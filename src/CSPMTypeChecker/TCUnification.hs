module CSPMTypeChecker.TCUnification 
	(generaliseGroup, instantiate, unify, unifyAll) where

import Data.List (nub, (\\), intersect, group, sort)

import CSPMDataStructures
import CSPMTypeChecker.TCMonad

import Util


class FreeTypeVars a where
	freeTypeVars :: a -> TypeCheckMonad [(TypeVar, [Constraint])]
	freeTypeVars = liftM nub . freeTypeVars'
	
	freeTypeVars' :: a -> TypeCheckMonad [(TypeVar, [Constraint])]

instance FreeTypeVars Type where
	freeTypeVars' (TVar tv) = 
		do
			typ <- readTypeRef tv
			case typ of
				Left (tv, cs)	-> return [(tv, cs)]
				Right t			-> freeTypeVars' t
	freeTypeVars' (TFunction targs tr) = 
		liftM concat (mapM freeTypeVars' (tr:targs))
	freeTypeVars' (TSeq t) = freeTypeVars' t
	freeTypeVars' (TSet t) = freeTypeVars' t
	freeTypeVars' (TInt) = return []
	freeTypeVars' TBool = return []
	freeTypeVars' (TTuple ts) = liftM concat (mapM freeTypeVars' ts)
	freeTypeVars' (TChannel tl) = freeTypeVars tl
	freeTypeVars' (TDotable t1 t2) = liftM concat (mapM freeTypeVars' [t1,t2])
	freeTypeVars' (TDatatypeClause n1 ts) = liftM concat (mapM freeTypeVars' ts)
	freeTypeVars' (TList t1 t2) = liftM concat (mapM freeTypeVars' [t1,t2])
	freeTypeVars' (TListEnd) = return []
	freeTypeVars' (TPolyList tv) =
		do
			typ <- readTypeRef tv
			case typ of
				Left (tv, cs)	-> return [(tv, cs)]
				Right t			-> freeTypeVars' t
	freeTypeVars' (TProc) = return []

-- *************************************************************************
-- Unification + Substitution
-- *************************************************************************
-- Name is a workaround for the problem as follows:
--	we convert a type T into forall vs T where vs = fvts (T) - fvts(Env)
--	where Env does not contain the function whose type we are generalizing
--  (this is because when we type a declaration we are really typing a 
--  lambda function).
generaliseGroup :: [Name] -> [TypeCheckMonad [(Name, Type)]] -> 
					TypeCheckMonad [[(Name, TypeScheme)]]
generaliseGroup names tsm =
	do
		ts <- sequence tsm
		envs <- getEnvironment
		envfvs <- liftM nub 
			(concatMapM freeTypeVars 
				[t | env <- envs, (n, (ForAll _ t)) <- env, not (n `elem` names)])
		mapM (\ nts -> mapM (\ (n,t) -> 
								do
									deffvs <- freeTypeVars t
									let unboundVars = 
										filter (\ (fv, cs) -> 
											not (fv `elem` map fst envfvs)) deffvs
									let t' = ForAll unboundVars t
									setType n t'
									return $ (n, t')) nts) ts

instantiate :: TypeScheme -> TypeCheckMonad Type
instantiate (ForAll ts t) =
	do
		tvs <- mapM (freshTypeVarWithConstraints . snd) ts
		foldM (\ x y -> substituteType y x) t (zip (map fst ts) tvs)
		
occurs :: TypeVar -> Type -> TypeCheckMonad Bool
occurs a (TVar (tvref @ (TypeVarRef tv _ _))) = 
	do
		res <- readTypeRef tvref
		case res of 
			Left (tv,cs)-> return $ a == tv
			Right t		-> occurs a t
occurs a (TSet t) = occurs a t
occurs a (TSeq t) = occurs a t
occurs a (TTuple ts) = liftM or (mapM (occurs a) ts)
occurs a (TFunction ts t) = liftM or (mapM (occurs a) (t:ts))
occurs a (TList t1 t2) = liftM or (mapM (occurs a) [t1,t2])
occurs a (TChannel t) = occurs a t
occurs a (TDatatypeClause n ts) = liftM or (mapM (occurs a) ts)
occurs a (TDotable t1 t2) = liftM or (mapM (occurs a) [t1,t2])
occurs a (TPolyList (tvref @ (TypeVarRef tv _ _))) = 
	do
		res <- readTypeRef tvref
		case res of 
			Left (tv,cs)-> return $ a == tv
			Right t		-> occurs a t
occurs a TListEnd = return False
occurs a TInt = return False
occurs a TBool = return False
occurs a TProc = return False

unifyTypeSchemes :: TypeScheme -> TypeScheme -> TypeCheckMonad TypeScheme
unifyTypeSchemes (ForAll ts1 t1) (ForAll ts2 t2) =
	do
		t3 <- unify t1 t2
		return $ ForAll ts1 t3

unifyAll :: [Type] -> TypeCheckMonad Type
unifyAll [] = freshTypeVar
unifyAll [t] = return t
unifyAll (t1:ts) =
	do
		t2 <- unifyAll ts
		unify t1 t2

-- Takes a constraint and a type and returns True iff the type satisfies the
-- constraint, or can be made to satsify the constraint by appropriate type
-- substitutions.
unifyConstraint :: Constraint -> Type -> TypeCheckMonad Bool
unifyConstraint c (TVar v) =
	do
		res <- readTypeRef v
		case res of
			Left (tva, cs)	-> if c `elem` cs then return True else
								do
									fv <- freshTypeVarWithConstraints (nub (cs++[c]))
									applySubstitution v fv
									return True
			Right t			-> unifyConstraint c t
unifyConstraint c TInt = return True
unifyConstraint Eq TBool = return True -- Bools are not orderable P524
unifyConstraint c (TSeq t) = unifyConstraint c t
unifyConstraint c (TSet t) = return True -- All set elements must support comparison
unifyConstraint c (TTuple ts) = liftM and (mapM (unifyConstraint c) ts)
unifyConstraint c (TList t1 t2) = liftM and (mapM (unifyConstraint c) [t1, t2])
unifyConstraint c (TListEnd) = return True
unifyConstraint c (TPolyList v) = 
	do
		res <- readTypeRef v
		case res of
			Left (tva, cs)	-> if c `elem` cs then return True else
								do
									(TVar nref) <- 
										freshTypeVarWithConstraints (nub (cs++[c]))
									applySubstitution v (TPolyList nref)
									return True
			Right t			-> unifyConstraint c t
unifyConstraint Eq (TChannel tl) = return True -- channels are comparable only
unifyConstraint Eq (TDotable a b) = -- channels and datatypes are only dotable things
	liftM and (mapM (unifyConstraint Eq) [a,b])
unifyConstraint Eq (TDatatypeClause n ts) = 
	liftM and (mapM (unifyConstraint Eq) ts) -- User data types are not orderable P524
unifyConstraint c t = return False
	
unify :: Type -> Type -> TypeCheckMonad Type
unify (TVar t1) (TVar t2) | t1 == t2 = 
	return (TVar t1)
unify (TVar t1) (TVar t2) = 
	do
		res1 <- readTypeRef t1
		res2 <- readTypeRef t2
		case (res1, res2) of
			(Left (tv1, cs1), Left (tv2,cs2)) ->
				do
					fv <- freshTypeVarWithConstraints (nub (cs1 ++ cs2))
					applySubstitution t1 fv
					applySubstitution t2 fv
					return fv
			(Left _, Right t)		-> unify (TVar t1) t
			(Right t, Left _)		-> unify t (TVar t2)
			(Right t1, Right t2)	-> unify t1 t2
unify (TVar a) b = 
	do
		res <- readTypeRef a
		case res of
			Left (tva, cs)	->
				do
					res <- liftM and (mapM (\ c -> unifyConstraint c b) cs)
					if res then applySubstitution a b
						else do
								t1' <- compress (TVar a)
								t2' <- compress b
								throwError $ UnknownUnificationError t1' t2'
			Right t			-> unify t b
unify t (TVar b) = unify (TVar b) t

unify TInt TInt = return TInt
unify TBool TBool = return TBool
unify TProc TProc = return TProc

unify (TFunction ts1 rt1) (TFunction ts2 rt2) | length ts1 == length ts2 =
	do
		ts <- zipWithM unify ts1 ts2
		rt <- unify rt1 rt2
		return $ TFunction ts rt
unify (TSeq t1) (TSeq t2) =
	do
		tr <- unify t1 t2
		return $ TSeq tr
unify (TSet t1) (TSet t2) =
	do
		tr <- unify t1 t2
		return $ TSet tr
unify (TTuple ts1) (TTuple ts2) | length ts1 == length ts2 =
	do
		ts <- zipWithM unify ts1 ts2
		return $ TTuple ts
unify (TDotable t1 t2) (TDotable t1' t2') =
	do
		a <- unify t1 t1'
		b <- unify t2 t2'
		return $ TDotable a b
unify (TChannel tl1) (TChannel tl2) =
	do
		tl <- unify tl1 tl2
		return $ TChannel tl
unify (TDatatypeClause n1 ts1) (TDatatypeClause n2 ts2) 
	| n1 == n2 && length ts1 == length ts2 =
	do
		ts <- zipWithM unify ts1 ts2
		return $ TDatatypeClause n1 ts
		
unify (TList t1 t2) (TList t1' t2') =
	do
		a <- unify t1 t1'
		b <- unify t2 t2'
		return $ TList a b
unify (TPolyList t1) (TPolyList t2) | t1 == t2 = return $ TPolyList t1
unify (TPolyList t1) (TPolyList t2) =
	do
		res1 <- readTypeRef t1
		res2 <- readTypeRef t2
		case (res1, res2) of
			(Left (tv1, cs1), Left (tv2,cs2)) ->
				do
					(TVar fv) <- freshTypeVarWithConstraints (nub (cs1 ++ cs2))
					applySubstitution t1 (TPolyList fv)
					applySubstitution t2 (TPolyList fv)
					return (TPolyList fv)
			(Left _, Right t)		-> unify (TVar t1) t
			(Right t, Left _)		-> unify t (TVar t2)
			(Right t1, Right t2)	-> unify t1 t2
unify (TPolyList t1) t2 = 
	do
		res <- readTypeRef t1
		case res of
			Left (tva, cs)	-> 
				do
					res <- liftM and (mapM (\ c -> unifyConstraint c t2) cs)
					if res then applySubstitution t1 t2
						else do
								t1' <- compress (TVar t1)
								t2' <- compress t2
								throwError $ UnknownUnificationError t1' t2'
			Right t'		-> unify t' t2
unify t (TPolyList t1) = unify (TPolyList t1) t
unify (TListEnd) (TListEnd) = return TListEnd

-- Non trivial cases
unify (TDotable t1 t2) (TChannel tl) =
	do
		fv1 <- freshTypeVar
		fv2 <- freshTypeVar
		unify tl (TList fv1 fv2)
		t' <- unify t1 fv1
		(TChannel tl') <- unify t2 (TChannel fv2)
		return $ TChannel (TList t' tl')
unify (TChannel tl) (TDotable t1 t2) = unify (TDotable t1 t2) (TChannel tl)
unify (TDotable t1 t2) (TDatatypeClause n1 (t1':ts)) =
	do
		t' <- unify t1 t1'
		(TDatatypeClause _ ts') <- unify t2 (TDatatypeClause n1 ts)
		return $ TDatatypeClause n1 (t':ts')
unify (TDatatypeClause n1 ts) (TDotable t1 t2) = 
	unify (TDotable t1 t2) (TDatatypeClause n1 ts)
unify t1 t2 = 
	do
		t1' <- compress t1
		t2' <- compress t2
		throwError $ UnknownUnificationError t1' t2'
		
-- Returns the type that we substitute for
-- NB: in a quantified type we do not apply the substitution to any 
-- quantified variables
applySubstitution :: TypeVarRef -> Type -> TypeCheckMonad Type
applySubstitution (tvref @ (TypeVarRef tv _ _)) typ =
	do
		t' <- compress typ
		errorIfFalseM (liftM not (occurs tv typ)) (InfiniteUnificationError tv t')
		writeTypeRef tvref typ
		return typ

-- Applies a subtitution directly to the type. This is used in
-- type instantiation where we create a fresh type for each universal 
-- variable
substituteType :: (TypeVar, Type) -> Type -> TypeCheckMonad Type
substituteType (tv, t) (b @ (TVar (a @ (TypeVarRef tv' cs ioref)))) = 
	do
		res <- readTypeRef a
		case res of
			Left tva	-> if tv == tv' then return t else return b
			Right t'	-> substituteType (tv, t) t'
substituteType sub (TFunction targs tr) =
	do
		targs' <- mapM (substituteType sub) targs
		tr' <- substituteType sub tr
		return $ TFunction targs' tr'
substituteType sub (TSeq t) = 
	do
		t' <- substituteType sub t
		return $ TSeq t'
substituteType sub (TSet t) =
	do
		t' <- substituteType sub t
		return $ TSet t'
substituteType sub (TChannel tl) = 
	do
		tl' <- substituteType sub tl
		return $ TChannel tl'
substituteType sub (TList t1 t2) =
	do 
		t1' <- substituteType sub t1
		t2' <- substituteType sub t2
		return $ TList t1' t2'
substituteType (tv,t) (b @ (TPolyList (a @ (TypeVarRef tv' cs ioref)))) =
	do
		res <- readTypeRef a
		case res of
			Left tva	-> if tv == tv' then return t else return b
			Right t'	-> substituteType (tv, t) t'
substituteType sub TListEnd = return TListEnd
substituteType sub (TDotable t1 t2) =
	do
		t1' <- substituteType sub t1
		t2' <- substituteType sub t2
		return $ TDotable t1' t2'
substituteType sub (TTuple ts) =
	do
		ts' <- mapM (substituteType sub) ts
		return $ TTuple ts'
substituteType sub (TDatatypeClause n1 ts)=
	do
		ts' <- mapM (substituteType sub) ts
		return $ TDatatypeClause n1 ts'
substituteType sub TInt = return TInt
substituteType sub TBool = return TBool
substituteType sub TProc = return TProc

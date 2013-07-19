module CSPMTypeChecker.TCDependencies 
	(Dependencies, dependencies, namesBoundByDecl, namesBoundByDecl',
	FreeVars, freeVars, prebindDataType) where

import Data.List (nub, (\\))

import CSPMDataStructures
import CSPMTypeChecker.TCMonad
import Util


-- This method heavily affects the DataType clause of typeCheckDecl.
-- If any changes are made here changes will need to be made to typeCheckDecl
-- too
prebindDataType :: Decl -> TypeCheckMonad ()
prebindDataType (DataType n cs) =
	let
		prebindDataTypeClause (DataTypeClause n' es) =
			do
				fvs <- replicateM (length es) freshTypeVar
				setType n' (ForAll [] (TDatatypeClause n fvs))
		clauseNames = [n' | DataTypeClause n' es <- map removeAnnotation cs]
	in do
		errorIfFalse (noDups clauseNames) (DuplicatedDefinitions clauseNames)
		mapM_ (prebindDataTypeClause . removeAnnotation) cs
		-- n is the set of all TDatatypeClause 
		setType n (ForAll [] (TSet (TDatatypeClause n [])))


class Dependencies a where
	dependencies :: a -> TypeCheckMonad [Name]
	dependencies xs = liftM nub (dependencies' xs)
	dependencies' :: a -> TypeCheckMonad [Name]

instance Dependencies a => Dependencies [a] where
	dependencies' xs = concatMapM dependencies xs
instance Dependencies a => Dependencies (Maybe a) where
	dependencies' (Just x) = dependencies' x
	dependencies' Nothing = return []
instance Dependencies a => Dependencies (Annotated b a) where
	dependencies' (Annotated _ _ inner) = dependencies inner

instance Dependencies Pat where
	dependencies' (PVar n) = 
		do
			res <- safeGetType n
			case res of
				Just (ForAll _ t) -> 
					case t of
						-- See typeCheck (PVar) for a discussion of why
						-- we only do this
						TDatatypeClause n ts	-> return [n]
						_						-> return []
				Nothing	-> return []	-- var is not bound
	dependencies' (PConcat p1 p2) =
		do
			fvs1 <- dependencies' p1
			fvs2 <- dependencies' p2
			return $ fvs1++fvs2
	dependencies' (PDotApp p1 p2) = dependencies' [p1,p2]
	dependencies' (PList ps) = dependencies' ps
	dependencies' (PWildCard) = return []
	dependencies' (PTuple ps) = dependencies' ps
	dependencies' (PSet ps) = dependencies' ps
	dependencies' (PParen p) = dependencies' p
	dependencies' (PLit l) = return []
	dependencies' (PDoublePattern p1 p2) = 
		do
			fvs1 <- dependencies' p1
			fvs2 <- dependencies' p2
			return $ fvs1++fvs2
	
instance Dependencies Exp where
	dependencies' (App e es) = dependencies' (e:es)
	dependencies' (BooleanBinaryOp _ e1 e2) = dependencies' [e1,e2]
	dependencies' (BooleanUnaryOp _ e) = dependencies' e
	dependencies' (Concat e1 e2) = dependencies' [e1,e2]
	dependencies' (DotApp e1 e2) = dependencies' [e1,e2]
	dependencies' (If e1 e2 e3) = dependencies' [e1,e2, e3]
	dependencies' (Lambda p e) = 
		do
			fvsp <- freeVars p
			depsp <- dependencies p
			fvse <- dependencies e
			return $ (fvse \\ fvsp)++depsp
	dependencies' (Let ds e) =
		do
			fvsd <- dependencies ds
			newBoundVars <- liftM nub (concatMapM namesBoundByDecl ds)
			fvse <- dependencies e
			return $ nub (fvse++fvsd) \\ newBoundVars
	dependencies' (Lit _) = return []
	dependencies' (List es) = dependencies es
	dependencies' (ListComp es stmts) =
		do
			fvStmts <- freeVars stmts
			depsStmts <- dependencies stmts
			fvses' <- dependencies es
			let fvse = nub (fvses'++depsStmts)
			return $ fvse \\ fvStmts
	dependencies' (ListEnumFrom e1) = dependencies' e1
	dependencies' (ListEnumFromTo e1 e2) = dependencies' [e1,e2]
	dependencies' (ListLength e) = dependencies' e
	dependencies' (MathsBinaryOp _ e1 e2) = dependencies' [e1,e2]
	dependencies' (NegApp e) = dependencies' e
	dependencies' (Paren e) = dependencies' e
	dependencies' (Set es) = dependencies es
	dependencies' (SetComp es stmts) =
		do
			fvStmts <- freeVars stmts
			depsStmts <- dependencies stmts
			fvses' <- dependencies es
			let fvse = nub (fvses'++depsStmts)
			return $ fvse \\ fvStmts
	dependencies' (SetEnumComp es stmts) =
		do
			fvStmts <- freeVars stmts
			depsStmts <- dependencies stmts
			fvses' <- dependencies es
			let fvse = nub (fvses'++depsStmts)
			return $ fvse \\ fvStmts
	dependencies' (SetEnumFrom e1) = dependencies' e1
	dependencies' (SetEnumFromTo e1 e2) = dependencies' [e1,e2]
	dependencies' (SetEnum es) = dependencies' es
	dependencies' (Tuple es) = dependencies' es
	dependencies' (Var (UnQual n)) = return [n]
	
	dependencies' (UserOperator n es) = dependencies' es
	dependencies' (ReplicatedUserOperator n es stmts) =
		do
			fvStmts <- freeVars stmts
			depsStmts <- dependencies stmts
			fvses' <- dependencies es
			let fvse = nub (fvses'++depsStmts)
			return $ fvse \\ fvStmts
		
instance Dependencies Stmt where
	dependencies' (Generator p e) =
		do
			ds1 <- dependencies p
			ds2 <- dependencies e
			return $ ds1++ds2
	dependencies' (Qualifier e) = dependencies e
	
instance Dependencies Decl where
	dependencies' (FunBind n ms t) = 
		do
			fvsms <- dependencies ms
			fvst <- dependencies t
			return $ fvsms++fvst
	dependencies' (PatBind p e) = 
		do
			depsp <- dependencies p
			fvsp <- freeVars p
			depse <- dependencies e
			return $ depsp++depse
	dependencies' (Channel ns es) = dependencies es
	dependencies' (Assert e1 e2 m) = dependencies [e1, e2]
	dependencies' (DataType n cs) = dependencies [cs]
	dependencies' (External ns) = return []
	dependencies' (Transparent ns) = return []

instance Dependencies Match where
	dependencies' (Match ps e) =
		do
			fvs1 <- freeVars ps
			depsPs <- dependencies ps
			fvs2 <- dependencies e
			return $ (fvs2 \\ fvs1) ++ depsPs

instance Dependencies DataTypeClause where
	dependencies' (DataTypeClause n es) = dependencies es
	
namesBoundByDecl :: AnDecl -> TypeCheckMonad [Name]
namesBoundByDecl =  namesBoundByDecl' . removeAnnotation
namesBoundByDecl' (FunBind n ms t) = return [n]
namesBoundByDecl' (PatBind p ms) = freeVars p
namesBoundByDecl' (Channel ns es) = return ns
namesBoundByDecl' (Assert e1 e2 m) = return []
namesBoundByDecl' (DataType n dcs) = 
	let
		namesBoundByDtClause (DataTypeClause n _) = [n]
	in
		return $ n:concatMap (namesBoundByDtClause . removeAnnotation) dcs
namesBoundByDecl' (External ns) = return ns
namesBoundByDecl' (Transparent ns) = return ns


class FreeVars a where
	freeVars :: a -> TypeCheckMonad [Name]
	freeVars = liftM nub . freeVars'
	
	freeVars' :: a -> TypeCheckMonad [Name]

instance FreeVars a => FreeVars [a] where
	freeVars' xs = concatMapM freeVars' xs
	
instance FreeVars a => FreeVars (Annotated b a) where
	freeVars' (Annotated _ _ inner) = freeVars inner

instance FreeVars Pat where
	freeVars' (PVar n) = 
		do
			res <- safeGetType n
			case res of
				Just (ForAll _ t) -> 
					case t of
						-- See typeCheck (PVar) for a discussion of why
						-- we only do this
						TDatatypeClause n ts	-> return []
						_						-> return [n]
				Nothing	-> return [n]	-- var is not bound
	freeVars' (PConcat p1 p2) =
		do
			fvs1 <- freeVars' p1
			fvs2 <- freeVars' p2
			return $ fvs1++fvs2
	freeVars' (PDotApp p1 p2) = freeVars' [p1,p2]
	freeVars' (PList ps) = freeVars' ps
	freeVars' (PWildCard) = return []
	freeVars' (PTuple ps) = freeVars' ps
	freeVars' (PSet ps) = freeVars' ps
	freeVars' (PParen p) = freeVars' p
	freeVars' (PLit l) = return []
	freeVars' (PDoublePattern p1 p2) = 
		do
			fvs1 <- freeVars' p1
			fvs2 <- freeVars' p2
			return $ fvs1++fvs2

instance FreeVars Stmt where
	freeVars' (Qualifier e) = return []
	freeVars' (Generator p e) = freeVars p

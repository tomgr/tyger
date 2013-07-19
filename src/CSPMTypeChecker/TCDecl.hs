{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
module CSPMTypeChecker.TCDecl (typeCheckDecls) where

import Data.Graph
import Data.List (nub, intersect)

import CSPMDataStructures
import CSPMTypeChecker.TCBuiltInFunctions
import CSPMTypeChecker.TCCommon
import CSPMTypeChecker.TCDependencies
import CSPMTypeChecker.TCExpr
import CSPMTypeChecker.TCMonad
import CSPMTypeChecker.TCPat
import CSPMTypeChecker.TCUnification

import Util

-- Type check a list of possibly mutually recursive functions
typeCheckDecls :: [PDecl] -> TypeCheckMonad ()
typeCheckDecls decls =
	do
		let declMap = zip decls [0..]
		boundVarToDeclIdMap <- 
			concatMapM (\ decl -> 
				do
					namesBound <- namesBoundByDecl decl
					return [(n, apply declMap decl) | n <- namesBound]) decls
		let fvs = map fst boundVarToDeclIdMap
		
		errorIfFalse (noDups fvs) (DuplicatedDefinitions fvs)

		-- Pre-analysis phase:
		-- We prebind the datatypes so that we can detect when something is
		-- a free variable in a pattern and when it is bound
		mapM_ prebindDataType [DataType n ms | DataType n ms <- map removeAnnotation decls]

		-- Map from decl id -> [decl id] meaning decl id depends on the list of
		-- ids
		declDeps <- mapM (\ decl -> 
				do
					fvsd <- dependencies decl
					let fvs' = intersect fvsd fvs
					return (apply declMap decl, mapPF boundVarToDeclIdMap fvs')
					) decls

		-- Edge from n -> n' iff n uses n'
		let sccs = map flattenSCC 
						(stronglyConnComp [(id, id, deps) | (id, deps) <- declDeps])
		let	typeInferenceGroups = map (mapPF (invert declMap)) sccs

		debugOutput ("Type check order: "
				++show (map (safeMapPF (invert boundVarToDeclIdMap)) sccs))
		
		mapM_ typeCheckMutualyRecursiveGroup typeInferenceGroups
	
typeCheckMutualyRecursiveGroup :: [PDecl] -> TypeCheckMonad ()
typeCheckMutualyRecursiveGroup ds =
	do
		-- We only create variables for non datatype declarations as the others
		-- were prebound in prebindDataType
		fvs <- liftM nub (concatMapM namesBoundByDecl 
					(filter (not . isDataTypeDecl) ds))
		ftvs <- replicateM (length fvs) freshTypeVar
		zipWithM setType fvs (map (ForAll []) ftvs)
		
		-- The list of all variables bound by these declaration
		fvs <- liftM nub (concatMapM namesBoundByDecl ds)

		-- Type check each declaration then generalise the types
		nts <- generaliseGroup fvs (map typeCheck ds)
		-- Add the type of each declaration (if one exists to each declaration)
		zipWithM annotate nts ds
		
		-- Compress all the types we have inferred here
		-- (They should never be touched again)
		mapM_ (\ n -> 
			do
				t <- getType n
				t' <- compressTypeScheme t
				setType n t') fvs
	where
		isDataTypeDecl (Annotated _ _ inner) = isDataTypeDecl' inner
		isDataTypeDecl' (DataType _ _ ) = True
		isDataTypeDecl' _ = False
		
		annotate nts (Annotated _ psymbtable _) =
			setPSymbolTable psymbtable nts

evaluateTypeExpression :: Type -> Type -> TypeCheckMonad ()
evaluateTypeExpression t fv =
	(do
		unify t (TSet fv)
		`catchError` (\ e ->
			case t of
				-- Could be a tuple of sets (TTuple [TSet t1,...] = TSet (TTuple [t1,...]))
				-- according to Bill's book P529
				TTuple ts -> 
					do
						fvs <- replicateM (length ts) freshTypeVar
						zipWithM evaluateTypeExpression ts fvs
						unify fv (TSet (TTuple fvs))))
	>> return ()

instance TypeCheckable PDecl [(Name, Type)] where
	errorConstructor = ErrorWithDecl
	-- We perform type annotation in  typeCheckMutualyRecursiveGroup since
	-- this is the first time we know the TypeScheme.
	typeCheck' = typeCheck' . removeAnnotation

instance TypeCheckable Decl [(Name, Type)] where
	errorConstructor = error "Decl () error constructor called"
	typeCheck' (FunBind n ms usertyp) = 
		do
			ts <- mapM typeCheck ms
			ForAll [] t <- getType n
			(t' @ (TFunction tsargs _)) <- unifyAll (t:ts)
			case usertyp of
				Nothing -> return ()
				Just es -> do
							ts <- mapM typeCheck es
							mapM ensureIsSet ts
							zipWithM unify (map TSet tsargs) ts
							return ()
			return [(n, t')]
	typeCheck' (PatBind pat exp) =
		do
			tpat <- typeCheck pat
			fvs <- freeVars pat
			-- Allow the pattern to be recursive
			texp <- local fvs (typeCheck exp)
			unify texp tpat
			ns <- namesBoundByDecl' (PatBind pat exp)
			ts <- mapM getType ns
			return $ zip ns [t | ForAll _ t <- ts]
	typeCheck' (Channel ns es) =
		do
			ts <- mapM typeCheck es
			fvs <- replicateM (length ts) freshTypeVar
			-- Make sure everything is a set
			zipWithM evaluateTypeExpression ts fvs
			-- Channels require that each component is comparable
			mapM (ensureHasConstraint Eq) fvs
			let t = TChannel $ foldr TList TListEnd fvs
			mapM_ (\ n -> setType n (ForAll [] t)) ns
			return [(n,t) | n <- ns]
	-- This clause is relies on the fact that prebindDataType has been called first
	-- any changes to that will require a change here
	typeCheck' (DataType n clauses) =
		do
			nts <- mapM (\ clause -> 
				do
					(n', ts) <- typeCheck clause
					-- We already have a variable for n' (introduced in prebindDataType)
					ForAll [] t <- getType n'
					unify t (TDatatypeClause n ts)
					return (n', t)
					) clauses
			-- We have already set the type of n in prebindDataType
			ForAll [] t <- getType n
			return $ (n,t):nts
	typeCheck' (Assert e1 e2 m) =
		do
			t1 <- typeCheck e1
			ensureIsProcess t1
			t2 <- typeCheck e2
			ensureIsProcess t2
			return []
	typeCheck' (Transparent ns) =
		do
			let ts = map (\ (Name n) -> 
							(Name n, ForAll [] (apply transparentFunctions n))) ns
			mapM_ (\ (n, t) -> setType n t) ts
			return []
	typeCheck' (External ns) =
		do
			let ts = map (\ (Name n) -> 
							(Name n, ForAll [] (apply externalFunctions n))) ns
			mapM_ (\ (n, t) -> setType n t) ts
			return []

instance TypeCheckable PDataTypeClause (Name, [Type]) where
	errorConstructor = ErrorWithDataTypeClause
	typeCheck' (Annotated srcloc typ inner) = 
		do
			t' <- typeCheck' inner
			-- TODO: type annotation
--			setPType typ t'
			return t'
-- TODO: allow Proc in a datatype declaration
-- TODO: check no type variables are left in a declaration of a datatype or
-- channel
instance TypeCheckable DataTypeClause (Name, [Type]) where
	errorConstructor = error "Error: DataTypeClause error constructor called"
	typeCheck' (DataTypeClause n' es) =
		do
			ts <- mapM typeCheck es
			fvs <- replicateM (length ts) freshTypeVar 
			-- Make sure everything is a set
			zipWithM evaluateTypeExpression ts fvs
			return (n', fvs)

instance TypeCheckable PMatch Type where
	errorConstructor = ErrorWithMatch
	typeCheck' (Annotated srcloc typ inner) = 
		do
			t' <- typeCheck' inner
			return t'
instance TypeCheckable Match Type where
	errorConstructor = error "Error: match error constructor called"
	typeCheck' (Match groups exp) = 
		do
			fvs <- liftM concat (mapM freeVars groups)
			local fvs (
				do
					tr <- typeCheck exp
					tgroups <- mapM (\ pats -> mapM typeCheck pats) groups
					return $ foldr (\ targs tr -> TFunction targs tr) tr tgroups)

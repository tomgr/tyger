{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module CSPMTypeChecker.TCCommon where

import CSPMDataStructures
import CSPMTypeChecker.TCBuiltInFunctions
import CSPMTypeChecker.TCMonad
import CSPMTypeChecker.TCUnification
import qualified OpSemDataStructures as OpSem
import Util

typeCheckWrapper :: TypeCheckable a b => 
	a -> PartialFunction OpSem.Name [OpSem.Type] -> TypeCheckMonad b
typeCheckWrapper tc ops =
		do
			setUserOperators convertedops
			injectBuiltInFunctions
			-- We add an extra scope layer here to allow the built in functions
			-- to be overloaded.
			local [] (typeCheck tc)
	where
		convertedops = 
			[(opSemOperatorNameToCSPMName n, map opSemTypeToCSPMType ts) 
				| (n,ts) <- ops]

-- *************************************************************************
-- Helper methods
-- *************************************************************************
ensureIsList :: Type -> TypeCheckMonad Type
ensureIsList typ =
	do
		fv <- freshTypeVar
		unify (TSeq fv) typ

ensureIsSet :: Type -> TypeCheckMonad Type
ensureIsSet typ =
	do
		fv <- freshTypeVar
		ensureHasConstraint Eq fv
		unify (TSet fv) typ

ensureIsBool :: Type -> TypeCheckMonad Type
ensureIsBool typ = unify (TBool) typ

ensureIsInt :: Type -> TypeCheckMonad Type
ensureIsInt typ = unify TInt typ

ensureIsChannel :: Type -> TypeCheckMonad Type
ensureIsChannel t =
	do
		(TVar fv) <- freshTypeVar
		unify t (TChannel (TPolyList fv))

ensureIsEvent :: Type -> TypeCheckMonad Type
ensureIsEvent t = unify t (TChannel TListEnd)

ensureIsDotable :: Type -> TypeCheckMonad Type
ensureIsDotable t =
	do
		fv1 <- freshTypeVar
		fv2 <- freshTypeVar
		unify t (TDotable fv1 fv2)

ensureHasConstraint :: Constraint -> Type -> TypeCheckMonad Type
ensureHasConstraint c t = 
	do
		fv1 <- freshTypeVarWithConstraints [c]
		unify fv1 t

ensureIsProcess :: Type -> TypeCheckMonad Type
ensureIsProcess t =
	do
		unify TProc t

-- See http://www.haskell.org/haskellwiki/Functional_dependencies for more
-- descriptions on a -> b but it esentially says that a determins the type
-- b (i.e. we can't have two instances that match on a but differ on b)
class TypeCheckable a b | a -> b where
	typeCheck :: a -> TypeCheckMonad b
	typeCheck a = typeCheck' a
		`catchError` (\ e -> throwError $ errorConstructor a e)
	
	errorConstructor :: a -> (TypeCheckError -> TypeCheckError)
	typeCheck' :: a -> TypeCheckMonad b

instance TypeCheckable Literal Type where
	errorConstructor = error "No error should ever occur in a literal"
	typeCheck' (Int n) = return TInt
	typeCheck' (Bool b) = return TBool


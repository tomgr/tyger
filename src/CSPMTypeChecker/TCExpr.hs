{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
module CSPMTypeChecker.TCExpr () where

import CSPMDataStructures
import CSPMTypeChecker.TCCommon
import {-# SOURCE #-} CSPMTypeChecker.TCDecl
import CSPMTypeChecker.TCDependencies
import CSPMTypeChecker.TCPat
import CSPMTypeChecker.TCMonad
import CSPMTypeChecker.TCUnification

import Util

instance TypeCheckable PExp Type where
	errorConstructor = ErrorWithExp
	-- Important: we use the typeCheck' version after removing the annotation
	-- so the error message contains this node
	typeCheck' (Annotated srcloc typ inner) = 
		do
			t' <- typeCheck' inner
			setPType typ t'
			return t'
instance TypeCheckable Exp Type where
	errorConstructor = error "Error: expression error constructor called."	
	typeCheck' (App f args) =
		do
			tFunc <- typeCheck f
			tr <- freshTypeVar
			tArgs <- replicateM (length args) freshTypeVar
			unify (TFunction tArgs tr) tFunc
			
			tArgs' <- mapM typeCheck args
			errorIfFalse (length tArgs == length tArgs') 
				(IncorrectNumberOfArguments f (length tArgs))
			unifiedTArgs <- zipWithM unify tArgs tArgs'
			return tr
	typeCheck' (BooleanBinaryOp op e1 e2) =
		do
			t1 <- typeCheck e1
			t2 <- typeCheck e2
			t <- unify t1 t2
			case op of
				And				-> ensureIsBool t
				Or				-> ensureIsBool t
				Equals			-> ensureHasConstraint Eq t
				NotEquals		-> ensureHasConstraint Eq t
				LessThan		-> ensureHasConstraint Ord t
				LessThanEq		-> ensureHasConstraint Ord t
				GreaterThan		-> ensureHasConstraint Ord t
				GreaterThanEq	-> ensureHasConstraint Ord t
			return TBool
	typeCheck' (BooleanUnaryOp op e1) =
		do
			t1 <- typeCheck e1
			ensureIsBool t1
			return TBool
	typeCheck' (Concat e1 e2) = 
		do
			t1 <- typeCheck e1
			t2 <- typeCheck e2
			ensureIsList t1
			ensureIsList t2
			unify t1 t2
	typeCheck' (DotApp e1 e2) =
		do
			t1 <- typeCheck e1
			t2 <- typeCheck e2
			
			argt <- freshTypeVar
			rt <- freshTypeVar
			unify t1 (TDotable argt rt)
			unify t2 argt
			
			return rt
	typeCheck' (If e1 e2 e3) =
		do
			t1 <- typeCheck e1
			ensureIsBool t1
			t2 <- typeCheck e2
			t3 <- typeCheck e3
			unify t2 t3
	typeCheck' (Lambda p exp) =
		do
			fvs <- freeVars p
			local fvs (
				do
					tr <- typeCheck exp
					targ <- typeCheck p
					return $ TFunction [targ] tr)
	typeCheck' (Let decls exp) =
		local [] (	-- Add a new scope: typeCheckDecl will add vars into it
			do
				typeCheckDecls decls
				typeCheck exp)
	typeCheck' (Lit lit) = typeCheck lit
	typeCheck' (List es) =
		do
			ts <- mapM typeCheck es
			t <- unifyAll ts
			return $ TSeq t
	typeCheck' (ListComp es stmts) =
		do
			fvs <- concatMapM freeVars stmts
			errorIfFalse (noDups fvs) (DuplicatedDefinitions fvs)
			local fvs (
				do
					stmts <- mapM (typeCheckStmt TSeq) stmts
					ts <- mapM typeCheck es
					t <- unifyAll ts
					return $ TSeq t)
	typeCheck' (ListEnumFrom lb) =
		do
			t1 <- typeCheck lb
			ensureIsInt t1
			return $ TSeq TInt
	typeCheck' (ListEnumFromTo lb ub) =
		do
			t1 <- typeCheck lb
			ensureIsInt t1
			t2 <- typeCheck ub
			ensureIsInt t1
			return $ TSeq TInt
	typeCheck' (ListLength e) =
		do
			t1 <- typeCheck e
			ensureIsList t1
			return $ TInt
	typeCheck' (MathsBinaryOp op e1 e2) =
		do
			t1 <- typeCheck e1
			t2 <- typeCheck e2
			ensureIsInt t1
			ensureIsInt t2
			return TInt
	typeCheck' (NegApp e1) =
		do
			t1 <- typeCheck e1
			ensureIsInt t1
			return TInt
	typeCheck' (Paren e) = typeCheck e
	typeCheck' (Set es) =
		do
			ts <- mapM typeCheck es
			t <- unifyAll ts
			ensureHasConstraint Eq t
			return $ TSet t
	typeCheck' (SetComp es stmts) = 
		do
			fvs <- concatMapM freeVars stmts
			errorIfFalse (noDups fvs) (DuplicatedDefinitions fvs)
			local fvs (
				do
					stmts <- mapM (typeCheckStmt TSet) stmts
					ts <- mapM typeCheck es
					t <- unifyAll ts
					ensureHasConstraint Eq t
					return $ TSet t)
	typeCheck' (SetEnum es) = 
		do
			ts <- mapM typeCheck es
			mapM ensureIsChannel ts
			return $ TSet (TChannel TListEnd)
	typeCheck' (SetEnumComp es stmts) = 
		do
			fvs <- concatMapM freeVars stmts
			errorIfFalse (noDups fvs) (DuplicatedDefinitions fvs)
			local fvs (
				do
					stmts <- mapM (typeCheckStmt TSet) stmts
					ts <- mapM typeCheck es
					mapM ensureIsChannel ts
					return $ TSet (TChannel TListEnd))
	typeCheck' (SetEnumFrom lb) =
		do
			t1 <- typeCheck lb
			ensureIsInt t1
			-- No need to check for Eq - Ints always are
			return $ TSet TInt
	typeCheck' (SetEnumFromTo lb ub) =
		do
			t1 <- typeCheck lb
			ensureIsInt t1
			t2 <- typeCheck ub
			ensureIsInt t2
			-- No need to check for Eq - Ints always are
			return $ TSet TInt
	typeCheck' (Tuple es) =
		do
			ts <- mapM typeCheck es
			return $ TTuple ts
	typeCheck' (ReplicatedUserOperator n es stmts) =
		do
			fvs <- concatMapM freeVars stmts
			errorIfFalse (noDups fvs) (DuplicatedDefinitions fvs)
			local fvs (
				do
					stmts <- mapM (typeCheckStmt TSet) stmts
					ts <- mapM typeCheck es
					opMap <- getUserOperators
					let opTypes = apply opMap n
					zipWithM unify ts opTypes
					return TProc)
	typeCheck' (UserOperator n es) =
		do
			-- TODO: possible ( I think) that some user functions
			-- may actually be applications
			ts <- mapM typeCheck es
			opMap <- getUserOperators
			let opTypes = apply opMap n
			zipWithM unify ts opTypes
			return TProc
	typeCheck' (Var (UnQual n)) = 
		do
			t <- getType n
			instantiate t

typeCheckStmt :: (Type -> Type) -> PStmt -> TypeCheckMonad Type
typeCheckStmt typc = typeCheckStmt' typc . removeAnnotation
typeCheckStmt' typc (Qualifier e) = 
	do
		t <- typeCheck e
		ensureIsBool t
typeCheckStmt' typc (Generator p exp) =
	do
		tpat <- typeCheck p
		texp <- typeCheck exp
		unify (typc tpat) texp

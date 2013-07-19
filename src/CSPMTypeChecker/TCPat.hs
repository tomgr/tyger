{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
module CSPMTypeChecker.TCPat () where

import CSPMDataStructures
import CSPMTypeChecker.TCCommon
import CSPMTypeChecker.TCMonad
import CSPMTypeChecker.TCUnification
	
instance TypeCheckable PPat Type where
	errorConstructor = ErrorWithPat
	typeCheck' (Annotated srcloc typ inner) = 
		do
			t' <- typeCheck' inner
			return t'
instance TypeCheckable Pat Type where
	errorConstructor = error "Error: pattern error constructor called"
	typeCheck' (PConcat p1 p2) =
		do
			t1 <- typeCheck p1
			t1 <- ensureIsList t1
			t2 <- typeCheck p2
			t2 <- ensureIsList t2
			unify t1 t2
	typeCheck' (PDoublePattern p1 p2) =
		do
			t1 <- typeCheck p1
			t2 <- typeCheck p2
			unify t1 t2
	typeCheck' (PDotApp p1 p2) =
		do
			t1 <- typeCheck p1
			t2 <- typeCheck p2
			argt <- freshTypeVar
			rt <- freshTypeVar
			unify t1 (TDotable argt rt)
			unify t2 argt
			return rt			
	typeCheck' (PList ps) =
		do
			ts <- mapM typeCheck ps
			t <- unifyAll ts
			return $ TSeq t
	typeCheck' (PLit lit) = typeCheck lit
	typeCheck' (PParen p1) = typeCheck p1
	typeCheck' (PSet ps) =
	    do
		    errorIfFalse (length ps <= 1) (InvalidSetPattern ps)
		    ts <- mapM typeCheck ps
		    t <- unifyAll ts
		    ensureHasConstraint Eq t
		    return $ TSet t
	typeCheck' (PTuple ps) = 
		do
			ts <- mapM typeCheck ps
			return $ TTuple ts
	typeCheck' (PWildCard) = freshTypeVar
	typeCheck' (PVar n) = 
		do
			t @ (ForAll _ t') <- getType n
			-- All variables are already in scope hence we can just return the
			-- type (since we always typeCheck a pattern in between a 
			-- local (freeVars pat)).
			return t'


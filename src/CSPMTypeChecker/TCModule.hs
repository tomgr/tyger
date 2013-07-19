{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
module CSPMTypeChecker.TCModule where

import CSPMDataStructures
import CSPMTypeChecker.TCCommon
import CSPMTypeChecker.TCDecl
import CSPMTypeChecker.TCMonad
import qualified OpSemDataStructures as OpSem
import Util

instance TypeCheckable [PModule] () where
	errorConstructor an = id
	typeCheck' ([m]) = typeCheck m

instance TypeCheckable PModule () where
	errorConstructor = ErrorWithModule
	typeCheck' (Annotated _ _ m) = typeCheck' m

instance TypeCheckable Module () where
	errorConstructor = error "Error: Module error constructor called"
	typeCheck' (GlobalModule ds) = 
		typeCheckDecls ds


typeCheckModules :: OpSem.OpSemDefinition -> [PModule] -> TypeCheckMonad [TCModule]
typeCheckModules opSemDefn ms =
	do
		let operatorTypeMap = 
			[(OpSem.opFriendlyName op, map snd (OpSem.opArgs op)) 
				| op <- OpSem.operators opSemDefn]
		typeCheckWrapper ms operatorTypeMap
		return ms
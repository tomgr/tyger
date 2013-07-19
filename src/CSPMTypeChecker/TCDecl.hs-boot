module CSPMTypeChecker.TCDecl where

import CSPMDataStructures
import CSPMTypeChecker.TCMonad

typeCheckDecls :: [PDecl] -> TypeCheckMonad ()

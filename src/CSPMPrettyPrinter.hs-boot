{-# LANGUAGE FlexibleInstances #-}
module CSPMPrettyPrinter where
import CSPMDataStructures as CSPM
import Text.PrettyPrint.HughesPJ

class PrettyPrintable a where
	prettyPrint :: a -> Doc

instance (PrettyPrintable b) => PrettyPrintable (CSPM.Annotated a b)

instance PrettyPrintable CSPM.Name
instance PrettyPrintable CSPM.QualifiedName

instance PrettyPrintable [CSPM.Module]
instance PrettyPrintable CSPM.Module

instance PrettyPrintable CSPM.Decl
instance PrettyPrintable CSPM.Model
instance PrettyPrintable CSPM.DataTypeClause
instance PrettyPrintable CSPM.Pat

instance PrettyPrintable CSPM.BinaryBooleanOp
instance PrettyPrintable CSPM.BooleanUnaryOp 
instance PrettyPrintable CSPM.MathsOp
instance PrettyPrintable CSPM.Exp
instance PrettyPrintable CSPM.Stmt
instance PrettyPrintable CSPM.Literal

{-# LANGUAGE FlexibleInstances #-}
module CSPMPrettyPrinter where
import CSPMTypeChecker.TCBuiltInFunctions
import qualified CSPMDataStructures as CSPM
import Text.PrettyPrint.HughesPJ

class PrettyPrintable a where
	prettyPrint :: a -> Doc

-- *************************************************************************
-- Extensions
-- *************************************************************************
angles :: Doc -> Doc
angles d = char '<' <> d <> char '>'

bars :: Doc -> Doc
bars d = char '|' <> d <> char '|'

list :: [Doc] -> Doc
list docs =	
	fsep (punctuate (text ",") docs)

tabWidth = 4
tabindent = nest tabWidth

instance (PrettyPrintable b) => PrettyPrintable (CSPM.Annotated a b) where
	prettyPrint (CSPM.Annotated loc typ inner) = prettyPrint inner
	
-- *************************************************************************
-- Names
-- *************************************************************************
instance PrettyPrintable CSPM.Name where
	prettyPrint (CSPM.Name "Events") = text "UserEvents"
	prettyPrint (CSPM.Name "WrapThread") = text "WrapThread"
	prettyPrint (CSPM.Name "ProcArgs") = text "ProcArgs"
	prettyPrint (CSPM.Name "GetProc") = text "GetProc"
	prettyPrint (CSPM.Name "CallProc") = text "CallProc"
	prettyPrint (CSPM.Name s) = 
		if s `elem` builtInNames then text s else text (s++"'")

instance PrettyPrintable CSPM.QualifiedName where
	prettyPrint (CSPM.UnQual name) = prettyPrint name

-- *************************************************************************
-- Modules
-- *************************************************************************
instance PrettyPrintable [CSPM.Module] where
	prettyPrint = vcat . map prettyPrint

instance PrettyPrintable CSPM.Module where
	prettyPrint (CSPM.GlobalModule decls) = 
		vcat (punctuate (char '\n') (map prettyPrint decls))

-- *************************************************************************
-- Declarations
-- *************************************************************************
instance PrettyPrintable CSPM.Decl where
	prettyPrint (CSPM.FunBind name matches _) =
			vcat (map (\ (CSPM.Annotated _ _ m) -> ppMatch m) matches)
		where
			ppGroup ps = parens (list (map prettyPrint ps))
			ppMatch (CSPM.Match groups exp) = 
				hang ((prettyPrint name <> hcat (map ppGroup groups))
					 <+> equals)
					tabWidth (prettyPrint exp)			
	prettyPrint (CSPM.PatBind pat exp) =
		hang (prettyPrint pat <+> equals)
			tabWidth (prettyPrint exp)
	prettyPrint (CSPM.Channel ns es) =
		text "channel" <+> list (map prettyPrint ns)
		<+> 
		if length es == 0 then empty
		else text ":" <+> fsep (punctuate (text ".") (map prettyPrint es))
		
	prettyPrint (CSPM.External ns) =
		text "external" <+> list (map prettyPrint ns)
	prettyPrint (CSPM.Transparent ns) =
		text "transparent" <+> list (map prettyPrint ns)
	prettyPrint (CSPM.DataType n dtcs) =
		text "datatype" <+> prettyPrint n <+> text "=" 
			<+> fsep (punctuate (text "|") (map prettyPrint dtcs))
	prettyPrint (CSPM.Assert e1 e2 m) =
		text "assert" <+> prettyPrint e1 <+> prettyPrint m <+> prettyPrint e2
instance PrettyPrintable CSPM.Model where
	prettyPrint (CSPM.Traces) = text "[T="
	prettyPrint (CSPM.Failures) = text "[F="
	prettyPrint (CSPM.FailuresDivergences) = text "[FD="

instance PrettyPrintable CSPM.DataTypeClause where
	prettyPrint (CSPM.DataTypeClause n es) =
		hcat (punctuate (text ".") (prettyPrint n:(map prettyPrint es)))

instance PrettyPrintable CSPM.Pat where
	prettyPrint (CSPM.PConcat p1 p2) =
		prettyPrint p1 <+> text "^" <+> prettyPrint p2
	prettyPrint (CSPM.PDotApp p1 p2) =
		prettyPrint p1 <> text "." <> prettyPrint p2
	prettyPrint (CSPM.PDoublePattern p1 p2) =
		prettyPrint p1 <+> text "@@" <+> prettyPrint p2
	prettyPrint (CSPM.PList patterns) = 
		angles (list (map prettyPrint patterns))
	prettyPrint (CSPM.PLit lit) = prettyPrint lit
	prettyPrint (CSPM.PSet patterns) = 
		braces (list (map prettyPrint patterns))
	prettyPrint (CSPM.PParen pattern) =
		parens (prettyPrint pattern)
	prettyPrint (CSPM.PTuple patterns) = 
		parens (list (map prettyPrint patterns))
	prettyPrint (CSPM.PVar name) = prettyPrint name
	prettyPrint (CSPM.PWildCard) = char '_'

-- *************************************************************************
-- Expressions
-- *************************************************************************
instance PrettyPrintable CSPM.BinaryBooleanOp where
	prettyPrint CSPM.And = text "and"
	prettyPrint CSPM.Or = text "or"
	prettyPrint CSPM.Equals = text "=="
	prettyPrint CSPM.NotEquals = text "!="
	prettyPrint CSPM.GreaterThan = text ">"
	prettyPrint CSPM.LessThan = text "<"
	prettyPrint CSPM.LessThanEq = text "<="
	prettyPrint CSPM.GreaterThanEq = text ">="

instance PrettyPrintable CSPM.BooleanUnaryOp where
	prettyPrint CSPM.Not = text "not"

instance PrettyPrintable CSPM.MathsOp where
	prettyPrint CSPM.Divide = text "/"
	prettyPrint CSPM.Minus = text "-"
	prettyPrint CSPM.Mod = text "%"
	prettyPrint CSPM.Plus = text "+"
	prettyPrint CSPM.Times = text "*"

class Precedence a where
	precedence :: a -> Int
minPrecedence = -1

instance Precedence CSPM.BinaryBooleanOp where
	precedence CSPM.And = 6
	precedence CSPM.Or = 6
	precedence CSPM.Equals = 4
	precedence CSPM.NotEquals = 4
	precedence CSPM.GreaterThan = 4
	precedence CSPM.LessThan = 4
	precedence CSPM.LessThanEq = 4
	precedence CSPM.GreaterThanEq = 4
instance Precedence CSPM.BooleanUnaryOp where
	precedence CSPM.Not = 1
instance Precedence CSPM.MathsOp where
	precedence CSPM.Divide = 2
	precedence CSPM.Mod = 2
	precedence CSPM.Times = 2
	precedence CSPM.Plus = 3
	precedence CSPM.Minus = 3
instance Precedence CSPM.Exp where
	precedence (CSPM.App _ _) = 0
	precedence (CSPM.BooleanBinaryOp op _ _) = precedence op
	precedence (CSPM.BooleanUnaryOp op _) = precedence op
	precedence (CSPM.Concat _ _) = 3
--	precedence (CSPM.DotApp _ _ ) = 3
	precedence (CSPM.ListLength _) = 3
	precedence (CSPM.MathsBinaryOp op _ _) = precedence op
	precedence (CSPM.NegApp _) = 1
	precedence (CSPM.ReplicatedUserOperator _ _ _) = 0
	precedence (CSPM.UserOperator _ _) = 0
	precedence _ = minPrecedence

instance (Precedence b) => Precedence (CSPM.Annotated a b) where
	precedence (CSPM.Annotated _ _ inner) = precedence inner

prettyPrintPrec :: (Precedence a, Precedence b, PrettyPrintable b) => a -> b -> Doc
prettyPrintPrec old new = 
	if precedence old < precedence new then parens (prettyPrint new)
	else prettyPrint new

instance PrettyPrintable CSPM.Exp where	
	prettyPrint (CSPM.App e1 args) = 
		prettyPrint e1 <> parens (list (map prettyPrint args))
	prettyPrint (CSPM.BooleanBinaryOp op e1 e2) =
		prettyPrintPrec op e1 <+> prettyPrint op <+> prettyPrintPrec op e2
	prettyPrint (CSPM.BooleanUnaryOp op e1) =
		prettyPrint op <+> prettyPrintPrec op e1
	prettyPrint (CSPM.Concat e1 e2) =
		prettyPrint e1 <> text "^" <> prettyPrint e2
	prettyPrint (CSPM.DotApp e1 e2) =
		prettyPrint e1 <> text "." <> prettyPrint e2
	prettyPrint (CSPM.If e1 e2 e3) = 
		hang (text "if" <+> prettyPrint e1 <+> text "then") 
			tabWidth (prettyPrint e2)
		$$
		hang (text "else")
			tabWidth (prettyPrint e3)
	prettyPrint (CSPM.Let decls exp) = 
		text "let" $+$
		tabindent (vcat ((map prettyPrint decls))) $+$
		text "within"  $+$
		tabindent (prettyPrint exp)
	prettyPrint (CSPM.ListLength exp) =
		char '#' <> prettyPrint exp
	prettyPrint (CSPM.List exps) = 
		angles (list (map prettyPrint exps))
	prettyPrint (CSPM.ListComp exps stmts) =
		angles (
			list (map prettyPrint exps)
			<+> char '|' 
			<+> list (map prettyPrint stmts))
	prettyPrint (CSPM.ListEnumFrom lb) = 
		angles (prettyPrint lb <> text "...")
	prettyPrint (CSPM.ListEnumFromTo lb ub) = 
		angles (prettyPrint lb <> text "..." <> prettyPrint ub)
	prettyPrint (CSPM.Lit lit) = prettyPrint lit
	prettyPrint (CSPM.MathsBinaryOp op e1 e2) =
		prettyPrintPrec op e1 <+> prettyPrint op <+> prettyPrintPrec op e2
	prettyPrint (CSPM.NegApp exp) = char '-' <> prettyPrintPrec (CSPM.NegApp exp) exp
	prettyPrint (CSPM.Paren e) = parens (prettyPrint e)
	prettyPrint (CSPM.ReplicatedUserOperator n exps stmts) =
		prettyPrint n <> parens (list [angles (
				prettyPrint e
				<+> char '|'
				<+> list (map (\ (CSPM.Annotated _ _ stmt) -> ppStmt stmt) stmts)) 
					| e <- exps])
		where 
			ppStmt (CSPM.Generator pat exp) = 
				sep [prettyPrint pat, 
						text "<-" <+> text "seq" <> parens (prettyPrint exp)]
			ppStmt stmt = prettyPrint stmt

	prettyPrint (CSPM.Set exps) = 
		braces (list (map prettyPrint exps))
	prettyPrint (CSPM.SetComp exps stmts) = 
		braces (
			list (map prettyPrint exps)
			<+> char '|' 
			<+> list (map prettyPrint stmts))
	prettyPrint (CSPM.SetEnum es) =
		braces . bars . list . map prettyPrint $ es
	prettyPrint (CSPM.SetEnumComp es stmts) =
		braces (bars (
			list (map prettyPrint es)
			<+> char '|' 
			<+> list (map prettyPrint stmts)))
	prettyPrint (CSPM.SetEnumFrom lb) =
		braces (prettyPrint lb <> text "..")
	prettyPrint (CSPM.SetEnumFromTo lb ub) =
		braces (prettyPrint lb <> text ".." <> prettyPrint ub)
	prettyPrint (CSPM.Tuple exps) = parens (list (map prettyPrint exps))
	prettyPrint (CSPM.UserOperator opName args) =
		prettyPrint opName <> 
			if length args == 0 then empty
			else parens (list (map prettyPrint args))
	prettyPrint (CSPM.Var qname) = prettyPrint qname

instance PrettyPrintable CSPM.Stmt where
	prettyPrint (CSPM.Generator pat exp) = 
		sep [prettyPrint pat, text "<-" <+> prettyPrint exp]
	prettyPrint (CSPM.Qualifier exp) = 
		prettyPrint exp

instance PrettyPrintable CSPM.Literal where
	prettyPrint (CSPM.Int n) = integer n
	prettyPrint (CSPM.Bool True) = text "true"
	prettyPrint (CSPM.Bool False) = text "false"

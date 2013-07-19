module CSPMDataStructures where

import Control.Monad.Trans
import Data.IORef
import Text.PrettyPrint.HughesPJ
import qualified OpSemDataStructures as OpSem
import Util

newtype ModuleName = ModuleName String deriving (Eq, Show)

newtype Name = Name String deriving (Eq, Ord, Show)

data QualifiedName =
	UnQual Name
	| Qual ModuleName Name
	deriving (Eq, Show)
	
data Literal = 
	Int Integer
	| Bool Bool
	deriving (Eq, Show)
	
data Annotated typeType innerType = 
	Annotated SrcLoc typeType innerType
	
instance Show b => Show (Annotated a b) where
	show (Annotated _ _ inner) = "("++show inner++")"

instance Eq b => Eq (Annotated a b) where
	(Annotated _ _ inner1) == (Annotated _ _ inner2) = inner1 == inner2

removeAnnotation :: Annotated t1 t2 -> t2
removeAnnotation (Annotated _ _ e) = e

-- P = post parsing, TC = post typechecking, An = annotated
type AnModule = Annotated () Module
-- Declarations may bind multiple names
type AnDecl = Annotated PSymbolTable Decl
type AnMatch = Annotated () Match
type AnPat = Annotated () Pat
type AnExp = Annotated PType Exp
type AnStmt = Annotated () Stmt
type AnDataTypeClause = Annotated () DataTypeClause

type PModule = AnModule
type PDecl = AnDecl
type PMatch = AnMatch
type PPat = AnPat
type PExp = AnExp
type PStmt = AnStmt
type PDataTypeClause = AnDataTypeClause

type TCModule = AnModule
type TCDecl = AnDecl
type TCMatch = AnMatch
type TCPat = AnPat
type TCExp = AnExp
type TCStmt = AnStmt
type TCDataTypeClause = AnDataTypeClause

data SrcLoc = 
	SrcLoc String Int Int -- filename, line, column
	| SrcSpan String (Int, Int) (Int, Int)
	deriving (Eq)

instance Show SrcLoc where
	show (SrcLoc fname line column) = fname++":"++show line++":"++show column
	show (SrcSpan fname (line1, col1) (line2, col2)) =
		fname++":"++show line1++":"++show col1++"-"++show line2++":"++show col2
	
-- *************************************************************************
-- Modules
-- *************************************************************************
data Module = 
	Module ModuleName [AnDecl] [AnDecl]	-- internal, exported
	| GlobalModule [AnDecl] -- TODO: add assertions
	deriving (Eq, Show)

-- *************************************************************************
-- Expressions
-- *************************************************************************
data BinaryBooleanOp =
	And 
	| Or 
	| Equals 
	| NotEquals 
	| LessThan 
	| GreaterThan 
	| LessThanEq 
	| GreaterThanEq
	deriving (Eq, Show)
	
data BooleanUnaryOp =
	Not
	deriving (Eq, Show)
	
data MathsOp = 
	Divide | Minus | Mod | Plus | Times
	deriving (Eq, Show)

data Exp =
	App AnExp [AnExp]
	| BooleanBinaryOp BinaryBooleanOp AnExp AnExp
	| BooleanUnaryOp BooleanUnaryOp AnExp
	| Concat AnExp AnExp
	| DotApp AnExp AnExp
	| If AnExp AnExp AnExp
	| Lambda AnPat AnExp
	| Let [AnDecl] AnExp
	| Lit Literal
	| List [AnExp]
	| ListComp [AnExp] [AnStmt]
	| ListEnumFrom AnExp
	| ListEnumFromTo AnExp AnExp
	-- TODO: ListEnumFrom and ListEnumTO - test in FDR
	-- TODO: compare with official CSPM syntax
	| ListLength AnExp
	| MathsBinaryOp MathsOp AnExp AnExp
	| NegApp AnExp
	| Paren AnExp
	| Set [AnExp]
	| SetComp [AnExp] [AnStmt]
	| SetEnum [AnExp]			-- {| |}
	| SetEnumComp [AnExp] [AnStmt]	-- {|c.x | x <- xs|}
	| SetEnumFrom AnExp
	| SetEnumFromTo AnExp AnExp
	| Tuple [AnExp]
	| Var QualifiedName
		
	-- Processes
	| ReplicatedUserOperator Name [AnExp] [AnStmt]
	| UserOperator Name [AnExp]
	
	{-
	| AlphaParallel AnExp AnExp AnExp
	| Event Name [Component]
	| Exception AnExp AnExp
	| ExtChoice AnExp AnExp
	| Interrupt AnExp AnExp
	| Prefix AnExp AnExp
	| RepAlphaParallel [Stmt] AnExp AnExp -- first exp is the alphabet
	| RepExtChoice [AnStmt a] AnExp
	| Rename AnExp [AnStmt a] [AnStmt a]	-- First one should only contain generators
	-}
	
	deriving (Eq, Show)

data Stmt = 
	Generator AnPat AnExp
	| Qualifier AnExp
	deriving (Eq, Show)

{-
data Component = 
	Input Name
	| Output Exp
	| InputRes Name Exp		-- ?x : {0..1}
	deriving (Eq, Show)
-}
	
-- *************************************************************************
-- Declarations
-- *************************************************************************
data Decl = 
	-- Third argument is the annotated type
	FunBind Name [AnMatch] (Maybe [AnExp])
	| PatBind AnPat AnExp
	| Channel [Name] [AnExp]
	| Assert AnExp AnExp Model
	-- TODO: support deadlock freedom etc
	| DataType Name [AnDataTypeClause]
	| External [Name]
	| Transparent [Name]
	deriving (Eq, Show)

data Model = 
	Traces | Failures | FailuresDivergences
	deriving (Eq, Show)

-- TODO: annotate
data DataTypeClause =
	DataTypeClause Name [AnExp]
	deriving (Eq, Show)
	
data Match =
	Match [[AnPat]] AnExp	-- allows for decls like drop(xs,ys)(n)
	deriving (Eq, Show)

data Pat =
	PConcat AnPat AnPat
	| PDotApp AnPat AnPat
	| PDoublePattern AnPat AnPat
	| PList [AnPat]
	| PLit Literal
	| PParen AnPat						-- Need to add PSet
	| PSet [AnPat]
	| PTuple [AnPat]
	| PVar Name
	| PWildCard
	deriving (Eq, Show)


-- *************************************************************************
-- Types
-- *************************************************************************
newtype TypeVar = TypeVar Int deriving (Eq, Show)

data TypeScheme =
	ForAll [(TypeVar, [Constraint])] Type
	deriving (Eq, Show)
	
data Constraint =
	Eq | Ord
	deriving (Eq, Ord, Show)
	
data Type =
	TVar TypeVarRef
	| TInt
	
	| TFunction [Type] Type	-- Arguments to result type
	| TSeq Type
	
	| TList Type Type		-- The second type should either be a TVar or TList
	| TListEnd			-- or a TEmptyList
	| TPolyList TypeVarRef	-- Polymorphic list thingy - should be a TypeVarRef
	
	| TBool
	| TSet Type
	| TTuple [Type]
	
	| TChannel Type			-- Should be a TList
	| TDotable Type Type	-- TDotted a b means that this type can be dotted
							-- with an a to yield a b
	| TDatatypeClause Name [Type]	
			-- Op_Parallel.T1.T2.T3 :: TDatatypeClause "Operators" [T1,T2,T3]
	
	| TProc
	deriving (Eq, Show)

data TypeVarRef = 
	TypeVarRef TypeVar [Constraint] PType
	deriving Eq

instance Show TypeVarRef where
	show (TypeVarRef tv cs _) = "TypeVarRef "++show tv ++ show cs


opSemTypeToCSPMType :: OpSem.Type -> Type
opSemTypeToCSPMType (OpSem.TEvent) = TChannel TListEnd
opSemTypeToCSPMType (OpSem.TOnProcess _) = TProc
opSemTypeToCSPMType (OpSem.TOffProcess _) = TProc
opSemTypeToCSPMType (OpSem.TSet t) = TSet (opSemTypeToCSPMType t)
opSemTypeToCSPMType (OpSem.TTuple ts) = TTuple (map opSemTypeToCSPMType ts)

opSemOperatorNameToCSPMName (OpSem.Name s) = Name s


type SymbolTable = PartialFunction Name TypeScheme
type PType = IORef (Maybe Type)
type PTypeScheme = IORef (Maybe TypeScheme)
type PSymbolTable = IORef SymbolTable

readPType :: (MonadIO m) => PType -> m (Maybe Type)
readPType ioref = 
	do
		t <- liftIO $ readIORef ioref
		return t
setPType :: (MonadIO m) => PType -> Type -> m ()
setPType ioref t = liftIO $ writeIORef ioref (Just t)
freshPType :: (MonadIO m) => m PType
freshPType = liftIO $ newIORef Nothing

readPSymbolTable :: (MonadIO m) => PSymbolTable -> m SymbolTable
readPSymbolTable ioref = 
	do
		t <- liftIO $ readIORef ioref
		return t
setPSymbolTable :: (MonadIO m) => PSymbolTable -> SymbolTable -> m ()
setPSymbolTable ioref t = liftIO $ writeIORef ioref t
freshPSymbolTable :: (MonadIO m) => m PSymbolTable
freshPSymbolTable = liftIO $ newIORef []


readPTypeScheme :: (MonadIO m) => PTypeScheme -> m (Maybe TypeScheme)
readPTypeScheme ioref = 
	do
		t <- liftIO $ readIORef ioref
		return t
setPTypeScheme :: (MonadIO m) => PTypeScheme -> TypeScheme -> m ()
setPTypeScheme ioref t = liftIO $ writeIORef ioref (Just t)
freshPTypeScheme :: (MonadIO m) => m PTypeScheme
freshPTypeScheme = liftIO $ newIORef Nothing



prettyPrintTypeScheme :: TypeScheme -> Doc
prettyPrintTypeScheme (ForAll ts t) =
	(if length ts > 0 then
		text "forall" <+> hsep (punctuate comma 
							[parens (hsep (punctuate comma (map ppConstraint cs)) <+>
								char (apply vmap n)) | (TypeVar n, cs) <- ts]) 
		<+> text ":"
	else
		empty)
		 <+> prettyPrintType vmap t
	where
		ppConstraint Eq = text "Eq"
		ppConstraint Ord = text "Ord"
		vmap = zip (map (\ (TypeVar n, _) -> n) ts) ['a'..'z']
prettyPrintType :: PartialFunction Int Char -> Type -> Doc
prettyPrintType vmap (TVar (TypeVarRef (TypeVar n) cs ioref)) = 
	case safeApply vmap n of
		Just c	-> char c
		Nothing	-> int n
prettyPrintType vmap (TFunction targs tr) = 
	parens (hsep (punctuate comma (map (prettyPrintType vmap) targs)))
	<+> text "->" <+> prettyPrintType vmap tr
prettyPrintType vmap (TSeq t) =
	char '<' <> prettyPrintType vmap t <> char '>'
prettyPrintType vmap (TSet t) =
	char '{' <> prettyPrintType vmap t <> char '}'
prettyPrintType vmap (TTuple ts) =
	parens (hsep (punctuate comma (map (prettyPrintType vmap) ts)))
prettyPrintType vmap (TDotable t1 t2) =
	text "DotableWith" <+> prettyPrintType vmap t1 <+> text "yielding" 
	<+> prettyPrintType vmap t2
prettyPrintType vmap (TChannel TListEnd) =
	text "Event"
prettyPrintType vmap (TChannel tl) =
	let 
		chanType TListEnd = []
		chanType (TPolyList tv) = [TPolyList tv]
		chanType (TList t1 t2) = t1:chanType t2

		ts = chanType tl
	in
		text "Channel" <+> 
			brackets (hsep (punctuate comma (map (prettyPrintType vmap) ts)))
prettyPrintType vmap (TListEnd) = text "Event"
prettyPrintType vmap (TList t1 t2) = 
	prettyPrintType vmap t1 <> comma <+> prettyPrintType vmap t2
prettyPrintType vmap (TPolyList (TypeVarRef (TypeVar n) cs ioref)) = 
	text "PolyList" <+> char (apply vmap n)
prettyPrintType vmap (TDatatypeClause (Name n) []) = text n
prettyPrintType vmap (TDatatypeClause (Name n) ts) =
	text "DataTypeClause" <+> text n <+>
	brackets (hsep (punctuate comma (map (prettyPrintType vmap) ts)))

prettyPrintType vmap (TBool) = text "Bool"
prettyPrintType vmap (TInt) = text "Int"
prettyPrintType vmap (TProc) = text "Proc"
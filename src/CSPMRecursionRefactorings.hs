{-# LANGUAGE QuasiQuotes #-}

module CSPMRecursionRefactorings where

import Control.Monad.State
import Data.Graph

import CSPMDataStructures
import CSPMTypeChecker.TCCommon
import CSPMTypeChecker.TCDependencies
import CSPMTypeChecker.TCModule
import CSPMTypeChecker.TCMonad
import CSPMParser
import CSPMPrettyPrinter
import Data.List (intersect)
import qualified OpSemDataStructures as OpSem
import OpSemRules
import OpSemParser
import OpSemTypeChecker

import Util

isProcessTypeScheme :: TypeScheme -> Bool
isProcessTypeScheme (ForAll _ t) = isProcessType t
isProcessType :: Type -> Bool
isProcessType (TFunction _ b) = isProcessType b
isProcessType (TTuple ts) = or $ map isProcessType ts   
    -- TODO: I think if this occrs we have to object as it is too hard
    -- to use WrapThread
isProcessType TProc = True
isProcessType _ = False

unWrappedName :: Name -> Name
unWrappedName (Name n) = (Name (n++"_UNWRAPPED"))

dataTypeMember :: Name -> AnExp
dataTypeMember (Name n) = an (Var (UnQual (Name ("Proc_"++n))))

an :: b -> Annotated a b
an = Annotated (error "inserted srcloc") (error "inserted annotation") 

listToDotApp :: [AnExp] -> AnExp
listToDotApp (e1:[]) = e1
listToDotApp (e1:es) = an (DotApp e1 (listToDotApp es))

listToPatDotApp :: [AnPat] -> AnPat
listToPatDotApp (e1:[]) = e1
listToPatDotApp (e1:es) = an (PDotApp e1 (listToPatDotApp es))
    
declHasBounds :: TCDecl -> Bool
declHasBounds (Annotated _ _ (FunBind _ _ Nothing)) = False
declHasBounds _ = True

computeProcessGraph :: [TCDecl] -> TypeCheckMonad [Name]
computeProcessGraph decls =
    do
        let declMap = zip decls [0..]
        varToDeclIdMap <- 
            concatMapM (\ decl -> 
                do
                    namesBound <- namesBoundByDecl decl
                    return [(n, apply declMap decl) | n <- namesBound]) decls
        
        procNames <- concatMapM (\ decl @ (Annotated _ psymtable _) ->
            do
                symtable <- readPSymbolTable psymtable
                liftM (map fst) (filterM (\ (n,t) ->
                    do
                        tc <- compressTypeScheme t
                        return $ isProcessTypeScheme tc) symtable)
            ) decls
        
        mapM_ prebindDataType 
            [DataType n ms | DataType n ms <- map removeAnnotation decls]
        
        -- Map from decl id -> [decl id] meaning decl id depends on the list of
        -- ids
        declDeps <- mapM (\ decl -> 
                do
                    fvsd <- dependencies decl
                    let fvs' = intersect fvsd procNames
                    return (apply declMap decl, mapPF varToDeclIdMap fvs')
                    ) decls
        
        -- Edge from n -> n' iff n uses n'
        let sccs = stronglyConnComp [(id, id, deps) | (id, deps) <- declDeps]
        let recursiveDeclIds = 
                concatMap (\ scc ->
                        case scc of
                            AcyclicSCC _    -> []
                            CyclicSCC vs    -> vs) sccs
        let boundedRecursiveDeclIds = 
                [id | id <- recursiveDeclIds, declHasBounds (apply (invert declMap) id)]
        let recursiveNames = 
                concatMap (applyRelation (invert varToDeclIdMap)) boundedRecursiveDeclIds
        debugOutput ("Recursive processes: "++show recursiveNames)
        
        return recursiveNames
    
data TransformMonadState = TransformMonadState {
        recursiveNames :: [[Name]],
        operatorTypeMap :: PartialFunction OpSem.Name [OpSem.Type],
        isRecursive :: Bool,
        recursiveCallsAllowed :: Bool   -- rule 0 below
    }
type TransformMonad = StateT TransformMonadState TypeCheckMonad

runTransformMonad :: TransformMonad a -> TypeCheckMonad a
runTransformMonad m = 
    liftM fst (runStateT m (TransformMonadState [] [] False True))

getOperatorType :: Name -> TransformMonad [OpSem.Type]
getOperatorType (Name n) =
    do
        m <- gets operatorTypeMap
        return $ apply m (OpSem.Name n)
setOperatorTypeMap :: PartialFunction OpSem.Name [OpSem.Type] -> TransformMonad ()
setOperatorTypeMap typeMap = modify (\ s -> s { operatorTypeMap = typeMap })

isRecursiveName :: Name -> TransformMonad Bool
isRecursiveName n =
    do
        names <- gets recursiveNames
        return $ or (map (elem n) names)
addRecursiveNames :: [Name] -> TransformMonad a -> TransformMonad a
addRecursiveNames ns m = 
    do 
        modify (\ s -> s { recursiveNames = ns:(recursiveNames s) })
        ret <- m
        modify (\ s -> s { recursiveNames = tail (recursiveNames s) })
        return ret
setIsRecursive :: Bool -> TransformMonad a -> TransformMonad a
setIsRecursive b m = 
    do
        oldv <- isCurrentlyRecursive
        modify (\ s -> s { isRecursive = b })
        ret <- m
        modify (\ s -> s { isRecursive = oldv })
        return ret
isCurrentlyRecursive :: TransformMonad Bool
isCurrentlyRecursive = gets isRecursive

allowRecursiveCalls :: TransformMonad Bool
allowRecursiveCalls = gets recursiveCallsAllowed
setAllowRecursiveCalls :: Bool -> TransformMonad a -> TransformMonad a
setAllowRecursiveCalls b m =
    do
        oldv <- allowRecursiveCalls
        modify (\ s -> s { recursiveCallsAllowed = b })
        ret <- m
        modify (\ s -> s { recursiveCallsAllowed = oldv })
        return ret


class Transformable a where
    transform :: a -> TransformMonad a
instance Transformable a => Transformable [a] where
    transform = mapM transform
instance Transformable b => Transformable (Annotated a b) where
    transform (Annotated srcloc b inner) =
        do
            inner' <- transform inner
            return $ Annotated srcloc b inner'

transformModules :: OpSem.OpSemDefinition -> [TCModule] -> TransformMonad [TCModule]
transformModules opSemDef [Annotated b c (GlobalModule ds)] =
    do
        let ops = OpSem.operators opSemDef
        let operatorTypeMap = 
                [(OpSem.opFriendlyName op, map snd (OpSem.opArgs op)) | op <- ops]
        setOperatorTypeMap operatorTypeMap
        ds' <- transformDecls ds
        return [Annotated b c (GlobalModule ds')]

transformDecls :: [TCDecl] -> TransformMonad [TCDecl]
transformDecls ds = 
    do
        ns <- lift (computeProcessGraph ds)
        addRecursiveNames ns (do
                declRecTypes <- mapM (\ (Annotated n t d) -> 
                        do
                            (ds', rt) <- transformDecl d
                            return ([Annotated n t d' | d' <- ds'], rt)) ds
                let (decls', recTypes) = unzip declRecTypes
                let hasRecTypes = length [0 | Just _ <- recTypes] /= 0
                let procDataType = 
                        if hasRecTypes then
                            an $ DataType (Name "ProcArgs")
                                    [an $ DataTypeClause (Name ("Proc_"++s)) es 
                                        | Just (Name s, es, isPat) <- recTypes]
                        else
                            an $ PatBind (an $ PVar (Name "ProcArgs")) (an $ Set [])
                let getProc = an $ 
                        FunBind (Name "GetProc")
                            [let
                                argNames = ["arg_"++show    i | i <- [1..(length es)]]
                                argPats = [an $ PVar (Name i) | i <- argNames]
                                argExps = [an $ Var (UnQual (Name i)) | i <- argNames]
                                arg = (an $ (PVar (Name ("Proc_"++s)))):argPats
                                exp = if isPat then Var (UnQual (Name $ s++"_UNWRAPPED"))
                                        else App (an $ Var (UnQual 
                                                        (Name $ s++"_UNWRAPPED")))
                                                    argExps
                            in
                                an $ Match [[listToPatDotApp arg]]
                                            (an exp)
                                | Just (Name s, es, isPat) <- recTypes]
                            Nothing
                if hasRecTypes then
                        return $ procDataType:getProc:(concat decls')
                    else return $ procDataType:concat decls')

makeWrapThread :: Name -> [AnExp] -> AnExp
makeWrapThread n args =
    an (App (an (Var (UnQual (Name "WrapThread")))) 
        [listToDotApp $ (dataTypeMember n):args])

transformDecl :: Decl -> TransformMonad ([Decl], Maybe (Name, [AnExp], Bool))
-- TODO: what about functions that return tuples?
{-
    SomeFunc(count) = let (_, P') = SomeFunc(count) in (count, a -> P')
-}
transformDecl (FunBind n ms annotTyp) =
    do
        b <- isRecursiveName n
        if b then setIsRecursive True (
            do
                ms' <- transform ms
                let args = head [ps | Match [ps] e <- map removeAnnotation ms]
                let argCount = length args
                let argList = map (\ s -> "arg_"++show s) [1..argCount]
                let decls = [FunBind (unWrappedName n) ms' annotTyp, 
                        FunBind n [an $
                            Match 
                                -- TODO: currying
                                [[an $ PVar (Name s) | s <- argList]]
                                (makeWrapThread n
                                    (map (\ s -> an (Var (UnQual (Name s)))) 
                                        argList))] annotTyp]
                case annotTyp of
                    Just es -> return (decls, Just (n, es, False))
                    Nothing -> return (decls, Nothing))
            else setIsRecursive False (
                do
                    ms' <- transform ms
                    return ([FunBind n ms' annotTyp], Nothing))
-- TODO: maybe need to prohibit patterns that contain processes??
{-
    (P, count) = (a -> P, count)
-}
transformDecl (PatBind (p @ (Annotated _ _ (PVar n))) e) =
    do
        b <- isRecursiveName n
        if b then setIsRecursive True (
            do
                e' <- transform e
                let decls = [PatBind (an $ PVar (unWrappedName n)) e',
                            PatBind p (makeWrapThread n [])]
                return (decls, Just (n, [], True)))
            else setIsRecursive False (
                do
                    e' <- transform e
                    return ([PatBind p e'], Nothing))
transformDecl (PatBind pat e) = error ""
transformDecl (Channel ns es) = return ([Channel ns es], Nothing)
transformDecl (DataType n dtcs) = return ([DataType n dtcs], Nothing)
transformDecl (External ns) = return ([External ns], Nothing)
transformDecl (Transparent ns) = return ([Transparent ns], Nothing)
transformDecl (Assert e1 e2 m) = return ([Assert e1 e2 m], Nothing)

instance Transformable Match where
    transform (Match ps e) =
        do
            e' <- transform e
            return $ Match ps e'
instance Transformable Exp where
    -- TODO: general application
    transform (App e es) = 
        do
            es' <- transform es
            case removeAnnotation e of
                Var (UnQual n) -> do
                    isRecursive <- isRecursiveName n
                    isCurrentlyRecursive <- isCurrentlyRecursive
                    return (
                        if isRecursive && isCurrentlyRecursive then
                            App (an (Var (UnQual (Name "CallProc")))) 
                                [listToDotApp $ (dataTypeMember n):es']
                        else App (an (Var (UnQual n))) es') -- TODO
    transform (BooleanBinaryOp op e1 e2) =
        do
            e1' <- transform e1
            e2' <- transform e2
            return $ BooleanBinaryOp op e1' e2'
    transform (BooleanUnaryOp op e) =
        do
            e' <- transform e
            return $ BooleanUnaryOp op e'
    transform (Concat e1 e2) =
        do
            e1' <- transform e1
            e2' <- transform e2
            return $ Concat e1' e2'
    transform (DotApp e1 e2) =
        do
            e1' <- transform e1
            e2' <- transform e2
            return $ DotApp e1' e2'
    transform (If e1 e2 e3) = 
        do
            e1' <- transform e1
            e2' <- transform e2
            e3' <- transform e3
            return $ If e1' e2' e3'
    transform (Lambda p e) = -- TODO: need to prohibit proc lambda exps
        do
            e' <- transform e
            return $ Lambda p e'
    transform (Let ds e) = 
        do
            namesBound <- lift (concatMapM namesBoundByDecl ds)
            recursiveNames <- lift (computeProcessGraph ds)
            if intersect namesBound recursiveNames == [] then (
                do
                    e' <- transform e
                    -- We don't transform ds as it does not contain any
                    -- recursive terms. TODO: recursive anyway
                    return $ Let ds e')
                else
                    error "let contains recursive names"
        -- TODO: compute process graph
        -- Or, possibly we remove all Let expressions and have one big 
        -- namespace, this would be ugly but maybe the only easy way to get 
        -- around the problem where we are rewriting
    transform (Lit lit) = return $ Lit lit
    transform (List es) =
        do
            es' <- transform es
            return $ List es'
    transform (ListComp es stmts) =
        do
            es' <- transform es
            stmts' <- transform stmts
            return $ ListComp es' stmts'
    transform (ListEnumFromTo e1 e2) =
        do
            e1' <- transform e1
            e2' <- transform e2
            return $ ListEnumFromTo e1' e2'
    transform (ListLength e) =
        do
            e' <- transform e
            return $ ListLength e'
    transform (MathsBinaryOp op e1 e2) =
        do
            e1' <- transform e1
            e2' <- transform e2
            return $ MathsBinaryOp op e1' e2'
    transform (NegApp e) = 
        do
            e' <- transform e
            return $ NegApp e
    transform (Paren e) =
        do
            e' <- transform e
            return $ Paren e'
    transform (ReplicatedUserOperator n es stmts) =
        do
            es' <- transform es
            stmts' <- transform stmts
            return $ ReplicatedUserOperator n es' stmts'
    transform (Set es) =
        do
            es' <- transform es
            return $ Set es'
    transform (SetComp es stmts) =
        do
            es' <- transform es
            stmts' <- transform stmts
            return $ SetComp es' stmts'
    transform (SetEnum es) =
        do
            es' <- transform es
            return $ SetEnum es'
    transform (SetEnumComp es stmts) =
        do
            es' <- transform es
            stmts' <- transform stmts
            return $ SetEnumComp es' stmts'
    transform (SetEnumFromTo e1 e2) =
        do
            e1' <- transform e1
            e2' <- transform e2
            return $ SetEnumFromTo e1' e2'
    transform (Tuple es) =
        do
            es' <- transform es
            return $ Tuple es'
    transform (Var (UnQual n)) =
        do
            isRecursive <- isRecursiveName n
            isCurrentlyRecursive <- isCurrentlyRecursive
            return (
                if isRecursive && isCurrentlyRecursive then
                    App (an (Var (UnQual (Name "CallProc")))) [dataTypeMember n]
                else Var (UnQual n))
    transform (UserOperator opname es) = 
        do
            opType <- getOperatorType opname
            es' <- zipWithM transformOpArg opType es
            return $ UserOperator opname es'
        where
            transformOpArg (OpSem.TOnProcess OpSem.InfinitelyRecursive) e =
                setIsRecursive False (transform e)
            transformOpArg (OpSem.TOffProcess OpSem.InfinitelyRecursive) e =
                setIsRecursive False (transform e)
            transformOpArg _ e = transform e
    transform x = error (show x ++ "is not supported")
instance Transformable Stmt where
    transform (Generator p e) = 
        do
            e' <- transform e
            return $ Generator p e'
    transform (Qualifier e) = 
        do
            e' <- transform e
            return $ Qualifier e'

testHarness :: String -> IO ()
testHarness exp = do
    r <- runTyger $
        do
            ops <- parseOpSemFile "../Examples/CSP.opsem"
            opSemDef <- typeCheckOperators ops
            
            let operatorSyntaxMap = 
                    [(OpSem.opFriendlyName op, OpSem.opParsingInformation op) 
                        | op <- OpSem.operators opSemDef]
            let operatorTypeMap = 
                    [(OpSem.opFriendlyName op, map snd (OpSem.opArgs op)) 
                        | op <- OpSem.operators opSemDef]
            
            (parsed @ [Annotated _ _ (GlobalModule ds)]) <- 
                stringParser exp (OpSem.operators opSemDef)
            toPrint <- runTypeChecker (
                do
                    typeCheckWrapper parsed operatorTypeMap
                    runTransformMonad (
                        setOperatorTypeMap operatorTypeMap >> transformDecls ds))
            debugOutput (unlines (map (show . prettyPrint) toPrint))
    case r of
        Left err -> putStrLn (show err)
        Right v -> return ()
                                    
-- TODO: sort out error message when changing Test2 to a false call
-- TODO: should bind original name to wrapped version
example1 = [multilineLiteral|
    channel a, b, c

--  Test(n) = Test2(n)

--  Test2(n) = 
--      if n < 10 then a -> Test2(n+1)
--      else CSPSTOP

--  Test3(n) =
--      if n < 10 then a -> Test3(n+1)
--      else Test(n)
    
--  Test4 = if false then a -> a -> a -> a -> CSPSTOP else CSPSTOP
    
    -- This is a pattern bind - TODO
    P = a -> P
    
--  Test5(0) = CSPSTOP
--  Test5(n) = Test3(n) [ {| a|} || {| a|} ] Test5(n)
    
--  Test6(n) = Test5(n) \ {|a|}

    -- Problem: this example shows why we need to rewrite
    --Test7() = a -> Test8() [] Test8()
    --Test8() = b -> Test7() [] a -> Test8() [] Test9()
    --Test9() = c -> Test9()
    
{-  Test10 =
        let
            Test(n) = a -> Test(n+1)
        within
            Test(0)
-}          
    Test11(x) = a -> Test11(x) [] b -> Test12(x)
    Test12(x) = b -> Test13(x)
    Test13(x) = c -> Test13(x) [] b -> Test11(x)
    
    -- TODO: pre-defined Events in functional language
    
    RUN :: (Set({| a, b, c |})) -> Proc
    RUN(A) = [] a : A @ a -> RUN(A)
    R = a -> R [] (Q [ {| b |} || {| a |}] RUN({| a |}))
    Q = a -> Q
|]

diningPhils = [multilineLiteral|
N = 4
ID = {0..N}
mplus(x,y) = (x + y) % (N+1)

channel pickup, putdown : ID.ID
channel sitdown, eat, getup : ID

-- Original process
Philosopher :: ({0..N}) -> Proc
Philosopher(id) =
    sitdown.id -> pickup.id.id -> pickup.id.mplus(id,1) -> eat.id -> 
    putdown.id.mplus(id,1) -> putdown.id.id -> getup.id -> Philosopher(id)

Fork :: ({0..N}) -> Proc
Fork(id) = 
    [] phil : {id, mplus(id,1)} @ pickup.phil.id -> putdown.phil.id -> Fork(id)
AlphaFork(id) = 
    {pickup.id.id, putdown.id.id, pickup.mplus(id,1).id, putdown.mplus(id,1).id}

System = 
    (|| id : {0..N} @ [AlphaFork(id)] Fork(id))

|]

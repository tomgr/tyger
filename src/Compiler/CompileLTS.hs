module Compiler.CompileLTS where

import CSPMDataStructures as CSP
import OpSemDataStructures as OpSem

data CompilerState = CompilerState {
		
		nextStateId :: Int
	}
	deriving Show

{- the idea is to evaluate the CSPM (or any other entry language) into the 
	following. For example:
		
		Count(0) = up -> Count(1)
		Count(n) = n < N & up -> Count(n+1) [] down -> Count(n-1)
		
		assert Count(0) [T= ...
		
		is compiled to:
			
			Count0 = Prefix(up, Count1)
			Count1 = ExternalChoice(Count1_0,Count1_1)
			Count1_0 = Prefix(up,Count2)
			Connt1_1 = Prefix(down, Count0)
			...
			
		We do this re-writing to make compilation of the LTS very fast.
		This is because we can effeciently implement a map from process name
		to state.
		
		However, this will probably mean that we use more memory than FDR since
		we have to keep the above (potentially huge data structure) in memory
		until the LTS is constructed. (For large examples consider the CSPM
		produced by this program: the processes are very very large).
		
		A compromise might be to implement some kind of class so that the
		above data structure can be computed lazily, this would 
		avoid the issue of memory usage (we would have to make sure it was
		all tail recursive). It might be hard to make everything have a unique
		number. Though this could be done quite simply by a monad i expect.
		
		class Compilable a where
			evaluateToValue :: a -> Value
			evaluateToOperatorApp :: a -> (OpName, [a], Ident)
				-- last parameter is Ident of this OperatorApp
				
		compileLTS p =
			do
				(opname, args, id) <- evaluateToOperatorApp p
				s <- addState id
				-- TODO: what if we create states twice? Is this possible?
				vs <- mapM (if isProcessType then 
								-- TODO: could also be a process name
								compileLTS
								-- this returns a state, we need to
								-- be careful though with finalized vs.
								-- non-finalized operators
							else
								evaluateToValue 
							) args
				ltsForOperator s opName vs
				return s
				
		ltsForOperator s opName vs =
			-- here we do things like:
		
	we should use:
		http://hackage.haskell.org/package/judy
	for the Ident -> Name map.
	
	we also need a high-level and low-level implementation of every operator
	so that we can effeciently test the RHS.
	
data Value =
	VProcessName Ident
	| VSet [Value]
	| VEvent Event
	
type AbstractFile = [ProcessDefn]

data ProcessDefn =
	OpApp OpName [Value]
-}
	

type State =
type StateIdent = 
type Edge =

type Event =

isTauTransition :: Edge -> Bool

getLabel :: Edge -> Event


getState :: CSPM.Exp -> CompilationMonad State

outgoingEdgesFromState :: State -> CompilationMonad [Edge]

insertStateWithResultingStates :: StateIdent -> [State] -> CompilationMonad State



compileLTS :: Exp -> CompilationMonad ()
compileLTS (CSP.UserOperator opName opArgs) =
	do
		op <- getOperator opName
		compileLTSForOperator


compileLTSForOperator :: OpSem.Operator -> [CSP.Exp] -> CompilationMonad ()
compileLTSForOperator (OpSem.Operator name opArgs rules _) args =
	let
		-- assume sc is true for now
		-- we also only deal with low level operators for now 
		-- (i.e. we assume every operators' result is the identity on something)
		compileLTSForRule (InductiveRule pres 
			(Performs (OperatorApp _ es) ev (OperatorApp (Name "Identity") [e])) 
			sideCondition) =
			
			do
				
	do
		

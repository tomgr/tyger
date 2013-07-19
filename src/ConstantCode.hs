{-# LANGUAGE QuasiQuotes #-} 
module ConstantCode where
import Util

-- ***************************************************************************
-- ***************************************************************************
operatorModuleNotExported = [multilineLiteral| 
-- Gives the set of all sequences of type t of length <= length
FinSeq(t, length) = 
	let
		Gen(0) = {<>}
		Gen(n) = {<x>^xs, xs | x <-t, xs <- Gen(n-1)}
	within
		Gen(length)
FinSeq'(t, length) = 
	let
		Gen(0) = <<>>
		Gen(n) = concat(< <<x>^xs,xs> | xs <- Gen(n-1), x <- t>)
	within
		Gen(length)

powerSeq(<>) = <<>>
powerSeq(<x>^xs) = <<x>^ys, ys | ys <- powerSeq(xs)>

zip(<>, _) = <>
zip(_, <>) = <>
zip(<x>^xs, <y>^ys) = <(x,y)>^zip(xs, ys)

flatmap(f,<>) = <>
flatmap(f,<x>^xs) = f(x)^flatmap(f,xs)

remdups(x) =
	let 
		iter(<>,X) = <>
		iter(<x>^xs,X) =
			if member(x,X) then iter(xs,X)
			else <x>^iter(xs,union(X,{x}))
	within
		iter(x, {})

foldr(f, e, <>) = e
foldr(f, e, <x>^xs) = f(x, foldr(f, e, xs))

foldl(f, e, <>) = e
foldl(f, e, <x>^xs) = foldl(f, f(e, x), xs)

-- *********************************************************************
-- Partial functions
-- *********************************************************************

functionDomain(f) = {x | (x,_) <- f}
functionDomainSeq(f) = <x | (x,_) <- f>
functionImage(f) = {x | (_,x) <- f}
functionImageSeq(f) = <x | (_,x) <- f>
identityFunction(domain) = {(x,x) | x <- domain}
identityFunctionSeq(domain) = <(x,x) | x <- domain>
invert(f) = {(a,b) | (b,a) <- f}
invertSeq(f) = <(a,b) | (b,a) <- f>

composeFunctions(fs1, fs2) = {(a, apply(fs1, b)) | (a, b) <- fs2}
composeFunctionsSeq(fs1, fs2) = <(a,applySeq(fs1,b)) | (a,b) <- fs2>

apply(f, x) = 
	let extract({x}) = x
	within extract({a | (x', a) <- f, x == x'})
	
applySeq(f, x) = 
	let extract(<x>) = x
	within
		extract(<a | (x', a) <- f, x == x'>)

mapOverSet(f, X) =
	{apply(f, x) | x <- X}
mapOverSeq(f, <>) = <>
mapOverSeq(f, <x>^xs) = <applySeq(f,x)>^mapOverSeq(f,xs)

seqDiff(xs, ys) = <x | x <- xs, not elem(x,ys)>
seqInter(xs, ys) = <x | x <- xs, elem(x, ys)>
seqUnion(xs, ys) = remdups(xs^ys)

-- *********************************************************************
-- Semantics Calculation
-- *********************************************************************

-- Returns a partial function from (op, onProcMap, procCount, offProcMap) to
-- the possible internal events
InternalEventsFromOperator(op, onProcMap, procCount, offProcMap, nextId, doneCalls) =
	let
		-- The sequence of all possible events that each rule gives
		(possibleEvents, nextId')  = 
			let
				process((events, nextId), 
						rule @@ (phi, x, mu, f, xi, chi, discards)) =
					let
						procsToDiscard = 
							mapOverSeq(onProcMap, discards)
						procEvents =
							<(applySeq(onProcMap, p), e) | (p, e) <- phi>
						newProcs = composeFunctionsSeq(offProcMap, f)
						thisEvent = 
							(rule, procEvents, x, procsToDiscard, procCount, newProcs)
					within
						(<(nextId,thisEvent)>^events, nextId+1)
			within
				foldl(process, (<>, nextId), Rules(op))

		-- The sequence of recursive calls to this function to make,
		-- it contains no duplicates and no items in doneCalls.
		recursiveCallsToMake = 
			seqDiff(
				remdups(<
					let					
						newOnProcMap =
							composeFunctionsSeq(
								concat(<onProcMap, 
										identityFunctionSeq(
											<procCount..procCount+newProcCount-1>)
										>),
										xi)
						newProcCount = procCount + length(f)
						newOffProcMap =
							composeFunctionsSeq(offProcMap, chi)
					within
						(mu, newOnProcMap, newProcCount, newOffProcMap)
					| (phi, x, mu, f, xi, chi, discards) <- Rules(op), op != mu>),
				doneCalls)
		
		doneCalls' = doneCalls^recursiveCallsToMake
		
		(recursiveEvents, recursiveDiscardableArgs, nextId'') = 
			let
				process((events, discardableArgs, nextId), (mu, xi, m, chi)) =
					let
						(events', discardableArgs', nextId') =
							InternalEventsFromOperator(mu, xi, m, chi, nextId, doneCalls')
					within
						(events'^events, remdups(discardableArgs'^discardableArgs), nextId')
			within
				foldl(process, (<>, <>, nextId'), recursiveCallsToMake)
	within
		(<((op, onProcMap, procCount, offProcMap), possibleEvents)>^recursiveEvents, 
			remdups(mapOverSeq(onProcMap, DiscardableArgs(op))^recursiveDiscardableArgs),
			nextId'')
|] 


-- ***************************************************************************
-- ***************************************************************************
operatorModuleExported = [multilineLiteral|
-- Allows the rules to specify a tau transition
channel tau
-- Let a process be turned off
channel off
-- Represents a primed event; used to let processes turn themselves off
channel prime : SystemEvents
-- TODO: calculate upper bound
channel renamed : {0..20000}

-- *********************************************************************
-- Main Simulator Function
-- *********************************************************************
--	startOperator	operator the process starts in
--	onProcesses		sequence of processes that are initially on
--  offProcesses	sequence of processes that are initially off
Operator(startOperator, onProcesses, offProcesses) =
	let
		OnProcessCount = length(onProcesses)
		OnProcesses = 
			zip(<0..OnProcessCount - 1>, onProcesses)
		OffProcessCount = length(offProcesses)
		OffProcesses = 
			zip(<(-OffProcessCount)..-1>, offProcesses)
		
		InternalEvents =
			concat(<es | (id, es) <- InternalEventsByOperator>)
		
		(InternalEventsByOperator, discardableProcs, _) = 
			InternalEventsFromOperator(startOperator, 
				identityFunctionSeq(<0..OnProcessCount-1>), OnProcessCount, 
				identityFunctionSeq(<(-OffProcessCount)..-1>),
				0, <>)
			
		RenamingsForProc(id) =
			let
				calc((rid, (rule, procs,b,discards,m,f))) =
					if elem(id, functionDomainSeq(procs)) then
						if elem(id,discards) then
							<(prime.applySeq(procs, id), rid)>
						else
							<(applySeq(procs, id), rid)>
					else
						if elem(id,discards) then
							<(off, rid)>
						else <>
			within
				flatmap(calc,InternalEvents)
	
		Process(proc, id) = 
			(if elem(id, discardableProcs) then
				explicate((proc[[a <- prime.a, a <- a | a <- SystemEvents]] 
				[| {| prime |} |> STOP)
				/\ off -> STOP)
			else
				proc)
			[[a <- renamed.b | (a,b) <- set(RenamingsForProc(id))]]
		
		-- onProcMap	Function from current process id to actual process id
		-- procCount	Current number of on processes
		-- offProcMap	Function from current off process id to actual off
		--				process ids
		Reg(currentOperator, onProcMap, procCount, offProcMap) = 
			[] (rid, (rule @@ (phi, x, mu, f, xi, chi, discards), _, _, _, _, _)) : 
				set(applySeq(InternalEventsByOperator, 
							(currentOperator, onProcMap, procCount, offProcMap))) @
				let
					procsToDiscard = 
						mapOverSeq(onProcMap, discards)
					procEvents =
						<(applySeq(onProcMap, p), e) | (p, e) <- phi>
					newOnProcMap =
						composeFunctionsSeq(concat(<onProcMap, 
											   identityFunctionSeq(<procCount..procCount+newProcCount-1>)>)
										 , xi)
					newProcCount = procCount + length(newProcs)
					newProcs = composeFunctionsSeq(offProcMap, f)
					newOffProcMap =
						composeFunctionsSeq(offProcMap, chi)
				within
					renamed.rid -> 
						if length(newProcs) == 0 then
							Reg(mu, newOnProcMap, newProcCount, newOffProcMap)
						else
							((|| id : {procCount..newProcCount-1}
							@ [AlphaProcess(id)] 
								Process(applySeq(OffProcesses, 
										applySeq(newProcs, id-procCount)), id))
							[| AlphaProcesses(newProcCount) \|\]
							Reg(mu, newOnProcMap, newProcCount, newOffProcMap))
		
		AlphaProcess(id) =
			set(<renamed.b | (a,b) <- RenamingsForProc(id)>)
		-- Important: /= Renamings beacuse there could be events that
		-- happen because of no processes events (cf internal choice).
		AlphaProcesses(maxId) = Union({AlphaProcess(id) | id <- {0..maxId-1}})
		
		H = {tau}
	within
		(((|| id : {0..OnProcessCount-1} @ 
			[AlphaProcess(id)] Process(applySeq(OnProcesses, id), id))
		)
		[| AlphaProcesses(OnProcessCount) \|\]
		Reg(startOperator, identityFunctionSeq(<0..OnProcessCount-1>), 
			OnProcessCount, identityFunctionSeq(<(-OffProcessCount)..-1>))
		)[[renamed.r <- b 
			| (r,b) <- 
				set(<(r,b) | (r,(_,_,b,_,_,_)) <- InternalEvents>)]]
		\ H
|]



globalModule = [multilineLiteral|
transparent explicate, diamond

-- *********************************************************************
-- Recursion control procedures
-- *********************************************************************
channel callProc, startProc : ProcArgs

CallProc(proc) = callProc.proc -> STOP

WrapThread(proc) =
	let
		RecursionRegulator =
			callProc?p -> startProc!p -> RecursionRegulator
			[] [] e : Operator_M::SystemEvents @ e -> RecursionRegulator
		Thread(proc) = 
			GetProc(proc)
			[| {| callProc |} |>
			startProc?proc' -> Thread(proc')
	within
		-- diamond removes the tau's from the resulting LTS (but never
		-- increases the size of the resulting LTS, cf. normalize)
		-- This removes the problem of the new events being introduced.
		-- TODO: replace this with the generalised exception operator
		diamond(
			(Thread(proc)|]
	++" [| union(Operator_M::SystemEvents, {| callProc, startProc |}) |] "++
	[multilineLiteral|RecursionRegulator) 
			\ {| startProc, callProc |}
		)
|]

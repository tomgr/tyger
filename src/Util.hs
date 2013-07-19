{-# LANGUAGE QuasiQuotes, GeneralizedNewtypeDeriving, 
			FlexibleInstances, MultiParamTypeClasses #-} 
module Util where

import Control.Monad
import Control.Monad.Error
import Control.Monad.Trans
import Control.Monad.State

import Language.Haskell.TH.Quote 
import Language.Haskell.TH.Syntax hiding (lift)
import Language.Haskell.TH.Lib 
import Data.List (nub)

-- See ConstantCode.hs for examples of how to use
multilineLiteral :: QuasiQuoter 
multilineLiteral = QuasiQuoter (litE . stringL) (litP . stringL)  (const listT) (const (returnQ []))

indentEveryLine :: String -> String
indentEveryLine = unlines . map (\l -> '\t':l) . lines

makeHeading :: String -> String
makeHeading s = 
	"-- *********************************************************************\n"++
	"-- "++s++"\n"++
	"-- *********************************************************************\n"

-- *********************************************************************
-- Partial functions
-- *********************************************************************
type PartialFunction a b = [(a,b)] -- From a to b

functionDomain :: Eq a => PartialFunction a b -> [a]
functionDomain f = map fst f

functionImage :: Eq a => PartialFunction a b -> [b]
functionImage f = map snd f

identityFunction :: Eq a => [a] -> PartialFunction a a
identityFunction xs = [(x,x) | x <- xs]

invert :: (Eq a, Eq b) => PartialFunction a b -> PartialFunction b a
invert f = [(a,b) | (b,a) <- f]

apply :: Eq a => PartialFunction a b -> a -> b
apply f x =
	let
		pos = [b | (a,b) <- f, a == x]
	in
		if length pos == 0 then 
			error ("Partial function applied to value outside of domain")
		else head pos
		
applyRelation :: Eq a => PartialFunction a b -> a -> [b]
applyRelation f x = [b | (a,b) <- f, a == x]

safeApply :: Eq a => PartialFunction a b -> a -> Maybe b
safeApply f x =
	let
		pos = [b | (a,b) <- f, a == x]
	in
		if length pos == 0 then Nothing
		else Just (head pos)

composeFunctions :: 
	(Eq a, Eq b) => PartialFunction b c -> PartialFunction a b -> 
					PartialFunction a c
composeFunctions f g = 
	[(a, apply f b) | (a,b) <- g]

mapPF :: Eq a => PartialFunction a b -> [a] -> [b]
mapPF f xs = [apply f x | x <- xs]

safeMapPF :: Eq a => PartialFunction a b -> [a] -> [b]
safeMapPF f xs = [x | Just x <- [safeApply f x | x <- xs]]

updatePF :: Eq a => PartialFunction a b -> a -> b -> PartialFunction a b
updatePF f a b = (a,b):[(c,d) | (c,d) <- f, c /= a]

removeEntry :: Eq a => PartialFunction a b -> a -> PartialFunction a b
removeEntry f a = [(c,d) | (c,d) <- f, c /= a]




noDups :: Eq a => [a] -> Bool
noDups xs = nub xs == xs

-- *********************************************************************
-- Monads
-- *********************************************************************
concatMapM :: (Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = liftM concat (mapM f xs)

data TygerError =
	CSPMTypeCheckError String
	| CSPMParseError String
	| OpSemParseError String
	| OpSemTypeCheckError String
	| TygerUnknownError String
	| Panic String

instance Show TygerError where
	show (CSPMTypeCheckError s) = s
	show (CSPMParseError s) = s
	show (OpSemParseError s) = s
	show (OpSemTypeCheckError s) = s
	show (TygerUnknownError s) = "An unknown error occured. More information: "++s
	show (Panic s) = "Internal inconsistency error! More information: "++s
		
instance Error TygerError where
	strMsg = TygerUnknownError

-- Main monad used
newtype Tyger a = Tyg {
	runTyg :: ErrorT TygerError IO a
} deriving (Monad, MonadIO, MonadError TygerError)

class Monad m => MonadTyger m where
	panic :: String -> m a
	debugOutput :: String -> m ()
instance MonadTyger Tyger where
	panic = throwError . Panic
	debugOutput = liftIO . putStrLn
instance MonadTyger m => MonadTyger (StateT s m) where
	panic = lift . panic
	debugOutput = lift . debugOutput
instance (MonadTyger m, Error e) => MonadTyger (ErrorT e m) where
	panic = lift . panic
	debugOutput = lift . debugOutput
		
runTyger :: Tyger a -> IO (Either TygerError a)
runTyger = runErrorT . runTyg

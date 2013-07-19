module Main where

import Control.Monad.Trans
import System.Directory
import System.FilePath
import System.Environment
import System.Exit
import Text.PrettyPrint.HughesPJ

import ConstantCode
import CSPMDataStructures
import CSPMParser
import CSPMPrettyPrinter
import CSPMRecursionRefactorings
import CSPMTypeChecker.TCModule
import CSPMTypeChecker.TCMonad
import OpSemRules
import OpSemParser
import OpSemTypeChecker
import Util

main :: IO ()
main = 
	do
		args <- getArgs
		res <- runTyger (tygerMain (args!!0) (args!!1))
		case res of
			Left err	-> putStrLn (show err) >> exitFailure
			Right _		-> exitSuccess

interactiveMain :: FilePath -> FilePath -> IO ()
interactiveMain opSemFile cspmFile =
	do
		res <- runTyger (tygerMain opSemFile cspmFile)
		case res of
			Left err	-> putStrLn (show err)
			Right _		-> putStrLn ("Done")

tygerMain :: FilePath -> FilePath -> Tyger ()
tygerMain opsemFile cspmFile = 
		do
			inputOpDefn <- parseOpSemFile opsemFile
			opSemDefn <- typeCheckOperators inputOpDefn
			
			let compiledOps = compileOperators opSemDefn
			cspmModules <- parseCSPMFile cspmFile opSemDefn
			
			if length cspmModules > 1 then 
					panic "Modules are not currently supported"
				else return ()
			
			transformedModules <- runTypeChecker (do
				typeCheckedModules <- typeCheckModules opSemDefn cspmModules
				runTransformMonad $ transformModules opSemDefn typeCheckedModules)
				
			let operatorsFile =
				"module Operator_M"
				++ indentEveryLine operatorModuleNotExported
				++ (indentEveryLine . show) (rulesFunctionToCSP compiledOps)
				++ ((indentEveryLine . show) 
						(discardableArgsFunctionToCSP compiledOps))
				++ "exports\n"
				++ (indentEveryLine . show) (channelsToCSP opSemDefn)
				++ indentEveryLine operatorModuleExported
				++ "endmodule\n"
				++ makeHeading "User Callable Functions"
				++ globalModule
				++ makeHeading "Operators"
				-- TODO: maybe move these into the exports of the module
				++ show (operatorDatatypeToCSP compiledOps)++"\n"
				++ show (operatorShortcutsToCSP compiledOps)++"\n"
				++ show (replicatedOperatorsToCSP opSemDefn)
			
			let outputOpSemFile = replaceExtension opsemFile ".csp" 
			let outputCSPMFile = 
				replaceFileName cspmFile 
				(dropExtension (takeFileName cspmFile)++"_Compiled.csp")
			
			let [Annotated _ _ (GlobalModule decls)] = cspmModules
			let channels = concat [n | Channel n _ <- map removeAnnotation decls]
			absoluteCSPMFilePath <- liftIO $ canonicalizePath outputCSPMFile
			absoluteOpSemFilePath <- liftIO $ canonicalizePath outputOpSemFile
			let cspmFile = 
				"include \""++makeRelative (takeDirectory absoluteCSPMFilePath)
											absoluteOpSemFilePath
							++"\"\n\n"
				++"UserEvents = {|"
					++ (show . sep . punctuate comma . map prettyPrint) channels
					++"|}\n\n"
				++show (prettyPrint (head transformedModules))

			liftIO $ writeFile outputOpSemFile (fixQuoting operatorsFile)
			liftIO $ writeFile outputCSPMFile cspmFile

			return ()

fixQuoting [] = []
fixQuoting ('\\':'|':'\\':']':xs) = '|' : ']' : fixQuoting xs
fixQuoting (x:xs) = x : fixQuoting xs

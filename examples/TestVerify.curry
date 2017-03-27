-- CurryCheck test for the curry-verify tool

import Directory ( doesFileExist )
import FilePath  ( (</>) )
import List      ( splitOn )
import System    ( getEnviron, system )
import Test.Prop

import VerifyPackageConfig ( packageExecutable )

checkAgda :: IO (Maybe String)
checkAgda = whichFileInPath "agda"

agdaImports :: String
agdaImports = "-i . -i /net/medoc/home/mh/home/languages_systems/agda/ial -i /usr/share/agda-stdlib"

agdaOptions :: String
agdaOptions = "--allow-unsolved-metas"


-- First we clean the directory from possible old files:
cleanBefore :: PropIO
cleanBefore = system "/bin/rm -f TO-PROVE-*" `returns` 0

-- Compile an example program with a given scheme and check the result:
compileToAgda :: String -> String -> IO Int
compileToAgda cvopts progname = do
  let ccmd = packageExecutable ++ " -t agda " ++ cvopts ++ " " ++ progname
  cres <- system ccmd
  if cres > 0
    then return cres
    else checkAgda >>=
         maybe (putStrLn noAgdaWarn >> return 0)
               (\agda -> do let acmd = unwords [ agda, agdaImports, agdaOptions
                                               , "TO-PROVE-*" ]
                            ares <- system acmd
                            system "/bin/rm -f TO-PROVE-*"
                            return ares)
 where
  noAgdaWarn =
    "WARNING: cannot completely test 'curry-verify' ('agda' not found)"

-- Compile an example program with all translation schemes and check the result:
compileToAgdaSchemes :: String -> IO Int
compileToAgdaSchemes progname = do
  r1 <- compileToAgda "-s choice" progname
  r2 <- compileToAgda "-s nondet" progname
  return (r1 + r2)

-- Now we can run the individual test examples:
testCompileDouble :: PropIO
testCompileDouble = compileToAgdaSchemes "Double" `returns` 0

testCompileEvenOdd :: PropIO
testCompileEvenOdd = compileToAgdaSchemes "EvenOdd" `returns` 0

testCompileGame :: PropIO
testCompileGame = compileToAgdaSchemes "Game" `returns` 0

testCompileMyList :: PropIO
testCompileMyList = compileToAgdaSchemes "MyList" `returns` 0

testCompilePerm :: PropIO
testCompilePerm = compileToAgdaSchemes "Perm" `returns` 0

-- At the end we clean the directory:
cleanAfter :: PropIO
cleanAfter =
  system "/bin/rm -rf .curry nondet.agda* nondet-thms.agda*" `returns` 0

--------------------------------------------------------------------------
-- Auxiliaries:

--- Checks whether a file exists in one of the directories on the PATH and
--- returns its file path.
whichFileInPath :: String -> IO (Maybe String)
whichFileInPath file = do
  path <- getEnviron "PATH"
  dirs <- return $ splitOn ":" path
  inPath dirs
 where
  inPath [] = return Nothing
  inPath (d:ds) = do
    let fpath = d </> file
    ex <- doesFileExist fpath
    if ex then return (Just fpath)
          else inPath ds


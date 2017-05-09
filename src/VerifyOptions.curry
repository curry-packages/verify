-------------------------------------------------------------------------
--- The options of the Curry->Verifier translation tool.
---
--- @author Michael Hanus
--- @version October 2016
-------------------------------------------------------------------------

module VerifyOptions where

import AbstractCurry.Types
import Char              (toLower)
import GetOpt
import List              (intercalate, last, splitOn)
import ReadNumeric       (readNat)

import Analysis.ProgInfo
import Analysis.Deterministic  (Deterministic(..))
import Analysis.TotallyDefined (Completeness(..))

-------------------------------------------------------------------------
-- Representation of command line options and information relevant
-- for the translation process.
data Options = Options
  { optHelp     :: Bool
  , optVerb     :: Int
  , optStore    :: Bool     -- store result in file?
  , optTarget   :: String   -- translation target
  , optScheme   :: String   -- translation scheme
  , optTheorems :: [QName]  -- names of theorems to be translated
  , isPrimFunc  :: (QName -> Bool) -- primitive function? (not translated)
  , primTypes   :: [QName] -- primitive types (not translated)
  , detInfos    :: ProgInfo Deterministic -- info about deteterministic funcs
  , patInfos    :: ProgInfo Completeness  -- info about pattern completeness
  }

-- Default command line options.
defaultOptions :: Options
defaultOptions  = Options
  { optHelp     = False
  , optVerb     = 1
  , optStore    = True
  , optTarget   = "agda"
  , optScheme   = "choice"
  , optTheorems = []
  , isPrimFunc  = isUntranslatedFunc
  , primTypes   = defPrimTypes
  , detInfos    = emptyProgInfo
  , patInfos    = emptyProgInfo
  }

-- Primitive functions that are not extracted and translated to the verifier.
-- In the future, it might be necessary to parameterize it w.r.t. the
-- target verifier.
isUntranslatedFunc :: QName -> Bool
isUntranslatedFunc qn =
  qn `elem` map pre ["?","==","+","*","<",">","<=",">=","length","map",
                     "if_then_else"] ||
  fst qn `elem` ["Test.Prop","Test.EasyCheck"]

-- Primitive functions that are not extracted and translated to the verifier.
-- In the future, it might be necessary to parameterize it w.r.t. the
-- target verifier.
defPrimTypes :: [QName]
defPrimTypes = [ pre "[]", pre "Bool", pre "Int", pre "Maybe", ("Nat","Nat")
               , ("Test.Prop","Prop"), ("Test.EasyCheck","Prop")]

-- Definition of actual command line options.
options :: [OptDescr (Options -> Options)]
options =
  [ Option "h?" ["help"]  (NoArg (\opts -> opts { optHelp = True }))
           "print help and exit"
  , Option "q" ["quiet"] (NoArg (\opts -> opts { optVerb = 0 }))
           "run quietly (no output, only exit code)"
  , Option "v" ["verbosity"]
            (OptArg (maybe (checkVerb 2) (safeReadNat checkVerb)) "<n>")
            "verbosity level:\n0: quiet (same as `-q')\n1: show progress (default)\n2: show generated output (same as `-v')\n3: show more details about translation"
  , Option "p" ["property"]
           (ReqArg addPropName "<n>")
           "name of property to be translated as theorem\n(default: translate all properties in module)"
  , Option "n" ["nostore"]
           (NoArg (\opts -> opts { optStore = False }))
           "do not store translation (show only)"
  , Option "t" ["target"]
           (ReqArg checkTarget "<t>")
           "translation target:\nAgda (default)"
  , Option "s" ["scheme"]
           (ReqArg checkScheme "<s>")
           "translation scheme:\nfor target Agda: 'choice' (default) or 'nondet'"
  ]
 where
  safeReadNat opttrans s opts =
   let numError = error "Illegal number argument (try `-h' for help)" in
    maybe numError
          (\ (n,rs) -> if null rs then opttrans n opts else numError)
          (readNat s)

  checkVerb n opts = if n>=0 && n<4
                     then opts { optVerb = n }
                     else error "Illegal verbosity level (try `-h' for help)"

  checkTarget s opts =
    if map toLower s `elem` ["agda"]
     then opts { optTarget = map toLower s }
     else error $ "Illegal target `" ++ s ++ "' (try `-h' for help)"

  checkScheme s opts =
    if map toLower s `elem` ["choice","nondet"]
     then opts { optScheme = map toLower s }
     else error $ "Illegal scheme `" ++ s ++ "' (try `-h' for help)"

  -- support also qualified names:
  addPropName name opts =
    let nameparts = splitOn "." name
        partnums  = length nameparts
        qname = if partnums < 2
                then ("",name)
                else (intercalate "." (take (partnums - 1) nameparts),
                      last nameparts)
     in opts { optTheorems = qname : optTheorems opts }

-------------------------------------------------------------------------

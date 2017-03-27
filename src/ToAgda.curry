-------------------------------------------------------------------------
--- A transformation of Curry programs into Agda programs.
---
--- @author Michael Hanus
--- @version August 2016
-------------------------------------------------------------------------

module ToAgda(theoremToAgda) where

import AbstractCurry.Types
import AbstractCurry.Select
import AbstractCurry.Build
import Directory
import FilePath          ((</>))
import List
import Maybe (fromJust)
import Rewriting.Files
import Rewriting.Term
import Rewriting.Rules
import Rewriting.CriticalPairs
import Time

import PropertyUsage
import VerifyOptions
import VerifyPackageConfig ( packagePath )

-- to access the determinism analysis:
import Analysis.ProgInfo       (ProgInfo, lookupProgInfo)
import Analysis.Deterministic  (Deterministic(..))
import Analysis.TotallyDefined (Completeness(..))

-------------------------------------------------------------------------

--- Generate an Agda program file for a given theorem name and the
--- list of all functions involved in this theorem.
theoremToAgda :: Options -> QName -> [CFuncDecl] -> [CTypeDecl] -> IO ()
theoremToAgda opts qtheo@(_,theoname) allfuncs alltypes = do
  let (rename, orgtypedrules)  = funcDeclsToTypedRules allfuncs
      transform = if optScheme opts == "nondet" then transformRuleWithNondet
                                                else transformRuleWithChoices
      typedrules = concatMap (transform opts) orgtypedrules
      (theorules,funcrules) = partition (\ (fn,_,_,_) -> fn == qtheo)
                                        typedrules
      mname = "TO-PROVE-" ++ theoname
      hrule = take 75 (repeat '-')
      agdaprog = unlines $
                  agdaHeader opts mname ++
                  [hrule, "-- Translated Curry operations:",""] ++
                  map typeDeclAsAgda alltypes ++
                  showTypedTRSAsAgda opts rename [] funcrules ++
                  [hrule, ""] ++
                  concatMap (theoremAsAgda rename) theorules ++
                  [hrule]
  --putStr agdaprog
  let agdafile = mname ++ ".agda"
  when (optVerb opts > 1 || not (optStore opts)) $ putStr agdaprog
  when (optStore opts) $ do
    writeFile agdafile agdaprog
    when (optScheme opts == "nondet") $
      mapIO_ copyImport ["nondet.agda","nondet-thms.agda"]
    when (optVerb opts > 0) $ putStrLn $
     "Agda module '" ++ agdafile ++ "' written.\n" ++
     "If you completed the proof, rename it to 'PROOF-" ++ theoname ++ ".agda'."

agdaHeader :: Options -> String -> [String]
agdaHeader opts mname =
  [ "-- Agda program using the Iowa Agda library\n"
  , "open import bool\n"
  , "module " ++ mname ] ++
  (if optScheme opts == "choice"
   then ["  (Choice : Set)\n  (choose : Choice → 𝔹)"
        , "  (lchoice : Choice → Choice)\n  (rchoice : Choice → Choice)"]
   else []) ++
  ["  where\n"
  , unlines (map (\im -> "open import " ++ im)
                 (["eq","nat","list","maybe"] ++
                 (if optScheme opts == "nondet" then ["nondet","nondet-thms"]
                                                else [])))
  ]

-------------------------------------------------------------------------
-- Map a list of function declarations into renaming function (for showing
-- identifiers in the the Agda code)
-- and a list of function names, comment lines, types, and TRS.
funcDeclsToTypedRules :: [CFuncDecl]
           -> (QName -> String, [(QName, [String], CTypeExpr, TRS QName)])
funcDeclsToTypedRules fdecls = (rename, typedrules)
 where
  typedrules  = map funcDeclToTypedRule fdecls
  allrules    = concatMap (\ (_,_,_,rules) -> rules) typedrules
  rename      = rename4agda (allNamesOfTRS allrules)

-- All function names occurring in a TRS.
allNamesOfTRS :: TRS a -> [a]
allNamesOfTRS =
  foldr union [] . map allNamesOfTerm . concatMap (\ (lhs,rhs) -> [lhs,rhs])

-- All function names occurring in a term.
allNamesOfTerm :: Term a -> [a]
allNamesOfTerm (TermVar _) = []
allNamesOfTerm (TermCons f ts) = foldr union [f] (map allNamesOfTerm ts)

-- Perform some renamings of qualified names for Agda.
-- In particular, drop the module qualifier from a name if it is still unique
-- to improve the readability of the Agda code.
rename4agda :: [QName] -> QName -> String
rename4agda allnames qn@(mn,fn)
  | (mn,fn) == pre ":"     = "_::_"
  | (mn,fn) == pre "+"     = "_+_"
  | (mn,fn) == pre "*"     = "_*_"
  | (mn,fn) == pre "True"  = "tt"
  | (mn,fn) == pre "False" = "ff"
  | (mn,fn) == nat "Z"     = "zero"
  | (mn,fn) == nat "S"     = "suc"
  | (mn,fn) == pre "<"     = "_<_"
  | (mn,fn) == pre ">"     = "_>_"
  | (mn,fn) == pre "<="    = "_\x2264_"
  | (mn,fn) == pre ">="    = "_\x2265_"
  | otherwise
  = maybe fn
          (const (showQName qn))
          (find (\ (q,f) -> f==fn && q /= mn) allnames)

-- Map a function declaration into the function name, comment, type, and TRS.
funcDeclToTypedRule :: CFuncDecl -> (QName, [String], CTypeExpr, TRS QName)
funcDeclToTypedRule (CFunc qn ar vis texp rules) =
  funcDeclToTypedRule (CmtFunc "" qn ar vis texp rules) 
funcDeclToTypedRule fdecl@(CmtFunc _ _ _ _ texp _) =
  let (fn, trs) = fromFuncDecl fdecl
   in (fn, [], texp, trs)

-------------------------------------------------------------------------
-- Eliminate overlapping rules by introducing a new operation
-- for each rule.

elimOverlappingRules :: Options
                     -> Bool
                     -> (QName, [String], CTypeExpr, TRS QName)
                     -> [(QName, [String], CTypeExpr, TRS QName)]
elimOverlappingRules opts withpartialfail (fn,cmt,texp,trs)
  | lookupProgInfo fn detinfo == Just Det || null critPairs
  = [(fn,cmt,texp,trs)]
  | otherwise
  = (fn, cmt ++ [splitCmt], texp,
     [(TermCons fn newargs,
       foldr1 (\x y -> TermCons (pre "?") [x,y])
              (map (\i -> TermCons (addRuleName fn i) newargs)
                   [1 .. length trs]))]) :
    map (\ (i,(TermCons _ args, rhs)) ->
           let rname = addRuleName fn i
            in (rname,
                ["Rule " ++ show i ++ " of operation '" ++ showQName fn ++"':"],
                texp,
                [(TermCons rname args, rhs)] ++
                if withpartialfail then [failRule rname] else []))
        (zip [1 .. length trs] trs)
 where
  detinfo   = detInfos opts
  critPairs = cPairs trs
  arity     = case head trs of (TermCons _ args,_) -> length args
                               _ -> error "elimOverlappingRules: no arity"
  newargs   = map TermVar [1 .. arity]

  failRule f = (TermCons f (map TermVar [0 .. (arity-1)]),
                TermCons (pre "failed") [])

  splitCmt = "Overlapping rules of '" ++ showQName fn ++
             "' split into a new operation for each rule."

-- Add a rule with a number to a name (to implement overlapping rules):
addRuleName :: QName -> Int -> QName
addRuleName (mn,fn) i = (mn, fn ++ "-rule" ++ show i)

-- Revert `addRuleName`.
stripRuleName :: QName -> QName
stripRuleName (mn,fn) =
   -- we assume that there are no more than 9 overlapping rules:
  (mn, if take 5 (tail (reverse fn)) == "elur-"
        then take (length fn - 6) fn
        else fn )

-------------------------------------------------------------------------
-- Transform a TRS for a function according to transformation method
-- based on choice arguments:
-- TODO: implement partial functions 

transformRuleWithChoices :: Options
                         -> (QName, [String], CTypeExpr, TRS QName)
                         -> [(QName, [String], CTypeExpr, TRS QName)]
transformRuleWithChoices opts (fn,cmt,texp,trs)
  | lookupProgInfo fn detinfo == Just Det
  = [(fn, cmt ++ concatMap theoremComment trs, texp, map transTheorem trs)]
  | otherwise
  = map (\ (f,c,t,rs) -> (f, c ++ concatMap theoremComment rs,
                          baseType (pre "Choice") ~> t,
                          map (transTheorem . addChoices) rs))
        (elimOverlappingRules opts False (fn,cmt,texp,trs))
 where
  detinfo   = detInfos opts
  choicevar = TermVar 46

  transTheorem rl@(lhs,rhs) =
    if isTheoremRule opts rl then (lhs, prop2agda rhs) else rl

  theoremComment rl@(_,rhs) =
    if isTheoremRule opts rl
     then case rhs of
            TermVar _    -> []
            TermCons f _ ->
              case snd f of
                "-=-"       -> []
                "<~>"       -> []
                "always"    -> []
                _           -> noTheoremTranslateCmt
     else []

  -- Translate CurryCheck proposition into Agda theorem:
  prop2agda v@(TermVar _) = v
  prop2agda t@(TermCons f args) =
     case snd f of
      "-=-"     -> TermCons (pre "_\x2261_") args
      "<~>"     -> TermCons (pre "_\x2261_") args
      "always"  -> TermCons (pre "_\x2261_") (args ++ [agdaTrue])
      _         -> t

  addChoices (lhs,rhs) =
   (addLhsChoice choicevar lhs,
    snd (addChoiceInTerm (choicesFor (numNondetOps rhs) choicevar) rhs))

  addLhsChoice _ v@(TermVar _)      = v  -- this case should not occur
  addLhsChoice ch (TermCons f args) = TermCons f (ch : args)

  isNondetOp f = lookupProgInfo (stripRuleName f) detinfo == Just NDet

  -- compute number of non-deterministic operations in a term:
  numNondetOps (TermVar _) = 0
  numNondetOps (TermCons f args) =
    (if f == curryChoice || isNondetOp f then 1 else 0) +
    sum (map numNondetOps args)

  addChoiceInTerm chs v@(TermVar _) = (chs,v)
  addChoiceInTerm chs (TermCons f args)
   | f == pre "?" && length args == 2
   = let (chs1,cargs) = addChoiceInTerms (tail chs) args
      in (chs1, TermCons (pre "if_then_else")
                         (TermCons (pre "choose") [head chs] : cargs))
   | isNondetOp f
     -- non-deterministic operation:
   = let (chs1,cargs) = addChoiceInTerms (tail chs) args
      in (chs1, TermCons f (head chs : cargs))
   | otherwise
   = let (chs1,cargs) = addChoiceInTerms chs args
      in (chs1, TermCons f cargs)

  addChoiceInTerms ch [] = (ch,[])
  addChoiceInTerms ch (t:ts) = let (ch1,ct ) = addChoiceInTerm  ch t
                                   (ch2,cts) = addChoiceInTerms ch1 ts
                                in (ch2,ct:cts)

-- Compute a list of disjoint choices for a given number of choices
-- and a base choice variable.
choicesFor :: Int -> Term QName -> [Term QName]
choicesFor n ch =
  if n <= 1
  then [ch]
  else
    map (\c -> TermCons (pre "lchoice") [c]) (choicesFor (n `div` 2) ch) ++
    map (\c -> TermCons (pre "rchoice") [c]) (choicesFor (n - n `div` 2) ch)

noTheoremTranslateCmt :: [String]
noTheoremTranslateCmt =
  ["WARNING: cannot translate property into an Agda theorem!"]

-------------------------------------------------------------------------
-- Transform a TRS for a function according to transformation method
-- based on trees of non-determistic values:

transformRuleWithNondet :: Options
                        -> (QName, [String], CTypeExpr, TRS QName)
                        -> [(QName, [String], CTypeExpr, TRS QName)]
transformRuleWithNondet opts (fn,cmt,texp,trs)
  | lookupProgInfo fn detinfo == Just Det
  = [(fn, cmt ++ concatMap theoremComment trs, texp, map transTheorem trs)]
  | otherwise
  = map (\ (f,c,t,rs) -> (f, c ++ concatMap theoremComment rs,
                          addNDToResultType t,
                          map addNondet rs ++ failRule f))
        (elimOverlappingRules opts True (fn,cmt,texp,trs))
 where
  detinfo = detInfos opts

  arity     = case head trs of (TermCons _ args,_) -> length args
                               _ -> error "transformRuleWithNondet: no arity"

  failRule f = if lookupProgInfo fn (patInfos opts) == Just Complete
                  || not (null (cPairs trs))
               then []
               else [(TermCons f (map TermVar [0 .. (arity-1)]),
                      TermCons (nondet "Fail") [])]

  addNDToResultType te = case te of
    CFuncType t1 t2 -> CFuncType t1 (addNDToResultType t2)
    _ -> CTCons (pre "ND") [te]

  addNondet rl@(lhs,rhs)
   | isTheoremRule opts rl
   = (lhs, prop2agda $ case rhs of TermVar _ -> rhs -- impossible case
                                   TermCons f args ->
                                     TermCons f (map addNondetInTerm args))
   | otherwise
   = (lhs, addNondetInTerm rhs)

  transTheorem rl@(lhs,rhs) =
    if isTheoremRule opts rl then (lhs, prop2agda rhs) else rl

  theoremComment rl@(_,rhs) =
    if isTheoremRule opts rl
     then case rhs of
            TermVar _    -> []
            TermCons f _ -> case snd f of
                              "-=-"       -> adaptOrderCmt
                              "<~>"       -> adaptOrderCmt
                              "always"    -> []
                              "eventually"-> []
                              "failing"   -> []
                              _           -> noTheoremTranslateCmt
     else []
   where
     adaptOrderCmt =
       ["This theorem should be adapted since the left- and right-hand sides",
        "might have their values in a different order in the tree!"]

  prop2agda v@(TermVar _) = v
  prop2agda t@(TermCons (mn,pn) args) =
    case pn of
     "-=-"        -> TermCons (pre "_\x2261_") args -- to be changed by user
     "<~>"        -> TermCons (pre "_\x2261_") args -- to be changed by user
     "always"     -> TermCons (pre "_\x2261_")
                              [TermCons (mn,"always") args, agdaTrue]
     "eventually" -> TermCons (pre "_\x2261_")
                              [TermCons (mn,"eventually") args, agdaTrue]
     "failing"    -> TermCons (pre "_\x2261_")
                              [TermCons (mn,"failing") args, agdaTrue]
     _            -> t

  isNondetOp f = lookupProgInfo (stripRuleName f) detinfo == Just NDet

  addNondetInTerm v@(TermVar _) = agdaVal v
  addNondetInTerm t@(TermCons f args)
   | f == pre "?" && length args == 2
   = TermCons (pre "_??_") (map addNondetInTerm args)
   | f == pre "failed" && null args
   = TermCons (nondet "Fail") []
   | not (hasNondetSubterms t)
   = agdaVal (TermCons f args)
   | otherwise
   = let (detargs,ndargs) = break hasNondetSubterms args
      in if isNondetOp f
          then
           if null ndargs
            then t
            else addArgsWithNdArg
                  (TermCons (withNdArgName (length ndargs))
                            [TermCons f detargs, addNondetInTerm (head ndargs)])
                  (tail ndargs)
          else addArgsWithNdArg
                  (TermCons (nondet "mapND")
                        [TermCons f detargs, addNondetInTerm (head ndargs)])
                  (tail ndargs)

  addArgsWithNdArg t [] = t
  addArgsWithNdArg t (arg:args) =
   if hasNondetSubterms arg
   then addArgsWithNdArg
          (TermCons (nondet "apply-nd") [t, addNondetInTerm arg]) args
   else addArgsWithNdArg (TermCons (nondet "apply-nd") [t,agdaVal arg]) args
  
  withNdArgName i = nondet ("with-nd-arg" ++ (if i>1 then show i else ""))

  hasNondetSubterms (TermVar _) = False
  hasNondetSubterms (TermCons f args) =
    f == (pre "?") || isNondetOp f || any hasNondetSubterms args

agdaVal :: Term QName -> Term QName
agdaVal t = TermCons (nondet "Val") [t]

-------------------------------------------------------------------------
-- Show typed rules (properties) as theorems in Agda.
theoremAsAgda :: (QName -> String) -> (QName, [String], CTypeExpr, TRS QName)
              -> [String]
theoremAsAgda _ (_,_,_,[]) = []
theoremAsAgda _ (fn,_,_,(TermVar _ ,_) : _) =
  error $ "Theorem '" ++ showQName fn ++ "': variable in left-hand side"
theoremAsAgda rn (fn, cmt, texp, (TermCons _ largs,rhs) : rules) =
  map ("-- "++) cmt ++
  [rn fn ++ " : " ++ (if null tvars then "" else showForAll tvars) ++
   showTypeWOResult largs texp ++ showTermAsAgda False (mapTerm rn rhs)
  ,showTermAsAgda False (mapTerm rn (TermCons fn largs)) ++ " = ?", ""
  ] ++ theoremAsAgda rn (fn,cmt,texp,rules)
 where
  tvars = nub (tvarsOfType texp)

  showTypeWOResult [] _ = ""
  showTypeWOResult (arg:args) te = case te of
    CFuncType t1 t2 -> "(" ++ showTermAsAgda False (mapTerm rn arg) ++ " : " ++
                       showTypeAsAgda False t1 ++
                       ") \x2192 " ++ showTypeWOResult args t2
    _ -> error $ "Inconsistent type in theorem '" ++ showQName fn ++ "': " ++
                 show te

-- Show a TRS for an operation whose type is given as Agda definitions.
-- Type signatures of mutual recursive functions must be written earlier.
-- Therefore, we pass the list of already printed functions as the
-- third argument.
showTypedTRSAsAgda :: Options -> (QName -> String) -> [QName]
                   -> [(QName,[String],CTypeExpr,TRS QName)] -> [String]
showTypedTRSAsAgda _ _ _ [] = []
showTypedTRSAsAgda opts rn prefuns ((fn,cmt,texp,trs) : morefuncs) =
  (concatMap (\ff -> let (f,_,t,_) = fromJust (find (\tf -> fst4 tf == ff)
                                                    morefuncs)
                        in ["-- Forward declaration:",
                            showTypeSignatureAsAgda (rn f) t,""])
             forwardfuncs) ++
  map ("-- "++) cmt ++
  (if lookupProgInfo fn (patInfos opts) == Just Complete
      || optScheme opts == "nondet"
    then []
    else ["-- WARNING: function '" ++ showQName fn ++
          "' is partial: adapt the code!"] ) ++
  (if fn `elem` prefuns then [] else [showTypeSignatureAsAgda (rn fn) texp]) ++
  map (showRuleAsAgda rn) trs ++ [""] ++
  showTypedTRSAsAgda opts rn (forwardfuncs ++ prefuns) morefuncs
 where
  forwardfuncs = filter (`elem` map fst4 morefuncs) (allNamesOfTRS trs \\ [fn])

showRuleAsAgda :: (QName -> String) -> Rule QName -> String
showRuleAsAgda rn (lhs,rhs) =
  showTermAsAgda False (mapTerm rn lhs) ++ " = " ++
  showTermAsAgda False (mapTerm rn rhs)

-- Show a term in Agda syntax with already renamed function names:
showTermAsAgda :: Bool -> Term String -> String
showTermAsAgda _ (TermVar v) = showVarAsAgda v
showTermAsAgda withbrackets (TermCons c args) = inBrackets $
  if c == "if_then_else" && length args == 3
   then let is = map (showTermAsAgda False) args
        in unwords ["if", is!!0, "then", is!!1, "else", is!!2]
   else
    if c == "apply" && length ts == 2
     then unwords ts
     else
      if isInfixOp c && length ts == 2
       then unwords [head ts, take (length c - 2) (tail c), head (tail ts)]
       else unwords (c : ts)
 where
  ts = map (showTermAsAgda True) args
  inBrackets s = if not (null ts) && withbrackets then "(" ++ s ++ ")" else s

-- Is infix operators in Agda?
isInfixOp :: String -> Bool
isInfixOp s = length s > 2 && head s == '_' && last s == '_'

showVarAsAgda :: Int -> String
showVarAsAgda v | v >= 0 = if q == 0
                          then [c]
                          else c:(show q)
  where
    (q, r) = divMod v 26
    c = "xyzuvwrstijklmnopqabcdefgh" !! r

-------------------------------------------------------------------------
--- Show a type declaration as an Agda data declaration.
typeDeclAsAgda :: CTypeDecl -> String
typeDeclAsAgda (CTypeSyn tc _ _ _) =
  error $ "Type synonyms not supported: " ++ showQName tc
typeDeclAsAgda (CNewType tc vis tvars consdecl) =
  typeDeclAsAgda (CType tc vis tvars [consdecl])
typeDeclAsAgda (CType tc _ tvars constrs) = unlines $
  (unwords $
     ["data", snd tc] ++
     map (\tv -> "("++ showTypeAsAgda False (CTVar tv) ++ " : Set)") tvars ++
     [": Set where"]) : map typeConsDeclAsAgda constrs
 where
  typeConsDeclAsAgda (CCons qc _ texps) =
    "   " ++ snd qc ++ " : " ++
    showTypeAsAgda False (foldr CFuncType (CTCons tc (map CTVar tvars)) texps)
  typeConsDeclAsAgda (CRecord qc _ _) =
    error $ "Records not yet supported: " ++ showQName qc

-------------------------------------------------------------------------
showTypeSignatureAsAgda :: String -> CTypeExpr -> String
showTypeSignatureAsAgda fn texp =
   fn ++ " : " ++ (if null tvars then "" else showForAll tvars) ++
   showTypeAsAgda False texp
 where
  tvars = nub (tvarsOfType texp)

showForAll :: [CTVarIName] -> String
showForAll tvars = "{" ++ unwords (map (showTypeAsAgda False . CTVar) tvars) ++
                   " : Set} \x2192 "

showTypeAsAgda :: Bool -> CTypeExpr -> String
showTypeAsAgda withbrackets texp = case texp of
  CFuncType t1 t2 -> inBrackets $ showTypeAsAgda False t1 ++ " \x2192 " ++
                                  showTypeAsAgda False t2
  CTVar (i,_) -> showVarAsAgda (i + 18) -- to get 'a' for var index 0...
  CTCons tc targs ->
    if null targs
     then showTCon tc
     else inBrackets $ unwords (showTCon tc : map (showTypeAsAgda True) targs)
 where
  inBrackets s = if withbrackets then "(" ++ s ++ ")" else s

showTCon :: QName -> String
showTCon tc
 | tc == pre "[]"        = "\x1d543"
 | tc == pre "Int"       = "\x2115"
 | tc == pre "Bool"      = "\x1d539"
 | tc == pre "Maybe"     = "maybe"
 | tc == pre "Choice"    = "Choice"
 | tc == nat "Nat"       = "\x2115"
 | otherwise = snd tc

-------------------------------------------------------------------------
curryChoice :: QName
curryChoice = pre "?"

nat :: String -> QName
nat s = ("Nat",s)

nondet :: String -> QName
nondet s = ("nondet",s)

agdaTrue :: Term QName
agdaTrue = TermCons (pre "tt") []

agdaFalse :: Term QName
agdaFalse = TermCons (pre "ff") []

ruleFunc :: Rule QName -> QName
ruleFunc rl@(TermVar _,_) = error $ "Rule with variable lhs: " ++
                                    showRule showQName rl
ruleFunc (TermCons f _,_) = f

-- Is this rule of a property of the source program?
isTheoremRule :: Options -> Rule QName -> Bool
isTheoremRule opts (lhs,_) =
  case lhs of
    TermVar _    -> False
    TermCons f _ -> f `elem` optTheorems opts

fst4 :: (a,b,c,d) -> a
fst4 (x,_,_,_) = x

-------------------------------------------------------------------------
--- Copy file from import dir into current dir if it is not newer
--- in the current dir.
copyImport :: String -> IO ()
copyImport library = do
  let importfile = packagePath </> "imports" </> library
  libexists <- doesFileExist library
  if not libexists
   then copyFile importfile library
   else do
     itime <- getModificationTime importfile
     ltime <- getModificationTime library
     unless (compareClockTime ltime itime == GT) $ copyFile importfile library

-------------------------------------------------------------------------

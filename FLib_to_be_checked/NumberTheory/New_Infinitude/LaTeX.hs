
module Alice.Import.LaTeX where
import Data.IORef
import Data.Time
import Control.Monad
import Data.List
import Data.List.Split

fromLaTeX :: String -> String
fromLaTeX s = if null half
              then s
              else handleDocument . head $ splitOn "\\end{document}" $ head half
    where half = tail $ splitOn "\\begin{document}" s

handleDocument :: String -> String
handleDocument s = foldr id ((filter snd $ applyRules [(s, False)]) >>= fst) $
  (map replacer replacements)

applyRules :: [(String, Bool)] -> [(String, Bool)]
applyRules pairs = foldr id pairs $
  (map lineRule linePairs) ++ (map sectionRule sectionPairs)

sectionRule :: (String, String) -> [(String, Bool)] -> [(String, Bool)]
sectionRule s ps = ps >>= sectionRule' s

sectionRule' :: (String, String) -> (String, Bool) -> [(String, Bool)]
sectionRule' (s1, s2) (t, v) = (head parts, v):(tail parts >>= getSection)
    where parts = splitOn ("\\begin{" ++ s1 ++ "}") t
           getSection u = let l = splitOn ("\\end{" ++ s1 ++ "}") u
                          in [("\n" ++ s2 ++ head l ++
                                (if head s1 == 'p' then "qed.\n" else ""), True),
                              (l !! 1, v)]

sectionPairs :: [(String, String)]
sectionPairs = [("signature", "Signature"), ("definition", "Definition"),
    ("axiom", "Axiom"), ("lemma", "Lemma"),
    ("theorem", "Theorem"), ("proofn", "Proof"),
    ("signaturep", "Signature."), ("definitionp", "Definition."),
    ("axiomp", "Axiom."), ("lemmap", "Lemma."),
    ("theoremp", "Theorem."), ("proof", "Proof."), ("forthel", "")]

lineRule :: (String, String) -> [(String, Bool)] -> [(String, Bool)]
lineRule s ps = ps >>= lineRule' s

lineRule' :: (String, String) -> (String, Bool) -> [(String, Bool)]
lineRule' (s1, s2) (t, v) = (head parts, v):(tail parts >>= getSection)
    where parts = splitOn s1 t
           getSection u = let l = splitOn "\n" u
                          in [(s2 ++ head l ++ "\n", True),
                              (intercalate "\n" $ tail l, v)]

linePairs :: [(String, String)]
linePairs = [("%%", ""), ("%#", "#")]

replacer :: (String, String) -> String -> String
replacer (s, t) u = (intercalate t . splitOn s) u

replacements :: [(String, String)]
replacements = [("\\{", "{"), ("\\}", "}"), ("$", ""),
    ("\\prec\\prec", "-<-"), ("\\neq", "!="),
    ("\\rightarrow", "=>"), ("\\wedge", "/\\"), ("\\vee", "\\/")]

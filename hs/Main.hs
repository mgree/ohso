module Main where

import Text.PrettyPrint

data SExp =
  Atom String
  | Apply [SExp]

atom :: Show a => a -> SExp
atom = Atom . show

e123, e1to6, bigE :: SExp
e123 = Apply $ map atom [1..3]

e1to6 = Apply [ Apply [atom 1]
              , Apply $ map atom [2..3]
              , Apply $ map atom [4..6]
              ]

bigE = Apply [ Apply $ map atom [0..3]
             , Apply $ map atom [4..10]
             , Apply $ map atom [11..25]
             ]

pretty :: SExp -> Doc
pretty (Atom a) = text a
pretty (Apply xs) = parens $ sep $ map (nest 1 . pretty) xs

main = do
  putStrLn $ render $ pretty e123
  putStrLn $ render $ pretty e1to6
  putStrLn $ render $ pretty bigE

module Examples where

import Terms
import Ident
import Fresh
import Eq

test_refl x = run emptyHeap $ testTerm x x

type TermId =  Term Id Id

tt,ff,case_t :: Term String String
ff = Constr "x" (Tag "False") (Conc "x")
tt = Constr "y" (Tag "True") (Conc "y")
case_t = Case "x" [Br "True" $ Conc $ "y", Br "False" $ Conc $ "z"]


{-# language PatternSynonyms #-}
{-# language PartialTypeSignatures #-}

module Lambda.LNR
  (
  ) where

-- ** Import

import Lambda.Prelude
import Relude.Extra.Enum (prev, next)
import qualified Text.Show
import Data.Attoparsec.Text
    ( decimal, parseTest, char, parseOnly, string, Parser )
import Data.Functor.Classes ( Eq1(..) )
import Yaya.Fold ( Steppable(..), Projectable(..), Mu(..), lambek, Recursive(..), Algebra, Coalgebra )

-- ** Locally Nameless Lambda calculi implementation

-- *** Initial type primitive boundaries

-- **** New type typisation

-- | Bruijn index in lambda term.
-- Index < number of external lambda binds => index == binded lambda value
-- Index >= number of external lambda binds => index == free variable
newtype BruijnIndex = BruijnIndex Int
 deriving (Eq, Enum, Num, Bounded, Show, Generic)

newtype LambdaTermFAppFunc a = LambdaTermFAppFunc (LambdaTermF a)
 deriving (Eq, Show, Generic, Functor, Traversable, Foldable)

newtype LambdaTermFAppParam a = LambdaTermFAppParam (LambdaTermF a)
 deriving (Eq, Show, Generic, Functor, Traversable, Foldable)

newtype LambdaTermFLamBody a = LambdaTermFLamBody (LambdaTermF a)
 deriving (Eq, Show, Generic, Functor, Traversable, Foldable)

-- **** Functorial Lambda term/expression

-- | Accumulator that indexes all bound variables.
newtype BoundVars a = BoundVars (Seq a)

-- | Accumulator that indexes all free variables.
newtype FreeVars a = FreeVars (Seq a)

-- | Level of the Lambda term closure.
--
-- (useful for:
--   * reference in the recursive scheme to evaluate the structure
--   * check that lambda term variables are enumerated properly
--   * access the particular level of structure
-- )
newtype LambdaClosureLevel = LambdaClosureLevel Int

data LNR
  = 
    
data LambdaTermF a
  = LambdaTermFBruijnIndex !BruijnIndex
  | LambdaTermFApp    !(LambdaTermFAppFunc a) !(LambdaTermFAppParam a)
  | LambdaTermFLam    !(LambdaTermFLamBody a)
 deriving (Eq, Show, Generic, Functor, Traversable, Foldable)


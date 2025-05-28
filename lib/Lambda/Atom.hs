{-# language PartialTypeSignatures #-}
{-# language StrictData #-}

-- | The context of this module is primitives that get shared between ifferent types of lambda terms.
module Lambda.Atom
where

import Lambda.Prelude


-- | Bruijn index in lambda term.
-- Index < number of external lambda binds => index == binded lambda value
-- Index >= number of external lambda binds => index == free variable
newtype BjIx = BjIx Natural
 deriving (Eq, Enum, Num, Show, Generic, Ord, Real, Integral)

{-# language CPP #-}

-- | This is a module of custom "Prelude" code.
-- It is for import for projects other then @Hisp@.
-- For @Hisp@ - this module gets reexported by "Prelude", so for @Hisp@ please fix-up pass-through there.
module Lambda.Util
  ( stub
  , pass
  , dup
  , both
  , mapPair
  , iterateN
  , nestM
  , applyAll
  , traverse2
  , lifted

  , whenTrue
  , whenFalse
  , monoid
  , whenJust
  , mapLeft
  , mapRight
  , fromEither
  , isPresent
  , handlePresence
  , whenText
  , free

  , Path(..)
  , isAbsolute
  , (</>)
  , joinPath
  , splitDirectories
  , takeDirectory
  , takeFileName
  , takeBaseName
  , takeExtension
  , takeExtensions
  , addExtension
  , dropExtensions
  , replaceExtension
  , readFile

  , Alg
  , Transform
  , TransformF
  , loebM
  , adi

  , Has(..)
  , askLocal

  , KeyMap

  , cons
  , snoc
  , lookupHM
  , lookupIM
  , lookupSeq

  , crc

  , trace
  , traceM
  , module X
  )
 where

import           Relude                  hiding ( pass
                                                , force
                                                , readFile
                                                , whenJust
                                                , whenNothing
                                                , trace
                                                , traceM
                                                )

import           Data.Binary                    ( Binary )
import           Data.Data                      ( Data )
import           Codec.Serialise                ( Serialise )
import           Control.Monad.Fix              ( MonadFix(..) )
import           Control.Monad.Free             ( Free(..) )
import           Control.Monad.Trans.Control    ( MonadTransControl(..) )
import           Data.Fix                       ( Fix(..) )
import qualified Data.Text                     as Text
import           Lens.Family2                  as X
                                                ( view
                                                , over
                                                , LensLike'
                                                , Lens'
                                                )
import           Lens.Family2.Stock             ( _1
                                                , _2
                                                )
import qualified System.FilePath              as FilePath
import           Control.Monad                  ( foldM )
import qualified Data.IntMap.Lazy              as IntMapL
import qualified Data.HashMap.Lazy             as HashMapL
import qualified Data.Sequence                 as Seq

#if ENABLE_TRACING
import qualified Relude.Debug                 as X
#else
-- Well, since it is currently CPP intermingled with Debug.Trace, required to use String here.
trace :: String -> a -> a
trace = const id
{-# inline trace #-}
traceM :: Monad m => String -> m ()
traceM = const stub
{-# inline traceM #-}
#endif

-- * Helpers

-- After migration from the @relude@ - @relude: pass -> stub@
-- | @pure mempty@: Short-curcuit, stub.
stub :: (Applicative f, Monoid a) => f a
stub = pure mempty
{-# inline stub #-}

-- | Alias for 'stub', since "Relude" has more specialized @pure ()@.
pass :: (Applicative f) => f ()
pass = stub
{-# inline pass #-}

-- | Duplicates object into a tuple.
dup :: a -> (a, a)
dup x = (x, x)
{-# inline dup #-}

-- | Apply a single function to both components of a pair.
--
-- > both succ (1,2) == (2,3)
--
-- Taken From package @extra@
both :: (a -> b) -> (a, a) -> (b, b)
both f (x,y) = (f x, f y)
{-# inline both #-}

-- | Gives tuple laziness.
--
-- Takem from @utility-ht@.
mapPair :: (a -> c, b -> d) -> (a,b) -> (c,d)
mapPair ~(f,g) ~(a,b) = (f a, g b)
{-# inline mapPair #-}

iterateN
  :: forall a
   . Int -- ^ Recursively apply 'Int' times
  -> (a -> a) -- ^ the function
  -> a -- ^ starting from argument
  -> a
iterateN n f x =
  -- It is hard to read - yes. It is a non-recursive momoized action - yes.
  fix ((<*> (0 /=)) . ((bool x . f) .) . (. pred)) n

nestM
  :: Monad m
  => Int -- ^ Recursively apply 'Int' times
  -> (a -> m a) -- ^ function (Kleisli arrow).
  -> a -- ^ to value
  -> m a -- ^ & join layers of 'm'
nestM 0 _ x = pure x
nestM n f x =
  foldM (const . f) x $ replicate @() n mempty -- fuses. But also, can it be fix join?
{-# inline nestM #-}

-- | In `foldr` order apply functions.
applyAll :: Foldable t => t (a -> a) -> a -> a
applyAll = flip (foldr id)

traverse2
  :: ( Applicative m
     , Applicative n
     , Traversable t
     )
  => ( a
     -> m (n b)
     ) -- ^ Run function that runs 2 'Applicative' actions
  -> t a -- ^ on every element in 'Traversable'
  -> m (n (t b)) -- ^ collect the results.
traverse2 f x = sequenceA <$> traverse f x

--  2021-08-21: NOTE: Someone needs to put in normal words, what this does.
-- This function is pretty spefic & used only once, in "Hisp.Normal".
lifted
  :: (MonadTransControl u, Monad (u m), Monad m)
  => ((a -> m (StT u b)) -> m (StT u b))
  -> (a -> u m b)
  -> u m b
lifted f k =
  restoreT . pure =<< liftWith (\run -> f (run . k))


-- * Eliminators

whenTrue :: (Monoid a)
  => a -> Bool -> a
whenTrue =
  bool
    mempty
{-# inline whenTrue #-}

whenFalse :: (Monoid a)
  => a  -> Bool  -> a
whenFalse f =
  bool
    f
    mempty
{-# inline whenFalse #-}

monoid :: (Eq a, Monoid a) => b -> (a -> b) -> a -> b
monoid v f a =
  bool
    v
    (f a)
    (mempty == a)

whenJust
  :: Monoid b
  => (a -> b)
  -> Maybe a
  -> b
whenJust =
  maybe
    mempty
{-# inline whenJust #-}

-- | Modify Left flow.
mapLeft :: (l -> a) -> Either l r -> Either a r
mapLeft f =
  either
    (Left . f)
    pure

-- | Modify Right flow.
mapRight :: (r -> a) -> Either l r -> Either l a
mapRight f =
  either
    Left
    (pure . f)

-- | Strip @Either@ structure (needs same type brunches).
fromEither :: Either c c -> c
fromEither =
  either
    id
    id
{-# inline fromEither #-}

isPresent :: Foldable t => t a -> Bool
isPresent = not . null
{-# inline isPresent #-}


-- | 'maybe'-like eliminator, for foldable empty/inhabited structures.
handlePresence :: Foldable t => b -> (t a -> b) -> t a -> b
handlePresence d f t =
  bool
    d
    (f t)
    (isPresent t)
{-# inline handlePresence #-}

whenText
  :: a -> (Text -> a) -> Text -> a
whenText e f t =
  bool
    e
    (f t)
    (not $ Text.null t)

-- | Lambda analog of @maybe@ or @either@ for Free monad.
free :: (a -> b) -> (f (Free f a) -> b) -> Free f a -> b
free fP fF fr =
  case fr of
    Pure a -> fP a
    Free fa -> fF fa
{-# inline free #-}


-- * Path

-- | Explicit type boundary between FilePath & String.
newtype Path = Path FilePath
  deriving
    ( Eq, Ord, Generic
    , Typeable, Data, NFData, Serialise, Binary
    , Show, Read, Hashable
    , Semigroup, Monoid
    )

instance ToText Path where
  toText = toText @String . crc

instance IsString Path where
  fromString = crc

-- ** Path functions

-- | This set of @Path@ funcs is to control system filepath types & typesafety and to easily migrate from FilePath to anything suitable (like @path@ or so).

-- | 'Path's 'FilePath.isAbsolute'.
isAbsolute :: Path -> Bool
isAbsolute = crc FilePath.isAbsolute

-- | 'Path's 'FilePath.(</>)'.
(</>) :: Path -> Path -> Path
(</>) = crc (FilePath.</>)
infixr 5 </>

-- | 'Path's 'FilePath.joinPath'.
joinPath :: [Path] -> Path
joinPath = crc FilePath.joinPath

-- | 'Path's 'FilePath.splitDirectories'.
splitDirectories :: Path -> [Path]
splitDirectories = crc FilePath.splitDirectories

-- | 'Path's 'FilePath.takeDirectory'.
takeDirectory :: Path -> Path
takeDirectory = crc FilePath.takeDirectory

-- | 'Path's 'FilePath.takeFileName'.
takeFileName :: Path -> Path
takeFileName = crc FilePath.takeFileName

-- | 'Path's 'FilePath.takeBaseName'.
takeBaseName :: Path -> String
takeBaseName = crc FilePath.takeBaseName

-- | 'Path's 'FilePath.takeExtension'.
takeExtension :: Path -> String
takeExtension = crc FilePath.takeExtensions

-- | 'Path's 'FilePath.takeExtensions'.
takeExtensions :: Path -> String
takeExtensions = crc FilePath.takeExtensions

-- | 'Path's 'FilePath.addExtensions'.
addExtension :: Path -> String -> Path
addExtension = crc FilePath.addExtension

-- | 'Path's 'FilePath.dropExtensions'.
dropExtensions :: Path -> Path
dropExtensions = crc FilePath.dropExtensions

-- | 'Path's 'FilePath.replaceExtension'.
replaceExtension :: Path -> String -> Path
replaceExtension = crc FilePath.replaceExtension

-- | 'Path's 'FilePath.readFile'.
readFile :: MonadIO m => Path -> m Text
readFile = readFileText . crc


-- * Recursion scheme

-- | F-algebra defines how to reduce the fixed-point of a functor to a value.
-- > type Alg f a = f a -> a
type Alg f a = f a -> a

-- | Do according transformation.
--
-- It is a transformation of a recursion scheme.
-- See @TransformF@.
type Transform f a = TransformF (Fix f) a
-- | Do according transformation.
--
-- It is a transformation between functors.
type TransformF f a = (f -> a) -> f -> a

loebM :: (MonadFix m, Traversable t) => t (t a -> m a) -> m (t a)
loebM f = mfix $ \a -> (`traverse` f) ($ a)
{-# inline loebM #-}

-- | adi is Abstracting Definitional Interpreters:
--
--     https://arxiv.org/abs/1707.04755
--
--   All ADI does is interleaves every layer of evaluation by inserting intermitten layers between them, in that way the evaluation can be extended/embelished in any way wanted. Look at its use to see great examples.
--
--   Essentially, it does for evaluation what recursion schemes do for
--   representation: allows threading layers through existing structure, only
--   in this case through behavior.
adi
  :: Functor f
  => Transform f a
  -> Alg f a
  -> Fix f
  -> a
adi g f = g $ f . (adi g f <$>) . unFix


-- * Has lens

class Has a b where
  hasLens :: Lens' a b

instance Has a a where
  hasLens f = f

instance Has (a, b) a where
  hasLens = _1

instance Has (a, b) b where
  hasLens = _2

-- | Retrive monad state by 'Lens''.
askLocal :: (MonadReader t m, Has t a) => m a
askLocal = asks $ view hasLens

-- * Other

-- | > Hashmap Text -- type synonym
type KeyMap = HashMap Text

cons :: (Semigroup a, One a) => OneItem a -> a -> a
cons = (<>) . one

snoc :: (Semigroup a, One a) => a -> OneItem a -> a
snoc xs = (<>) xs . one

lookupHM :: Hashable k => HashMap k v -> k -> Maybe v
lookupHM = flip HashMapL.lookup

lookupIM :: IntMap a -> IntMapL.Key -> Maybe a
lookupIM = flip IntMapL.lookup

lookupSeq :: Seq a -> Int -> Maybe a
lookupSeq = flip Seq.lookup

while :: (a -> Bool) -> (a -> a) -> a -> a
while p f = liftA3
  bool
    id
    (while p f . f)
    p

-- | Purely to fix type application code, and make the target type application first (imho the most useful case).
-- @
--    coerce \@_ \@TypeB
--    crc \@TypeB
-- @
crc :: forall b a . (Coercible a b) => a -> b
crc = coerce @a @b

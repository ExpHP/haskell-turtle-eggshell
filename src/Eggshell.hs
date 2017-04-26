#!/usr/bin/env runghc

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}

{-# OPTIONS_GHC -threaded -with-rtsopts<-N #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Eggshell(
    module Turtle,

    Eggshell(..),
    Egg(..), singularToEgg,

    MonadEgg(..),

    -- sigh
    idgaf, -- (this probably shouldn't be here,
           --  but it complements some orphan instances)

    -- an omelette of utils
    -- some of these should probably just go directly
    --   into the scripts that use them instead
    symlink, symlinkAbs,
    glob,
    hPutStrLn,
    editFile,
    traceManaged,

    -- this api's in the incubator
    writingOut, appendingOut,
    writingErr, appendingErr,
    writeOut, appendOut,
    writeErr, appendErr,

    -- eggy overrides
    die, exit,
    continue,
    echo, err,
    select,
    egg, -- the new 'sh'
    fold, foldIO, foldEgg,
    ls, lsif, lstree,
    Feline, -- ?
    cat, grep, sed, find,
    yes, endless,

    -- combineggers
    voidify, unitify,
    thisMany,

    -- yolk around with stdout/stderr
    interact, outeract,
    eggIO, eggIO_, loudIO, loudIO_, quietIO, quietIO_,
    shellLefts, shellRights,
    toErrOutShell, toShell, toErrOut, toErr, toOut,
    fromErrOutShell, fromShell,
    share,
    tease,

    killOut, killErr,
    addStrictOut, addStrictErr, addStrictErrOut,

    -- plugging a chip
    toOut', toPipe',

    -- navigating the coop
    (<.>), (</>), (<-.>), (</->),

    -- run some runny commands
    procs, procGlobal,
    shells, shellGlobal,
) where

-- {-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -fno-warn-name-shadowing #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-}
-- {-# OPTIONS_GHC -fno-warn-orphans #-}

import Prelude hiding (FilePath,interact)

import           "base" Control.Monad(ap)
import           "base" Control.Exception(bracket,bracket_)
import           "base" System.IO.Error(isDoesNotExistError)
import           "base" Debug.Trace(traceIO)
import           "base" Data.IORef -- OHHH BOY
import           "base" Control.Arrow((>>>), (<<<), (&&&))
import           "managed" Control.Monad.Managed(MonadManaged)
import qualified "turtle" Turtle
import           "turtle" Turtle hiding (
    -- these now produce eggshells
    fold, foldIO,
    select,
    echo, err, echo', err',
    exit, die,
    sh,
    ls, lsif, lstree,
    cat, grep, sed, find,
    yes, endless,

    -- we reexport these for fixity concerns
    (<.>), (</>),

    -- eggshell provides a slightly different gamut of procs
    -- NOTE: Turtle.xxxStrict and Turtle.xxxStrictWithErr are explicitly supported
    --       as part of this collection, because there's no need to wrap them.
    proc, procs, inproc, inprocWithErr,
    shell, shells, inshells, inshellWithErr,
    )
import           "exceptions" Control.Monad.Catch(handleIf)
import qualified "text" Data.Text.IO as Text.IO(hPutStrLn, writeFile, readFile)
import           "unix" System.Posix.Files(createSymbolicLink)
import qualified "string-convert" Text.StringConvert as StringConvert
import qualified "Glob" System.FilePath.Glob as Glob
import qualified "foldl" Control.Foldl as Fold
import           "extra" Control.Monad.Extra(whenJust)
import qualified "system-filepath" Filesystem.Path as FilePath

type Item u e a = Either (Either u e) a

-- | 'Eggshell' is an eggshell-thin wrapper around 'Turtle.Shell' which makes it
--   easier to redirect @stdout@ and @stderr@. 'Eggshell' carries lines of
--   @stdout@ and @stderr@ (the white stuff) /implicitly/ alongside the
--   values we actually care about (the yolk), so that we can capture stdout
--   and stderr without them interfering with the comprehensions we actually
--   want to write.  It contains a @Shell (Either (Either Line Line) a)@.
--
-- For instance, while 'Turtle.echo' always outputs to the global stdout, an
-- @echo@ for 'Eggshell' would emit a 'Left (Left line)' to the underlying 'Shell'.
-- This line is invisible to the user within the confines of `do` notation,
-- but can be intercepted via a function of type @(Eggshell a -> Eggshell a)@.
--
-- There's still no 'stdin' because the author isn't quite sure how to fit it in.
-- Currently, things that take an input stream have type 'Shell Line -> x' for some x,
-- and if this isn't enough to meet your needs... um, well, tough luck I guess.
--
-- USE WITH CAUTION! While @Eggshell@ implements a variety of instances,
--  it has not yet been proven that @Eggshell@ is a law-abiding citizen.
--
-- Also, the author doesn't tend to think too hard about exception safety,
-- so we can only hope that he at least thought /hard enough!/
data Eggshell a = Eggshell
    { runEggshell :: Shell (Item Line Line a) -- ^ Crack the Eggshell, and void your warranty.
    }

-- NOTE: I'd call this an 'Omelette' (the result of folding an Eggshell),
--       but I don't think I could spell it consistently.
-- | 'Egg' is to 'Eggshell' as '(MonadIO io)=> io' is to 'Turtle.Shell'.
--   It is an indivisible unit of computation which can be safely embedded
--   in the middle of an 'Eggshell' comprehension without fear of leaking
--   managed resources into the enclosing shell, or unwittingly introducing
--   some sort of implicit loop.
--
--   More precisely, an 'Egg a' is an 'Eggshell a' that produces __a single value__
--   of type @a@.  It does so after streaming all of its stdout/stderr, and closing
--   all of its managed resources.
data Egg a = MkEggUnchecked -- ^ Make an Egg. You promise that it produces a single value
                            --   of type a, that this is the final thing contained
                            --   in its output stream, and that all managed resources
                            --   are closed before this value is emitted.
    { runEgg :: Eggshell a -- ^ Smash the Egg, and get shell everywhere. (you brute!)
    }

-- TODO: Perhaps we can use the checkers package to help verify these
--       (in particular there is Test.QuickCheck.Classes) for Egg.
--       Notice this does NOT require writing an Eq instance.
--        (we need to write an EqProp instance, which is weaker and permits IO(?))

-- STATUS: Valid by isomorphism to ExceptT
instance Functor Eggshell where
    fmap f (Eggshell xs) = Eggshell (fmap (fmap f) xs)

-- STATUS: Validity follows from proof of Monad
instance Applicative Eggshell where
    pure = Eggshell . pure . Right
    (<*>) = ap

{- XXX These proofs are doing things the needlessly hard way.
       It turns out Eggshell is just  'ExceptT Shell (Either String String)'
       (the monad implementation is a perfect match), so the validity of this
       Monad instance follows by isomorphism.

-- STATUS:  PROVEN (?)
--          But not verified...
--          Would you trust it?
--
--
--
--
--          (correct answer: yeah prolly lol)

-- These proofs use the following abbreviations:
--     run = runEggshell
--     Mk  = MkEggshell

-- 1. LEFT IDENTITY:   pure v >>= f = f v
--   - pure v >>= f                                               :: given
--   - Mk $ run (pure v) >>= either (pure . Left) (run . f)       :: defn of (>>=)
--   - Mk $ run (Mk . pure . Right $ v)                           :: defn of pure
--             >>= either (pure . Left) (run . f)
--   - Mk $ (run . Mk . pure . Right $ v)                         :: defn of (.)
--             >>= either (pure . Left) (run . f)
--   - Mk $ (pure . Right $ v) >>= either (pure . Left) (run . f) :: run . Mk = id
--   - Mk $ pure (Right v) >>= either (pure . Left) (run . f)     :: defn of (.)
--   - Mk $ either (pure . Left) (run . f) (Right v)              :: Left Identity for Shell (a known Monad)
--   - Mk $ (run . f) v                                           :: case matching on 'either'
--   - (Mk . run . f) v                                           :: defn of (.)
--   - f v                                                        :: run . Mk = id

-- 2. RIGHT IDENTITY:   v >>= pure = v

--   - v >>= pure                                          :: given
--   - Mk $ run v >>= either (pure . Left) (run . pure)    :: defn of (>>=)
--   - Mk $ run v >>= either (pure . Left)                 :: defn of pure
--                           (run . Mk . pure . Right)
--   - Mk $ run v >>= either (pure . Left) (pure . Right)  :: run . Mk = id
--   - Mk $ run v >>= pure . either Left Right             :: factorize case match
--   - Mk $ run v >>= pure                                 :: either Left Right = id
--   - Mk $ run v                                          :: Right Identity for Shell (a known Monad)
--   - v                                                   :: Mk . run = id

-- 3. ASSOCIATIVITY:   (v >>= f) >>= g = v >>= (\x -> f x >>= g)
--
--   - v >>= (\x -> f x >>= g)                                         :: RHS
--   - Mk $ run v >>= either (pure . Left)                             :: defn of (>>=)
--                           (run . \x -> f x >>= g)
--   - Mk $ run v >>= K (run . \x -> f x >>= g)                        :: let K :: forall a b.
--                                                                                 (a -> Shell (Item b))
--                                                                              -> (Item a)
--                                                                              -> Shell (Item b)
--                                                                            K = either (pure . Left)
--   - Mk $ run v >>= K (run . \x -> Mk $ run (f x) >>= K (run . g))   :: another (>>=)
--   - Mk $ run v >>= K (run . \x -> Mk $ run (f x) >>= K (run . g))   :: another (>>=)
--   - Mk $ run v >>= K (run . \x -> Mk $ (run . f) x >>= K (run . g)) :: aw geez man
--   - Mk $ v' >>= K (run . \x -> Mk $ f' x >>= K g')                  :: let f' = run . f  :: A -> Shell (Item B)
--                                                                            g' = run . g  :: B -> Shell (Item C)
--                                                                            v' = run v    :: Shell (Item A)
--   - Mk $ v' >>= K (run . \x -> Mk $ (\x -> f' x >>= K g') x)        :: eta expand
--   - Mk $ v' >>= K (run . \x -> Mk . (\x -> f' x >>= K g') $ x)      :: more (.) tricks
--   - Mk $ v' >>= K (run . Mk . (\x -> f' x >>= K g'))                :: un-eta expand
--   - Mk $ v' >>= K (\x -> f' x >>= K g')                             :: run . Mk

--   - (v >>= f) >>= g                                       :: LHS
--   - (Mk $ run v >>= K (run . f)) >>= g                    :: here we go again
--   - Mk $ run (Mk $ run v >>= K (run . f)) >>= K (run . g) :: ok that's not too bad
--   - Mk $ run (Mk $ v' >>= K f') >>= K g'                  :: v', f' and g' from above
--   - Mk $ (v' >>= K f') >>= K g'                           :: another (run . Mk) cancellation

--
--   Goal is to prove these two equal
--   - LHS:  Mk $ (v' >>= K f') >>= K g'
--   - RHS:  Mk $ v' >>= K (\x -> f' x >>= K g')
--
--   Factor out the leading Mk
--   - LHS:  (v' >>= K f') >>= K g'
--   - RHS:  v' >>= K (\x -> f' x >>= K g')
--
--   Let f'' = K f' :: Item A -> Shell (Item B)
--       g'' = K g' :: Item B -> Shell (Item C)
--   - LHS:  (v' >>= f'') >>= g''
--   - RHS:  v' >>= K (\x -> f' x >>= g'')
--
--   Apply the monad Associativity Law on Shells to the LHS
--   - LHS:  v' >>= (\x -> f'' x >>= g'')
--   - RHS:  v' >>= K (\x -> f' x >>= g'')
--
--   Factor
--   - LHS:  (\x -> f'' x >>= g'')
--   - RHS:  K (\x -> f' x >>= g'')
--
--   Functional extensionality (i.e. apply x to both sides)
--   - LHS:  f'' x >>= g''
--   - RHS:  K (\x -> f' x >>= g'') x
--
--   - RHS:  either (pure . Left) (\x -> f' x >>= g'') x
--   - RHS:  case x of Left  x -> pure (Left x)
--                     Right x -> f' x >>= g''
--
--   - LHS:  K f' x >>= g''
--   - LHS:  either (pure . Left) f' x >>= g''
--   - LHS:  (case x of Left  x -> pure (Left x)
--                      Right x -> f' x) >>= g''
--   - LHS:  case x of Left  x -> pure (Left x) >>= g''
--                     Right x -> f' x >>= g''
--
--   New goal:  pure (Left x) >>= g''   ==   pure (Left x)
--
--   - pure (Left x) >>= g''
--   - g'' (Left x)
--   - K g' (Left x)
--   - either (pure . Left) g' (Left x)
--   - (pure . Left) x
--   - pure (Left x)                           QED.
-}

instance Monad Eggshell where
    xs >>= f = Eggshell $
        runEggshell xs >>= either
            (pure . Left)      -- forward stdout/stderr
            (runEggshell . f)  -- normal Shell behavior on values

-- NOTE: Valid by isomorphism to Shell.
--       (the only laws on Alternative are that it forms a monoid;
--        this is obviously true)
--       Notice this is NOT isomorphic to ExceptT's Alternative instance.
instance Alternative Eggshell where
    empty = Eggshell empty
    a <|> b = Eggshell $ (runEggshell a) <|> (runEggshell b)

-- NOTE: Eggshell VIOLATES the Right Zero law:  a >> empty /= empty
--
--       However, I'm told this is a highly contested MonadPlus law and
--       many instances in base violate it. Probably not a concern. (?)
instance MonadPlus Eggshell where

-- STATUS: Valid by isomorphism to ExceptT.
instance MonadIO Eggshell where
    liftIO = Eggshell . liftIO . fmap pure

-- STATUS:  NOT PROVEN   FIXME
instance MonadManaged Eggshell where
    using = Eggshell . using . fmap pure

-- NOTE: Tragedy of tragedies, Eggshell cannot implement MonadZip, thanks to this law:
--
--  INFORMATION PRESERVATION:
--    if:   fmap (const ()) ma = fmap (const ()) mb
--    then: ma = fmap fst (mzip ma mb)
--          mb = fmap snd (mzip ma mb)
--
--  Eggshell fails an even simpler law:  'fmap fst (mzip ma ma) /= ma', as the content
--  of stdout/stderr would get duplicated in the LHS.

-- NOTE: Obviously valid.
instance Functor Egg where
    fmap f (MkEggUnchecked xs) = MkEggUnchecked (fmap f xs)

-- NOTE: Validity follows from proof of Monad
instance Applicative Egg where
    pure = MkEggUnchecked . pure
    (MkEggUnchecked fs) <*> (MkEggUnchecked xs) = MkEggUnchecked (fs <*> xs)

-- NOTE:  NOT PROVEN   FIXME
instance Monad Egg where
    (MkEggUnchecked xs) >>= f = MkEggUnchecked $ xs >>= (runEgg . f)

-- NOTE:  NOT PROVEN   FIXME
instance MonadIO Egg where
    liftIO = MkEggUnchecked . liftIO

-- NOTE: Egg deliberately does not implement MonadManaged;
--       MonadManaged is for types where (>>=) DOES expose LHS resources to the RHS.

-------------
-- TYPE CLASS
-------------

-- FIXME: Laws?
-- | Type class for lifting 'Egg's into other monads.
--
-- ...laws? What are those?
class (MonadIO egg)=> MonadEgg egg where
    liftEgg :: Egg a -> egg a

instance MonadEgg Eggshell where
    liftEgg = runEgg
instance MonadEgg Egg where
    liftEgg = id

---------------------------
-- INTERNAL HELPERS
---------------------------

-- Voids and units both show up all over the place here,
-- and getting the distinction between them right is crucial.
-- A little bit of consistent nomenclature goes a long way.

-- Unfortunately, "null" and "unit" surprisingly take a bit of effort
--  to distinguish visually in the font I'm using, and we're already
--  re-exporting something under the name "void" by proxy through Turtle.
-- So... vood it is.

-- An empty stream. (identity of (<|>))
vood :: Eggshell b
vood = empty

-- A unit stream. (left-identity of (>>))
unit :: (MonadEgg egg)=> egg ()
unit = pure () & liftEgg

-- Creates an empty stream with a single line of stdout.
voodOut :: Line -> Eggshell b
voodOut = Eggshell . pure . Left . Right

-- Creates an empty stream with a single line of stderr.
voodErr :: Line -> Eggshell b
voodErr = Eggshell . pure . Left . Left

-- Creates a unit stream with a single line of stdout.
unitOut :: (MonadEgg egg)=> Line -> egg ()
unitOut = egg . Eggshell . pure . Left . Right

-- Creates a unit stream with a single line of stderr.
unitErr :: (MonadEgg egg)=> Line -> egg ()
unitErr = egg . Eggshell . pure . Left . Left

voodIO :: IO a -> Eggshell b
voodIO a = liftIO a >> vood

unitIO :: (MonadEgg egg)=> IO a -> egg ()
unitIO a = liftIO a >> unit

-- Case analysis for 'Either (Either a b) c'
item :: (e -> x) -> (u -> x) -> (v -> x) -> Item e u v -> x
item f g h = either (either f g) h

itemToErr :: Item e u v -> Maybe e
itemToOut :: Item e u v -> Maybe u
itemToVal :: Item e u v -> Maybe v
itemToErr = item Just (const Nothing) (const Nothing)
itemToOut = item (const Nothing) Just (const Nothing)
itemToVal = item (const Nothing) (const Nothing) Just

-- Pull the entire stream up into value context.
-- Not ever really strictly necessary, but it helps eliminate a lot
--   of back and forth between Eggshell and Shell contexts.
-- Behind the scenes, we generate an object with the horrifying type of
-- (Shell (Either (Either Line Line) (Either (Either Line Line) a)))
liftRaw :: Eggshell a -> Eggshell (Item Line Line a)
liftRaw = Eggshell . fmap Right . runEggshell

-- Recover a normalish-looking eggshell from lifted content.
dunkRaw :: Item Line Line a -> Eggshell a
dunkRaw = item voodErr voodOut pure

-- Pull the entire stream up into value context while continuing
-- to stream a copy of stdout and stderr that remains untouched.
copyLiftRaw :: Eggshell a -> Eggshell (Item Line Line a)
copyLiftRaw e = Eggshell $ do
    x <- runEggshell e
    runEggshell $ item voodErr voodOut (const vood) x <|> pure x

---------------------------
-- UTILS: STRING CONVERSION
---------------------------

instance StringConvert.ToString FilePath where
    toString = format fp >>> StringConvert.toString
instance StringConvert.ToString Line where
    toString = lineToText >>> StringConvert.toString

-- turtle took the name 's', so here's a name that succinctly sums up
-- my feelings every time I find that I need to fit a rectangular peg
-- into a rounded-rectangular hole.
idgaf :: (StringConvert.ToString a, IsString b) => a -> b
idgaf = StringConvert.s

-------------------------
-- UTILS: MORE IO ACTIONS
-------------------------

-- | @ln -s src dest@
symlink :: (MonadIO io)=> FilePath -> FilePath -> io ()
symlink contents loc = liftIO $ createSymbolicLink (idgaf contents) (idgaf loc)

-- | @ln -s "$(realpath src)" dest@
symlinkAbs :: (MonadIO io)=> FilePath -> FilePath -> io ()
symlinkAbs src dest = liftIO $ realpath src >>= flip symlink dest

-----------------------
-- UTILS: TURTLE-ISH IO
-----------------------

glob :: Text -> Eggshell FilePath
glob pat = (>>= select) $ liftIO $ do
    ([matches], _) <- Glob.globDirWith Glob.matchPosix [Glob.compile (idgaf pat)] "."
    return $ fromString <$> matches

-- | Print a line to a file.
hPutStrLn :: (MonadIO io)=> Handle -> Line -> io ()
hPutStrLn handle = liftIO . Text.IO.hPutStrLn handle . idgaf

-- | Modify a file, in-place.
--   (I hope you know what you're doing...)
editFile :: (MonadIO io)=> FilePath -> (Text -> Text) -> io ()
editFile path change = liftIO $ do
    text <- change <$> Text.IO.readFile (idgaf path)
    Text.IO.writeFile (idgaf path) text

-- XXX Obsoleted by 'tracing' ?
-- | Use a 'Managed', printing lines to the /global/ stderr on entry and exit.
traceManaged :: (MonadManaged m)=> Line -> Managed a -> m a
traceManaged s = (tracing s >>) . using

-- | A 'Managed' that prints lines to the /global/ stderr on entry and exit.
tracing :: (MonadManaged m)=> Line -> m ()
tracing s = using $ managed $ bracket
    (traceIO $ idgaf $ "Entering: " <> s)
    (const (traceIO $ idgaf $ "Leaving: "  <> s))

-----------------------------------------
-- UTILS: TURTLY REPLACEMENTS FOR EXSHELL
-----------------------------------------

-- | Echo a diagnostic string to local stderr and fail via an exit-code Exception.
die :: (MonadEgg egg)=> Text -> egg b
die t = liftEgg $ err t >> exit (ExitFailure 1)

-- | Lifted from 'Turtle.exit'.  Exit via an Exception (possibly successfully).
exit :: (MonadEgg egg)=> ExitCode -> egg b
exit = liftEgg . MkEggUnchecked . Eggshell . Turtle.exit

-- | Emits no values, short-circuiting the rest of the monadic computation
--   (i.e. the parts that come textually after the continue).
--
-- Unsuitable for large-scale usage as it may be difficult to determine where
-- control-flow will resume. Generally it will resume with the next iteration of
-- the closest enclosing (i.e. textually prior) statement in a do block.
-- 'egg' and '(<|>)' will also "catch" continues, allowing execution to resume
-- from that point.
--
-- (...actually it's just an alias for 'empty'.)
continue :: Eggshell b -- NOTE: Not MonadEgg, because those can't be empty.
continue = vood

-- | Echo to local stdout, appending a newline at the end.
--
-- What? /Of course/ you can echo more than one line, silly! Why would you think otherwise!?
echo :: (MonadEgg egg)=> Text -> egg ()
echo = egg . Eggshell . fmap (Left . Right) . Turtle.select . textToLines

-- | Echo to local stderr, appending a newline at the end.
err :: (MonadEgg egg)=> Text -> egg ()
err = egg . Eggshell . fmap (Left . Left) . Turtle.select . textToLines

-- | Produce an Eggshell that emits the given values, and no stdout/stderr.
select :: [a] -> Eggshell a
select = Eggshell . fmap Right . Turtle.select

-- | Eggshell's answer to 'Turtle.sh'.
--
--   Box an 'Eggshell' up into an 'Egg', encapsulating all loops and
--   managed resources, and throwing away all values. Stderr/stdout remain.
egg :: (MonadEgg egg)=> Eggshell a -> egg ()
egg = unitify >>> MkEggUnchecked >>> liftEgg

data Feline = Feline !Feline

ls :: FilePath -> Eggshell FilePath
ls = fromShell . Turtle.ls
lsif :: (FilePath -> IO Bool) -> FilePath -> Eggshell FilePath
lsif = (fromShell .) . Turtle.lsif
lstree :: FilePath -> Eggshell FilePath
lstree = fromShell . Turtle.lstree

-- | Hates Mondays. Go use 'msum' instead.
cat :: Feline
cat = error "cat: mrrow!"

grep :: Pattern a -> Shell Line -> Eggshell Line
grep = (fromShell .) . Turtle.grep
sed :: Pattern Text -> Shell Line -> Eggshell Line
sed = (fromShell .) . Turtle.sed
find :: Pattern a -> FilePath -> Eggshell FilePath
find = (fromShell .) . Turtle.find
yes :: a -> Eggshell a
yes a = select $ cycle [a]
endless :: Eggshell ()
endless = yes ()

-- NOTE: these guys are tricky
-- nl paste limit limitWhile



---------------------------
-- UTILS: SHELL COMBINATORS
---------------------------

-- NOTE: not "voodify" because it's public API :P

-- | Make an Eggshell produce no values, while preserving its stdout/stderr.
--
-- Empty eggshells are the identity of '(<|>)', at least in terms of values;
-- they contribute their stdout/stderr to a stream without affecting the values.
-- But be careful! __An empty stream in the middle of a @do@ block will
-- short circuit the rest of the computation!__
voidify :: Eggshell a -> Eggshell b
voidify = (>> vood)

-- | Make an Eggshell unitlike.
--
-- Runs a stream to completion (forwarding stderr and stdout),
-- closes all managed resources, and then produces a single unit.
--
-- All exceptions (including ExitSuccess) will propagate through this.
unitify :: Eggshell a -> Eggshell ()
unitify = voidify >>> (<|> unit)

-- FIXME: horrible name
-- | 'replicate' for Shells (or at least, those without input)
thisMany :: Int -> Eggshell a -> Eggshell a
thisMany n cmd = select (replicate n ()) >> cmd

-- NOTE: THE FOLLOWING IMPLEMENTATION IS BAD!!!!!
--       'limit' is apparently strict!
--thisMany n cmd = (limit n endless) >> cmd

-------------------------------
-- UTILS: CONVERSIONS TO TURTLE
-------------------------------

shellLefts :: Shell (Either l r) -> Shell l
shellLefts = (>>= either pure (const empty))
shellRights :: Shell (Either l r) -> Shell r
shellRights = (>>= either (const empty) pure)

-- | Crack the egg to find a Turtle Shell that puts stdout, stderr, and values all together
--   in a single stream! What a mess!!
toErrOutShell :: Eggshell a -> Shell (Either (Either Line Line) a)
toErrOutShell = runEggshell

-- | Crack the egg to get a Turtle Shell with the same values; stdout and stderr are lost.
toShell :: Eggshell a -> Shell a
toShell = shellRights . runEggshell

-- | Crack the egg to get stderr/stdout, throwing away values.
toErrOut :: Eggshell a -> Shell (Either Line Line)
toErrOut = shellLefts . runEggshell

-- | Crack the egg to get stderr, throwing away stdout and values.
toErr :: Eggshell a -> Shell Line
toErr = shellLefts . shellLefts . runEggshell

-- | Crack the egg to get stdout, throwing away stderr and values.
toOut :: Eggshell a -> Shell Line
toOut = shellRights . shellLefts . runEggshell

-- | Wrap an eggshell around a really messy turtle shell that puts stdout, stderr,
--   and values all together in one stream, oh god what is this
fromErrOutShell :: Shell (Either (Either Line Line) a) -> Eggshell a
fromErrOutShell = Eggshell

-- | Wrap an eggshell around a turtle shell, producing the same values.
fromShell :: Shell a -> Eggshell a
fromShell = Eggshell . fmap Right

-- NOTE: I am unconvinced that fromOut/etc. are a good idea,
--       because it might not be obvious that they are voidlike.
--       (an unsuspecting user might put 'fromOut shell' in a do block)

-- -- | Wrap an eggshell around a turtle shell containing stderr and stdout.
-- fromErrOut :: Shell (Either Line Line) -> Eggshell a
-- fromErrOut = Eggshell . fmap Left

-- -- | Wrap an eggshell around a turtle shell containing stderr.
-- fromErr :: Shell Line -> Eggshell a
-- fromErr = Eggshell . fmap Left . fmap Left

-- -- | Wrap an eggshell around a turtle shell containing stdout.
-- fromOut :: Shell Line -> Eggshell a
-- fromOut = Eggshell . fmap Left . fmap Right

-- NOTE: Any attempt to split Err and Out into separate streams will require some form
--       of concurrency and/or buffering. Instead, we have functions which take callbacks:

-- | Crack the egg to get stdout... and toss stderr into the global stderr
--   so that it at least shows up SOMEWHERE.
--
-- This is a stopgap measure for until there's a better story to "pipe" eggshells.
toOut' :: Eggshell a -> Shell Line
toOut' shell = toShell $ do
    line <- liftRaw shell
    whenJust (itemToErr line) Turtle.err
    item (const empty) pure (const empty) line

-- | For a stream with input, crack the egg to get stdout... and toss stderr into the
--   global stderr so that it at least shows up SOMEWHERE.
--
-- This is a stopgap measure for until there's a better story to "pipe" eggshells.
toPipe' :: (Shell Line -> Eggshell a) -> (Shell Line -> Shell Line)
toPipe' = fmap toOut'

-------------------------------------------
-- UTILS: OTHER FORMS OF OUTPUT REDIRECTION
-------------------------------------------

-- FIXME maybe pull apart into separate functions for stdout and stderr

-- FIXME name
-- | Let a callback synchronously intercept stdout and stderr.
share :: (_)=> (Either Line Line -> IO b) -> Eggshell a -> Eggshell a
share f shell = do
    item <- liftRaw shell
    either (unitIO . f) (const unit) item
    dunkRaw item

-- FIXME name
-- FIXME kinda niche, probably won't stick around if we can break it up
-- | This is @> >(tee out.log >&1) 2> >(tee err.log >&2)@.
tease :: FilePath -> FilePath -> Eggshell a -> Eggshell a
tease out err shell = do
    out <- writeonly out
    err <- writeonly err
    share (either (hPutStrLn err) (hPutStrLn out)) shell

-- TODO Really not sure what I want the API surface to look like
--      for finely-grained operations on stdout/stderr.
--      These are a stopgap measure.
-- FIXME: Aw geez it's even worse than I thought.
--        Take a look at that CAUTION sticker.

-- | Redirect the local stdout of an eggshell into a new file,
--   eliminating it from the stream.  (stderr will remain)
--
-- __CAUTION:__ The file handle will remain open as a resource of the
--              stream! If you need it to be written now, you must
--              'egg' or 'fold' the stream, or use 'writeOut'.
writingOut :: FilePath -> Eggshell a -> Eggshell a
writingOut = redirectingBaseImpl writeonly 'o'

-- | Redirect the local stdout of an eggshell into a file in append mode,
--   eliminating it from the stream.  (stderr will remain)
--
-- __CAUTION:__ The file handle will remain open as a resource of the
--              stream! If you need it to be written now, you must
--              'egg' or 'fold' the stream, or use 'appendOut'.
appendingOut :: FilePath -> Eggshell a -> Eggshell a
appendingOut = redirectingBaseImpl appendonly 'o'

-- | Redirect the local stderr of an eggshell into a new file,
--   eliminating it from the stream.  (stdout will remain)
--
-- __CAUTION:__ The file handle will remain open as a resource of the
--              stream! If you need it to be written now, you must
--              'egg' or 'fold' the stream, or use 'writeErr'.
writingErr :: FilePath -> Eggshell a -> Eggshell a
writingErr = redirectingBaseImpl writeonly 'e'

-- | Redirect the local stderr of an eggshell into a file in append mode,
--   eliminating it from the stream.  (stdout will remain)
--
-- __CAUTION:__ The file handle will remain open as a resource of the
--              stream! If you need it to be written now, you must
--              'egg' or 'fold' the stream, or use 'appendErr'.
appendingErr :: FilePath -> Eggshell a -> Eggshell a
appendingErr = redirectingBaseImpl appendonly 'e'

-- | Redirect the local stdout of an egg into a new file,
--   eliminating it from the stream.  (stderr will remain)
writeOut :: FilePath -> Egg a -> Egg a
writeOut = redirectBaseImpl writingOut

-- | Redirect the local stdout of an egg into a file in append mode,
--   eliminating it from the stream.  (stderr will remain)
appendOut :: FilePath -> Egg a -> Egg a
appendOut = redirectBaseImpl appendingOut

-- | Redirect the local stderr of an egg into a new file,
--   eliminating it from the stream.  (stdout will remain)
writeErr :: FilePath -> Egg a -> Egg a
writeErr = redirectBaseImpl writingErr

-- | Redirect the local stderr of an egg into a file in append mode,
--   eliminating it from the stream.  (stdout will remain)
appendErr :: FilePath -> Egg a -> Egg a
appendErr = redirectBaseImpl appendingErr

redirectingBaseImpl openonly outOrErr path shell = impl where
    impl = do
        handle <- openonly path
        liftRaw shell >>= casefun outOrErr handle
    casefun 'o' h = item voodErr (voodIO . hPutStrLn h) pure
    casefun 'e' h = item (voodIO . hPutStrLn h) voodOut pure

redirectBaseImpl ing a b = singularToEgg $ ing a (runEgg b)

-- TODO: 'proc' and 'shell' variants which stream stdout/stderr and return ExitCode.
--       This is not currently possible (?) using any API provided by turtle;
--       but once it is, these variants will be bestowed the holiest of names:
--       'proc' and 'shell'. No prefix. No suffix.

-- | Run a command and capture the exit code.
--
--   stdout and stderr are inherited from the process; this is really just 'Turtle.proc'
procGlobal :: (MonadIO io)=> Text -> [Text] -> Shell Line -> io ExitCode
procGlobal = Turtle.proc

-- | Run a command line using the shell, retrieving the exit code.
--   This command is more powerful than `proc`, but highly vulnerable to code
--    injection if you template the command line with untrusted input.
--
--   stdout and stderr are inherited from the process; this is really just 'Turtle.shell'
shellGlobal :: (MonadIO io)=> Text -> Shell Line -> io ExitCode
shellGlobal = Turtle.shell

-- | Run a command.
--
-- stdout and stderr are routed (synchronously) through the Eggshell,
-- ready for routing and processing.
--
-- FIXME: Due to a limitation in Turtle's API,
--        THIS DOES NOT SIGNAL NONZERO EXIT CODES IN ANY FASHION! (not even exceptions)
procs :: (MonadEgg egg)=> Text -> [Text] -> Shell Line -> egg ()
procs cmd args input = Turtle.inprocWithErr cmd args input & fmap Left & Eggshell & egg

-- | Run a command line using the shell, throwing 'ShellFailed' on nonzero exit codes.
--   This command is more powerful than `proc`, but highly vulnerable to code
--    injection if you template the command line with untrusted input.
--
-- stdout and stderr are routed (synchronously) through the Eggshell,
-- ready for routing and processing.
--
-- FIXME: Due to a limitation in Turtle's API,
--        THIS DOES NOT SIGNAL NONZERO EXIT CODES IN ANY FASHION! (not even exceptions)
shells :: (MonadEgg egg)=> Text -> Shell Line -> egg ()
shells cmd input = Turtle.inshellWithErr cmd input & fmap Left & Eggshell & egg

-- NOTE: Turtle(procStrict, procStrictWithErr, shellStrict, shellStrictWithErr)
--       are explicitly supported re-exports; there is no advantage to wrapping them
--       in an Eggshell.

-- ONE DAY... one day....
-- proc :: Text -> [Text] -> Shell Line -> Eggshell ExitCode
-- shell :: Text -> Shell Line -> Eggshell ExitCode


-- | Force an eggshell to simply drop its stdout, without remorse.
killOut :: Eggshell a -> Eggshell a
killOut = liftRaw >>> (>>= item voodErr (const empty) pure)

-- | Force an eggshell to simply drop its stderr, without remorse.
killErr :: Eggshell a -> Eggshell a
killErr = liftRaw >>> (>>= item (const empty) voodOut pure)

-- | Make an egg collect its stdout, while also streaming it.
--
-- For eggs with output of bounded length, this gives you an opportunity to
-- parse and make decisions upon the content of stdout.
addStrictOut :: Egg a -> Egg (Text, a)
addStrictOut = transform where
    transform = runEgg >>> copyLiftRaw >>> fold (Fold step init finish)
    init = ([], error "addStrictOut: no value!?")
    step (lines, v) = item (\_ -> (lines, v)) (\t -> (t:lines, v)) ((,) lines)
    finish (lines, v) = (linesToText (reverse lines), v)

-- | Make an egg collect its stderr, while also streaming it.
--
-- For eggs with output of bounded length, this gives you an opportunity to
-- parse and make decisions upon the content of stderr.
addStrictErr :: Egg a -> Egg (Text, a)
addStrictErr = transform where
    transform = runEgg >>> copyLiftRaw >>> fold (Fold step init finish)
    init = ([], error "addStrictErr: no value!?")
    step (lines, v) = item (\t -> (t:lines, v)) (\_ -> (lines, v)) ((,) lines)
    finish (lines, v) = (linesToText (reverse lines), v)

-- | Make an egg collect its stderr and stdout, while also streaming them.
--
-- Order is @((err, out), value)@.
addStrictErrOut :: Egg a -> Egg ((Text, Text), a)
addStrictErrOut = addStrictOut >>> addStrictErr >>> fmap (\(e,(u,v)) -> ((e,u),v))

-------------------------------------------

-- | Use a side-effectful fold to reduce a stream of values into
--   a single value.  All local stdout/stderr from both the original stream
--   and the fold are all streamed together; it's really quite the party.
--
-- Also known as "making an omelette."
foldEgg :: forall a b egg. (MonadEgg egg)=> (FoldM Egg a b) -> Eggshell a -> egg b
foldEgg (FoldM step init finish) eggshell = liftEgg $ lesson where

    lesson :: Egg b
    lesson = do
        -- An IORef is used to allow a value to escape the managed context.
        -- (the ref itself will be 'managed' by the garbage collector!)
        ref <- init >>= liftIO . newIORef

        -- a very paranoid folding shell searches for the value
        let foldShell :: Shell (Item Line Line b)
            foldShell = do
                runEggshell eggshell >>=
                    either (pure . Left) -- forward out/err
                           (\value -> runEggshell $ (>> empty) $ runEgg $ do
                               prev <- liftIO $ readIORef ref
                               next <- step prev value
                               liftIO $ writeIORef ref next)

        -- a separate shell returns the value, after (<|>) closes managed resources
        let endShell :: Shell (Item Line Line b)
            endShell = (liftIO $ readIORef ref) >>= runEggshell . runEgg . finish

        MkEggUnchecked $ Eggshell (foldShell <|> endShell)

-- | Use a pure fold to reduce a stream of values into a single value.
--   All stdout/stderr from the original stream is streamed
--   synchronously, as usual.
fold :: (MonadEgg egg)=> Fold a b -> Eggshell a -> egg b
fold f = foldEgg (Fold.generalize f)

-- | Use a "FoldM IO" on a 'Eggshell', since in all due fairness,
--   you probably don't have too many "FoldM Egg"s lying around.
foldIO :: (MonadEgg egg)=> FoldM IO a b -> Eggshell a -> egg b
foldIO f = foldEgg (regeneralize liftIO f)

-- FIXME don't like this name;  the 'interact' in base is for programs
--       that have no side-effects
-- | Connect all of stdin, stdout, and stderr of a shell to the
--   process' global streams.
interact :: (MonadIO io)=> (Shell Line -> Eggshell a) -> io ()
interact s = result where
    t = (s Turtle.stdin) :: Eggshell _
    t' = () <$ t
    u = runEggshell t' :: Turtle.Shell (Item Line Line ())
    v = u >>= item Turtle.err Turtle.echo pure :: Turtle.Shell ()
    result = Turtle.sh v :: (MonadIO io)=> io ()

-- Interact with an eggshell that takes no stdin.  Geddit?
outeract :: (MonadIO io)=> Eggshell a -> io ()
outeract = interact . const

regeneralize :: (forall c. m c -> m' c) -> FoldM m a b -> FoldM m' a b
regeneralize lift0 (FoldM step init finish) = f where
    f = FoldM (lift2 step) (lift0 init) (lift1 finish)
    lift1 = (lift0 .)
    lift2 = (lift1 .)

-- | Take an Eggshell that meets the following precondition:
--
--  1. Produces only a single value.
--
-- and transform it into a proper Egg by satisying the remaining conditions:
--
--  2. This value is the last thing it produces.
--  3. All 'Managed' resources will be closed when this value is emitted.
--
-- The input precondition is checked at runtime.
singularToEgg :: Eggshell a -> Egg a
singularToEgg = teachAnEggshellToCleanUpAfterItself

teachAnEggshellToCleanUpAfterItself :: forall a. Eggshell a -> Egg a
teachAnEggshellToCleanUpAfterItself = foldEgg onlyValueChecked where
    onlyValueChecked = FoldM step init finish
    init = pure (errUnseen, PolyId id, errMissing)
    step (_, PolyId id', _) value = id' $ pure (value, PolyId errPresent, id)
    finish (value, _, id') = id' $ pure value

    errUnseen  = error "teachAnEggToCleanUpAfterItself: You should never see this message!"
    errPresent = error "teachAnEggToCleanUpAfterItself: Stream had more than one value!"
    errMissing = error "teachAnEggToCleanUpAfterItself: Stream had no values!"

-- Util type to conceal the type of an identity-like function when it acts upon
-- something that contains itself. (without concealment it will have an infinite type)
data PolyId = PolyId (forall a. a -> a)

-- | Make an egg into IO by connecting it to the process stderr\/stdout.
loudIO :: (MonadIO io)=> Egg a -> io a
loudIO = eggIOImpl voodErr voodOut

-- | Make an egg into IO by connecting it to the process stderr,
--   and forgetting stdout.
eggIO :: (MonadIO io)=> Egg a -> io a
eggIO = eggIOImpl voodErr (const vood)

-- | Make an egg into IO by dropping its stderr/stdout.
quietIO :: (MonadIO io)=> Egg a -> io a
quietIO = eggIOImpl (const vood) (const vood)

-- | Make an egg into IO by connecting it to the process stderr\/stdout.
--   This underscored variant forgets the value.
loudIO_ :: (MonadIO io)=> Egg a -> io ()
loudIO_ = loudIO >=> const (pure ())

-- | Make an egg into IO by connecting it to the process stderr,
--   and forgetting stdout. This underscored variant forgets the value.
eggIO_ :: (MonadIO io)=> Egg a -> io ()
eggIO_ = eggIO >=> const (pure ())

-- | Convince an egg to sacrifice all of its worldly possessions--stderr,
--   stdout, and values--in the pursuit of nirvana.
quietIO_ :: (MonadIO io)=> Egg a -> io ()
quietIO_ = quietIO >=> const (pure ())

eggIOImpl :: (MonadIO io)
          => (Line -> Eggshell ())
          -> (Line -> Eggshell ())
          -> Egg a -> io a
eggIOImpl onErr onOut eg = liftIO $ do
    ref <- newIORef (error "eggIO: You shouldn't see this error message!")
    Turtle.sh . outeract
          $ liftRaw (runEgg eg)
          >>= item onErr onOut (liftIO . writeIORef ref)
    readIORef ref

------------------------------------------------
---------- FILEPATH UTILS? WHY HERE!? ----------
------------------------------------------------


-- | append "-suffix" to a path's basename
(<-.>) :: (StringConvert.ToString s)=> FilePath -> s -> FilePath
file <-.> suffix = flip FilePath.addExtensions (FilePath.extensions file)
                   $ idgaf (format (fp%"-"%s) (FilePath.dropExtensions file) (idgaf suffix))

-- | prepend "prefix-" to a path's basename
(</->) :: (StringConvert.ToString s)=> s -> FilePath -> FilePath
prefix </-> file = parent file
                   </> idgaf (format (s%"-"%fp) (idgaf prefix) (filename file))

-- a/b.d/v-w-x-y-z/1-2-3.tar.gz
-- a </> b <.> d </> v </-> w </-> x <-.> y <-.> z </> 1 </-> 2 <-.> 3 <.> tar <.> gz
-- a </> (b <.> d) </> v </-> w </-> ((x <-.> y) <-.> z) </> 1 </-> (((2 <-.> 3) <.> tar) <.> gz)
-- a </> b.d </> v </-> w </-> (x-y <-.> z) </> 1 </-> ((2-3 <.> tar) <.> gz)
-- a </> b.d </> v </-> w </-> x-y-z </> 1 </-> 2-3.tar.gz
-- a </> b.d </> (v </-> (w </-> x-y-z)) </> (1 </-> 2-3.tar.gz)
-- a </> b.d </> v-w-x-y-z </> 1-2-3.tar.gz
-- a/b.d/v-w-x-y-z/1-2-3.tar.gz
infixl 9 <.>
infixl 9 <-.>
infixr 8 </->
infixr 7 </>

-- Manually re-export these to tweak fixities
(<.>) :: FilePath -> Text -> FilePath
(<.>) = (Turtle.<.>)
(</>) :: FilePath -> FilePath -> FilePath
(</>) = (Turtle.</>)

------------------------------------------------
------------- LOOP CONSTRUCTS ------------------
------------------------------------------------

-- NOTE: I wrote this as a kind of general dual to foldEgg, but on attempting
--       to use it, it became clear that one size doesn't necessarily fit all.

--       Interestingly enough I see a 'monad-loops' library which provides
--        unfolding loops abstracted over two container types:
--        'unfoldM :: (Monad m, MonadPlus f)=> m (Maybe a) -> m (f a)'
--       But I can't quite puzzle out though what happened to 'b' in this
--        signature (I guess the state is just threaded through 'm' instead?)

unfoldEgg :: (b -> Egg (Maybe (a, b))) -> Egg b -> Eggshell a
unfoldEgg step init =
    runEgg (init >>= step) >>= \case
        Nothing -> empty
        Just (a,b) -> pure a <|> unfoldEgg step (pure b)

--------------------------------------------------
------------- TESTS FOR FOLDING ------------------
--------------------------------------------------

-- Okay so this is kind of dumb.
-- 'teachAnEggshellToCleanUpAfterItself' was written before 'foldEgg',
--   and these tests were written at the same time.

-- There's no proper test harness;  (TODO)
-- I've just been calling them from the repl and eyeballing the output.

-- A function for testing "bad" inputs to the function, to verify that errors are
-- thrown even when there are no data dependencies on the egg's value
tcValueIgnoringMain :: Eggshell b -> IO ()
tcValueIgnoringMain e = interact . const $
    runEgg (teachAnEggshellToCleanUpAfterItself e)

-- A function for testing "good" inputs, to verify that values are emitted at the
-- proper time, and that Managed resources are cleaned up properly.
tcValueShowingMain :: (Show b)=> Eggshell b -> IO ()
tcValueShowingMain e = interact . const $
    runEgg (teachAnEggshellToCleanUpAfterItself e >>= echo . repr)

-- Expected:
--   ()
testSuperSimple :: IO ()
testSuperSimple = tcValueShowingMain unit

-- Expected:
--   Entering: lol
--   out
--   err after val
--   out after val
--   Leaving: lol
--   3
testGeneralCaseWithCleanup :: IO ()
testGeneralCaseWithCleanup = tcValueShowingMain $ using (tracing "lol") >> msum
    [ voodOut "out"
    , pure 3
    , voodErr  "err after val"
    , voodOut "out after val"
    ]

-- Expected:
--   *** Exception: teachAnEggshellToCleanUpAfterItself: Stream had no values!
testNothingAtAll :: IO ()
testNothingAtAll = tcValueIgnoringMain vood

-- Expected:
--   stdout
--   stderr
--   stdout again
--   *** Exception: teachAnEggshellToCleanUpAfterItself: Stream had no values!
testNoValues :: IO ()
testNoValues = tcValueIgnoringMain $ msum
    [ voodOut "stdout"
    , voodErr "stderr"
    , voodOut "stdout again"
    ]

-- Expected:
--   *** Exception: teachAnEggshellToCleanUpAfterItself: Stream had more than one value!
testTwoValues :: IO ()
testTwoValues = tcValueIgnoringMain $ msum
    [ pure 2
    , pure 3
    ]

-- Expected:
--   out
--   err
--   *** Exception: teachAnEggshellToCleanUpAfterItself: Stream had more than one value!
testTwoValuesWithOutput :: IO ()
testTwoValuesWithOutput = tcValueIgnoringMain $ msum
    [ voodOut "out"
    , pure 2
    , voodErr "err"
    , pure 3
    -- actually, chalk this one up to "implementation detail"
    -- , voodOut "you won't see this"
    ]

-- Expected:
--   Entering: lol
--   Leaving: lol
--   *** Exception: teachAnEggshellToCleanUpAfterItself: Stream had more than one value!
testProperCleanupForBadInput :: IO ()
testProperCleanupForBadInput = tcValueIgnoringMain $ using (tracing "lol") >> msum
    [ pure 2
    , pure 3
    ]

-- NOTE: This is currently the only test for more general folds.
--       It is the complete antithesis of all good testing practice,
--         and covers pretty much everything under the sun in one go.
--
--       As above, the only testing harness in place is the repl + your eyeballs.
--       I am sorry.
--
--       More specifically, it covers:
--         * output in init, step, and finish functions
--           (both that they ARE streamed, as well as WHEN)
--         * Timing of closed resources (via 'tracing')
--         * More verification that resources are open during the input stream
--           (via debuggingManaged and the IORef)
--
--       (Okay, so maybe not "everything under the sun"...)

-- Expected:
--   called init
--   Entering: lol
--   out yall
--   err yall
--   Got the number 2 which is:
--        this many
--        this many
--   If this prints '0' we got serious issues: 1
--   Got the number 3 which is:
--        this many
--        this many
--        this many
--   Got the number 5 which is:
--        this many
--        this many
--        this many
--        this many
--        this many
--   tell
--   Leaving: lol
--   called finish
testFoldEgg :: IO ()
testFoldEgg = interact $ const $ runEgg $ foldEgg f e where
    e :: Eggshell Int
    e = using (tracing "lol") >> using debuggingManaged >>= \x -> msum
        [ voodOut "out yall"
        , voodErr "err yall"
        , pure 2
        , liftIO (readIORef x) >>=
            (\s -> voodErr $ "If this prints '0' we got serious issues: " <> idgaf (repr s))
        , pure 3
        , pure 5
        , voodErr "tell"
        ]
    f = FoldM
        (\s n -> do
            echo $ "Got the number " <> repr n <> " which is:"
            egg $ thisMany n $ echo "     this many"
            pure (s+n))
        (echo "called init" >> pure 0)
        (\n -> do
            echo "called finish"
            pure n)

-- Expected:
testUnfoldEgg :: IO ()
testUnfoldEgg = interact $ const $ runEgg $ foldEgg f e where
    e :: Eggshell Int
    e = unfoldEgg step init where
        init = echo "unfold init" >> pure 2
        step 10 = echo "unfold stop" >> pure Nothing
        step x = do
            echo $ "Testing " <> repr x
            if any ((==0) . (x `mod`)) [2..x-1]
                then step (x+1)
                else pure $ Just (x*x, x+1)

    f = FoldM
        (\s n -> do (echo $ "Adding " <> repr n <> " to sum: " <> repr (s+n)) >> pure (s+n))
        (echo "fold init" >> pure 0)
        (\n -> echo "called finish" >> pure n)

debuggingManaged :: Managed (IORef Int)
debuggingManaged = using $ managed $ bracket
    (newIORef 1)
    (flip writeIORef 0)

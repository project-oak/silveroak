{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module AltOneBitAdder where

import qualified Prelude
import qualified AltCava
import qualified Ascii
import qualified Datatypes
import qualified String

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

reorg1Fn :: (Datatypes.Coq_prod a1 (Datatypes.Coq_prod a1 a1)) ->
            Datatypes.Coq_prod (Datatypes.Coq_prod a1 a1)
            (Datatypes.Coq_prod a1 a1)
reorg1Fn cinab =
  case cinab of {
   Datatypes.Coq_pair cin s ->
    case s of {
     Datatypes.Coq_pair a b -> Datatypes.Coq_pair (Datatypes.Coq_pair cin a)
      (Datatypes.Coq_pair a b)}}

reorg1 :: AltCava.Coq_cava
reorg1 =
  AltCava.Reshape (AltCava.Tuple2 AltCava.Bit (AltCava.Tuple2 AltCava.Bit
    AltCava.Bit)) (AltCava.Tuple2 (AltCava.Tuple2 AltCava.Bit AltCava.Bit)
    (AltCava.Tuple2 AltCava.Bit AltCava.Bit)) (unsafeCoerce (\_ -> reorg1Fn))

reorg2Fn :: (Datatypes.Coq_prod (Datatypes.Coq_prod a1 a1) a1) ->
            Datatypes.Coq_prod (Datatypes.Coq_prod a1 a1)
            (Datatypes.Coq_prod a1 (Datatypes.Coq_prod a1 a1))
reorg2Fn cinaps =
  case cinaps of {
   Datatypes.Coq_pair s ps ->
    case s of {
     Datatypes.Coq_pair cin a -> Datatypes.Coq_pair (Datatypes.Coq_pair cin
      ps) (Datatypes.Coq_pair ps (Datatypes.Coq_pair a cin))}}

reorg2 :: AltCava.Coq_cava
reorg2 =
  AltCava.Reshape (AltCava.Tuple2 (AltCava.Tuple2 AltCava.Bit AltCava.Bit)
    AltCava.Bit) (AltCava.Tuple2 (AltCava.Tuple2 AltCava.Bit AltCava.Bit)
    (AltCava.Tuple2 AltCava.Bit (AltCava.Tuple2 AltCava.Bit AltCava.Bit)))
    (unsafeCoerce (\_ -> reorg2Fn))

oneBitAdder :: AltCava.Coq_cava
oneBitAdder =
  AltCava.Compose (AltCava.Tuple2 AltCava.Bit (AltCava.Tuple2 AltCava.Bit
    AltCava.Bit)) (AltCava.Tuple2 (AltCava.Tuple2 AltCava.Bit AltCava.Bit)
    (AltCava.Tuple2 AltCava.Bit AltCava.Bit)) (AltCava.Tuple2 AltCava.Bit
    AltCava.Bit) reorg1 (AltCava.Compose (AltCava.Tuple2 (AltCava.Tuple2
    AltCava.Bit AltCava.Bit) (AltCava.Tuple2 AltCava.Bit AltCava.Bit))
    (AltCava.Tuple2 (AltCava.Tuple2 AltCava.Bit AltCava.Bit) AltCava.Bit)
    (AltCava.Tuple2 AltCava.Bit AltCava.Bit)
    (AltCava.second (AltCava.Tuple2 AltCava.Bit AltCava.Bit) AltCava.Bit
      (AltCava.Tuple2 AltCava.Bit AltCava.Bit) AltCava.xor2) (AltCava.Compose
    (AltCava.Tuple2 (AltCava.Tuple2 AltCava.Bit AltCava.Bit) AltCava.Bit)
    (AltCava.Tuple2 (AltCava.Tuple2 AltCava.Bit AltCava.Bit) (AltCava.Tuple2
    AltCava.Bit (AltCava.Tuple2 AltCava.Bit AltCava.Bit))) (AltCava.Tuple2
    AltCava.Bit AltCava.Bit) reorg2 (AltCava.Par2 (AltCava.Tuple2 AltCava.Bit
    AltCava.Bit) (AltCava.Tuple2 AltCava.Bit (AltCava.Tuple2 AltCava.Bit
    AltCava.Bit)) AltCava.Bit AltCava.Bit AltCava.xorcy AltCava.Muxcy)))

oneBitAdder_top :: AltCava.Coq_cava
oneBitAdder_top =
  AltCava.Compose (AltCava.Tuple2 AltCava.Bit (AltCava.Tuple2 AltCava.Bit
    AltCava.Bit)) (AltCava.Tuple2 AltCava.Bit (AltCava.Tuple2 AltCava.Bit
    AltCava.Bit)) (AltCava.Tuple2 AltCava.Bit AltCava.Bit) (AltCava.Par2
    AltCava.Bit (AltCava.Tuple2 AltCava.Bit AltCava.Bit) AltCava.Bit
    (AltCava.Tuple2 AltCava.Bit AltCava.Bit) (AltCava.Input AltCava.Bit
    (String.String (Ascii.Ascii Datatypes.Coq_true Datatypes.Coq_true
    Datatypes.Coq_false Datatypes.Coq_false Datatypes.Coq_false
    Datatypes.Coq_true Datatypes.Coq_true Datatypes.Coq_false) (String.String
    (Ascii.Ascii Datatypes.Coq_true Datatypes.Coq_false Datatypes.Coq_false
    Datatypes.Coq_true Datatypes.Coq_false Datatypes.Coq_true
    Datatypes.Coq_true Datatypes.Coq_false) (String.String (Ascii.Ascii
    Datatypes.Coq_false Datatypes.Coq_true Datatypes.Coq_true
    Datatypes.Coq_true Datatypes.Coq_false Datatypes.Coq_true
    Datatypes.Coq_true Datatypes.Coq_false) String.EmptyString))))
    (AltCava.Par2 AltCava.Bit AltCava.Bit AltCava.Bit AltCava.Bit
    (AltCava.Input AltCava.Bit (String.String (Ascii.Ascii Datatypes.Coq_true
    Datatypes.Coq_false Datatypes.Coq_false Datatypes.Coq_false
    Datatypes.Coq_false Datatypes.Coq_true Datatypes.Coq_true
    Datatypes.Coq_false) String.EmptyString)) (AltCava.Input AltCava.Bit
    (String.String (Ascii.Ascii Datatypes.Coq_false Datatypes.Coq_true
    Datatypes.Coq_false Datatypes.Coq_false Datatypes.Coq_false
    Datatypes.Coq_true Datatypes.Coq_true Datatypes.Coq_false)
    String.EmptyString)))) (AltCava.Compose (AltCava.Tuple2 AltCava.Bit
    (AltCava.Tuple2 AltCava.Bit AltCava.Bit)) (AltCava.Tuple2 AltCava.Bit
    AltCava.Bit) (AltCava.Tuple2 AltCava.Bit AltCava.Bit) oneBitAdder
    (AltCava.Par2 AltCava.Bit AltCava.Bit AltCava.Bit AltCava.Bit
    (AltCava.Output AltCava.Bit (String.String (Ascii.Ascii
    Datatypes.Coq_true Datatypes.Coq_true Datatypes.Coq_false
    Datatypes.Coq_false Datatypes.Coq_true Datatypes.Coq_true
    Datatypes.Coq_true Datatypes.Coq_false) (String.String (Ascii.Ascii
    Datatypes.Coq_true Datatypes.Coq_false Datatypes.Coq_true
    Datatypes.Coq_false Datatypes.Coq_true Datatypes.Coq_true
    Datatypes.Coq_true Datatypes.Coq_false) (String.String (Ascii.Ascii
    Datatypes.Coq_true Datatypes.Coq_false Datatypes.Coq_true
    Datatypes.Coq_true Datatypes.Coq_false Datatypes.Coq_true
    Datatypes.Coq_true Datatypes.Coq_false) String.EmptyString))))
    (AltCava.Output AltCava.Bit (String.String (Ascii.Ascii
    Datatypes.Coq_true Datatypes.Coq_true Datatypes.Coq_false
    Datatypes.Coq_false Datatypes.Coq_false Datatypes.Coq_true
    Datatypes.Coq_true Datatypes.Coq_false) (String.String (Ascii.Ascii
    Datatypes.Coq_true Datatypes.Coq_true Datatypes.Coq_true
    Datatypes.Coq_true Datatypes.Coq_false Datatypes.Coq_true
    Datatypes.Coq_true Datatypes.Coq_false) (String.String (Ascii.Ascii
    Datatypes.Coq_true Datatypes.Coq_false Datatypes.Coq_true
    Datatypes.Coq_false Datatypes.Coq_true Datatypes.Coq_true
    Datatypes.Coq_true Datatypes.Coq_false) (String.String (Ascii.Ascii
    Datatypes.Coq_false Datatypes.Coq_false Datatypes.Coq_true
    Datatypes.Coq_false Datatypes.Coq_true Datatypes.Coq_true
    Datatypes.Coq_true Datatypes.Coq_false) String.EmptyString)))))))


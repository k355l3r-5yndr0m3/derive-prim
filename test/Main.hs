{-# LANGUAGE LexicalNegation #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DataKinds #-}
module Main (main) where
import Control.Monad
import Control.Monad.ST

import Data.Primitive
import Data.Primitive.ByteArray.Unaligned
import Data.Primitive.Generic
import Data.Word
import Data.Int

import System.Exit (exitFailure)
import GHC.Generics

data Struct1 = Struct1 Char Int32 Float Word64
  deriving (Generic, Eq)
  deriving (Prim, PrimUnaligned) via (GenericPrim Struct1)

data Struct2 = Struct2 Word8 Struct1
  deriving (Generic, Eq)
  deriving (Prim, PrimUnaligned) via (GenericPrim Struct2)

deriving newtype instance Eq (Packed Struct2)
data Struct3 = Struct3 Word16 (Packed Struct2)
  deriving (Generic, Eq)
  deriving (Prim, PrimUnaligned) via (GenericPrim Struct3)

data Struct4 = Struct4
  { membA :: Int
  , membB :: Float
  , membC :: Int
  , membD :: Int8
  } deriving (Generic, Eq) 
    deriving (Prim, PrimUnaligned) via (GenericPrim Struct4)

testPrim :: (Eq a, Prim a) => [a] -> Bool
testPrim list = ba
  where listLen = length list
        ba = runST do
          mutarr <- newPrimArray listLen
          zipWithM_ (writePrimArray mutarr) [0..] list
          readWork <- and <$> zipWithM (\ idx value -> (value ==) <$> readPrimArray mutarr idx ) [0..] list
          array <- unsafeFreezePrimArray mutarr
          let idxWork = and $ zipWith (\ idx value -> value == indexPrimArray array idx ) [0..] list
          return $ readWork && idxWork

main :: IO ()
main = do 
  unless (testPrim [ Struct1 '3' 523 0.41 8371
                   , Struct1 '5' -32 99.0 33
                   , Struct1 '2' 902 3.02 0
                   ]) exitFailure
  unless (testPrim [ Struct2 32 $ Struct1 '3' 523 0.41 8371
                   , Struct2 02 $ Struct1 '5' -32 99.0 33
                   , Struct2 03 $ Struct1 '2' 902 3.02 0
                   ]) exitFailure
  unless (testPrim [ Struct3 2 $ Align $ Struct2 32 $ Struct1 '3' 523 0.41 8371
                   , Struct3 1 $ Align $ Struct2 02 $ Struct1 '5' -32 99.0 33
                   , Struct3 6 $ Align $ Struct2 03 $ Struct1 '2' 902 3.02 0
                   ]) exitFailure
  print (offsetOf @Struct4 @"membD")

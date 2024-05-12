{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Data.Primitive.Generic
  ( Align(..), Packed
  , GenericPrim(..)
  , offsetOf
  ) where
import Data.Semigroup
import Data.Functor.Identity
import Data.Functor.Const
import Data.Complex 
import Data.Primitive.ByteArray.Unaligned
import Data.Primitive
import Data.Proxy
import Data.Kind (Type)

import Foreign.C
import Foreign.Ptr

import System.Posix.Types

import GHC.Generics
import GHC.Stable
import GHC.TypeLits
import GHC.Exts hiding (setByteArray#)

-- |A wrapper that modify the wrapped type alignment
newtype Align (a :: Nat) t = Align t
  deriving newtype (PrimUnaligned)

-- |Modify type to have alignment of 1
type Packed = Align 1
type family ValidAlign (n :: Nat) :: Constraint where
  ValidAlign 0 = TypeError (Text "Alignment must be strictly possitive (> 0)")
  ValidAlign _ = ()

-- |Derive Prim and PrimUnaligned instances
newtype GenericPrim a = GenericPrim a

instance (ValidAlign a, KnownNat a, Prim t) => Prim (Align a t) where
  alignmentOfType# _ = align#
    where !(I# align#) = fromIntegral (natVal @a Proxy)
  sizeOfType# _ = sizeOfType# @t Proxy
  indexByteArray# ba# idx# = Align (indexByteArray# ba# idx#)
  readByteArray# ba# idx# state# =
    let !(# state'#, value #) = readByteArray# ba# idx# state#
    in  (# state'#, Align value #)
  writeByteArray# ba# idx# (Align value) = writeByteArray# ba# idx# value

  indexOffAddr# addr# idx# = Align (indexOffAddr# addr# idx#)
  readOffAddr# addr# idx# state# =
    let !(# state'#, value #) = readOffAddr# addr# idx# state# 
    in  (# state'#, Align value #)
  writeOffAddr# addr# idx# (Align value) = writeOffAddr# addr# idx# value

-- TODO: Implement a plugin to make the performance not terrible
instance (Generic a, DerivePrim (Rep a)) => PrimUnaligned (GenericPrim a) where
  indexUnalignedByteArray# ba# offs# = GenericPrim (to (implIndexUnalignedByteArray# (membOffsets @(Rep a)) ba# offs#))
  readUnalignedByteArray# ba# offs# state# =
    let !(# state'#, value #) = implReadUnalignedByteArray# (membOffsets @(Rep a)) ba# offs# state#
    in  (# state'#, GenericPrim (to value) #)
  writeUnalignedByteArray# ba# offs# (GenericPrim (from -> value)) = implWriteUnalignedByteArray# (membOffsets @(Rep a)) ba# offs# value

type family Or (a :: Bool) (b :: Bool) :: Bool where
  Or False False = False
  Or _     _     = True

type family HasOffsetOf t (s :: Symbol) :: Bool where
  HasOffsetOf (f :*: g) s = Or (HasOffsetOf f s) (HasOffsetOf g s)
  HasOffsetOf (M1 _ (MetaSel (Just s) _ _ _) _) s = True
  HasOffsetOf (M1 _ _ f) s = HasOffsetOf f s
  HasOffsetOf _ _ = False

type family Assert (s :: Symbol) (c :: Bool) :: Constraint where
  Assert _ True  = ()
  Assert s False = TypeError (Text s)

type family Equal a b :: Bool where
  Equal a a = True
  Equal _ _ = False


class KnownBool (b :: Bool) where
  boolVal :: Proxy b -> Bool
  ifBool  :: a -> a -> Proxy b -> a
instance KnownBool True where
  boolVal _ = True
  ifBool _ a _ = a
  
instance KnownBool False where
  boolVal _ = False
  ifBool a _ _ = a

instance (Generic a, DerivePrim (Rep a)) => Prim (GenericPrim a) where
  sizeOfType# _ = structSize# @(Rep a) Proxy
  alignmentOfType# _ = structAlign# @(Rep a) Proxy

  indexByteArray# ba# idx# = GenericPrim (to (implIndexUnalignedByteArray# (membOffsets @(Rep a)) ba# (idx# *# structSize# @(Rep a) Proxy)))
  readByteArray# ba# idx# state# =
    let !(# state'#, value #) = implReadUnalignedByteArray# (membOffsets @(Rep a)) ba# (idx# *# structSize# @(Rep a) Proxy) state# 
    in  (# state'#, GenericPrim (to value) #)
  writeByteArray# ba# idx# (GenericPrim (from -> value)) = implWriteUnalignedByteArray# (membOffsets @(Rep a)) ba# (idx# *# structSize# @(Rep a) Proxy) value

  indexOffAddr# addr# idx# = GenericPrim (to (implIndexUnalignedOffAddr# (membOffsets @(Rep a)) (addr# `plusAddr#` (idx# *# structSize# @(Rep a) Proxy))))
  readOffAddr# addr# idx# state# =
    let !(# state'#, value #) = implReadUnalignedOffAddr# (membOffsets @(Rep a)) (addr# `plusAddr#` (idx# *# structSize# @(Rep a) Proxy)) state#
    in  (# state'#, GenericPrim (to value) #)
  writeOffAddr# addr# idx# (GenericPrim (from -> value)) = implWriteUnalignedOffAddr# (membOffsets @(Rep a)) (addr# `plusAddr#` (idx# *# structSize# @(Rep a) Proxy)) value

-- Base must be strictly possitive ( > 0 )
alignTo# :: Int# -> Int# -> Int#
alignTo# offs# base# = res#
  where padded# = offs# +# base# -# 1#
        res# = padded# -# (padded# `remInt#` base#)

class DerivePrim q where
  type DeriveTree q :: Type -> Type
  inOrder' :: (Int# -> (# Int#, Int# #) -> Int#) -> Int# -> Int#
  --         accum     alignment size        output  accum'   in accum  out accum
  inOrder  :: (Int# -> (# Int#, Int# #) -> (# Int#, Int# #)) -> Int# -> (# DeriveTree q p, Int# #)

  -- NOTE: Offset are always in bytes
  implIndexUnalignedByteArray# :: DeriveTree q p -> ByteArray# -> Int# -> q p
  implReadUnalignedByteArray#  :: DeriveTree q p -> MutableByteArray# s -> Int# -> State# s -> (# State# s, q p #)
  implWriteUnalignedByteArray# :: DeriveTree q p -> MutableByteArray# s -> Int# -> q p -> State# s -> State# s

  -- TODO: Maybe remove the index since that can be implemented by plusAddr#
  implIndexUnalignedOffAddr# :: DeriveTree q p -> Addr# -> q p
  implReadUnalignedOffAddr#  :: DeriveTree q p -> Addr# -> State# s -> (# State# s, q p #)
  implWriteUnalignedOffAddr# :: DeriveTree q p -> Addr# -> q p -> State# s -> State# s

class OffsetOf t (s :: Symbol) where
  -- | return -1 if does not contain field
  offsetOf# :: t p -> Int#
  getInt#   :: t p -> Int#

instance OffsetOf V1 s where
  offsetOf# _ = -1#
  getInt#   _ = -1#
instance OffsetOf U1 s where
  offsetOf# _ = -1#
  getInt#   _ = -1#

instance (OffsetOf f s, OffsetOf g s, KnownBool (HasOffsetOf f s), KnownBool (HasOffsetOf g s)) => OffsetOf (f :*: g) s where
  offsetOf# (f :*: g)
    | boolVal @(HasOffsetOf f s) Proxy = offsetOf# @_ @s f
    | boolVal @(HasOffsetOf g s) Proxy = offsetOf# @_ @s g
    | otherwise     = -1#

  getInt# _ = -1#
instance OffsetOf (K1 i Int) s where
  offsetOf# _ = -1#
  getInt# (K1 (I# offs#)) = offs#

instance OffsetOf c s => OffsetOf (M1 i (MetaSel (Just s') a b d) c) s where
  offsetOf# (M1 c) = getInt# @_ @s c
  getInt# (M1 c) = getInt# @_ @s c

instance OffsetOf c s => OffsetOf (M1 i (MetaSel Nothing a b d) c) s where
  offsetOf# (M1 c) = offsetOf# @_ @s c
  getInt# (M1 c) = getInt# @_ @s c

instance OffsetOf c s => OffsetOf (M1 i (MetaData a b d e) c) s where
  offsetOf# (M1 c) = offsetOf# @_ @s c
  getInt# (M1 c) = getInt# @_ @s c

instance OffsetOf c s => OffsetOf (M1 i (MetaCons a b e) c) s where
  offsetOf# (M1 c) = offsetOf# @_ @s c
  getInt# (M1 c) = getInt# @_ @s c

offsetOf :: forall t s. (Generic t, DerivePrim (Rep t), OffsetOf (DeriveTree (Rep t)) s, Assert "Field does not exist" (HasOffsetOf (DeriveTree (Rep t)) s)) => Int
offsetOf = I# (offsetOf# @_ @s (membOffsets @(Rep t)))

membOffsets :: forall q p. DerivePrim q => DeriveTree q p
membOffsets = tree
  where (# tree, _ #) = inOrder @q fn 0# 
        fn accum# (# align#, size# #) =
          let offs# = accum# `alignTo#` align#
          in  (# offs#, offs# +# size# #)

membAligns :: forall q p. DerivePrim q => DeriveTree q p
membAligns = tree
  where (# tree, _ #) = inOrder @q fn 0# 
        fn (_ :: Int#) (# align# :: Int# , _ :: Int# #) = 
          (# align#, 0# #)

membSizes :: forall q p. DerivePrim q => DeriveTree q p
membSizes = tree
  where (# tree, _ #) = inOrder @q fn 0# 
        fn (_ :: Int#) (# _ :: Int# , size# :: Int# #) = 
          (# size#, 0# #)

structSize# :: forall q. DerivePrim q => Proxy q -> Int#
structSize# p = inOrder' @q fn 0# `alignTo#` structAlign# p
  where fn offset# (# align#, size# #) = (offset# `alignTo#` align#) +# size#

structAlign# :: forall q. DerivePrim q => Proxy q -> Int#
structAlign# _ = inOrder' @q fn 1#
  where fn (I# -> accum) (# I# -> align, _ :: Int# #) = 
          let !(I# result#) = lcm accum align
          in  result#

instance DerivePrim V1 where 
  type DeriveTree V1 = V1
  inOrder' _ a = a
  inOrder  _ a = (# undefined, a #)

  implIndexUnalignedByteArray# _ _ _ = undefined
  implReadUnalignedByteArray# _ _ _ state# = (# state#, undefined #)
  implWriteUnalignedByteArray# _ _ _ _ state# = state#

  implIndexUnalignedOffAddr# _ _ = undefined
  implReadUnalignedOffAddr# _ _ state# = (# state#, undefined #)
  implWriteUnalignedOffAddr# _ _ _ state# = state#


instance DerivePrim U1 where
  type DeriveTree U1 = U1
  inOrder' fn a = fn a (# 1#, 0# #)
  inOrder  fn a = (# U1, a' #)
    where !(# _, a' #) = fn a (# 1#, 0# #)

  implIndexUnalignedByteArray# _ _ _ = U1
  implReadUnalignedByteArray# _ _ _ state# = (# state#, U1 #)
  implWriteUnalignedByteArray# _ _ _ _ state# = state#

  implIndexUnalignedOffAddr# _ _ = U1
  implReadUnalignedOffAddr# _ _ state# = (# state#, U1 #)
  implWriteUnalignedOffAddr# _ _ _ state# = state#

instance (DerivePrim f, DerivePrim g) => DerivePrim (f :*: g) where
  type DeriveTree (f :*: g) = DeriveTree f :*: DeriveTree g
  inOrder' fn a = inOrder' @g fn (inOrder' @f fn a)
  inOrder  fn a = (# f :*: g, g# #)
    where !(# f, f# #) = inOrder @f fn a
          !(# g, g# #) = inOrder @g fn f#

  implIndexUnalignedByteArray# (fi :*: gi) ba# baseOffs# = 
    implIndexUnalignedByteArray# fi ba# baseOffs# :*:
    implIndexUnalignedByteArray# gi ba# baseOffs#
  implReadUnalignedByteArray# (fi :*: gi) ba# baseOffs# state0# =
    let !(# state1#, f #) = implReadUnalignedByteArray# @f fi ba# baseOffs# state0#
        !(# state2#, g #) = implReadUnalignedByteArray# @g gi ba# baseOffs# state1#
    in  (# state2#, f :*: g #)
  implWriteUnalignedByteArray# (fi :*: gi) ba# baseOffs# (f :*: g) state# =
    implWriteUnalignedByteArray# @g gi ba# baseOffs# g (implWriteUnalignedByteArray# @f fi ba# baseOffs# f state#)

  implIndexUnalignedOffAddr# (fi :*: gi) addr# = 
    implIndexUnalignedOffAddr# fi addr# :*:
    implIndexUnalignedOffAddr# gi addr# 
  implReadUnalignedOffAddr# (fi :*: gi) addr# state0# =
    let !(# state1#, f #) = implReadUnalignedOffAddr# @f fi addr# state0#
        !(# state2#, g #) = implReadUnalignedOffAddr# @g gi addr# state1#
    in  (# state2#, f :*: g #)
  implWriteUnalignedOffAddr# (fi :*: gi) addr# (f :*: g) state# =
    implWriteUnalignedOffAddr# @g gi addr# g (implWriteUnalignedOffAddr# @f fi addr# f state#)

instance DerivePrim f => DerivePrim (M1 i t f) where
  type DeriveTree (M1 i t f) = M1 i t (DeriveTree f)
  inOrder' = inOrder' @f
  inOrder fn a = (# M1 f, f# #)
    where !(# f, f# #) = inOrder @f fn a 

  implIndexUnalignedByteArray# (M1 fi) ba# baseOffs# = M1 (implIndexUnalignedByteArray# fi ba# baseOffs#)
  implReadUnalignedByteArray# (M1 fi) ba# baseOffs# state# = 
    let !(# state'#, value #) = implReadUnalignedByteArray# fi ba# baseOffs# state# 
    in  (# state'#, M1 value #)
  implWriteUnalignedByteArray# (M1 fi) ba# baseOffs# (M1 value) =
    implWriteUnalignedByteArray# fi ba# baseOffs# value


  implIndexUnalignedOffAddr# (M1 fi) addr# = M1 (implIndexUnalignedOffAddr# fi addr#)
  implReadUnalignedOffAddr# (M1 fi) addr# state# = 
    let !(# state'#, value #) = implReadUnalignedOffAddr# fi addr# state# 
    in  (# state'#, M1 value #)
  implWriteUnalignedOffAddr# (M1 fi) addr# (M1 value) =
    implWriteUnalignedOffAddr# fi addr# value

-- NOTE: The reliant on PrimUnaligned is a little problematic since PrimUnaligned does 
-- not implement all instances of Prim (Some notable include StablePtr)
instance (Prim c, PrimUnaligned c) => DerivePrim (K1 i c) where
  type DeriveTree (K1 i c) = K1 i Int

  inOrder' fn a = fn a (# alignmentOfType# @c Proxy, sizeOfType# @c Proxy #)
  inOrder  fn a = (# K1 v, a' #)
    where !(# I# -> v, a' #) = fn a (# alignmentOfType# @c Proxy, sizeOfType# @c Proxy #)

  implIndexUnalignedByteArray# (K1 (I# membOffs#)) ba# baseOffs# = K1 (indexUnalignedByteArray# ba# (baseOffs# +# membOffs#))
  implReadUnalignedByteArray# (K1 (I# membOffs#)) ba# baseOffs# state# = (# state'#, K1 value #)
    where !(# state'#, value #) = readUnalignedByteArray# ba# (baseOffs# +# membOffs#) state#
  implWriteUnalignedByteArray# (K1 (I# membOffs#)) ba# baseOffs# (K1 value) =
    writeUnalignedByteArray# ba# (baseOffs# +# membOffs#) value

  implIndexUnalignedOffAddr# (K1 (I# membOffs#)) addr# = K1 (indexOffAddr# (addr# `plusAddr#` membOffs#) 0#)
  implReadUnalignedOffAddr# (K1 (I# membOffs#)) addr# state# = (# state'#, K1 value #)
    where !(# state'#, value #) = readOffAddr# (addr# `plusAddr#` membOffs#) 0# state#
  implWriteUnalignedOffAddr# (K1 (I# membOffs#)) addr# (K1 value) =
    writeOffAddr# (addr# `plusAddr#` membOffs#) 0# value

-- Extra PrimUnaligned instances
instance PrimUnaligned (StablePtr a) where
  indexUnalignedByteArray# ba# offset# = StablePtr (indexWord8ArrayAsStablePtr# ba# offset#)
  readUnalignedByteArray# ba# offset# state# = 
    let !(# state'#, ptr# #) = readWord8ArrayAsStablePtr# ba# offset# state# 
    in  (# state'#, StablePtr ptr# #)
  writeUnalignedByteArray# ba# offset# (StablePtr ptr#) = writeWord8ArrayAsStablePtr# ba# offset# ptr#
instance PrimUnaligned (FunPtr a) where
  indexUnalignedByteArray# ba# offset# = FunPtr (indexWord8ArrayAsAddr# ba# offset#)
  readUnalignedByteArray# ba# offset# state# = 
    let !(# state'#, ptr# #) = readWord8ArrayAsAddr# ba# offset# state# 
    in  (# state'#, FunPtr ptr# #)
  writeUnalignedByteArray# ba# offset# (FunPtr ptr#) = writeWord8ArrayAsAddr# ba# offset# ptr#
instance (Prim a, PrimUnaligned a) => PrimUnaligned (Complex a) where
  indexUnalignedByteArray# ba# offset# =
    indexUnalignedByteArray# ba# offset# :+
    indexUnalignedByteArray# ba# (offset# +# sizeOfType# @a Proxy)
  readUnalignedByteArray# ba# offset# state0# = 
    let !(# state1#, a #) = readUnalignedByteArray# ba# offset# state0# 
        !(# state2#, b #) = readUnalignedByteArray# ba# (offset# +# sizeOfType# @a Proxy) state1#
    in  (# state2#, a :+ b #)
  writeUnalignedByteArray# ba# offset# (a :+ b) state# =
    writeUnalignedByteArray# ba# (offset# +# sizeOfType# @a Proxy) b (writeUnalignedByteArray# ba# offset# a state#)

-- Derive missing instances
deriving newtype instance PrimUnaligned CBool
deriving newtype instance PrimUnaligned CClock
deriving newtype instance PrimUnaligned CFloat
deriving newtype instance PrimUnaligned CIntMax
deriving newtype instance PrimUnaligned CUIntMax
deriving newtype instance PrimUnaligned CIntPtr
deriving newtype instance PrimUnaligned CUIntPtr
deriving newtype instance PrimUnaligned CPtrdiff
deriving newtype instance PrimUnaligned CUSeconds
deriving newtype instance PrimUnaligned CSUSeconds
deriving newtype instance PrimUnaligned CSigAtomic
deriving newtype instance PrimUnaligned CSize
deriving newtype instance PrimUnaligned CTime
deriving newtype instance PrimUnaligned CUChar
deriving newtype instance PrimUnaligned CUShort
deriving newtype instance PrimUnaligned CWchar
deriving newtype instance PrimUnaligned IntPtr
deriving newtype instance PrimUnaligned WordPtr
deriving newtype instance PrimUnaligned CBlkCnt
deriving newtype instance PrimUnaligned CBlkSize
deriving newtype instance PrimUnaligned CCc
deriving newtype instance PrimUnaligned CClockId
deriving newtype instance PrimUnaligned CFsBlkCnt
deriving newtype instance PrimUnaligned CFsFilCnt
deriving newtype instance PrimUnaligned CGid
deriving newtype instance PrimUnaligned CId
deriving newtype instance PrimUnaligned CKey
deriving newtype instance PrimUnaligned CNlink
deriving newtype instance PrimUnaligned CRLim
deriving newtype instance PrimUnaligned CSpeed
deriving newtype instance PrimUnaligned CTcflag
deriving newtype instance PrimUnaligned CTimer
deriving newtype instance PrimUnaligned CUid
deriving newtype instance PrimUnaligned a => PrimUnaligned (Identity a)
deriving newtype instance PrimUnaligned a => PrimUnaligned (Down a)
deriving newtype instance PrimUnaligned a => PrimUnaligned (First a)
deriving newtype instance PrimUnaligned a => PrimUnaligned (Last a)
deriving newtype instance PrimUnaligned a => PrimUnaligned (Max a)
deriving newtype instance PrimUnaligned a => PrimUnaligned (Min a)
deriving newtype instance PrimUnaligned a => PrimUnaligned (Dual a)
deriving newtype instance PrimUnaligned a => PrimUnaligned (Product a)
deriving newtype instance PrimUnaligned a => PrimUnaligned (Sum a)
deriving newtype instance PrimUnaligned a => PrimUnaligned (Const a b)

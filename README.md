# derive-prim: Derive Prim and PrimUnaligned using Generic
## USAGE
Here is an example of how to derive the Prim and PrimUnaligned instance.
```
{-# LANGUAGE DerivingVia #-}
import Data.Primitive
import Data.Primitive.Generic
import Data.Primitive.ByteArray.Unaligned

data Struct = Struct
  { membChar  :: Char    
  , membInt   :: Int
  , membFloat :: Float
  } derive (Generic)
    derive (Prim, PrimUnaligned) via (GenericPrim Struct)
```
All members must implement both an instance of Prim and an instance of PrimUnaligned. Nested structs are also allowed as long as they implement the nessisary instances.
```
data Inside = ... 
  derive (Generic) 
  derive (Prim, PrimUnaligned) via (GenericPrim Struct)

data Outside = Outside 
  { ...
  , nested :: Inside
    ...
  } derive (Generic) derive (Prim, PrimUnaligned) via (GenericPrim Struct)
```
To tweak members placement in memory use `Align` or `Packed`.
```
data Struct = Struct 
  { ...
  , someField :: Align 4 SomeType {- This field will have an alignment of 4 bytes -}
    ...
  , someOtherField :: Packed SomeOtherType {- This field will have an alignment of 1 bytes #-}
  }
```
## Details
Members are layout in memory according to their order. Members placed higher will have a lower memory address. 
Each member's offset will be the lowest offset respecting its alignment such that no overlapping between previous members occur.
The alignment of the structure is the least common multiple of all its members' alignments.
The size of the structures is rounded up to the nearest multiple of the structure's alignment.

Currently, only data types with one constructor are supported.

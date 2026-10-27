module

/-!
SHA-256 (FIPS 180-4) in pure Lean, so a transcript digest can be checked by a
second Lean program without trusting the host's `shasum`. Compiled it runs on
native `UInt32`s; the kernel can also reduce it, which is what the theorem at
the end of this file does for the "abc" test vector.

The loops are structural recursion on fuel (never well-founded recursion), so
`decide +kernel` can unfold them.
-/

namespace LeanAgent.Sha256

public section

/-- Round constants: the first 32 bits of the fractional parts of the cube
roots of the first 64 primes. -/
public def k : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

/-- Initial hash value: the first 32 bits of the fractional parts of the square
roots of the first 8 primes. -/
public def h0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

public def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

public def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
public def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
public def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
public def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)
public def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~x) &&& z)
public def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Big-endian bytes of a 64-bit word. -/
public def beBytes64 (n : UInt64) : Array UInt8 := #[
  (n >>> 56).toUInt8, (n >>> 48).toUInt8, (n >>> 40).toUInt8, (n >>> 32).toUInt8,
  (n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8
]

/-- Big-endian bytes of a 32-bit word. -/
public def beBytes32 (n : UInt32) : Array UInt8 :=
  #[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]

/-- Padding: a 0x80 byte, zeros up to 56 mod 64, then the bit length as a
big-endian 64-bit word. The result's length is a multiple of 64. -/
public def pad (msg : Array UInt8) : Array UInt8 :=
  let zeros := (55 + 64 - msg.size % 64) % 64
  (msg.push 0x80 ++ Array.replicate zeros 0) ++ beBytes64 (msg.size * 8).toUInt64

/-- The big-endian 32-bit word at byte offset `off` (zero past the end). -/
public def wordAt (bytes : Array UInt8) (off : Nat) : UInt32 :=
  ((bytes.getD off 0).toUInt32 <<< 24) ||| ((bytes.getD (off + 1) 0).toUInt32 <<< 16) |||
    ((bytes.getD (off + 2) 0).toUInt32 <<< 8) ||| (bytes.getD (off + 3) 0).toUInt32

/-- The first 16 schedule words of the block starting at byte `base`. -/
public def loadWords (bytes : Array UInt8) (base : Nat) : Nat → Array UInt32 → Array UInt32
  | 0, w => w
  | n + 1, w => loadWords bytes base n (w.push (wordAt bytes (base + 4 * w.size)))

/-- Extend the message schedule from 16 to 64 words. -/
public def extendWords : Nat → Array UInt32 → Array UInt32
  | 0, w => w
  | n + 1, w =>
    let i := w.size
    let next := smallSigma1 (w.getD (i - 2) 0) + w.getD (i - 7) 0 +
      smallSigma0 (w.getD (i - 15) 0) + w.getD (i - 16) 0
    extendWords n (w.push next)

public structure State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

public def State.ofWords (hv : Array UInt32) : State :=
  { a := hv.getD 0 0, b := hv.getD 1 0, c := hv.getD 2 0, d := hv.getD 3 0
    e := hv.getD 4 0, f := hv.getD 5 0, g := hv.getD 6 0, h := hv.getD 7 0 }

public def State.addTo (s : State) (hv : Array UInt32) : Array UInt32 :=
  #[hv.getD 0 0 + s.a, hv.getD 1 0 + s.b, hv.getD 2 0 + s.c, hv.getD 3 0 + s.d,
    hv.getD 4 0 + s.e, hv.getD 5 0 + s.f, hv.getD 6 0 + s.g, hv.getD 7 0 + s.h]

public def round (w : Array UInt32) (i : Nat) (s : State) : State :=
  let t1 := s.h + bigSigma1 s.e + ch s.e s.f s.g + k.getD i 0 + w.getD i 0
  let t2 := bigSigma0 s.a + maj s.a s.b s.c
  { a := t1 + t2, b := s.a, c := s.b, d := s.c, e := s.d + t1, f := s.e, g := s.f, h := s.g }

public def rounds (w : Array UInt32) : Nat → Nat → State → State
  | _, 0, s => s
  | i, n + 1, s => rounds w (i + 1) n (round w i s)

/-- Compress the 64-byte block at byte offset `base` into the hash value. -/
public def compressBlock (bytes : Array UInt8) (base : Nat) (hv : Array UInt32) : Array UInt32 :=
  let w := extendWords 48 (loadWords bytes base 16 #[])
  (rounds w 0 64 (State.ofWords hv)).addTo hv

/-- Compress `n` consecutive blocks starting at byte offset `base`. -/
public def compressBlocks (bytes : Array UInt8) : Nat → Nat → Array UInt32 → Array UInt32
  | _, 0, hv => hv
  | base, n + 1, hv => compressBlocks bytes (base + 64) n (compressBlock bytes base hv)

/-- SHA-256 of a byte array, as 32 bytes. -/
public def hashBytes (msg : Array UInt8) : Array UInt8 :=
  let padded := pad msg
  let hv := compressBlocks padded 0 (padded.size / 64) h0
  hv.foldl (init := #[]) fun acc word => acc ++ beBytes32 word

/-- SHA-256 of a string's UTF-8 bytes, as 32 bytes. -/
public def hashString (s : String) : Array UInt8 :=
  hashBytes s.toUTF8.data

public def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n.toNat) else Char.ofNat ('a'.toNat + n.toNat - 10)

/-- Lowercase hex of a byte array. -/
public def hex (bytes : Array UInt8) : String :=
  bytes.foldl (init := "") fun acc b =>
    (acc.push (hexDigit (b >>> (4 : UInt8)))).push (hexDigit (b &&& (0x0f : UInt8)))

/-- Lowercase hex SHA-256 of a string's UTF-8 bytes: 64 hex characters. -/
public def hexOfString (s : String) : String :=
  hex (hashString s)

-- FIPS 180-4 test vectors.
#guard hexOfString "" == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard hexOfString "abc" == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
-- 56 bytes: the padding spills into a second block.
#guard hexOfString "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" ==
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
-- 64 bytes: exactly one block of message, padding is a whole second block.
#guard hexOfString "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef" ==
  "a8ae6e6ee929abea3afcfc5258c8ccd6f85273e0d4626d26c7279f3250f77c8e"
#guard (pad #[]).size == 64 && (pad (Array.replicate 55 0)).size == 64 &&
  (pad (Array.replicate 56 0)).size == 128 && (pad (Array.replicate 64 0)).size == 128
#guard hex #[0x00, 0x0f, 0xa5, 0xff] == "000fa5ff"
#guard (hashString "abc").size == 32

/-- The "abc" test vector, checked by the kernel rather than the evaluator. -/
public theorem hashBytes_abc :
    hashBytes #[0x61, 0x62, 0x63] = #[
      0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
      0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad
    ] := by decide +kernel

end

end LeanAgent.Sha256

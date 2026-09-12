import Mathlib.Tactic
import XRPL.Model.Protocol.Errors

set_option linter.style.nativeDecide false

namespace XRPL.Model.Protocol

abbrev rep := Int64
abbrev internalrep := UInt64

abbrev UInt128 := BitVec 128

def toUInt128 (x : UInt64) : UInt128 := x.toBitVec.zeroExtend 128
def toUInt64 (x : UInt128) : UInt64 := ⟨x.truncate 64⟩

private theorem u64_pos_of_gt {m v : UInt64} (h : m > v) : 0 < m.toNat :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) h

private theorem u64_ten_val : (10 : UInt64).toNat = 10 := by rfl

private theorem bv128_pos_of_gt {m v : BitVec 128} (h : m > v) : 0 < m.toNat :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) h

private theorem bv128_ten_val : (10 : BitVec 128).toNat = 10 := by rfl

inductive rounding_mode where
  | to_nearest | towards_zero | downward | upward
  deriving DecidableEq, Repr

def cMinValue : UInt64 := 1000000000000000
def cMaxValue : UInt64 := 9999999999999999

structure MantissaRange where
  min : UInt64
  max : UInt64
  hrange : max.toNat + 1 = 10 * min.toNat := by decide
  hfit : cMaxValue.toNat ≤ max.toNat := by decide

instance : BEq MantissaRange where
  beq a b := a.min == b.min && a.max == b.max

instance : DecidableEq MantissaRange := fun a b =>
  if h : a.min = b.min ∧ a.max = b.max then
    isTrue (by cases a; cases b; obtain ⟨rfl, rfl⟩ := h; rfl)
  else
    isFalse (by intro heq; apply h; cases heq; exact ⟨rfl, rfl⟩)

def largeRange : MantissaRange := { min := 1_000_000_000_000_000_000, max := 9_999_999_999_999_999_999 }
def cMinOffset : Int := -96
def cMaxOffset : Int := 80
def minExponent : Int := -32768
def maxExponent : Int := 32768
def maxRep : UInt64 := 9223372036854775807
def maxRepUp : UInt64 := 9223372036854775810

structure Number where
  negative_ : Bool
  mantissa_ : UInt64
  exponent_ : Int
  deriving DecidableEq, Repr

def Number.zero : Number :=
  { negative_ := false, mantissa_ := 0, exponent_ := -2_147_483_648 }

def Number.unchecked (negative : Bool) (mantissa : UInt64) (exponent : Int) : Number :=
  { negative_ := negative, mantissa_ := mantissa, exponent_ := exponent }

def Number.isnormal (n : Number) : Prop :=
  n = Number.zero ∨
  (largeRange.min ≤ n.mantissa_ ∧ n.mantissa_ ≤ largeRange.max ∧
   (n.mantissa_ ≤ maxRep ∨ n.mantissa_.toNat % 10 = 0) ∧
   minExponent ≤ n.exponent_ ∧ n.exponent_ ≤ maxExponent)

abbrev Number.isNormalized (n : Number) : Prop := n.isnormal

-- `Number.isnormal` is a decidable arithmetic condition.
instance Number.instDecidableIsnormal (n : Number) : Decidable n.isnormal := by
  unfold Number.isnormal; infer_instance

-- `∀ d, e = .ok d → p d` over an `Except Error Number` is decidable: vacuous on
-- error, `p d` on the single `ok` value.
instance {e : Except Error Number} {p : Number → Prop} [∀ d, Decidable (p d)] :
    Decidable (∀ d, e = .ok d → p d) :=
  match e with
  | .error _ => isTrue (fun _ h => by simp at h)
  | .ok d0 =>
    decidable_of_iff (p d0)
      ⟨fun hp d hd => by injection hd with hd'; exact hd' ▸ hp, fun h => h d0 rfl⟩

-- `∃ d, e = .ok d` over an `Except Error Number` is decidable: true exactly when `e` is `.ok`.
instance {e : Except Error Number} : Decidable (∃ d, e = .ok d) :=
  match e with
  | .error _ => isFalse (by rintro ⟨d, h⟩; simp at h)
  | .ok d0 => isTrue ⟨d0, rfl⟩

-- For Number.zero we have `mantissa = 0`, whose exponent is `-2^31` that
-- would build `10 ^ 2^31` in the denominator at runtime, so we early exit
def Number.toRat (n : Number) : ℚ :=
  if n.mantissa_ = 0 then 0
  else
    let sign : Int := if n.negative_ then -1 else 1
    let m : Int := n.mantissa_.toNat
    if n.exponent_ ≥ 0 then
      mkRat (sign * m * (10 : Int) ^ n.exponent_.toNat) 1
    else
      mkRat (sign * m) ((10 : Nat) ^ (-n.exponent_).toNat)

def divu10 (u : UInt64) : UInt64 × UInt64 := (u / 10, u % 10)

structure Guard where
  digits_ : UInt64
  xbit_ : Bool
  sbit_ : Bool
  deriving Repr

def Guard.new : Guard := { digits_ := 0, xbit_ := false, sbit_ := false }

def Guard.set_negative (g : Guard) : Guard := { g with sbit_ := true }
def Guard.set_positive (g : Guard) : Guard := { g with sbit_ := false }
def Guard.set_sticky (g : Guard) : Guard := { g with xbit_ := true }

def Guard.push (g : Guard) (d : UInt64) : Guard :=
  let xbit' := g.xbit_ || ((g.digits_ &&& 0xF) != 0)
  let digits' := (g.digits_ >>> 4) ||| ((d &&& 0xF) <<< 60)
  { digits_ := digits', xbit_ := xbit', sbit_ := g.sbit_ }

def Guard.pop (g : Guard) : Guard × UInt64 :=
  let d := (g.digits_ >>> 60) &&& 0xF
  let digits' := (g.digits_ <<< 4) &&& 0xFFFF_FFFF_FFFF_FFFF
  ({ digits_ := digits', xbit_ := g.xbit_, sbit_ := g.sbit_ }, d)

def Guard.doDropDigit (g : Guard) (mantissa : UInt64) (exponent : Int) : Guard × UInt64 × Int :=
  (g.push (mantissa % 10), mantissa / 10, exponent + 1)

def Guard.doDropDigit128 (g : Guard) (mantissa : UInt128) (exponent : Int) : Guard × UInt128 × Int :=
  (g.push (toUInt64 (mantissa % 10)), mantissa / 10, exponent + 1)

-- no recoverable digits in the guard; xbit_ may still record that one was dropped
def Guard.unrecoverable (g : Guard) : Bool := g.digits_ == 0

def Guard.empty (g : Guard) : Bool := g.unrecoverable && !g.xbit_

-- `doDropDigitWithTarget` from xrpld: drop digits from `mantissa` into the guard
-- until `exponent` reaches `target`. Once `mantissa` is 0 and the guard has no recoverable
-- digits, the remaining drops change only the exponent, so it is set to `target` directly.
def Guard.doDropDigitWithTargetU64 (g : Guard) (mantissa : UInt64) (exponent target : Int)
    : UInt64 × Int × Guard :=
  if exponent < target then
    if mantissa == 0 && g.unrecoverable then (mantissa, target, g)
    else (g.doDropDigit mantissa exponent).1.doDropDigitWithTargetU64
           (g.doDropDigit mantissa exponent).2.1 (g.doDropDigit mantissa exponent).2.2 target
  else (mantissa, exponent, g)
termination_by (target - exponent).toNat
decreasing_by simp [Guard.doDropDigit]; omega

-- `rep` version of `doDropDigitWithTargetU64`, with the drop written out since `doDropDigit`
-- takes a `UInt64`. `to_rep` uses only the value and guard, so the exponent is not returned.
def Guard.doDropDigitWithTargetI64 (g : Guard) (drops : rep) (offset target : Int)
    : rep × Guard :=
  if offset < target then
    if drops == 0 && g.unrecoverable then (drops, g)
    else (g.push (drops % 10).toUInt64).doDropDigitWithTargetI64 (drops / 10) (offset + 1) target
  else (drops, g)
termination_by (target - offset).toNat
decreasing_by omega

def Guard.round (g : Guard) (mode : rounding_mode) : Int :=
  if g.empty then -2
  else match mode with
  | .towards_zero => -1
  | .downward =>
    if g.sbit_ then
      if g.digits_ > 0 || g.xbit_ then 1 else -1
    else -1
  | .upward =>
    if g.sbit_ then -1
    else if g.digits_ > 0 || g.xbit_ then 1 else -1
  | .to_nearest =>
    if g.digits_ > 0x5000_0000_0000_0000 then 1
    else if g.digits_ < 0x5000_0000_0000_0000 then -1
    else if g.xbit_ then 1
    else 0

structure RoundResult where
  negative_ : Bool
  mantissa_ : UInt64
  exponent_ : Int
  deriving Repr

def RoundResult.toNumber (r : RoundResult) : Number :=
  { negative_ := r.negative_, mantissa_ := r.mantissa_, exponent_ := r.exponent_ }

@[inline] def Guard.bringIntoRange (negative : Bool) (mantissa : UInt64) (exponent : Int)
    (minMantissa : UInt64) : RoundResult :=
  let (mantissa, exponent) :=
    if mantissa < minMantissa ∧ mantissa ≠ 0 then (mantissa * 10, exponent - 1)
    else (mantissa, exponent)
  if exponent < minExponent ∨ mantissa = 0 then
    { negative_ := false, mantissa_ := 0, exponent_ := -2147483648 }
  else
    { negative_ := negative, mantissa_ := mantissa, exponent_ := exponent }

def Guard.pushOverflow (g : Guard) (mantissa : UInt64) (mode : rounding_mode) : Guard :=
    if maxRep ≤ mantissa ∧ mantissa < maxRepUp then
        let spread := maxRepUp - maxRep
        let mantissa :=
            if mantissa % 10 < 9 then
                let midpoint := maxRep + spread / 2
                let r := g.round mode
                if r == 1 || (r == 0 && mantissa == midpoint) then mantissa + 1 else mantissa
            else mantissa
        if mantissa == maxRep then g
        else
            let diff := mantissa - maxRep
            let digit := (diff * 10) / spread
            g.push digit
    else
        g

def Guard.doRoundUp (g : Guard) (negative : Bool) (mantissa : UInt64) (exponent : Int)
    (minMantissa maxMantissa : internalrep) (mode : rounding_mode)
    (location : Error) : Except Error RoundResult :=
  let g := g.pushOverflow mantissa mode
  let r := g.round mode
  let roundUp := r == 1 || (r == 0 && mantissa % 2 == 1)
  let res :=
    if roundUp then
      if mantissa < maxMantissa ∧ mantissa < maxRep then
        Guard.bringIntoRange negative (mantissa + 1) exponent minMantissa
      else if maxRep < mantissa ∧ mantissa < maxRepUp then
        Guard.bringIntoRange negative maxRepUp exponent minMantissa
      else
        let (g', mantissa, exponent) := g.doDropDigit mantissa exponent
        let r' := g'.round mode
        let roundUp' := r' == 1 || (r' == 0 && mantissa % 2 == 1)
        let mantissa := if roundUp' then mantissa + 1 else mantissa
        Guard.bringIntoRange negative mantissa exponent minMantissa
    else if maxRep < mantissa ∧ mantissa < maxRepUp then
      Guard.bringIntoRange negative maxRep exponent minMantissa
    else
      Guard.bringIntoRange negative mantissa exponent minMantissa
  if res.exponent_ > maxExponent then .error location
  else .ok res

def doNormalize_scaleUp (minMantissa : UInt64) (m : UInt64) (e : Int) : UInt64 × Int :=
  if m < minMantissa ∧ minExponent < e then
    doNormalize_scaleUp minMantissa (m * 10) (e - 1)
  else (m, e)
termination_by (e - minExponent).toNat
decreasing_by omega

def doNormalize_scaleDown (maxMantissa : UInt64) (m : UInt64) (e : Int) (g : Guard)
    : Except Error (UInt64 × Int × Guard) :=
  if h : m > maxMantissa then
    if e ≥ maxExponent then .error .normalize1
    else doNormalize_scaleDown maxMantissa (m / 10) (e + 1) (g.push (m % 10))
  else .ok (m, e, g)
termination_by m.toNat
decreasing_by
  rw [UInt64.toNat_div, u64_ten_val]
  exact Nat.div_lt_self (u64_pos_of_gt h) (by omega)

def doNormalize_capAtMaxRep (m : UInt64) (e : Int) (g : Guard)
    : Except Error (UInt64 × Int × Guard) :=
  if m > maxRepUp then
    if e ≥ maxExponent then .error .normalize1_5
    else
      let (q, r) := divu10 m
      .ok (q, e + 1, g.push r)
  else .ok (m, e, g)

def doNormalize (negative : Bool) (mantissa : UInt64) (exponent : Int)
    (minMantissa maxMantissa : UInt64) (mode : rounding_mode) : Except Error Number :=
  if mantissa == 0 then .ok Number.zero
  else
    let (m, e) := doNormalize_scaleUp minMantissa mantissa exponent
    let g0 := if negative then Guard.new.set_negative else Guard.new
    match doNormalize_scaleDown maxMantissa m e g0 with
    | .error err => .error err
    | .ok (m, e, g) =>
      if e < minExponent || m < minMantissa then .ok Number.zero
      else
        match doNormalize_capAtMaxRep m e g with
        | .error err => .error err
        | .ok (m, e, g) =>
          match g.doRoundUp negative m e minMantissa maxMantissa mode .normalize2 with
          | .error err => .error err
          | .ok res => .ok res.toNumber

def Number.normalize (n : Number) (minMant maxMant : UInt64)
    (mode : rounding_mode) : Except Error Number :=
  doNormalize n.negative_ n.mantissa_ n.exponent_ minMant maxMant mode

def Number.normalizeToRange (n : Number) (minMant maxMant : UInt64)
    (mode : rounding_mode) : Except Error (Int64 × Int) :=
  match doNormalize n.negative_ n.mantissa_ n.exponent_ minMant maxMant mode with
  | .error e => .error e
  | .ok res =>
    -- safe only when `maxMant ≤ Int64.maxValue`.
    let mant : Int64 := res.mantissa_.toInt64
    let signedM : Int64 := if res.negative_ then -mant else mant
    .ok (signedM, res.exponent_)

def Number.normalized (negative : Bool) (mantissa : UInt64) (exponent : Int)
    (minMant maxMant : UInt64) (mode : rounding_mode) : Except Error Number :=
  (Number.unchecked negative mantissa exponent).normalize minMant maxMant mode

-- C++ `Number(rep mantissa, int exponent)` — the signed-int64 entry-point ctor.
-- `rep = std::int64_t`; sign + magnitude split happens inside via `externalToInternal`.
def Number.from_rep (mantissa : Int64) (exponent : Int)
    (minMant maxMant : UInt64) (mode : rounding_mode) : Except Error Number :=
  Number.normalized (mantissa < 0) mantissa.toInt.natAbs.toUInt64 exponent minMant maxMant mode

-- Number(int64_t) ctor
def Number.ofInt64 (m : Int64) : Number :=
  (Number.from_rep m 0 largeRange.min largeRange.max .to_nearest).toOption.getD Number.zero

-- Divide the mantissa by 10 (dropping the low digit) until the exponent reaches 0,
-- i.e. discard the fractional part toward zero.
def Number.truncateAux (m : UInt64) (e : Int) : UInt64 × Int :=
  if e < 0 ∧ m ≠ 0 then
    Number.truncateAux (m / 10) (e + 1)
  else
    (m, e)
termination_by (-e).toNat
decreasing_by omega

-- Round toward zero to an integer. Sign is preserved; the exponent is ≥ 0 afterwards
-- so re-normalization neither rounds nor throws (mode is inert).
def Number.truncate (n : Number) : Except Error Number :=
  if n.exponent_ ≥ 0 ∨ n.mantissa_ = 0 then
    .ok n
  else
    let (m, e) := Number.truncateAux n.mantissa_ n.exponent_
    Number.normalized n.negative_ m e largeRange.min largeRange.max .to_nearest

def Number.operator_eq (x y : Number) : Bool :=
  x.negative_ == y.negative_ &&
    x.mantissa_ == y.mantissa_ &&
    x.exponent_ == y.exponent_

def Number.operator_ne (x y : Number) : Bool :=
  !(x.operator_eq y)

def Number.operator_lt (l r : Number) : Bool :=
  let lneg := l.negative_
  let rneg := r.negative_
  if lneg != rneg then lneg
  else if l.mantissa_ == 0 then r.mantissa_ > 0
  else if r.mantissa_ == 0 then false
  else if l.exponent_ > r.exponent_ then lneg
  else if l.exponent_ < r.exponent_ then !lneg
  else if lneg then l.mantissa_ > r.mantissa_
  else l.mantissa_ < r.mantissa_

def Number.operator_le (x y : Number) : Bool :=
  !(y.operator_lt x)

def Number.operator_gt (x y : Number) : Bool :=
  y.operator_lt x

def Number.operator_ge (x y : Number) : Bool :=
  !(x.operator_lt y)

def Number.min (x y : Number) : Number := if y.operator_lt x then y else x
def Number.max (x y : Number) : Number := if x.operator_lt y then y else x

def Number.clamp (value low high : Number) : Number :=
  if value.operator_lt low then low else if high.operator_lt value then high else value

def Number.signum (n : Number) : Int :=
  if n.negative_ then -1
  else if n.mantissa_ != 0 then 1
  else 0

def Number.operator_neg (n : Number) : Number :=
  if n.mantissa_ == 0 then Number.zero
  else { n with negative_ := !n.negative_ }

def scaleDown128 (m : UInt128) (e : Int) (g : Guard) : UInt64 × Int × Guard :=
  if h : m > toUInt128 maxRepUp then
    let d := toUInt64 (m % 10)
    scaleDown128 (m / 10) (e + 1) (g.push d)
  else (toUInt64 m, e, g)
termination_by m.toNat
decreasing_by
  rw [BitVec.toNat_udiv, bv128_ten_val]
  exact Nat.div_lt_self (bv128_pos_of_gt h) (by omega)

def doNormalize_scaleDown128 (maxMantissa : UInt64) (m : UInt128) (e : Int) (g : Guard)
    : Except Error (UInt128 × Int × Guard) :=
  if h : m > toUInt128 maxMantissa then
    if e ≥ maxExponent then .error .normalize1
    else doNormalize_scaleDown128 maxMantissa (m / 10) (e + 1) (g.push (toUInt64 (m % 10)))
  else .ok (m, e, g)
termination_by m.toNat
decreasing_by
  rw [BitVec.toNat_udiv, bv128_ten_val]
  exact Nat.div_lt_self (bv128_pos_of_gt h) (by omega)

def doNormalize128 (negative : Bool) (mantissa : UInt128) (exponent : Int)
    (minMantissa maxMantissa : UInt64) (mode : rounding_mode)
    (stickyTail : Bool := false) : Except Error Number :=
  if mantissa == 0 then .ok Number.zero
  else
    let (m, e) :=
      let rec scaleUp (m : UInt128) (e : Int) : UInt128 × Int :=
        if m < toUInt128 minMantissa ∧ minExponent < e then
          scaleUp (m * 10) (e - 1)
        else (m, e)
      termination_by (e - minExponent).toNat
      decreasing_by omega
      scaleUp mantissa exponent
    let g0 := if negative then Guard.new.set_negative else Guard.new
    let g0 := if stickyTail then g0.set_sticky else g0
    match doNormalize_scaleDown128 maxMantissa m e g0 with
    | .error err => .error err
    | .ok (m, e, g) =>
      if e < minExponent || m < toUInt128 minMantissa then .ok Number.zero
      else
        match doNormalize_capAtMaxRep (toUInt64 m) e g with
        | .error err => .error err
        | .ok (m, e, g) =>
          match g.doRoundUp negative m e minMantissa maxMantissa mode .normalize2 with
          | .error err => .error err
          | .ok res => .ok res.toNumber

def Number.operator_mul (x y : Number)
    (mode : rounding_mode) : Except Error Number := do
  if x.operator_eq Number.zero then return x
  else if y.operator_eq Number.zero then return y
  else
    let zn := x.negative_ != y.negative_ -- zn: result sign
    let zm128 := toUInt128 x.mantissa_ * toUInt128 y.mantissa_ -- result mantissa in unsigned 128 bits
    let ze := x.exponent_ + y.exponent_
    let g := if zn then Guard.new.set_negative else Guard.new
    let (zm, ze, g) := scaleDown128 zm128 ze g
    match g.doRoundUp zn zm ze largeRange.min largeRange.max mode .overflow with
    | .error err => .error err
    | .ok res => res.toNumber.normalize largeRange.min largeRange.max mode

def divQuotient128 (xm ym : UInt64) (xe ye : Int) : UInt128 × Int × Bool :=
  let xm128 := toUInt128 xm
  let ym128 := toUInt128 ym
  let f : UInt128 := 100000000000000000         -- 10^17
  let fexp : Int := 17
  let numerator := xm128 * f
  let zm128 := numerator / ym128
  let ze : Int := xe - ye - fexp
  let remainder := numerator % ym128
  if remainder != 0 then
    let correctionFactor : UInt128 := 100000    -- 10^5
    let partialNumerator := remainder * correctionFactor
    let correction := partialNumerator / ym128
    let (zm128, ze) :=
      if correction != 0 then (zm128 * correctionFactor + correction, ze - 5)
      else (zm128, ze)
    let dropped := partialNumerator % ym128 != 0
    (zm128, ze, dropped)
  else (zm128, ze, false)

def Number.operator_div (x y : Number)
    (mode : rounding_mode) : Except Error Number := do
  if y.operator_eq Number.zero then .error .divByZero
  else if x.operator_eq Number.zero then return x
  else
    let zn := x.negative_ != y.negative_
    let (zm128, ze, dropped) := divQuotient128 x.mantissa_ y.mantissa_ x.exponent_ y.exponent_
    doNormalize128 zn zm128 ze largeRange.min largeRange.max mode dropped

-- Number::power, exponentiation by squaring (to_nearest multiply)
def Number.power (base : Number) (exponent : Nat) : Except Error Number :=
  match exponent with
  | 0 => .ok (Number.ofInt64 1)
  | 1 => .ok base
  | k + 2 => do
    let half ← Number.power base ((k + 2) / 2)
    let squared ← half.operator_mul half .to_nearest
    if (k + 2) % 2 == 1 then squared.operator_mul base .to_nearest else .ok squared
  termination_by exponent
  decreasing_by omega

def Number.operator_add (x y : Number)
    (mode : rounding_mode) : Except Error Number := do
  if y.operator_eq Number.zero then return x
  else if x.operator_eq Number.zero then return y
  else if x.operator_eq (y.operator_neg) then return Number.zero
  else
    let xn := x.negative_
    let xm := x.mantissa_
    let xe := x.exponent_
    let yn := y.negative_
    let ym := y.mantissa_
    let ye := y.exponent_
    let rec alignDown (m : UInt64) (e : Int) (g : Guard)
        (target : Int) : UInt64 × Int × Guard :=
      g.doDropDigitWithTargetU64 m e target
    let (xm, xe, ym, _ye, g) :=
      if xe < ye then
        let g := if xn then Guard.new.set_negative else Guard.new
        let (xm', xe', g') := alignDown xm xe g ye
        (xm', xe', ym, ye, g')
      else if xe > ye then
        let g := if yn then Guard.new.set_negative else Guard.new
        let (ym', _ye', g') := alignDown ym ye g xe
        (xm, xe, ym', xe, g')
      else
        let g := if xn then Guard.new.set_negative else Guard.new
        (xm, xe, ym, ye, g)
    if xn == yn then
      let zm128 : UInt128 := toUInt128 xm + toUInt128 ym
      let (zm, xe, g) :=
        if zm128 > toUInt128 largeRange.max || zm128 > toUInt128 maxRepUp then
          let (g', zm128', xe') := g.doDropDigit128 zm128 xe
          (toUInt64 zm128', xe', g')
        else (toUInt64 zm128, xe, g)
      match g.doRoundUp xn zm xe largeRange.min largeRange.max mode .overflow with
      | .error err => .error err
      | .ok res => res.toNumber.normalize largeRange.min largeRange.max mode
    else
      let (zm128, zn, ze) :=
        if xm > ym then (toUInt128 xm - toUInt128 ym, xn, xe)
        else (toUInt128 ym - toUInt128 xm, yn, xe)
      let upperLimit : UInt128 := toUInt128 largeRange.min * 1000
      let rec recover (m : UInt128) (e : Int) (g : Guard)
          (fuel : Nat) : UInt128 × Int × Guard :=
        match fuel with
        | 0 => (m, e, g)
        | fuel + 1 =>
          if m < upperLimit ∧ ¬ g.empty then
            let (g', d) := g.pop
            recover (m * 10 - toUInt128 d) (e - 1) g' fuel
          else (m, e, g)
      let (zm128, ze, g) := recover zm128 ze g 40
      -- doRoundDown (Enabled330): borrow 1 unless the guard is exactly empty.
      -- DELIBERATE DEVIATION from the vendored C++ (PR 7389 head)
      let stickyTail := !g.empty
      let zm128 := if g.empty then zm128 else zm128 - 1
      doNormalize128 zn zm128 ze largeRange.min largeRange.max mode stickyTail

def Number.operator_sub (x y : Number)
    (mode : rounding_mode) : Except Error Number :=
  Number.operator_add x y.operator_neg mode

def Number.mantissa (n : Number) : rep :=
  let m : UInt64 := if n.mantissa_ > maxRep then n.mantissa_ / 10 else n.mantissa_
  let s : rep := m.toInt64
  if n.negative_ then -s else s

def Number.exponent (n : Number) : Int :=
  if n.mantissa_ > maxRep then n.exponent_ + 1 else n.exponent_

def Number.to_rep (n : Number) (mode : rounding_mode) : Except Error rep :=
  let drops : rep := n.mantissa
  let offset : Int := n.exponent
  if drops == 0 then .ok 0
  else
    let g := if n.negative_ then Guard.new.set_negative else Guard.new
    let drops : rep := if n.negative_ then -drops else drops

    let rec shift (drops : rep) (offset : Int) (g : Guard) : rep × Guard :=
      g.doDropDigitWithTargetI64 drops offset 0

    let rec grow (drops : rep) (offset : Int) : Except Error rep :=
      if offset > 0 then
        if drops > maxRep.toInt64 / 10 then
          .error .overflow
        else grow (drops * 10) (offset - 1)
      else .ok drops
    termination_by offset.toNat
    decreasing_by omega

    let (drops, g) :=
      if offset < 0 then shift drops offset g
      else (drops, g)

    match (if offset ≥ 0 then grow drops offset else .ok drops) with
    | .error e => .error e
    | .ok drops =>
      let g := g.pushOverflow drops.toUInt64 mode
      let r := g.round mode
      if r == 1 || (r == 0 && drops % 2 == 1) then
        if drops ≥ maxRep.toInt64 then
          .error .overflow
        else
          let drops := drops + 1
          .ok (if n.negative_ then -drops else drops)
      else
        let drops := if maxRep.toInt64 < drops ∧ drops < maxRepUp.toInt64 then maxRep.toInt64 else drops
        .ok (if n.negative_ then -drops else drops)

end XRPL.Model.Protocol

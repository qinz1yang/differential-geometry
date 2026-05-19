import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Real Time Intervals for RicciFlower

Ricci-flow solutions live over concrete real time domains.  The carrier records
where the metric exists, while `regular` records the interior times where
two-sided evolution identities are stated.
-/

namespace RicciFlower
namespace Realized

/-! ## Endpoint-general intervals -/

/-- Endpoint for a real time interval, allowing infinite endpoints. -/
inductive TimeEndpoint where
  | negInf
  | finite (t : Real)
  | posInf

namespace TimeEndpoint

/-- Strict lower-bound relation `a < t`, with `-infinity < t` always true
and `+infinity < t` always false. -/
def lowerLt (a : TimeEndpoint) (t : Real) : Prop :=
  match a with
  | negInf => True
  | finite s => s < t
  | posInf => False

/-- Closed lower-bound relation `a <= t`, with `-infinity <= t` always true
and `+infinity <= t` always false. -/
def lowerLe (a : TimeEndpoint) (t : Real) : Prop :=
  match a with
  | negInf => True
  | finite s => s <= t
  | posInf => False

/-- Strict upper-bound relation `t < b`, with `t < +infinity` always true
and `t < -infinity` always false. -/
def upperLt (t : Real) (b : TimeEndpoint) : Prop :=
  match b with
  | negInf => False
  | finite s => t < s
  | posInf => True

/-- Closed upper-bound relation `t <= b`, with `t <= +infinity` always true
and `t <= -infinity` always false. -/
def upperLe (t : Real) (b : TimeEndpoint) : Prop :=
  match b with
  | negInf => False
  | finite s => t <= s
  | posInf => True

/-- Lower endpoint membership, controlled by whether the finite lower endpoint
is closed.  Infinite lower endpoints ignore the closure flag. -/
def lowerMem (closed : Bool) (a : TimeEndpoint) (t : Real) : Prop :=
  match closed, a with
  | _, negInf => True
  | true, finite s => s <= t
  | false, finite s => s < t
  | _, posInf => False

/-- Upper endpoint membership, controlled by whether the finite upper endpoint
is closed.  Infinite upper endpoints ignore the closure flag. -/
def upperMem (closed : Bool) (t : Real) (b : TimeEndpoint) : Prop :=
  match closed, b with
  | _, negInf => False
  | true, finite s => t <= s
  | false, finite s => t < s
  | _, posInf => True

theorem lowerLt_to_mem (closed : Bool) {a : TimeEndpoint} {t : Real}
    (h : lowerLt a t) :
  lowerMem closed a t := by
  cases closed
  · cases a with
    | negInf => simp [lowerMem]
    | finite s => exact h
    | posInf => simp [lowerLt] at h
  · cases a with
    | negInf => simp [lowerMem]
    | finite s =>
        exact le_of_lt h
    | posInf => simp [lowerLt] at h

theorem upperLt_to_mem (closed : Bool) {b : TimeEndpoint} {t : Real}
    (h : upperLt t b) :
  upperMem closed t b := by
  cases closed
  · cases b with
    | negInf => simp [upperLt] at h
    | finite s => exact h
    | posInf => simp [upperMem]
  · cases b with
    | negInf => simp [upperLt] at h
    | finite s =>
        exact le_of_lt h
    | posInf => simp [upperMem]

end TimeEndpoint

/-- A real time interval with a distinguished initial time and a regular
subdomain for evolution equations. -/
structure RealTimeInterval where
  carrier : Set Real
  regular : Set Real
  initial : Real
  initial_mem : initial ∈ carrier
  regular_subset : regular ⊆ carrier

namespace RealTimeInterval

/-- Times on which the flow is defined. -/
abbrev FlowTime (D : RealTimeInterval) : Type := {t : Real // t ∈ D.carrier}

/-- Times at which local evolution equations are stated. -/
abbrev RegularTime (D : RealTimeInterval) : Type := {t : Real // t ∈ D.regular}

/-- The initial time as a flow time. -/
def initialTime (D : RealTimeInterval) : D.FlowTime :=
  ⟨D.initial, D.initial_mem⟩

/-- A regular time is canonically a flow time. -/
def regularToFlow {D : RealTimeInterval} (t : D.RegularTime) : D.FlowTime :=
  ⟨t.1, D.regular_subset t.2⟩

@[simp] theorem initialTime_val (D : RealTimeInterval) :
    (D.initialTime : Real) = D.initial := by
  rfl

@[simp] theorem regularToFlow_val {D : RealTimeInterval} (t : D.RegularTime) :
    (D.regularToFlow t : Real) = (t : Real) := by
  rfl

/-- Time translation of an interval.

The shifted time `s` corresponds to the original time `s + τ`.  Thus shifting by
`τ = D.initial` normalizes the distinguished initial time to `0`. -/
def timeShift (D : RealTimeInterval) (τ : Real) : RealTimeInterval where
  carrier := {s : Real | s + τ ∈ D.carrier}
  regular := {s : Real | s + τ ∈ D.regular}
  initial := D.initial - τ
  initial_mem := by
    simpa [sub_add_cancel] using D.initial_mem
  regular_subset := by
    intro s hs
    exact D.regular_subset hs

@[simp] theorem timeShift_carrier (D : RealTimeInterval) (τ : Real) :
    (D.timeShift τ).carrier = {s : Real | s + τ ∈ D.carrier} := by
  rfl

@[simp] theorem timeShift_regular (D : RealTimeInterval) (τ : Real) :
    (D.timeShift τ).regular = {s : Real | s + τ ∈ D.regular} := by
  rfl

@[simp] theorem timeShift_initial (D : RealTimeInterval) (τ : Real) :
    (D.timeShift τ).initial = D.initial - τ := by
  rfl

@[simp] theorem timeShift_initial_self (D : RealTimeInterval) :
    (D.timeShift D.initial).initial = 0 := by
  simp [timeShift]

@[simp] theorem timeShift_initialTime_val (D : RealTimeInterval) (τ : Real) :
    ((D.timeShift τ).initialTime : Real) = D.initial - τ := by
  rfl

@[simp] theorem timeShift_initialTime_self_val (D : RealTimeInterval) :
    ((D.timeShift D.initial).initialTime : Real) = 0 := by
  simp [timeShift]

/-- Endpoint-general interval constructor.

The two Boolean flags control whether finite endpoints are included in the
carrier.  The regular set is always the open interior between the endpoints.
For infinite endpoints the corresponding closure flag has no effect. -/
def ofEndpoints
    (a b : TimeEndpoint) (lowerClosed upperClosed : Bool)
    (initial : Real)
    (hinit :
      TimeEndpoint.lowerMem lowerClosed a initial ∧
        TimeEndpoint.upperMem upperClosed initial b) : RealTimeInterval where
  carrier := {t : Real |
    TimeEndpoint.lowerMem lowerClosed a t ∧
      TimeEndpoint.upperMem upperClosed t b}
  regular := {t : Real | TimeEndpoint.lowerLt a t ∧ TimeEndpoint.upperLt t b}
  initial := initial
  initial_mem := hinit
  regular_subset := by
    intro t ht
    exact
      ⟨TimeEndpoint.lowerLt_to_mem lowerClosed ht.1,
        TimeEndpoint.upperLt_to_mem upperClosed ht.2⟩

/-- Closed interval `[a,b]`, with regular times `(a,b)`. -/
def closed (a b : Real) (hab : a ≤ b) : RealTimeInterval where
  carrier := Set.Icc a b
  regular := Set.Ioo a b
  initial := a
  initial_mem := ⟨le_rfl, hab⟩
  regular_subset := by
    intro t ht
    exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩

/-- Half-open interval `[a,b)`, with regular times `(a,b)`. -/
def closedOpen (a b : Real) (hab : a < b) : RealTimeInterval where
  carrier := Set.Ico a b
  regular := Set.Ioo a b
  initial := a
  initial_mem := ⟨le_rfl, hab⟩
  regular_subset := by
    intro t ht
    exact ⟨le_of_lt ht.1, ht.2⟩

/-- Carrier of a half-open interval after shifting its initial endpoint to
zero. -/
theorem timeShift_closedOpen_carrier
    {a b : Real} (hab : a < b) :
    ((closedOpen a b hab).timeShift a).carrier = Set.Ico 0 (b - a) := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩
  · intro hs
    rcases hs with ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩

/-- Regular times of a half-open interval after shifting its initial endpoint
to zero. -/
theorem timeShift_closedOpen_regular
    {a b : Real} (hab : a < b) :
    ((closedOpen a b hab).timeShift a).regular = Set.Ioo 0 (b - a) := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩
  · intro hs
    rcases hs with ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩

/-- Open interval `(a,b)`, with a chosen initial time inside it. -/
def openInterval (a b t₀ : Real) (ht₀ : t₀ ∈ Set.Ioo a b) : RealTimeInterval where
  carrier := Set.Ioo a b
  regular := Set.Ioo a b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ht

/-- Open-closed interval `(a,b]`, with a chosen initial time inside it. -/
def openClosed (a b t₀ : Real) (ht₀ : t₀ ∈ Set.Ioc a b) : RealTimeInterval where
  carrier := Set.Ioc a b
  regular := Set.Ioo a b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ⟨ht.1, le_of_lt ht.2⟩

/-- Infinite interval `[a,∞)`, with regular times `(a,∞)`. -/
def closedInfinite (a : Real) : RealTimeInterval where
  carrier := Set.Ici a
  regular := Set.Ioi a
  initial := a
  initial_mem := by
    exact Set.mem_Ici.mpr le_rfl
  regular_subset := by
    intro t ht
    exact Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp ht))

/-- Infinite interval `(a,∞)`, with a chosen initial time inside it. -/
def openInfinite (a t₀ : Real) (ht₀ : a < t₀) : RealTimeInterval where
  carrier := Set.Ioi a
  regular := Set.Ioi a
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ht

/-- Infinite interval `(-∞,b]`, with a chosen initial time inside it. -/
def infiniteClosed (b t₀ : Real) (ht₀ : t₀ ≤ b) : RealTimeInterval where
  carrier := Set.Iic b
  regular := Set.Iio b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact Set.mem_Iic.mpr (le_of_lt (Set.mem_Iio.mp ht))

/-- Infinite interval `(-∞,b)`, with a chosen initial time inside it. -/
def infiniteOpen (b t₀ : Real) (ht₀ : t₀ < b) : RealTimeInterval where
  carrier := Set.Iio b
  regular := Set.Iio b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ht

/-- Whole real line, with a chosen reference initial time. -/
def univ (t₀ : Real) : RealTimeInterval where
  carrier := Set.univ
  regular := Set.univ
  initial := t₀
  initial_mem := trivial
  regular_subset := by
    intro t ht
    exact ht

end RealTimeInterval

end Realized
end RicciFlower

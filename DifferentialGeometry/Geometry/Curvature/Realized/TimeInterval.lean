import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open scoped Topology

/-!
# Real Time Intervals

Ricci-flow solutions live over concrete real time domains.  The carrier records
where the metric exists, while `regular` records the interior times where
two-sided evolution identities are stated.
-/

namespace DifferentialGeometry.Integral.Connection

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
  regular_isOpen : IsOpen regular
  regular_mem_nhds : ∀ {t : Real}, t ∈ regular -> carrier ∈ 𝓝 t

namespace RealTimeInterval

private theorem endpointCarrier_mem_nhds
    (a b : TimeEndpoint) (lowerClosed upperClosed : Bool) {t : Real}
    (ht : TimeEndpoint.lowerLt a t ∧ TimeEndpoint.upperLt t b) :
    {s : Real |
      TimeEndpoint.lowerMem lowerClosed a s ∧
        TimeEndpoint.upperMem upperClosed s b} ∈ 𝓝 t := by
  have hstrict :
      {s : Real | TimeEndpoint.lowerLt a s ∧ TimeEndpoint.upperLt s b} ∈ 𝓝 t := by
    cases a with
    | negInf =>
        cases b with
        | negInf =>
            simp [TimeEndpoint.upperLt] at ht
        | finite b =>
            simpa [TimeEndpoint.lowerLt, TimeEndpoint.upperLt] using Iio_mem_nhds ht.2
        | posInf =>
            simp [TimeEndpoint.lowerLt, TimeEndpoint.upperLt]
    | finite a =>
        cases b with
        | negInf =>
            simp [TimeEndpoint.upperLt] at ht
        | finite b =>
            simpa [TimeEndpoint.lowerLt, TimeEndpoint.upperLt] using Ioo_mem_nhds ht.1 ht.2
        | posInf =>
            simpa [TimeEndpoint.lowerLt, TimeEndpoint.upperLt] using Ioi_mem_nhds ht.1
    | posInf =>
        simp [TimeEndpoint.lowerLt] at ht
  exact
    Filter.mem_of_superset hstrict (by
      intro s hs
      exact
        ⟨TimeEndpoint.lowerLt_to_mem lowerClosed hs.1,
          TimeEndpoint.upperLt_to_mem upperClosed hs.2⟩)

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

/-- Every regular time lies in the interior of a compact time window that is
still contained in the regular set. -/
theorem exists_Icc_regular (D : RealTimeInterval) {t : Real}
    (ht : t ∈ D.regular) :
    ∃ a b : Real, t ∈ Set.Ioo a b ∧ Set.Icc a b ⊆ D.regular := by
  obtain ⟨a, b, _htIcc, hIcc, hsub⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (D.regular_isOpen.mem_nhds ht)
  exact ⟨a, b, Icc_mem_nhds_iff.mp hIcc, hsub⟩

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
  regular_isOpen := by
    exact D.regular_isOpen.preimage (continuous_id.add continuous_const)
  regular_mem_nhds := by
    intro s hs
    simpa [Set.preimage] using
      (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds
        (D.regular_mem_nhds hs)

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
  regular_isOpen := by
    have h1 : IsOpen {t : Real | TimeEndpoint.lowerLt a t} := by
      cases a with
      | negInf => simp [TimeEndpoint.lowerLt]
      | finite s => simpa [TimeEndpoint.lowerLt] using isOpen_Ioi
      | posInf => simp [TimeEndpoint.lowerLt]
    have h2 : IsOpen {t : Real | TimeEndpoint.upperLt t b} := by
      cases b with
      | negInf => simp [TimeEndpoint.upperLt]
      | finite s => simpa [TimeEndpoint.upperLt] using isOpen_Iio
      | posInf => simp [TimeEndpoint.upperLt]
    exact h1.inter h2
  regular_mem_nhds := by
    intro t ht
    exact endpointCarrier_mem_nhds a b lowerClosed upperClosed ht

/-- Closed interval `[a,b]`, with regular times `(a,b)`. -/
def closed (a b : Real) (hab : a ≤ b) : RealTimeInterval where
  carrier := Set.Icc a b
  regular := Set.Ioo a b
  initial := a
  initial_mem := ⟨le_rfl, hab⟩
  regular_subset := by
    intro t ht
    exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  regular_isOpen := isOpen_Ioo
  regular_mem_nhds := by
    intro t ht
    exact Icc_mem_nhds ht.1 ht.2

/-- Half-open interval `[a,b)`, with regular times `(a,b)`. -/
def closedOpen (a b : Real) (hab : a < b) : RealTimeInterval where
  carrier := Set.Ico a b
  regular := Set.Ioo a b
  initial := a
  initial_mem := ⟨le_rfl, hab⟩
  regular_subset := by
    intro t ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  regular_isOpen := isOpen_Ioo
  regular_mem_nhds := by
    intro t ht
    exact Ico_mem_nhds ht.1 ht.2

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
  regular_isOpen := isOpen_Ioo
  regular_mem_nhds := by
    intro t ht
    exact Ioo_mem_nhds ht.1 ht.2

/-- Left endpoint of the `n`th compact window exhausting `(a,b)` while
retaining the distinguished time `t₀`. -/
noncomputable def openWindowLeft (a t₀ : Real) (n : Nat) : Real :=
  a + (t₀ - a) / ((n : Real) + 2)

/-- Right endpoint of the `n`th compact window exhausting `(a,b)` while
retaining the distinguished time `t₀`. -/
noncomputable def openWindowRight (b t₀ : Real) (n : Nat) : Real :=
  b - (b - t₀) / ((n : Real) + 2)

/-- The canonical nested compact windows exhausting an open time interval. -/
def openWindow (a b t₀ : Real) (n : Nat) : Set Real :=
  Set.Icc (openWindowLeft a t₀ n) (openWindowRight b t₀ n)

/-- Every canonical compact window lies strictly inside the ambient open
interval. -/
theorem openWindow_subset {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b) (n : Nat) :
    openWindow a b t₀ n ⊆ Set.Ioo a b := by
  intro t ht
  have hden : (0 : Real) < (n : Real) + 2 := by positivity
  have hleft : a < openWindowLeft a t₀ n := by
    have hfrac : 0 < (t₀ - a) / ((n : Real) + 2) :=
      div_pos (sub_pos.mpr ht₀.1) hden
    simp only [openWindowLeft]
    linarith
  have hright : openWindowRight b t₀ n < b := by
    have hfrac : 0 < (b - t₀) / ((n : Real) + 2) :=
      div_pos (sub_pos.mpr ht₀.2) hden
    simp only [openWindowRight]
    linarith
  exact ⟨hleft.trans_le ht.1, ht.2.trans_lt hright⟩

/-- The distinguished time belongs to every canonical compact window. -/
theorem initial_mem_window {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b) (n : Nat) :
    t₀ ∈ openWindow a b t₀ n := by
  have hden : (0 : Real) < (n : Real) + 2 := by positivity
  have hden_ge : (1 : Real) ≤ (n : Real) + 2 := by
    have hn : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
    linarith
  have hleft : openWindowLeft a t₀ n ≤ t₀ := by
    have hfrac : (t₀ - a) / ((n : Real) + 2) ≤ t₀ - a := by
      rw [div_le_iff₀ hden]
      calc
        t₀ - a = (t₀ - a) * 1 := (mul_one _).symm
        _ ≤ (t₀ - a) * ((n : Real) + 2) :=
          mul_le_mul_of_nonneg_left hden_ge (sub_nonneg.mpr ht₀.1.le)
    simp only [openWindowLeft]
    linarith
  have hright : t₀ ≤ openWindowRight b t₀ n := by
    have hfrac : (b - t₀) / ((n : Real) + 2) ≤ b - t₀ := by
      rw [div_le_iff₀ hden]
      calc
        b - t₀ = (b - t₀) * 1 := (mul_one _).symm
        _ ≤ (b - t₀) * ((n : Real) + 2) :=
          mul_le_mul_of_nonneg_left hden_ge (sub_nonneg.mpr ht₀.2.le)
    simp only [openWindowRight]
    linarith
  exact ⟨hleft, hright⟩

/-- The canonical compact windows are increasing with their index. -/
theorem openWindow_mono {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    {n m : Nat} (hnm : n ≤ m) :
    openWindow a b t₀ n ⊆ openWindow a b t₀ m := by
  intro t ht
  have hnpos : (0 : Real) < (n : Real) + 2 := by positivity
  have hden : (n : Real) + 2 ≤ (m : Real) + 2 := by
    have hcast : (n : Real) ≤ (m : Real) := Nat.cast_le.mpr hnm
    linarith
  have hleft : openWindowLeft a t₀ m ≤ openWindowLeft a t₀ n := by
    have hfrac : (t₀ - a) / ((m : Real) + 2) ≤
        (t₀ - a) / ((n : Real) + 2) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr ht₀.1.le) hnpos hden
    simp only [openWindowLeft]
    linarith
  have hright : openWindowRight b t₀ n ≤ openWindowRight b t₀ m := by
    have hfrac : (b - t₀) / ((m : Real) + 2) ≤
        (b - t₀) / ((n : Real) + 2) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr ht₀.2.le) hnpos hden
    simp only [openWindowRight]
    linarith
  exact ⟨hleft.trans ht.1, ht.2.trans hright⟩

/-- Every point of `(a,b)` lies in one canonical compact window. -/
theorem mem_openWindow {a b t₀ t : Real} (ht : t ∈ Set.Ioo a b) :
    ∃ n : Nat, t ∈ openWindow a b t₀ n := by
  have hta : 0 < t - a := sub_pos.mpr ht.1
  have htb : 0 < b - t := sub_pos.mpr ht.2
  obtain ⟨n, hn⟩ :=
    exists_nat_gt (max ((t₀ - a) / (t - a)) ((b - t₀) / (b - t)))
  have hnleft : (t₀ - a) / (t - a) < (n : Real) :=
    (le_max_left _ _).trans_lt hn
  have hnright : (b - t₀) / (b - t) < (n : Real) :=
    (le_max_right _ _).trans_lt hn
  refine ⟨n, ?_, ?_⟩
  · have hden : (0 : Real) < (n : Real) + 2 := by positivity
    have hkey : (t₀ - a) / ((n : Real) + 2) < t - a := by
      rw [div_lt_iff₀ hden]
      have heq : t₀ - a = (t₀ - a) / (t - a) * (t - a) := by
        field_simp
      rw [heq, mul_comm (t - a) ((n : Real) + 2)]
      calc
        (t₀ - a) / (t - a) * (t - a) < (n : Real) * (t - a) :=
          mul_lt_mul_of_pos_right hnleft hta
        _ ≤ ((n : Real) + 2) * (t - a) :=
          mul_le_mul_of_nonneg_right (by linarith) hta.le
    simp only [openWindowLeft]
    linarith
  · have hden : (0 : Real) < (n : Real) + 2 := by positivity
    have hkey : (b - t₀) / ((n : Real) + 2) < b - t := by
      rw [div_lt_iff₀ hden]
      have heq : b - t₀ = (b - t₀) / (b - t) * (b - t) := by
        field_simp
      rw [heq, mul_comm (b - t) ((n : Real) + 2)]
      calc
        (b - t₀) / (b - t) * (b - t) < (n : Real) * (b - t) :=
          mul_lt_mul_of_pos_right hnright htb
        _ ≤ ((n : Real) + 2) * (b - t) :=
          mul_le_mul_of_nonneg_right (by linarith) htb.le
    simp only [openWindowRight]
    linarith

/-- The canonical compact windows exhaust the open interval. -/
theorem iUnion_openWindow {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b) :
    (⋃ n : Nat, openWindow a b t₀ n) = Set.Ioo a b := by
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ht
    exact openWindow_subset ht₀ n hn
  · intro t ht
    obtain ⟨n, hn⟩ := mem_openWindow ht
    exact Set.mem_iUnion.mpr ⟨n, hn⟩

/-- Every compact interval contained in `(a,b)` is contained in one canonical
compact window. -/
theorem exists_window_superset {a b t₀ c d : Real}
    (ht₀ : t₀ ∈ Set.Ioo a b) (hcd : Set.Icc c d ⊆ Set.Ioo a b) :
    ∃ n : Nat, Set.Icc c d ⊆ openWindow a b t₀ n := by
  by_cases hle : c ≤ d
  · have hc : c ∈ Set.Ioo a b := hcd ⟨le_rfl, hle⟩
    have hd : d ∈ Set.Ioo a b := hcd ⟨hle, le_rfl⟩
    obtain ⟨nc, hnc⟩ := mem_openWindow (t₀ := t₀) hc
    obtain ⟨nd, hnd⟩ := mem_openWindow (t₀ := t₀) hd
    refine ⟨max nc nd, ?_⟩
    have hnc' : c ∈ openWindow a b t₀ (max nc nd) :=
      openWindow_mono ht₀ (Nat.le_max_left nc nd) hnc
    have hnd' : d ∈ openWindow a b t₀ (max nc nd) :=
      openWindow_mono ht₀ (Nat.le_max_right nc nd) hnd
    intro t ht
    exact ⟨hnc'.1.trans ht.1, ht.2.trans hnd'.2⟩
  · refine ⟨0, ?_⟩
    intro t ht
    exact (hle (ht.1.trans ht.2)).elim

/-- Every point of the ambient open interval has one canonical compact window
as a neighborhood, not merely as a containing set. -/
theorem exists_window_nhds {a b t₀ t : Real}
    (ht₀ : t₀ ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    ∃ n : Nat, openWindow a b t₀ n ∈ 𝓝 t := by
  obtain ⟨c, d, _htIcc, hmem, hsub⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (Ioo_mem_nhds ht.1 ht.2)
  obtain ⟨n, hn⟩ := exists_window_superset ht₀ hsub
  exact ⟨n, Filter.mem_of_superset hmem hn⟩

/-- Open-closed interval `(a,b]`, with a chosen initial time inside it. -/
def openClosed (a b t₀ : Real) (ht₀ : t₀ ∈ Set.Ioc a b) : RealTimeInterval where
  carrier := Set.Ioc a b
  regular := Set.Ioo a b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ⟨ht.1, le_of_lt ht.2⟩
  regular_isOpen := isOpen_Ioo
  regular_mem_nhds := by
    intro t ht
    exact Ioc_mem_nhds ht.1 ht.2

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
  regular_isOpen := isOpen_Ioi
  regular_mem_nhds := by
    intro t ht
    exact Ici_mem_nhds (Set.mem_Ioi.mp ht)

/-- Infinite interval `(a,∞)`, with a chosen initial time inside it. -/
def openInfinite (a t₀ : Real) (ht₀ : a < t₀) : RealTimeInterval where
  carrier := Set.Ioi a
  regular := Set.Ioi a
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ht
  regular_isOpen := isOpen_Ioi
  regular_mem_nhds := by
    intro t ht
    exact Ioi_mem_nhds ht

/-- Infinite interval `(-∞,b]`, with a chosen initial time inside it. -/
def infiniteClosed (b t₀ : Real) (ht₀ : t₀ ≤ b) : RealTimeInterval where
  carrier := Set.Iic b
  regular := Set.Iio b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact Set.mem_Iic.mpr (le_of_lt (Set.mem_Iio.mp ht))
  regular_isOpen := isOpen_Iio
  regular_mem_nhds := by
    intro t ht
    exact Iic_mem_nhds (Set.mem_Iio.mp ht)

/-- Infinite interval `(-∞,b)`, with a chosen initial time inside it. -/
def infiniteOpen (b t₀ : Real) (ht₀ : t₀ < b) : RealTimeInterval where
  carrier := Set.Iio b
  regular := Set.Iio b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ht
  regular_isOpen := isOpen_Iio
  regular_mem_nhds := by
    intro t ht
    exact Iio_mem_nhds ht

/-- Whole real line, with a chosen reference initial time. -/
def univ (t₀ : Real) : RealTimeInterval where
  carrier := Set.univ
  regular := Set.univ
  initial := t₀
  initial_mem := trivial
  regular_subset := by
    intro t ht
    exact ht
  regular_isOpen := isOpen_univ
  regular_mem_nhds := by
    intro t ht
    simp

end RealTimeInterval

end DifferentialGeometry.Integral.Connection

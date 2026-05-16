import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic

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

/-- Open interval `(a,b)`, with a chosen initial time inside it. -/
def openInterval (a b t₀ : Real) (ht₀ : t₀ ∈ Set.Ioo a b) : RealTimeInterval where
  carrier := Set.Ioo a b
  regular := Set.Ioo a b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ht

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

end RealTimeInterval

end Realized
end RicciFlower

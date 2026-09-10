import DifferentialGeometry.Tensor.Alternating.Wedge

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

structure HarnackClock where
  origin : Real
  time : Real
  origin_lt_time : origin < time

namespace HarnackClock

def elapsed (clock : HarnackClock) : Real :=
  clock.time - clock.origin

theorem elapsed_pos (clock : HarnackClock) : 0 < clock.elapsed := by
  exact sub_pos.mpr clock.origin_lt_time

theorem elapsed_ne_zero (clock : HarnackClock) : clock.elapsed ≠ 0 :=
  ne_of_gt clock.elapsed_pos

theorem origin_ne_time (clock : HarnackClock) : clock.origin ≠ clock.time :=
  ne_of_lt clock.origin_lt_time

theorem one_div_elapsed_pos (clock : HarnackClock) : 0 < 1 / clock.elapsed := by
  exact one_div_pos.mpr clock.elapsed_pos

theorem not_exists_at_same_time (t : Real) :
    ¬Nonempty {clock : HarnackClock // clock.origin = t ∧ clock.time = t} := by
  intro h
  obtain ⟨clock⟩ := h
  exact clock.1.origin_ne_time (clock.2.1.trans clock.2.2.symm)

end HarnackClock

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]

abbrev HamiltonHarnackTwoForm (V : Type*) [NormedAddCommGroup V]
    [NormedSpace Real V] :=
  V [⋀^Fin 2]→L[Real] Real

abbrev HamiltonHarnackCarrier (V : Type*) [NormedAddCommGroup V]
    [NormedSpace Real V] :=
  HamiltonHarnackTwoForm V × StrongDual Real V

noncomputable def normalizedWedge (A B : StrongDual Real V) :
    HamiltonHarnackTwoForm V :=
  (2 : Real)⁻¹ •
    ContinuousAlternatingMap.uncurryFin
      (A.smulRight
        (ContinuousAlternatingMap.ofSubsingleton Real V Real (0 : Fin 1) B))

theorem normalizedWedge_apply (A B : StrongDual Real V) (v : Fin 2 -> V) :
    normalizedWedge A B v =
      (1 / 2 : Real) * (A (v 0) * B (v 1) - A (v 1) * B (v 0)) := by
  simp [normalizedWedge, ContinuousAlternatingMap.uncurryFin_apply,
    Fin.sum_univ_two, Fin.removeNth, sub_eq_add_neg]

end DifferentialGeometry.PDE.RicciFlow

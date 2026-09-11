import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.TangentCone.Real

open Filter
open scoped Topology

theorem IsLocalMax.deriv_deriv_nonpos {f : ℝ → ℝ} {x : ℝ}
    (hmax : IsLocalMax f x) (hcont : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hpos : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hmin := isLocalMin_of_deriv_deriv_pos hpos hmax.deriv_eq_zero hcont
  have heq : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hmax, hmin] with y hle hge
    exact le_antisymm hle hge
  have hzero : deriv (deriv f) x = 0 := by
    simpa only [deriv_const', deriv_const] using heq.deriv.deriv_eq
  exact hpos.ne' hzero

theorem mem_posTangentConeAt_halfSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (phi : E →L[Real] Real) {a : Real} {x v : E}
    (hx : phi x = a) (hv : 0 ≤ phi v) :
    v ∈ posTangentConeAt {z | a ≤ phi z} x := by
  have hconv : Convex Real {z | a ≤ phi z} :=
    convex_halfSpace_ge phi.toLinearMap.isLinear a
  have hmem : x + v ∈ {z | a ≤ phi z} := by
    simp only [Set.mem_ofPred_eq, map_add, hx]
    linarith
  have hseg := hconv.openSegment_subset (show x ∈ {z | a ≤ phi z} from hx.ge) hmem
  simpa only [add_sub_cancel_left] using sub_mem_posTangentConeAt_of_openSegment_subset hseg

theorem IsLocalMinOn.hasFDerivWithinAt_pos_of_halfSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {f : E → Real} {f' : E →L[Real] Real} (phi : E →L[Real] Real)
    {a : Real} {x v : E} (hx : phi x = a)
    (hmin : IsLocalMinOn f {z | a ≤ phi z} x)
    (hf : HasFDerivWithinAt f f' {z | a ≤ phi z} x)
    (hf' : f' ≠ 0) (hv : 0 < phi v) : 0 < f' v := by
  have hnonneg : 0 ≤ f' v := hmin.hasFDerivWithinAt_nonneg hf
    (mem_posTangentConeAt_halfSpace phi hx hv.le)
  apply lt_of_le_of_ne hnonneg
  intro hzero
  apply hf'
  ext w
  have ht : phi (w - (phi w / phi v) • v) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul]
    rw [div_mul_cancel₀ _ hv.ne']
    exact sub_self _
  have heq := hmin.hasFDerivWithinAt_eq_zero hf
    (mem_posTangentConeAt_halfSpace phi hx ht.ge)
    (mem_posTangentConeAt_halfSpace phi hx (by rw [map_neg, ht, neg_zero]))
  change f' w = 0
  simpa only [map_sub, map_smul, smul_eq_mul, ← hzero, mul_zero, sub_zero,
    Pi.zero_apply] using heq

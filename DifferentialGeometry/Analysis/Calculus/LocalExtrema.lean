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

theorem HasFDerivAt.apply_nonneg_of_eventually_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {a : E} {f' g' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' a) (hg : HasFDerivAt g g' a)
    (hfa : f a = 0) (hga : g a = 0)
    (hpos : ∀ᶠ x in 𝓝 a, 0 < f x → 0 ≤ g x)
    {v : E} (hv : 0 < f' v) : 0 ≤ g' v := by
  by_contra! hn
  have hc : HasDerivAt (fun t : ℝ => a + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add a
  have hfc : HasDerivAt (fun t : ℝ => f (a + t • v)) (f' v) 0 := by
    exact (show HasFDerivAt f f' (a + (0 : ℝ) • v) by simpa using hf).comp_hasDerivAt 0 hc
  have hgc : HasDerivAt (fun t : ℝ => g (a + t • v)) (g' v) 0 := by
    exact (show HasFDerivAt g g' (a + (0 : ℝ) • v) by simpa using hg).comp_hasDerivAt 0 hc
  have hfs := eventually_nhdsWithin_sign_eq_of_deriv_pos
    (hfc.deriv.symm ▸ hv) (by simpa using hfa)
  have hgs := eventually_nhdsWithin_sign_eq_of_deriv_neg
    (hgc.deriv.symm ▸ hn) (by simpa using hga)
  have hct : Tendsto (fun t : ℝ => a + t • v) (𝓝 0) (𝓝 a) := by
    simpa using hc.continuousAt.tendsto
  have hps := hct.eventually hpos
  have hboth := hfs.and (hgs.and hps)
  obtain ⟨ε, hε, hεprop⟩ := Metric.eventually_nhds_iff.mp hboth
  have ht : 0 < ε / 2 := by linarith
  have hdist : dist (ε / 2) (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    linarith
  obtain ⟨hft, hgt, hpt⟩ := hεprop hdist
  have hfpos : 0 < f (a + (ε / 2) • v) := by
    apply sign_eq_one_iff.mp
    simpa only [sub_zero, sign_pos ht] using hft
  have hgneg : g (a + (ε / 2) • v) < 0 := by
    apply sign_eq_neg_one_iff.mp
    simpa only [zero_sub, sign_neg (neg_neg_of_pos ht)] using hgt
  exact (hpt hfpos).not_gt hgneg

private theorem continuousLinearMap_apply_pos_of_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ ψ : E →L[ℝ] ℝ) (hψ : ψ ≠ 0)
    (h : ∀ v, 0 < φ v → 0 ≤ ψ v) {v : E} (hv : 0 < φ v) : 0 < ψ v := by
  apply lt_of_le_of_ne (h v hv)
  intro heq
  have hz : ψ v = 0 := heq.symm
  apply hψ
  ext w
  let t := (|φ w| + 1) / φ v
  have ht : t * φ v = |φ w| + 1 := div_mul_cancel₀ _ hv.ne'
  have hp : 0 < φ (w + t • v) := by
    rw [map_add, map_smul, smul_eq_mul, ht]
    linarith [neg_abs_le (φ w)]
  have hn : 0 < φ (-w + t • v) := by
    rw [map_add, map_neg, map_smul, smul_eq_mul, ht]
    linarith [le_abs_self (φ w)]
  have hwp := h _ hp
  have hwn := h _ hn
  simp only [map_add, map_smul, smul_eq_mul, hz, mul_zero, add_zero, map_neg] at hwp hwn
  change ψ w = 0
  exact le_antisymm (by linarith) hwp

theorem HasFDerivAt.apply_pos_of_eventually_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {a : E} {f' g' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' a) (hg : HasFDerivAt g g' a)
    (hfa : f a = 0) (hga : g a = 0) (hg' : g' ≠ 0)
    (hpos : ∀ᶠ x in 𝓝 a, 0 < f x → 0 ≤ g x)
    {v : E} (hv : 0 < f' v) : 0 < g' v :=
  continuousLinearMap_apply_pos_of_nonneg f' g' hg'
    (fun _ hw => HasFDerivAt.apply_nonneg_of_eventually_nonneg hf hg hfa hga hpos hw) hv

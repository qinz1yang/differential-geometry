import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem radial_derivative_eventually_positive
    {δ : ℝ → E} {v : E}
    (hδ : ContDiffAt ℝ 1 δ 0) (hzero : δ 0 = 0)
    (hd : HasDerivAt δ v 0) (hv : v ≠ 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      HasDerivAt (fun s => ‖δ s‖) (deriv (fun s => ‖δ s‖) t) t ∧
      ‖v‖ / 2 ≤ deriv (fun s => ‖δ s‖) t := by
  let q : ℝ → E := fun t => t⁻¹ • δ t
  let d : ℝ → ℝ := fun t => (fderiv ℝ (norm : E → ℝ) (q t)) (deriv δ t)
  have hq : Tendsto q (𝓝[>] 0) (𝓝 v) := by
    simpa only [q, zero_add, hzero, sub_zero] using hd.tendsto_slope_zero_right
  have hcder : ContinuousAt (deriv δ) 0 := by
    exact (hδ.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
  have hder : Tendsto (deriv δ) (𝓝[>] 0) (𝓝 v) := by
    simpa only [hd.deriv] using hcder.tendsto.mono_left nhdsWithin_le_nhds
  have hnorm : ContDiffAt ℝ 1 (norm : E → ℝ) v := contDiffAt_norm ℝ hv
  have heval : ContinuousAt
      (fun p : E × E => (fderiv ℝ (norm : E → ℝ) p.1) p.2) (v, v) :=
    ((hnorm.continuousAt_fderiv one_ne_zero).comp continuousAt_fst).clm_apply
      continuousAt_snd
  have hlim : Tendsto d (𝓝[>] 0) (𝓝 ‖v‖) := by
    have hc := heval.tendsto.comp (hq.prodMk_nhds hder)
    change Tendsto d (𝓝[>] 0)
      (𝓝 ((fderiv ℝ (norm : E → ℝ) v) v)) at hc
    simpa only [(hnorm.differentiableAt one_ne_zero).fderiv_norm_self] using hc
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hlower : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖v‖ / 2 ≤ d t :=
    hlim.eventually_const_le (by linarith)
  have hreg : ∀ᶠ t in 𝓝[>] (0 : ℝ), ContDiffAt ℝ 1 δ t :=
    (hδ.eventually (by simp)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hq.eventually_ne hv, hreg, hlower]
    with t ht hqt hdt hlt
  have htpos : 0 < t := ht
  have hnq : HasFDerivAt (norm : E → ℝ)
      (fderiv ℝ (norm : E → ℝ) (q t)) (q t) :=
    ((contDiffAt_norm ℝ hqt : ContDiffAt ℝ 1 (norm : E → ℝ) (q t)).differentiableAt
      one_ne_zero).hasFDerivAt
  have hnδ : HasFDerivAt (norm : E → ℝ)
      (fderiv ℝ (norm : E → ℝ) (q t)) (δ t) := by
    simpa only [q, smul_inv_smul₀ htpos.ne'] using
      hnq.hasFDerivAt_norm_smul_pos htpos
  have hμ : HasDerivAt (fun s => ‖δ s‖) (d t) t :=
    hnδ.comp_hasDerivAt t (hdt.differentiableAt one_ne_zero).hasDerivAt
  simpa only [hμ.deriv] using And.intro hμ hlt

/-- A regular `C¹` arc starting at the origin has a Lipschitz parametrization
by its original ambient radius. The inverse is the inverse of the literal norm
of that arc, and its radial derivative bound is derived from the nonzero tangent.
No differentiability of the original parametrization beyond `C¹` is asserted. -/
theorem exists_radial_reparametrization_of_contDiffAt
    {δ : ℝ → E} {v : E} {tmax : ℝ}
    (hδ : ContDiffAt ℝ 1 δ 0) (hzero : δ 0 = 0)
    (hd : HasDerivAt δ v 0) (hv : v ≠ 0) (htmax : 0 < tmax) :
    ∃ T : ℝ, 0 < T ∧ T < tmax ∧
      let R := ‖δ T‖
      let τ := Function.invFunOn (fun t => ‖δ t‖) (Icc 0 T)
      0 < R ∧ τ 0 = 0 ∧
      MapsTo τ (Icc 0 R) (Icc 0 T) ∧
      (∀ r ∈ Icc 0 R, ‖δ (τ r)‖ = r) ∧
      (∀ t ∈ Icc 0 T, τ ‖δ t‖ = t) ∧
      (∃ K L : ℝ≥0,
        LipschitzOnWith K τ (Icc 0 R) ∧
        LipschitzOnWith L (δ ∘ τ) (Icc 0 R)) ∧
      (∀ t ∈ Ioc 0 T,
        HasDerivAt (fun s => ‖δ s‖) (deriv (fun s => ‖δ s‖) t) t ∧
        ‖v‖ / 2 ≤ deriv (fun s => ‖δ s‖) t) := by
  obtain ⟨L, s, hs, hLip⟩ := hδ.exists_lipschitzOnWith
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (t ∈ s ∧ HasDerivAt (fun s => ‖δ s‖) (deriv (fun s => ‖δ s‖) t) t ∧
        ‖v‖ / 2 ≤ deriv (fun s => ‖δ s‖) t) ∧ t < tmax := by
    exact (((show ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ s from hs).filter_mono
      nhdsWithin_le_nhds).and
      (radial_derivative_eventually_positive hδ hzero hd hv)).and
      ((eventually_lt_nhds htmax).filter_mono nhdsWithin_le_nhds)
  obtain ⟨T, hT, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hevent
  have hTpos : 0 < T := hT
  have hsIcc : Icc 0 T ⊆ s := by
    intro t ht
    rcases ht.1.eq_or_lt with heq | hpos
    · simpa only [← heq] using mem_of_mem_nhds hs
    · exact (hsub ⟨hpos, ht.2⟩).1.1
  have hδLip : LipschitzOnWith L δ (Icc 0 T) := hLip.mono hsIcc
  let μ : ℝ → ℝ := fun t => ‖δ t‖
  have hμcont : ContinuousOn μ (Icc 0 T) := hδLip.continuousOn.norm
  have hbound : ∀ t ∈ Ioc 0 T, HasDerivAt μ (deriv μ t) t ∧
      ‖v‖ / 2 ≤ deriv μ t := fun t ht => (hsub ht).1.2
  have hdiff : DifferentiableOn ℝ μ (interior (Icc 0 T)) := by
    intro t ht
    rw [interior_Icc] at ht
    exact (hbound t ⟨ht.1, ht.2.le⟩).1.differentiableAt.differentiableWithinAt
  have hgrowth : ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, x ≤ y →
      ‖v‖ / 2 * (y - x) ≤ μ y - μ x :=
    (convex_Icc (0 : ℝ) T).mul_sub_le_image_sub_of_le_deriv hμcont hdiff
      (by
        intro t ht
        rw [interior_Icc] at ht
        exact (hbound t ⟨ht.1, ht.2.le⟩).2)
  have hcpos : 0 < ‖v‖ / 2 := half_pos (norm_pos_iff.mpr hv)
  have hmono : StrictMonoOn μ (Icc 0 T) := by
    intro x hx y hy hxy
    have := hgrowth x hx y hy hxy.le
    have := mul_pos hcpos (sub_pos.mpr hxy)
    linarith
  have hμzero : μ 0 = 0 := by simp only [μ, hzero, norm_zero]
  have hzeroIcc : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hTpos.le⟩
  have hTIcc : T ∈ Icc 0 T := ⟨hTpos.le, le_rfl⟩
  have hR : 0 < μ T := by simpa only [hμzero] using hmono hzeroIcc hTIcc hTpos
  let τ := Function.invFunOn μ (Icc 0 T)
  have hsurj : SurjOn μ (Icc 0 T) (Icc 0 (μ T)) := by
    simpa only [hμzero] using hμcont.surjOn_Icc hzeroIcc hTIcc
  have hτmem : MapsTo τ (Icc 0 (μ T)) (Icc 0 T) := hsurj.mapsTo_invFunOn
  have hright : ∀ r ∈ Icc 0 (μ T), μ (τ r) = r := hsurj.rightInvOn_invFunOn
  have hleft : ∀ t ∈ Icc 0 T, τ (μ t) = t := hmono.injOn.leftInvOn_invFunOn
  have hτzero : τ 0 = 0 := by simpa only [hμzero] using hleft 0 hzeroIcc
  have hanti : ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T,
      dist x y ≤ (‖v‖ / 2)⁻¹ * dist (μ x) (μ y) := by
    intro x hx y hy
    wlog hxy : x ≤ y generalizing x y
    · simpa only [dist_comm] using this y hy x hx (le_of_not_ge hxy)
    have hμxy : μ x ≤ μ y := hmono.monotoneOn hx hy hxy
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy),
      Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hμxy)]
    have hg := hgrowth x hx y hy hxy
    have hh : y - x ≤ (μ y - μ x) / (‖v‖ / 2) :=
      (le_div_iff₀ hcpos).mpr (by simpa only [mul_comm] using hg)
    simpa only [div_eq_inv_mul, neg_sub] using hh
  have hτLip : LipschitzOnWith (Real.toNNReal ((‖v‖ / 2)⁻¹)) τ (Icc 0 (μ T)) := by
    apply LipschitzOnWith.of_dist_le'
    intro r hr s hs'
    simpa only [hright r hr, hright s hs'] using hanti (τ r) (hτmem hr) (τ s) (hτmem hs')
  refine ⟨T, hTpos, (hsub ⟨hTpos, le_rfl⟩).2,
    hR, hτzero, hτmem, hright, hleft, ?_, hbound⟩
  exact ⟨_, L * Real.toNNReal ((‖v‖ / 2)⁻¹), hτLip, hδLip.comp hτLip hτmem⟩

end DifferentialGeometry.Analysis

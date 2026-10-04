import DifferentialGeometry.Analysis.Calculus.SmoothApproximation.FineChart
import DifferentialGeometry.Analysis.Calculus.ContDiff.QuadraticJetZeroExtension
import DifferentialGeometry.Analysis.Calculus.Inverse.PerturbationDeterminant

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

theorem exists_hasFDerivAt_equiv_of_contDiffOn_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {r : ℕ} (hr : 1 ≤ r) (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ r e e.source) (hesymm : ContDiffOn ℝ r e.symm e.target) {y : E}
    (hy : y ∈ e.target) :
    ∃ M : E ≃L[ℝ] E, HasFDerivAt e.symm (M : E →L[ℝ] E) y := by
  have hr0 : ((r : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hx : e.symm y ∈ e.source := e.map_target hy
  have hA : HasFDerivAt e.symm (fderiv ℝ e.symm y) y :=
    ((hesymm.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt hr0).hasFDerivAt
  have hB : HasFDerivAt e (fderiv ℝ e (e.symm y)) (e.symm y) :=
    ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt hr0).hasFDerivAt
  have h1 : (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) = ContinuousLinearMap.id ℝ E := by
    have hcomp : HasFDerivAt (⇑e ∘ ⇑e.symm)
        ((fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y)) y :=
      hB.comp y hA
    have hid : HasFDerivAt (⇑e ∘ ⇑e.symm) (ContinuousLinearMap.id ℝ E) y := by
      refine (hasFDerivAt_id (𝕜 := ℝ) y).congr_of_eventuallyEq ?_
      filter_upwards [e.open_target.mem_nhds hy] with z hz
      exact e.right_inv hz
    exact hcomp.unique hid
  have h2 : (fderiv ℝ e.symm y).comp (fderiv ℝ e (e.symm y)) = ContinuousLinearMap.id ℝ E := by
    have hA' : HasFDerivAt e.symm (fderiv ℝ e.symm y) (e (e.symm y)) := by
      rw [e.right_inv hy]
      exact hA
    have hcomp : HasFDerivAt (⇑e.symm ∘ ⇑e)
        ((fderiv ℝ e.symm y).comp (fderiv ℝ e (e.symm y))) (e.symm y) :=
      hA'.comp (e.symm y) hB
    have hid : HasFDerivAt (⇑e.symm ∘ ⇑e) (ContinuousLinearMap.id ℝ E) (e.symm y) := by
      refine (hasFDerivAt_id (𝕜 := ℝ) (e.symm y)).congr_of_eventuallyEq ?_
      filter_upwards [e.open_source.mem_nhds hx] with z hz
      exact e.left_inv hz
    exact hcomp.unique hid
  refine ⟨ContinuousLinearEquiv.equivOfInverse' (fderiv ℝ e.symm y) (fderiv ℝ e (e.symm y)) h2 h1,
    ?_⟩
  exact hA.congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)

private theorem contDiffOn_comp_homeomorph_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {r : ℕ} (hr : 1 ≤ r) (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ r e e.source) (hesymm : ContDiffOn ℝ r e.symm e.target) (g : E ≃ₜ E)
    (hg : ContDiffOn ℝ ∞ (⇑g ∘ ⇑e.symm) e.target)
    (hgL : ∀ x, ∃ L : E ≃L[ℝ] E, HasFDerivAt g (L : E →L[ℝ] E) x) :
    ContDiffOn ℝ ∞ (⇑e ∘ ⇑g.symm) (⇑g '' e.source) := by
  rintro _ ⟨x, hx, rfl⟩
  have hy : e x ∈ e.target := e.map_source hx
  obtain ⟨M, hM⟩ := exists_hasFDerivAt_equiv_of_contDiffOn_symm hr e he hesymm hy
  obtain ⟨L, hL⟩ := hgL (e.symm (e x))
  have hΦt : g x ∈ (e.symm.trans g.toOpenPartialHomeomorph).target := by
    rw [OpenPartialHomeomorph.trans_target]
    refine ⟨mem_univ _, ?_⟩
    change g.symm (g x) ∈ e.source
    rw [g.symm_apply_apply]
    exact hx
  have hΦs : (e.symm.trans g.toOpenPartialHomeomorph).symm (g x) = e x := by
    change e (g.symm (g x)) = e x
    rw [g.symm_apply_apply]
  have hcomp : HasFDerivAt (⇑g ∘ ⇑e.symm) ((L : E →L[ℝ] E).comp (M : E →L[ℝ] E)) (e x) :=
    hL.comp (e x) hM
  have hderiv : HasFDerivAt (e.symm.trans g.toOpenPartialHomeomorph)
      ((M.trans L : E ≃L[ℝ] E) : E →L[ℝ] E)
      ((e.symm.trans g.toOpenPartialHomeomorph).symm (g x)) := by
    rw [hΦs]
    exact hcomp
  have hsmooth : ContDiffAt ℝ ∞ (e.symm.trans g.toOpenPartialHomeomorph)
      ((e.symm.trans g.toOpenPartialHomeomorph).symm (g x)) := by
    rw [hΦs]
    exact hg.contDiffAt (e.open_target.mem_nhds hy)
  exact ((e.symm.trans g.toOpenPartialHomeomorph).contDiffAt_symm hΦt hderiv
    hsmooth).contDiffWithinAt

theorem exists_smoothing_homeomorph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} {r : ℕ} (hr : 1 ≤ r)
    (χ : ι → OpenPartialHomeomorph E E)
    (hχ : ∀ a, ContDiffOn ℝ r (χ a) (χ a).source)
    (hχsymm : ∀ a, ContDiffOn ℝ r (χ a).symm (χ a).target)
    (htrans : ∀ a b,
      ContDiffOn ℝ ∞ ((χ a).symm.trans (χ b)) ((χ a).symm.trans (χ b)).source) :
    ∃ g : E ≃ₜ E,
      (ContDiff ℝ r g ∧ ContDiff ℝ r g.symm) ∧
      (∀ x, x ∉ ⋃ a, (χ a).source → g x = x) ∧
      (∀ a, ContDiffOn ℝ ∞ (⇑g ∘ ⇑(χ a).symm) (χ a).target) ∧
      (∀ a, ContDiffOn ℝ ∞ (⇑(χ a) ∘ ⇑g.symm) (⇑g '' (χ a).source)) ∧
      ∀ x, 0 < (fderiv ℝ g x).det := by
  have hW : IsOpen (⋃ a, (χ a).source) := isOpen_iUnion fun a => (χ a).open_source
  obtain ⟨δ, hδc, hδ0, hδ1, hδpos, hδU⟩ := exists_jet_decay_weight hW
  have hεc : Continuous fun x => 1 / 2 * δ x ^ 2 := (hδc.fun_pow 2).const_mul (1 / 2)
  obtain ⟨h, hh, hhW, hhbd⟩ := exists_chart_smooth_fine_approximation χ hχ hχsymm htrans
    (ε := fun x => 1 / 2 * δ x ^ 2) hεc.continuousOn
    (fun x hx => mul_pos (by norm_num) (pow_pos (hδpos x hx) 2))
  have hf : ContDiffOn ℝ (r : ℕ∞ω) (fun y => h y - y) (⋃ a, (χ a).source) :=
    hhW.sub contDiffOn_id
  obtain ⟨hηc, -, hηd⟩ := contDiff_indicator_of_weight_decay hW r hf (c := 1 / 2)
    (by norm_num) hδ0 hδ1 hδU fun j hj x hx => hhbd x hx j hj
  obtain ⟨g, hgη, hgc, hgsc, hgL, -⟩ :=
    exists_homeomorph_add_of_norm_fderiv_le hr hηc (c := 1 / 2) (by norm_num) (hηd hr)
  have hgfix : ∀ x, x ∉ ⋃ a, (χ a).source → g x = x := by
    intro x hx
    rw [hgη x, indicator_of_notMem hx, add_zero]
  have hgh : ∀ x ∈ ⋃ a, (χ a).source, g x = h x := by
    intro x hx
    rw [hgη x, indicator_of_mem hx]
    exact add_sub_cancel x (h x)
  have h3 : ∀ a, ContDiffOn ℝ ∞ (⇑g ∘ ⇑(χ a).symm) (χ a).target := by
    intro a
    refine (hh a).congr fun y hy => ?_
    exact hgh _ (mem_iUnion_of_mem a ((χ a).map_target hy))
  refine ⟨g, ⟨hgc, hgsc⟩, hgfix, h3, fun a => ?_, fun x => ?_⟩
  · exact contDiffOn_comp_homeomorph_symm hr (χ a) (hχ a) (hχsymm a) g (h3 a)
      fun x => (hgL x).imp fun _ hL => hL.2.hasFDerivAt
  · obtain ⟨L, hL1, hL2⟩ := hgL x
    rw [hL2.hasFDerivAt.fderiv, hL1]
    exact det_id_add_pos _ ((hηd hr x).trans_lt (by norm_num))

theorem exists_smoothing_homeomorph_trans {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} {r : ℕ} (hr : 1 ≤ r)
    (χ : ι → OpenPartialHomeomorph E E)
    (hχ : ∀ a, ContDiffOn ℝ r (χ a) (χ a).source)
    (hχsymm : ∀ a, ContDiffOn ℝ r (χ a).symm (χ a).target)
    (htrans : ∀ a b,
      ContDiffOn ℝ ∞ ((χ a).symm.trans (χ b)) ((χ a).symm.trans (χ b)).source) :
    ∃ g : E ≃ₜ E,
      (ContDiff ℝ r g ∧ ContDiff ℝ r g.symm) ∧
      (∀ x, x ∉ ⋃ a, (χ a).source → g x = x ∧ g.symm x = x) ∧
      g '' (⋃ a, (χ a).source) = ⋃ a, (χ a).source ∧
      (∀ a, ContDiffOn ℝ ∞ ((χ a).symm.trans g.toOpenPartialHomeomorph)
        ((χ a).symm.trans g.toOpenPartialHomeomorph).source) ∧
      (∀ a, ContDiffOn ℝ ∞ (g.toOpenPartialHomeomorph.symm.trans (χ a))
        (g.toOpenPartialHomeomorph.symm.trans (χ a)).source) ∧
      ∀ x, 0 < (fderiv ℝ g x).det := by
  obtain ⟨g, hgc, hgfix, h3, h4, hdet⟩ := exists_smoothing_homeomorph hr χ hχ hχsymm htrans
  refine ⟨g, hgc, fun x hx => ⟨hgfix x hx, homeomorph_symm_apply_eq_self_of_apply_eq g hgfix hx⟩,
    homeomorph_image_eq_self_of_apply_eq g hgfix, fun a => ?_, fun a => ?_, hdet⟩
  · have hsub : ((χ a).symm.trans g.toOpenPartialHomeomorph).source ⊆ (χ a).target := by
      intro y hy
      rw [OpenPartialHomeomorph.trans_source] at hy
      exact hy.1
    exact (h3 a).mono hsub
  · have hsub : (g.toOpenPartialHomeomorph.symm.trans (χ a)).source ⊆ ⇑g '' (χ a).source := by
      intro z hz
      rw [OpenPartialHomeomorph.trans_source] at hz
      exact ⟨g.symm z, hz.2, g.apply_symm_apply z⟩
    exact (h4 a).mono hsub

end DifferentialGeometry.Analysis

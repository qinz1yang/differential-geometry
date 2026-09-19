import DifferentialGeometry.Analysis.Calculus.Sard
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace DifferentialGeometry.Calculus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_curve_perturbation_parameter
    (c : ℝ × ℝ → F) (ρ : ℝ × ℝ → ℝ) (q : ℝ × ℝ × ℝ) (v : F) :
    HasFDerivAt (fun w : F =>
      (c (q.1, q.2.1) - ρ (q.1, q.2.1) • w) -
      (c (q.1, q.2.2) - ρ (q.1, q.2.2) • w))
      ((ρ (q.1, q.2.2) - ρ (q.1, q.2.1)) • ContinuousLinearMap.id ℝ F) v := by
  let L : F →L[ℝ] F :=
    (ρ (q.1, q.2.2) - ρ (q.1, q.2.1)) • ContinuousLinearMap.id ℝ F
  have h : HasFDerivAt (fun w : F => (c (q.1, q.2.1) - c (q.1, q.2.2)) + L w) L v :=
    L.hasFDerivAt.const_add _
  convert h using 1
  funext w
  change c (q.1, q.2.1) - ρ (q.1, q.2.1) • w -
      (c (q.1, q.2.2) - ρ (q.1, q.2.2) • w) =
    c (q.1, q.2.1) - c (q.1, q.2.2) + (ρ (q.1, q.2.2) - ρ (q.1, q.2.1)) • w
  rw [sub_smul]
  abel

theorem surjective_fderiv_curve_perturbation_parameter
    (c : ℝ × ℝ → F) (ρ : ℝ × ℝ → ℝ) (q : ℝ × ℝ × ℝ) (v : F)
    (hρ : ρ (q.1, q.2.1) ≠ ρ (q.1, q.2.2)) :
    Function.Surjective (fderiv ℝ (fun w : F =>
      (c (q.1, q.2.1) - ρ (q.1, q.2.1) • w) -
      (c (q.1, q.2.2) - ρ (q.1, q.2.2) • w)) v) := by
  rw [(hasFDerivAt_curve_perturbation_parameter c ρ q v).fderiv]
  intro z
  refine ⟨(ρ (q.1, q.2.2) - ρ (q.1, q.2.1))⁻¹ • z, ?_⟩
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_smul]
  rw [mul_inv_cancel₀ (sub_ne_zero.mpr hρ.symm), one_smul]

theorem hasCompactSupport_curve_perturbation_sub
    (c : ℝ × ℝ → F) {ρ : ℝ × ℝ → ℝ} (hρ : HasCompactSupport ρ) (v : F) :
    HasCompactSupport (fun p => (c p - ρ p • v) - c p) := by
  convert (hρ.smul_right (f' := fun _ => v)).neg using 1
  funext p
  simp only [Pi.neg_apply]
  abel

theorem contDiffOn_curve_spacetime_perturbation
    {c : ℝ × ℝ → F} {ρ : ℝ × ℝ → ℝ} {O : Set (ℝ × ℝ)}
    (hc : ContDiffOn ℝ ∞ c O) (hρ : ContDiffOn ℝ ∞ ρ O) :
    ContDiffOn ℝ ∞ (fun q : F × (ℝ × ℝ) =>
      (q.2.1, c q.2 - ρ q.2 • q.1)) (univ ×ˢ O) :=
  (contDiff_fst.comp contDiff_snd).contDiffOn.prodMk
    ((hc.comp contDiffOn_snd (fun _ h => h.2)).sub
      ((hρ.comp contDiffOn_snd (fun _ h => h.2)).smul contDiffOn_fst))


theorem exists_pos_curve_perturbation_mem_open
    {c : ℝ × ℝ → F} {p₀ : ℝ × ℝ}
    (φ : ContDiffBump p₀) (hc : ContinuousOn c (closedBall p₀ φ.rOut)) {U : Set F} (hU : IsOpen U)
    (hcU : ∀ p ∈ closedBall p₀ φ.rOut, c p ∈ U) :
    ∃ δ > 0, ∀ v : F, ‖v‖ < δ → ∀ p, c p ∈ U → c p - φ p • v ∈ U := by
  have hcompact : IsCompact (c '' closedBall p₀ φ.rOut) :=
    (isCompact_closedBall p₀ φ.rOut).image_of_continuousOn hc
  obtain ⟨δ, hδ, hδU⟩ := hcompact.exists_cthickening_subset_open hU
    (by rintro _ ⟨p, hp, rfl⟩; exact hcU p hp)
  refine ⟨δ, hδ, fun v hv p hp => ?_⟩
  by_cases hpB : p ∈ closedBall p₀ φ.rOut
  · apply hδU
    apply mem_cthickening_of_dist_le _ (c p) δ (c '' closedBall p₀ φ.rOut) (by exact ⟨p, hpB, rfl⟩)
    have hdist : dist (c p - φ p • v) (c p) ≤ ‖v‖ := by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_of_nonneg φ.nonneg]
      exact mul_le_of_le_one_left (norm_nonneg v) φ.le_one
    exact hdist.trans hv.le
  · have hzero : φ p = 0 := φ.zero_of_le_dist (not_le.mp hpB).le
    simpa only [hzero, zero_smul, sub_zero] using hp

private theorem exists_norm_lt_regular_value_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {f : E → F} {U : Set E}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : F, ‖v‖ < ε ∧ ∀ x ∈ U, f x = v → Function.Surjective (fderiv ℝ f x) := by
  borelize F
  let μ : Measure F := MeasureTheory.Measure.addHaar
  have hnull : μ (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 :=
    hf.sard hU μ
  have hae : ∀ᵐ v ∂μ, ∀ x ∈ U, f x = v → Function.Surjective (fderiv ℝ f x) := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hnull] with v hv x hx heq
    by_contra hn
    exact hv ⟨x, ⟨hx, hn⟩, heq⟩
  obtain ⟨v, hv, hreg⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (measure_ball_pos μ 0 hε).ne' (ae_restrict_of_ae hae)
  exact ⟨v, by simpa only [mem_ball, dist_zero_right] using hv, hreg⟩

theorem exists_small_curve_perturbation_transverse_on_disjoint_arcs
    [FiniteDimensional ℝ F] {c : ℝ × ℝ → F} {O : Set (ℝ × ℝ)}
    (hc : ContDiffOn ℝ ∞ c O)
    {p₀ : ℝ × ℝ} (φ : ContDiffBump p₀) {V : Set F} (hV : IsOpen V)
    (hsupp : closedBall p₀ φ.rOut ⊆ O)
    (hcV : ∀ p ∈ closedBall p₀ φ.rOut, c p ∈ V)
    {U : Set (ℝ × ℝ × ℝ)} (hU : IsOpen U)
    (hpairs : ∀ q ∈ U, (q.1, q.2.1) ∈ O ∧ (q.1, q.2.2) ∈ O)
    (hleft : ∀ q ∈ U, (q.1, q.2.1) ∈ closedBall p₀ φ.rIn)
    (hright : ∀ q ∈ U, φ.rOut ≤ dist (q.1, q.2.2) p₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : F, ‖v‖ < ε ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (p.1, c p - φ p • v)) O ∧
      HasCompactSupport (fun p => (c p - φ p • v) - c p) ∧
      (∀ p, φ.rOut ≤ dist p p₀ → c p - φ p • v = c p) ∧
      (∀ p, ‖(c p - φ p • v) - c p‖ < ε) ∧
      (∀ p, c p ∈ V → c p - φ p • v ∈ V) ∧
      (∀ q ∈ U, Function.Surjective (fderiv ℝ (fun w : F =>
        (c (q.1, q.2.1) - φ (q.1, q.2.1) • w) -
        (c (q.1, q.2.2) - φ (q.1, q.2.2) • w)) v)) ∧
      ∀ q ∈ U,
        c (q.1, q.2.1) - φ (q.1, q.2.1) • v =
          c (q.1, q.2.2) - φ (q.1, q.2.2) • v →
        Function.Surjective (fderiv ℝ (fun r : ℝ × ℝ × ℝ =>
          (c (r.1, r.2.1) - φ (r.1, r.2.1) • v) -
          (c (r.1, r.2.2) - φ (r.1, r.2.2) • v)) q) := by
  let f : ℝ × ℝ × ℝ → F := fun q => c (q.1, q.2.1) - c (q.1, q.2.2)
  have hf : ContDiffOn ℝ ∞ f U :=
    (hc.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).contDiffOn
      (fun q hq => (hpairs q hq).1)).sub
      (hc.comp (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)).contDiffOn
        (fun q hq => (hpairs q hq).2))
  obtain ⟨δ, hδ, hδV⟩ := exists_pos_curve_perturbation_mem_open φ
    (hc.continuousOn.mono hsupp) hV hcV
  obtain ⟨v, hv, hreg⟩ := exists_norm_lt_regular_value_on hf hU (lt_min hε hδ)
  have hvε : ‖v‖ < ε := hv.trans_le (min_le_left _ _)
  have hvδ : ‖v‖ < δ := hv.trans_le (min_le_right _ _)
  have hφleft (q : ℝ × ℝ × ℝ) (hq : q ∈ U) : φ (q.1, q.2.1) = 1 :=
    φ.one_of_mem_closedBall (hleft q hq)
  have hφright (q : ℝ × ℝ × ℝ) (hq : q ∈ U) : φ (q.1, q.2.2) = 0 :=
    φ.zero_of_le_dist (hright q hq)
  refine ⟨v, hvε, contDiffOn_fst.prodMk (hc.sub (φ.contDiff.contDiffOn.smul contDiffOn_const)),
    hasCompactSupport_curve_perturbation_sub c φ.hasCompactSupport v, ?_, ?_,
    hδV v hvδ, ?_, ?_⟩
  · intro p hp
    rw [φ.zero_of_le_dist hp, zero_smul, sub_zero]
  · intro p
    have hnorm : ‖(c p - φ p • v) - c p‖ ≤ ‖v‖ := by
      rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg φ.nonneg]
      exact mul_le_of_le_one_left (norm_nonneg v) φ.le_one
    exact hnorm.trans_lt hvε
  · intro q hq
    apply surjective_fderiv_curve_perturbation_parameter
    rw [hφleft q hq, hφright q hq]
    exact one_ne_zero
  · intro q hq hcollision
    have heq : (fun r : ℝ × ℝ × ℝ =>
        (c (r.1, r.2.1) - φ (r.1, r.2.1) • v) -
        (c (r.1, r.2.2) - φ (r.1, r.2.2) • v)) =ᶠ[𝓝 q] fun r => f r - v := by
      filter_upwards [hU.mem_nhds hq] with r hr
      simp only [hφleft r hr, hφright r hr, one_smul, zero_smul, sub_zero, f]
      abel
    rw [heq.fderiv_eq, fderiv_sub_const]
    apply hreg q hq
    dsimp only [f]
    simp only [hφleft q hq, hφright q hq, one_smul, zero_smul, sub_zero] at hcollision
    exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hcollision).trans (add_comm _ _))

end DifferentialGeometry.Calculus

end

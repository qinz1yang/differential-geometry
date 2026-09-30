import DifferentialGeometry.Geometry.Metric.Approximation.RealSplitting
import DifferentialGeometry.Geometry.Metric.Approximation.PrescribedLowDimensionalModel
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Analysis.Normed.Affine.AddTorsor

set_option autoImplicit false
open Set Metric GC.MetricGeometry
open DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem real_comparison : fourPointComparison 0 (univ : Set ℝ) := by
  intro p _ a _ b _ c _ ha hb hc
  have hz {x y : ℝ} (hx : x ≠ p) (hy : y ≠ p)
      (hside : (x < p ∧ y < p) ∨ (p < x ∧ p < y)) :
      comparisonAngleNegCurvature 0 (dist p x) (dist p y) (dist x y) = 0 := by
    have hd : dist x y = |dist p x - dist p y| := by
      rcases hside with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rw [Real.dist_eq p x, Real.dist_eq p y,
          abs_of_pos (sub_pos.mpr hx), abs_of_pos (sub_pos.mpr hy), Real.dist_eq]
        have hh : p - x - (p - y) = -(x - y) := by ring
        rw [hh, abs_neg]
      · rw [Real.dist_eq p x, Real.dist_eq p y,
          abs_of_neg (sub_neg.mpr hx), abs_of_neg (sub_neg.mpr hy), Real.dist_eq]
        congr 1
        ring
    rw [hd]
    exact comparisonAngleNegCurvature_abs_sub le_rfl (dist_pos.mpr hx.symm) (dist_pos.mpr hy.symm)
  have hab := (comparisonAngleNegCurvature_mem_Icc 0 (dist p a) (dist p b) (dist a b)).2
  have hbc := (comparisonAngleNegCurvature_mem_Icc 0 (dist p b) (dist p c) (dist b c)).2
  have hca := (comparisonAngleNegCurvature_mem_Icc 0 (dist p c) (dist p a) (dist c a)).2
  rcases lt_or_gt_of_ne ha with ha' | ha' <;>
    rcases lt_or_gt_of_ne hb with hb' | hb' <;>
      rcases lt_or_gt_of_ne hc with hc' | hc'
  all_goals first
    | have hh := hz ha hb (Or.inl ⟨ha', hb'⟩); linarith
    | have hh := hz ha hb (Or.inr ⟨ha', hb'⟩); linarith
    | have hh := hz hb hc (Or.inl ⟨hb', hc'⟩); linarith
    | have hh := hz hb hc (Or.inr ⟨hb', hc'⟩); linarith
    | have hh := hz hc ha (Or.inl ⟨hc', ha'⟩); linarith
    | have hh := hz hc ha (Or.inr ⟨hc', ha'⟩); linarith

example : ∃ (W : Type) (mW : MetricSpace W), letI := mW
    ∃ q : W, CompleteSpace W ∧ ProperSpace W ∧ dimH (univ : Set W) ≤ 1 ∧
      ∃ G : KleinerLottApprox (0 : ℝ) (WithLp.toLp 2 ((0 : ℝ), q)) (1 / 100),
        ∀ x : ℝ, (G.toFun x).fst = x := by
  obtain ⟨a₀, ha, hasmall, hmodel⟩ :=
    exists_prescribed_one_dimensional_model_parameter.{0, 0, 0}
      (by norm_num : 0 < (1 / 100 : ℝ)) (by norm_num)
  have haone : a₀ < 1 := by linarith
  have hcurves := arbitrarily_short_curves_of_metric_segments (X := ℝ) (by
    intro x y
    refine ⟨fun t => AffineMap.lineMap x y (t : ℝ),
      AffineMap.lineMap_continuous.comp continuous_subtype_val, ?_, ?_, ?_⟩
    · exact AffineMap.lineMap_apply_zero x y
    · exact AffineMap.lineMap_apply_one x y
    · intro s t
      simpa only [Subtype.dist_eq, mul_comm] using dist_lineMap_lineMap x y (s : ℝ) (t : ℝ))
  let f := (IsometryEquiv.refl ℝ).toKleinerLottApprox (p := 0) rfl ha haone
  let F := (IsometryEquiv.withLpProdUnique 2 ℝ PUnit).symm.toKleinerLottApprox
    (p := 0) (q := WithLp.toLp 2 ((0 : ℝ), PUnit.unit)) rfl ha haone
  obtain ⟨W, mW, q, hp, hc, _, hd, _, G, hG⟩ :=
    hmodel ℝ 0 ℝ 0 hcurves (by rw [Real.dimH_univ]; norm_num) real_comparison
      PUnit PUnit.unit a₀ a₀ le_rfl le_rfl f F
  exact ⟨W, mW, q, hc, hp, hd, G, hG⟩

example : ∃ η : ℝ, 0 < η ∧ η < 1 / 10 ∧
    splittingRank.{0, 0} (0 : ℝ) (fun j => if j = 0 then 0 else if j = 1 then η / 2 else η) 2 = 1 ∧
      ¬ Nonempty (KleinerLottApprox (0 : ℝ) (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) η) := by
  obtain ⟨η, hη, hηsmall, hsep⟩ :=
    exists_no_higher_rank_splitting_parameter.{0, 0, 0} (by decide : 1 ≤ 1) (by decide : 1 < 2)
  have hηone : η < 1 := by linarith
  have hhalf : 0 < η / 2 := by positivity
  have hhalfone : η / 2 < 1 := by linarith
  have hcurves := arbitrarily_short_curves_of_metric_segments (X := ℝ) (by
    intro x y
    refine ⟨fun t => AffineMap.lineMap x y (t : ℝ),
      AffineMap.lineMap_continuous.comp continuous_subtype_val, ?_, ?_, ?_⟩
    · exact AffineMap.lineMap_apply_zero x y
    · exact AffineMap.lineMap_apply_one x y
    · intro s t
      simpa only [Subtype.dist_eq, mul_comm] using dist_lineMap_lineMap x y (s : ℝ) (t : ℝ))
  let f := (IsometryEquiv.refl ℝ).toKleinerLottApprox (p := 0) rfl hη hηone
  let F := (IsometryEquiv.withLpProdUnique 2 ℝ PUnit).symm.toKleinerLottApprox
    (p := 0) (q := WithLp.toLp 2 ((0 : ℝ), PUnit.unit)) rfl hhalf hhalfone
  have hone : HasEuclideanSplitting.{0, 0} (0 : ℝ) 1 (η / 2) :=
    hasEuclideanSplitting_one_iff.mpr ⟨PUnit, inferInstance, PUnit.unit, ⟨F⟩⟩
  have htwo : ¬ HasEuclideanSplitting.{0, 0} (0 : ℝ) 2 η := by
    rintro ⟨A, mA, a, ⟨G⟩⟩
    let := mA
    exact hsep ℝ 0 ℝ 0 hcurves (by rw [Real.dimH_univ]; norm_num) real_comparison
      A a η η le_rfl le_rfl f G
  have hrank : splittingRank.{0, 0} (0 : ℝ) (fun j => if j = 0 then 0 else if j = 1 then η / 2 else η) 2 = 1 := by
    apply (splittingRank_eq_iff (0 : ℝ) _ 2 1).mpr
    refine ⟨by decide, fun _ => ?_, ?_⟩
    · simpa only [Nat.one_ne_zero, ite_false, ite_true] using hone
    · intro j hj hjN
      have hjtwo : j = 2 := by omega
      subst j
      simpa only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ite_false] using htwo
  refine ⟨η, hη, hηsmall, hrank, ?_⟩
  simpa only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ite_false] using
    (splittingRank_one_real_model_and_no_plane (by decide) hrank).2

example : splittingRank.{0, 0} (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ)))
    (fun _ => 1 / 1000) 2 = 2 := by
  let p := WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))
  let F := (IsometryEquiv.refl (WithLp 2 (ℝ × ℝ))).toKleinerLottApprox (p := p) rfl
    (by norm_num : 0 < (1 / 1000 : ℝ)) (by norm_num)
  exact le_antisymm (splittingRank_le p _ 2)
    (le_splittingRank p _ (by decide) (hasEuclideanSplitting_two_of_plane_approximation F))

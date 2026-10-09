import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionNorm
import DifferentialGeometry.Geometry.Neck.InsertionInput
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem exists_normalizedDatum_insertedMetric_ball_error_bound
    (A : ℝ) (hA : 0 < A) (D : ℝ) (hD : 0 ≤ D) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ) (hAB : 2 * A < δ⁻¹), D + 1 < δ⁻¹ →
      ∀ k : ℕ, m ≤ k → ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M)
        (d : normalizedDatum g x₀ δ k),
        metricDerivENormSupOn {x : insertionBall δ⁻¹ | ‖(x : E3)‖ ≤ transitionEnd + D} m
          (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric)
          (metric.restrictOpen (insertionBall δ⁻¹)) (metric.restrictOpen (insertionBall δ⁻¹)) <
          ENNReal.ofReal (C * (δ + Real.sqrt δ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_insertedMetric_ball_error_bound A hA D hD m
  refine ⟨C, hC, ?_⟩
  intro δ hAB hDB k hmk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  have hin : metricDerivENormSupOn
      {q : openCylinder δ⁻¹ | q.val.2 ∈ Icc (-2 * A) D} m d.controlledMetric
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹))
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹)) < ENNReal.ofReal δ :=
    (metricDerivENormSupOn_mono (subset_univ _) hmk _ _ _).trans_lt d.controlledMetric_error_lt
  have habs : |1 - Real.sqrt δ - 1| = Real.sqrt δ := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (hbound δ⁻¹ hAB hDB (1 - Real.sqrt δ) d.controlledMetric_cylinder_lower.1 d.controlledMetric).trans_lt
  rw [habs]
  have hsum := ENNReal.add_lt_add_right (a := ENNReal.ofReal (Real.sqrt δ)) ENNReal.ofReal_ne_top hin
  have hmul := ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) ENNReal.ofReal_ne_top hsum
  apply hmul.trans_eq
  rw [← ENNReal.ofReal_add d.precision_pos.le (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul hC.le]

private theorem exists_pos_precision_for_bound
    (A : ℝ) (hA : 0 < A) (D : ℝ) (hD : 0 ≤ D) (C : ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      2 * A < δ⁻¹ ∧ D + 1 < δ⁻¹ ∧ C * (δ + Real.sqrt δ) < ε := by
  have hc : Continuous (fun δ : ℝ => C * (δ + Real.sqrt δ)) := by fun_prop
  have he : ∀ᶠ δ : ℝ in 𝓝 0, C * (δ + Real.sqrt δ) < ε :=
    hc.continuousAt.eventually_lt_const (by simpa using hε)
  obtain ⟨r, hr, hrr⟩ := Metric.eventually_nhds_iff.mp he
  let T := 2 * A + D + 2
  have hT : 0 < T := by dsimp [T]; linarith
  let δ₀ := min (r / 2) (min (1 / 4 : ℝ) (1 / (2 * T)))
  have hδ₀ : 0 < δ₀ := lt_min (half_pos hr) (lt_min (by norm_num) (by positivity))
  have hquarter : δ₀ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨δ₀, hδ₀, hquarter.trans_lt (by norm_num), ?_⟩
  intro δ hδ hδle
  have hδT : δ ≤ 1 / (2 * T) := hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hprod : T * δ < 1 := by
    have h := mul_le_mul_of_nonneg_left hδT hT.le
    have heq : T * (1 / (2 * T)) = 1 / 2 := by field_simp
    rw [heq] at h
    linarith
  have hfit : T < δ⁻¹ := by
    rw [inv_eq_one_div]
    exact (lt_div_iff₀ hδ).mpr hprod
  refine ⟨(show 2 * A < T by dsimp [T]; linarith).trans hfit,
    (show D + 1 < T by dsimp [T]; linarith).trans hfit, ?_⟩
  apply hrr
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hδ]
  exact (hδle.trans (min_le_left _ _)).trans_lt (half_lt_self hr)

theorem exists_normalizedDatum_insertedMetric_ball_error_lt
    (A : ℝ) (hA : 0 < A) (D : ℝ) (hD : 0 ≤ D) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ hAB : 2 * A < δ⁻¹, D + 1 < δ⁻¹ ∧ ∀ k : ℕ, m ≤ k →
        ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k),
        metricDerivENormSupOn {x : insertionBall δ⁻¹ | ‖(x : E3)‖ ≤ transitionEnd + D} m
          (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric)
          (metric.restrictOpen (insertionBall δ⁻¹)) (metric.restrictOpen (insertionBall δ⁻¹)) <
          ENNReal.ofReal ε := by
  obtain ⟨C, hC, hb⟩ := exists_normalizedDatum_insertedMetric_ball_error_bound A hA D hD m
  obtain ⟨δ₀, hδ₀, hδ₀half, hmod⟩ := exists_pos_precision_for_bound A hA D hD C ε hε
  refine ⟨δ₀, hδ₀, hδ₀half, ?_⟩
  intro δ hδ hδle
  obtain ⟨hAB, hDB, herr⟩ := hmod δ hδ hδle
  refine ⟨hAB, hDB, ?_⟩
  intro k hmk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  exact (hb δ hAB hDB k hmk g x₀ d).trans
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr herr)

end DifferentialGeometry.PDE.RicciFlow.StandardCap

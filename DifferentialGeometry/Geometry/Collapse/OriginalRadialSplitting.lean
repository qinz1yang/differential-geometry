import DifferentialGeometry.Geometry.Metric.Approximation.OriginalRadialSplitting
import DifferentialGeometry.Geometry.Collapse.CompleteRiemannianSegments
import DifferentialGeometry.Geometry.Comparison.RiemannianFourPoint
import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianHausdorffVolume

/-!
# Original radial splitting on complete Riemannian manifolds

The LC70 binding discharges dimension by finite Riemannian volume on a compact exhaustion.
No compactness of the whole manifold or replacement of its original radial function is used.
-/

set_option autoImplicit false

open Set Metric Bundle Manifold MeasureTheory
open DifferentialGeometry
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u v uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem dimH_univ_le_finrank_of_riemannian_distance
    {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) :
    dimH (univ : Set M) ≤ Module.finrank ℝ E := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : IsRiemannianManifold I M := ⟨fun a b => by
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]⟩
  have hEnorm : IsMetricNorm (I := I) g := isMetricNorm_of_riemannianBundle g
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  have hmeasure := normalizedHausdorffMeasure_eq_riemannianVolumeMeasure g hEnorm
  let := riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) g
  have hdim (j : ℕ) : dimH (compactCovering M j) ≤ Module.finrank ℝ E := by
    have hne : (normalizedHausdorffMeasure (Module.finrank ℝ E) : Measure M)
        (compactCovering M j) ≠ ⊤ := by
      rw [hmeasure]
      exact (isCompact_compactCovering M j).measure_lt_top.ne
    have hμ : μH[(Module.finrank ℝ E : ℝ)] (compactCovering M j) ≠ ⊤ := by
      intro htop
      apply hne
      simp only [normalizedHausdorffMeasure, Measure.smul_apply]
      rw [htop]
      exact ENNReal.mul_top (by exact_mod_cast (euclideanHausdorffFactor_pos _).ne')
    have hd := dimH_le_of_hausdorffMeasure_ne_top (d := (Module.finrank ℝ E : NNReal))
      (s := compactCovering M j) (by simpa only [NNReal.coe_natCast] using hμ)
    simpa only [ENNReal.coe_natCast] using hd
  rw [← iUnion_compactCovering M, dimH_iUnion]
  exact iSup_le hdim

theorem exists_original_radial_splitting_parameter_riemannian
    {β : ℝ} (hβ : 0 < β) (hβone : β < 1) :
    ∃ δstar Λstar : ℝ, 0 < δstar ∧ 0 < Λstar ∧
      ∀ (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M] [ConnectedSpace M]
        (g : SmoothRiemannianMetric I M),
      (∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) → ∀ p : M,
      (∀ y ∈ ball p 400, SectionalBoundedBelowAt g y (-((1 / 60) ^ 2))) →
      ∀ (C : Type v) [MetricSpace C] (o : C), RadialConeData o →
      ∀ {δ : ℝ}, KleinerLottApprox p o δ → δ < δstar →
      ∀ q : M, 1 / 10 ≤ dist p q → dist p q ≤ 10 →
      ∀ (lam : ℝ) (hlam : 0 < lam), Λstar ≤ lam →
      ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
        ∃ (z : Z) (F : @KleinerLottApprox M
          (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z)) (m.rescale lam hlam)
          inferInstance q (WithLp.toLp 2 (0, z)) β),
          ∀ x : M, (@KleinerLottApprox.toFun M
            (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z)) (m.rescale lam hlam)
            inferInstance q (WithLp.toLp 2 (0, z)) β F x).fst = WithLp.toLp 2
            (Function.const (Fin 1) (lam * (dist p x - dist p q))) := by
  have hn : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  obtain ⟨δstar, Λstar, hδstar, hΛstar, hproduce⟩ :=
    exists_original_radial_splitting_parameter.{u, v} hn hβ hβone
  refine ⟨δstar, Λstar, hδstar, hΛstar, ?_⟩
  intro M m hcharts hmanifold hsigma hcomplete hconnected g hmetric p hsec C mC o H δ F hδ
    q hqlo hqhi lam hlam hΛ
  apply hproduce M
    (DifferentialGeometry.Geometry.Collapse.segments_of_riemannianEDistOf_eq g hmetric)
    (dimH_univ_le_finrank_of_riemannian_distance g hmetric) C p o H F hδ
  · apply fourPointComparison_of_sectional_lower_bound_on_eight_ball g hmetric p
      (by positivity)
    intro y hy
    exact hsec y (by change dist y p < 400; change dist y p < 8 * 21 at hy; linarith)
  · exact hqlo
  · exact hqhi
  · exact hΛ

end GC.MetricGeometry

import DifferentialGeometry.Geometry.Comparison.Volume.ScaledBallComparison
import DifferentialGeometry.Geometry.Metric.LipschitzScaleMultiplicity

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [ConnectedSpace M] [CompactSpace M]

open _root_.Metric DifferentialGeometry.Integral.Measure

theorem exists_finite_scale_cover_of_ricci_bound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (S : Set M) {ρ : M → ℝ} {Λ : NNReal} {Δ C q : ℝ}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ p, 0 < ρ p)
    (hΔ : 0 < Δ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hselection : (Λ : ℝ) * Δ ≤ 1 / 100) (hoverlap : (Λ : ℝ) * C ≤ 1 / 4)
    (hRic : ∀ p ∈ S, ricciBoundedBelowOn (I := I) g
      (ball p ((3 * C + 2 * (Δ / 3)) * ρ p))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((q / ρ p) ^ 2)))) :
    ∃ J : Set M, J ⊆ S ∧ J.Finite ∧ J.PairwiseDisjoint (fun p => ball p (Δ * ρ p / 3)) ∧
      (∀ p ∈ S, ∃ i ∈ J, ball p (Δ * ρ p) ⊆ ball i (2 * Δ * ρ i)) ∧
      ∀ x : M, ((J ∩ {i | x ∈ ball i (C * ρ i)}).ncard : ℝ) ≤
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (3 * C + 2 * (Δ / 3)) /
          modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (Δ / 3) := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  let : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  let D := 3 * C + 2 * (Δ / 3)
  have hs : 0 < Δ / 3 := by positivity
  have hsD : Δ / 3 ≤ D := by dsimp only [D]; linarith
  have hn : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hm (t : ℝ) (ht : 0 < t) : 0 < modelVolume (-(q ^ 2)) (Module.finrank ℝ E) t :=
    modelVolume_pos hn ht ⟨ht.le, fun h => (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg _)) h).elim⟩
  have hball (p : M) (r : ℝ) :
      {y : M | riemannianEDist I p y < ENNReal.ofReal r} = ball p r := by
    ext y
    rw [mem_ofPred_eq, ← IsRiemannianManifold.out (I := I), edist_lt_ofReal]
    exact dist_comm p y ▸ Iff.rfl
  apply GC.MetricGeometry.exists_finite_scale_cover_with_multiplicity μ S hρ hρpos hΔ hC
    (div_nonneg (hm D (hs.trans_le hsD)).le (hm _ hs).le) hselection hoverlap
  · intro p _
    exact ENNReal.toReal_pos (measure_ball_pos μ p (div_pos (mul_pos hΔ (hρpos p)) (by norm_num))).ne' (measure_ne_top μ _)
  · intro p _
    exact measure_ne_top μ _
  · intro p hp
    have hric := hRic p hp
    rw [← hball p (D * ρ p)] at hric
    have hc := ballVolume_mul_scale_le_model_ratio g hEnorm p hq (hρpos p) hs hsD hric
    have hv (r : ℝ) : ballVolume g p r = μ (ball p r) := by
      simp only [ballVolume, μ, hball]
    rw [hv, hv] at hc
    have hc' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)) hc
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (div_nonneg (hm D (hs.trans_le hsD)).le (hm _ hs).le)] at hc'
    have hid : (Δ / 3) * ρ p = Δ * ρ p / 3 := by ring
    simpa only [hid, D, Measure.real] using hc'

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

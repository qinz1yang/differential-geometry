import DifferentialGeometry.Geometry.Comparison.Volume.Ball.Basic
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open scoped Topology Manifold ContDiff Bundle

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Integral.Measure
open Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section BallUpper

variable [I.Boundaryless] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pair_rrm1_ge
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ C κ Blo : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < Blo ∧ ∀ {Rm A Bhi R s : ℝ},
      0 ≤ Bhi → 0 ≤ Rm →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      C * R < ρ →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2 ≤ κ →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) * A) 1 ≤ Bhi →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, C, hρ, hC, hvol⟩ := exists_pair_rglobal1 (I := I) (M := M) g hEnorm p
  obtain ⟨κ, Blo, hκ, lowerBound_nonneg, lowerComparison⟩ := exists_dirModel_ge1 (I := I) g p
  refine ⟨ρ, C, κ, Blo, hρ, hC, hκ, lowerBound_nonneg, ?_⟩
  intro Rm A Bhi R s upperBound_nonneg curvatureBound_nonneg domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius hCRρ tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius
    hKcap hRmGlobal hbasis upperComparison
  have hK_nonneg :
      0 ≤ Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2 := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) curvatureBound_nonneg) (sq_nonneg (C * R))
  exact hvol (Rm := Rm) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R) (s := s)
    lowerBound_nonneg.le upperBound_nonneg curvatureBound_nonneg domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius hCRρ tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius
    hRmGlobal hbasis upperComparison (lowerComparison hK_nonneg hKcap)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pair_rrm1
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ C κ Blo : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < κ ∧ 0 < Blo ∧ ∀ {Rm A R s : ℝ},
      0 ≤ Rm →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      C * R < ρ →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2 ≤ κ →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      let Bhi : ℝ :=
        max
          (A + gronwallBound 0
            (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
              Rm * (C * R) ^ 2) 1)
            ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
              Rm * (C * R) ^ 2) * A) 1)
          0
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, C, κ, Blo, hρ, hC, hκ, lowerBound_nonneg, hvol⟩ :=
    exists_pair_rrm1_ge (I := I) (M := M) g hEnorm p
  refine ⟨ρ, C, κ, Blo, hρ, hC, hκ, lowerBound_nonneg, ?_⟩
  intro Rm A R s curvatureBound_nonneg domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius hCRρ tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius hKcap
    hRmGlobal hbasis
  let Bhi : ℝ :=
    max
      (A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) * A) 1)
      0
  have upperBound_nonneg : 0 ≤ Bhi := by
    dsimp [Bhi]
    exact le_max_right _ _
  have upperComparison :
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) * A) 1 ≤ Bhi := by
    dsimp [Bhi]
    exact le_max_left _ _
  exact hvol (Rm := Rm) (A := A) (Bhi := Bhi) (R := R) (s := s) upperBound_nonneg
    curvatureBound_nonneg domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius hCRρ tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius hKcap hRmGlobal hbasis
    upperComparison

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_pair_coeff
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm b A Blo Bhi R s : ℝ},
      0 ≤ Blo → 0 ≤ Bhi → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
              (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
                  (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_pair_launch (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm b A Blo Bhi R s lowerBound_nonneg upperBound_nonneg curvatureBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius
    tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius curvature_norm_le hbasis upperComparison lowerComparison
  let K : ℝ :=
    Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) * Rm * ρ ^ 2
  have growthBound_nonneg : 0 ≤ K := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) curvatureBound_nonneg) (sq_nonneg ρ)
  have jacobiCoefficient_le :
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ K := by
    rfl
  exact hvol (K := K) (Rm := Rm) (b := b) (A := A) (Blo := Blo) (Bhi := Bhi)
    (R := R) (s := s) lowerBound_nonneg upperBound_nonneg growthBound_nonneg curvatureBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius
    tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius jacobiCoefficient_le curvature_norm_le hbasis (by simpa [K] using upperComparison)
    (by simpa [K] using lowerComparison)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_pair_regionRm
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm b A Blo Bhi R s : ℝ} {U : Set M},
      0 ≤ Blo → 0 ≤ Bhi → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        radialCurve (I := I) g p w t ∈ U) →
      (∀ q ∈ U,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
              (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
                  (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_pair_coeff (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm b A Blo Bhi R s U lowerBound_nonneg upperBound_nonneg curvatureBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt
    geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius hcurve hRmU hbasis upperComparison lowerComparison
  refine hvol (Rm := Rm) (b := b) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R)
    (s := s) lowerBound_nonneg upperBound_nonneg curvatureBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius
    geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius ?_ hbasis upperComparison lowerComparison
  intro w hw t ht
  exact hRmU (radialCurve (I := I) g p w t) (hcurve w hw t ht)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_pair_globalRm
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm b A Blo Bhi R s : ℝ},
      0 ≤ Blo → 0 ≤ Bhi → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
              (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
                  (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_pair_regionRm (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm b A Blo Bhi R s lowerBound_nonneg upperBound_nonneg curvatureBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt
    geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius hRmGlobal hbasis upperComparison lowerComparison
  exact hvol (Rm := Rm) (b := b) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R)
    (s := s) (U := Set.univ) lowerBound_nonneg upperBound_nonneg curvatureBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius
    tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius (fun _ _ _ _ => Set.mem_univ _) (fun q _ => hRmGlobal q)
    hbasis upperComparison lowerComparison

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_pair_globalRm1
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm A Blo Bhi R s : ℝ},
      0 ≤ Blo → 0 ≤ Bhi → 0 ≤ Rm →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
              (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * Real.sqrt
                (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
                  (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_pair_globalRm (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm A Blo Bhi R s lowerBound_nonneg upperBound_nonneg curvatureBound_nonneg domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius
    normalizedGeodesicRadius_lt_domainRadius hRmGlobal hbasis upperComparison lowerComparison
  exact hvol (Rm := Rm) (b := 1) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R) (s := s)
    lowerBound_nonneg upperBound_nonneg curvatureBound_nonneg zero_le_one le_rfl le_rfl domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt
    geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius hRmGlobal hbasis (by simpa [one_mul] using upperComparison)
    (fun v hv => by simpa [one_mul] using lowerComparison v hv)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_pair_rm1_ge
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ κ Blo : ℝ, 0 < ρ ∧ 0 < κ ∧ 0 < Blo ∧ ∀ {Rm A Bhi R s : ℝ},
      0 ≤ Bhi → 0 ≤ Rm →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ κ →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1 ≤ Bhi →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_pair_globalRm1 (I := I) (M := M) g hEnorm p
  obtain ⟨κ, Blo, hκ, lowerBound_nonneg, lowerComparison⟩ := exists_dirModel_ge1 (I := I) g p
  refine ⟨ρ, κ, Blo, hρ, hκ, lowerBound_nonneg, ?_⟩
  intro Rm A Bhi R s upperBound_nonneg curvatureBound_nonneg domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius
    hKcap hRmGlobal hbasis upperComparison
  have hK_nonneg :
      0 ≤ Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) curvatureBound_nonneg) (sq_nonneg ρ)
  exact hvol (Rm := Rm) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R) (s := s)
    lowerBound_nonneg.le upperBound_nonneg curvatureBound_nonneg domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius
    hRmGlobal hbasis upperComparison (lowerComparison hK_nonneg hKcap)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_pair_rm1_auto
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ κ Blo : ℝ, 0 < ρ ∧ 0 < κ ∧ 0 < Blo ∧ ∀ {Rm A R s : ℝ},
      0 ≤ Rm →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ κ →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      let Bhi : ℝ :=
        max
          (A + gronwallBound 0
            (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
              Rm * ρ ^ 2) 1)
            ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
              Rm * ρ ^ 2) * A) 1)
          0
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (Bhi * Bhi) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, κ, Blo, hρ, hκ, lowerBound_nonneg, hvol⟩ :=
    exists_vol_pair_rm1_ge (I := I) (M := M) g hEnorm p
  refine ⟨ρ, κ, Blo, hρ, hκ, lowerBound_nonneg, ?_⟩
  intro Rm A R s curvatureBound_nonneg domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius hKcap
    hRmGlobal hbasis
  let Bhi : ℝ :=
    max
      (A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1)
      0
  have upperBound_nonneg : 0 ≤ Bhi := by
    dsimp [Bhi]
    exact le_max_right _ _
  have upperComparison :
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1 ≤ Bhi := by
    dsimp [Bhi]
    exact le_max_left _ _
  exact hvol (Rm := Rm) (A := A) (Bhi := Bhi) (R := R) (s := s) upperBound_nonneg
    curvatureBound_nonneg domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius hKcap hRmGlobal hbasis
    upperComparison

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_two_rm04
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {a K Rm Vb b A B R s : ℝ},
      0 ≤ B → 0 < a → 0 ≤ K → 0 ≤ Rm → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R →
      R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k‖ < ρ) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)‖ < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb) →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * Vb ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ w ∈ Metric.ball (0 : E) R,
        ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p w)) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p w t))) →
      (F : ∀ w : E, ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p w t)) →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p w) (F w i) t = 0) →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p w t) (F w i t) (F w j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p w) (F w i) t) t) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p (a • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) (a • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a * B ≤ Real.sqrt
            (g.inner p (a • (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
              (a • (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (a • (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
                  (a • (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, h⟩ := exists_vol_two_rm04_at (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro a K Rm Vb b A B R s bound_nonneg scale_pos growthBound_nonneg curvatureBound_nonneg speedBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius
    domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius scaledBasis_mem_chartRadius scaledUnitDirection_mem_chartRadius radialSpeed_le jacobiCoefficient_le curvature_norm_le radialCurve_contMDiffAt
    ι _ _ _ frame_cardinality F frame_parallel frame_orthonormal frameRepresentation_differentiable initialFrame_norm_le upperComparison lowerComparison
  exact h bound_nonneg scale_pos growthBound_nonneg curvatureBound_nonneg speedBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt
    geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius scaledBasis_mem_chartRadius scaledUnitDirection_mem_chartRadius radialSpeed_le jacobiCoefficient_le curvature_norm_le
    (fun w hw _ _ => (radialCurve_contMDiffAt w hw).contMDiffAt) frame_cardinality F frame_parallel frame_orthonormal frameRepresentation_differentiable
    initialFrame_norm_le upperComparison lowerComparison

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_volume_bounds_of_radialComparison
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {a K Rm Vb b A B R s : ℝ},
      (D : RadialFrameFamily (I := I) g p R b) →
      RadialVolumeComparisonBounds (I := I) g p D ρ a K Rm Vb A B s →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_two_rm04_at (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro a K Rm Vb b A B R s D H
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let : Fintype D.ι := D.fintype
  let : DecidableEq D.ι := D.decidableEq
  let : Nonempty D.ι := D.nonempty
  exact hvol H.bound_nonneg H.scale_pos H.growthBound_nonneg H.curvatureBound_nonneg H.speedBound_nonneg H.time_nonneg H.time_le_one H.one_le_time
    H.domainRadius_pos H.domainRadius_le_chartRadius H.domainRadius_le_expMapC2Radius H.tangentBall_metricRadius_lt H.tangentBall_geodesicRadius_lt H.geodesicRadius_lt_domainRadius H.geodesicRadius_lt_chartRadius H.normalizedGeodesicRadius_lt_domainRadius
    H.scaledBasis_mem_chartRadius H.scaledUnitDirection_mem_chartRadius H.radialSpeed_le H.jacobiCoefficient_le H.curvature_norm_le H.radialCurve_contMDiffAt
    H.frame_cardinality D.frame H.frame_parallel H.frame_orthonormal H.frameRepresentation_differentiable H.initialFrame_norm_le H.upperComparison H.lowerComparison

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_scale
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {K Rm Vb b A B R s : ℝ},
      (D : RadialFrameFamily (I := I) g p R b) →
      (∀ a : ℝ, 0 < a →
        (∀ k : Fin (Module.finrank ℝ E), ‖a • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k‖ < ρ) →
        (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
          ‖a • (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)‖ < ρ) →
        RadialVolumeComparisonBounds (I := I) g p D ρ a K Rm Vb A B s) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_volume_bounds_of_radialComparison (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro K Rm Vb b A B R s D H
  obtain ⟨a, Ha⟩ := exists_rm04_scale (I := I) g p D hρ H
  exact hvol D Ha

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_scalar
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {K Rm Vb b A B R s : ℝ},
      0 ≤ B → 0 ≤ K → 0 ≤ Rm → 0 ≤ Vb →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb) →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * Vb ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
              (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
                  (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_volume_bounds_of_radialComparison.{_, _, _, 0} (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro K Rm Vb b A B R s bound_nonneg growthBound_nonneg curvatureBound_nonneg speedBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius
    domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius radialSpeed_le jacobiCoefficient_le curvature_norm_le hbasis upperComparison lowerComparison
  obtain ⟨a, scale_pos, scaledBasis_mem_chartRadius, scaledUnitDirection_mem_chartRadius⟩ := basisUnitScaleSmall (E := E) hρ
  obtain ⟨D, H⟩ :=
    exists_rm04_scalar.{_, _, _, 0} (I := I) g p bound_nonneg scale_pos growthBound_nonneg curvatureBound_nonneg speedBound_nonneg time_nonneg time_le_one one_le_time
      domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius scaledBasis_mem_chartRadius scaledUnitDirection_mem_chartRadius radialSpeed_le
      jacobiCoefficient_le curvature_norm_le hbasis upperComparison lowerComparison
  exact hvol D H

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_launch
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {K Rm b A B R s : ℝ},
      0 ≤ B → 0 ≤ K → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
              (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
                  (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_scalar (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro K Rm b A B R s bound_nonneg growthBound_nonneg curvatureBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius
    tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius jacobiCoefficient_le curvature_norm_le hbasis upperComparison lowerComparison
  let Vb : ℝ := ρ
  have speedBound_nonneg : 0 ≤ Vb := by
    exact hρ.le
  have radialSpeed_le : ∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb := by
    intro w hw
    exact le_of_lt (by simpa [Vb] using tangentBall_metricRadius_lt w hw)
  exact hvol (K := K) (Rm := Rm) (Vb := Vb) (b := b) (A := A) (B := B)
    (R := R) (s := s) bound_nonneg growthBound_nonneg curvatureBound_nonneg speedBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius
    tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius radialSpeed_le (by simpa [Vb] using jacobiCoefficient_le) curvature_norm_le hbasis
    upperComparison lowerComparison

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_coeff
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm b A B R s : ℝ},
      0 ≤ B → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
              (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
                  (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_launch (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm b A B R s bound_nonneg curvatureBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt
    geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius curvature_norm_le hbasis upperComparison lowerComparison
  let K : ℝ :=
    Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) * Rm * ρ ^ 2
  have growthBound_nonneg : 0 ≤ K := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) curvatureBound_nonneg) (sq_nonneg ρ)
  have jacobiCoefficient_le :
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ K := by
    rfl
  exact hvol (K := K) (Rm := Rm) (b := b) (A := A) (B := B) (R := R) (s := s)
    bound_nonneg growthBound_nonneg curvatureBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius
    jacobiCoefficient_le curvature_norm_le hbasis (by simpa [K] using upperComparison)
    (by simpa [K] using lowerComparison)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_regionRm
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm b A B R s : ℝ} {U : Set M},
      0 ≤ B → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        radialCurve (I := I) g p w t ∈ U) →
      (∀ q ∈ U,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
              (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
                  (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_coeff (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm b A B R s U bound_nonneg curvatureBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt
    geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius hcurve hRmU hbasis upperComparison lowerComparison
  refine hvol (Rm := Rm) (b := b) (A := A) (B := B) (R := R) (s := s)
    bound_nonneg curvatureBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius ?_
    hbasis upperComparison lowerComparison
  intro w hw t ht
  exact hRmU (radialCurve (I := I) g p w t) (hcurve w hw t ht)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_globalRm
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm b A B R s : ℝ},
      0 ≤ B → 0 ≤ Rm →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
              (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
                  (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_regionRm (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm b A B R s bound_nonneg curvatureBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt
    geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius hRmGlobal hbasis upperComparison lowerComparison
  exact hvol (Rm := Rm) (b := b) (A := A) (B := B) (R := R) (s := s)
    (U := Set.univ) bound_nonneg curvatureBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt
    geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius (fun _ _ _ _ => Set.mem_univ _) (fun q _ => hRmGlobal q)
    hbasis upperComparison lowerComparison

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_globalRm1
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {Rm A B R s : ℝ},
      0 ≤ B → 0 ≤ Rm →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
              (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * Real.sqrt
                (g.inner p (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
                  (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))) 1) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_globalRm (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro Rm A B R s bound_nonneg curvatureBound_nonneg domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius
    hRmGlobal hbasis upperComparison lowerComparison
  exact hvol (Rm := Rm) (b := 1) (A := A) (B := B) (R := R) (s := s)
    bound_nonneg curvatureBound_nonneg (by norm_num) (by norm_num) (by norm_num) domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius
    tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius hRmGlobal hbasis
    (by simpa [one_mul] using upperComparison)
    (by
      intro v hv
      simpa [one_mul] using lowerComparison v hv)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_rm1_ge
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ κ B : ℝ, 0 < ρ ∧ 0 < κ ∧ 0 < B ∧ ∀ {Rm A R s : ℝ},
      0 ≤ Rm →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ κ →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1 ≤ B →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_globalRm1 (I := I) (M := M) g hEnorm p
  obtain ⟨κ, B, hκ, hB, lowerComparison⟩ := exists_dirModel_ge1 (I := I) g p
  refine ⟨ρ, κ, B, hρ, hκ, hB, ?_⟩
  intro Rm A R s curvatureBound_nonneg domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius hKcap
    hRmGlobal hbasis upperComparison
  have hK_nonneg :
      0 ≤ Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) curvatureBound_nonneg) (sq_nonneg ρ)
  exact hvol (Rm := Rm) (A := A) (B := B) (R := R) (s := s) hB.le curvatureBound_nonneg
    domainRadius_pos domainRadius_le_chartRadius domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius hRmGlobal hbasis upperComparison
    (lowerComparison hK_nonneg hKcap)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_frame
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {K Rm Vb b A B R s : ℝ},
      0 ≤ B → 0 ≤ K → 0 ≤ Rm → 0 ≤ Vb →
      0 ≤ b → b ≤ 1 → (1 : ℝ) ≤ b →
      0 < R → R ≤ ρ →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb) →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * Vb ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ a : ℝ, 0 < a →
        (∀ k : Fin (Module.finrank ℝ E), ‖a • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k‖ < ρ) →
        (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
          ‖a • (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)‖ < ρ) →
        (∀ k : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner p (a • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) (a • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) ≤ A) ∧
        A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B ∧
        (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
          a * B ≤ Real.sqrt
              (g.inner p (a • (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
                (a • (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))) -
              gronwallBound 0 (max K 1)
                (K * (b * Real.sqrt
                  (g.inner p (a • (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
                    (a • (∑ i, v i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))))) 1)) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (Real.sqrt ((B ^ 2) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
          (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
            (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_scale.{_, _, _, 0} (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro K Rm Vb b A B R s bound_nonneg growthBound_nonneg curvatureBound_nonneg speedBound_nonneg time_nonneg time_le_one one_le_time domainRadius_pos domainRadius_le_chartRadius
    domainRadius_le_expMapC2Radius tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius radialSpeed_le jacobiCoefficient_le curvature_norm_le hscalar
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one one_le_time
  obtain ⟨D, frame_cardinality, frame_parallel, frame_orthonormal, frameRepresentation_differentiable⟩ :=
    exists_radialFrameFamily_of_radius_le_expMapC2Radius.{_, _, _, 0} (I := I) g p hb time_le_one domainRadius_le_expMapC2Radius
  refine hvol (K := K) (Rm := Rm) (Vb := Vb) (b := b) (A := A)
    (B := B) (R := R) (s := s) D ?_
  intro a scale_pos scaledBasis_mem_chartRadius scaledUnitDirection_mem_chartRadius
  obtain ⟨initialFrame_norm_le, upperComparison, lowerComparison⟩ := hscalar a scale_pos scaledBasis_mem_chartRadius scaledUnitDirection_mem_chartRadius
  exact {
    bound_nonneg := bound_nonneg
    scale_pos := scale_pos
    growthBound_nonneg := growthBound_nonneg
    curvatureBound_nonneg := curvatureBound_nonneg
    speedBound_nonneg := speedBound_nonneg
    time_nonneg := time_nonneg
    time_le_one := time_le_one
    one_le_time := one_le_time
    domainRadius_pos := domainRadius_pos
    domainRadius_le_chartRadius := domainRadius_le_chartRadius
    domainRadius_le_expMapC2Radius := domainRadius_le_expMapC2Radius
    tangentBall_metricRadius_lt := tangentBall_metricRadius_lt
    tangentBall_geodesicRadius_lt := tangentBall_geodesicRadius_lt
    geodesicRadius_lt_domainRadius := geodesicRadius_lt_domainRadius
    geodesicRadius_lt_chartRadius := geodesicRadius_lt_chartRadius
    normalizedGeodesicRadius_lt_domainRadius := normalizedGeodesicRadius_lt_domainRadius
    scaledBasis_mem_chartRadius := scaledBasis_mem_chartRadius
    scaledUnitDirection_mem_chartRadius := scaledUnitDirection_mem_chartRadius
    radialSpeed_le := radialSpeed_le
    jacobiCoefficient_le := jacobiCoefficient_le
    curvature_norm_le := curvature_norm_le
    radialCurve_contMDiffAt := radialC1AtBall (I := I) g p domainRadius_le_expMapC2Radius time_le_one
    frame_cardinality := frame_cardinality
    frame_parallel := frame_parallel
    frame_orthonormal := frame_orthonormal
    frameRepresentation_differentiable := frameRepresentation_differentiable
    initialFrame_norm_le := initialFrame_norm_le
    upperComparison := upperComparison
    lowerComparison := lowerComparison }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_metricBall_vol_two_local
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {c B Rlo Rup s : ℝ},
      0 ≤ B →
      0 < Rlo →
      0 < Rup →
      Rlo ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) Rlo,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) Rlo,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      (∀ w ∈ Metric.ball (0 : E) Rlo,
        c ≤ normalChartDensity (I := I) g p w) →
      s < Rup →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < Rup →
      Rup ≤ expMapC2Radius (I := I) g p →
      (letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
       MeasurableSet (Metric.ball p s)) →
      (∀ w ∈ Metric.ball (0 : E) Rup,
        ∀ i : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
            (radialJacobiField (I := I) g p w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) 1)
            (radialJacobiField (I := I) g p w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) 1)) ≤ B) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal c *
          (ENNReal.ofReal (Rlo ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
            (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
              (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (Rup ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρlo, hρlo_pos, hlower⟩ := exists_metricBall_vol_ge_sc_local (I := I) g hEnorm p
  obtain ⟨ρup, hρup_pos, hupper⟩ := exists_metricBall_vol_scale_local (I := I) (M := M) g hEnorm p
  refine ⟨min ρlo ρup, lt_min hρlo_pos hρup_pos, ?_⟩
  intro c B Rlo Rup s hB hRlo_pos hRup_pos hRlo hρlo_ball tangentBall_geodesicRadius_lt hdens
    hsRup geodesicRadius_lt_chartRadius hs_div_Rup hRup hmeas hJ
  let : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hρlo_ball' : ∀ w ∈ Metric.ball (0 : E) Rlo,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρlo :=
    fun w hw => lt_of_lt_of_le (hρlo_ball w hw) (min_le_left _ _)
  have geodesicRadius_lt_chartRadiusup : s < ρup := lt_of_lt_of_le geodesicRadius_lt_chartRadius (min_le_right _ _)
  exact ⟨
    hlower hRlo_pos hRlo hρlo_ball' tangentBall_geodesicRadius_lt hdens,
    hupper hB hRup_pos hsRup geodesicRadius_lt_chartRadiusup hs_div_Rup hRup hmeas hJ⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_two_same
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {c B R s : ℝ},
      0 ≤ B →
      0 < R →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      (∀ w ∈ Metric.ball (0 : E) R,
        c ≤ normalChartDensity (I := I) g p w) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      (letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
       MeasurableSet (Metric.ball p s)) →
      (∀ w ∈ Metric.ball (0 : E) R,
        ∀ i : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
            (radialJacobiField (I := I) g p w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) 1)
            (radialJacobiField (I := I) g p w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) 1)) ≤ B) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal c *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
            (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
              (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρpos, htwo⟩ := exists_metricBall_vol_two_local (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρpos, ?_⟩
  intro c B R s hB domainRadius_pos hR tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt hdens geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius hmeas hJ
  exact htwo hB domainRadius_pos domainRadius_pos hR tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt hdens geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius hR hmeas hJ

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_vol_two_meas
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {c B R s : ℝ},
      0 ≤ B →
      0 < R →
      R ≤ expMapC2Radius (I := I) g p →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρ) →
      (∀ w ∈ Metric.ball (0 : E) R,
        Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < s) →
      (∀ w ∈ Metric.ball (0 : E) R,
        c ≤ normalChartDensity (I := I) g p w) →
      s < R →
      s < ρ →
      s / Real.sqrt (metricCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R,
        ∀ i : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
            (radialJacobiField (I := I) g p w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) 1)
            (radialJacobiField (I := I) g p w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) 1)) ≤ B) →
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal c *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ∧
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) ≤
        ENNReal.ofReal
            (Real.sqrt (((Module.finrank ℝ E).factorial : ℝ) *
              (B * B) ^ Module.finrank ℝ E)) *
          (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
            (modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  obtain ⟨ρ, hρpos, htwo⟩ := exists_vol_two_same (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρpos, ?_⟩
  intro c B R s hB domainRadius_pos hR tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt hdens geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius hJ
  exact htwo hB domainRadius_pos hR tangentBall_metricRadius_lt tangentBall_geodesicRadius_lt hdens geodesicRadius_lt_domainRadius geodesicRadius_lt_chartRadius normalizedGeodesicRadius_lt_domainRadius
    (metricBall_meas (I := I) (M := M) p s) hJ

omit [NeZero (Module.finrank ℝ E)] in
theorem metricBall_vol_ge [PseudoMetricSpace M]
    (g : SmoothRiemannianMetric I M) (p : M)
    {c R s : ℝ}
    (hball_target : Metric.ball (0 : E) R ⊆ (normalChartAt (I := I) g p).target)
    (hcoord_subset :
      (normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R ⊆ Metric.ball p s)
    (hdens : ∀ w ∈ Metric.ball (0 : E) R,
      c ≤ normalChartDensity (I := I) g p w) :
    ENNReal.ofReal c * (modelHaar (E := E)) (Metric.ball (0 : E) R) ≤
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) := by
  exact le_trans
    (coordBall_vol_ge (I := I) g p hball_target hdens)
    (MeasureTheory.measure_mono hcoord_subset)


omit [NeZero (Module.finrank ℝ E)] in
theorem metricBall_vol_ge_sc [PseudoMetricSpace M]
    (g : SmoothRiemannianMetric I M) (p : M)
    {c R s : ℝ} (domainRadius_pos : 0 < R)
    (hball_target : Metric.ball (0 : E) R ⊆ (normalChartAt (I := I) g p).target)
    (hcoord_subset :
      (normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R ⊆ Metric.ball p s)
    (hdens : ∀ w ∈ Metric.ball (0 : E) R,
      c ≤ normalChartDensity (I := I) g p w) :
    ENNReal.ofReal c *
        (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) := by
  simpa [modelHaar_ball (E := E) domainRadius_pos] using
    metricBall_vol_ge (I := I) g p hball_target hcoord_subset hdens

omit [NeZero (Module.finrank ℝ E)] in
theorem metricBall_vol_ge_sc_c2 [PseudoMetricSpace M]
    (g : SmoothRiemannianMetric I M) (p : M)
    {c R s : ℝ} (domainRadius_pos : 0 < R)
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (hcoord_subset :
      (normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R ⊆ Metric.ball p s)
    (hdens : ∀ w ∈ Metric.ball (0 : E) R,
      c ≤ normalChartDensity (I := I) g p w) :
    ENNReal.ofReal c *
        (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) :=
  metricBall_vol_ge_sc (I := I) g p domainRadius_pos
    (ball_target_of_radius (I := I) g p hR) hcoord_subset hdens

end BallUpper

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

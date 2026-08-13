import DifferentialGeometry.Geometry.Comparison.Volume.BallVolume
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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2 ≤ κ →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
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
  obtain ⟨κ, Blo, hκ, hBlo, hmodelGe⟩ := exists_dirModel_ge1 (I := I) g p
  refine ⟨ρ, C, κ, Blo, hρ, hC, hκ, hBlo, ?_⟩
  intro Rm A Bhi R s hBhi hRm_nonneg hRpos hRρ hRC2 hCRρ hgs hsR hsρ hsdiv
    hKcap hRmGlobal hbasis hmodelLe
  have hK_nonneg :
      0 ≤ Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2 := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hRm_nonneg) (sq_nonneg (C * R))
  exact hvol (Rm := Rm) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R) (s := s)
    hBlo.le hBhi hRm_nonneg hRpos hRρ hRC2 hCRρ hgs hsR hsρ hsdiv
    hRmGlobal hbasis hmodelLe (hmodelGe hK_nonneg hKcap)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2 ≤ κ →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
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
  obtain ⟨ρ, C, κ, Blo, hρ, hC, hκ, hBlo, hvol⟩ :=
    exists_pair_rrm1_ge (I := I) (M := M) g hEnorm p
  refine ⟨ρ, C, κ, Blo, hρ, hC, hκ, hBlo, ?_⟩
  intro Rm A R s hRm_nonneg hRpos hRρ hRC2 hCRρ hgs hsR hsρ hsdiv hKcap
    hRmGlobal hbasis
  let Bhi : ℝ :=
    max
      (A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) * A) 1)
      0
  have hBhi : 0 ≤ Bhi := by
    dsimp [Bhi]
    exact le_max_right _ _
  have hmodelLe :
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * (C * R) ^ 2) * A) 1 ≤ Bhi := by
    dsimp [Bhi]
    exact le_max_left _ _
  exact hvol (Rm := Rm) (A := A) (Bhi := Bhi) (R := R) (s := s) hBhi
    hRm_nonneg hRpos hRρ hRC2 hCRρ hgs hsR hsρ hsdiv hKcap hRmGlobal hbasis
    hmodelLe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
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
  intro Rm b A Blo Bhi R s hBlo hBhi hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2
    hρball hgs hsR hsρ hsdiv hRm hbasis hmodelLe hmodelGe
  let K : ℝ :=
    Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) * Rm * ρ ^ 2
  have hK : 0 ≤ K := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hRm_nonneg) (sq_nonneg ρ)
  have hKbound :
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ K := by
    rfl
  exact hvol (K := K) (Rm := Rm) (b := b) (A := A) (Blo := Blo) (Bhi := Bhi)
    (R := R) (s := s) hBlo hBhi hK hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2
    hρball hgs hsR hsρ hsdiv hKbound hRm hbasis (by simpa [K] using hmodelLe)
    (by simpa [K] using hmodelGe)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        radialCurve (I := I) g p w t ∈ U) →
      (∀ q ∈ U,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
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
  intro Rm b A Blo Bhi R s U hBlo hBhi hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv hcurve hRmU hbasis hmodelLe hmodelGe
  refine hvol (Rm := Rm) (b := b) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R)
    (s := s) hBlo hBhi hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs hsR
    hsρ hsdiv ?_ hbasis hmodelLe hmodelGe
  intro w hw t ht
  exact hRmU (radialCurve (I := I) g p w t) (hcurve w hw t ht)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
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
  intro Rm b A Blo Bhi R s hBlo hBhi hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv hRmGlobal hbasis hmodelLe hmodelGe
  exact hvol (Rm := Rm) (b := b) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R)
    (s := s) (U := Set.univ) hBlo hBhi hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2
    hρball hgs hsR hsρ hsdiv (fun _ _ _ _ => Set.mem_univ _) (fun q _ => hRmGlobal q)
    hbasis hmodelLe hmodelGe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1 ≤ Bhi →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Blo ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i))) 1) →
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
  intro Rm A Blo Bhi R s hBlo hBhi hRm_nonneg hRpos hRρ hRC2 hρball hgs hsR hsρ
    hsdiv hRmGlobal hbasis hmodelLe hmodelGe
  exact hvol (Rm := Rm) (b := 1) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R) (s := s)
    hBlo hBhi hRm_nonneg zero_le_one le_rfl le_rfl hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv hRmGlobal hbasis (by simpa [one_mul] using hmodelLe)
    (fun v hv => by simpa [one_mul] using hmodelGe v hv)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ κ →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
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
  obtain ⟨κ, Blo, hκ, hBlo, hmodelGe⟩ := exists_dirModel_ge1 (I := I) g p
  refine ⟨ρ, κ, Blo, hρ, hκ, hBlo, ?_⟩
  intro Rm A Bhi R s hBhi hRm_nonneg hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv
    hKcap hRmGlobal hbasis hmodelLe
  have hK_nonneg :
      0 ≤ Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hRm_nonneg) (sq_nonneg ρ)
  exact hvol (Rm := Rm) (A := A) (Blo := Blo) (Bhi := Bhi) (R := R) (s := s)
    hBlo.le hBhi hRm_nonneg hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv
    hRmGlobal hbasis hmodelLe (hmodelGe hK_nonneg hKcap)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ κ →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
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
  obtain ⟨ρ, κ, Blo, hρ, hκ, hBlo, hvol⟩ :=
    exists_vol_pair_rm1_ge (I := I) (M := M) g hEnorm p
  refine ⟨ρ, κ, Blo, hρ, hκ, hBlo, ?_⟩
  intro Rm A R s hRm_nonneg hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hKcap
    hRmGlobal hbasis
  let Bhi : ℝ :=
    max
      (A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1)
      0
  have hBhi : 0 ≤ Bhi := by
    dsimp [Bhi]
    exact le_max_right _ _
  have hmodelLe :
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1 ≤ Bhi := by
    dsimp [Bhi]
    exact le_max_left _ _
  exact hvol (Rm := Rm) (A := A) (Bhi := Bhi) (R := R) (s := s) hBhi
    hRm_nonneg hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hKcap hRmGlobal hbasis
    hmodelLe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ) →
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
        Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a * B ≤ Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                  (a • (∑ i, v i • (chartModelBasis E) i))))) 1) →
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
  intro a K Rm Vb b A B R s hBnn ha hK hRm_nonneg hVb hb0 hb1 h1b hRpos hRρ
    hRC2 hρball hgs hsR hsρ hsdiv hsmallBasis hsmallDir hlaunch hKbound hRm hγ
    ι _ _ _ hcard F hpar hON hFdiff hinit hmodelLe hmodelGe
  exact h hBnn ha hK hRm_nonneg hVb hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv hsmallBasis hsmallDir hlaunch hKbound hRm
    (fun w hw _ _ => (hγ w hw).contMDiffAt) hcard F hpar hON hFdiff
    hinit hmodelLe hmodelGe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_vol_rm04_pkg
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {a K Rm Vb b A B R s : ℝ},
      (D : Rm04FrameData (I := I) g p R b) →
      IsRm04VolHyp (I := I) g p D ρ a K Rm Vb A B s →
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
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  letI : Fintype D.ι := D.fintype
  letI : DecidableEq D.ι := D.decidableEq
  letI : Nonempty D.ι := D.nonempty
  exact hvol H.hBnn H.ha H.hK H.hRm_nonneg H.hVb H.hb0 H.hb1 H.h1b
    H.hRpos H.hRρ H.hRC2 H.hρball H.hgs H.hsR H.hsρ H.hsdiv
    H.hsmallBasis H.hsmallDir H.hlaunch H.hKbound H.hRm H.hγ
    H.hcard D.F H.hpar H.hON H.hFdiff H.hinit H.hmodelLe H.hmodelGe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_vol_scale
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {K Rm Vb b A B R s : ℝ},
      (D : Rm04FrameData (I := I) g p R b) →
      (∀ a : ℝ, 0 < a →
        (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ) →
        (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
          ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ) →
        IsRm04VolHyp (I := I) g p D ρ a K Rm Vb A B s) →
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
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_rm04_pkg (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro K Rm Vb b A B R s D H
  obtain ⟨a, Ha⟩ := exists_rm04_scale (I := I) g p D hρ H
  exact hvol D Ha

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb) →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * Vb ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
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
  obtain ⟨ρ, hρ, hvol⟩ := exists_vol_rm04_pkg.{_, _, _, 0} (I := I) (M := M) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro K Rm Vb b A B R s hBnn hK hRm_nonneg hVb hb0 hb1 h1b hRpos hRρ
    hRC2 hρball hgs hsR hsρ hsdiv hlaunch hKbound hRm hbasis hmodelLe hmodelGe
  obtain ⟨a, ha, hsmallBasis, hsmallDir⟩ := basisUnitScaleSmall (E := E) hρ
  obtain ⟨D, H⟩ :=
    exists_rm04_scalar.{_, _, _, 0} (I := I) g p hBnn ha hK hRm_nonneg hVb hb0 hb1 h1b
      hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hsmallBasis hsmallDir hlaunch
      hKbound hRm hbasis hmodelLe hmodelGe
  exact hvol D H

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
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
  intro K Rm b A B R s hBnn hK hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2
    hρball hgs hsR hsρ hsdiv hKbound hRm hbasis hmodelLe hmodelGe
  let Vb : ℝ := ρ
  have hVb : 0 ≤ Vb := by
    exact hρ.le
  have hlaunch : ∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb := by
    intro w hw
    exact le_of_lt (by simpa [Vb] using hρball w hw)
  exact hvol (K := K) (Rm := Rm) (Vb := Vb) (b := b) (A := A) (B := B)
    (R := R) (s := s) hBnn hK hRm_nonneg hVb hb0 hb1 h1b hRpos hRρ hRC2
    hρball hgs hsR hsρ hsdiv hlaunch (by simpa [Vb] using hKbound) hRm hbasis
    hmodelLe hmodelGe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
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
  intro Rm b A B R s hBnn hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv hRm hbasis hmodelLe hmodelGe
  let K : ℝ :=
    Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) * Rm * ρ ^ 2
  have hK : 0 ≤ K := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hRm_nonneg) (sq_nonneg ρ)
  have hKbound :
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ K := by
    rfl
  exact hvol (K := K) (Rm := Rm) (b := b) (A := A) (B := B) (R := R) (s := s)
    hBnn hK hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv
    hKbound hRm hbasis (by simpa [K] using hmodelLe)
    (by simpa [K] using hmodelGe)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        radialCurve (I := I) g p w t ∈ U) →
      (∀ q ∈ U,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
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
  intro Rm b A B R s U hBnn hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv hcurve hRmU hbasis hmodelLe hmodelGe
  refine hvol (Rm := Rm) (b := b) (A := A) (B := B) (R := R) (s := s)
    hBnn hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv ?_
    hbasis hmodelLe hmodelGe
  intro w hw t ht
  exact hRmU (radialCurve (I := I) g p w t) (hcurve w hw t ht)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * (b * A)) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1) →
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
  intro Rm b A B R s hBnn hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv hRmGlobal hbasis hmodelLe hmodelGe
  exact hvol (Rm := Rm) (b := b) (A := A) (B := B) (R := R) (s := s)
    (U := Set.univ) hBnn hRm_nonneg hb0 hb1 h1b hRpos hRρ hRC2 hρball hgs
    hsR hsρ hsdiv (fun _ _ _ _ => Set.mem_univ _) (fun q _ => hRmGlobal q)
    hbasis hmodelLe hmodelGe

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0
        (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) 1)
        ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2) * A) 1 ≤ B →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
                Rm * ρ ^ 2) * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i))) 1) →
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
  intro Rm A B R s hBnn hRm_nonneg hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv
    hRmGlobal hbasis hmodelLe hmodelGe
  exact hvol (Rm := Rm) (b := 1) (A := A) (B := B) (R := R) (s := s)
    hBnn hRm_nonneg (by norm_num) (by norm_num) (by norm_num) hRpos hRρ hRC2
    hρball hgs hsR hsρ hsdiv hRmGlobal hbasis
    (by simpa [one_mul] using hmodelLe)
    (by
      intro v hv
      simpa [one_mul] using hmodelGe v hv)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 ≤ κ →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ Rm) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) →
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
  obtain ⟨κ, B, hκ, hB, hmodelGe⟩ := exists_dirModel_ge1 (I := I) g p
  refine ⟨ρ, κ, B, hρ, hκ, hB, ?_⟩
  intro Rm A R s hRm_nonneg hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hKcap
    hRmGlobal hbasis hmodelLe
  have hK_nonneg :
      0 ≤ Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * ρ ^ 2 := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hRm_nonneg) (sq_nonneg ρ)
  exact hvol (Rm := Rm) (A := A) (B := B) (R := R) (s := s) hB.le hRm_nonneg
    hRpos hRρ hRC2 hρball hgs hsR hsρ hsdiv hRmGlobal hbasis hmodelLe
    (hmodelGe hK_nonneg hKcap)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R, Real.sqrt (g.inner p w w) ≤ Vb) →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Rm * Vb ^ 2 ≤ K →
      (∀ w ∈ Metric.ball (0 : E) R, ∀ t (_ht : t ∈ Set.Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p w t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p w t))) ≤ Rm) →
      (∀ a : ℝ, 0 < a →
        (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < ρ) →
        (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
          ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < ρ) →
        (∀ k : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) ∧
        A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B ∧
        (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
          a * B ≤ Real.sqrt
              (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                (a • (∑ i, v i • (chartModelBasis E) i))) -
              gronwallBound 0 (max K 1)
                (K * (b * Real.sqrt
                  (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                    (a • (∑ i, v i • (chartModelBasis E) i))))) 1)) →
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
  intro K Rm Vb b A B R s hBnn hK hRm_nonneg hVb hb0 hb1 h1b hRpos hRρ
    hRC2 hρball hgs hsR hsρ hsdiv hlaunch hKbound hRm hscalar
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one h1b
  obtain ⟨D, hcard, hpar, hON, hFdiff⟩ :=
    exists_rm04FrameData_radius.{_, _, _, 0} (I := I) g p hb hb1 hRC2
  refine hvol (K := K) (Rm := Rm) (Vb := Vb) (b := b) (A := A)
    (B := B) (R := R) (s := s) D ?_
  intro a ha hsmallBasis hsmallDir
  obtain ⟨hinit, hmodelLe, hmodelGe⟩ := hscalar a ha hsmallBasis hsmallDir
  exact {
    hBnn := hBnn
    ha := ha
    hK := hK
    hRm_nonneg := hRm_nonneg
    hVb := hVb
    hb0 := hb0
    hb1 := hb1
    h1b := h1b
    hRpos := hRpos
    hRρ := hRρ
    hRC2 := hRC2
    hρball := hρball
    hgs := hgs
    hsR := hsR
    hsρ := hsρ
    hsdiv := hsdiv
    hsmallBasis := hsmallBasis
    hsmallDir := hsmallDir
    hlaunch := hlaunch
    hKbound := hKbound
    hRm := hRm
    hγ := radialC1AtBall (I := I) g p hRC2 hb1
    hcard := hcard
    hpar := hpar
    hON := hON
    hFdiff := hFdiff
    hinit := hinit
    hmodelLe := hmodelLe
    hmodelGe := hmodelGe }

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < Rup →
      Rup ≤ expMapC2Radius (I := I) g p →
      (letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
       MeasurableSet (Metric.ball p s)) →
      (∀ w ∈ Metric.ball (0 : E) Rup,
        ∀ i : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
            (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
            (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) →
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
  intro c B Rlo Rup s hB hRlo_pos hRup_pos hRlo hρlo_ball hgs hdens
    hsRup hsρ hs_div_Rup hRup hmeas hJ
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hρlo_ball' : ∀ w ∈ Metric.ball (0 : E) Rlo,
      Real.sqrt (g.inner p (show TangentSpace I p from w) (show TangentSpace I p from w)) < ρlo :=
    fun w hw => lt_of_lt_of_le (hρlo_ball w hw) (min_le_left _ _)
  have hsρup : s < ρup := lt_of_lt_of_le hsρ (min_le_right _ _)
  exact ⟨
    hlower hRlo_pos hRlo hρlo_ball' hgs hdens,
    hupper hB hRup_pos hsRup hsρup hs_div_Rup hRup hmeas hJ⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
       MeasurableSet (Metric.ball p s)) →
      (∀ w ∈ Metric.ball (0 : E) R,
        ∀ i : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
            (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
            (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) →
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
  intro c B R s hB hRpos hR hρball hgs hdens hsR hsρ hsdiv hmeas hJ
  exact htwo hB hRpos hRpos hR hρball hgs hdens hsR hsρ hsdiv hR hmeas hJ

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
      s / Real.sqrt (gpCoerciveConst (I := I) g p) < R →
      (∀ w ∈ Metric.ball (0 : E) R,
        ∀ i : Fin (Module.finrank ℝ E),
          Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from w))
            (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)
            (radialJacobiField (I := I) g p w ((chartModelBasis E) i) 1)) ≤ B) →
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
  intro c B R s hB hRpos hR hρball hgs hdens hsR hsρ hsdiv hJ
  exact htwo hB hRpos hR hρball hgs hdens hsR hsρ hsdiv
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
    {c R s : ℝ} (hRpos : 0 < R)
    (hball_target : Metric.ball (0 : E) R ⊆ (normalChartAt (I := I) g p).target)
    (hcoord_subset :
      (normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R ⊆ Metric.ball p s)
    (hdens : ∀ w ∈ Metric.ball (0 : E) R,
      c ≤ normalChartDensity (I := I) g p w) :
    ENNReal.ofReal c *
        (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) := by
  simpa [modelHaar_ball (E := E) hRpos] using
    metricBall_vol_ge (I := I) g p hball_target hcoord_subset hdens

theorem metricBall_vol_ge_sc_c2 [PseudoMetricSpace M]
    (g : SmoothRiemannianMetric I M) (p : M)
    {c R s : ℝ} (hRpos : 0 < R)
    (hR : R ≤ expMapC2Radius (I := I) g p)
    (hcoord_subset :
      (normalChartAt (I := I) g p).symm '' Metric.ball (0 : E) R ⊆ Metric.ball p s)
    (hdens : ∀ w ∈ Metric.ball (0 : E) R,
      c ≤ normalChartDensity (I := I) g p w) :
    ENNReal.ofReal c *
        (ENNReal.ofReal (R ^ Module.finrank ℝ E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p s) :=
  metricBall_vol_ge_sc (I := I) g p hRpos
    (ball_tgt_of_radius (I := I) g p hR) hcoord_subset hdens

end BallUpper

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

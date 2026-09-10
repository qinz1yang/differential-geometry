import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalCoverNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossModelNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceProductNoncollapse

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
  [LocallyPathConnectedSpace N] [SemilocallySimplyConnectedSpace N] [Inhabited N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance universalCoverSplitC1N : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance universalCoverSplitC1M : IsManifold (𝓡 2) 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance universalCoverSplitC1Cover : IsManifold I 1 (UniversalCover N) :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance universalCoverSplitMeasurableN : MeasurableSpace N := borel N
private local instance universalCoverSplitBorelN : BorelSpace N := ⟨rfl⟩
private local instance universalCoverSplitMeasurableM : MeasurableSpace M := borel M
private local instance universalCoverSplitBorelM : BorelSpace M := ⟨rfl⟩

theorem universalCover_split_surface_tensor_half_noncollapsed
    (g : SmoothRiemannianMetric I N) (hdim : Module.finrank ℝ E = 3)
    (h : SmoothRiemannianMetric (𝓡 2) M)
    (Phi : (M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover N)
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) g).inner (Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
        h.inner y v w + a * c)
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hnoncollapse : ∀ (p : N) (rho : ℝ), 0 < rho →
      (∀ z ∈ riemannianBallOf (I := I) g p rho,
        rho ^ 4 * normSq0S (I := I) g z 4 (metricRm04At (I := I) g z) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := N) g
          (riemannianBallOf (I := I) g p rho))
    (y : M) (r : ℝ) (hr : 0 < r)
    (hcurvature : ∀ z ∈ riemannianBallOf (I := 𝓡 2) h y r,
      r ^ 4 * normSq0S (I := 𝓡 2) h z 4 (metricRm04At (I := 𝓡 2) h z) ≤ 1) :
    ENNReal.ofReal (kappa / 2) * ENNReal.ofReal r ^ 2 ≤
      riemannianVolumeMeasure (I := 𝓡 2) (M := M) h
        (riemannianBallOf (I := 𝓡 2) h y r) := by
  let : SigmaCompactSpace (UniversalCover N) :=
    Phi.toHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  let gP : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ, ℝ)) (M × ℝ) :=
    Diffeomorph.pullbackMetricCross (UniversalCover.liftedMetric (I := I) g) Phi
  have hprod : ∀ (p : M × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p),
      gP.inner p v w = h.inner p.1 v.1 w.1 + v.2 * w.2 := by
    rintro ⟨z, s⟩ v w
    change (Diffeomorph.pullbackMetricCross
      (UniversalCover.liftedMetric (I := I) g) Phi).inner (z, s) v w = _
    rw [Diffeomorph.pullbackMetricCross_inner]
    exact hproduct z s v.1 w.1 v.2 w.2
  have hcover : ∀ (p : UniversalCover N) (rho : ℝ), 0 < rho →
      (∀ z ∈ riemannianBallOf (I := I) (UniversalCover.liftedMetric (I := I) g) p rho,
        rho ^ 4 * normSq0S (I := I) (UniversalCover.liftedMetric (I := I) g) z 4
          (metricRm04At (I := I) (UniversalCover.liftedMetric (I := I) g) z) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal rho ^ 3 ≤
        riemannianVolumeMeasure (I := I) (M := UniversalCover N)
          (UniversalCover.liftedMetric (I := I) g)
          (riemannianBallOf (I := I) (UniversalCover.liftedMetric (I := I) g) p rho) := by
    intro p rho hrho hRm
    simpa only [hdim] using
      universalCover_tensor_noncollapsed g kappa hnoncollapse p rho hrho hRm
  have hproductNC : ∀ (p : M × ℝ) (rho : ℝ), 0 < rho →
      (∀ z : M × ℝ,
        riemannianEDistOf (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP p z < ENNReal.ofReal rho →
        rho ^ 4 * normSq0S (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP z 4
          (metricRm04At (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP z) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal rho ^ 3 ≤
        riemannianVolumeMeasure (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (M := M × ℝ) gP
          {z : M × ℝ |
            riemannianEDistOf (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP p z < ENNReal.ofReal rho} := by
    intro p rho hrho hRm
    exact tensor_noncollapsed_pullbackMetricCross
      (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (J := I)
      (UniversalCover.liftedMetric (I := I) g) Phi kappa 3 hcover p rho hrho hRm
  exact surfaceProduct_tensor_half_noncollapsed h gP hprod kappa hkappa
    hproductNC y r hr hcurvature

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

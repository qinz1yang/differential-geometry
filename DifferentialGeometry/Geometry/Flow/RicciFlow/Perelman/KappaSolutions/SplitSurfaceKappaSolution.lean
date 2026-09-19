import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SplitSurfaceAncientGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalCoverSplitNoncollapse

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
  (G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval)

local instance splitSurfaceKappaBaseTopology : TopologicalSpace F.M := F.topology
local instance splitSurfaceKappaBaseCharted : ChartedSpace H F.M := F.charted
local instance splitSurfaceKappaBaseSmooth : IsManifold I ∞ F.M := F.smooth
local instance splitSurfaceKappaBaseC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
local instance splitSurfaceKappaBaseT2 : T2Space F.M := F.t2
local instance splitSurfaceKappaBaseSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance splitSurfaceKappaBaseInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance splitSurfaceKappaBaseLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance splitSurfaceKappaBaseSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)
local instance splitSurfaceKappaBaseMeasurable : MeasurableSpace F.M := borel F.M
local instance splitSurfaceKappaBaseBorel : BorelSpace F.M := ⟨rfl⟩

local instance splitSurfaceKappaSurfaceTopology : TopologicalSpace G.M := G.topology
local instance splitSurfaceKappaSurfaceCharted :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
local instance splitSurfaceKappaSurfaceSmooth : IsManifold (𝓡 2) ∞ G.M := G.smooth
local instance splitSurfaceKappaSurfaceC1 : IsManifold (𝓡 2) 1 G.M :=
  IsManifold.of_le (n := ∞) (by decide)
local instance splitSurfaceKappaSurfaceT2 : T2Space G.M := G.t2
local instance splitSurfaceKappaSurfaceSigma : SigmaCompactSpace G.M := G.sigmaCompact
local instance splitSurfaceKappaSurfaceMeasurable : MeasurableSpace G.M := borel G.M
local instance splitSurfaceKappaSurfaceBorel : BorelSpace G.M := ⟨rfl⟩

variable (Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
  (hproduct : ∀ t : ℝ, t ≤ 0 → ∀ (y : G.M) (s : ℝ)
    (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
    (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
      (G.S.family.metric t).inner y v w + a * c)

include hproduct

theorem splitSurface_noncollapsed_all_scales {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3) :
    PointedFlowNoncollapsedAllScales (I := 𝓡 2) G (kappa / 2) := by
  let _ : ConnectedSpace F.M := hF.connected
  intro time B hRm
  refine ⟨div_pos hF.kappa_pos (by norm_num), ?_⟩
  have hbase : ∀ (p : F.M) (rho : ℝ), 0 < rho →
      (∀ z ∈ riemannianBallOf (I := I) (F.S.family.metric (time : ℝ)) p rho,
        rho ^ 4 * normSq0S (I := I) (F.S.family.metric (time : ℝ)) z 4
          (metricRm04At (I := I) (F.S.family.metric (time : ℝ)) z) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := F.M) (F.S.family.metric (time : ℝ))
          (riemannianBallOf (I := I) (F.S.family.metric (time : ℝ)) p rho) := by
    intro p rho hrho hcurvature
    let B0 : FlowMetricBall (I := I) (M := F.M) F.S time := ⟨p, rho, hrho⟩
    have hB0 : B0.IsSpatiallyRmControlled := by
      intro z hz
      simpa only [B0, FlowMetricBall.rmNormSq, SolutionFamily.rm04,
        metricRm04_apply, SolutionOn.family] using hcurvature z hz
    have hvolume := (hF.noncollapsed time B0 hB0).2
    change ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := F.M) (F.S.family.metric (time : ℝ))
        (riemannianBallOf (I := I) (F.S.family.metric (time : ℝ)) p rho) at hvolume
    exact hvolume
  have hsurface :
      ∀ z ∈ riemannianBallOf (I := 𝓡 2) (G.S.family.metric (time : ℝ))
        B.center B.radius,
      B.radius ^ 4 * normSq0S (I := 𝓡 2) (G.S.family.metric (time : ℝ)) z 4
        (metricRm04At (I := 𝓡 2) (G.S.family.metric (time : ℝ)) z) ≤ 1 := by
    intro z hz
    simpa only [FlowMetricBall.rmNormSq, SolutionFamily.rm04,
      metricRm04_apply, SolutionOn.family] using hRm z hz
  have ht : (time : ℝ) ≤ 0 := by simpa using time.property
  have hvolume := universalCover_split_surface_tensor_half_noncollapsed
    (F.S.family.metric (time : ℝ)) hdim (G.S.family.metric (time : ℝ))
    Phi (hproduct (time : ℝ) ht) kappa hF.kappa_pos.le hbase
    B.center B.radius B.radius_pos hsurface
  change ENNReal.ofReal (kappa / 2) * ENNReal.ofReal B.radius ^
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) ≤
    riemannianVolumeMeasure (I := 𝓡 2) (M := G.M) (G.S.family.metric (time : ℝ))
      (riemannianBallOf (I := 𝓡 2) (G.S.family.metric (time : ℝ)) B.center B.radius)
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using hvolume

theorem splitSurface_toIsAncientKappaSolution {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hconnectedG : ConnectedSpace G.M)
    (hcompleteG : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := 𝓡 2) (G.atTime t))
    (hpositiveG : ∀ t : ℝ, t ≤ 0 → ∀ y : G.M, 0 < G.S.scalar t y) :
    IsAncientKappaSolution (I := 𝓡 2) (kappa / 2) G := by
  obtain ⟨C, _, hsign, hscalar, _, hnotFlat⟩ :=
    splitSurface_ancient_geometry F G Phi hproduct hF hdim hpositiveG
  exact
    { kappa_pos := div_pos hF.kappa_pos (by norm_num)
      carrier_eq := rfl
      regular_eq := rfl
      connected := hconnectedG
      complete := fun t ht => hcompleteG t (by simpa using ht)
      nonnegativeCurvatureOperator := fun t ht => hsign t (by simpa using ht)
      globalScalarBound := ⟨C, hscalar⟩
      noncollapsed := splitSurface_noncollapsed_all_scales F G Phi hproduct hF hdim
      notFlat := hnotFlat }

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

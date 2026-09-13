import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactPointedLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerCover
import DifferentialGeometry.Topology.Covering.CylinderQuotientModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderAsymptoticVolumeRatio
import DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cylinder" => S × ℝ
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "gS" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

private local instance noncompactShrinkerClassificationSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (L : PointedRiemannianManifold.{u, uE, uH} (I := I))

local instance classifiedShrinkerTopology : TopologicalSpace L.M := L.topology
local instance classifiedShrinkerCharted : ChartedSpace H L.M := L.charted
local instance classifiedShrinkerSmooth : IsManifold I ∞ L.M := L.smooth
local instance classifiedShrinkerT2 : T2Space L.M := L.t2
local instance classifiedShrinkerSigma : SigmaCompactSpace L.M := L.sigmaCompact
local instance classifiedShrinkerInhabited : Inhabited L.M := ⟨L.basepoint⟩
local instance classifiedShrinkerLocallyPathConnected : LocallyPathConnectedSpace L.M := by
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H L.M
local instance classifiedShrinkerSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace L.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := L.M)

theorem noncompact_backward_three_shrinker_classification
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 3)
    (hnoncompact : @NoncompactSpace F.M F.topology)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
    (hcomplete : MetricComplete (I := I) L) (hconnected : ConnectedSpace L.M)
    (f : C^∞⟮I, L.M; ℝ⟯) (hsoliton : gradientRicciSoliton (I := I) L.metric f 1)
    (hnonflat : ∃ x : L.M, metricScalarAt (I := I) L.metric x ≠ 0)
    (hclass : NoncompactShrinkerCylinderClassification (I := I) (M := L.M) L.metric f 1) :
    NoncompactSpace L.M ∧
      ∃ Psi : Cylinder ≃ₘ⟮CI, I⟯ UniversalCover L.M,
        (∀ (y : S) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a b : ℝ),
          (UniversalCover.liftedMetric (I := I) L.metric).inner (Psi (y, s))
              (mfderiv CI I Psi (y, s) (v, a)) (mfderiv CI I Psi (y, s) (w, b)) =
            2 * (gS).inner y v w + a * b) ∧
        CylinderQuotientModels (I := I)
          (fun p : Cylinder => UniversalCover.proj (Psi p)) ∧
        ∀ p : L.M, asymptoticVolumeRatio (I := I) L.metric p = 0 := by
  let _ : ConnectedSpace L.M := hconnected
  have hlimitNoncompact := backwardSliceLimit_noncompact
    F hF.connected hnoncompact tau htau q Phi
  let _ : NoncompactSpace L.M := hlimitNoncompact
  have hmetricComplete : RiemannianMetricComplete (I := I) L.metric := ⟨hcomplete⟩
  obtain ⟨Psi, hproduct, hfibres⟩ :=
    complete_noncompact_three_shrinker_universal_cover_fibres
      L.metric f (by norm_num : (0 : ℝ) < 1) hdim hmetricComplete hsoliton hnonflat hclass
  have hproduct' : ∀ (y : S) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) L.metric).inner (Psi (y, s))
          (mfderiv CI I Psi (y, s) (v, a)) (mfderiv CI I Psi (y, s) (w, b)) =
        2 * (gS).inner y v w + a * b := by
    simpa only [div_one] using hproduct
  have hlocal : IsLocalDiffeomorph CI I ∞
      (fun p : Cylinder => UniversalCover.proj (Psi p)) :=
    isLocalDiffeomorph_comp (UniversalCover.proj_localDiffeo (I := I) (M := L.M))
      Psi.isLocalDiffeomorph
  have hcover : IsCoveringMap (fun p : Cylinder => UniversalCover.proj (Psi p)) :=
    (UniversalCover.proj_isCoveringMap (X := L.M)).comp_homeomorph Psi.toHomeomorph
  have hsurj : Function.Surjective (fun p : Cylinder => UniversalCover.proj (Psi p)) := by
    let _ : PathConnectedSpace L.M := PathConnectedSpace.of_locallyPathConnectedSpace
    intro x
    let u : UniversalCover L.M :=
      ⟨x, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (default : L.M) x)⟩
    exact ⟨Psi.symm u, congrArg (UniversalCover.proj : UniversalCover L.M → L.M)
      (Psi.apply_symm_apply u)⟩
  refine ⟨hlimitNoncompact, Psi, hproduct',
    cylinderQuotientModels_of_fibres _ hlocal hcover hsurj hfibres, ?_⟩
  let h : SmoothRiemannianMetric (𝓡 2) S := scaleMetric 2 (by norm_num) gS
  have hprod : ∀ (y : S) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) L.metric).inner (Psi (y, s))
          (mfderiv CI I Psi (y, s) (v, a)) (mfderiv CI I Psi (y, s) (w, b)) =
        h.inner y v w + a * b := by
    intro y s v w a b
    simpa only [h, scaleMetric_inner] using hproduct' y s v w a b
  intro p
  exact cylinderCover_asymptoticVolumeRatio_eq_zero L.metric hdim h Psi hprod p

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

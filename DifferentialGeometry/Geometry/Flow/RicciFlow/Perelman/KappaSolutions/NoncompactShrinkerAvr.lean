import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactAsymptoticShrinker
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderAsymptoticVolumeRatio

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance noncompactShrinkerAvrSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

theorem exists_noncompact_backward_three_limit_avr_zero
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 3)
    (hnoncompact : @NoncompactSpace F.M F.topology)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) ∧
        (∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric) ∧
        MetricComplete (I := I) L ∧
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace H L.M := L.charted
         let _ : IsManifold I ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         let _ : SigmaCompactSpace L.M := L.sigmaCompact
         ConnectedSpace L.M ∧ NoncompactSpace L.M ∧
           ∀ p : L.M, asymptoticVolumeRatio (I := I) L.metric p = 0) := by
  obtain ⟨q, L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hgeometry⟩ :=
    exists_noncompact_backward_three_shrinker_cover F hF hdim hnoncompact tau htau hescape
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  let _ : IsManifold I ∞ L.M := L.smooth
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  let _ : Inhabited L.M := ⟨L.basepoint⟩
  let _ : LocallyPathConnectedSpace L.M := by
    let _ : LocallyPathConnectedSpace H :=
      I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    exact ChartedSpace.locallyPathConnectedSpace H L.M
  let _ : SemilocallySimplyConnectedSpace L.M :=
    manifold_semilocallySimplyConnectedSpace (I := I) (M := L.M)
  obtain ⟨hconnected, hnoncompactLimit, Psi, hproduct⟩ := hgeometry
  let _ : ConnectedSpace L.M := hconnected
  let h : SmoothRiemannianMetric (𝓡 2) SphereTwo :=
    scaleMetric 2 (by norm_num) (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
  have hprod : ∀ (x : SphereTwo) (s : ℝ) (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) L.metric).inner (Psi (x, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (w, b)) =
        h.inner x v w + a * b := by
    intro x s v w a b
    simpa only [h, scaleMetric_inner] using hproduct x s v w a b
  refine ⟨q, L, phi, hphi, Phi, C, hdomain, hreference, hcomplete,
    hconnected, hnoncompactLimit, ?_⟩
  intro p
  exact cylinderCover_asymptoticVolumeRatio_eq_zero (I := I) L.metric hdim h Psi hprod p

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

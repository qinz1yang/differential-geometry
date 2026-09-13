import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinker
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactPointedLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerCover

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance noncompactAsymptoticSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

theorem exists_noncompact_backward_three_shrinker_cover
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 3)
    (hnoncompact : @NoncompactSpace F.M F.topology)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop)
    (hfrontier : NoncompactShrinkerCylinderClassificationTheorem.{uE, uH, u}) :
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
         let _ : Inhabited L.M := ⟨L.basepoint⟩
         let _ : LocallyPathConnectedSpace L.M := by
           let _ : LocallyPathConnectedSpace H :=
             I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
           exact ChartedSpace.locallyPathConnectedSpace H L.M
         let _ : SemilocallySimplyConnectedSpace L.M :=
           manifold_semilocallySimplyConnectedSpace (I := I) (M := L.M)
         ConnectedSpace L.M ∧ NoncompactSpace L.M ∧
         ∃ Psi : (SphereTwo × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover L.M,
           ∀ (x : SphereTwo) (s : ℝ) (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
             (UniversalCover.liftedMetric (I := I) L.metric).inner (Psi (x, s))
                 (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a))
                 (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (w, b)) =
               2 * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
                 x v w + a * b) := by
  obtain ⟨q, L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hgeometry⟩ :=
    exists_backward_slice_asymptotic_shrinker F hF (by omega) tau htau hescape
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
  obtain ⟨hconnected, hnonflat, f, hsoliton⟩ := hgeometry
  let _ : ConnectedSpace L.M := hconnected
  have hlimitNoncompact := backwardSliceLimit_noncompact F hF.connected hnoncompact tau htau q Phi
  let _ : NoncompactSpace L.M := hlimitNoncompact
  have hmetricComplete : RiemannianMetricComplete (I := I) L.metric := ⟨hcomplete⟩
  have hclass : NoncompactShrinkerCylinderClassification (I := I) (M := L.M) L.metric f 1 :=
    hfrontier (I := I) (M := L.M) (g := L.metric) (f := f) (sigma := 1)
      (by norm_num) hdim hmetricComplete hsoliton hnonflat
  obtain ⟨Psi, hproduct⟩ := complete_noncompact_three_shrinker_universal_cover_cylinder
    (I := I) L.metric f (by norm_num : (0 : ℝ) < 1) hdim hmetricComplete hsoliton hnonflat hclass
  refine ⟨q, L, phi, hphi, Phi, C, hdomain, hreference, hcomplete,
    hconnected, hlimitNoncompact, Psi, ?_⟩
  intro x s v w a b
  simpa only [div_one] using hproduct x s v w a b

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

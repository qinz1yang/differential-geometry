import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinker
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceShrinker
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactLimitGlobalization

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance ancientSurfaceCompactTopology : TopologicalSpace F.M := F.topology
local instance ancientSurfaceCompactCharted : ChartedSpace H F.M := F.charted
local instance ancientSurfaceCompactSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientSurfaceCompactT2 : T2Space F.M := F.t2

theorem exists_compact_backward_surface_limit [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 2)
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
         CompactSpace L.M ∧ ConnectedSpace L.M ∧
           ∀ x : L.M, metricScalarAt (I := I) L.metric x = 1) := by
  obtain ⟨q, L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hgeometry⟩ :=
    exists_backward_slice_asymptotic_shrinker F hF (by omega) tau htau hescape
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  let _ : IsManifold I ∞ L.M := L.smooth
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  obtain ⟨hconnected, hnonflat, f, hsoliton⟩ := hgeometry
  let _ : ConnectedSpace L.M := hconnected
  have hmetricComplete : RiemannianMetricComplete (I := I) L.metric := ⟨hcomplete⟩
  obtain ⟨hcompact, hscalar⟩ :=
    complete_surface_shrinker_compact_constant_scalar (I := I)
      L.metric f (by norm_num : (0 : ℝ) < 1) hdim hmetricComplete hsoliton hnonflat
  exact ⟨q, L, phi, hphi, Phi, C, hdomain, hreference, hcomplete,
    hcompact, hconnected, hscalar⟩

theorem ancientKappaSurface_compact {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 2) : CompactSpace F.M := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let tau : ℕ → ℝ := fun i => (i : ℝ) + 1
  have htau : ∀ i, 0 < tau i := by
    intro i
    dsimp only [tau]
    positivity
  have hescape : Tendsto tau atTop atTop := by
    apply tendsto_atTop_mono (fun i => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    dsimp only [tau]
    linarith
  obtain ⟨q, L, phi, _, Phi, _, _, _, _, hgeometry⟩ :=
    exists_compact_backward_surface_limit F hF hdim tau htau hescape
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  obtain ⟨hcompact, _, _⟩ := hgeometry
  have hconnected : ∀ k : ℕ,
      @ConnectedSpace ((backwardSliceSequence F tau htau q).obj (phi k)).M
        ((backwardSliceSequence F tau htau q).obj (phi k)).topology :=
    fun k => backwardSliceSequence_connected F hF tau htau q (phi k)
  obtain ⟨k0, hk0⟩ := compactLimit_eventually_globalizes Phi hcompact hconnected
  obtain ⟨_, _, _, _, _, _, hcompactSource⟩ := hk0 k0 le_rfl
  exact hcompactSource

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

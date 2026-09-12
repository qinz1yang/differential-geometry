import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSurfaceCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactEntropyConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.GlobalizedMetricConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyNaturality

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientEntropyLimitTopology : TopologicalSpace F.M := F.topology
local instance ancientEntropyLimitCharted : ChartedSpace H F.M := F.charted
local instance ancientEntropyLimitSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientEntropyLimitC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance ancientEntropyLimitT2 : T2Space F.M := F.t2
local instance ancientEntropyLimitSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance ancientEntropyLimitNonempty : Nonempty F.M := ⟨F.basepoint⟩

theorem ancientKappaSurface_exists_backward_entropy_minimum
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 2) :
    let _ : CompactSpace F.M := ancientKappaSurface_compact F hF hdim
    ∃ rho : ℕ → ℝ,
      (∀ k : ℕ, 0 < rho k) ∧ Tendsto rho atTop atTop ∧
        Tendsto (fun k => surfaceEntropy (F.S.family.metric (-rho k))) atTop
          (𝓝 (totalScalarCurvature (F.S.family.metric 0) *
            Real.log (totalScalarCurvature (F.S.family.metric 0)))) := by
  classical
  let _ : CompactSpace F.M := ancientKappaSurface_compact F hF hdim
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
  obtain ⟨q, L, phi, hphi, Phi, C, hcanonical, _, _, hgeometry⟩ :=
    exists_compact_backward_surface_limit F hF hdim tau htau hescape
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  let _ : IsManifold I ∞ L.M := L.smooth
  let _ : IsManifold I 1 L.M := IsManifold.of_le (n := ∞) (by decide)
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  let _ : Nonempty L.M := ⟨L.basepoint⟩
  obtain ⟨hcompact, _, hscalar⟩ := hgeometry
  let _ : CompactSpace L.M := hcompact
  have hconnected : ∀ k : ℕ,
      @ConnectedSpace ((backwardSliceSequence F tau htau q).obj (phi k)).M
        ((backwardSliceSequence F tau htau q).obj (phi k)).topology :=
    fun k => backwardSliceSequence_connected F hF tau htau q (phi k)
  obtain ⟨k0, e, _, hconv⟩ :=
    compactLimit_global_pullback_metric_convergence Phi C hcanonical hcompact hconnected
  let G : ℕ → SmoothRiemannianMetric I L.M := fun k =>
    Diffeomorph.pullbackMetric (I := I)
      ((backwardSliceSequence F tau htau q).obj (phi (k0 + k))).metric (e k)
  have hGconv : MetricCInfConvergenceOnCompacts (I := I) G L.metric L.metric := hconv
  obtain ⟨_, hCconv, hNconv⟩ := metric_integrals_tendsto_of_metricCInf G L.metric hGconv
  let rho : ℕ → ℝ := fun k => tau (phi (k0 + k))
  have hrho : ∀ k : ℕ, 0 < rho k := fun k => htau (phi (k0 + k))
  have hshift : Tendsto (fun k : ℕ => k0 + k) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat k0
  have hrhoEscape : Tendsto rho atTop atTop :=
    hescape.comp (hphi.tendsto_atTop.comp hshift)
  let C0 := totalScalarCurvature (F.S.family.metric 0)
  have hCseq (k : ℕ) : totalScalarCurvature (G k) = C0 := by
    dsimp only [G]
    rw [totalScalarCurvature_pullbackMetric]
    change totalScalarCurvature
        (scaleMetric (tau (phi (k0 + k)))⁻¹ (inv_pos.mpr (htau (phi (k0 + k))))
          (F.S.base.metric (-tau (phi (k0 + k))))) = C0
    rw [totalScalarCurvature_scaleMetric _ hdim]
    exact ancientSurfaceFlow_totalScalar_eq_terminal F.S F.isSolution hdim
      (neg_nonpos.mpr (htau (phi (k0 + k))).le)
  have hCfun : (fun k => totalScalarCurvature (G k)) = fun _ : ℕ => C0 :=
    funext hCseq
  rw [hCfun] at hCconv
  have hClimit : totalScalarCurvature L.metric = C0 :=
    tendsto_nhds_unique hCconv tendsto_const_nhds
  have hlimitPositive : ∀ x : L.M, 0 < metricScalarAt (I := I) L.metric x := by
    intro x
    rw [hscalar x]
    norm_num
  have hNlimit : surfaceEntropy L.metric = C0 * Real.log C0 := by
    have heq := (surfaceEntropy_lower_and_eq_iff_constant L.metric hlimitPositive).2.mpr
      ⟨1, hscalar⟩
    rw [hClimit] at heq
    exact heq
  have hNseq (k : ℕ) : surfaceEntropy (G k) =
      surfaceEntropy (F.S.family.metric (-rho k)) := by
    dsimp only [G]
    rw [surfaceEntropy_pullbackMetric]
    change surfaceEntropy
        (scaleMetric (tau (phi (k0 + k)))⁻¹ (inv_pos.mpr (htau (phi (k0 + k))))
          (F.S.base.metric (-tau (phi (k0 + k))))) =
      surfaceEntropy (F.S.family.metric (-rho k))
    rw [surfaceEntropy_scaleMetric _ hdim]
    rfl
  have hNfun : (fun k => surfaceEntropy (G k)) =
      fun k => surfaceEntropy (F.S.family.metric (-rho k)) := funext hNseq
  rw [hNfun, hNlimit] at hNconv
  exact ⟨rho, hrho, hrhoEscape, hNconv⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

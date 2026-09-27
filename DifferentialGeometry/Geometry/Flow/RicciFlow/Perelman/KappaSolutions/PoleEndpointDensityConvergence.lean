import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Defs
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

theorem HalfLineMetricConvergenceData.tendstoLocallyUniformly_poleEndpoint_redDensity
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (p : F.M) (t : ℝ) (ell : P.M → ℝ) (hell : Continuous ell)
    (hconv : TendstoLocallyUniformly
      (fun k y => redLength ((U).term (phi (co.φ k))).S 0 p
        (Phi.map (co.φ k) y) (1 - t)) ell atTop) :
    TendstoLocallyUniformly
      (fun k y => redDensity ((U).term (phi (co.φ k))).S 0 p
        (Phi.map (co.φ k) y) (1 - t))
      (fun y => Real.exp (-ell y -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - t) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) atTop := by
  let f : ℝ → ℝ := fun r => Real.exp (-r -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - t) -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  have hf : Continuous f := by dsimp only [f]; fun_prop
  rw [tendstoLocallyUniformly_iff_forall_tendsto] at hconv ⊢
  intro x
  have hleft : Tendsto (fun z : ℕ × P.M => ell z.2) (atTop ×ˢ 𝓝 x) (𝓝 (ell x)) :=
    hell.continuousAt.tendsto.comp tendsto_snd
  have hright : Tendsto
      (fun z : ℕ × P.M => redLength ((U).term (phi (co.φ z.1))).S 0 p
        (Phi.map (co.φ z.1) z.2) (1 - t)) (atTop ×ˢ 𝓝 x) (𝓝 (ell x)) :=
    hleft.congr_uniformity (hconv x)
  have hpair := (hf.continuousAt.tendsto.comp hleft).prodMk_nhds
    (hf.continuousAt.tendsto.comp hright)
  simpa only [f, redDensity, Function.comp_def] using
    hpair.mono_right (nhds_le_uniformity (f (ell x)))

end DifferentialGeometry.CheegerGromovCompactness

end

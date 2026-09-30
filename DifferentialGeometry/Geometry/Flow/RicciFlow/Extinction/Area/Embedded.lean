import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution.MinimizingDisk
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauExistence

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [hBoundary : I.Boundaryless] [hT2 : T2Space M]
    [hCompact : CompactSpace M] [hNonempty : Nonempty M]

variable [SigmaCompactSpace M]
variable {D : RealTimeInterval} {a b : ℝ}

include hBoundary hT2 hCompact hNonempty


theorem rfs_csf_embedded_area (B : RicciBackground (I := I) (M := M) D a b)
    (hdim : Module.finrank ℝ E = 3) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (γ t)) :
    ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric γ (t + h) -
          loopFamilyLeastArea B.family.metric γ t) / h ≤
        -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε := by
  let _ := hNonempty
  intro t ht
  have htcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  let gamma : Width.RegularLoop I M := regularLoopSlice γ hγ t htcc
  have hslice : ContMDiff 𝓘(ℝ, ℝ) I ∞ (Width.loopLift gamma.toContinuousLoop) :=
    (curveOfLoopFamily γ).smooth_slice hγ htcc
  have himm : ∀ x, Width.loopVelocity (I := I) gamma.toContinuousLoop x ≠ 0 :=
    fun x => hi x t htcc
  obtain ⟨u, sigma, htrace, hconf, hharm, hmin⟩ := Width.conformal_disk_producer
    (B.family.metric t) hdim gamma hslice (hemb t htcc) himm (hctr t htcc)
  exact leastArea_slope_le_of_conformal_minimizing_disk B hdim γ hγ hi hemb t ht
    (hctr t htcc) u sigma htrace hconf hharm hmin


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

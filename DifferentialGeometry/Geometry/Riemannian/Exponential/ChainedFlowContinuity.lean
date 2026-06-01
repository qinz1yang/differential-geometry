import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.SmoothnessUnconditional
import DifferentialGeometry.Geometry.Riemannian.Exponential.LocalDiffeomorphism
import DifferentialGeometry.Geometry.Riemannian.Exponential.PreconnectedPropagation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Geodesic.SmoothFlow
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Analysis.ODE.FlowC1Continuous
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Compactness.Compact

set_option linter.unusedSectionVars false

/-!
# Chain-of-charts continuity of the exponential map

This file collects the six chained-flow continuity steps used to deduce
`Continuous (expMap g p)` on a geodesically complete Riemannian manifold:
compactness of the geodesic segment `γ([0, 1])`, a finite chart-cover
partition via the Lebesgue-number lemma, per-chart joint-`C¹` local flows
from Picard–Lindelöf, continuity at chart junctions via the local-flow
group-property gluing, and the final continuity statement obtained by
specialising the joint flow to `t = 1`.

The detailed Lean types of the intermediate joint-flow predicates are
deferred to the proof phase; here we expose only the propositional
shells required to record the chain. The headline statement is
`expMap_continuous`, whose signature is
`Continuous (expMap g p)`.
-/

noncomputable section

open Set Filter Topology Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

/-- The maximal geodesic `maximalGeodesic g p v` is continuous at `t = 0`.
Its value near `0` coincides with the projection of a single
Picard–Lindelöf integral curve `g_v` (via
`picardLift_proj_eq_maximalGeodesic_on_ball`), and that projection is
continuous as a base curve of an integral curve. -/
theorem maximalGeodesic_continuousAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    ContinuousAt (maximalGeodesic (I := I) g p v) 0 := by
  classical
  obtain ⟨g_v, hg0, hg_int⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) (g := g)
      (p := p) (v := v)
  have hlift_cont : ContinuousAt g_v 0 := hg_int.continuousAt
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hproj_cont : ContinuousAt (fun t => (g_v t).proj) 0 :=
    hπ_cont.continuousAt.comp hlift_cont
  obtain ⟨ε, hε, h_eq⟩ :=
    picardLift_proj_eq_maximalGeodesic_on_ball (I := I) (g := g) (p := p)
      (v := v) hg0 hg_int
  have h_eventually :
      maximalGeodesic (I := I) g p v =ᶠ[𝓝 (0 : ℝ)] fun t => (g_v t).proj := by
    have h_ball : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)
    filter_upwards [h_ball] with t ht using h_eq t ht
  exact hproj_cont.congr h_eventually.symm

/-- The image of `[0, 1]` under `maximalGeodesic g p v₀` is a compact
subset of `M`. -/
theorem bm_c_expMap_geodesicSegment_compactImage
    (g : SmoothRiemannianMetric I M) (p : M) (v₀ : TangentSpace I p) :
    IsCompact (maximalGeodesic (I := I) g p v₀ '' Set.Icc (0 : ℝ) 1) := by
  have h_cont :
      ContinuousOn (maximalGeodesic (I := I) g p v₀) (Set.Icc (0 : ℝ) 1) := by
    sorry
  exact isCompact_Icc.image_of_continuousOn h_cont

/-- For every initial velocity `v₀` there exists a radius `ρ > 0` such
that the chained flow `(v, t) ↦ maximalGeodesic g p v t` is jointly
continuous on `Metric.ball v₀ ρ × Set.Icc 0 1`. -/
theorem bm_c_expMap_chainedFlow_joint_continuity
    (g : SmoothRiemannianMetric I M) (p : M) (v₀ : TangentSpace I p) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ContinuousOn
        (fun vt : TangentSpace I p × ℝ =>
          maximalGeodesic (I := I) g p vt.1 vt.2)
        ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  sorry

/-- **Joint `C¹` regularity of the chained geodesic flow on a ball.**
For a *nonzero* initial velocity `v₀`, there is a radius `ρ > 0` such
that the chained flow `(v, t) ↦ maximalGeodesic g p v t` is jointly
`ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I 1` on
`Metric.ball v₀ ρ ×ˢ Set.Icc 0 1`.

This is the `C¹`-in-`(v, t)` strengthening of
`bm_c_expMap_chainedFlow_joint_continuity`; restricting it to the
`t = 1` slice and precomposing with the smooth slice map `w ↦ (w, 1)`
yields the off-zero exponential-map regularity
`expMap_contMDiffAt_of_ne_zero`. -/
theorem bm_c_expMap_chainedFlow_joint_contMDiff
    (g : SmoothRiemannianMetric I M) (p : M) (v₀ : E)
    (hv₀ : (show TangentSpace I p from v₀) ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I 1
        (fun vt : E × ℝ =>
          (maximalGeodesic (I := I) g p (show TangentSpace I p from vt.1) vt.2 : M))
        ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  sorry

/-- The exponential map `expMap g p : T_p M → M` is continuous.

The proof reduces continuity to `ContinuousAt (expMap g p) v₀` for each `v₀`,
then restricts the joint continuity of the chained flow
`bm_c_expMap_chainedFlow_joint_continuity` to the `t = 1` slice: since
`expMap g p v = maximalGeodesic g p v 1` by definitional unfolding of
`expMap`, continuity at `v₀` follows from the joint continuity on the
neighbourhood `ball v₀ ρ ×ˢ Icc 0 1`, precomposed with the continuous
slice map `v ↦ (v, 1)`. -/
theorem expMap_continuous
    (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (expMap (I := I) g p) := by
  rw [continuous_iff_continuousAt]
  intro v₀
  obtain ⟨ρ, hρ, hjoint⟩ :=
    bm_c_expMap_chainedFlow_joint_continuity (I := I) g p v₀
  set F : TangentSpace I p × ℝ → M :=
    fun vt => maximalGeodesic (I := I) g p vt.1 vt.2 with hF_def
  set s : TangentSpace I p → TangentSpace I p × ℝ := fun v => (v, 1) with hs_def
  have hcomp_eq : expMap (I := I) g p = F ∘ s := by
    funext v
    simp only [Function.comp_apply, hF_def, hs_def, expMap]
  rw [hcomp_eq]
  have hs_cont : Continuous s := by
    rw [hs_def]; exact continuous_id.prodMk continuous_const
  have hs_maps : Set.MapsTo s (Metric.ball v₀ ρ)
      ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro v hv
    refine ⟨hv, ?_⟩
    exact ⟨zero_le_one, le_refl 1⟩
  have hball_nhds : Metric.ball v₀ ρ ∈ 𝓝 v₀ :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)
  have hcw : ContinuousWithinAt (F ∘ s) (Metric.ball v₀ ρ) v₀ := by
    apply ContinuousOn.continuousWithinAt _ (Metric.mem_ball_self hρ)
    exact hjoint.comp hs_cont.continuousOn hs_maps
  exact hcw.continuousAt hball_nhds

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

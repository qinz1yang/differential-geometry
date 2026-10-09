import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthAngularContinuation
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleFlowFamily
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthGramDensity
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthAngularContinuation
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleGramLimit
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Gram
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthTangentMap
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorChartMetric
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleJacobiFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryJointJacobiFrame
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.VariationPairing
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorMetric
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

/-!
The actual native phase curve converges in the original manifold to its true boundary pole.
Full birth matching and actual pole flow continuity derive the physical initial point limit.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem originalPoleContinuity_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryPhase_original_birth_limit (g : SmoothRiemannianMetric I M) (p : M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      originalPoleContinuity_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ V : Opens (E × ℝ), ∀ ρ : E × ℝ → U,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V →
      (∀ q ∈ V, (ρ q : M) = (extChartAt I p).symm
        (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2)) →
      (∀ q ∈ V, HasGeodesicEquationAt k (fun r => ρ (q.1, r)) q.2) →
      ∀ (v : E) (δ a : ℝ) (σ : E → TangentBundle 𝓘(ℝ, E) U) (W : Opens E),
        v ∈ W → a ∈ Ioo 0 δ → (∀ r ∈ Ioo 0 δ, (v, r) ∈ V) →
        (∀ u ∈ W, σ u = DifferentialGeometry.velocityLift
          (I := 𝓘(ℝ, E)) (fun r => ρ (u, r)) a) →
        Tendsto (fun t : ℝ => ((boundaryPhasePoint k σ v (t - a) : U) : M))
          (𝓝[>] (0 : ℝ)) (𝓝 p) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    originalPoleContinuity_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro V ρ hρ hall hgeo v δ a σ W hv ha hbirth hseed
  have hmatch := boundaryBirth_angular_continuation k V ρ hρ hgeo σ W hv ha hbirth hseed
  have hnear : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 δ := by
    have hδ : 0 < δ := lt_trans ha.1 ha.2
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
    exact ⟨ht, htδ⟩
  have heq : (fun t : ℝ => ((boundaryPhasePoint k σ v (t - a) : U) : M)) =ᶠ[
      𝓝[>] (0 : ℝ)] (fun t => (extChartAt I p).symm
        (boundaryPoleFlowFamily G (extChartAt I p p) v t)) := by
    filter_upwards [hnear] with t ht
    have hp := congrArg (Subtype.val : U → M) (hmatch t ht).2.1
    exact hp.trans (hall (v, t) (hbirth t ht))
  have hpoint : Tendsto (boundaryPoleFlowFamily G (extChartAt I p p) v)
      (𝓝[>] (0 : ℝ)) (𝓝 (extChartAt I p p)) := by
    have hh := (boundaryPoleFlowFamily_initial G (extChartAt I p p) v).2.continuousAt.tendsto
    rw [(boundaryPoleFlowFamily_initial G (extChartAt I p p) v).1] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  have hinverse := (continuousAt_extChartAt_symm (I := I) p).tendsto.comp hpoint
  have hcenter : (extChartAt I p).symm (extChartAt I p p) = p :=
    (extChartAt I p).left_inv (mem_extChartAt_source p)
  rw [hcenter] at hinverse
  exact hinverse.congr' heq.symm

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

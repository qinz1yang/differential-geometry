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
The actual native phase frame has physical birth density divided by time squared tending to one.
Whole birth interval angular matching and genuine chart metric transport derive the pole limit.
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

private theorem phaseBirthDensity_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryPhase_birth_density_limit
    (g : SmoothRiemannianMetric I M) (p : M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (O : Opens E)
    (hG : ∀ y ∈ (O : Set E) ∩ range I, ∀ w z : E,
      G.inner y w z = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
        g p y w z) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      phaseBirthDensity_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ V : Opens (E × ℝ), ∀ ρ : E × ℝ → U,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V →
      (∀ q ∈ V, boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2 ∈
          (O : Set E) ∩ interior (extChartAt I p).target ∧
        (ρ q : M) = (extChartAt I p).symm
          (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2)) →
      (∀ q ∈ V, HasGeodesicEquationAt k (fun r => ρ (q.1, r)) q.2) →
      ∀ (v : E) (δ a : ℝ) (σ : E → TangentBundle 𝓘(ℝ, E) U) (W : Opens E),
        v ∈ W → a ∈ Ioo 0 δ → (∀ r ∈ Ioo 0 δ, (v, r) ∈ V) →
        (∀ u ∈ W, σ u = DifferentialGeometry.velocityLift
          (I := 𝓘(ℝ, E)) (fun r => ρ (u, r)) a) →
        (∀ t ∈ Ioo 0 δ, (σ v, t - a) ∈ k.geodesicFlowDomain) ∧
        ∀ e : Fin 2 → E,
          (∀ i j, G.inner (extChartAt I p p) (e i) (e j) = if i = j then 1 else 0) →
          Tendsto (fun t : ℝ => curveDensity k
            (fun r => boundaryPhasePoint k σ v (r - a))
            (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t / t ^ 2)
            (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    phaseBirthDensity_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro V ρ hρ hall hgeo v δ a σ W hv ha hbirth hseed
  have hmatch := boundaryBirth_angular_continuation k V ρ hρ hgeo σ W hv ha hbirth hseed
  have hdensity := (boundaryBirthJacobi_gram_density g p G O hG V ρ hρ hall).2
  refine ⟨fun t ht => (hmatch t ht).1, ?_⟩
  intro e hON
  have hnear : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 δ := by
    have hδ : 0 < δ := lt_trans ha.1 ha.2
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
    exact ⟨ht, htδ⟩
  have heq : (fun t : ℝ => curveDensity k
      (fun r => boundaryPhasePoint k σ v (r - a))
      (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t / t ^ 2) =ᶠ[
        𝓝[>] (0 : ℝ)]
      (fun t : ℝ => curveDensity G (boundaryPoleFlowFamily G (extChartAt I p p) v)
        (fun i r => boundaryPoleJacobiLinear G (extChartAt I p p) v r (e i)) t / t ^ 2) := by
    filter_upwards [hnear] with t ht
    have hp := (hmatch t ht).2.1
    have hcol := (hmatch t ht).2.2
    have hborn : curveDensity k (fun r => boundaryPhasePoint k σ v (r - a))
        (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t =
        curveDensity k (fun r => ρ (v, r))
          (fun i r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ v r (e i)) t := by
      unfold curveDensity
      apply congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => Real.sqrt A.det)
      ext i j
      have hc := congrArg₂ (fun w z : E => k.inner (boundaryPhasePoint k σ v (t - a)) w z)
        (hcol (e i)) (hcol (e j))
      have hb := congrArg (fun x : U => k.inner x
        (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ v t (e i) : E)
        (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ v t (e j) : E)) hp
      exact hc.trans hb
    exact congrArg (fun d : ℝ => d / t ^ 2)
      (hborn.trans (hdensity (v, t) (hbirth t ht) e))
  exact (boundaryPoleJacobiLinear_density_div_sq_tendsto G (extChartAt I p p)
    v e hON).congr' heq.symm

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

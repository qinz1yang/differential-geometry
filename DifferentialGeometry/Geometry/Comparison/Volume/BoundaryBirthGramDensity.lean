import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Gram
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthTangentMap
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorChartMetric
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleJacobiFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryJointJacobiFrame
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.VariationPairing
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorMetric
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

/-!
Actual original chart metric and angular tangent transport identify birth Gram matrices and density.
The theorem retains arbitrary genuine birth geometry, allowing the same global phase seeds.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
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

private theorem birthGram_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryBirthJacobi_gram_density
    (g : SmoothRiemannianMetric I M) (p : M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (O : Opens E)
    (hG : ∀ y ∈ (O : Set E) ∩ range I, ∀ w z : E,
      G.inner y w z = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
        g p y w z) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      birthGram_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ V : Opens (E × ℝ), ∀ ρ : E × ℝ → U,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V →
      (∀ q ∈ V, boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2 ∈
          (O : Set E) ∩ interior (extChartAt I p).target ∧
        (ρ q : M) = (extChartAt I p).symm
          (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2)) →
      (∀ q ∈ V, ∀ w z : E,
        k.inner (ρ q) (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 w)
          (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 z) =
          G.inner (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2)
            (boundaryPoleJacobiLinear G (extChartAt I p p) q.1 q.2 w)
            (boundaryPoleJacobiLinear G (extChartAt I p p) q.1 q.2 z)) ∧
      ∀ q ∈ V, ∀ e : Fin 2 → E,
        curveDensity k (fun r => ρ (q.1, r))
          (fun i r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r (e i)) q.2 =
          curveDensity G (boundaryPoleFlowFamily G (extChartAt I p p) q.1)
            (fun i r => boundaryPoleJacobiLinear G (extChartAt I p p) q.1 r (e i)) q.2 := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    birthGram_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro V ρ hρ hall
  let y := extChartAt I p p
  let F := fun x : U => extChartAt I p (x : M)
  let S := {x : U | (x : M) ∈ (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧
    F x ∈ O}
  obtain ⟨_hS, _hF, hmetric⟩ := boundaryInteriorChart_metric_isometry g p G O hG
  have hpoint (q : E × ℝ) (hq : q ∈ V) :
      F (ρ q) = boundaryPoleFlowFamily G y q.1 q.2 := by
    change extChartAt I p (ρ q : M) = _
    rw [(hall q hq).2]
    exact (extChartAt I p).right_inv (interior_subset (hall q hq).1.2)
  have hsource (q : E × ℝ) (hq : q ∈ V) : ρ q ∈ S := by
    have hx := (DifferentialGeometry.Manifold.interiorChart I ∞ p).map_target
      (hall q hq).1.2
    exact ⟨(hall q hq).2.symm ▸ hx, (hpoint q hq).symm ▸ (hall q hq).1.1⟩
  have hgram (q : E × ℝ) (hq : q ∈ V) (w z : E) :
      k.inner (ρ q) (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 w)
        (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 z) =
        G.inner (boundaryPoleFlowFamily G y q.1 q.2)
          (boundaryPoleJacobiLinear G y q.1 q.2 w)
          (boundaryPoleJacobiLinear G y q.1 q.2 z) := by
    have hm := hmetric (ρ q) (hsource q hq)
      (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 w)
      (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 z)
    have hmap := (boundaryBirthJacobi_tangent_map g p G O hG V ρ hρ hall q hq).1
    rw [hmap w, hmap z] at hm
    have hp := congrArg (fun x : E => G.inner x
      (boundaryPoleJacobiLinear (E := E) G y q.1 q.2 w : E)
      (boundaryPoleJacobiLinear (E := E) G y q.1 q.2 z : E)) (hpoint q hq)
    exact hm.trans hp
  refine ⟨hgram, ?_⟩
  intro q hq e
  unfold curveDensity
  apply congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => Real.sqrt A.det)
  ext i j
  exact hgram q hq (e i) (e j)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorChartMetric
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleJacobiFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryJointJacobiFrame
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.VariationPairing
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorMetric
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

/-!
Actual native interior angular covariant pairings equal the same genuine pole pairings.
The original point matching is differentiated on real joint opens and a chart local isometry.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem birthCovariantPairing_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryBirthJacobi_covariant_pairing
    (g : SmoothRiemannianMetric I M) (p : M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (O : Opens E)
    (hG : ∀ y ∈ (O : Set E) ∩ range I, ∀ w z : E,
      G.inner y w z = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
        g p y w z) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      birthCovariantPairing_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ V : Opens (E × ℝ), ∀ ρ : E × ℝ → U,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V →
      (∀ q ∈ V, boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2 ∈
          (O : Set E) ∩ interior (extChartAt I p).target ∧
        (ρ q : M) = (extChartAt I p).symm
          (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2)) →
      ∀ q ∈ V, ∀ w z : E,
        k.inner (ρ q)
            (covDerivAlong k (fun r => ρ (q.1, r))
              (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r w) q.2)
            (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 z) =
          G.inner (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2)
            (covDerivAlong G (boundaryPoleFlowFamily G (extChartAt I p p) q.1)
              (fun r => boundaryPoleJacobiLinear (E := E) G (extChartAt I p p) q.1 r w) q.2)
            (boundaryPoleJacobiLinear (E := E) G (extChartAt I p p) q.1 q.2 z) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    birthCovariantPairing_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro V ρ hρ hall q hq w z
  let y := extChartAt I p p
  let F := fun x : U => extChartAt I p (x : M)
  let S := {x : U | (x : M) ∈ (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧
    F x ∈ O}
  obtain ⟨hS, hF, hmetric⟩ := boundaryInteriorChart_metric_isometry g p G O hG
  have hpoint (a : E × ℝ) (ha : a ∈ V) :
      F (ρ a) = boundaryPoleFlowFamily G y a.1 a.2 := by
    change extChartAt I p (ρ a : M) = _
    rw [(hall a ha).2]
    exact (extChartAt I p).right_inv (interior_subset (hall a ha).1.2)
  have hsource : ρ q ∈ S := by
    have hx := (DifferentialGeometry.Manifold.interiorChart I ∞ p).map_target
      (hall q hq).1.2
    change (ρ q : M) ∈ (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧
      F (ρ q) ∈ O
    exact ⟨(hall q hq).2.symm ▸ hx, (hpoint q hq).symm ▸ (hall q hq).1.1⟩
  have hη := hρ.contMDiffAt (V.isOpen.mem_nhds hq)
  have hnat := inner_covDerivAlong_parameter_derivative_map_of_local_isometry_on
    k G hS hF hmetric hη hsource w z
  have htime : ∀ᶠ r in 𝓝 q.2, (q.1, r) ∈ V :=
    (V.isOpen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hq
  have hcurve : (fun r => F (ρ (q.1, r))) =ᶠ[𝓝 q.2]
      boundaryPoleFlowFamily G y q.1 := by
    filter_upwards [htime] with r hr
    exact hpoint (q.1, r) hr
  have hcolumn (u : E) (r : ℝ) (hr : (q.1, r) ∈ V) :
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun a => F (ρ (a, r))) q.1 u : E) =
        boundaryPoleJacobiLinear (E := E) G y q.1 r u := by
    have hnear : ∀ᶠ a in 𝓝 q.1, (a, r) ∈ V :=
      (V.isOpen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hr
    have heq : (fun a => F (ρ (a, r))) =ᶠ[𝓝 q.1]
        (fun a => boundaryPoleFlowFamily G y a r) := by
      filter_upwards [hnear] with a ha
      exact hpoint (a, r) ha
    have hd := heq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    exact congrArg (fun A : E →L[ℝ] E => A u) hd
  have hfield : ∀ᶠ r in 𝓝 q.2,
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun a => F (ρ (a, r))) q.1 w : E) =
        boundaryPoleJacobiLinear (E := E) G y q.1 r w := by
    filter_upwards [htime] with r hr
    exact hcolumn w r hr
  have hcov := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve G
    (fun r => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun a => F (ρ (a, r))) q.1 w)
    (fun r => boundaryPoleJacobiLinear (E := E) G y q.1 r w) hcurve hfield
  change G.inner (F (ρ q))
    (covDerivAlong G (fun r => F (ρ (q.1, r)))
      (fun r => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun a => F (ρ (a, r))) q.1 w) q.2)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun a => F (ρ (a, q.2))) q.1 z) =
      k.inner (ρ q) (covDerivAlong k (fun r => ρ (q.1, r))
        (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r w) q.2)
        (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 z) at hnat
  have hboth := congrArg₂ (fun a b : E => G.inner (F (ρ q)) a b)
    hcov (hcolumn z q.2 hq)
  have hbase := congrArg (fun a : E => G.inner a
    (covDerivAlong G (boundaryPoleFlowFamily G y q.1)
      (fun r => boundaryPoleJacobiLinear (E := E) G y q.1 r w) q.2)
    (boundaryPoleJacobiLinear (E := E) G y q.1 q.2 z)) (hpoint q hq)
  exact hnat.symm.trans (hboth.trans hbase)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

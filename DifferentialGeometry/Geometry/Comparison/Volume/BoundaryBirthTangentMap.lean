import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorChartMetric
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleJacobiFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryJointJacobiFrame
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.VariationPairing
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorMetric
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

/-!
The actual interior chart derivative maps native angular fields and velocities to the pole fields.
It also maps the genuine native covariant angular derivative using the actual local isometry.
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

private theorem birthTangentMap_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryBirthJacobi_tangent_map
    (g : SmoothRiemannianMetric I M) (p : M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (O : Opens E)
    (hG : ∀ y ∈ (O : Set E) ∩ range I, ∀ w z : E,
      G.inner y w z = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
        g p y w z) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      birthTangentMap_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    let F := fun x : U => extChartAt I p (x : M)
    ∀ V : Opens (E × ℝ), ∀ ρ : E × ℝ → U,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V →
      (∀ q ∈ V, boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2 ∈
          (O : Set E) ∩ interior (extChartAt I p).target ∧
        (ρ q : M) = (extChartAt I p).symm
          (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2)) →
      ∀ q ∈ V,
        (∀ w : E, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F (ρ q)
            (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 w) : E) =
          boundaryPoleJacobiLinear (E := E) G (extChartAt I p p) q.1 q.2 w) ∧
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F (ρ q)
            (curveVelocity (I := 𝓘(ℝ, E)) (fun r => ρ (q.1, r)) q.2) : E) =
          curveVelocity (I := 𝓘(ℝ, E))
            (boundaryPoleFlowFamily G (extChartAt I p p) q.1) q.2) ∧
        ∀ w : E, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F (ρ q)
            (covDerivAlong k (fun r => ρ (q.1, r))
              (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r w) q.2) : E) =
          covDerivAlong G (boundaryPoleFlowFamily G (extChartAt I p p) q.1)
            (fun r => boundaryPoleJacobiLinear (E := E) G (extChartAt I p p) q.1 r w) q.2 := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    birthTangentMap_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro V ρ hρ hall q hq
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
  have hsource (a : E × ℝ) (ha : a ∈ V) : ρ a ∈ S := by
    have hx := (DifferentialGeometry.Manifold.interiorChart I ∞ p).map_target
      (hall a ha).1.2
    change (ρ a : M) ∈ (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧
      F (ρ a) ∈ O
    exact ⟨(hall a ha).2.symm ▸ hx, (hpoint a ha).symm ▸ (hall a ha).1.1⟩
  have htime : ∀ᶠ r in 𝓝 q.2, (q.1, r) ∈ V :=
    (V.isOpen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hq
  have hcurve : (fun r => F (ρ (q.1, r))) =ᶠ[𝓝 q.2]
      boundaryPoleFlowFamily G y q.1 := by
    filter_upwards [htime] with r hr
    exact hpoint (q.1, r) hr
  have hcompositeColumn (u : E) (r : ℝ) (hr : (q.1, r) ∈ V) :
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
  have hmapColumn (u : E) (r : ℝ) (hr : (q.1, r) ∈ V) :
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F (ρ (q.1, r))
        (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r u) : E) =
        boundaryPoleJacobiLinear (E := E) G y q.1 r u := by
    have hslice : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun a => ρ (a, r)) q.1 :=
      (hρ.contMDiffAt (V.isOpen.mem_nhds hr)).comp q.1
        (contMDiffAt_id.prodMk contMDiffAt_const)
    have hFAt := (hF ⟨ρ (q.1, r), hsource (q.1, r) hr⟩).contMDiffAt
    have hcomp := mfderiv_comp q.1 (hFAt.mdifferentiableAt (by simp))
      (hslice.mdifferentiableAt (by simp))
    have hcompApplied := congrArg (fun A : E →L[ℝ] E => A u) hcomp
    exact hcompApplied.symm.trans (hcompositeColumn u r hr)
  have hγ : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun r => ρ (q.1, r)) q.2 :=
    (hρ.contMDiffAt (V.isOpen.mem_nhds hq)).comp q.2
      (contMDiffAt_const.prodMk contMDiffAt_id)
  have hFAt := (hF ⟨ρ q, hsource q hq⟩).contMDiffAt
  refine ⟨(fun w => hmapColumn w q.2 hq), ?_, ?_⟩
  · have hcomp := mfderiv_comp q.2 (hFAt.mdifferentiableAt (by simp))
      (hγ.mdifferentiableAt (by simp))
    have hcompApplied := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hcomp
    have hder := hcurve.mfderiv_eq (I := 𝓘(ℝ)) (I' := 𝓘(ℝ, E))
    have hderApplied := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hder
    exact hcompApplied.symm.trans hderApplied
  · intro w
    have hfield := boundaryJointJacobiLinear_smoothAt V ρ hρ q.1 w q.2 hq
    have hdiff := differentiableAt_chartRepAt_of_contMDiffAt_two
      (hfield.of_le (by norm_num))
    have hnat := covDerivAlong_map_of_local_isometry_on k G hS hF hmetric
      (fun r => ρ (q.1, r))
      (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r w)
      (hsource q hq) hγ hdiff
    have hmapped : ∀ᶠ r in 𝓝 q.2,
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F (ρ (q.1, r))
          (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r w) : E) =
          boundaryPoleJacobiLinear (E := E) G y q.1 r w := by
      filter_upwards [htime] with r hr
      exact hmapColumn w r hr
    have hcov := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve G
      (fun r => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F (ρ (q.1, r))
        (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r w))
      (fun r => boundaryPoleJacobiLinear (E := E) G y q.1 r w) hcurve hmapped
    exact hnat.trans hcov

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

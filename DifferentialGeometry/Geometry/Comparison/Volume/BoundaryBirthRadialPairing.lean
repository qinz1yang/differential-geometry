import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthTangentMap
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPolePerpendicular
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Speed
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleJacobiFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryJointJacobiFrame
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.VariationPairing
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorMetric
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

/-!
The actual native interior angular field and its covariant derivative have radial pole pairings.
Actual chart metric and derivative identities derive these from the genuine pole geodesic field.
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

private theorem birthRadialPairing_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryBirthJacobi_radial_pairing
    (g : SmoothRiemannianMetric I M) (p : M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (O : Opens E)
    (hG : ∀ y ∈ (O : Set E) ∩ range I, ∀ w z : E,
      G.inner y w z = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
        g p y w z) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      birthRadialPairing_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ V : Opens (E × ℝ), ∀ ρ : E × ℝ → U,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V →
      (∀ q ∈ V,
        ((⟨extChartAt I p p, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈
          G.geodesicFlowDomain ∧
        boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2 ∈
          (O : Set E) ∩ interior (extChartAt I p).target ∧
        (ρ q : M) = (extChartAt I p).symm
          (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2)) →
      ∀ q ∈ V, ∀ w : E,
        k.inner (ρ q) (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 w)
            (curveVelocity (I := 𝓘(ℝ, E)) (fun r => ρ (q.1, r)) q.2) =
          q.2 * G.inner (extChartAt I p p) w q.1 ∧
        k.inner (ρ q)
            (covDerivAlong k (fun r => ρ (q.1, r))
              (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r w) q.2)
            (curveVelocity (I := 𝓘(ℝ, E)) (fun r => ρ (q.1, r)) q.2) =
          G.inner (extChartAt I p p) w q.1 := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    birthRadialPairing_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro V ρ hρ hall q hq w
  let y := extChartAt I p p
  let F := fun x : U => extChartAt I p (x : M)
  obtain ⟨_hS, _hF, hmetric⟩ := boundaryInteriorChart_metric_isometry g p G O hG
  have hpoint : F (ρ q) = boundaryPoleFlowFamily G y q.1 q.2 := by
    change extChartAt I p (ρ q : M) = _
    rw [(hall q hq).2.2]
    exact (extChartAt I p).right_inv (interior_subset (hall q hq).2.1.2)
  have hsource : (ρ q : M) ∈ (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧
      F (ρ q) ∈ O := by
    have hx := (DifferentialGeometry.Manifold.interiorChart I ∞ p).map_target
      (hall q hq).2.1.2
    exact ⟨(hall q hq).2.2.symm ▸ hx, hpoint.symm ▸ (hall q hq).2.1.1⟩
  have hmap := boundaryBirthJacobi_tangent_map g p G O hG V ρ hρ
    (fun a ha => (hall a ha).2) q hq
  let γ := fun r => ρ (q.1, r)
  let J := fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r w
  let Γ := boundaryPoleFlowFamily G y q.1
  let P := fun r => boundaryPoleJacobiLinear (E := E) G y q.1 r w
  have hleft := hmetric (ρ q) hsource (J q.2) (curveVelocity (I := 𝓘(ℝ, E)) γ q.2)
  have hright := hmetric (ρ q) hsource (covDerivAlong k γ J q.2)
    (curveVelocity (I := 𝓘(ℝ, E)) γ q.2)
  have hleftMap := congrArg₂ (fun a b : E => G.inner (F (ρ q)) a b)
    (hmap.1 w) hmap.2.1
  have hrightMap := congrArg₂ (fun a b : E => G.inner (F (ρ q)) a b)
    (hmap.2.2 w) hmap.2.1
  have hleftPoint := congrArg (fun a : E => G.inner a (P q.2)
    (curveVelocity (I := 𝓘(ℝ, E)) Γ q.2)) hpoint
  have hrightPoint := congrArg (fun a : E => G.inner a (covDerivAlong G Γ P q.2)
    (curveVelocity (I := 𝓘(ℝ, E)) Γ q.2)) hpoint
  have hpole := boundaryPoleJacobiLinear_velocity_pairing G y q.1 w q.2 (hall q hq).1
  exact ⟨(hleft.trans (hleftMap.trans hleftPoint)).trans hpole.1,
    (hright.trans (hrightMap.trans hrightPoint)).trans hpole.2⟩

theorem boundaryBirthJacobi_perpendicular
    (g : SmoothRiemannianMetric I M) (p : M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (O : Opens E)
    (hG : ∀ y ∈ (O : Set E) ∩ range I, ∀ w z : E,
      G.inner y w z = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
        g p y w z) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      birthRadialPairing_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ V : Opens (E × ℝ), ∀ ρ : E × ℝ → U,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V →
      (∀ q ∈ V,
        ((⟨extChartAt I p p, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈
          G.geodesicFlowDomain ∧
        boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2 ∈
          (O : Set E) ∩ interior (extChartAt I p).target ∧
        (ρ q : M) = (extChartAt I p).symm
          (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2)) →
      ∀ q ∈ V, ∀ w : E, G.inner (extChartAt I p p) w q.1 = 0 →
        k.inner (ρ q) (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 w)
            (curveVelocity (I := 𝓘(ℝ, E)) (fun r => ρ (q.1, r)) q.2) =
          0 ∧
        k.inner (ρ q)
            (covDerivAlong k (fun r => ρ (q.1, r))
              (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 r w) q.2)
            (curveVelocity (I := 𝓘(ℝ, E)) (fun r => ρ (q.1, r)) q.2) =
          0 := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    birthRadialPairing_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro V ρ hρ hall q hq w hperp
  have hh := boundaryBirthJacobi_radial_pairing g p G O hG V ρ hρ hall q hq w
  simpa only [hperp, mul_zero] using hh

theorem boundaryBirth_velocity_norm
    (g : SmoothRiemannianMetric I M) (p : M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (O : Opens E)
    (hG : ∀ y ∈ (O : Set E) ∩ range I, ∀ w z : E,
      G.inner y w z = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
        g p y w z) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      birthRadialPairing_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ V : Opens (E × ℝ), ∀ ρ : E × ℝ → U,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V →
      (∀ q ∈ V,
        ((⟨extChartAt I p p, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈
          G.geodesicFlowDomain ∧
        boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2 ∈
          (O : Set E) ∩ interior (extChartAt I p).target ∧
        (ρ q : M) = (extChartAt I p).symm
          (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2)) →
      ∀ q ∈ V, k.inner (ρ q)
          (curveVelocity (I := 𝓘(ℝ, E)) (fun r => ρ (q.1, r)) q.2)
          (curveVelocity (I := 𝓘(ℝ, E)) (fun r => ρ (q.1, r)) q.2) =
        G.inner (extChartAt I p p) q.1 q.1 := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    birthRadialPairing_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro V ρ hρ hall q hq
  let y := extChartAt I p p
  let F := fun x : U => extChartAt I p (x : M)
  obtain ⟨_hS, _hF, hmetric⟩ := boundaryInteriorChart_metric_isometry g p G O hG
  have hpoint : F (ρ q) = boundaryPoleFlowFamily G y q.1 q.2 := by
    change extChartAt I p (ρ q : M) = _
    rw [(hall q hq).2.2]
    exact (extChartAt I p).right_inv (interior_subset (hall q hq).2.1.2)
  have hsource : (ρ q : M) ∈ (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧
      F (ρ q) ∈ O := by
    have hx := (DifferentialGeometry.Manifold.interiorChart I ∞ p).map_target
      (hall q hq).2.1.2
    exact ⟨(hall q hq).2.2.symm ▸ hx, hpoint.symm ▸ (hall q hq).2.1.1⟩
  have hmap := boundaryBirthJacobi_tangent_map g p G O hG V ρ hρ
    (fun a ha => (hall a ha).2) q hq
  let γ := fun r => ρ (q.1, r)
  let Γ := boundaryPoleFlowFamily G y q.1
  have hmetricNorm := hmetric (ρ q) hsource
    (curveVelocity (I := 𝓘(ℝ, E)) γ q.2) (curveVelocity (I := 𝓘(ℝ, E)) γ q.2)
  have hnormMap := congrArg₂ (fun a b : E => G.inner (F (ρ q)) a b)
    hmap.2.1 hmap.2.1
  have hnormPoint := congrArg (fun a : E => G.inner a
    (curveVelocity (I := 𝓘(ℝ, E)) Γ q.2) (curveVelocity (I := 𝓘(ℝ, E)) Γ q.2)) hpoint
  let seed : TangentBundle 𝓘(ℝ, E) E := ⟨y, q.1⟩
  have hMF := G.hasMFDerivAt_geodesicFlow_proj (r := ⊤) le_top (hall q hq).1
  have hvel : (curveVelocity (I := 𝓘(ℝ, E)) Γ q.2 : E) =
      (G.geodesicFlow seed q.2).snd := by
    have hh := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hMF.mfderiv
    change (curveVelocity (I := 𝓘(ℝ, E)) Γ q.2 : E) =
      (1 : ℝ) • (G.geodesicFlow seed q.2).snd at hh
    simpa only [one_smul] using hh
  have henergy := G.inner_geodesicFlow_eq (r := ⊤) le_top seed q.2 (hall q hq).1
  have hvelInner := congrArg₂ (fun a b : E => G.inner (Γ q.2) a b) hvel hvel
  exact (hmetricNorm.trans (hnormMap.trans hnormPoint)).trans (hvelInner.trans henergy)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

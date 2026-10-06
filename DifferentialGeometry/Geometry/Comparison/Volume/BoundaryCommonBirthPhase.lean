import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhaseRadialFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhaseBirthDensity
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
The same original common pole family has an actual native phase frame with full birth data.
Physical density limits coexist with all native time speed, perpendicularity and Jacobi data.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]


private theorem commonBirthPhase_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem exists_boundary_common_birth_phase_frame (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      commonBirthPhase_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∃ G : SmoothRiemannianMetric 𝓘(ℝ, E) E, RiemannianMetricComplete G ∧
      ∃ O : Opens E, extChartAt I p p ∈ O ∧
        (∀ y ∈ (O : Set E) ∩ range I, ∀ z w : E,
          G.inner y z w = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
            g p y z w) ∧
        ∃ V : Opens (E × ℝ), ∃ ρ : E × ℝ → U,
          ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V ∧
          (∀ q ∈ V,
            ((⟨extChartAt I p p, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈
              G.geodesicFlowDomain ∧
            boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2 ∈
              (O : Set E) ∩ interior (extChartAt I p).target ∧
            (ρ q : M) = (extChartAt I p).symm
              (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2) ∧
            HasGeodesicEquationAt k (fun t => ρ (q.1, t)) q.2) ∧
          ∀ v : E, (∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
            v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) →
            ∃ δ : ℝ, 0 < δ ∧ ∃ a ∈ Ioo 0 δ,
              ∃ σ : E → TangentBundle 𝓘(ℝ, E) U,
              ∃ W : Opens E, ∃ ε : ℝ, v ∈ W ∧ 0 < ε ∧
                ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ W ∧
                (∀ u ∈ W, (u, a) ∈ V ∧ (σ u).proj = ρ (u, a)) ∧
                (∀ u ∈ W, ∀ r ∈ Metric.ball (0 : ℝ) ε,
                  (σ u, r) ∈ k.geodesicFlowDomain ∧
                  boundaryPhasePoint k σ u r = ρ (u, r + a) ∧
                  ∀ w : E, (boundaryPhaseJacobiLinear k σ u r w : E) =
                    boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (r + a) w) ∧
                (∀ u ∈ W, σ u = DifferentialGeometry.velocityLift
                  (I := 𝓘(ℝ, E)) (fun r => ρ (u, r)) a) ∧
                (∀ t ∈ Ioo 0 δ, (σ v, t - a) ∈ k.geodesicFlowDomain ∧
                  boundaryPhasePoint k σ v (t - a) = ρ (v, t) ∧
                  ∀ w : E, (boundaryPhaseJacobiLinear k σ v (t - a) w : E) =
                    boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ v t w) ∧
                (∀ e : Fin 2 → E,
                  (∀ i j, G.inner (extChartAt I p p) (e i) (e j) = if i = j then 1 else 0) →
                  Tendsto (fun t : ℝ => curveDensity k
                    (fun r => boundaryPhasePoint k σ v (r - a))
                    (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t / t ^ 2)
                    (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ))) ∧
                ∀ u ∈ W, ∀ t : ℝ, (σ u, t) ∈ k.geodesicFlowDomain →
                  k.inner (boundaryPhasePoint k σ u t)
                      (curveVelocity (I := 𝓘(ℝ, E)) (fun r => boundaryPhasePoint k σ u r) t)
                      (curveVelocity (I := 𝓘(ℝ, E)) (fun r => boundaryPhasePoint k σ u r) t) =
                    G.inner (extChartAt I p p) u u ∧
                  (∀ w : E, G.inner (extChartAt I p p) w u = 0 →
                    k.inner (boundaryPhasePoint k σ u t) (boundaryPhaseJacobiLinear k σ u t w)
                        (curveVelocity (I := 𝓘(ℝ, E)) (fun r => boundaryPhasePoint k σ u r) t) = 0 ∧
                      k.inner (boundaryPhasePoint k σ u t)
                        (covDerivAlong k (fun r => boundaryPhasePoint k σ u r)
                          (fun r => boundaryPhaseJacobiLinear k σ u r w) t)
                        (curveVelocity (I := 𝓘(ℝ, E)) (fun r => boundaryPhasePoint k σ u r) t)
                        = 0) ∧
                  (∀ w z : E, jacobiWronskian k (fun r => boundaryPhasePoint k σ u r)
                    (fun r => boundaryPhaseJacobiLinear k σ u r w)
                    (fun r => boundaryPhaseJacobiLinear k σ u r z) t = 0) ∧
                  ∀ w : E, IsJacobiAt k (fun r => boundaryPhasePoint k σ u r)
                      (fun r => boundaryPhaseJacobiLinear k σ u r w) t ∧
                    ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞
                      (fun r => (⟨boundaryPhasePoint k σ u r, boundaryPhaseJacobiLinear k σ u r w⟩ :
                        TangentBundle 𝓘(ℝ, E) U)) t := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    commonBirthPhase_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  obtain ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, _hJac, hWr, hbirth⟩ :=
    exists_boundary_common_wronskian_frame g p b hb
  let y := extChartAt I p p
  have hdata : ∀ q ∈ V,
      ((⟨y, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈ G.geodesicFlowDomain ∧
      boundaryPoleFlowFamily G y q.1 q.2 ∈ (O : Set E) ∩ interior (extChartAt I p).target ∧
      (ρ q : M) = (extChartAt I p).symm (boundaryPoleFlowFamily G y q.1 q.2) :=
    fun q hq => ⟨(hall q hq).1, (hall q hq).2.1, (hall q hq).2.2.1⟩
  have hnorm := boundaryBirth_velocity_norm g p G O hG V ρ hρ hdata
  have hbornPair := boundaryBirthJacobi_radial_pairing g p G O hG V ρ hρ hdata
  refine ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, ?_⟩
  intro v hin
  obtain ⟨δ, hδ, hentry⟩ := hbirth v hin
  let a := δ / 2
  have ha : (v, a) ∈ V := hentry a ⟨by dsimp only [a]; linarith,
    by dsimp only [a]; linarith⟩
  obtain ⟨σ, W, ε, hv, hε, hσ, hseed, hmatch, hseedVel, hjet⟩ :=
    boundaryBirth_phase_initial_frame g V ρ hρ
      (fun q hq => (hall q hq).2.2.2) v a ha
  have haI : a ∈ Ioo 0 δ :=
    ⟨by dsimp only [a]; linarith, by dsimp only [a]; linarith⟩
  have hlift (u : E) (hu : u ∈ W) : σ u = DifferentialGeometry.velocityLift
      (I := 𝓘(ℝ, E)) (fun r => ρ (u, r)) a := by
    apply Bundle.TotalSpace.ext (hseed u hu).2
    exact heq_of_eq (hseedVel u hu)
  have hfullBirth := boundaryBirth_angular_continuation k V ρ hρ
    (fun q hq => (hall q hq).2.2.2) σ W hv haI hentry hlift
  have hlimit := (boundaryPhase_birth_density_limit g p G O hG V ρ hρ
    (fun q hq => ⟨(hall q hq).2.1, (hall q hq).2.2.1⟩)
    (fun q hq => (hall q hq).2.2.2) v δ a σ W hv haI hentry hlift).2
  refine ⟨δ, hδ, a, haI, σ, W, ε, hv, hε, hσ, hseed, hmatch, hlift,
    hfullBirth, hlimit, ?_⟩
  intro u hu t ht
  let γ := fun r => boundaryPhasePoint k σ u r
  let γ₀ := fun r => ρ (u, r)
  let J := fun (w : E) (r : ℝ) => boundaryPhaseJacobiLinear k σ u r w
  let P := fun (w : E) (r : ℝ) => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r w
  have hzero := k.geodesicFlow_zero (r := ⊤) le_top (σ u)
  have hpoint : γ 0 = ρ (u, a) :=
    (congrArg (fun x : TangentBundle 𝓘(ℝ, E) U => x.proj) hzero).trans (hseed u hu).2
  have hvelocity : (curveVelocity (I := 𝓘(ℝ, E)) γ 0 : E) =
      curveVelocity (I := 𝓘(ℝ, E)) γ₀ a :=
    (boundaryPhasePoint_velocity k σ u 0
      (k.mem_geodesicFlowDomain_zero (r := ⊤) le_top (σ u))).trans
      ((congrArg (fun x : TangentBundle 𝓘(ℝ, E) U => (x.snd : E)) hzero).trans (hseedVel u hu))
  have hleft (w : E) : k.inner (γ 0) (J w 0) (curveVelocity (I := 𝓘(ℝ, E)) γ 0) =
      a * G.inner y w u := by
    have hm := congrArg₂ (fun x z : E => k.inner (γ 0) x z) (hjet u hu w).1 hvelocity
    have hp := congrArg (fun x : U => k.inner x (P w a)
      (curveVelocity (I := 𝓘(ℝ, E)) γ₀ a)) hpoint
    exact (hm.trans hp).trans (hbornPair (u, a) (hseed u hu).1 w).1
  have hright (w : E) : k.inner (γ 0) (covDerivAlong k γ (J w) 0)
      (curveVelocity (I := 𝓘(ℝ, E)) γ 0) = G.inner y w u := by
    have hm := congrArg₂ (fun x z : E => k.inner (γ 0) x z) (hjet u hu w).2 hvelocity
    have hp := congrArg (fun x : U => k.inner x (covDerivAlong k γ₀ (P w) a)
      (curveVelocity (I := 𝓘(ℝ, E)) γ₀ a)) hpoint
    exact (hm.trans hp).trans (hbornPair (u, a) (hseed u hu).1 w).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm := congrArg₂ (fun x z : E => k.inner (σ u).proj x z)
      (hseedVel u hu) (hseedVel u hu)
    have hp := congrArg (fun x : U => k.inner x
      (curveVelocity (I := 𝓘(ℝ, E)) γ₀ a) (curveVelocity (I := 𝓘(ℝ, E)) γ₀ a)) (hseed u hu).2
    exact (boundaryPhasePoint_velocity_norm k σ u t ht).trans
      ((hm.trans hp).trans (hnorm (u, a) (hseed u hu).1))
  · intro w hperp
    have hh := boundaryPhaseJacobiLinear_radial_pairing k W σ hσ u hu w t ht
    have hzeroLeft : k.inner (γ 0) (J w 0)
        (curveVelocity (I := 𝓘(ℝ, E)) γ 0) = 0 :=
      (hleft w).trans ((congrArg (fun x : ℝ => a * x) hperp).trans (mul_zero a))
    have hzeroRight : k.inner (γ 0) (covDerivAlong k γ (J w) 0)
        (curveVelocity (I := 𝓘(ℝ, E)) γ 0) = 0 := (hright w).trans hperp
    have hzeroAffine : k.inner (γ 0) (J w 0)
        (curveVelocity (I := 𝓘(ℝ, E)) γ 0) +
        t * k.inner (γ 0) (covDerivAlong k γ (J w) 0)
          (curveVelocity (I := 𝓘(ℝ, E)) γ 0) = 0 := by
      calc
        _ = (0 : ℝ) + t * 0 :=
          congrArg₂ (fun x z : ℝ => x + t * z) hzeroLeft hzeroRight
        _ = 0 := by ring
    exact ⟨hh.1.trans hzeroAffine, hh.2.trans hzeroRight⟩
  · intro w z
    have hl := congrArg₂ (fun x z : E => k.inner (γ 0) x z)
      (hjet u hu w).2 (hjet u hu z).1
    have hr := congrArg₂ (fun x z : E => k.inner (γ 0) x z)
      (hjet u hu w).1 (hjet u hu z).2
    have hlp := congrArg (fun x : U => k.inner x (covDerivAlong k γ₀ (P w) a) (P z a)) hpoint
    have hrp := congrArg (fun x : U => k.inner x (P w a) (covDerivAlong k γ₀ (P z) a)) hpoint
    have hinit : jacobiWronskian k γ (J w) (J z) 0 =
        jacobiWronskian k γ₀ (P w) (P z) a :=
      congrArg₂ (fun x z : ℝ => x - z) (hl.trans hlp) (hr.trans hrp)
    exact (boundaryPhaseJacobiLinear_wronskian_constant k W σ hσ u hu w z t ht).trans
      (hinit.trans (hWr (u, a) (hseed u hu).1 w z))
  · intro w
    exact boundaryPhaseJacobiLinear_jacobi k W σ hσ u hu w t ht


end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

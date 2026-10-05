import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthPhaseContinuation
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthWronskianFrame
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AffineReparam

/-!
Actual native phase angular Wronskians are conserved on their genuine maximal flow intervals.
The original common birth family's zero invariant will therefore propagate through real phase flow.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]

section NativePhase

variable {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundaryless : I.Boundaryless] {N : Type*} [interiorTopology : TopologicalSpace N]
  [interiorCharts : ChartedSpace H N] [interiorSmooth : IsManifold I ∞ N]
  [interiorT2 : T2Space N]

theorem boundaryPhaseJacobiLinear_wronskian_constant (g : SmoothRiemannianMetric I N)
    (W : Opens E) (σ : E → TangentBundle I N)
    (hσ : ContMDiffOn 𝓘(ℝ, E) I.tangent ∞ σ W) (v : E) (hv : v ∈ W)
    (w z : E) (t : ℝ) (ht : (σ v, t) ∈ g.geodesicFlowDomain) :
    jacobiWronskian g (fun r => boundaryPhasePoint g σ v r)
        (fun r => boundaryPhaseJacobiLinear g σ v r w)
        (fun r => boundaryPhaseJacobiLinear g σ v r z) t =
      jacobiWronskian g (fun r => boundaryPhasePoint g σ v r)
        (fun r => boundaryPhaseJacobiLinear g σ v r w)
        (fun r => boundaryPhaseJacobiLinear g σ v r z) 0 := by
  let γ := fun r => boundaryPhasePoint g σ v r
  let s := maximalIntegralCurveInterval g.geodesicSpray (σ v)
  have hzero : (0 : ℝ) ∈ s := g.mem_geodesicFlowDomain_zero (r := ⊤) le_top _
  have hs : Convex ℝ s := ordConnected_maximalIntegralCurveInterval.convex
  have hfield (u : E) (a : ℝ) (ha : a ∈ s) :
      ContMDiffAt 𝓘(ℝ) I.tangent ∞
        (fun r => (⟨γ r, boundaryPhaseJacobiLinear g σ v r u⟩ : TangentBundle I N)) a :=
    (boundaryPhaseJacobiLinear_jacobi g W σ hσ v hv u a ha).2
  have hγ (a : ℝ) (ha : a ∈ s) : ContMDiffAt 𝓘(ℝ) I 1 γ a :=
    ((contMDiff_proj (TangentSpace I : N → Type _)).contMDiffAt.comp a
      (hfield 0 a ha)).of_le (by norm_num)
  have hJ (u : E) (a : ℝ) (ha : a ∈ s) :
      MDifferentiableAt 𝓘(ℝ) I.tangent
        (fun r => (⟨γ r, boundaryPhaseJacobiLinear g σ v r u⟩ : TangentBundle I N)) a :=
    (hfield u a ha).mdifferentiableAt (by simp)
  have hDJ (u : E) (a : ℝ) (ha : a ∈ s) :
      MDifferentiableAt 𝓘(ℝ) I.tangent
        (fun r => (⟨γ r, covDerivAlong g γ
          (fun r => boundaryPhaseJacobiLinear g σ v r u) r⟩ : TangentBundle I N)) a := by
    have hregular := contMDiffAt_covDerivAlong g (m := 1) (n := 2)
      (by norm_num) ((hfield u a ha).of_le (by norm_num))
    exact hregular.mdifferentiableAt (by norm_num)
  have hJac (u : E) (a : ℝ) (ha : a ∈ interior s) :
      IsJacobiAt g γ (fun r => boundaryPhaseJacobiLinear g σ v r u) a := by
    have ham : a ∈ s := interior_subset ha
    exact (boundaryPhaseJacobiLinear_jacobi g W σ hσ v hv u a ham).1
  exact jacobiWronskian_eq_of_isJacobiAt g γ
    (fun r => boundaryPhaseJacobiLinear g σ v r w)
    (fun r => boundaryPhaseJacobiLinear g σ v r z)
    hs hγ (hJ w) (hJ z) (hDJ w) (hDJ z) (hJac w) (hJac z) (a := 0) (t := t) hzero ht

end NativePhase

section OriginalBirth

open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem phaseWronskian_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem exists_boundary_common_phase_wronskian (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      phaseWronskian_infty_ne_zero (M := M)
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
            ∃ a : ℝ, 0 < a ∧ ∃ σ : E → TangentBundle 𝓘(ℝ, E) U,
              ∃ W : Opens E, ∃ ε : ℝ, v ∈ W ∧ 0 < ε ∧
                ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ W ∧
                (∀ u ∈ W, (u, a) ∈ V ∧ (σ u).proj = ρ (u, a)) ∧
                (∀ u ∈ W, ∀ r ∈ Metric.ball (0 : ℝ) ε,
                  (σ u, r) ∈ k.geodesicFlowDomain ∧
                  boundaryPhasePoint k σ u r = ρ (u, r + a) ∧
                  ∀ w : E, (boundaryPhaseJacobiLinear k σ u r w : E) =
                    boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (r + a) w) ∧
                ∀ u ∈ W, ∀ w z : E, ∀ t : ℝ, (σ u, t) ∈ k.geodesicFlowDomain →
                  jacobiWronskian k (fun r => boundaryPhasePoint k σ u r)
                    (fun r => boundaryPhaseJacobiLinear k σ u r w)
                    (fun r => boundaryPhaseJacobiLinear k σ u r z) t = 0 := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    phaseWronskian_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  obtain ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, _hJac, hWr, hbirth⟩ :=
    exists_boundary_common_wronskian_frame g p b hb
  refine ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, ?_⟩
  intro v hin
  obtain ⟨δ, hδ, hentry⟩ := hbirth v hin
  let a := δ / 2
  have ha : (v, a) ∈ V := hentry a ⟨by dsimp only [a]; linarith,
    by dsimp only [a]; linarith⟩
  obtain ⟨σ, W, ε, hv, hε, hσ, hseed, hmatch, _hPhaseJac⟩ :=
    boundaryBirth_phase_continuation g V ρ hρ
      (fun q hq => (hall q hq).2.2.2) v a ha
  refine ⟨a, by dsimp only [a]; linarith, σ, W, ε, hv, hε, hσ, hseed, hmatch, ?_⟩
  intro u hu w z t ht
  have hball : (0 : ℝ) ∈ Metric.ball 0 ε := by simpa using hε
  have hcurve : (fun r => boundaryPhasePoint k σ u r) =ᶠ[𝓝 (0 : ℝ)]
      (fun r => ρ (u, r + a)) :=
    eventually_of_mem (Metric.isOpen_ball.mem_nhds hball)
      (fun r hr => (hmatch u hu r hr).2.1)
  have hcov (d : E) : covDerivAlong k (fun r => boundaryPhasePoint k σ u r)
      (fun r => boundaryPhaseJacobiLinear k σ u r d) 0 =
      covDerivAlong k (fun r => ρ (u, r))
        (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r d) a := by
    have hfield : ∀ᶠ r in 𝓝 (0 : ℝ), (boundaryPhaseJacobiLinear k σ u r d : E) =
        boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (r + a) d :=
      eventually_of_mem (Metric.isOpen_ball.mem_nhds hball)
        (fun r hr => (hmatch u hu r hr).2.2 d)
    have htransport := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve k
      (fun r => boundaryPhaseJacobiLinear k σ u r d)
      (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (r + a) d) hcurve hfield
    have hshift := DifferentialGeometry.Geometry.Riemannian.covDeriv_comp_affine k
      (fun r => ρ (u, r))
      (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r d) 1 a 0
    have hshiftLiteral : covDerivAlong k (fun r => ρ (u, r + a))
        (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (r + a) d) 0 =
        covDerivAlong k (fun r => ρ (u, r))
          (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r d) a := by
      have hcurveShift : (fun r => ρ (u, 1 * r + a)) =ᶠ[𝓝 (0 : ℝ)]
          (fun r => ρ (u, r + a)) := Eventually.of_forall (fun r =>
        congrArg (fun t : ℝ => ρ (u, t))
          (congrArg (fun t : ℝ => t + a) (one_mul r)))
      have hfieldShift : ∀ᶠ r in 𝓝 (0 : ℝ),
          (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (1 * r + a) d : E) =
            boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (r + a) d :=
        Eventually.of_forall (fun r => congrArg
          (fun t : ℝ => (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u t d : E))
          (congrArg (fun t : ℝ => t + a) (one_mul r)))
      have hleft := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve k
        (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (1 * r + a) d)
        (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (r + a) d)
        hcurveShift hfieldShift
      have htime : (1 : ℝ) * 0 + a = a := by ring
      have hright : (1 : ℝ) • covDerivAlong k (fun r => ρ (u, r))
          (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r d) (1 * 0 + a) =
          covDerivAlong k (fun r => ρ (u, r))
            (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r d) a :=
        (one_smul ℝ _).trans (congrArg (fun t : ℝ =>
          (covDerivAlong k (fun r => ρ (u, r))
            (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r d) t : E)) htime)
      exact hleft.symm.trans (hshift.trans hright)
    exact htransport.trans hshiftLiteral
  have hpoint : boundaryPhasePoint k σ u 0 = ρ (u, a) := by
    simpa only [zero_add] using (hmatch u hu 0 hball).2.1
  have hfield (d : E) : (boundaryPhaseJacobiLinear k σ u 0 d : E) =
      boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u a d := by
    exact ((hmatch u hu 0 hball).2.2 d).trans (congrArg
      (fun r : ℝ => (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r d : E))
      (zero_add a))
  let γ := fun r => boundaryPhasePoint k σ u r
  let Jw := fun r => boundaryPhaseJacobiLinear k σ u r w
  let Jz := fun r => boundaryPhaseJacobiLinear k σ u r z
  let γ₀ := fun r => ρ (u, r)
  let Pw := fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r w
  let Pz := fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r z
  have hleft := congrArg₂ (fun x y : E => k.inner (γ 0) x y) (hcov w) (hfield z)
  have hright := congrArg₂ (fun x y : E => k.inner (γ 0) x y) (hfield w) (hcov z)
  have hleftPoint := congrArg (fun x : U => k.inner x
    (covDerivAlong k γ₀ Pw a) (Pz a)) hpoint
  have hrightPoint := congrArg (fun x : U => k.inner x
    (Pw a) (covDerivAlong k γ₀ Pz a)) hpoint
  have hinitial : jacobiWronskian k γ Jw Jz 0 = jacobiWronskian k γ₀ Pw Pz a :=
    congrArg₂ (fun x y : ℝ => x - y) (hleft.trans hleftPoint) (hright.trans hrightPoint)
  exact (boundaryPhaseJacobiLinear_wronskian_constant k W σ hσ u hu w z t ht).trans
    (hinitial.trans (hWr (u, a) (hseed u hu).1 w z))

end OriginalBirth

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

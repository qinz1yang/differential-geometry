import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthPhaseContinuation
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AffineReparam

/-!
The constructed native phase seeds have the actual birth velocity and angular covariant jet.
Actual common point and field matching yields initial data by genuine affine time transport.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem birthPhaseInitial_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryBirth_phase_initial_frame (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      birthPhaseInitial_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ V : Opens (E × ℝ), ∀ ρ : E × ℝ → U,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V →
      (∀ q ∈ V, HasGeodesicEquationAt k (fun r => ρ (q.1, r)) q.2) →
      ∀ (v₀ : E) (a : ℝ), (v₀, a) ∈ V →
        ∃ σ : E → TangentBundle 𝓘(ℝ, E) U, ∃ W : Opens E, ∃ ε : ℝ,
          v₀ ∈ W ∧ 0 < ε ∧ ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ W ∧
          (∀ v ∈ W, (v, a) ∈ V ∧ (σ v).proj = ρ (v, a)) ∧
          (∀ v ∈ W, ∀ s ∈ Metric.ball (0 : ℝ) ε,
            (σ v, s) ∈ k.geodesicFlowDomain ∧
            boundaryPhasePoint k σ v s = ρ (v, s + a) ∧
            ∀ w : E, (boundaryPhaseJacobiLinear k σ v s w : E) =
              boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ v (s + a) w) ∧
          (∀ u ∈ W, ((σ u).snd : E) =
            curveVelocity (I := 𝓘(ℝ, E)) (fun r => ρ (u, r)) a) ∧
          ∀ u ∈ W, ∀ w : E,
            (boundaryPhaseJacobiLinear k σ u 0 w : E) =
                boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u a w ∧
              covDerivAlong k (fun r => boundaryPhasePoint k σ u r)
                  (fun r => boundaryPhaseJacobiLinear k σ u r w) 0 =
                covDerivAlong k (fun r => ρ (u, r))
                  (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r w) a := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    birthPhaseInitial_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro V ρ hρ hgeo v₀ a hva
  obtain ⟨σ, W, ε, hv, hε, hσ, hseed, hmatch, _hJac⟩ :=
    boundaryBirth_phase_continuation g V ρ hρ hgeo v₀ a hva
  have hball : (0 : ℝ) ∈ Metric.ball 0 ε := by simpa using hε
  have hcurve (u : E) (hu : u ∈ W) : (fun r => boundaryPhasePoint k σ u r) =ᶠ[𝓝 (0 : ℝ)]
      (fun r => ρ (u, r + a)) :=
    eventually_of_mem (Metric.isOpen_ball.mem_nhds hball)
      (fun r hr => (hmatch u hu r hr).2.1)
  refine ⟨σ, W, ε, hv, hε, hσ, hseed, hmatch, ?_, ?_⟩
  · intro u hu
    have hder := (hcurve u hu).mfderiv_eq (I := 𝓘(ℝ)) (I' := 𝓘(ℝ, E))
    have hphaseShift := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hder
    have hcurveShift : (fun r => ρ (u, 1 * r + a)) =ᶠ[𝓝 (0 : ℝ)]
        (fun r => ρ (u, r + a)) := Eventually.of_forall (fun r =>
      congrArg (fun t : ℝ => ρ (u, t))
        (congrArg (fun t : ℝ => t + a) (one_mul r)))
    have hshiftDer := hcurveShift.mfderiv_eq (I := 𝓘(ℝ)) (I' := 𝓘(ℝ, E))
    have hshiftVelocity := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hshiftDer
    have hγ : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun r => ρ (u, r)) a :=
      (hρ.contMDiffAt (V.isOpen.mem_nhds (hseed u hu).1)).comp a
        (contMDiffAt_const.prodMk contMDiffAt_id)
    have htime : (1 : ℝ) * 0 + a = a := by ring
    have hγAffine : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) (fun r => ρ (u, r)) (1 * 0 + a) :=
      htime.symm ▸ hγ.mdifferentiableAt (by simp)
    have hvelocityAffine := DifferentialGeometry.Geometry.Riemannian.curveVelocity_comp_affine
      (I := 𝓘(ℝ, E)) (fun r => ρ (u, r)) 1 a 0 hγAffine
    have hright : (1 : ℝ) • curveVelocity (I := 𝓘(ℝ, E)) (fun r => ρ (u, r))
        (1 * 0 + a) = curveVelocity (I := 𝓘(ℝ, E)) (fun r => ρ (u, r)) a :=
      (one_smul ℝ _).trans (congrArg (fun t : ℝ =>
        (curveVelocity (I := 𝓘(ℝ, E)) (fun r => ρ (u, r)) t : E)) htime)
    have hphaseBorn := hphaseShift.trans (hshiftVelocity.symm.trans
      (hvelocityAffine.trans hright))
    have hMF := k.hasMFDerivAt_geodesicFlow_proj (r := ⊤) le_top
      (k.mem_geodesicFlowDomain_zero (r := ⊤) le_top (σ u))
    have hMFVelocity := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hMF.mfderiv
    change (curveVelocity (I := 𝓘(ℝ, E)) (fun r => boundaryPhasePoint k σ u r) 0 : E) =
      (1 : ℝ) • (k.geodesicFlow (σ u) 0).snd at hMFVelocity
    have hzero := k.geodesicFlow_zero (r := ⊤) le_top (σ u)
    have hzeroVelocity := congrArg (fun x : TangentBundle 𝓘(ℝ, E) U => (x.snd : E)) hzero
    have hphaseSeed := hMFVelocity.trans ((one_smul ℝ _).trans hzeroVelocity)
    exact hphaseSeed.symm.trans hphaseBorn
  · intro u hu w
    refine ⟨((hmatch u hu 0 hball).2.2 w).trans (congrArg
      (fun r : ℝ => (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r w : E))
      (zero_add a)), ?_⟩
    have hfield : ∀ᶠ r in 𝓝 (0 : ℝ), (boundaryPhaseJacobiLinear k σ u r w : E) =
        boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (r + a) w :=
      eventually_of_mem (Metric.isOpen_ball.mem_nhds hball)
        (fun r hr => (hmatch u hu r hr).2.2 w)
    have htransport := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve k
      (fun r => boundaryPhaseJacobiLinear k σ u r w)
      (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (r + a) w) (hcurve u hu) hfield
    have hshift := DifferentialGeometry.Geometry.Riemannian.covDeriv_comp_affine k
      (fun r => ρ (u, r))
      (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r w) 1 a 0
    have hshiftLiteral : covDerivAlong k (fun r => ρ (u, r + a))
        (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (r + a) w) 0 =
        covDerivAlong k (fun r => ρ (u, r))
          (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r w) a := by
      have hcurveShift : (fun r => ρ (u, 1 * r + a)) =ᶠ[𝓝 (0 : ℝ)]
          (fun r => ρ (u, r + a)) := Eventually.of_forall (fun r =>
        congrArg (fun t : ℝ => ρ (u, t))
          (congrArg (fun t : ℝ => t + a) (one_mul r)))
      have hfieldShift : ∀ᶠ r in 𝓝 (0 : ℝ),
          (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (1 * r + a) w : E) =
            boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (r + a) w :=
        Eventually.of_forall (fun r => congrArg
          (fun t : ℝ => (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u t w : E))
          (congrArg (fun t : ℝ => t + a) (one_mul r)))
      have hleft := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve k
        (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (1 * r + a) w)
        (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u (r + a) w)
        hcurveShift hfieldShift
      have htime : (1 : ℝ) * 0 + a = a := by ring
      have hright : (1 : ℝ) • covDerivAlong k (fun r => ρ (u, r))
          (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r w) (1 * 0 + a) =
          covDerivAlong k (fun r => ρ (u, r))
            (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r w) a :=
        (one_smul ℝ _).trans (congrArg (fun t : ℝ =>
          (covDerivAlong k (fun r => ρ (u, r))
            (fun r => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ u r w) t : E)) htime)
      exact hleft.symm.trans (hshift.trans hright)
    exact htransport.trans hshiftLiteral

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

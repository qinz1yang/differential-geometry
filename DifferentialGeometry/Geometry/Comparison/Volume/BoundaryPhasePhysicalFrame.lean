import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhaseRadialFrame
import DifferentialGeometry.Geometry.Comparison.Variation.JacobiReparam
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SmoothSpray

/-!
Actual native phase flow and its angular Jacobi fields retain their equations in physical time.
Literal affine time transport derives velocities, smooth bundles and covariant derivatives.
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
  {N : Type*} [nativeTopology : TopologicalSpace N] [nativeCharts : ChartedSpace E N]
  [nativeSmooth : IsManifold 𝓘(ℝ, E) ∞ N] [nativeT2 : T2Space N]

private theorem phaseSeed_geodesic (g : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    (seed : TangentBundle 𝓘(ℝ, E) N) (t : ℝ) (ht : (seed, t) ∈ g.geodesicFlowDomain) :
    HasGeodesicEquationAt g (fun r => (g.geodesicFlow seed r).proj) t := by
  obtain ⟨x, w⟩ := seed
  exact ((g.isGeodesicOnWithInitial_geodesicFlow x w).isGeodesicAt
    (isOpen_maximalIntegralCurveInterval.mem_nhds ht)).hasGeodesicEquationAt

theorem boundaryPhase_physical_geodesic (g : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    (W : Opens E) (σ : E → TangentBundle 𝓘(ℝ, E) N)
    (hσ : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ W) (v : E) (hv : v ∈ W) (a : ℝ) :
    ∀ t : ℝ, (σ v, t - a) ∈ g.geodesicFlowDomain →
      ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun r => boundaryPhasePoint g σ v (r - a)) t ∧
      HasGeodesicEquationAt g (fun r => boundaryPhasePoint g σ v (r - a)) t ∧
      (curveVelocity (I := 𝓘(ℝ, E)) (fun r => boundaryPhasePoint g σ v (r - a)) t : E) =
        curveVelocity (I := 𝓘(ℝ, E)) (fun r => boundaryPhasePoint g σ v r) (t - a) := by
  intro t ht
  let Γ := fun r => boundaryPhasePoint g σ v r
  obtain ⟨hD, hpoint⟩ := boundaryPhasePoint_smooth g W σ hσ
  have hΓ : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ Γ (t - a) :=
    (hpoint.contMDiffAt (hD.mem_nhds ⟨hv, ht⟩)).comp (t - a)
      (contMDiffAt_const.prodMk contMDiffAt_id)
  have hshift : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ (fun r : ℝ => r - a) t :=
    contMDiffAt_id.sub contMDiffAt_const
  have htime : (1 : ℝ) * t + -a = t - a := by ring
  have hgeo : HasGeodesicEquationAt g Γ (1 * t + -a) :=
    htime.symm ▸ phaseSeed_geodesic g (σ v) (t - a) ht
  have hphysical : HasGeodesicEquationAt g (fun r => Γ (r - a)) t := by
    simpa only [one_mul, sub_eq_add_neg] using hasGeodesicEquationAt_comp_affine hgeo
  refine ⟨hΓ.comp (f := fun r : ℝ => r - a) t hshift, hphysical, ?_⟩
  have hcurve : (fun r => Γ (1 * r + -a)) =ᶠ[𝓝 t] (fun r => Γ (r - a)) :=
    Eventually.of_forall (fun r => congrArg Γ (by ring : (1 : ℝ) * r + -a = r - a))
  have hder := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ))
    (hcurve.mfderiv_eq (I := 𝓘(ℝ)) (I' := 𝓘(ℝ, E)))
  have hMDiff : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) Γ (1 * t + -a) :=
    htime.symm ▸ hΓ.mdifferentiableAt (by simp)
  have hvelocity := DifferentialGeometry.Geometry.Riemannian.curveVelocity_comp_affine
    (I := 𝓘(ℝ, E)) Γ 1 (-a) t hMDiff
  have hright : (1 : ℝ) • curveVelocity (I := 𝓘(ℝ, E)) Γ (1 * t + -a) =
      curveVelocity (I := 𝓘(ℝ, E)) Γ (t - a) :=
    (one_smul ℝ _).trans (congrArg (fun r : ℝ =>
      (curveVelocity (I := 𝓘(ℝ, E)) Γ r : E)) htime)
  exact hder.symm.trans (hvelocity.trans hright)

theorem boundaryPhase_physical_jacobi (g : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    (W : Opens E) (σ : E → TangentBundle 𝓘(ℝ, E) N)
    (hσ : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ W) (v : E) (hv : v ∈ W) (a : ℝ) :
    ∀ w : E, ∀ t : ℝ, (σ v, t - a) ∈ g.geodesicFlowDomain →
      IsJacobiAt g (fun r => boundaryPhasePoint g σ v (r - a))
        (fun r => boundaryPhaseJacobiLinear g σ v (r - a) w) t ∧
      ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞
        (fun r => (⟨boundaryPhasePoint g σ v (r - a),
          boundaryPhaseJacobiLinear g σ v (r - a) w⟩ : TangentBundle 𝓘(ℝ, E) N)) t ∧
      covDerivAlong g (fun r => boundaryPhasePoint g σ v (r - a))
        (fun r => boundaryPhaseJacobiLinear g σ v (r - a) w) t =
        covDerivAlong g (fun r => boundaryPhasePoint g σ v r)
          (fun r => boundaryPhaseJacobiLinear g σ v r w) (t - a) := by
  intro w t ht
  let Γ := fun r => boundaryPhasePoint g σ v r
  let J := fun r => boundaryPhaseJacobiLinear g σ v r w
  obtain ⟨hD, hpoint⟩ := boundaryPhasePoint_smooth g W σ hσ
  have hΓ : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ Γ (t - a) :=
    (hpoint.contMDiffAt (hD.mem_nhds ⟨hv, ht⟩)).comp (t - a)
      (contMDiffAt_const.prodMk contMDiffAt_id)
  have hshift : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ (fun r : ℝ => r - a) t :=
    contMDiffAt_id.sub contMDiffAt_const
  have htime : (1 : ℝ) * t + -a = t - a := by ring
  obtain ⟨hJ, hbundle⟩ := boundaryPhaseJacobiLinear_jacobi g W σ hσ v hv w (t - a) ht
  have hJac : IsJacobiAt g Γ J (1 * t + -a) := htime.symm ▸ hJ
  have hMDiff : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) Γ (1 * t + -a) :=
    htime.symm ▸ hΓ.mdifferentiableAt (by simp)
  have hstate : (fun r => (⟨Γ (1 * r + -a), J (1 * r + -a)⟩ :
      TangentBundle 𝓘(ℝ, E) N)) =ᶠ[𝓝 t]
      (fun r => (⟨Γ (r - a), J (r - a)⟩ : TangentBundle 𝓘(ℝ, E) N)) :=
    Eventually.of_forall (fun r => congrArg
      (fun s : ℝ => (⟨Γ s, J s⟩ : TangentBundle 𝓘(ℝ, E) N))
      (by ring : (1 : ℝ) * r + -a = r - a))
  have hphysical : IsJacobiAt g (fun r => Γ (r - a)) (fun r => J (r - a)) t :=
    (hJac.comp_affine hMDiff).congr_of_eventuallyEq hstate
  refine ⟨hphysical, hbundle.comp (f := fun r : ℝ => r - a) t hshift, ?_⟩
  have hcurve : (fun r => Γ (1 * r + -a)) =ᶠ[𝓝 t] (fun r => Γ (r - a)) :=
    Eventually.of_forall (fun r => congrArg Γ (by ring : (1 : ℝ) * r + -a = r - a))
  have hfield : ∀ᶠ r in 𝓝 t, (J (1 * r + -a) : E) = J (r - a) :=
    Eventually.of_forall (fun r => congrArg (fun s : ℝ => (J s : E))
      (by ring : (1 : ℝ) * r + -a = r - a))
  have htransport := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve g
    (fun r => J (1 * r + -a)) (fun r => J (r - a)) hcurve hfield
  have hcov := DifferentialGeometry.Geometry.Riemannian.covDeriv_comp_affine g Γ J 1 (-a) t
  have hright : (1 : ℝ) • covDerivAlong g Γ J (1 * t + -a) =
      covDerivAlong g Γ J (t - a) :=
    (one_smul ℝ _).trans (congrArg (fun r : ℝ => (covDerivAlong g Γ J r : E)) htime)
  exact htransport.symm.trans (hcov.trans hright)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

import DifferentialGeometry.Geometry.Connection.PullbackScaling
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling

noncomputable section

open Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V]

theorem pullbackFiberwiseLinearEquiv_scaleMetric_apply
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (φ : ∀ x, V x ≃ₗ[ℝ] TangentSpace I x)
    (hφ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, E)) 1
      (fun p : TotalSpace F V => (⟨p.1, φ p.1 p.2⟩ : TangentBundle I M)))
    {σ : ∀ x, V x} {x : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) x)
    (X : TangentSpace I x) :
    let a := (Real.sqrt c)⁻¹
    let ha : a ≠ 0 := inv_ne_zero (Real.sqrt_ne_zero'.mpr hc)
    let ψ := fun y => (φ y).trans (LinearEquiv.smulOfNeZero ℝ (TangentSpace I y) a ha)
    let hψ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, E)) 1
      (fun p : TotalSpace F V => (⟨p.1, ψ p.1 p.2⟩ : TangentBundle I M)) := by
        simpa only [ψ, LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply] using
          (contMDiff_const.smul_bundle hφ :
            ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, E)) 1
              (fun p : TotalSpace F V => (⟨p.1, a • φ p.1 p.2⟩ : TangentBundle I M)))
    pullbackFiberwiseLinearEquiv ψ hψ (leviCivitaConnectionOfMetric (scaleMetric c hc g)) σ x X =
      pullbackFiberwiseLinearEquiv φ hφ (leviCivitaConnectionOfMetric g) σ x X := by
  dsimp only
  rw [lcConn_scaleMetric]
  apply pullbackFiberwiseLinearEquiv_apply_eq_of_const_smul φ hφ (leviCivitaConnectionOfMetric g)
    ((Real.sqrt c)⁻¹) _ _ _ hσ X
  intro y v
  simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply]

end CovariantDerivative

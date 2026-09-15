import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CalculusGeometryFrontier
import DifferentialGeometry.Geometry.Submanifold.IsometricImmersionGauss
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.OpenImmersion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle Function Manifold Set Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion
open DifferentialGeometry.Geometry.Riemannian.Geodesic (chartChristoffelContraction)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem hasAmbientGaussEquation_iff_hasGaussEquation [I.Boundaryless] {m : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (himmersion : IsRiemannianIsometricImmersion h g (fun y : U => F y)) :
    hasAmbientGaussEquation U F g h ↔ himmersion.hasGaussEquation := by
  constructor
  · intro hgauss x X Y Z W
    have h1 := hgauss x X Y Z W
    rw [← mfderiv_restrict_open F U x] at h1
    simp only [] at h1 ⊢
    simp only [
      secondFundamentalFormAt_coe_eq_ambient himmersion x X W,
      secondFundamentalFormAt_coe_eq_ambient himmersion x Y Z,
      secondFundamentalFormAt_coe_eq_ambient himmersion x X Z,
      secondFundamentalFormAt_coe_eq_ambient himmersion x Y W] at h1 ⊢
    exact h1
  · intro hgauss x X Y Z W
    have h1 := hgauss x X Y Z W
    rw [mfderiv_restrict_open F U x] at h1
    simp only [] at h1 ⊢
    simp only [
      secondFundamentalFormAt_coe_eq_ambient himmersion x X W,
      secondFundamentalFormAt_coe_eq_ambient himmersion x Y Z,
      secondFundamentalFormAt_coe_eq_ambient himmersion x X Z,
      secondFundamentalFormAt_coe_eq_ambient himmersion x Y W] at h1 ⊢
    exact h1

omit [CompleteSpace E] in
theorem immersionSecondFundamental_inner_mfderiv_eq_zero [I.Boundaryless] {m : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (hF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ F U)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (himmersion : IsRiemannianIsometricImmersion h g (fun y : U => F y))
    (x : U) (X Y Z : EuclideanSpace ℝ (Fin m)) :
    g.inner (F x) (immersionSecondFundamental U F g h x X Y)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x Z) = 0 := by
  have hchart := immersionSecondFundamental_eq_secondFundamentalFormAmbientAt_of_contMDiffOn U F hF g h
  rw [hchart x X Y, ← mfderiv_restrict_open F U x]
  exact IsRiemannianIsometricImmersion.secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero
    himmersion x X Y Z

omit [CompleteSpace E] in
theorem isometricImmersionPullbackConnection_of_isRiemannianIsometricImmersion [I.Boundaryless]
    {m : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (hF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ F U)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (himmersion : IsRiemannianIsometricImmersion h g (fun y : U => F y)) :
    IsometricImmersionPullbackConnection g F U h := by
  refine (isometricImmersionPullbackConnection_iff_secondFundamentalForm_orthogonal g F U h
    (fun x X Y => ?_)).mpr ?_
  · rw [← mfderiv_restrict_open F U x]
    exact (himmersion.inner_map x X Y).symm
  intro x X Y Z
  have h := immersionSecondFundamental_inner_mfderiv_eq_zero U F hF g h himmersion x X Y Z
  simp only [immersionSecondFundamental] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

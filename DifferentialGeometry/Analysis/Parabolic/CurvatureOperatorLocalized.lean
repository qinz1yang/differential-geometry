import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.LocalizedEigenvalue
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionAlgebra

noncomputable section

open Bundle CovariantDerivative Filter Set
open DifferentialGeometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology InnerProductSpace

open DifferentialGeometry.Geometry.Curvature.DimensionThree
namespace DifferentialGeometry.Analysis.Parabolic

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

private theorem curvatureOperatorReactionEndomorphism3_apply_of_least_eigenvector
    (hdim : Module.finrank ℝ V = 3) (A : V →L[ℝ] V)
    (hA : A.toLinearMap.IsSymmetric) {v : V}
    (hv : A v = (⨅ w : {w : V // w ≠ 0}, A.rayleighQuotient w) • v) :
    curvatureOperatorReactionEndomorphism3 A.toLinearMap v =
      ((⨅ w : {w : V // w ≠ 0}, A.rayleighQuotient w) ^ 2 +
        hA.eigenvalues hdim 0 * hA.eigenvalues hdim 1) • v := by
  have hmin := hA.iInf_rayleighQuotient_eq_eigenvalues_last (n := 2) hdim
  have he : Fin.last 2 = (2 : Fin 3) := rfl
  rw [he] at hmin
  rw [hmin] at hv ⊢
  exact curvatureOperatorReactionEndomorphism3_apply_of_eigenvalues_last hdim A.toLinearMap hA hv

private theorem curvatureOperatorReactionEndomorphism3_inner_of_least_eigenvector
    (hdim : Module.finrank ℝ V = 3) (A : V →L[ℝ] V)
    (hA : A.toLinearMap.IsSymmetric) {v : V} (hunit : ‖v‖ = 1)
    (hv : A v = (⨅ w : {w : V // w ≠ 0}, A.rayleighQuotient w) • v) :
    inner ℝ (curvatureOperatorReactionEndomorphism3 A.toLinearMap v) v =
      (⨅ w : {w : V // w ≠ 0}, A.rayleighQuotient w) ^ 2 +
        hA.eigenvalues hdim 0 * hA.eigenvalues hdim 1 := by
  rw [curvatureOperatorReactionEndomorphism3_apply_of_least_eigenvector hdim A hA hv]
  simp only [real_inner_smul_left, real_inner_self_eq_norm_sq, hunit, one_pow, mul_one]

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem cutoff_negative_minimum_eigenvalue_reaction_inequality_at_spacetime_max
    [NeZero (Module.finrank ℝ E)]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    {t : ℝ} (ht : 0 < t)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (x : M) (hx : I.IsInteriorPoint x)
    (X : ℝ → (y : M) → TangentSpace I y)
    (hGconn : G.connection t = LeviCivita (I := I) (G.metric t))
    (hdim : Module.finrank ℝ (V x) = 3)
    (hPDE : letI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
      HasDerivWithinAt (fun s => A s x)
        (rawBundleEndomorphismConnLap (I := I) (G.metric t) cov (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
            (fun y => A t y) x (X t x) +
          (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap)
        (Icc 0 t) t)
    (hA : (A t x).toLinearMap.IsSymmetric)
    (hneg : (⨅ v : {v : V x // v ≠ 0}, (A t x).rayleighQuotient v) < 0)
    (χ φ : ℝ → M → ℝ)
    (hφχ : ∀ᶠ p in 𝓝[Icc 0 t ×ˢ (Set.univ : Set M)] (t, x),
      0 ≤ φ p.1 p.2 ∧ φ p.1 p.2 ≤ χ p.1 p.2)
    (hφeq : φ t x = χ t x)
    (hφtime : DifferentiableWithinAt ℝ (fun q => φ q x) (Icc 0 t) t)
    (hφspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y)
    (hφgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (φ t) y) x)
    (hmax : IsLocalMaxOn (fun p : ℝ × M => χ p.1 p.2 *
      max (-(⨅ w : {w : V p.2 // w ≠ 0}, (A p.1 p.2).rayleighQuotient w)) 0)
      (Icc 0 t ×ˢ (Set.univ : Set M)) (t, x)) :
    letI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
    let ν := ⨅ w : {w : V x // w ≠ 0}, (A t x).rayleighQuotient w
    φ t x ^ 2 * (ν ^ 2 + hA.eigenvalues hdim 0 * hA.eigenvalues hdim 1) +
      ν * φ t x * parabolicOperatorWithDrift (I := I) G t X φ t x +
      2 * ν * (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
        (gradientAt (I := I) G t (φ t) x) ≤ 0 := by
  let : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  obtain ⟨v, _, hunit, heigen, hineq⟩ :=
    exists_cutoff_negative_minimum_eigenvalue_parabolic_inequality_at_spacetime_max
      (I := I) G cov hcov ht A x hx X hGconn hPDE.differentiableWithinAt hA hneg
      χ φ hφχ hφeq hφtime hφspace hφgrad hmax
  have hder := hPDE.derivWithin ((uniqueDiffOn_Icc ht).uniqueDiffWithinAt ⟨ht.le, le_rfl⟩)
  rw [hder] at hineq
  have hres :
      rawBundleEndomorphismConnLap (I := I) (G.metric t) cov (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
            (fun y => A t y) x (X t x) +
          (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap -
        rawBundleEndomorphismConnLap (I := I) (G.metric t) cov (fun y => A t y) x -
        HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
          (fun y => A t y) x (X t x) =
      (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap := by
    abel
  rw [hres] at hineq
  have hreact := curvatureOperatorReactionEndomorphism3_inner_of_least_eigenvector
    hdim (A t x) hA hunit.self_of_nhds heigen
  change inner ℝ
    ((curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap
      (v x)) (v x) = _ at hreact
  rw [hreact] at hineq
  exact hineq

end DifferentialGeometry.Analysis.Parabolic

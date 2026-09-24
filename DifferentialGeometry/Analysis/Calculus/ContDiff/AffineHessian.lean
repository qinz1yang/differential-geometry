import DifferentialGeometry.Analysis.Calculus.ContDiff.AffineDerivative
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear


namespace DifferentialGeometry.Analysis.Calculus

open scoped ContDiff

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_of_affine_hessian_components
    (b : Module.Basis ι ℝ E) {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : DifferentiableOn ℝ u U)
    (hdu : DifferentiableOn ℝ (fderiv ℝ u) U)
    {A : ι → ι → E → ℝ} {Γ : ι → ι → ι → E → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (A i j) U)
    (hΓ : ∀ i j k, ContDiffOn ℝ ∞ (Γ i j k) U)
    (heq : ∀ y ∈ U, ∀ i j,
      fderiv ℝ (fderiv ℝ u) y (b i) (b j) =
        A i j y + ∑ k, Γ i j k y * fderiv ℝ u y (b k)) :
    ContDiffOn ℝ ∞ u U := by
  classical
  let _ : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  let _ : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let _ : NormedAddCommGroup
      ((E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ
      ((E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let c : ι → E →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  let q : ι → ι → E →L[ℝ] E →L[ℝ] ℝ := fun i j =>
    (c i).smulRight (c j)
  let r : ι → ι → ι → (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
    fun i j k => (ContinuousLinearMap.apply ℝ ℝ (b k)).smulRight (q i j)
  let a : E → E →L[ℝ] E →L[ℝ] ℝ :=
    fun y => ∑ i, ∑ j, A i j y • q i j
  let γ : E → (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
    fun y => ∑ i, ∑ j, ∑ k, Γ i j k y • r i j k
  have hq : ∀ i j, ContDiffOn ℝ ∞ (fun _ : E => q i j) U :=
    fun i j => contDiffOn_const
  have hr : ∀ i j k, ContDiffOn ℝ ∞ (fun _ : E => r i j k) U :=
    fun i j k => contDiffOn_const
  have ha : ContDiffOn ℝ ∞ a U := by
    dsimp only [a]
    exact ContDiffOn.sum fun i _ =>
      ContDiffOn.sum fun j _ => (hA i j).smul (hq i j)
  have hγ : ContDiffOn ℝ ∞ γ U := by
    dsimp only [γ]
    exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      ContDiffOn.sum fun k _ => (hΓ i j k).smul (hr i j k)
  have hc_apply (i p : ι) : c i (b p) = if p = i then 1 else 0 := by
    simp [c, Module.Basis.coord_apply, Finsupp.single_apply]
  have hA_apply (y : E) (i j : ι) : a y (b i) (b j) = A i j y := by
    simp [a, q, c, sum_apply, smul_apply, hc_apply, smul_eq_mul, mul_ite]
  have hΓ_apply (y : E) (v : E →L[ℝ] ℝ) (i j : ι) :
      γ y v (b i) (b j) = ∑ k, Γ i j k y * v (b k) := by
    simp [γ, r, q, c, sum_apply, smul_apply, hc_apply, smul_eq_mul, mul_ite]
  have hderiv : Set.EqOn (fderiv ℝ (fderiv ℝ u))
      (fun y => a y + γ y (fderiv ℝ u y)) U := by
    intro y hy
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro i
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro j
    change fderiv ℝ (fderiv ℝ u) y (b i) (b j) =
      (a y + γ y (fderiv ℝ u y)) (b i) (b j)
    simpa only [add_apply, hA_apply, hΓ_apply] using heq y hy i j
  have hdu_smooth : ContDiffOn ℝ ∞ (fderiv ℝ u) U :=
    contDiffOn_of_fderiv_eq_add_clm_apply hU hdu hderiv ha hγ
  exact (contDiffOn_infty_iff_fderiv_of_isOpen hU).mpr ⟨hu, hdu_smooth⟩

end DifferentialGeometry.Analysis.Calculus

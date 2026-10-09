import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory

/-!
A coefficient comparison for the actual weak Dirichlet replacement. The second
coefficient can be the constant matrix frozen at the center of a ball. The proof
uses the existing weak stability theorem and preserves both supplied solutions
and their exact Sobolev trace. No pointwise gradient regularity is asserted.
-/

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace

namespace DifferentialGeometry.Analysis

open DeGiorgi

variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

private theorem bilinForm_sub_coeff_bound
    {Ω : Set E} (A B : EllipticCoeff d Ω) {u v : E → ℝ}
    (hu : MemW1pWitness 2 u Ω) (hv : MemW1pWitness 2 v Ω)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ᵐ x ∂volume.restrict Ω, ∀ ξ : E,
      ‖matMulE (A.a x) ξ - matMulE (B.a x) ξ‖ ≤ ε * ‖ξ‖) :
    |bilinFormOfCoeff A hu hv - bilinFormOfCoeff B hu hv| ≤
      ε * (∫ x, ‖hu.weakGrad x‖ ^ (2 : ℝ) ∂volume.restrict Ω) ^ (1 / (2 : ℝ)) *
        (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂volume.restrict Ω) ^ (1 / (2 : ℝ)) := by
  let μ := volume.restrict Ω
  have hint : Integrable
      (fun x => bilinFormIntegrandOfCoeff A hu hv x -
        bilinFormIntegrandOfCoeff B hu hv x) μ :=
    (integrable_bilinFormIntegrandOfCoeff A hu hv).sub
      (integrable_bilinFormIntegrandOfCoeff B hu hv)
  have hdom : Integrable (fun x => ε * (‖hu.weakGrad x‖ * ‖hv.weakGrad x‖)) μ :=
    (hu.weakGrad_memLp.norm.integrable_mul hv.weakGrad_memLp.norm).const_mul ε
  have hpoint : ∀ᵐ x ∂μ,
      ‖bilinFormIntegrandOfCoeff A hu hv x - bilinFormIntegrandOfCoeff B hu hv x‖ ≤
        ε * (‖hu.weakGrad x‖ * ‖hv.weakGrad x‖) := by
    filter_upwards [hosc] with x hx
    change |⟪matMulE (A.a x) (hu.weakGrad x), hv.weakGrad x⟫_ℝ -
      ⟪matMulE (B.a x) (hu.weakGrad x), hv.weakGrad x⟫_ℝ| ≤ _
    rw [← inner_sub_left]
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_right (hx (hu.weakGrad x))
        (norm_nonneg (hv.weakGrad x))).trans_eq (mul_assoc _ _ _))
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (f := hu.weakGrad) (g := hv.weakGrad)
    Real.HolderConjugate.two_two
    (show MemLp hu.weakGrad (ENNReal.ofReal (2 : ℝ)) μ by
      simpa using hu.weakGrad_memLp)
    (show MemLp hv.weakGrad (ENNReal.ofReal (2 : ℝ)) μ by
      simpa using hv.weakGrad_memLp)
  calc
    |bilinFormOfCoeff A hu hv - bilinFormOfCoeff B hu hv| =
        ‖∫ x, (bilinFormIntegrandOfCoeff A hu hv x -
          bilinFormIntegrandOfCoeff B hu hv x) ∂μ‖ := by
      unfold bilinFormOfCoeff
      rw [integral_sub (integrable_bilinFormIntegrandOfCoeff A hu hv)
        (integrable_bilinFormIntegrandOfCoeff B hu hv), Real.norm_eq_abs]
    _ ≤ ∫ x, ‖bilinFormIntegrandOfCoeff A hu hv x -
        bilinFormIntegrandOfCoeff B hu hv x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ε * (‖hu.weakGrad x‖ * ‖hv.weakGrad x‖) ∂μ :=
      integral_mono_ae hint.norm hdom hpoint
    _ = ε * ∫ x, ‖hu.weakGrad x‖ * ‖hv.weakGrad x‖ ∂μ := integral_const_mul _ _
    _ ≤ ε * ((∫ x, ‖hu.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hholder hε
    _ = _ := (mul_assoc _ _ _).symm

/-- The same-trace weak `B`-harmonic replacement differs from the supplied weak
`A`-harmonic function by at most the coefficient oscillation divided by the
coercivity constant of `B`, in the actual `L²` gradient seminorm. In the frozen
coefficient application, `B.a` is the constant matrix `A.a c` on the ball.
No regularity or nonvanishing of either gradient is assumed or concluded. -/
theorem weakGrad_l2_sub_le_of_coefficient_oscillation
    {Ω : Set E} (hΩ : IsOpen Ω) (A B : EllipticCoeff d Ω)
    {u h : E → ℝ} (hu : IsHomogeneousWeakSolution A u)
    (hh : IsHomogeneousWeakSolution B h)
    (htrace : MemW01p 2 (fun x => h x - u x) Ω)
    (wu : MemW1pWitness 2 u Ω) (wh : MemW1pWitness 2 h Ω)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ᵐ x ∂volume.restrict Ω, ∀ ξ : E,
      ‖matMulE (A.a x) ξ - matMulE (B.a x) ξ‖ ≤ ε * ‖ξ‖) :
    (∫ x, ‖wh.weakGrad x - wu.weakGrad x‖ ^ (2 : ℝ) ∂volume.restrict Ω) ^
        (1 / (2 : ℝ)) ≤
      (ε / B.lam) *
        (∫ x, ‖wu.weakGrad x‖ ^ (2 : ℝ) ∂volume.restrict Ω) ^ (1 / (2 : ℝ)) := by
  classical
  let wadd : MemW1pWitness 2 (fun x => h x + (-1) * u x) Ω :=
    wh.add (wu.smul (-1))
  let wd : MemW1pWitness 2 (fun x => h x - u x) Ω := {
    memLp := by simpa only [neg_one_mul, sub_eq_add_neg] using wadd.memLp
    weakGrad := wadd.weakGrad
    weakGrad_component_memLp := wadd.weakGrad_component_memLp
    isWeakGrad := by
      intro i
      simpa only [neg_one_mul, sub_eq_add_neg] using wadd.isWeakGrad i }
  let rhs : (E → ℝ) → ℝ := fun φ =>
    if hφ : MemW1p 2 φ Ω then
      bilinFormOfCoeff A wu hφ.someWitness - bilinFormOfCoeff B wu hφ.someWitness
    else 0
  have hrhs (φ : E → ℝ) (hφ : MemH01 φ Ω) (wφ : MemW1pWitness 2 φ Ω) :
      rhs φ = bilinFormOfCoeff A wu wφ - bilinFormOfCoeff B wu wφ := by
    dsimp only [rhs]
    rw [dite_eq_left hφ.memW1p,
      bilinFormOfCoeff_eq_right hΩ A wu _ wφ,
      bilinFormOfCoeff_eq_right hΩ B wu _ wφ]
  have hbound (φ : E → ℝ) (hφ : MemH01 φ Ω) (wφ : MemW1pWitness 2 φ Ω) :
      |rhs φ| ≤ (ε * ‖gradLpOfWitness wu‖) *
        (∫ x, ‖wφ.weakGrad x‖ ^ (2 : ℝ) ∂volume.restrict Ω) ^ (1 / (2 : ℝ)) := by
    rw [hrhs φ hφ wφ, norm_gradLpOfWitness_eq]
    exact bilinForm_sub_coeff_bound A B wu wφ hε hosc
  have hws : bilinFormOfCoeff B wd wd = rhs (fun x => h x - u x) := by
    rw [hrhs _ htrace wd, hu.2 wu _ htrace wd]
    change bilinFormOfCoeff B (wh.add (wu.smul (-1))) wd =
      0 - bilinFormOfCoeff B wu wd
    rw [bilinFormOfCoeff_add_left, bilinFormOfCoeff_smul_left,
      hh.2 wh _ htrace wd]
    ring
  have hstab := weakSolution_stability B htrace wd
    (rhs := rhs) (C_F := ε * ‖gradLpOfWitness wu‖)
    (mul_nonneg hε (norm_nonneg _)) hbound hws
  have hgrad : wd.weakGrad = fun x => wh.weakGrad x - wu.weakGrad x := by
    funext x
    simp only [wd, wadd, MemW1pWitness.add,
      MemW1pWitness.smul, neg_one_smul, sub_eq_add_neg]
  rw [hgrad] at hstab
  simpa only [norm_gradLpOfWitness_eq, div_eq_mul_inv, mul_assoc, mul_comm,
    mul_left_comm] using hstab

end DifferentialGeometry.Analysis

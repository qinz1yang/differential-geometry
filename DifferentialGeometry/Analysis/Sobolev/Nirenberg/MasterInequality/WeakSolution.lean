import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.Localization
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.WeakSolution
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.SubstitutionNonSmooth
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Localization

noncomputable section

open MeasureTheory
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitutionNonSmooth
  (principal_term_ge_lambda_norm_sq_nonsmooth)

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_extension_nirenberg_master_inequality
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : MemW1pWitness 2 u Omega)
    (hweak : ∀ v, MemH01 v Omega →
      ∀ hv : MemW1pWitness 2 v Omega,
        bilinFormOfCoeff A hu hv =
          ∫ x in Omega, f x * v x ∂(volume : Measure E))
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : rho ≠ 0)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta)
    {R₀ : ℝ}
    (hK_Omega : Metric.cthickening R₀ (tsupport eta) ⊆ Omega)
    (hcoeff : ∀ x ∈ Metric.cthickening R₀ (tsupport eta),
      ∀ i j : Fin d, A.a x i j = rho * B.a x i j)
    (k : Fin d) :
    ∃ (U : E → ℝ) (hU : MemW1pWitness 2 U Set.univ),
      (∀ x ∈ Metric.cthickening R₀ (tsupport eta), U x = u x) ∧
      (∀ x ∈ Metric.cthickening R₀ (tsupport eta), ∀ i : Fin d,
        hU.weakGrad x i = hu.weakGrad x i) ∧
      ∀ {h : ℝ}, |h| ≤ R₀ →
        B.lam * ∫ x, eta x ^ 2 * ∑ i : Fin d,
            diffQuot k h (fun y => hU.weakGrad y i) x ^ 2
          ∂(volume : Measure E) ≤
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
            2 * translate k h (fun y : E => B.a y i j) x * eta x *
              (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
              diffQuot k h (fun y => hU.weakGrad y i) x * diffQuot k h U x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
            diffQuot k h (fun y : E => B.a y i j) x * eta x ^ 2 *
              hU.weakGrad x i * diffQuot k h (fun y => hU.weakGrad y j) x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
            2 * diffQuot k h (fun y : E => B.a y i j) x * eta x *
              (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
              hU.weakGrad x i * diffQuot k h U x
            ∂(volume : Measure E)| +
        |rho⁻¹ * ∫ x in Omega,
            f x * nirenbergTestFunction k h eta u x ∂(volume : Measure E)| := by
  obtain ⟨U, hU, _, _, hU_eq, hgrad_eq⟩ :=
    hu.exists_compactly_supported_extension (by norm_num) hOmega
      heta_cpt.isCompact.cthickening hK_Omega
  have hU_eq' : ∀ x ∈ Metric.cthickening R₀ (tsupport eta), U x = u x :=
    fun _ hx => hU_eq hx
  have hgrad_eq' : ∀ x ∈ Metric.cthickening R₀ (tsupport eta), ∀ i : Fin d,
      hU.weakGrad x i = hu.weakGrad x i :=
    fun _ hx i => congrArg (fun z : E => z i) (hgrad_eq hx)
  refine ⟨U, hU, hU_eq', hgrad_eq', ?_⟩
  intro h hh_le
  have hroom : Metric.cthickening |h| (tsupport eta) ⊆
      Metric.cthickening R₀ (tsupport eta) := Metric.cthickening_mono hh_le _
  have hfour := nirenberg_substitution_identity_of_eqOn hu hU
    heta_cpt.isCompact.cthickening hK_Omega hU_eq' hgrad_eq' B hrho hcoeff
    heta heta_cpt k h hroom
  have hlocal := integral_sum_mul_diffQuot_eq_integral_mul_nirenbergTestFunction
    hOmega hu hweak heta heta_cpt k h (hroom.trans hK_Omega)
  rw [hlocal] at hfour
  have hg_l2 : ∀ i : Fin d, MemLp (fun x => hU.weakGrad x i) 2 volume := by
    intro i
    simpa only [Measure.restrict_univ] using hU.weakGrad_component_memLp i
  have hprincipal := principal_term_ge_lambda_norm_sq_nonsmooth B hg_l2 heta heta_cpt
    (Ω' := Set.univ) (Set.subset_univ _) (R₀ := R₀)
    (fun {_} _ => Set.subset_univ _) k hh_le
  linarith [neg_le_abs (∑ i : Fin d, ∑ j : Fin d, ∫ x,
            2 * translate k h (fun y : E => B.a y i j) x * eta x *
              (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
              diffQuot k h (fun y => hU.weakGrad y i) x * diffQuot k h U x
            ∂(volume : Measure E)),
    neg_le_abs (∑ i : Fin d, ∑ j : Fin d, ∫ x,
            diffQuot k h (fun y : E => B.a y i j) x * eta x ^ 2 *
              hU.weakGrad x i * diffQuot k h (fun y => hU.weakGrad y j) x
            ∂(volume : Measure E)),
    neg_le_abs (∑ i : Fin d, ∑ j : Fin d, ∫ x,
            2 * diffQuot k h (fun y : E => B.a y i j) x * eta x *
              (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
              hU.weakGrad x i * diffQuot k h U x
            ∂(volume : Measure E)),
    neg_le_abs (rho⁻¹ * ∫ x in Omega,
            f x * nirenbergTestFunction k h eta u x ∂(volume : Measure E))]

theorem IsSolution.exists_extension_nirenberg_master_inequality
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : EllipticCoeff d Omega} {u : E → ℝ}
    (hu : MemW1pWitness 2 u Omega)
    (hsol : IsSolution A u)
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : rho ≠ 0)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta)
    {R₀ : ℝ}
    (hK_Omega : Metric.cthickening R₀ (tsupport eta) ⊆ Omega)
    (hcoeff : ∀ x ∈ Metric.cthickening R₀ (tsupport eta),
      ∀ i j : Fin d, A.a x i j = rho * B.a x i j)
    (k : Fin d) :
    ∃ (U : E → ℝ) (hU : MemW1pWitness 2 U Set.univ),
      (∀ x ∈ Metric.cthickening R₀ (tsupport eta), U x = u x) ∧
      (∀ x ∈ Metric.cthickening R₀ (tsupport eta), ∀ i : Fin d,
        hU.weakGrad x i = hu.weakGrad x i) ∧
      ∀ {h : ℝ}, |h| ≤ R₀ →
        B.lam * ∫ x, eta x ^ 2 * ∑ i : Fin d,
            diffQuot k h (fun y => hU.weakGrad y i) x ^ 2
          ∂(volume : Measure E) ≤
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
            2 * translate k h (fun y : E => B.a y i j) x * eta x *
              (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
              diffQuot k h (fun y => hU.weakGrad y i) x * diffQuot k h U x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
            diffQuot k h (fun y : E => B.a y i j) x * eta x ^ 2 *
              hU.weakGrad x i * diffQuot k h (fun y => hU.weakGrad y j) x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
            2 * diffQuot k h (fun y : E => B.a y i j) x * eta x *
              (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
              hU.weakGrad x i * diffQuot k h U x
            ∂(volume : Measure E)| := by
  simpa using DeGiorgi.exists_extension_nirenberg_master_inequality (f := fun _ => 0)
    hOmega hu (fun _ hv0 hv => by
      simpa using hsol.bilinFormOfCoeff_eq_zero hOmega hu hv0 hv)
    B hrho heta heta_cpt hK_Omega hcoeff k

end DeGiorgi

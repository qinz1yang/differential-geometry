import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set Filter InnerProductSpace
open scoped Topology ContDiff ComplexConjugate

namespace DifferentialGeometry.Analysis

/-- The actual complex gradient of a real scalar function, with the Wirtinger
normalization used by the elliptic equation. -/
def planarComplexGradient (v : ℂ → ℝ) (z : ℂ) : ℂ :=
  ⟨fderiv ℝ v z 1 / 2, -fderiv ℝ v z Complex.I / 2⟩

/-- Augment the scalar gradient by the same scalar value, retaining the potential term. -/
def planarGradientSection (v : ℂ → ℝ) (z : ℂ) : ℂ × ℂ :=
  (planarComplexGradient v z, (v z : ℂ))

/-- Complex-linear part of the full augmented equation for `Δv + Dv(B) + q*v = 0`. -/
def planarGradientLinearCoefficient (B : ℂ) (q : ℝ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (-(1 / 4 : ℂ) * B) •
    ((ContinuousLinearMap.inl ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ ℂ ℂ)) +
  (-(1 / 4 : ℂ) * (q : ℂ)) •
    ((ContinuousLinearMap.inl ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ ℂ))

/-- Coefficient acting on the conjugate augmented section. This term is not discarded. -/
def planarGradientConjugateCoefficient (B : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (-(1 / 4 : ℂ) * conj B) •
    ((ContinuousLinearMap.inl ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ ℂ ℂ)) +
  (ContinuousLinearMap.inr ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ ℂ ℂ)

private theorem fderiv_planarComplexGradient_apply {v : ℂ → ℝ} {z : ℂ}
    (hv : ContDiffAt ℝ 2 v z) (t : ℂ) :
    fderiv ℝ (planarComplexGradient v) z t =
      ⟨fderiv ℝ (fun y => fderiv ℝ v y 1) z t / 2,
        -fderiv ℝ (fun y => fderiv ℝ v y Complex.I) z t / 2⟩ := by
  have hd := (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have ha := hd.clm_apply (differentiableAt_const (1 : ℂ))
  have hb := hd.clm_apply (differentiableAt_const Complex.I)
  have hp := (ha.hasFDerivAt.mul_const (2 : ℝ)⁻¹).prodMk
    (hb.hasFDerivAt.neg.mul_const (2 : ℝ)⁻¹)
  have hh := Complex.equivRealProdCLM.symm.hasFDerivAt.comp z hp
  change HasFDerivAt (planarComplexGradient v) _ z at hh
  rw [hh.fderiv]
  apply Complex.ext <;>
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      smul_eq_mul, div_eq_mul_inv] <;> ring

/-- The actual scalar gradient has `∂bar ∂v = Δv/4`, including at gradient zeros. -/
theorem planarComplexGradient_dbar_laplacian {v : ℂ → ℝ} {z : ℂ}
    (hv : ContDiffAt ℝ 2 v z) :
    (fderiv ℝ (planarComplexGradient v) z 1 +
      Complex.I * fderiv ℝ (planarComplexGradient v) z Complex.I) / 2 =
        (Laplacian.laplacian v z : ℂ) / 4 := by
  have hd := (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hpartial (s t : ℂ) :
      fderiv ℝ (fun y => fderiv ℝ v y t) z s = fderiv ℝ (fderiv ℝ v) z s t := by
    rw [fderiv_clm_apply hd (differentiableAt_const t)]
    simp
  have hsym := hv.isSymmSndFDerivAt (by norm_num) (1 : ℂ) Complex.I
  rw [fderiv_planarComplexGradient_apply hv, fderiv_planarComplexGradient_apply hv,
    hpartial, hpartial, hpartial, hpartial, laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply]
  apply Complex.ext <;> simp [hsym] <;> ring

private theorem differentiableAt_planarComplexGradient {v : ℂ → ℝ} {z : ℂ}
    (hv : ContDiffAt ℝ 2 v z) : DifferentiableAt ℝ (planarComplexGradient v) z := by
  have hd := (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hp := ((hd.clm_apply (differentiableAt_const (1 : ℂ))).mul
      (differentiableAt_const ((2 : ℝ)⁻¹))).prodMk
    ((hd.clm_apply (differentiableAt_const Complex.I)).neg.mul
      (differentiableAt_const ((2 : ℝ)⁻¹)))
  exact Complex.equivRealProdCLM.symm.differentiableAt.comp z hp

private theorem fderiv_eq_planarComplexGradient_pair (v : ℂ → ℝ) (z B : ℂ) :
    (fderiv ℝ v z B : ℂ) =
      B * planarComplexGradient v z + conj B * conj (planarComplexGradient v z) := by
  have hB : B = B.re • (1 : ℂ) + B.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hB, map_add, map_smul, map_smul]
  apply Complex.ext <;>
    simp [planarComplexGradient, Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

/-- The full scalar equation gives a smooth linear-plus-conjugate first-order
system for the actual augmented section. No solution-dependent quotient appears. -/
theorem planarGradientSection_dbar_eq {v : ℂ → ℝ} {z : ℂ} (B : ℂ) (q : ℝ)
    (hv : ContDiffAt ℝ 2 v z)
    (hpde : Laplacian.laplacian v z + fderiv ℝ v z B + q * v z = 0) :
    (1 / 2 : ℂ) • (fderiv ℝ (planarGradientSection v) z 1 +
      Complex.I • fderiv ℝ (planarGradientSection v) z Complex.I) =
      planarGradientLinearCoefficient B q (planarGradientSection v z) +
        planarGradientConjugateCoefficient B
          (conj (planarGradientSection v z).1, conj (planarGradientSection v z).2) := by
  have hg := differentiableAt_planarComplexGradient hv
  have hd (t : ℂ) : fderiv ℝ (planarGradientSection v) z t =
      (fderiv ℝ (planarComplexGradient v) z t, (fderiv ℝ v z t : ℂ)) := by
    have hh := (hg.hasFDerivAt.prodMk (Complex.ofRealCLM.hasFDerivAt.comp z
      (hv.differentiableAt (by norm_num)).hasFDerivAt)).fderiv
    exact congrArg (fun L : ℂ →L[ℝ] ℂ × ℂ => L t) hh
  rw [hd, hd]
  apply Prod.ext
  · change (1 / 2 : ℂ) * (fderiv ℝ (planarComplexGradient v) z 1 +
        Complex.I * fderiv ℝ (planarComplexGradient v) z Complex.I) =
      (-(1 / 4 : ℂ) * B * planarComplexGradient v z +
        -(1 / 4 : ℂ) * (q : ℂ) * (v z : ℂ)) +
        (-(1 / 4 : ℂ) * conj B * conj (planarComplexGradient v z) + 0)
    rw [add_zero]
    rw [mul_comm (1 / 2 : ℂ)]
    have hgrad := planarComplexGradient_dbar_laplacian hv
    simp only [div_eq_mul_inv, one_mul] at hgrad ⊢
    rw [hgrad]
    have hh := congrArg (fun r : ℝ => (r : ℂ)) hpde
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_zero] at hh
    rw [fderiv_eq_planarComplexGradient_pair v z B] at hh
    linear_combination (1 / 4 : ℂ) * hh
  · change (1 / 2 : ℂ) * ((fderiv ℝ v z 1 : ℂ) +
        Complex.I * (fderiv ℝ v z Complex.I : ℂ)) =
      (-(1 / 4 : ℂ) * B * 0 + -(1 / 4 : ℂ) * (q : ℂ) * 0) +
        (-(1 / 4 : ℂ) * conj B * 0 + conj (planarComplexGradient v z))
    simp only [mul_zero, zero_add]
    apply Complex.ext <;> simp [planarComplexGradient, Complex.mul_re, Complex.mul_im] <;> ring

/-- The augmented section vanishes exactly at an actual critical zero. -/
theorem planarGradientSection_eq_zero_iff (v : ℂ → ℝ) (z : ℂ) :
    planarGradientSection v z = 0 ↔ v z = 0 ∧ fderiv ℝ v z = 0 := by
  constructor
  · intro h
    have hg : planarComplexGradient v z = 0 := congrArg Prod.fst h
    have hv : (v z : ℂ) = 0 := congrArg Prod.snd h
    have h1 : fderiv ℝ v z 1 = 0 := by
      have hh := congrArg Complex.re hg
      change fderiv ℝ v z 1 / 2 = 0 at hh
      linarith
    have hI : fderiv ℝ v z Complex.I = 0 := by
      have hh := congrArg Complex.im hg
      change -fderiv ℝ v z Complex.I / 2 = 0 at hh
      linarith
    refine ⟨Complex.ofReal_eq_zero.mp hv, ?_⟩
    apply ContinuousLinearMap.ext
    intro t
    have ht : t = t.re • (1 : ℂ) + t.im • Complex.I := by
      apply Complex.ext <;> simp
    rw [ht, map_add, map_smul, map_smul, h1, hI]
    simp
  · rintro ⟨hv, hd⟩
    apply Prod.ext <;> simp [planarGradientSection, planarComplexGradient, hv, hd]
    rfl

/-- Smooth real scalar data give a smooth actual augmented section. -/
theorem contDiffOn_planarGradientSection {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ ∞ v Ω) :
    ContDiffOn ℝ ∞ (planarGradientSection v) Ω := by
  have hd := hv.fderiv_of_isOpen (m := ∞) hΩ (by simp)
  have ha := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have hb := hd.clm_apply (contDiffOn_const (c := Complex.I))
  have hp := (ha.mul (contDiffOn_const (c := (2 : ℝ)⁻¹))).prodMk
    (hb.neg.mul (contDiffOn_const (c := (2 : ℝ)⁻¹)))
  have hg : ContDiffOn ℝ ∞ (planarComplexGradient v) Ω := by
    refine (Complex.equivRealProdCLM.symm.contDiff.comp_contDiffOn hp).congr ?_
    intro z _
    apply Complex.ext <;> simp [planarComplexGradient,
      Complex.equivRealProdCLM_symm_apply, div_eq_mul_inv]
  exact hg.prodMk (Complex.ofRealCLM.contDiff.comp_contDiffOn hv)

/-- The two coefficient fields are constructed smoothly from the actual drift and potential. -/
theorem contDiffOn_planarGradientCoefficients {Ω : Set ℂ}
    {B : ℂ → ℂ} {q : ℂ → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) (hq : ContDiffOn ℝ ∞ q Ω) :
    ContDiffOn ℝ ∞ (fun z => planarGradientLinearCoefficient (B z) (q z)) Ω ∧
      ContDiffOn ℝ ∞ (fun z => planarGradientConjugateCoefficient (B z)) Ω := by
  have hqC := Complex.ofRealCLM.contDiff.comp_contDiffOn hq
  have hBc := Complex.conjCLE.contDiff.comp_contDiffOn hB
  constructor
  · exact ((contDiffOn_const.mul hB).smul contDiffOn_const).add
      ((contDiffOn_const.mul hqC).smul contDiffOn_const)
  · exact ((contDiffOn_const.mul hBc).smul contDiffOn_const).add contDiffOn_const

private theorem planarGradientSection_dbar_norm_le
    {v : ℂ → ℝ} {z : ℂ} (B : ℂ) (q : ℝ) (hv : ContDiffAt ℝ 2 v z)
    (hpde : Laplacian.laplacian v z + fderiv ℝ v z B + q * v z = 0) :
    ‖(1 / 2 : ℂ) • (fderiv ℝ (planarGradientSection v) z 1 +
      Complex.I • fderiv ℝ (planarGradientSection v) z Complex.I)‖ ≤
      (‖planarGradientLinearCoefficient B q‖ + ‖planarGradientConjugateCoefficient B‖) *
        ‖planarGradientSection v z‖ := by
  rw [planarGradientSection_dbar_eq B q hv hpde]
  have hc : ‖(conj (planarGradientSection v z).1, conj (planarGradientSection v z).2)‖ =
      ‖planarGradientSection v z‖ := by simp only [Prod.norm_def, Complex.norm_conj]
  calc
    _ ≤ ‖planarGradientLinearCoefficient B q (planarGradientSection v z)‖ +
        ‖planarGradientConjugateCoefficient B
          (conj (planarGradientSection v z).1, conj (planarGradientSection v z).2)‖ := norm_add_le _ _
    _ ≤ ‖planarGradientLinearCoefficient B q‖ * ‖planarGradientSection v z‖ +
        ‖planarGradientConjugateCoefficient B‖ *
          ‖(conj (planarGradientSection v z).1, conj (planarGradientSection v z).2)‖ :=
      add_le_add ((planarGradientLinearCoefficient B q).le_opNorm _)
        ((planarGradientConjugateCoefficient B).le_opNorm _)
    _ = _ := by rw [hc]; ring

/-- Every point of the full smooth scalar equation has an actual neighborhood
on which its augmented section satisfies the first-order differential inequality.
This includes critical zeros and imposes no sign on the potential. -/
theorem exists_local_planarGradientSection_dbar_bound
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {v : ℂ → ℝ} {B : ℂ → ℂ} {q : ℂ → ℝ}
    (hv : ContDiffOn ℝ ∞ v Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (hq : ContDiffOn ℝ ∞ q Ω)
    (hpde : ∀ z ∈ Ω, Laplacian.laplacian v z + fderiv ℝ v z (B z) + q z * v z = 0)
    {p : ℂ} (hp : p ∈ Ω) :
    ∃ (U : Set ℂ) (C : ℝ), IsOpen U ∧ p ∈ U ∧ U ⊆ Ω ∧ 0 < C ∧
      ∀ z ∈ U, ‖(1 / 2 : ℂ) • (fderiv ℝ (planarGradientSection v) z 1 +
        Complex.I • fderiv ℝ (planarGradientSection v) z Complex.I)‖ ≤
          C * ‖planarGradientSection v z‖ := by
  obtain ⟨hA, hK⟩ := contDiffOn_planarGradientCoefficients hB hq
  let C := ‖planarGradientLinearCoefficient (B p) (q p)‖ +
    ‖planarGradientConjugateCoefficient (B p)‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hcont : ContinuousAt (fun z => ‖planarGradientLinearCoefficient (B z) (q z)‖ +
      ‖planarGradientConjugateCoefficient (B z)‖) p :=
    ((hA.continuousOn p hp).continuousAt (hΩ.mem_nhds hp)).norm.add
      (((hK.continuousOn p hp).continuousAt (hΩ.mem_nhds hp)).norm)
  have hnear : ∀ᶠ z in 𝓝 p,
      ‖planarGradientLinearCoefficient (B z) (q z)‖ +
        ‖planarGradientConjugateCoefficient (B z)‖ < C :=
    hcont.eventually_lt continuousAt_const (by dsimp [C]; linarith)
  have hboth : ∀ᶠ z in 𝓝 p, z ∈ Ω ∧
      ‖planarGradientLinearCoefficient (B z) (q z)‖ +
        ‖planarGradientConjugateCoefficient (B z)‖ < C := by
    filter_upwards [hΩ.mem_nhds hp, hnear] with z hz hbound
    exact ⟨hz, hbound⟩
  obtain ⟨U, hUsub, hUo, hpU⟩ := mem_nhds_iff.mp hboth
  refine ⟨U, C, hUo, hpU, fun z hz => (hUsub hz).1, hC, ?_⟩
  intro z hz
  have hzΩ := (hUsub hz).1
  exact (planarGradientSection_dbar_norm_le (B z) (q z)
    ((hv.contDiffAt (hΩ.mem_nhds hzΩ)).of_le (by simp)) (hpde z hzΩ)).trans
      (mul_le_mul_of_nonneg_right (hUsub hz).2.le (norm_nonneg _))

end DifferentialGeometry.Analysis

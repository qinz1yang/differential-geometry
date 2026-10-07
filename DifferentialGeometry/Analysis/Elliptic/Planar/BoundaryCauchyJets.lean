import DifferentialGeometry.Analysis.Elliptic.Planar.FirstOrderReduction
import DifferentialGeometry.Analysis.Elliptic.Planar.CoordinateChange
import Mathlib.LinearAlgebra.Matrix.PosDef
import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.ZeroExtension
import Mathlib.Analysis.Complex.ReImTopology

set_option autoImplicit false
noncomputable section

open Set Filter InnerProductSpace
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem fderiv_fderiv_tangent_eq_zero
    {U : Set ℂ} (hU : IsOpen U) {v : ℂ → ℝ} (hv : ContDiffOn ℝ ∞ v U)
    (hzero : ∀ z ∈ U, z.im = 0 → fderiv ℝ v z = 0)
    {z : ℂ} (hz : z ∈ U) (him : z.im = 0) :
    fderiv ℝ (fderiv ℝ v) z 1 = 0 := by
  have hv2 : ContDiffAt ℝ 2 v z := (hv.contDiffAt (hU.mem_nhds hz)).of_le (by simp)
  have hd := (hv2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hbase : HasFDerivAt (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v) z)
      (z + Complex.ofRealCLM 0) := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_zero, add_zero] using hd.hasFDerivAt
  have hcomp := hbase.comp (0 : ℝ) (Complex.ofRealCLM.hasFDerivAt.const_add z)
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, z + (t : ℂ) ∈ U := by
    have hc : ContinuousAt (fun t : ℝ => z + (t : ℂ)) 0 :=
      (continuous_const.add Complex.continuous_ofReal).continuousAt
    have hz0 : z + ((0 : ℝ) : ℂ) ∈ U := by
      simpa only [Complex.ofReal_zero, add_zero] using hz
    exact hc.preimage_mem_nhds (hU.mem_nhds hz0)
  have heq : (fun t : ℝ => fderiv ℝ v (z + (t : ℂ))) =ᶠ[𝓝 0] (fun _ => 0) := by
    filter_upwards [hnear] with t ht
    exact hzero _ ht (by simp [him])
  have hc : HasFDerivAt (𝕜 := ℝ) (fun t : ℝ => fderiv ℝ v (z + (t : ℂ))) 0 0 :=
    (hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ →L[ℝ] ℝ) (0 : ℝ)).congr_of_eventuallyEq heq
  have hh := congrArg (fun L : ℝ →L[ℝ] (ℂ →L[ℝ] ℝ) => L 1) (hcomp.unique hc)
  simpa only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    Complex.ofReal_one, zero_apply] using hh

/-- Vanishing scalar Cauchy data force the second derivative to vanish on a
flat seam. The reduced elliptic equation is required only on the upper side;
its value at the seam follows from continuity. The drift and potential remain
in that equation throughout. -/
theorem fderiv_fderiv_eq_zero_on_flat_seam
    {U : Set ℂ} (hU : IsOpen U) {v : ℂ → ℝ} {B : ℂ → ℂ} {q : ℂ → ℝ}
    (hv : ContDiffOn ℝ ∞ v U) (hB : ContinuousOn B U) (hq : ContinuousOn q U)
    (hpde : ∀ z ∈ U, 0 < z.im →
      Laplacian.laplacian v z + fderiv ℝ v z (B z) + q z * v z = 0)
    (hzero : ∀ z ∈ U, z.im = 0 → v z = 0 ∧ fderiv ℝ v z = 0) :
    ∀ z ∈ U, z.im = 0 → fderiv ℝ (fderiv ℝ v) z = 0 := by
  let L : ℂ → ℝ := fun z =>
    Laplacian.laplacian v z + fderiv ℝ v z (B z) + q z * v z
  have hLc : ContinuousOn L U := by
    have hΔ : ContinuousOn (Laplacian.laplacian v) U := fun z hz =>
      ((hv.contDiffAt (hU.mem_nhds hz)).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).continuousAt_laplacian.continuousWithinAt
    exact (hΔ.add ((hv.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply hB)).add
      (hq.mul hv.continuousOn)
  have hEq : EqOn L (fun _ => 0) (U ∩ {z : ℂ | 0 < z.im}) :=
    fun z hz => hpde z hz.1 hz.2
  have hclosure : U ∩ {z : ℂ | 0 ≤ z.im} ⊆ closure (U ∩ {z : ℂ | 0 < z.im}) := by
    intro z hz
    have hzc : z ∈ closure {z : ℂ | 0 < z.im} := by
      rw [Complex.closure_setOfPred_lt_im]
      exact hz.2
    apply mem_closure_iff.mpr
    intro O hO hzO
    obtain ⟨w, hwOU, hwim⟩ := mem_closure_iff.mp hzc (O ∩ U) (hO.inter hU) ⟨hzO, hz.1⟩
    exact ⟨w, hwOU.1, hwOU.2, hwim⟩
  have hsub : U ∩ {z : ℂ | 0 < z.im} ⊆ U ∩ {z : ℂ | 0 ≤ z.im} :=
    fun z hz => ⟨hz.1, show (0 : ℝ) ≤ z.im from (show (0 : ℝ) < z.im from hz.2).le⟩
  have hEqClosed : EqOn L (fun _ => 0) (U ∩ {z : ℂ | 0 ≤ z.im}) :=
    hEq.of_subset_closure (hLc.mono inter_subset_left) continuousOn_const hsub hclosure
  intro z hz him
  obtain ⟨hv0, hd0⟩ := hzero z hz him
  have hΔ := hEqClosed (show z ∈ U ∩ {z : ℂ | 0 ≤ z.im} from ⟨hz, by simp [him]⟩)
  change Laplacian.laplacian v z + fderiv ℝ v z (B z) + q z * v z = 0 at hΔ
  simp only [hd0, zero_apply, hv0, mul_zero, add_zero] at hΔ
  have h1 : fderiv ℝ (fderiv ℝ v) z 1 = 0 :=
    fderiv_fderiv_tangent_eq_zero hU hv (fun y hy hyim => (hzero y hy hyim).2) hz him
  have hv2 : ContDiffAt ℝ 2 v z := (hv.contDiffAt (hU.mem_nhds hz)).of_le (by simp)
  have hI1 : fderiv ℝ (fderiv ℝ v) z Complex.I 1 = 0 := by
    rw [hv2.isSymmSndFDerivAt (by norm_num) Complex.I (1 : ℂ), h1]
    rfl
  have hII : fderiv ℝ (fderiv ℝ v) z Complex.I Complex.I = 0 := by
    simpa only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, h1, zero_apply, zero_add] using hΔ
  have hI : fderiv ℝ (fderiv ℝ v) z Complex.I = 0 := by
    apply ContinuousLinearMap.ext
    intro t
    have ht : t = t.re • (1 : ℂ) + t.im • Complex.I := by apply Complex.ext <;> simp
    rw [ht, map_add, map_smul, map_smul, hI1, hII]
    simp
  apply ContinuousLinearMap.ext
  intro t
  have ht : t = t.re • (1 : ℂ) + t.im • Complex.I := by apply Complex.ext <;> simp
  rw [ht, map_add, map_smul, map_smul, h1, hI]
  simp

private theorem fderiv_planarGradientSection_eq_zero_of_secondJet_zero
    {v : ℂ → ℝ} {z : ℂ} (hv : ContDiffAt ℝ 2 v z)
    (hd0 : fderiv ℝ v z = 0) (hdd0 : fderiv ℝ (fderiv ℝ v) z = 0) :
    fderiv ℝ (planarGradientSection v) z = 0 := by
  have hd := (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have ha := hd.clm_apply (differentiableAt_const (1 : ℂ))
  have hb := hd.clm_apply (differentiableAt_const Complex.I)
  have hp := (ha.hasFDerivAt.mul_const (2 : ℝ)⁻¹).prodMk
    (hb.hasFDerivAt.neg.mul_const (2 : ℝ)⁻¹)
  have hg := Complex.equivRealProdCLM.symm.hasFDerivAt.comp z hp
  change HasFDerivAt (planarComplexGradient v) _ z at hg
  have hf := hg.prodMk (Complex.ofRealCLM.hasFDerivAt.comp z
    (hv.differentiableAt (by norm_num)).hasFDerivAt)
  change HasFDerivAt (planarGradientSection v) _ z at hf
  rw [hf.fderiv]
  apply ContinuousLinearMap.ext
  intro t
  apply Prod.ext
  · apply Complex.ext <;>
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        fderiv_clm_apply, hd, hdd0]
  · simp [ContinuousLinearMap.comp_apply, hd0]

/-- The actual scalar Cauchy data produce a `C¹` zero-extended augmented
section, suitable for the bounded-coefficient and weak inverse-gauge suppliers.
The coefficient bound is imposed only on the actual upper side. Neither the
scalar PDE nor its smooth extension is asserted to solve the PDE below it. -/
theorem planarGradientSection_zeroExtension_flat_seam
    {U : Set ℂ} (hU : IsOpen U) {v : ℂ → ℝ} {B : ℂ → ℂ} {q : ℂ → ℝ}
    (hv : ContDiffOn ℝ ∞ v U) (hB : ContinuousOn B U) (hq : ContinuousOn q U)
    (hpde : ∀ z ∈ U, 0 < z.im →
      Laplacian.laplacian v z + fderiv ℝ v z (B z) + q z * v z = 0)
    (hzero : ∀ z ∈ U, z.im = 0 → v z = 0 ∧ fderiv ℝ v z = 0)
    {C : ℝ} (hC : ∀ z ∈ U, 0 < z.im →
      ‖planarGradientLinearCoefficient (B z) (q z)‖ +
        ‖planarGradientConjugateCoefficient (B z)‖ ≤ C) :
    let Z := ({z : ℂ | 0 < z.im}).indicator (planarGradientSection v)
    ContDiffOn ℝ 1 Z U ∧ (∀ z ∈ U, ‖complexDbar Z z‖ ≤ C * ‖Z z‖) ∧
      (∀ z : ℂ, 0 < z.im → Z z = planarGradientSection v z) ∧
      (∀ z : ℂ, z.im ≤ 0 → Z z = 0) := by
  classical
  have hs : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hsec : ContDiffOn ℝ 1 (planarGradientSection v) U :=
    (contDiffOn_planarGradientSection hU hv).of_le (by simp)
  have hjets : ∀ z ∈ U ∩ frontier {z : ℂ | 0 < z.im},
      planarGradientSection v z = 0 ∧ fderiv ℝ (planarGradientSection v) z = 0 := by
    intro z hz
    have him : z.im = 0 := by
      simpa only [Complex.frontier_setOfPred_lt_im, mem_ofPred_eq] using hz.2
    obtain ⟨hv0, hd0⟩ := hzero z hz.1 him
    exact ⟨(planarGradientSection_eq_zero_iff v z).mpr ⟨hv0, hd0⟩,
      fderiv_planarGradientSection_eq_zero_of_secondJet_zero
        ((hv.contDiffAt (hU.mem_nhds hz.1)).of_le (by simp)) hd0
        (fderiv_fderiv_eq_zero_on_flat_seam hU hv hB hq hpde hzero z hz.1 him)⟩
  have hbound : ∀ z ∈ U ∩ {z : ℂ | 0 < z.im},
      ‖complexDbar (planarGradientSection v) z‖ ≤ C * ‖planarGradientSection v z‖ := by
    intro z hz
    change ‖(1 / 2 : ℂ) • (fderiv ℝ (planarGradientSection v) z 1 +
      Complex.I • fderiv ℝ (planarGradientSection v) z Complex.I)‖ ≤ _
    rw [planarGradientSection_dbar_eq (B z) (q z)
      ((hv.contDiffAt (hU.mem_nhds hz.1)).of_le (by simp)) (hpde z hz.1 hz.2)]
    have hconj : ‖(starRingEnd ℂ (planarGradientSection v z).1,
        starRingEnd ℂ (planarGradientSection v z).2)‖ = ‖planarGradientSection v z‖ := by
      simp only [Prod.norm_def, Complex.norm_conj]
    calc
      _ ≤ ‖planarGradientLinearCoefficient (B z) (q z) (planarGradientSection v z)‖ +
          ‖planarGradientConjugateCoefficient (B z)
            (starRingEnd ℂ (planarGradientSection v z).1, starRingEnd ℂ (planarGradientSection v z).2)‖ := norm_add_le _ _
      _ ≤ ‖planarGradientLinearCoefficient (B z) (q z)‖ * ‖planarGradientSection v z‖ +
          ‖planarGradientConjugateCoefficient (B z)‖ *
            ‖(starRingEnd ℂ (planarGradientSection v z).1, starRingEnd ℂ (planarGradientSection v z).2)‖ :=
        add_le_add ((planarGradientLinearCoefficient (B z) (q z)).le_opNorm _)
          ((planarGradientConjugateCoefficient (B z)).le_opNorm _)
      _ = (‖planarGradientLinearCoefficient (B z) (q z)‖ +
          ‖planarGradientConjugateCoefficient (B z)‖) * ‖planarGradientSection v z‖ := by
        rw [hconj]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hC z hz.1 hz.2) (norm_nonneg _)
  obtain ⟨hreg, _, hineq⟩ := complexDbar_indicator_of_frontier_firstJet_zero hU hs hsec hjets hbound
  exact ⟨hreg, hineq, fun z hz =>
      indicator_of_mem (show z ∈ {z : ℂ | 0 < z.im} from hz) (planarGradientSection v),
    fun z hz => indicator_of_notMem
      (show z ∉ {z : ℂ | 0 < z.im} from not_lt.mpr hz) (planarGradientSection v)⟩

private theorem continuousOn_planarScalarOperator
    {U : Set ℂ} (hU : IsOpen U)
    {A : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {beta : ℂ → Fin 2 → ℝ} {c w : ℂ → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) U)
    (hbeta : ∀ i, ContDiffOn ℝ ∞ (fun z => beta z i) U)
    (hc : ContDiffOn ℝ ∞ c U) (hw : ContDiffOn ℝ ∞ w U) :
    ContinuousOn (planarScalarOperator A beta c w) U := by
  have hd := hw.fderiv_of_isOpen (m := ∞) hU (by simp)
  have hdd := hd.fderiv_of_isOpen (m := ∞) hU (by simp)
  have hprincipal : ContDiffOn ℝ ∞ (fun z =>
      ∑ i : Fin 2, ∑ j : Fin 2, A z i j * fderiv ℝ (fderiv ℝ w) z
        ((![1, Complex.I] : Fin 2 → ℂ) i) ((![1, Complex.I] : Fin 2 → ℂ) j)) U := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact (hA i j).mul ((hdd.clm_apply contDiffOn_const).clm_apply contDiffOn_const)
  have hdrift : ContDiffOn ℝ ∞ (fun z => ∑ i : Fin 2,
      beta z i * fderiv ℝ w z ((![1, Complex.I] : Fin 2 → ℂ) i)) U := by
    apply ContDiffOn.sum
    intro i _
    exact (hbeta i).mul (hd.clm_apply contDiffOn_const)
  exact ((hprincipal.add hdrift).add (hc.mul hw)).continuousOn

/-- For the original positive-principal scalar operator, flat-seam Cauchy data
force the full second jet to vanish. The original PDE is used only above the
seam, and reaches the seam by continuity; positivity of its normal coefficient
then supplies the missing normal second derivative. -/
theorem fderiv_fderiv_eq_zero_on_flat_seam_of_planarScalarOperator
    {U : Set ℂ} (hU : IsOpen U)
    {A : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {beta : ℂ → Fin 2 → ℝ} {c w : ℂ → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) U)
    (hbeta : ∀ i, ContDiffOn ℝ ∞ (fun z => beta z i) U)
    (hc : ContDiffOn ℝ ∞ c U) (hw : ContDiffOn ℝ ∞ w U)
    (hpos : ∀ z ∈ U, (A z).PosDef)
    (hpde : ∀ z ∈ U, 0 < z.im → planarScalarOperator A beta c w z = 0)
    (hzero : ∀ z ∈ U, z.im = 0 → w z = 0 ∧ fderiv ℝ w z = 0) :
    ∀ z ∈ U, z.im = 0 → fderiv ℝ (fderiv ℝ w) z = 0 := by
  have hOp := continuousOn_planarScalarOperator hU hA hbeta hc hw
  have hEq : EqOn (planarScalarOperator A beta c w) (fun _ => 0)
      (U ∩ {z : ℂ | 0 < z.im}) := fun z hz => hpde z hz.1 hz.2
  have hclosure : U ∩ {z : ℂ | 0 ≤ z.im} ⊆ closure (U ∩ {z : ℂ | 0 < z.im}) := by
    intro z hz
    have hzc : z ∈ closure {z : ℂ | 0 < z.im} := by
      rw [Complex.closure_setOfPred_lt_im]
      exact hz.2
    apply mem_closure_iff.mpr
    intro O hO hzO
    obtain ⟨y, hyOU, hyim⟩ := mem_closure_iff.mp hzc (O ∩ U) (hO.inter hU) ⟨hzO, hz.1⟩
    exact ⟨y, hyOU.1, hyOU.2, hyim⟩
  have hsub : U ∩ {z : ℂ | 0 < z.im} ⊆ U ∩ {z : ℂ | 0 ≤ z.im} :=
    fun z hz => ⟨hz.1, show (0 : ℝ) ≤ z.im from (show (0 : ℝ) < z.im from hz.2).le⟩
  have hEqClosed : EqOn (planarScalarOperator A beta c w) (fun _ => 0)
      (U ∩ {z : ℂ | 0 ≤ z.im}) :=
    hEq.of_subset_closure (hOp.mono inter_subset_left) continuousOn_const hsub hclosure
  intro z hz him
  obtain ⟨hw0, hd0⟩ := hzero z hz him
  have h1 : fderiv ℝ (fderiv ℝ w) z 1 = 0 :=
    fderiv_fderiv_tangent_eq_zero hU hw (fun y hy hi => (hzero y hy hi).2) hz him
  have hw2 : ContDiffAt ℝ 2 w z := (hw.contDiffAt (hU.mem_nhds hz)).of_le (by simp)
  have hI1 : fderiv ℝ (fderiv ℝ w) z Complex.I 1 = 0 := by
    rw [hw2.isSymmSndFDerivAt (by norm_num) Complex.I (1 : ℂ), h1]
    rfl
  have hOp0 := hEqClosed (show z ∈ U ∩ {z : ℂ | 0 ≤ z.im} from ⟨hz, by simp [him]⟩)
  have hII : fderiv ℝ (fderiv ℝ w) z Complex.I Complex.I = 0 := by
    have hprod : A z 1 1 * fderiv ℝ (fderiv ℝ w) z Complex.I Complex.I = 0 := by
      simpa only [planarScalarOperator, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, h1, hI1, hd0, hw0,
        zero_apply, mul_zero, zero_add, add_zero] using hOp0
    exact (mul_eq_zero.mp hprod).resolve_left (hpos z hz).diag_pos.ne'
  have hI : fderiv ℝ (fderiv ℝ w) z Complex.I = 0 := by
    apply ContinuousLinearMap.ext
    intro t
    have ht : t = t.re • (1 : ℂ) + t.im • Complex.I := by apply Complex.ext <;> simp
    rw [ht, map_add, map_smul, map_smul, hI1, hII]
    simp
  apply ContinuousLinearMap.ext
  intro t
  have ht : t = t.re • (1 : ℂ) + t.im • Complex.I := by apply Complex.ext <;> simp
  rw [ht, map_add, map_smul, map_smul, h1, hI]
  simp

/-- The proved scalar second-jet vanishing supplies the first-jet condition for
the literal augmented section used by zero extension. -/
theorem planarGradientSection_firstJet_zero_of_secondJet_zero
    {w : ℂ → ℝ} {z : ℂ} (hw : ContDiffAt ℝ 2 w z)
    (hw0 : w z = 0) (hd0 : fderiv ℝ w z = 0)
    (hdd0 : fderiv ℝ (fderiv ℝ w) z = 0) :
    planarGradientSection w z = 0 ∧ fderiv ℝ (planarGradientSection w) z = 0 :=
  ⟨(planarGradientSection_eq_zero_iff w z).mpr ⟨hw0, hd0⟩,
    fderiv_planarGradientSection_eq_zero_of_secondJet_zero hw hd0 hdd0⟩

private theorem planar_symmetric_form_eq_zero_of_posDef_contraction
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (hH : ∀ u v, H u v = H v u)
    {τ : ℂ} (hτ : τ ≠ 0) (hker : H τ = 0)
    (htrace : (∑ i : Fin 2, ∑ j : Fin 2,
      A i j * H ((![1, Complex.I] : Fin 2 → ℂ) i)
        ((![1, Complex.I] : Fin 2 → ℂ) j)) = 0) : H = 0 := by
  have hAsym : A 1 0 = A 0 1 := by
    simpa only [star_trivial] using hA.isHermitian.apply 0 1
  have h10 : H Complex.I 1 = H 1 Complex.I := hH _ _
  have hτexp : τ = τ.re • (1 : ℂ) + τ.im • Complex.I := by
    apply Complex.ext <;> simp
  have hk1 := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) hker
  have hk2 := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) hker
  rw [hτexp, map_add, map_smul, map_smul] at hk1 hk2
  simp only [add_apply, smul_apply, smul_eq_mul,
    zero_apply, h10] at hk1 hk2
  have hp : A 0 0 * H 1 1 + 2 * A 0 1 * H 1 Complex.I +
      A 1 1 * H Complex.I Complex.I = 0 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      hAsym, h10] at htrace
    nlinarith only [htrace]
  have h00 : H 1 1 = 0 := by
    by_cases hy : τ.im = 0
    · have hx : τ.re ≠ 0 := by
        intro hx
        apply hτ
        apply Complex.ext <;> simp [hx, hy]
      simp only [hy, zero_mul, add_zero] at hk1
      exact (mul_eq_zero.mp hk1).resolve_left hx
    · have hn : (![τ.im, -τ.re] : Fin 2 → ℝ) ≠ 0 := by
        intro hn
        have hh := congrFun hn 0
        exact hy (by simpa using hh)
      have hquad := hA.dotProduct_mulVec_pos hn
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply,
        star_trivial, Matrix.cons_val_zero, Matrix.cons_val_one, hAsym] at hquad
      have hq : 0 < A 0 0 * τ.im ^ 2 - 2 * A 0 1 * τ.re * τ.im +
          A 1 1 * τ.re ^ 2 := by nlinarith only [hquad]
      have hmul : (A 0 0 * τ.im ^ 2 - 2 * A 0 1 * τ.re * τ.im +
          A 1 1 * τ.re ^ 2) * H 1 1 = 0 := by
        linear_combination τ.im ^ 2 * hp - (2 * A 0 1 * τ.im) * hk1 +
          (A 1 1 * τ.re) * hk1 - (A 1 1 * τ.im) * hk2
      exact (mul_eq_zero.mp hmul).resolve_left hq.ne'
  have h01 : H 1 Complex.I = 0 := by
    by_cases hy : τ.im = 0
    · have hx : τ.re ≠ 0 := by
        intro hx
        apply hτ
        apply Complex.ext <;> simp [hx, hy]
      simp only [hy, zero_mul, add_zero] at hk2
      exact (mul_eq_zero.mp hk2).resolve_left hx
    · simp only [h00, mul_zero, zero_add] at hk1
      exact (mul_eq_zero.mp hk1).resolve_left hy
  have h11 : H Complex.I Complex.I = 0 := by
    simp only [h00, h01, mul_zero, zero_add] at hp
    exact (mul_eq_zero.mp hp).resolve_left hA.diag_pos.ne'
  have h1 : H 1 = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    have hu : u = u.re • (1 : ℂ) + u.im • Complex.I := by
      apply Complex.ext <;> simp
    rw [hu, map_add, map_smul, map_smul, h00, h01]
    simp
  have hI : H Complex.I = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    have hu : u = u.re • (1 : ℂ) + u.im • Complex.I := by
      apply Complex.ext <;> simp
    rw [hu, map_add, map_smul, map_smul, h10, h01, h11]
    simp
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = u.re • (1 : ℂ) + u.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hu, map_add, map_smul, map_smul, h1, hI]
  simp

private theorem fderiv_fderiv_curve_tangent_eq_zero
    {w : ℂ → ℝ} {z τ : ℂ} {γ : ℝ → ℂ}
    (hw : ContDiffAt ℝ 2 w z) (hγ : HasDerivAt γ τ 0) (hγ0 : γ 0 = z)
    (hzero : (fun t => fderiv ℝ w (γ t)) =ᶠ[𝓝 0] (fun _ => 0)) :
    fderiv ℝ (fderiv ℝ w) z τ = 0 := by
  have hd := (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdγ : HasFDerivAt (fderiv ℝ w) (fderiv ℝ (fderiv ℝ w) z) (γ 0) := by
    simpa only [hγ0] using hd.hasFDerivAt
  have hcomp := hdγ.comp_hasDerivAt 0 hγ
  have hconst : HasDerivAt (fun t => fderiv ℝ w (γ t)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℂ →L[ℝ] ℝ)).congr_of_eventuallyEq hzero
  exact hcomp.unique hconst

/-- Cauchy data along a regular curved frontier force the full scalar second
jet to vanish there. The equation is required only on the supplied side, and
its original positive principal matrix, drift and potential are retained.
The regular parameters describe the actual frontier; they need not be straight
in the original graph coordinates or in any later isothermal coordinates. -/
theorem fderiv_fderiv_eq_zero_on_regular_frontier_of_planarScalarOperator
    {U s : Set ℂ} (hU : IsOpen U) (hsU : s ⊆ U)
    {A : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {beta : ℂ → Fin 2 → ℝ} {c w : ℂ → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) U)
    (hbeta : ∀ i, ContDiffOn ℝ ∞ (fun z => beta z i) U)
    (hc : ContDiffOn ℝ ∞ c U) (hw : ContDiffOn ℝ ∞ w U)
    (hpos : ∀ z ∈ U, (A z).PosDef)
    (hpde : ∀ z ∈ s, planarScalarOperator A beta c w z = 0)
    (hzero : ∀ z ∈ U ∩ frontier s, w z = 0 ∧ fderiv ℝ w z = 0)
    (hcurve : ∀ z ∈ U ∩ frontier s, ∃ (γ : ℝ → ℂ) (τ : ℂ),
      γ 0 = z ∧ HasDerivAt γ τ 0 ∧ τ ≠ 0 ∧
        ∀ᶠ t in 𝓝 0, γ t ∈ U ∩ frontier s) :
    ∀ z ∈ U ∩ frontier s, fderiv ℝ (fderiv ℝ w) z = 0 := by
  have hOp := continuousOn_planarScalarOperator hU hA hbeta hc hw
  have hEq : EqOn (planarScalarOperator A beta c w) (fun _ => 0) s := hpde
  have hEqClosed : EqOn (planarScalarOperator A beta c w) (fun _ => 0)
      (U ∩ closure s) :=
    hEq.of_subset_closure (hOp.mono inter_subset_left) continuousOn_const
      (fun z hz => ⟨hsU hz, subset_closure hz⟩) inter_subset_right
  intro z hz
  obtain ⟨γ, τ, hγ0, hγ, hτ, hnear⟩ := hcurve z hz
  obtain ⟨hw0, hd0⟩ := hzero z hz
  have hw2 : ContDiffAt ℝ 2 w z :=
    (hw.contDiffAt (hU.mem_nhds hz.1)).of_le (by simp)
  have hnearZero : (fun t => fderiv ℝ w (γ t)) =ᶠ[𝓝 0] (fun _ => 0) := by
    filter_upwards [hnear] with t ht
    exact (hzero _ ht).2
  have hker := fderiv_fderiv_curve_tangent_eq_zero hw2 hγ hγ0 hnearZero
  have hOp0 := hEqClosed ⟨hz.1, frontier_subset_closure hz.2⟩
  have hprincipal : (∑ i : Fin 2, ∑ j : Fin 2, A z i j *
      fderiv ℝ (fderiv ℝ w) z ((![1, Complex.I] : Fin 2 → ℂ) i)
        ((![1, Complex.I] : Fin 2 → ℂ) j)) = 0 := by
    simpa only [planarScalarOperator, hd0, hw0, zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero] using hOp0
  exact planar_symmetric_form_eq_zero_of_posDef_contraction (hpos z hz.1)
    (fderiv ℝ (fderiv ℝ w) z) (hw2.isSymmSndFDerivAt (by norm_num))
    hτ hker hprincipal

end DifferentialGeometry.Analysis

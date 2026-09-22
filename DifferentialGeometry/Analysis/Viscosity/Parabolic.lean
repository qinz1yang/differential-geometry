import DifferentialGeometry.Analysis.Calculus.Matrix.Factorization
import DifferentialGeometry.Analysis.Viscosity.Distribution
import Mathlib.LinearAlgebra.Basis.Prod

noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Elementwise

namespace DifferentialGeometry.Analysis.Viscosity

private theorem sum_integral_fderiv_fderiv
    {F κ : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype κ]
    [MeasurableSpace F] [BorelSpace F] {μ : Measure F} [IsLocallyFiniteMeasure μ]
    {Ω : Set F} (hΩ : IsOpen Ω) {u : F → ℝ} (hu : ContinuousOn u Ω)
    {f : κ → F → ℝ} (hf : ∀ k, ContDiff ℝ 2 (f k))
    (hfc : ∀ k, HasCompactSupport (f k)) (hfs : ∀ k, tsupport (f k) ⊆ Ω) (v w : F) :
    (∑ k, ∫ x, u x * fderiv ℝ (fderiv ℝ (f k)) x v w ∂μ) =
      ∫ x, u x * fderiv ℝ (fderiv ℝ (fun y => ∑ k, f k y)) x v w ∂μ := by
  have hc (k : κ) : Continuous (fun x => fderiv ℝ (fderiv ℝ (f k)) x v w) :=
    ((((hf k).fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const
  have hs (k : κ) : tsupport (fun x => fderiv ℝ (fderiv ℝ (f k)) x v w) ⊆ Ω :=
    ((tsupport_comp_subset (g := fun L : F →L[ℝ] ℝ => L w) rfl _).trans
      ((tsupport_fderiv_apply_subset ℝ v).trans (tsupport_fderiv_subset ℝ))).trans (hfs k)
  have hi (k : κ) : Integrable (fun x => u x * fderiv ℝ (fderiv ℝ (f k)) x v w) μ := by
    have hcompact := (((hfc k).fderiv ℝ).fderiv_apply ℝ v).comp_left
      (g := fun L : F →L[ℝ] ℝ => L w) rfl
    exact ((hu.mul (hc k).continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans (hs k))).integrable_of_hasCompactSupport hcompact.mul_left
  have hd : fderiv ℝ (fun y => ∑ k, f k y) = fun y => ∑ k, fderiv ℝ (f k) y := by
    funext y
    exact fderiv_fun_sum (fun k _ => (hf k).differentiable (by norm_num) y)
  rw [← integral_finsetSum Finset.univ (fun k _ => hi k)]
  apply integral_congr_ae
  filter_upwards with x
  rw [hd, fderiv_fun_sum (fun k _ => ((hf k).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)]
  simp only [sum_apply, Finset.mul_sum]


theorem parabolic_distribution_le_of_upper_tests_of_locallyLipschitzOn
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    [MeasurableSpace (ℝ × E)] [BorelSpace (ℝ × E)]
    {μ : Measure (ℝ × E)} [μ.IsAddHaarMeasure]
    (e : Module.Basis ι ℝ E) {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    {u : ℝ × E → ℝ} (hu : LocallyLipschitzOn Ω u)
    {A : ℝ × E → Matrix ι ι ℝ} {b : ℝ × E → E} {c r : ℝ × E → ℝ}
    (hA : ContDiffOn ℝ 2 A Ω) (hpos : ∀ x ∈ Ω, (A x).PosDef)
    (hb : ContDiffOn ℝ 1 b Ω) (hc : LocallyLipschitzOn Ω c) (hr : LocallyLipschitzOn Ω r)
    (hsub : ∀ x ∈ Ω, ∀ ψ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      IsLocalMax (fun y => u y - ψ y) x →
      -(∑ i, ∑ j, A x i j * fderiv ℝ (fderiv ℝ ψ) x (0, e i) (0, e j)) +
        fderiv ℝ ψ x (1, b x) + c x * u x ≤ r x)
    {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) (hφ0 : ∀ x, 0 ≤ φ x) :
    -(∑ i, ∑ j, ∫ x, u x * fderiv ℝ (fderiv ℝ (fun y => A y i j * φ y))
        x (0, e j) (0, e i) ∂μ) -
      (∫ x, u x * fderiv ℝ φ x (1, 0) ∂μ) -
      (∑ i, ∫ x, u x * fderiv ℝ (fun y => e.repr (b y) i * φ y) x (0, e i) ∂μ) +
      (∫ x, (c x * u x - r x) * φ x ∂μ) ≤ 0 := by
  classical
  let : FiniteDimensional ℝ E := e.finiteDimensional_of_finite
  obtain ⟨S, hS, hfactor⟩ := hA.exists_mul_transpose hpos
  let L : (ι → ℝ) →L[ℝ] ℝ × E :=
    (ContinuousLinearMap.inr ℝ ℝ E).comp e.equivFunL.symm.toContinuousLinearMap
  let V (k : ι) (x : ℝ × E) : ℝ × E := L ((S x).col k)
  let W (x : ℝ × E) : ℝ × E := (1, b x)
  let eP : Module.Basis (Unit ⊕ ι) ℝ (ℝ × E) := (Module.Basis.singleton Unit ℝ).prod e
  have hV (k : ι) : ContDiffOn ℝ 2 (V k) Ω :=
    L.contDiff.comp_contDiffOn (contDiffOn_pi.mpr fun i => contDiffOn_pi.mp (contDiffOn_pi.mp hS i) k)
  have hL : Function.Injective L := by
    intro v w h
    exact e.equivFunL.symm.injective (congrArg Prod.snd h)
  have hind (x : ℝ × E) (hx : x ∈ Ω) : LinearIndependent ℝ (fun k => V k x) :=
    (Matrix.linearIndependent_cols_iff_isUnit.mpr (hfactor x hx).1).map' L.toLinearMap
      (LinearMap.ker_eq_bot.mpr hL)
  have hVsum (k : ι) (x : ℝ × E) : V k x = ∑ i, S x i k • (0, e i) := by
    change (0, e.equivFun.symm ((S x).col k)) = _
    rw [Module.Basis.equivFun_symm_apply]
    ext <;> simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_mk, smul_zero,
      Finset.sum_const_zero, Matrix.col_apply]
  have hcoeff (x : ℝ × E) (hx : x ∈ Ω) (i j : ι) :
      (∑ k, S x i k * S x j k) = A x i j := by
    exact congrArg (fun M : Matrix ι ι ℝ => M i j) (hfactor x hx).2
  have htrace (x : ℝ × E) (hx : x ∈ Ω) (H : (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) :
      (∑ k, H (V k x) (V k x)) = ∑ i, ∑ j, A x i j * H (0, e i) (0, e j) := by
    have he (k : ι) : H (V k x) (V k x) =
        ∑ i, ∑ j, (S x i k * S x j k) * H (0, e i) (0, e j) := by
      rw [hVsum]
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [he]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, hcoeff x hx]
  have hW : ContDiffOn ℝ 1 W Ω := contDiffOn_const.prodMk hb
  have hineq := distribution_le_of_upper_tests_of_locallyLipschitzOn (μ := μ) eP hΩ hu hV
    hW hc hr hind
    (fun x hx ψ hψ hm => by simpa only [htrace x hx, W] using hsub x hx ψ hψ hm)
    hφ hφc hφs hφ0
  have htime (x : ℝ × E) (k : ι) : eP.repr (V k x) (Sum.inl ()) = 0 := by
    simp only [eP, Module.Basis.prod_repr_inl, Module.Basis.singleton_repr]
    rfl
  have hspace (x : ℝ × E) (k i : ι) : eP.repr (V k x) (Sum.inr i) = S x i k := by
    change e.equivFun (e.equivFun.symm ((S x).col k)) i = _
    rw [e.equivFun.apply_symm_apply]
    rfl
  have hbtime (x : ℝ × E) : eP.repr (W x) (Sum.inl ()) = 1 := by
    simp only [eP, Module.Basis.prod_repr_inl, Module.Basis.singleton_repr, W]
  have hbspace (x : ℝ × E) (i : ι) : eP.repr (W x) (Sum.inr i) = e.repr (b x) i := rfl
  have hetime : eP (Sum.inl ()) = (1, 0) := by
    simp only [eP, Module.Basis.prod_apply, Function.comp_apply, Sum.elim_inl,
      Module.Basis.singleton_apply, LinearMap.inl_apply]
  have hespace (i : ι) : eP (Sum.inr i) = (0, e i) := by
    simp only [eP, Module.Basis.prod_apply, Function.comp_apply, Sum.elim_inr, LinearMap.inr_apply]
  have hzero (x v w : ℝ × E) :
      fderiv ℝ (fderiv ℝ (fun _ : ℝ × E => (0 : ℝ))) x v w = 0 := by
    have hz : fderiv ℝ (fun _ : ℝ × E => (0 : ℝ)) = fun _ => (0 : (ℝ × E) →L[ℝ] ℝ) :=
      funext fun y => fderiv_const_apply 0
    rw [hz, fderiv_const_apply]
    rfl
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, htime, hspace, hbtime, hbspace,
    zero_mul, mul_zero, one_mul, hzero, integral_zero, Finset.sum_const_zero,
    zero_add, hetime, hespace] at hineq
  have hdiff (i j : ι) :
      (∑ k, ∫ x, u x * fderiv ℝ (fderiv ℝ (fun y => S y i k * S y j k * φ y))
        x (0, e j) (0, e i) ∂μ) =
      ∫ x, u x * fderiv ℝ (fderiv ℝ (fun y => A y i j * φ y)) x (0, e j) (0, e i) ∂μ := by
    have hf (k : ι) : ContDiff ℝ 2 (fun y => S y i k * S y j k * φ y) :=
      ((((contDiffOn_pi.mp (contDiffOn_pi.mp hS i) k).mul
        (contDiffOn_pi.mp (contDiffOn_pi.mp hS j) k)).mul hφ.contDiffOn).contDiff_of_tsupport_subset
          hΩ (tsupport_mul_subset_right.trans hφs))
    have heq : (fun y => ∑ k, S y i k * S y j k * φ y) = (fun y => A y i j * φ y) := by
      funext y
      by_cases hy : y ∈ Ω
      · rw [← Finset.sum_mul, hcoeff y hy]
      · have hz : φ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hφs h))
        simp only [hz, mul_zero, Finset.sum_const_zero]
    have h := sum_integral_fderiv_fderiv (μ := μ) hΩ hu.continuousOn hf
      (fun _ => hφc.mul_left) (fun _ => tsupport_mul_subset_right.trans hφs) (0, e j) (0, e i)
    rw [heq] at h
    exact h
  have hsum : (∑ k, ∑ i, ∑ j, ∫ x, u x *
      fderiv ℝ (fderiv ℝ (fun y => S y i k * S y j k * φ y)) x (0, e j) (0, e i) ∂μ) =
      ∑ i, ∑ j, ∫ x, u x * fderiv ℝ (fderiv ℝ (fun y => A y i j * φ y))
        x (0, e j) (0, e i) ∂μ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => hdiff i j)
  rw [hsum] at hineq
  linarith

end DifferentialGeometry.Analysis.Viscosity

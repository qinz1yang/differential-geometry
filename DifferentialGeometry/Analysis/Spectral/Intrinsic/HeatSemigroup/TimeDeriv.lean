import DifferentialGeometry.Analysis.Parabolic.AbstractSemigroup.AbstractSpectralSemigroupContinuity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Intrinsic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Calculus.Deriv.Slope
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section

open Set Filter Topology
open scoped RealInnerProductSpace InnerProductSpace BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic

variable {ι : Type*} {X : Type*} [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] [CompleteSpace X]

theorem expFactorDeriv_le {a t : ℝ} (ht : 0 < t) :
    a * Real.exp (-a * t) ≤ 1 / (Real.exp 1 * t) := by
  have hbound : Real.exp 1 * (a * t) ≤ Real.exp (a * t) := Real.exp_one_mul_le_exp
  have hexp_pos : (0 : ℝ) < Real.exp (a * t) := Real.exp_pos _
  have het_pos : (0 : ℝ) < Real.exp 1 * t := mul_pos (Real.exp_pos 1) ht
  rw [le_div_iff₀ het_pos]
  have hexp_neg : Real.exp (-a * t) = (Real.exp (a * t))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [hexp_neg]
  rw [mul_comm (Real.exp 1) t]
  have hkey : a * (Real.exp (a * t))⁻¹ * (t * Real.exp 1) =
      (Real.exp 1 * (a * t)) * (Real.exp (a * t))⁻¹ := by ring
  rw [hkey]
  rw [mul_inv_le_iff₀ hexp_pos, one_mul]
  exact hbound

theorem abs_expFactorDeriv_le_of_ge {a τ s : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ)
    (hs : τ ≤ s) :
    |a * Real.exp (-a * s)| ≤ 1 / (Real.exp 1 * τ) := by
  have hs_pos : 0 < s := lt_of_lt_of_le hτ hs
  have hnn : 0 ≤ a * Real.exp (-a * s) := mul_nonneg ha (Real.exp_pos _).le
  rw [abs_of_nonneg hnn]
  refine le_trans (expFactorDeriv_le hs_pos) ?_
  have heτ_pos : (0 : ℝ) < Real.exp 1 * τ := mul_pos (Real.exp_pos 1) hτ
  have hmono : Real.exp 1 * τ ≤ Real.exp 1 * s :=
    mul_le_mul_of_nonneg_left hs (Real.exp_pos 1).le
  exact one_div_le_one_div_of_le heτ_pos hmono

theorem expFactor_hasDerivAt (a t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-a * s)) (-a * Real.exp (-a * t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => -a * s) (-a) t := by
    simpa using (hasDerivAt_id t).const_mul (-a)
  have h2 := (Real.hasDerivAt_exp (-a * t)).comp t h1
  rw [mul_comm] at h2
  exact h2

theorem expFactor_differentiable (a : ℝ) :
    Differentiable ℝ (fun s : ℝ => Real.exp (-a * s)) :=
  fun t => (expFactor_hasDerivAt a t).differentiableAt

theorem abs_expFactor_sub_le {a τ u w : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ)
    (hu : τ ≤ u) (hw : τ ≤ w) :
    |Real.exp (-a * w) - Real.exp (-a * u)| ≤
      (1 / (Real.exp 1 * τ)) * |w - u| := by
  have hconv : Convex ℝ (Ici τ) := convex_Ici τ
  have hdiff : ∀ x ∈ Ici τ, DifferentiableAt ℝ (fun s : ℝ => Real.exp (-a * s)) x :=
    fun x _ => (expFactor_hasDerivAt a x).differentiableAt
  have hbound : ∀ x ∈ Ici τ,
      ‖deriv (fun s : ℝ => Real.exp (-a * s)) x‖ ≤ 1 / (Real.exp 1 * τ) := by
    intro x hx
    rw [(expFactor_hasDerivAt a x).deriv]
    have hxτ : τ ≤ x := hx
    have := abs_expFactorDeriv_le_of_ge ha hτ hxτ
    rw [Real.norm_eq_abs]
    rw [show (-a * Real.exp (-a * x)) = -(a * Real.exp (-a * x)) by ring, abs_neg]
    exact this
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun s : ℝ => Real.exp (-a * s)) hdiff hbound hconv
    (mem_Ici.mpr hu) (mem_Ici.mpr hw)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  exact hmvt

def heatDerivCoeff (lam : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  -(lam i) * heatCoeff lam t i

lemma heatDerivCoeff_def (lam : ι → ℝ) (t : ℝ) (i : ι) :
    heatDerivCoeff lam t i = -(lam i) * Real.exp (-(lam i) * t) := rfl

lemma abs_heatDerivCoeff_le {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {t : ℝ} (ht : 0 < t) (i : ι) :
    |heatDerivCoeff lam t i| ≤ 1 / (Real.exp 1 * t) := by
  rw [heatDerivCoeff_def, show (-(lam i) * Real.exp (-(lam i) * t)) =
    -((lam i) * Real.exp (-(lam i) * t)) by ring, abs_neg]
  exact abs_expFactorDeriv_le_of_ge (hlam i) ht (le_refl t)

lemma summable_heatDerivTerm (b : HilbertBasis ι ℝ X) {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 < t) (v : X) :
    Summable (fun i : ι => heatDerivCoeff lam t i • ⟪b i, v⟫_ℝ • b i) := by
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_orthFam :
      OrthogonalFamily ℝ (fun _ : ι => ℝ)
        (fun i => LinearIsometry.toSpanSingleton ℝ X (h_orthonormal.1 i)) :=
    h_orthonormal.orthogonalFamily
  set C : ℝ := 1 / (Real.exp 1 * t) with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]; positivity
  have h_sq_summable : Summable
      (fun i : ι => (heatDerivCoeff lam t i * ⟪b i, v⟫_ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_
      ((summable_basis_coeff_sq' b v).mul_left (C ^ 2))
    · intro i; positivity
    · intro i
      have h_coeff_le : |heatDerivCoeff lam t i| ≤ C := abs_heatDerivCoeff_le hlam ht i
      have h_coeff_sq_le : (heatDerivCoeff lam t i) ^ 2 ≤ C ^ 2 := by
        have := sq_le_sq' (neg_le_of_abs_le h_coeff_le) (le_of_abs_le h_coeff_le)
        simpa using this
      have h_inner_sq_nn : 0 ≤ (⟪b i, v⟫_ℝ) ^ 2 := sq_nonneg _
      calc (heatDerivCoeff lam t i * ⟪b i, v⟫_ℝ) ^ 2
          = (heatDerivCoeff lam t i) ^ 2 * (⟪b i, v⟫_ℝ) ^ 2 := by ring
        _ ≤ C ^ 2 * (⟪b i, v⟫_ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right h_coeff_sq_le h_inner_sq_nn
  have h_iff := h_orthFam.summable_iff_norm_sq_summable
    (fun i : ι => heatDerivCoeff lam t i * ⟪b i, v⟫_ℝ)
  have h_sq_eq : (fun i : ι => ‖heatDerivCoeff lam t i * ⟪b i, v⟫_ℝ‖ ^ 2) =
      (fun i => (heatDerivCoeff lam t i * ⟪b i, v⟫_ℝ) ^ 2) := by
    funext i; rw [Real.norm_eq_abs, sq_abs]
  rw [h_sq_eq] at h_iff
  have h_map_eq : (fun i : ι =>
        LinearIsometry.toSpanSingleton ℝ X (h_orthonormal.1 i)
          (heatDerivCoeff lam t i * ⟪b i, v⟫_ℝ)) =
      (fun i => heatDerivCoeff lam t i • ⟪b i, v⟫_ℝ • b i) := by
    funext i; rw [LinearIsometry.toSpanSingleton_apply, mul_smul]
  have h_summable_V := h_iff.mpr h_sq_summable
  rw [h_map_eq] at h_summable_V
  exact h_summable_V

def abstractSpectralSemigroupDeriv (b : HilbertBasis ι ℝ X) (lam : ι → ℝ)
    (t : ℝ) (v : X) : X :=
  ∑' i : ι, heatDerivCoeff lam t i • ⟪b i, v⟫_ℝ • b i

omit [CompleteSpace X] in
lemma abstractSpectralSemigroupDeriv_def (b : HilbertBasis ι ℝ X) (lam : ι → ℝ)
    (t : ℝ) (v : X) :
    abstractSpectralSemigroupDeriv b lam t v =
      ∑' i : ι, heatDerivCoeff lam t i • ⟪b i, v⟫_ℝ • b i := rfl

theorem abstractSpectralSemigroupDeriv_repr_apply (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 < t)
    (v : X) (i : ι) :
    (b.repr (abstractSpectralSemigroupDeriv b lam t v) : ι → ℝ) i =
      heatDerivCoeff lam t i * (b.repr v : ι → ℝ) i := by
  classical
  rw [b.repr_apply_apply, b.repr_apply_apply,
    abstractSpectralSemigroupDeriv_def]
  have hsum := summable_heatDerivTerm b hlam ht v
  change (innerSL (𝕜 := ℝ) (E := X) (b i))
      (∑' j : ι, heatDerivCoeff lam t j • ⟪b j, v⟫_ℝ • b j) = _
  rw [(innerSL (𝕜 := ℝ) (E := X) (b i)).map_tsum hsum]
  have horth := (orthonormal_iff_ite (𝕜 := ℝ) (v := b)).mp b.orthonormal
  simp_rw [innerSL_apply_apply, inner_smul_right, horth]
  have heq : (fun j : ι =>
      heatDerivCoeff lam t j * (⟪b j, v⟫_ℝ * if i = j then 1 else 0)) =
      (fun j => if j = i then heatDerivCoeff lam t j * ⟪b j, v⟫_ℝ else 0) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji, Ne.symm hji]
  rw [heq, tsum_ite_eq]

private theorem abstractSpectralSemigroupDeriv_map_add (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 < t)
    (v w : X) :
    abstractSpectralSemigroupDeriv b lam t (v + w) =
      abstractSpectralSemigroupDeriv b lam t v +
        abstractSpectralSemigroupDeriv b lam t w := by
  apply b.repr.injective
  ext i
  calc
    (b.repr (abstractSpectralSemigroupDeriv b lam t (v + w)) : ι → ℝ) i =
        heatDerivCoeff lam t i * (b.repr (v + w) : ι → ℝ) i :=
      abstractSpectralSemigroupDeriv_repr_apply b hlam ht (v + w) i
    _ = heatDerivCoeff lam t i * (b.repr v : ι → ℝ) i +
        heatDerivCoeff lam t i * (b.repr w : ι → ℝ) i := by
      rw [map_add]
      change heatDerivCoeff lam t i *
          ((b.repr v : ι → ℝ) i + (b.repr w : ι → ℝ) i) = _
      ring
    _ = (b.repr (abstractSpectralSemigroupDeriv b lam t v +
        abstractSpectralSemigroupDeriv b lam t w) : ι → ℝ) i := by
      rw [map_add]
      change _ =
        (b.repr (abstractSpectralSemigroupDeriv b lam t v) : ι → ℝ) i +
          (b.repr (abstractSpectralSemigroupDeriv b lam t w) : ι → ℝ) i
      rw [
        abstractSpectralSemigroupDeriv_repr_apply b hlam ht,
        abstractSpectralSemigroupDeriv_repr_apply b hlam ht]

private theorem abstractSpectralSemigroupDeriv_map_smul (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 < t)
    (c : ℝ) (v : X) :
    abstractSpectralSemigroupDeriv b lam t (c • v) =
      c • abstractSpectralSemigroupDeriv b lam t v := by
  apply b.repr.injective
  ext i
  calc
    (b.repr (abstractSpectralSemigroupDeriv b lam t (c • v)) : ι → ℝ) i =
        heatDerivCoeff lam t i * (b.repr (c • v) : ι → ℝ) i :=
      abstractSpectralSemigroupDeriv_repr_apply b hlam ht (c • v) i
    _ = c * (heatDerivCoeff lam t i * (b.repr v : ι → ℝ) i) := by
      rw [map_smul]
      change heatDerivCoeff lam t i * (c * (b.repr v : ι → ℝ) i) = _
      ring
    _ = (b.repr (c • abstractSpectralSemigroupDeriv b lam t v) : ι → ℝ) i := by
      rw [map_smul]
      change _ = c *
        (b.repr (abstractSpectralSemigroupDeriv b lam t v) : ι → ℝ) i
      rw [abstractSpectralSemigroupDeriv_repr_apply b hlam ht]

theorem norm_abstractSpectralSemigroupDeriv_le (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 < t)
    (v : X) :
    ‖abstractSpectralSemigroupDeriv b lam t v‖ ≤
      (1 / (Real.exp 1 * t)) * ‖v‖ := by
  set C : ℝ := 1 / (Real.exp 1 * t) with hC_def
  have hC_nn : 0 ≤ C := by rw [hC_def]; positivity
  have hcoeff_summable : Summable
      (fun i : ι => (heatDerivCoeff lam t i * ⟪b i, v⟫_ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_)
      ((summable_basis_coeff_sq' b v).mul_left (C ^ 2))
    have hcoeff := abs_heatDerivCoeff_le hlam ht i
    have hcoeff_sq : (heatDerivCoeff lam t i) ^ 2 ≤ C ^ 2 := by
      have := sq_le_sq' (neg_le_of_abs_le hcoeff) (le_of_abs_le hcoeff)
      simpa only [hC_def] using this
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hcoeff_sq (sq_nonneg _)
  have hderiv_sq : ‖abstractSpectralSemigroupDeriv b lam t v‖ ^ 2 =
      ∑' i : ι, (heatDerivCoeff lam t i * ⟪b i, v⟫_ℝ) ^ 2 := by
    rw [abstractSpectralSemigroupDeriv_def]
    have heq : (fun i : ι =>
        heatDerivCoeff lam t i • ⟪b i, v⟫_ℝ • b i) =
        (fun i => (heatDerivCoeff lam t i * ⟪b i, v⟫_ℝ) • b i) := by
      funext i
      rw [mul_smul]
    rw [heq]
    exact orthonormal_norm_sq_eq_tsum_sq b _ hcoeff_summable
  have hv_sq : ‖v‖ ^ 2 = ∑' i : ι, (⟪b i, v⟫_ℝ) ^ 2 := by
    have hparseval := b.tsum_inner_mul_inner v v
    have hinner : ⟪v, v⟫_ℝ = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    have heq : (fun i : ι => ⟪v, b i⟫_ℝ * ⟪b i, v⟫_ℝ) =
        (fun i => (⟪b i, v⟫_ℝ) ^ 2) := by
      funext i
      rw [show ⟪v, b i⟫_ℝ = ⟪b i, v⟫_ℝ from real_inner_comm _ _, sq]
    rw [heq] at hparseval
    linarith only [hparseval, hinner]
  have hsum_le :
      ∑' i : ι, (heatDerivCoeff lam t i * ⟪b i, v⟫_ℝ) ^ 2 ≤
        ∑' i : ι, C ^ 2 * (⟪b i, v⟫_ℝ) ^ 2 := by
    refine Summable.tsum_le_tsum (fun i => ?_) hcoeff_summable
      ((summable_basis_coeff_sq' b v).mul_left (C ^ 2))
    have hcoeff := abs_heatDerivCoeff_le hlam ht i
    have hcoeff_sq : (heatDerivCoeff lam t i) ^ 2 ≤ C ^ 2 := by
      have := sq_le_sq' (neg_le_of_abs_le hcoeff) (le_of_abs_le hcoeff)
      simpa only [hC_def] using this
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hcoeff_sq (sq_nonneg _)
  have hsq : ‖abstractSpectralSemigroupDeriv b lam t v‖ ^ 2 ≤
      (C * ‖v‖) ^ 2 := by
    rw [hderiv_sq, mul_pow, hv_sq, ← tsum_mul_left]
    exact hsum_le
  nlinarith [norm_nonneg (abstractSpectralSemigroupDeriv b lam t v),
    mul_nonneg hC_nn (norm_nonneg v)]

def abstractSpectralSemigroupDerivCLM (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) (t : ℝ) (ht : 0 < t) :
    X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := abstractSpectralSemigroupDeriv b lam t
      map_add' := abstractSpectralSemigroupDeriv_map_add b hlam ht
      map_smul' := abstractSpectralSemigroupDeriv_map_smul b hlam ht }
    (1 / (Real.exp 1 * t))
    (norm_abstractSpectralSemigroupDeriv_le b hlam ht)

@[simp] theorem abstractSpectralSemigroupDerivCLM_apply
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (t : ℝ) (ht : 0 < t) (v : X) :
    abstractSpectralSemigroupDerivCLM b hlam t ht v =
      abstractSpectralSemigroupDeriv b lam t v :=
  rfl

theorem abstractSpectralSemigroupDerivCLM_opNorm_le
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (t : ℝ) (ht : 0 < t) :
    ‖abstractSpectralSemigroupDerivCLM b hlam t ht‖ ≤
      1 / (Real.exp 1 * t) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  exact norm_abstractSpectralSemigroupDeriv_le b hlam ht v

theorem abstractSpectralSemigroupDeriv_add (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t s : ℝ}
    (ht : 0 < t) (hs : 0 ≤ s) (v : X) :
    abstractSpectralSemigroupDeriv b lam (t + s) v =
      abstractSpectralSemigroup b hlam s
        (abstractSpectralSemigroupDeriv b lam t v) := by
  apply b.repr.injective
  ext i
  rw [abstractSpectralSemigroupDeriv_repr_apply b hlam (add_pos_of_pos_of_nonneg ht hs),
    abstractSpectralSemigroup_repr_apply b hlam hs,
    abstractSpectralSemigroupDeriv_repr_apply b hlam ht]
  simp only [heatDerivCoeff_def, heatCoeff_def]
  rw [show -(lam i) * (t + s) = -(lam i) * t + -(lam i) * s by ring,
    Real.exp_add]
  ring

theorem abstractSpectralSemigroupDeriv_continuousOn (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) (v : X) :
    ContinuousOn (fun t : ℝ => abstractSpectralSemigroupDeriv b lam t v)
      (Set.Ioi 0) := by
  intro t ht
  have ht' : 0 < t := ht
  set a : ℝ := t / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hat : a < t := by rw [ha_def]; linarith
  have hta : 0 < t - a := sub_pos.mpr hat
  set w : X := abstractSpectralSemigroupDeriv b lam a v with hw_def
  have hsemigroup : ContinuousAt
      (fun q : ℝ => abstractSpectralSemigroup b hlam q w) (t - a) :=
    (abstractSpectralSemigroup_continuousOn b hlam w).continuousAt
      (Ici_mem_nhds hta)
  have hcomp : ContinuousAt
      (fun q : ℝ => abstractSpectralSemigroup b hlam (q - a) w) t := by
    have hsub : ContinuousAt (fun q : ℝ => q - a) t :=
      continuousAt_id.sub continuousAt_const
    exact hsemigroup.comp_of_eq hsub rfl
  have heq : (fun q : ℝ => abstractSpectralSemigroupDeriv b lam q v) =ᶠ[𝓝 t]
      (fun q : ℝ => abstractSpectralSemigroup b hlam (q - a) w) := by
    filter_upwards [Ioi_mem_nhds hat] with q hq
    calc
      abstractSpectralSemigroupDeriv b lam q v =
          abstractSpectralSemigroupDeriv b lam (a + (q - a)) v := by
            congr 2
            ring
      _ = abstractSpectralSemigroup b hlam (q - a)
          (abstractSpectralSemigroupDeriv b lam a v) :=
        abstractSpectralSemigroupDeriv_add b hlam ha (sub_nonneg.mpr hq.le) v
      _ = abstractSpectralSemigroup b hlam (q - a) w := by rw [hw_def]
  exact (hcomp.congr_of_eventuallyEq heq).continuousWithinAt

theorem abstractSpectralSemigroupDeriv_continuousOn_uncurry
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) :
    ContinuousOn
      (Function.uncurry fun t : ℝ => abstractSpectralSemigroupDeriv b lam t)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  rintro ⟨t, v⟩ ⟨ht, -⟩
  have ht_pos : 0 < t := by simpa using ht
  set a : ℝ := t / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith only [ht_pos]
  have hat : a < t := by rw [ha_def]; linarith
  have hta : 0 < t - a := sub_pos.mpr hat
  let D := abstractSpectralSemigroupDerivCLM b hlam a ha
  let S : QuasiLinear.BoundedC0Semigroup X :=
    { toFun := abstractSpectralSemigroup b hlam
      apply_zero := abstractSpectralSemigroup_apply_zero b hlam
      apply_add := fun _ _ hq hs =>
        abstractSpectralSemigroup_apply_add b hlam hq hs
      opNorm_le_one := fun q _ => abstractSpectralSemigroup_opNorm_le_one b hlam q
      continuousOn_apply := abstractSpectralSemigroup_continuousOn b hlam }
  have hS : ContinuousAt (fun p : ℝ × X => S p.1 p.2) (t - a, D v) :=
    S.continuousOn_uncurry.continuousAt
      (prod_mem_nhds (Ici_mem_nhds hta) univ_mem)
  have hinner : ContinuousAt (fun p : ℝ × X => (p.1 - a, D p.2)) (t, v) :=
    (continuous_fst.sub continuous_const).prodMk (D.continuous.comp continuous_snd)
      |>.continuousAt
  have hcomp : ContinuousAt
      (fun p : ℝ × X => S (p.1 - a) (D p.2)) (t, v) :=
    hS.comp_of_eq hinner rfl
  have heq :
      (Function.uncurry fun q : ℝ => abstractSpectralSemigroupDeriv b lam q) =ᶠ[
        𝓝 (t, v)] fun p => S (p.1 - a) (D p.2) := by
    filter_upwards [prod_mem_nhds (Ioi_mem_nhds hat) univ_mem] with p hp
    change abstractSpectralSemigroupDeriv b lam p.1 p.2 =
      abstractSpectralSemigroup b hlam (p.1 - a)
        (abstractSpectralSemigroupDeriv b lam a p.2)
    calc
      abstractSpectralSemigroupDeriv b lam p.1 p.2 =
          abstractSpectralSemigroupDeriv b lam (a + (p.1 - a)) p.2 := by
        congr 2
        ring
      _ = abstractSpectralSemigroup b hlam (p.1 - a)
          (abstractSpectralSemigroupDeriv b lam a p.2) :=
        abstractSpectralSemigroupDeriv_add b hlam ha (sub_nonneg.mpr hp.1.le) p.2
  exact (hcomp.congr_of_eventuallyEq heq).continuousWithinAt

private def slopeMinusDerivCoeff (lam : ι → ℝ) (t s : ℝ) (i : ι) : ℝ :=
  (s - t)⁻¹ * (heatCoeff lam s i - heatCoeff lam t i) - heatDerivCoeff lam t i

private lemma slopeMinusDeriv_eq_tsum (b : HilbertBasis ι ℝ X) {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) (v : X) :
    (s - t)⁻¹ • (abstractSpectralSemigroup b hlam s v -
        abstractSpectralSemigroup b hlam t v) -
        abstractSpectralSemigroupDeriv b lam t v =
      ∑' i : ι, slopeMinusDerivCoeff lam t s i • ⟪b i, v⟫_ℝ • b i := by
  rw [abstractSpectralSemigroup_apply_of_nonneg b hlam hs,
    abstractSpectralSemigroup_apply_of_nonneg b hlam ht.le,
    abstractSpectralSemigroupDeriv_def]
  have hSs := summable_heatTerm b hlam hs v
  have hSt := summable_heatTerm b hlam ht.le v
  have hSd := summable_heatDerivTerm b hlam ht v
  have hslope : (s - t)⁻¹ • ((∑' i : ι, heatCoeff lam s i • ⟪b i, v⟫_ℝ • b i) -
        ∑' i : ι, heatCoeff lam t i • ⟪b i, v⟫_ℝ • b i) =
      ∑' i : ι, ((s - t)⁻¹ * (heatCoeff lam s i - heatCoeff lam t i)) •
        ⟪b i, v⟫_ℝ • b i := by
    rw [← hSs.tsum_sub hSt, ← (hSs.sub hSt).tsum_const_smul ((s - t)⁻¹)]
    apply tsum_congr
    intro i
    rw [smul_sub]
    module
  rw [hslope]
  have hSslope : Summable (fun i : ι =>
      ((s - t)⁻¹ * (heatCoeff lam s i - heatCoeff lam t i)) • ⟪b i, v⟫_ℝ • b i) := by
    refine ((hSs.sub hSt).const_smul ((s - t)⁻¹)).congr ?_
    intro i
    rw [smul_sub]
    module
  rw [← hSslope.tsum_sub hSd]
  apply tsum_congr
  intro i
  rw [slopeMinusDerivCoeff]
  module

private lemma slopeMinusDerivCoeff_tendsto (lam : ι → ℝ) (t : ℝ) (i : ι) :
    Tendsto (fun s : ℝ => slopeMinusDerivCoeff lam t s i) (𝓝[≠] t) (𝓝 0) := by
  have hderiv : HasDerivAt (fun s : ℝ => heatCoeff lam s i) (heatDerivCoeff lam t i) t := by
    have := expFactor_hasDerivAt (lam i) t
    exact this
  have hslope := hderiv.tendsto_slope
  have hslope' : Tendsto (fun s : ℝ => (s - t)⁻¹ * (heatCoeff lam s i - heatCoeff lam t i))
      (𝓝[≠] t) (𝓝 (heatDerivCoeff lam t i)) := by
    refine hslope.congr ?_
    intro s
    rw [slope_def_field, div_eq_inv_mul]
  have := hslope'.sub (tendsto_const_nhds (x := heatDerivCoeff lam t i))
  simpa only [slopeMinusDerivCoeff, sub_self] using this

private lemma abs_slopeMinusDerivCoeff_le {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {t s : ℝ} (ht : 0 < t) (hs_lo : t / 2 ≤ s) (hsne : s ≠ t) (i : ι) :
    |slopeMinusDerivCoeff lam t s i| ≤ 2 / (Real.exp 1 * (t / 2)) := by
  have hτ_pos : 0 < t / 2 := by linarith
  have ht_lo : t / 2 ≤ t := by linarith
  have hslope_bound :
      |(s - t)⁻¹ * (heatCoeff lam s i - heatCoeff lam t i)| ≤ 1 / (Real.exp 1 * (t / 2)) := by
    rw [abs_mul, abs_inv]
    have hmvt := abs_expFactor_sub_le (a := lam i) (τ := t / 2) (u := t) (w := s)
      (hlam i) hτ_pos ht_lo hs_lo
    have hcoeff_diff :
        |heatCoeff lam s i - heatCoeff lam t i| ≤
          (1 / (Real.exp 1 * (t / 2))) * |s - t| := by
      simpa only [heatCoeff_def] using hmvt
    have hne' : |s - t| ≠ 0 := by
      rw [abs_ne_zero]; exact sub_ne_zero.mpr hsne
    rw [inv_mul_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hsne))]
    calc |heatCoeff lam s i - heatCoeff lam t i|
        ≤ (1 / (Real.exp 1 * (t / 2))) * |s - t| := hcoeff_diff
      _ = |s - t| * (1 / (Real.exp 1 * (t / 2))) := by ring
  have hderiv_bound : |heatDerivCoeff lam t i| ≤ 1 / (Real.exp 1 * (t / 2)) := by
    refine le_trans (abs_heatDerivCoeff_le hlam ht i) ?_
    have het_pos : (0 : ℝ) < Real.exp 1 * (t / 2) := mul_pos (Real.exp_pos 1) hτ_pos
    have hmono : Real.exp 1 * (t / 2) ≤ Real.exp 1 * t :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos 1).le
    exact one_div_le_one_div_of_le het_pos hmono
  calc |slopeMinusDerivCoeff lam t s i|
      = |(s - t)⁻¹ * (heatCoeff lam s i - heatCoeff lam t i) - heatDerivCoeff lam t i| := by
        rw [slopeMinusDerivCoeff]
    _ ≤ |(s - t)⁻¹ * (heatCoeff lam s i - heatCoeff lam t i)| + |heatDerivCoeff lam t i| :=
        abs_sub _ _
    _ ≤ 1 / (Real.exp 1 * (t / 2)) + 1 / (Real.exp 1 * (t / 2)) :=
        add_le_add hslope_bound hderiv_bound
    _ = 2 / (Real.exp 1 * (t / 2)) := by ring

private theorem slopeMinusDeriv_normSq_tendsto_zero (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 < t) (v : X) :
    Tendsto (fun s : ℝ =>
        ‖(s - t)⁻¹ • (abstractSpectralSemigroup b hlam s v -
            abstractSpectralSemigroup b hlam t v) -
            abstractSpectralSemigroupDeriv b lam t v‖ ^ 2)
      (𝓝[≠] t) (𝓝 0) := by
  set Cb : ℝ := (2 / (Real.exp 1 * (t / 2))) ^ 2 with hCb_def
  set bound : ι → ℝ := fun i => Cb * (⟪b i, v⟫_ℝ) ^ 2 with hbound_def
  set fmode : ℝ → ι → ℝ := fun s i =>
    (slopeMinusDerivCoeff lam t s i * ⟪b i, v⟫_ℝ) ^ 2 with hfmode_def
  have hbound_summable : Summable bound := by
    rw [hbound_def]; exact (summable_basis_coeff_sq' b v).mul_left Cb
  have hpermode : ∀ i : ι, Tendsto (fun s : ℝ => fmode s i) (𝓝[≠] t) (𝓝 0) := by
    intro i
    rw [hfmode_def]
    have htend := slopeMinusDerivCoeff_tendsto lam t i
    have : Tendsto (fun s : ℝ => slopeMinusDerivCoeff lam t s i * ⟪b i, v⟫_ℝ)
        (𝓝[≠] t) (𝓝 (0 * ⟪b i, v⟫_ℝ)) :=
      htend.mul_const _
    rw [zero_mul] at this
    have hsq := this.pow 2
    simpa using hsq
  have h_event : ∀ᶠ s : ℝ in 𝓝[≠] t,
      (‖(s - t)⁻¹ • (abstractSpectralSemigroup b hlam s v -
          abstractSpectralSemigroup b hlam t v) -
          abstractSpectralSemigroupDeriv b lam t v‖ ^ 2 = ∑' i, fmode s i) ∧
      (∀ i, ‖fmode s i‖ ≤ bound i) := by
    have h_Ioo : Ioo (t / 2) (3 * t / 2) ∈ 𝓝 t := by
      apply Ioo_mem_nhds <;> linarith
    have h_Ioo' : Ioo (t / 2) (3 * t / 2) ∈ 𝓝[≠] t := mem_nhdsWithin_of_mem_nhds h_Ioo
    filter_upwards [h_Ioo', self_mem_nhdsWithin] with s hs_Ioo hs_ne
    have hs_lo : t / 2 ≤ s := hs_Ioo.1.le
    have hsne : s ≠ t := hs_ne
    have hs_nn : 0 ≤ s := by linarith [hs_Ioo.1, ht]
    have heq := slopeMinusDeriv_eq_tsum b hlam ht hs_nn v
    refine ⟨?_, ?_⟩
    · rw [heq]
      have hrw : (fun i : ι => slopeMinusDerivCoeff lam t s i • ⟪b i, v⟫_ℝ • b i) =
          (fun i => (slopeMinusDerivCoeff lam t s i * ⟪b i, v⟫_ℝ) • b i) := by
        funext i; rw [mul_smul]
      rw [hrw]
      have hf_sq_summable : Summable (fun i : ι =>
          (slopeMinusDerivCoeff lam t s i * ⟪b i, v⟫_ℝ) ^ 2) := by
        refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) hbound_summable
        rw [hbound_def]
        have hc := abs_slopeMinusDerivCoeff_le hlam ht hs_lo hsne i
        have hc_sq : (slopeMinusDerivCoeff lam t s i) ^ 2 ≤ Cb := by
          rw [hCb_def]
          have := sq_le_sq' (neg_le_of_abs_le hc) (le_of_abs_le hc)
          simpa using this
        calc (slopeMinusDerivCoeff lam t s i * ⟪b i, v⟫_ℝ) ^ 2
            = (slopeMinusDerivCoeff lam t s i) ^ 2 * (⟪b i, v⟫_ℝ) ^ 2 := by ring
          _ ≤ Cb * (⟪b i, v⟫_ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right hc_sq (sq_nonneg _)
      rw [orthonormal_norm_sq_eq_tsum_sq b _ hf_sq_summable]
    · intro i
      rw [hfmode_def, hbound_def]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hc := abs_slopeMinusDerivCoeff_le hlam ht hs_lo hsne i
      have hc_sq : (slopeMinusDerivCoeff lam t s i) ^ 2 ≤ Cb := by
        rw [hCb_def]
        have := sq_le_sq' (neg_le_of_abs_le hc) (le_of_abs_le hc)
        simpa using this
      calc (slopeMinusDerivCoeff lam t s i * ⟪b i, v⟫_ℝ) ^ 2
          = (slopeMinusDerivCoeff lam t s i) ^ 2 * (⟪b i, v⟫_ℝ) ^ 2 := by ring
        _ ≤ Cb * (⟪b i, v⟫_ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hc_sq (sq_nonneg _)
  have h_tannery : Tendsto (fun s : ℝ => ∑' i, fmode s i) (𝓝[≠] t) (𝓝 (∑' i, (0 : ℝ))) :=
    tendsto_tsum_of_dominated_convergence hbound_summable hpermode
      (h_event.mono (fun s hs => hs.2))
  rw [tsum_zero] at h_tannery
  refine h_tannery.congr' ?_
  filter_upwards [h_event] with s hs
  exact (hs.1).symm

theorem abstractSpectralSemigroup_hasDerivAt (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 < t) (v : X) :
    HasDerivAt (fun u : ℝ => abstractSpectralSemigroup b hlam u v)
      (abstractSpectralSemigroupDeriv b lam t v) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hsq := slopeMinusDeriv_normSq_tendsto_zero b hlam ht v
  have hnorm : Tendsto (fun s : ℝ =>
      ‖(s - t)⁻¹ • (abstractSpectralSemigroup b hlam s v -
          abstractSpectralSemigroup b hlam t v) -
          abstractSpectralSemigroupDeriv b lam t v‖) (𝓝[≠] t) (𝓝 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at hsqrt
    refine hsqrt.congr ?_
    intro s
    rw [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]
  have hX : Tendsto (fun s : ℝ =>
      (s - t)⁻¹ • (abstractSpectralSemigroup b hlam s v -
          abstractSpectralSemigroup b hlam t v) -
          abstractSpectralSemigroupDeriv b lam t v) (𝓝[≠] t) (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).mpr hnorm
  have hX' := hX.add (tendsto_const_nhds
    (x := abstractSpectralSemigroupDeriv b lam t v))
  rw [zero_add] at hX'
  refine hX'.congr ?_
  intro s
  rw [slope_def_module, sub_add_cancel]

end Parabolic
end Analysis

namespace Analysis
namespace Spectral

open Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem tensorHeatSemigroup_intrinsic_hasDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    HasDerivAt
      (fun u : ℝ => tensorHeatSemigroup (I := I) (M := M) g r s u u₀)
      (DifferentialGeometry.Analysis.Parabolic.abstractSpectralSemigroupDeriv
        (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s))
        (TensorEigenIdx.lambda (I := I) (M := M)) t u₀) t :=
  DifferentialGeometry.Analysis.Parabolic.abstractSpectralSemigroup_hasDerivAt
    (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s))
    (fun i => tensor_lambda_nonneg (I := I) (M := M) i) ht u₀

end Spectral
end Analysis
end DifferentialGeometry

end

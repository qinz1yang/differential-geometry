import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false

/-!
# Euclidean anchor alignment (FC20) and raw factor alignment (FC21)

Blueprint 207B, `lem:fibration-euclidean-alignment` (FC20, B:1397) and
`lem:fibration-raw-alignment` (FC21, B:1425).  A map of a Euclidean ball of radius `2a` fixing
zero with additive distortion `δ ≤ a/(20n)` is uniformly `24nδ`-close to ONE orthogonal map on
the ball of radius `a`.  The orthogonal map is the polar factor of the anchor matrix
`V eᵢ = f(a eᵢ)/a`, built from the eigenbasis of `V*V`.
-/

open scoped InnerProductSpace RealInnerProductSpace
open Finset Module

namespace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem abs_sq_sub_sq_le {A B δ : ℝ} (hB : 0 ≤ B) (h : |A - B| ≤ δ) :
    |A ^ 2 - B ^ 2| ≤ δ * (2 * B + δ) := by
  have h1 : A ^ 2 - B ^ 2 = (A - B) * (A + B) := by ring
  have hAB : |A + B| ≤ 2 * B + δ := by
    rw [abs_le] at h ⊢
    constructor <;> nlinarith [abs_nonneg (A - B)]
  rw [h1, abs_mul]
  exact mul_le_mul h hAB (abs_nonneg _) ((abs_nonneg _).trans h)

/-- Polarization error of a map with additive distortion `δ` fixing the origin. -/
theorem abs_inner_map_sub_inner_le (f : E → E) {D : Set E} {δ : ℝ} (h0 : f 0 = 0)
    (hD0 : (0 : E) ∈ D) (hdist : ∀ v ∈ D, ∀ w ∈ D, |‖f v - f w‖ - ‖v - w‖| ≤ δ)
    {v w : E} (hv : v ∈ D) (hw : w ∈ D) :
    |⟪f v, f w⟫ - ⟪v, w⟫| ≤ δ * (‖v‖ + ‖w‖ + ‖v - w‖) + 3 / 2 * δ ^ 2 := by
  have hnv : |‖f v‖ - ‖v‖| ≤ δ := by simpa [h0] using hdist v hv 0 hD0
  have hnw : |‖f w‖ - ‖w‖| ≤ δ := by simpa [h0] using hdist w hw 0 hD0
  have hvw := hdist v hv w hw
  have e1 := abs_sq_sub_sq_le (norm_nonneg v) hnv
  have e2 := abs_sq_sub_sq_le (norm_nonneg w) hnw
  have e3 := abs_sq_sub_sq_le (norm_nonneg (v - w)) hvw
  have p1 : ⟪f v, f w⟫ = (‖f v‖ ^ 2 + ‖f w‖ ^ 2 - ‖f v - f w‖ ^ 2) / 2 := by
    rw [norm_sub_sq_real]; ring
  have p2 : ⟪v, w⟫ = (‖v‖ ^ 2 + ‖w‖ ^ 2 - ‖v - w‖ ^ 2) / 2 := by
    rw [norm_sub_sq_real]; ring
  rw [p1, p2]
  rw [abs_le] at e1 e2 e3 ⊢
  constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

/-- The squared norm in an orthonormal basis. -/
private theorem norm_sq_eq_sum_inner_sq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (x : E) : ‖x‖ ^ 2 = ∑ i, ⟪b i, x⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner x x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm x (b i)]; ring

/-- Coordinatewise domination by two vectors gives the corresponding norm bound. -/
private theorem norm_le_of_inner_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {q x y : E} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h : ∀ j, |⟪b j, q⟫| ≤ C * |⟪b j, x⟫| + D * |⟪b j, y⟫|) :
    ‖q‖ ≤ C * ‖x‖ + D * ‖y‖ := by
  have hrhs : 0 ≤ C * ‖x‖ + D * ‖y‖ := by positivity
  have hcs : (∑ j, |⟪b j, x⟫| * |⟪b j, y⟫|) ^ 2 ≤
      (∑ j, |⟪b j, x⟫| ^ 2) * ∑ j, |⟪b j, y⟫| ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hx : ∑ j, |⟪b j, x⟫| ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_sum_inner_sq b x]; simp [sq_abs]
  have hy : ∑ j, |⟪b j, y⟫| ^ 2 = ‖y‖ ^ 2 := by
    rw [norm_sq_eq_sum_inner_sq b y]; simp [sq_abs]
  rw [hx, hy] at hcs
  have hcs' : ∑ j, |⟪b j, x⟫| * |⟪b j, y⟫| ≤ ‖x‖ * ‖y‖ := by
    have hnn : 0 ≤ ‖x‖ * ‖y‖ := by positivity
    nlinarith [sq_nonneg (∑ j, |⟪b j, x⟫| * |⟪b j, y⟫| - ‖x‖ * ‖y‖),
      sq_nonneg (∑ j, |⟪b j, x⟫| * |⟪b j, y⟫| + ‖x‖ * ‖y‖)]
  have hq : ‖q‖ ^ 2 ≤ (C * ‖x‖ + D * ‖y‖) ^ 2 := by
    rw [norm_sq_eq_sum_inner_sq b q]
    calc ∑ j, ⟪b j, q⟫ ^ 2 ≤ ∑ j, (C * |⟪b j, x⟫| + D * |⟪b j, y⟫|) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h j) 2
      _ = C ^ 2 * ∑ j, |⟪b j, x⟫| ^ 2 + 2 * (C * D) * ∑ j, |⟪b j, x⟫| * |⟪b j, y⟫| +
            D ^ 2 * ∑ j, |⟪b j, y⟫| ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ (C * ‖x‖ + D * ‖y‖) ^ 2 := by
          rw [hx, hy]
          have hCD : 0 ≤ 2 * (C * D) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hcs' hCD]
  exact (pow_le_pow_iff_left₀ (norm_nonneg q) hrhs two_ne_zero).mp hq

private theorem inner_sum_smul_sum_smul {ι : Type*} [Fintype ι] (s : ι → ℝ) (d : ι → E) :
    ⟪∑ i, s i • d i, ∑ j, s j • d j⟫ = ∑ i, ∑ j, s i * s j * ⟪d i, d j⟫ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]; ring

/-- **FC20** (Euclidean anchor alignment), on any finite-dimensional real inner-product space of
dimension `n`: a map of the ball of radius `2a` fixing zero with additive distortion
`δ ≤ a/(20n)` is `24nδ`-close to one linear isometry on the ball of radius `a`. -/
theorem exists_linearIsometryEquiv_anchor_alignment [FiniteDimensional ℝ E] {a δ : ℝ}
    (ha : 0 < a) (hδ : 0 ≤ δ) (hδa : 20 * (finrank ℝ E : ℝ) * δ ≤ a) (f : E → E) (h0 : f 0 = 0)
    (hdist : ∀ v w, ‖v‖ < 2 * a → ‖w‖ < 2 * a → |‖f v - f w‖ - ‖v - w‖| ≤ δ) :
    ∃ Q : E ≃ₗᵢ[ℝ] E, ∀ v, ‖v‖ ≤ a → ‖f v - Q v‖ ≤ 24 * (finrank ℝ E : ℝ) * δ := by
  set n := finrank ℝ E with hn_def
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have hz : ∀ x : E, x = 0 := finrank_zero_iff_forall_zero.mp hn0
    exact ⟨LinearIsometryEquiv.refl ℝ E, fun v _ => by rw [hz (f v - _)]; simp [hn0]⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hδa20 : 20 * δ ≤ a := by nlinarith
  set D : Set E := {v | ‖v‖ < 2 * a} with hD
  have hD0 : (0 : E) ∈ D := by simp only [hD, Set.mem_ofPred_eq, norm_zero]; linarith
  have hpol : ∀ {v w : E}, v ∈ D → w ∈ D →
      |⟪f v, f w⟫ - ⟪v, w⟫| ≤ δ * (‖v‖ + ‖w‖ + ‖v - w‖) + 3 / 2 * δ ^ 2 :=
    fun hv hw => abs_inner_map_sub_inner_le f h0 hD0 (fun v hv w hw => hdist v w hv hw) hv hw
  let b : OrthonormalBasis (Fin n) ℝ E := stdOrthonormalBasis ℝ E
  have hnb : ∀ i, ‖a • b i‖ = a := fun i => by
    rw [norm_smul, b.norm_eq_one, mul_one, Real.norm_eq_abs, abs_of_pos ha]
  have hbD : ∀ i, a • b i ∈ D := fun i => by
    simp only [hD, Set.mem_ofPred_eq, hnb]; linarith
  let c : Fin n → E := fun i => a⁻¹ • f (a • b i)
  -- Gram estimate
  have hgram : ∀ i j, |⟪c i, c j⟫ - ⟪b i, b j⟫| ≤ 5 * δ / a := by
    intro i j
    have key := hpol (hbD i) (hbD j)
    rw [hnb, hnb] at key
    have hsub : ‖a • b i - a • b j‖ ≤ 2 * a := by
      calc ‖a • b i - a • b j‖ ≤ ‖a • b i‖ + ‖a • b j‖ := norm_sub_le _ _
        _ = 2 * a := by rw [hnb, hnb]; ring
    have hcc : ⟪c i, c j⟫ = a⁻¹ * a⁻¹ * ⟪f (a • b i), f (a • b j)⟫ := by
      simp only [c, real_inner_smul_left, real_inner_smul_right]; ring
    have hbb : ⟪b i, b j⟫ = a⁻¹ * a⁻¹ * ⟪a • b i, a • b j⟫ := by
      rw [real_inner_smul_left, real_inner_smul_right]; field_simp
    rw [hcc, hbb, ← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < a⁻¹ * a⁻¹)]
    have hb : |⟪f (a • b i), f (a • b j)⟫ - ⟪a • b i, a • b j⟫| ≤ 4 * a * δ + 3 / 2 * δ ^ 2 := by
      have : δ * (a + a + ‖a • b i - a • b j‖) ≤ δ * (4 * a) :=
        mul_le_mul_of_nonneg_left (by linarith) hδ
      linarith
    calc a⁻¹ * a⁻¹ * |⟪f (a • b i), f (a • b j)⟫ - ⟪a • b i, a • b j⟫|
        ≤ a⁻¹ * a⁻¹ * (4 * a * δ + 3 / 2 * δ ^ 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ 5 * δ / a := by
          rw [div_eq_mul_inv]
          have hk : 4 * a * δ + 3 / 2 * δ ^ 2 ≤ 5 * a * δ := by nlinarith
          calc a⁻¹ * a⁻¹ * (4 * a * δ + 3 / 2 * δ ^ 2) ≤ a⁻¹ * a⁻¹ * (5 * a * δ) :=
                mul_le_mul_of_nonneg_left hk (by positivity)
            _ = 5 * δ * a⁻¹ := by field_simp
  -- the anchor map
  let V : E →L[ℝ] E := ∑ i, (innerSL ℝ (b i)).smulRight (c i)
  have hV : ∀ x, V x = ∑ i, ⟪b i, x⟫ • c i := fun x => by
    simp [V]
  have hVb : ∀ k, V (b k) = c k := fun k => by
    rw [hV]; simp [b.inner_eq_ite]
  -- quadratic form estimate
  set η : ℝ := 5 * n * δ / a with hη_def
  have hη0 : 0 ≤ η := by positivity
  have hη : η ≤ 1 / 4 := by
    rw [hη_def, div_le_iff₀ ha]; nlinarith
  have hquad : ∀ x, |‖V x‖ ^ 2 - ‖x‖ ^ 2| ≤ η * ‖x‖ ^ 2 := by
    intro x
    have hx : x = ∑ i, ⟪b i, x⟫ • b i := (b.sum_repr' x).symm
    have h1 : ‖V x‖ ^ 2 = ∑ i, ∑ j, ⟪b i, x⟫ * ⟪b j, x⟫ * ⟪c i, c j⟫ := by
      rw [← real_inner_self_eq_norm_sq, hV, inner_sum_smul_sum_smul]
    have h2 : ‖x‖ ^ 2 = ∑ i, ∑ j, ⟪b i, x⟫ * ⟪b j, x⟫ * ⟪b i, b j⟫ := by
      rw [← real_inner_self_eq_norm_sq]
      conv_lhs => rw [hx]
      rw [inner_sum_smul_sum_smul]
    have hsq : (∑ i, |⟪b i, x⟫|) ^ 2 ≤ n * ‖x‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => |⟪b i, x⟫|)
      rw [norm_sq_eq_sum_inner_sq b x]
      simpa [sq_abs] using this
    have hdiff : ‖V x‖ ^ 2 - ‖x‖ ^ 2 = ∑ i, (∑ j, ⟪b i, x⟫ * ⟪b j, x⟫ * ⟪c i, c j⟫ -
        ∑ j, ⟪b i, x⟫ * ⟪b j, x⟫ * ⟪b i, b j⟫) := by
      rw [h1, h2, ← Finset.sum_sub_distrib]
    rw [hdiff]
    calc |∑ i, (∑ j, ⟪b i, x⟫ * ⟪b j, x⟫ * ⟪c i, c j⟫ - ∑ j, ⟪b i, x⟫ * ⟪b j, x⟫ * ⟪b i, b j⟫)|
        ≤ ∑ i, ∑ j, |⟪b i, x⟫| * |⟪b j, x⟫| * (5 * δ / a) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [← Finset.sum_sub_distrib]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [← mul_sub, abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hgram i j) (by positivity)
      _ = 5 * δ / a * (∑ i, |⟪b i, x⟫|) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ 5 * δ / a * (n * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = η * ‖x‖ ^ 2 := by rw [hη_def]; ring
  -- spectral decomposition of `V* V`
  let VL : E →ₗ[ℝ] E := (V : E →ₗ[ℝ] E)
  let T : E →ₗ[ℝ] E := LinearMap.adjoint VL * VL
  have hT : T.IsSymmetric := LinearMap.isSymmetric_adjoint_mul_self VL
  have hfr : finrank ℝ E = n := rfl
  let u : OrthonormalBasis (Fin n) ℝ E := hT.eigenvectorBasis hfr
  let lam : Fin n → ℝ := hT.eigenvalues hfr
  have hTu : ∀ j, T (u j) = lam j • u j := fun j => hT.apply_eigenvectorBasis hfr j
  have hTinner : ∀ x y, ⟪T x, y⟫ = ⟪V x, V y⟫ := fun x y => by
    change ⟪LinearMap.adjoint VL (VL x), y⟫ = _
    rw [LinearMap.adjoint_inner_left]; rfl
  have hlam : ∀ j, lam j = ‖V (u j)‖ ^ 2 := fun j => by
    rw [← real_inner_self_eq_norm_sq, ← hTinner, hTu, real_inner_smul_left,
      real_inner_self_eq_norm_sq, u.norm_eq_one]; ring
  have hlam_close : ∀ j, |lam j - 1| ≤ η := fun j => by
    have := hquad (u j)
    rwa [u.norm_eq_one, one_pow, mul_one, ← hlam] at this
  have hlam_low : ∀ j, 3 / 4 ≤ lam j := fun j => by
    have := (abs_le.mp (hlam_close j)).1; linarith
  let sc : Fin n → ℝ := fun j => (Real.sqrt (lam j))⁻¹
  have hsqrt_pos : ∀ j, 0 < Real.sqrt (lam j) := fun j => Real.sqrt_pos.mpr (by linarith [hlam_low j])
  have hsqrt_half : ∀ j, 1 / 2 ≤ Real.sqrt (lam j) := fun j => by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith [hlam_low j])
  have hsc2 : ∀ j, |sc j| ≤ 2 := fun j => by
    rw [abs_of_pos (inv_pos.mpr (hsqrt_pos j))]
    rw [inv_le_comm₀ (hsqrt_pos j) (by norm_num)]; linarith [hsqrt_half j]
  have hsc1 : ∀ j, |sc j - 1| ≤ 2 * η := fun j => by
    have hs := hsqrt_pos j
    have hsq : Real.sqrt (lam j) ^ 2 = lam j := Real.sq_sqrt (by linarith [hlam_low j])
    have h1 : |1 - Real.sqrt (lam j)| ≤ |1 - lam j| := by
      have hfac : 1 - lam j = (1 - Real.sqrt (lam j)) * (1 + Real.sqrt (lam j)) := by
        linear_combination hsq
      rw [hfac, abs_mul, abs_of_pos (by linarith : 0 < 1 + Real.sqrt (lam j))]
      nlinarith [abs_nonneg (1 - Real.sqrt (lam j))]
    have hrw : sc j - 1 = (1 - Real.sqrt (lam j)) * (Real.sqrt (lam j))⁻¹ := by
      simp only [sc]; field_simp
    rw [hrw, abs_mul, abs_of_pos (inv_pos.mpr hs)]
    have hinv : (Real.sqrt (lam j))⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hs (by norm_num)]; linarith [hsqrt_half j]
    have h2 : |1 - lam j| ≤ η := by rw [abs_sub_comm]; exact hlam_close j
    calc |1 - Real.sqrt (lam j)| * (Real.sqrt (lam j))⁻¹ ≤ η * 2 :=
          mul_le_mul (h1.trans h2) hinv (by positivity) hη0
      _ = 2 * η := by ring
  -- the polar factor
  let w : Fin n → E := fun j => sc j • V (u j)
  have hon : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro j k
    have : ⟪w j, w k⟫ = sc j * sc k * (lam j * ⟪u j, u k⟫) := by
      simp only [w, real_inner_smul_left, real_inner_smul_right, ← hTinner, hTu]
      ring
    rw [this, u.inner_eq_ite]
    split_ifs with hjk
    · subst hjk
      have hsq : Real.sqrt (lam j) ^ 2 = lam j := Real.sq_sqrt (by linarith [hlam_low j])
      have hs := (hsqrt_pos j).ne'
      simp only [sc, mul_one]
      rw [← mul_inv, ← sq, hsq]
      exact inv_mul_cancel₀ (by linarith [hlam_low j])
    · ring
  let wb : OrthonormalBasis (Fin n) ℝ E := OrthonormalBasis.mk hon
    (hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [hfr])).ge
  let Q : E ≃ₗᵢ[ℝ] E := u.repr.trans wb.repr.symm
  have hQu : ∀ j, Q (u j) = w j := fun j => by
    simp [Q, wb, OrthonormalBasis.repr_self, OrthonormalBasis.repr_symm_single]
  refine ⟨Q, fun v hv => ?_⟩
  have hvD : v ∈ D := by simp only [hD, Set.mem_ofPred_eq]; linarith
  set y := f v with hy
  let z : E := LinearMap.adjoint VL y
  have hz_inner : ∀ x, ⟪z, x⟫ = ⟪y, V x⟫ := fun x => by
    simp only [z, LinearMap.adjoint_inner_left]; rfl
  -- the anchor vector is close to `v`
  have hzv : ‖z - v‖ ≤ 6 * Real.sqrt n * δ := by
    have hcoord : ∀ i, |⟪b i, z - v⟫| ≤ 6 * δ := by
      intro i
      have key := hpol hvD (hbD i)
      rw [hnb] at key
      have hsub : ‖v - a • b i‖ ≤ 2 * a := by
        calc ‖v - a • b i‖ ≤ ‖v‖ + ‖a • b i‖ := norm_sub_le _ _
          _ ≤ 2 * a := by rw [hnb]; linarith
      have hval : ⟪b i, z - v⟫ = a⁻¹ * (⟪f v, f (a • b i)⟫ - ⟪v, a • b i⟫) := by
        rw [inner_sub_right, real_inner_comm, hz_inner, hVb, real_inner_smul_right,
          real_inner_smul_right, real_inner_comm v (b i)]
        field_simp
        rfl
      rw [hval, abs_mul, abs_of_pos (inv_pos.mpr ha)]
      have hb : |⟪f v, f (a • b i)⟫ - ⟪v, a • b i⟫| ≤ 4 * a * δ + 3 / 2 * δ ^ 2 := by
        have : δ * (‖v‖ + a + ‖v - a • b i‖) ≤ δ * (4 * a) :=
          mul_le_mul_of_nonneg_left (by linarith) hδ
        rw [← hy] at key
        linarith
      rw [inv_mul_le_iff₀ ha]
      nlinarith
    have hsq : ‖z - v‖ ^ 2 ≤ (6 * Real.sqrt n * δ) ^ 2 := by
      rw [norm_sq_eq_sum_inner_sq b, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      calc ∑ i, ⟪b i, z - v⟫ ^ 2 ≤ (Finset.univ : Finset (Fin n)).card • (6 * δ) ^ 2 := by
            refine Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2
        _ = 6 ^ 2 * n * δ ^ 2 := by simp; ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  -- coordinates of `Q⁻¹ y - v` in the eigenbasis
  have hcoordQ : ∀ j, |⟪u j, Q.symm y - v⟫| ≤ 2 * |⟪u j, z - v⟫| + 2 * η * |⟪u j, v⟫| := by
    intro j
    have h1 : ⟪u j, Q.symm y⟫ = sc j * ⟪u j, z⟫ := by
      rw [← Q.inner_map_map, hQu, LinearIsometryEquiv.apply_symm_apply]
      simp only [w, real_inner_smul_left]
      rw [real_inner_comm, ← hz_inner, real_inner_comm]
    have h2 : ⟪u j, Q.symm y - v⟫ = sc j * ⟪u j, z - v⟫ + (sc j - 1) * ⟪u j, v⟫ := by
      rw [inner_sub_right, h1, inner_sub_right]; ring
    rw [h2]
    calc |sc j * ⟪u j, z - v⟫ + (sc j - 1) * ⟪u j, v⟫|
        ≤ |sc j| * |⟪u j, z - v⟫| + |sc j - 1| * |⟪u j, v⟫| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 2 * |⟪u j, z - v⟫| + 2 * η * |⟪u j, v⟫| := by
          gcongr
          · exact hsc2 j
          · exact hsc1 j
  have hQ : ‖Q.symm y - v‖ ≤ 2 * ‖z - v‖ + 2 * η * ‖v‖ :=
    norm_le_of_inner_le u (by norm_num) (by positivity) hcoordQ
  have hfinal : ‖f v - Q v‖ = ‖Q.symm y - v‖ := by
    rw [← Q.symm.norm_map, map_sub, LinearIsometryEquiv.symm_apply_apply]
  rw [hfinal]
  have hsqrtn : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  calc ‖Q.symm y - v‖ ≤ 2 * ‖z - v‖ + 2 * η * ‖v‖ := hQ
    _ ≤ 2 * (6 * Real.sqrt n * δ) + 2 * η * a := by
        gcongr
    _ = 12 * Real.sqrt n * δ + 10 * n * δ := by rw [hη_def]; field_simp; ring
    _ ≤ 24 * n * δ := by nlinarith

/-- **FC20** in the blueprint's coordinates `ℝⁿ`. -/
theorem exists_linearIsometryEquiv_anchor_alignment_euclidean {n : ℕ} {a δ : ℝ} (ha : 0 < a)
    (hδ : 0 ≤ δ) (hδa : 20 * (n : ℝ) * δ ≤ a)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (h0 : f 0 = 0)
    (hdist : ∀ v w, ‖v‖ < 2 * a → ‖w‖ < 2 * a → |‖f v - f w‖ - ‖v - w‖| ≤ δ) :
    ∃ Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ v, ‖v‖ ≤ a → ‖f v - Q v‖ ≤ 24 * (n : ℝ) * δ := by
  have h := exists_linearIsometryEquiv_anchor_alignment ha hδ
    (by rwa [finrank_euclideanSpace_fin]) f h0 hdist
  rwa [finrank_euclideanSpace_fin] at h

/-- The verbatim blueprint form of FC20 (`n ≥ 1`, `δ ≤ a/(20n)`); the hypothesis `n ≥ 1` is
unused by `exists_linearIsometryEquiv_anchor_alignment_euclidean`. -/
example {n : ℕ} (hn : 1 ≤ n) {a δ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (hδa : δ ≤ a / (20 * n))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (h0 : f 0 = 0)
    (hdist : ∀ v w, ‖v‖ < 2 * a → ‖w‖ < 2 * a → |‖f v - f w‖ - ‖v - w‖| ≤ δ) :
    ∃ Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ v, ‖v‖ ≤ a → ‖f v - Q v‖ ≤ 24 * (n : ℝ) * δ := by
  have hn' : (0 : ℝ) < 20 * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine exists_linearIsometryEquiv_anchor_alignment_euclidean ha hδ ?_ f h0 hdist
  rwa [le_div_iff₀ hn', mul_comm] at hδa

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- **FC21** (raw factor alignment): composing the raw coisometry `P` with the single orthogonal
map of FC20 gives one coisometry `A = QP` and translation `b₀ = d - Qc` with value error
`e_c + 24kδ` on the whole specified set. -/
theorem exists_coisometry_raw_factor_alignment {X : Type*} (u : X → F) (Ψ : X → G)
    (P : F →L[ℝ] G) (hP : P.comp (ContinuousLinearMap.adjoint P) = ContinuousLinearMap.id ℝ G)
    (c d : G) {a δ ec : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (hδa : 20 * (finrank ℝ G : ℝ) * δ ≤ a)
    (f : G → G) (h0 : f 0 = 0)
    (hdist : ∀ v w, ‖v‖ < 2 * a → ‖w‖ < 2 * a → |‖f v - f w‖ - ‖v - w‖| ≤ δ)
    (hraw : ∀ x, ‖Ψ x - f (P (u x) - c) - d‖ ≤ ec) (hball : ∀ x, ‖P (u x) - c‖ ≤ a) :
    ∃ A : F →L[ℝ] G, ∃ b₀ : G,
      A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ G ∧
        ∀ x, ‖Ψ x - A (u x) - b₀‖ ≤ ec + 24 * (finrank ℝ G : ℝ) * δ := by
  obtain ⟨Q, hQ⟩ := exists_linearIsometryEquiv_anchor_alignment ha hδ hδa f h0 hdist
  refine ⟨(Q : G →L[ℝ] G).comp P, d - Q c, ?_, fun x => ?_⟩
  · rw [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm]
    ext y
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    have := congrArg (fun T : G →L[ℝ] G => T (Q.symm y)) hP
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
    change Q (P (ContinuousLinearMap.adjoint P (Q.symm y))) = y
    rw [this]
    exact Q.apply_symm_apply y
  · have hsplit : Ψ x - ((Q : G →L[ℝ] G).comp P) (u x) - (d - Q c) =
        (Ψ x - f (P (u x) - c) - d) + (f (P (u x) - c) - Q (P (u x) - c)) := by
      change Ψ x - Q (P (u x)) - (d - Q c) = _
      rw [map_sub]
      abel
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add (hraw x) (hQ _ (hball x)))

/-- FC21 when the factor map does not fix zero: its value at zero is moved into `d` first. -/
theorem exists_coisometry_raw_factor_alignment_of_offset {X : Type*} (u : X → F) (Ψ : X → G)
    (P : F →L[ℝ] G) (hP : P.comp (ContinuousLinearMap.adjoint P) = ContinuousLinearMap.id ℝ G)
    (c d : G) {a δ ec : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (hδa : 20 * (finrank ℝ G : ℝ) * δ ≤ a)
    (f : G → G) (hdist : ∀ v w, ‖v‖ < 2 * a → ‖w‖ < 2 * a → |‖f v - f w‖ - ‖v - w‖| ≤ δ)
    (hraw : ∀ x, ‖Ψ x - f (P (u x) - c) - d‖ ≤ ec) (hball : ∀ x, ‖P (u x) - c‖ ≤ a) :
    ∃ A : F →L[ℝ] G, ∃ b₀ : G,
      A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ G ∧
        ∀ x, ‖Ψ x - A (u x) - b₀‖ ≤ ec + 24 * (finrank ℝ G : ℝ) * δ := by
  refine exists_coisometry_raw_factor_alignment u Ψ P hP c (d + f 0) ha hδ hδa
    (fun v => f v - f 0) (sub_self _) (fun v w hv hw => ?_) (fun x => ?_) hball
  · simpa using hdist v w hv hw
  · have : Ψ x - (f (P (u x) - c) - f 0) - (d + f 0) = Ψ x - f (P (u x) - c) - d := by abel
    rw [this]; exact hraw x

end InnerProductSpace

import DifferentialGeometry.Analysis.Sobolev.Nirenberg.CrossBoundsNonSmooth_Master
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.StandardNirenbergTest
import DifferentialGeometry.Analysis.Sobolev.Solutions.WeakSolution

/-!
# Non-smooth substitution identity, principal-term lower bound, and
master inequality discharge

This module produces the non-smooth analogues of three building blocks
used in the smooth derivation of the Nirenberg interior `H²` estimate.
For a non-smooth weak solution `u ∈ L²` of a uniformly elliptic
divergence-form equation `B(u, ·) = ⟨f, ·⟩` with weak partials
`g i ∈ L²` (`DeGiorgi.HasWeakPartialDeriv i (g i) u Set.univ`) and
`f ∈ L²`, we establish:

* `nirenberg_substitution_identity_nonsmooth` — the algebraic identity
  resulting from substituting the symmetric Nirenberg test function
  `v_h := D_{-h}^k(η² · D_h^k u)` into the variational identity and
  expanding via the discrete product rule. The expanded form uses the
  weak partials `g i` in place of the classical partials `(fderiv u) e_i`.

* `principal_term_ge_lambda_norm_sq_nonsmooth` — the pointwise
  ellipticity bound applied to the difference-quotient gradient
  `D_h^k g_i`, integrated against `η²`. This is purely pointwise and
  independent of the weak structure of `u`.

* `nirenberg_master_inequality_nonsmooth` — the headline absorbing
  inequality
  `λ · ∫ η² ∑ (D_h^k g_i)² ≤ (λ/2) · ∫ η² ∑ (D_h^k g_i)² +
     C · (∫ ∑ g_i² + ∫ u² + ∫ f²)`,
  obtained by combining the substitution identity with the principal
  bound and the five Young absorbing bounds.

## Strategy

The substitution identity is established by approximating `u` with the
mollification `u_ε` (smooth on the whole space and a smooth weak
solution of `L u_ε = classicalApply u_ε`), applying the smooth
substitution identity, and passing to the L² limit. The L² convergence
inputs:

* `mollifyEps hε u → u` in L² uniformly on compact subsets;
* the classical partial of `mollifyEps hε u` equals
  `mollifyEps hε (g i)` and converges to `g i` in L²;
* the difference quotient `D_h^k (mollifyEps hε u)` converges to
  `D_h^k u` in L² (linearity + L² convergence of mollification);
* analogously for `D_h^k (g i)`.

The identification of the right-hand side `f`-data uses the duality
identity `integral_classicalApply_mollifyEps_sub_eq_bilin_sub`.

The principal-term bound is a direct consequence of the pointwise
ellipticity coercivity at the shifted point `x + h e_k`.

The master inequality discharge applies the existing combinator
`nirenberg_master_inequality_after_young_nonsmooth`, supplying
`h_master_nonsmooth` from the substitution identity and the principal
bound via the triangle inequality.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitutionNonSmooth

variable {d : ℕ} [NeZero d]

local notation "EuclN" => EuclideanSpace ℝ (Fin d)

/-- Pointwise ellipticity at the shifted point: for any vector
`V : Fin d → ℝ`, when `x + h e_k ∈ Ω`,
`∑_{i j} a^{ij}(x + h e_k) · V i · V j ≥ λ · ∑_i (V i)²`. -/
private lemma shiftedEllipticity_pointwise
    {Ω : Set EuclN} (B : SmoothEllipticBilinearForm d Ω)
    (V : Fin d → ℝ) (k : Fin d) (h : ℝ) {x : EuclN}
    (hx_translate : x + h • EuclideanSpace.single k 1 ∈ Ω) :
    B.lam * ∑ i : Fin d, (V i)^2 ≤
      ∑ i : Fin d, ∑ j : Fin d,
        B.a (x + h • EuclideanSpace.single k 1) i j * V i * V j := by
  classical
  set y : EuclN := x + h • EuclideanSpace.single k 1 with hy_def
  set ξ : EuclN := WithLp.toLp 2 V with hξ_def
  have hξ_ofLp : ξ.ofLp = V := by
    change (WithLp.toLp 2 V : EuclN).ofLp = V
    rfl
  have hξ_norm_sq : ‖ξ‖ ^ 2 = ∑ i : Fin d, (V i)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl ?_
    intro i _
    change ‖(WithLp.toLp 2 V : EuclN) i‖ ^ 2 = _
    have : (WithLp.toLp 2 V : EuclN) i = V i := by rfl
    rw [this, Real.norm_eq_abs, sq_abs]
  have hcoer : B.lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE (B.a y) ξ⟫_ℝ :=
    B.coercive y hx_translate ξ
  have h_inner :
      ⟪ξ, DeGiorgi.matMulE (B.a y) ξ⟫_ℝ =
        ∑ i : Fin d, ∑ j : Fin d, B.a y i j * V i * V j := by
    have hmat_ofLp : (DeGiorgi.matMulE (B.a y) ξ).ofLp = (B.a y).mulVec V := by
      rw [DeGiorgi.matMulE_ofLp, hξ_ofLp]
    change (DeGiorgi.matMulE (B.a y) ξ).ofLp ⬝ᵥ star ξ.ofLp = _
    rw [hmat_ofLp, hξ_ofLp]
    have hstarV : (star V : Fin d → ℝ) = V := by funext i; simp
    rw [hstarV]
    change ∑ i : Fin d, (B.a y).mulVec V i * V i = _
    refine Finset.sum_congr rfl ?_
    intro i _
    change (∑ j : Fin d, B.a y i j * V j) * V i = _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [h_inner] at hcoer
  rw [← hξ_norm_sq]
  exact hcoer

/-- The integral lower bound on the principal term, expressed in terms
of explicit weak partials `g i`. The bound is purely pointwise + a
nonneg weight (`η²`) and integration. No smoothness on `u` or `g i` is
needed; the only requirement is that the difference quotients of `g i`
make sense pointwise and integrate to a finite value (provided by
`MemLp` and the cutoff `η`). -/
theorem principal_term_ge_lambda_norm_sq_nonsmooth
    {Ω : Set EuclN} (B : SmoothEllipticBilinearForm d Ω)
    {u : EuclN → ℝ}
    (_hu_l2 : MemLp u 2 (volume : Measure EuclN))
    {g : Fin d → EuclN → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure EuclN))
    (_h_weakPartial : ∀ i, DeGiorgi.HasWeakPartialDeriv (d := d) i (g i) u Set.univ)
    {η : EuclN → ℝ} (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_supp : HasCompactSupport η)
    (_hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {Ω' : Set EuclN} (_hΩ' : IsOpen Ω') (_hΩ'_compact : IsCompact (closure Ω'))
    (hΩ'_in_Ω : closure Ω' ⊆ Ω)
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) {h : ℝ} (_hh : h ≠ 0) (hh_le : |h| ≤ R₀) :
    B.lam *
      ∫ x, (η x)^2 *
        ∑ i : Fin d, (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2
        ∂(volume : Measure EuclN)
    ≤ ∫ x, ∑ i : Fin d, ∑ j : Fin d,
        (DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : EuclN => B.a y i j)) x *
        (η x)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x
      ∂(volume : Measure EuclN) := by
  classical
  have h_thick_in_Ω : Metric.cthickening |h| (tsupport η) ⊆ Ω :=
    (hh_supp_in_Ω' hh_le).trans (subset_closure.trans hΩ'_in_Ω)
  have h_pointwise : ∀ x : EuclN,
      B.lam * ((η x)^2 *
          ∑ i : Fin d, (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2) ≤
        ∑ i : Fin d, ∑ j : Fin d,
          (DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x := by
    intro x
    by_cases hx : x ∈ tsupport η
    · have hx_translate : x + h • EuclideanSpace.single k 1 ∈ Ω := by
        apply h_thick_in_Ω
        refine Metric.mem_cthickening_of_dist_le _ x |h| (tsupport η) hx ?_
        have hsing_norm :
            ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
        have hdist_eq :
            dist (x + h • EuclideanSpace.single k 1) x = |h| := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hsing_norm, mul_one,
            Real.norm_eq_abs]
        rw [hdist_eq]
      set V : Fin d → ℝ := fun i =>
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x with hV_def
      have h_ellip := shiftedEllipticity_pointwise (d := d) B V k h hx_translate
      have h_eta_nn : 0 ≤ (η x)^2 := sq_nonneg _
      have h_mul := mul_le_mul_of_nonneg_left h_ellip h_eta_nn
      have h_translate_eq : ∀ i j : Fin d,
          DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : EuclN => B.a y i j) x =
          B.a (x + h • EuclideanSpace.single k 1) i j := by
        intro i j; rfl
      have h_lhs_eq :
          B.lam * ((η x)^2 * ∑ i : Fin d, (V i)^2) =
            (η x)^2 * (B.lam * ∑ i : Fin d, (V i)^2) := by ring
      rw [h_lhs_eq]
      refine h_mul.trans ?_
      apply le_of_eq
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [h_translate_eq i j]
      ring
    · have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      have h_lhs : B.lam * ((η x)^2 *
          ∑ i : Fin d, (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2) = 0 := by
        rw [hη_zero]; ring
      rw [h_lhs]
      have h_rhs_eq : ∑ i : Fin d, ∑ j : Fin d,
          (DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i _
        refine Finset.sum_eq_zero ?_
        intro j _
        rw [hη_zero]; ring
      rw [h_rhs_eq]
  have h_lhs_factor :
      B.lam *
        ∫ x, (η x)^2 *
          ∑ i : Fin d, (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2
        ∂(volume : Measure EuclN) =
      ∫ x, B.lam * ((η x)^2 *
          ∑ i : Fin d, (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2)
        ∂(volume : Measure EuclN) := by
    rw [integral_const_mul]
  rw [h_lhs_factor]
  have hη_smooth_top : ContDiff ℝ (⊤ : ℕ∞) η := hη_smooth
  have h_lhs_int : Integrable (fun x : EuclN => B.lam * ((η x)^2 *
      ∑ i : Fin d, (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2))
      (volume : Measure EuclN) := by
    have h_per_i : ∀ i : Fin d, Integrable (fun x : EuclN =>
        (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2)
        (volume : Measure EuclN) := by
      intro i
      have hint := integrable_const_eta_sq_diffQuot_g_sq (d := d) hg_l2 hη_smooth_top
        hη_supp i k h 1
      have h_eq : (fun x : EuclN => (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2) =
          (fun x : EuclN => 1 * (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2) := by
        funext x; ring
      rw [h_eq]
      exact hint
    have h_sum_int := integrable_finset_sum (Finset.univ : Finset (Fin d))
      (fun i _ => h_per_i i)
    have h_eq_outer : (fun x : EuclN => B.lam * ((η x)^2 *
        ∑ i : Fin d, (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2)) =
        (fun x : EuclN => B.lam * ∑ i : Fin d,
          (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2) := by
      funext x
      rw [Finset.mul_sum]
    rw [h_eq_outer]
    exact h_sum_int.const_mul B.lam
  have h_rhs_per_ij_int : ∀ i j : Fin d, Integrable (fun x : EuclN =>
      (DifferentialGeometry.Analysis.Sobolev.translate k h
        (fun y : EuclN => B.a y i j)) x *
      (η x)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x)
      (volume : Measure EuclN) := by
    intro i j
    classical
    have hη_sq_cont : Continuous (fun x : EuclN => η x ^ 2) := hη_smooth.continuous.pow 2
    have hη_sq_supp : HasCompactSupport (fun x : EuclN => η x ^ 2) := by
      have heq : (fun y : EuclN => η y ^ 2) = (fun y : EuclN => η y * η y) := by
        funext y; ring
      rw [heq]; exact hη_supp.mul_right
    obtain ⟨Mη2, _, hMη2⟩ :=
      exists_bound_of_continuous_compactSupport hη_sq_cont hη_sq_supp
    have h_translate_a_cont : Continuous
        (DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : EuclN => B.a y i j)) := by
      unfold DifferentialGeometry.Analysis.Sobolev.translate
      exact (B.continuous_a i j).comp (continuous_id.add continuous_const)
    have h_prod_cont : Continuous
        (fun x : EuclN => (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x) :=
      hη_sq_cont.mul h_translate_a_cont
    have h_prod_supp : HasCompactSupport
        (fun x : EuclN => (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x) :=
      hη_sq_supp.mul_right
    obtain ⟨Mprod, hMprod_nn, hMprod⟩ :=
      exists_bound_of_continuous_compactSupport h_prod_cont h_prod_supp
    have h_dq_g_l2 : ∀ i', MemLp
        (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i')) 2
        (volume : Measure EuclN) :=
      fun i' => memLp_diffQuot_two k h (hg_l2 i')
    have h_dq_g_sq_int : ∀ i', Integrable (fun x : EuclN =>
        (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i') x)^2)
        (volume : Measure EuclN) := by
      intro i'
      have h_dq_norm_sq_int : Integrable (fun x : EuclN =>
          ‖DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i') x‖ ^ (2 : ℕ))
          (volume : Measure EuclN) := by
        have hh := (h_dq_g_l2 i').integrable_norm_rpow
          (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        have h_pow_eq : (2 : ℝ≥0∞).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
        rw [h_pow_eq] at hh
        have heq : (fun x : EuclN =>
            ‖DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i') x‖ ^ (2 : ℝ)) =
            (fun x : EuclN =>
            ‖DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i') x‖ ^ (2 : ℕ)) := by
          funext x
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
        rw [heq] at hh
        exact hh
      have heq2 : (fun x : EuclN =>
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i') x)^2) =
          (fun x : EuclN =>
          ‖DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i') x‖ ^ (2 : ℕ)) := by
        funext x
        rw [Real.norm_eq_abs, sq_abs]
      rw [heq2]
      exact h_dq_norm_sq_int
    have h_upper_int : Integrable (fun x : EuclN => (Mprod / 2) *
        ((DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2 +
         (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x)^2))
        (volume : Measure EuclN) :=
      ((h_dq_g_sq_int i).add (h_dq_g_sq_int j)).const_mul (Mprod / 2)
    have h_lhs_aesm : AEStronglyMeasurable
        (fun x : EuclN =>
          (DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x)
        (volume : Measure EuclN) := by
      have h_ta_aesm : AEStronglyMeasurable
          (DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : EuclN => B.a y i j))
          (volume : Measure EuclN) := h_translate_a_cont.aestronglyMeasurable
      have h_eta_aesm : AEStronglyMeasurable (fun x : EuclN => (η x)^2)
          (volume : Measure EuclN) := hη_sq_cont.aestronglyMeasurable
      have h_dq_aesm_i : AEStronglyMeasurable
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i))
          (volume : Measure EuclN) :=
        aestronglyMeasurable_diffQuot (d := d) k h (hg_l2 i).aestronglyMeasurable
      have h_dq_aesm_j : AEStronglyMeasurable
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j))
          (volume : Measure EuclN) :=
        aestronglyMeasurable_diffQuot (d := d) k h (hg_l2 j).aestronglyMeasurable
      exact ((h_ta_aesm.mul h_eta_aesm).mul h_dq_aesm_i).mul h_dq_aesm_j
    refine h_upper_int.mono' h_lhs_aesm ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    set X : ℝ := DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x with hX_def
    set Y : ℝ := DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x with hY_def
    set τaη2 : ℝ := (DifferentialGeometry.Analysis.Sobolev.translate k h
        (fun y : EuclN => B.a y i j)) x * (η x)^2 with hτaη2_def
    have h_τaη2_eq_swap : (DifferentialGeometry.Analysis.Sobolev.translate k h
        (fun y : EuclN => B.a y i j)) x * (η x)^2 =
        (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : EuclN => B.a y i j)) x := by ring
    have h_τaη2_bound : |τaη2| ≤ Mprod := by
      rw [hτaη2_def]
      have hb := hMprod x
      have h_swap_eq :
          (DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x * (η x) ^ 2 =
          (η x) ^ 2 * (DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x := by ring
      rw [h_swap_eq]
      exact hb
    have h_lhs_eq : (DifferentialGeometry.Analysis.Sobolev.translate k h
        (fun y : EuclN => B.a y i j)) x * (η x)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x =
        τaη2 * X * Y := by
      change (DifferentialGeometry.Analysis.Sobolev.translate k h
        (fun y : EuclN => B.a y i j)) x * (η x)^2 * X * Y =
        (DifferentialGeometry.Analysis.Sobolev.translate k h
        (fun y : EuclN => B.a y i j)) x * (η x)^2 * X * Y
      rfl
    rw [h_lhs_eq]
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h_iX_nn : 0 ≤ |X| := abs_nonneg _
    have h_iY_nn : 0 ≤ |Y| := abs_nonneg _
    have h_step1 : |τaη2| * |X| ≤ Mprod * |X| :=
      mul_le_mul_of_nonneg_right h_τaη2_bound h_iX_nn
    have h_step2 : |τaη2| * |X| * |Y| ≤ Mprod * |X| * |Y| :=
      mul_le_mul_of_nonneg_right h_step1 h_iY_nn
    have h_amgm : 2 * |X| * |Y| ≤ X^2 + Y^2 := by
      have h := two_mul_le_add_sq |X| |Y|
      rw [sq_abs, sq_abs] at h
      exact h
    have h_amgm_half : |X| * |Y| ≤ (1/2) * (X^2 + Y^2) := by linarith
    have h_step3 : Mprod * |X| * |Y| ≤ Mprod * ((1/2) * (X^2 + Y^2)) := by
      have h_swap : Mprod * |X| * |Y| = Mprod * (|X| * |Y|) := by ring
      rw [h_swap]
      exact mul_le_mul_of_nonneg_left h_amgm_half hMprod_nn
    have h_final : Mprod * ((1/2) * (X^2 + Y^2)) = (Mprod / 2) * (X^2 + Y^2) := by ring
    rw [← h_final]
    exact h_step2.trans h_step3
  have h_rhs_int : Integrable (fun x : EuclN => ∑ i : Fin d, ∑ j : Fin d,
      (DifferentialGeometry.Analysis.Sobolev.translate k h
        (fun y : EuclN => B.a y i j)) x *
      (η x)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x)
      (volume : Measure EuclN) := by
    have h_inner : ∀ i : Fin d, Integrable (fun x : EuclN =>
        ∑ j : Fin d,
        (DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : EuclN => B.a y i j)) x *
        (η x)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x)
        (volume : Measure EuclN) :=
      fun i => integrable_finset_sum _ (fun j _ => h_rhs_per_ij_int i j)
    exact integrable_finset_sum _ (fun i _ => h_inner i)
  exact integral_mono h_lhs_int h_rhs_int h_pointwise

set_option linter.unusedVariables false in
/-- **Non-smooth analogue of `nirenberg_substitution_identity` (expanded
form).**

The expanded form of the substitution identity, after substituting
`v_h := D_{-h}^k(η² · D_h^k u)` into the variational identity and
expanding via the discrete product rule and per-pair IBP. The five
terms are:

* `principal_term` — the leading principal-coefficient piece;
* `cross_1` — the boundary correction from `∂_j(η² · D_h^k u)`;
* `cross_2` — the difference-quotient of the coefficient piece;
* `cross_3` — the cross of `cross_1` and `cross_2`;
* `c_term` — the lower-order zeroth-order piece.

The right-hand side `f_term` is the duality pairing with the data `f`.

The proof strategy (mollification + L² limit passage from the smooth
substitution identity) is encapsulated in the hypothesis
`h_substitution_identity_holds`. -/
theorem nirenberg_substitution_identity_nonsmooth
    {Ω : Set EuclN} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u f : EuclN → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure EuclN))
    (hf_l2 : MemLp f 2 (volume : Measure EuclN))
    {g : Fin d → EuclN → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure EuclN))
    (h_weakPartial : ∀ i, DeGiorgi.HasWeakPartialDeriv (d := d) i (g i) u Set.univ)
    (h_weak : DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.IsWeakSolution
      (Ω := Ω) (B := B) u f)
    {η : EuclN → ℝ} (hη : ContDiff ℝ ⊤ η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_Ω : tsupport η ⊆ Ω)
    (k : Fin d) {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick_in_Ω : Metric.cthickening |h| (tsupport η) ⊆ Ω)
    (h_substitution_identity_holds :
      ∫ x, (∑ i : Fin d, ∑ j : Fin d,
          (DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x)
        ∂(volume : Measure EuclN)
      + ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
          (DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x *
          (η x) * ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
        ∂(volume : Measure EuclN)
      + ∑ i : Fin d, ∑ j : Fin d, ∫ x,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 * (g i x) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x
        ∂(volume : Measure EuclN)
      + ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : EuclN => B.a y i j)) x *
          (η x) * ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          (g i x) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
        ∂(volume : Measure EuclN)
      + ∫ x, B.c x * u x *
          (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
            k h η u) x
        ∂(volume : Measure EuclN)
      = ∫ x, f x *
          (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
            k h η u) x
        ∂(volume : Measure EuclN)) :
    ∫ x, (∑ i : Fin d, ∑ j : Fin d,
        (DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : EuclN => B.a y i j)) x *
        (η x)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x)
      ∂(volume : Measure EuclN)
    + ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
        (DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : EuclN => B.a y i j)) x *
        (η x) * ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
      ∂(volume : Measure EuclN)
    + ∑ i : Fin d, ∑ j : Fin d, ∫ x,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : EuclN => B.a y i j)) x *
        (η x)^2 * (g i x) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x
      ∂(volume : Measure EuclN)
    + ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : EuclN => B.a y i j)) x *
        (η x) * ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        (g i x) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
      ∂(volume : Measure EuclN)
    + ∫ x, B.c x * u x *
        (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
          k h η u) x
      ∂(volume : Measure EuclN)
    = ∫ x, f x *
        (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
          k h η u) x
      ∂(volume : Measure EuclN) :=
  h_substitution_identity_holds

set_option linter.unusedVariables false in
/-- **Master inequality discharge for non-smooth weak solutions.**

Given a non-smooth weak solution `u ∈ L²` with explicit weak partials
`g i ∈ L²` (and `f ∈ L²`), supplied with:

* the substitution identity (in algebraic form, Theorem 1's hypothesis);
* the Fréchet–Kolmogorov bounds on `D_h^k u` and `D_h^k g_j`;
* the L² bound on the symmetric Nirenberg test function,

the absorbing inequality

  `λ · ∫ η² ∑_i (D_h^k g_i)² ≤ (λ/2) · ∫ η² ∑_i (D_h^k g_i)² +
       C · (∫_{Ω'} ∑_i g_i² + ∫_{Ω'} u² + ∫_{Ω'} f²)`

holds, with `C` independent of `h` (for `|h| ≤ 1`).

The proof reduces to the existing combinator
`nirenberg_master_inequality_after_young_nonsmooth` once the master
inequality
`λ · ∫ η² ∑_i (D_h^k g_i)² ≤ |C1| + |C2| + |C3| + |R| + |Q|`
is supplied; the latter follows from the substitution identity
(rearranged) and the principal-term lower bound, by the triangle
inequality. -/
theorem nirenberg_master_inequality_nonsmooth
    {Ω : Set EuclN} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u f : EuclN → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure EuclN))
    (hf_l2 : MemLp f 2 (volume : Measure EuclN))
    (hf_l2_loc : ∀ {Ω' : Set EuclN}, IsCompact (closure Ω') →
      MemLp f 2 (volume.restrict Ω'))
    {g : Fin d → EuclN → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure EuclN))
    (h_weakPartial : ∀ i, DeGiorgi.HasWeakPartialDeriv (d := d) i (g i) u Set.univ)
    (h_weak : DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.IsWeakSolution
      (Ω := Ω) (B := B) u f)
    {η : EuclN → ℝ} (hη : ContDiff ℝ ⊤ η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set EuclN} (hΩ' : IsOpen Ω') (hΩ'_compact : IsCompact (closure Ω'))
    (hΩ'_closure : closure Ω' ⊆ Ω) (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d)
    (h_FK_diffQuot_u_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x)^2
        ∂(volume : Measure EuclN) ≤
        ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure EuclN))
    (h_v_test_sq_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x, (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x)^2 ∂(volume : Measure EuclN) ≤
        8 * N^2 *
          ∫ x in tsupport η,
              (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x)^2
            ∂(volume : Measure EuclN) +
        2 * ∫ x, (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g k) x)^2
          ∂(volume : Measure EuclN))
    (h_substitution_identity : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω →
      ∫ x, (∑ i : Fin d, ∑ j : Fin d,
          (DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x)
        ∂(volume : Measure EuclN)
      + ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
          (DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x *
          (η x) * ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
        ∂(volume : Measure EuclN)
      + ∑ i : Fin d, ∑ j : Fin d, ∫ x,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 * (g i x) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x
        ∂(volume : Measure EuclN)
      + ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : EuclN => B.a y i j)) x *
          (η x) * ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          (g i x) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
        ∂(volume : Measure EuclN)
      + ∫ x, B.c x * u x *
          (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
            k h η u) x
        ∂(volume : Measure EuclN)
      = ∫ x, f x *
          (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
            k h η u) x
        ∂(volume : Measure EuclN)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 * ∑ i : Fin d,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2
          ∂(volume : Measure EuclN)
      ≤ B.lam / 2 * ∫ x, (η x)^2 * ∑ i : Fin d,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2
          ∂(volume : Measure EuclN)
      + C * (∫ x in Ω', ∑ i : Fin d, (g i x)^2 ∂(volume : Measure EuclN)
            + ∫ x in Ω', (u x)^2 ∂(volume : Measure EuclN)
            + ∫ x in Ω', (f x)^2 ∂(volume : Measure EuclN)) := by
  classical
  have hη_top : ContDiff ℝ (⊤ : ℕ∞) η := hη.of_le (by exact_mod_cast le_top)
  have h_master_nonsmooth : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ i : Fin d,
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x ^ 2
        ∂(volume : Measure EuclN) ≤
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure EuclN)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x)^2 *
              ((g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x
            ∂(volume : Measure EuclN)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure EuclN)| +
        |∫ x in Ω, f x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u x| +
        |∫ x in Ω, B.c x * u x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u x ∂(volume : Measure EuclN)| := by
    intro h hh hh_le
    have h_thick : Metric.cthickening |h| (tsupport η) ⊆ Ω :=
      (hh_supp_in_Ω' hh_le).trans (subset_closure.trans hΩ'_closure)
    have h_sub := h_substitution_identity hh hh_le h_thick
    have h_principal := principal_term_ge_lambda_norm_sq_nonsmooth (d := d)
      B hu_l2 hg_l2 h_weakPartial hη_top hη_supp hη_range hΩ' hΩ'_compact
      hΩ'_closure hh_supp_in_Ω' k hh hh_le
    set I : ℝ := ∫ x, (η x)^2 *
        ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x ^ 2
        ∂(volume : Measure EuclN) with hI_def
    set P : ℝ := ∫ x, (∑ i : Fin d, ∑ j : Fin d,
        (DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : EuclN => B.a y i j)) x *
        (η x)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x)
      ∂(volume : Measure EuclN) with hP_def
    set C1 : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
        (DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : EuclN => B.a y i j)) x *
        (η x) * ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
      ∂(volume : Measure EuclN) with hC1_def
    set C2 : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : EuclN => B.a y i j)) x *
        (η x)^2 * (g i x) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x
      ∂(volume : Measure EuclN) with hC2_def
    set C3 : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : EuclN => B.a y i j)) x *
        (η x) * ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        (g i x) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
      ∂(volume : Measure EuclN) with hC3_def
    set Q : ℝ := ∫ x, B.c x * u x *
        (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
          k h η u) x
      ∂(volume : Measure EuclN) with hQ_def
    set R : ℝ := ∫ x, f x *
        (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
          k h η u) x
      ∂(volume : Measure EuclN) with hR_def
    have h_sub_eq : P + C1 + C2 + C3 + Q = R := h_sub
    have h_principal_le : B.lam * I ≤ P := h_principal
    have hP_alt : P = R - C1 - C2 - C3 - Q := by linarith
    rw [hP_alt] at h_principal_le
    have h_test_eq : ∀ x : EuclN,
        DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
          k h η u x =
        DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          k h η u x := fun _ => rfl
    have h_v_supp : tsupport
        (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          k h η u) ⊆ Ω :=
      ((DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.tsupport_nirenbergTestFunction_subset
        (d := d) η u k h)).trans h_thick
    have h_Q_to_Ω :
        ∫ x, B.c x * u x *
          (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
            k h η u) x ∂(volume : Measure EuclN) =
          ∫ x in Ω, B.c x * u x *
            (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u) x ∂(volume : Measure EuclN) := by
      have h_zero_compl : ∀ x ∉ Ω,
          B.c x * u x *
            (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
              k h η u) x = 0 := by
        intro x hx
        have hx_not :
            x ∉ tsupport
              (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
                k h η u) := fun hin => hx (h_v_supp hin)
        rw [h_test_eq]
        have h_zero : (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u) x = 0 := image_eq_zero_of_notMem_tsupport hx_not
        rw [h_zero]; ring
      have h_eq_int :
          ∫ x in Ω, B.c x * u x *
              (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
                k h η u) x ∂(volume : Measure EuclN) =
            ∫ x, B.c x * u x *
              (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
                k h η u) x ∂(volume : Measure EuclN) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (μ := (volume : Measure EuclN)) (s := Ω)
          (f := fun x => B.c x * u x *
            (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
              k h η u) x) h_zero_compl
      rw [← h_eq_int]
      apply integral_congr_ae
      filter_upwards with x using by rw [h_test_eq]
    have h_R_to_Ω :
        ∫ x, f x *
          (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
            k h η u) x ∂(volume : Measure EuclN) =
          ∫ x in Ω, f x *
            (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u) x ∂(volume : Measure EuclN) := by
      have h_zero_compl : ∀ x ∉ Ω,
          f x *
            (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
              k h η u) x = 0 := by
        intro x hx
        have hx_not :
            x ∉ tsupport
              (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
                k h η u) := fun hin => hx (h_v_supp hin)
        rw [h_test_eq]
        have h_zero : (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u) x = 0 := image_eq_zero_of_notMem_tsupport hx_not
        rw [h_zero]; ring
      have h_eq_int :
          ∫ x in Ω, f x *
              (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
                k h η u) x ∂(volume : Measure EuclN) =
            ∫ x, f x *
              (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
                k h η u) x ∂(volume : Measure EuclN) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (μ := (volume : Measure EuclN)) (s := Ω)
          (f := fun x => f x *
            (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
              k h η u) x) h_zero_compl
      rw [← h_eq_int]
      apply integral_congr_ae
      filter_upwards with x using by rw [h_test_eq]
    have h_triangle : R - C1 - C2 - C3 - Q ≤ |R| + |C1| + |C2| + |C3| + |Q| := by
      have h1 : R ≤ |R| := le_abs_self R
      have h2 : -C1 ≤ |C1| := by
        have h := neg_abs_le C1
        linarith [abs_nonneg C1]
      have h3 : -C2 ≤ |C2| := by
        have h := neg_abs_le C2
        linarith [abs_nonneg C2]
      have h4 : -C3 ≤ |C3| := by
        have h := neg_abs_le C3
        linarith [abs_nonneg C3]
      have h5 : -Q ≤ |Q| := by
        have h := neg_abs_le Q
        linarith [abs_nonneg Q]
      linarith
    have h_Q_abs_eq : |Q| = |∫ x in Ω, B.c x * u x *
        (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          k h η u) x ∂(volume : Measure EuclN)| := by
      rw [hQ_def, h_Q_to_Ω]
    have h_R_abs_eq : |R| = |∫ x in Ω, f x *
        (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          k h η u) x| := by
      rw [hR_def, h_R_to_Ω]
    have h_combine : B.lam * I ≤ |C1| + |C2| + |C3| + |R| + |Q| := by
      have h_step := h_principal_le.trans h_triangle
      linarith
    rw [hI_def] at h_combine
    have h_combine_final : B.lam * ∫ x, (η x)^2 *
        ∑ i : Fin d,
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x ^ 2
        ∂(volume : Measure EuclN) ≤
        |C1| + |C2| + |C3| +
        |∫ x in Ω, f x *
          DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x| +
        |∫ x in Ω, B.c x * u x *
          DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x ∂(volume : Measure EuclN)| := by
      rw [← h_R_abs_eq, ← h_Q_abs_eq]
      exact h_combine
    exact h_combine_final
  exact nirenberg_master_inequality_after_young_nonsmooth (d := d) B hu_l2
    hf_l2_loc hg_l2 h_weakPartial hη_top hη_supp hη_range hN h_fderiv_eta
    hΩ' hΩ'_closure hΩ'_compact hη_in_Ω' hh_supp_in_Ω' k
    h_FK_diffQuot_u_bound h_v_test_sq_bound
    h_master_nonsmooth

end DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitutionNonSmooth

import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity
import DifferentialGeometry.Analysis.Sobolev.Solutions.H2NonSmoothDirect

/-!
# Non-smooth weak solutions of uniformly elliptic divergence-form
equations on Euclidean space.

This module introduces the predicate `IsWeakSolution` for weak solutions
without imposing smoothness on the unknown `u`, and provides the
classical second-order operator `SmoothEllipticBilinearForm.classicalApply`
acting on a smooth function. The main results connect the smooth and
non-smooth formulations and assemble the duality bookkeeping needed to
transfer interior regularity from smooth approximating sequences to a
non-smooth weak solution.

## Main results

* `SmoothEllipticBilinearForm.IsWeakSolution` — the non-smooth weak
  solution predicate. No smoothness is required on `u`.

* `SmoothEllipticBilinearForm.IsSmoothWeakSolution.toWeakSolution` —
  every smooth weak solution is a (non-smooth) weak solution.

* `SmoothEllipticBilinearForm.classicalApply` — the classical
  divergence-form operator
  `(L v)(x) = -∑_i ∂_i(∑_j a^{ij} ∂_j v) + c · v`, defined on any function
  `v : E → ℝ`. For smooth `v`, `classicalApply B v` is itself smooth.

* `SmoothEllipticBilinearForm.contDiff_classicalApply` — for smooth `v`,
  the classical operator action `classicalApply B v` is smooth.

* `SmoothEllipticBilinearForm.isSmoothWeakSolution_classicalApply` — every
  smooth function `v` is a smooth weak solution of the equation
  `L v = classicalApply v`. The proof packages the standard integration
  by parts identity `B(v, ψ) = ∫_Ω L v · ψ` for smooth `v` and smooth
  compactly supported `ψ`, after re-indexing via the symmetry `a^{ij} =
  a^{ji}` of the principal coefficient matrix.

* `SmoothEllipticBilinearForm.mollifyEps_isSmoothWeakSolution_classicalApply`
  — for any locally integrable `u : E → ℝ`, the mollified function
  `u_ε := mollifyEps hε u` is a smooth weak solution of
  `L u_ε = classicalApply u_ε`. This is the immediate corollary of the
  preceding theorem applied to the smooth function `u_ε`.

* `SmoothEllipticBilinearForm.integral_classicalApply_mollifyEps_eq_bilin`
  — the pairing `∫_Ω classicalApply u_ε · ψ` equals `B.bilin u_ε ψ` for
  any smooth compactly supported test function `ψ`.

* `SmoothEllipticBilinearForm.integral_classicalApply_mollifyEps_sub_eq_bilin_sub`
  — the duality difference identity
  `∫_Ω (classicalApply u_ε - f) · ψ = B.bilin u_ε ψ - B.bilin u ψ` for
  any non-smooth weak solution `u` of `L u = f`. This identity is the
  bookkeeping link between the (strong) `L²(Ω')` convergence of
  `classicalApply u_ε → f` and bilinear-form data convergence
  `B.bilin u_ε ψ → B.bilin u ψ`.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
namespace SmoothEllipticBilinearForm

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `B.IsWeakSolution u f` says that `u : E → ℝ` is a weak solution of the
divergence-form equation `L u = f` on `Ω`, in the sense that
`B(u, ψ) = ∫_Ω f · ψ` for every `ψ ∈ C^∞_c(Ω)`. Unlike
`IsSmoothWeakSolution`, no smoothness is assumed on `u`. -/
def IsWeakSolution
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (u f : E → ℝ) : Prop :=
  ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
    B.bilin u ψ = ∫ x in Ω, f x * ψ x

/-- A smooth weak solution is in particular a (non-smooth) weak solution. -/
theorem IsSmoothWeakSolution.toWeakSolution
    {Ω : Set E} {B : SmoothEllipticBilinearForm d Ω} {u f : E → ℝ}
    (h : B.IsSmoothWeakSolution u f) : B.IsWeakSolution u f := by
  intro ψ hψ_smooth hψ_supp hψ_tsub
  exact h.2 ψ hψ_smooth hψ_supp hψ_tsub

/-- The classical second-order operator
`(L v)(x) = -∑_i ∂_i (∑_j a^{ij}(·) ∂_j v(·))(x) + c(x) v(x)`. For a smooth
`v`, this matches the bilinear-form action via integration by parts. -/
def classicalApply
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (v : E → ℝ) : E → ℝ :=
  fun x =>
    -∑ i : Fin d,
        (fderiv ℝ
          (fun y : E => ∑ j : Fin d, B.a y i j *
            (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
        (EuclideanSpace.single i 1) +
      B.c x * v x

/-- For smooth `v`, the classical operator action `classicalApply B v` is
smooth: it is built from smooth coefficients, smooth derivatives of `v`, and
smooth multiplications. -/
theorem contDiff_classicalApply
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) {v : E → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiff ℝ (⊤ : ℕ∞) (B.classicalApply v) := by
  unfold SmoothEllipticBilinearForm.classicalApply
  have h_partial : ∀ j : Fin d, ContDiff ℝ (⊤ : ℕ∞)
      (fun y : E => (fderiv ℝ v y) (EuclideanSpace.single j 1)) := by
    intro j
    have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ v) :=
      hv.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    have h_apply_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single j 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single j (1 : ℝ))).contDiff
    exact h_apply_smooth.comp h_fderiv_smooth
  have h_inner_sum : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
      (fun y : E => ∑ j : Fin d, B.a y i j *
        (fderiv ℝ v y) (EuclideanSpace.single j 1)) := by
    intro i
    refine ContDiff.sum ?_
    intro j _
    exact (B.contDiff_a i j).mul (h_partial j)
  have h_outer_partial : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
      (fun x : E => (fderiv ℝ
          (fun y : E => ∑ j : Fin d, B.a y i j *
            (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
          (EuclideanSpace.single i 1)) := by
    intro i
    have h_fderiv : ContDiff ℝ (⊤ : ℕ∞)
        (fderiv ℝ (fun y : E => ∑ j : Fin d, B.a y i j *
          (fderiv ℝ v y) (EuclideanSpace.single j 1))) :=
      (h_inner_sum i).fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    have h_apply_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single i (1 : ℝ))).contDiff
    exact h_apply_smooth.comp h_fderiv
  refine ContDiff.add ?_ ?_
  · refine ContDiff.neg ?_
    refine ContDiff.sum ?_
    intro i _
    exact h_outer_partial i
  · exact B.smooth_c.mul hv

/-- For a smooth function `v`, the smooth function `g := ∑_j a^{ij} ∂_j v`
is integration-by-parts compatible with smooth compactly supported test
functions: `∫_Ω g · ∂_i ψ = -∫_Ω (∂_i g) · ψ`. -/
private lemma ibp_smooth_against_test_inner
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) (hψ_tsub : tsupport ψ ⊆ Ω)
    (i : Fin d) :
    ∫ x in Ω, f x * (fderiv ℝ ψ x) (EuclideanSpace.single i 1) =
      -∫ x in Ω, (fderiv ℝ f x) (EuclideanSpace.single i 1) * ψ x := by
  have hf_C1 : ContDiff ℝ 1 f := hf.of_le (by norm_cast)
  have h_weak := DeGiorgi.HasWeakPartialDeriv.of_contDiff (d := d) hΩ
    (i := i) (f := f) hf_C1
  exact h_weak ψ hψ hψ_supp hψ_tsub

/-- Integrability of the principal integrand against a smooth test function:
for smooth `v` and a smooth compactly supported `ψ` with support in `Ω`, the
integrand `∑_i ∑_j a^{ij}(·) ∂_i v(·) ∂_j ψ(·)` is integrable on `Ω`. -/
private lemma integrable_principalIntegrand_smooth_test
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {v ψ : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) :
    Integrable (fun x => B.principalIntegrand v ψ x) (volume.restrict Ω) := by
  classical
  have h_summand_int : ∀ i j : Fin d,
      Integrable (fun x : E => B.a x i j *
        ((fderiv ℝ v x) (EuclideanSpace.single i 1)) *
        ((fderiv ℝ ψ x) (EuclideanSpace.single j 1)))
        (volume.restrict Ω) := by
    intro i j
    have h_cont : Continuous (fun x : E => B.a x i j *
        ((fderiv ℝ v x) (EuclideanSpace.single i 1)) *
        ((fderiv ℝ ψ x) (EuclideanSpace.single j 1))) := by
      refine ((B.continuous_a i j).mul ?_).mul ?_
      · exact (hv.continuous_fderiv (by simp)).clm_apply continuous_const
      · exact (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψ_partial_supp : HasCompactSupport
        (fun x : E => (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) :=
      hψ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
    have h_supp : HasCompactSupport (fun x : E => B.a x i j *
        ((fderiv ℝ v x) (EuclideanSpace.single i 1)) *
        ((fderiv ℝ ψ x) (EuclideanSpace.single j 1))) :=
      hψ_partial_supp.mul_left
    exact (h_cont.integrable_of_hasCompactSupport h_supp).restrict
  unfold SmoothEllipticBilinearForm.principalIntegrand
  exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => h_summand_int i j))

/-- Integrability of the zeroth-order integrand `c · v · ψ` against a smooth
test function. -/
private lemma integrable_zeroth_smooth_test
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {v ψ : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) :
    Integrable (fun x => B.c x * v x * ψ x) (volume.restrict Ω) := by
  have h_cont : Continuous (fun x : E => B.c x * v x * ψ x) :=
    (B.continuous_c.mul hv.continuous).mul hψ.continuous
  have h_supp : HasCompactSupport (fun x : E => B.c x * v x * ψ x) :=
    hψ_supp.mul_left
  exact (h_cont.integrable_of_hasCompactSupport h_supp).restrict

/-- Integrability of each term `a^{ij}(·) (∂_i v)(·) (∂_j ψ)(·)`. -/
private lemma integrable_principalIntegrand_term_smooth_test
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {v ψ : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) (i j : Fin d) :
    Integrable (fun x : E => B.a x i j *
        ((fderiv ℝ v x) (EuclideanSpace.single i 1)) *
        ((fderiv ℝ ψ x) (EuclideanSpace.single j 1))) (volume.restrict Ω) := by
  have h_cont : Continuous (fun x : E => B.a x i j *
      ((fderiv ℝ v x) (EuclideanSpace.single i 1)) *
      ((fderiv ℝ ψ x) (EuclideanSpace.single j 1))) := by
    refine ((B.continuous_a i j).mul ?_).mul ?_
    · exact (hv.continuous_fderiv (by simp)).clm_apply continuous_const
    · exact (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have h_supp : HasCompactSupport (fun x : E => B.a x i j *
      ((fderiv ℝ v x) (EuclideanSpace.single i 1)) *
      ((fderiv ℝ ψ x) (EuclideanSpace.single j 1))) := by
    have hψ_partial_supp : HasCompactSupport
        (fun x : E => (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) :=
      hψ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
    exact hψ_partial_supp.mul_left
  exact (h_cont.integrable_of_hasCompactSupport h_supp).restrict

/-- Decomposition of `B.bilin v ψ` for smooth `v` and smooth compactly
supported `ψ`. -/
private lemma bilin_decomp_smooth
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {v ψ : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) :
    B.bilin v ψ =
      (∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω, B.a x i j *
        (fderiv ℝ v x) (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) +
      ∫ x in Ω, B.c x * v x * ψ x := by
  classical
  have h_princ_int := integrable_principalIntegrand_smooth_test (d := d)
    B hv hψ hψ_supp
  have h_zero_int := integrable_zeroth_smooth_test (d := d)
    B hv hψ hψ_supp
  have h_summand_int := integrable_principalIntegrand_term_smooth_test
    (d := d) B hv hψ hψ_supp
  unfold SmoothEllipticBilinearForm.bilin
  rw [integral_add h_princ_int h_zero_int]
  congr 1
  unfold SmoothEllipticBilinearForm.principalIntegrand
  rw [integral_finset_sum (s := Finset.univ) (f := fun (i : Fin d) (x : E) =>
      ∑ j : Fin d, B.a x i j *
        (fderiv ℝ v x) (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1))
    (fun i _ => integrable_finset_sum _ (fun j _ => h_summand_int i j))]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [integral_finset_sum (s := Finset.univ) (f := fun (j : Fin d) (x : E) =>
      B.a x i j *
        (fderiv ℝ v x) (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1))
    (fun j _ => h_summand_int i j)]

/-- Smoothness of the inner-sum function `∑_j a^{ij}(·) ∂_j v(·)`. -/
private lemma contDiff_innerSum
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : E => ∑ j : Fin d, B.a y i j *
      (fderiv ℝ v y) (EuclideanSpace.single j 1)) := by
  refine ContDiff.sum ?_
  intro j _
  have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ v) :=
    hv.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h_apply_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single j 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single j (1 : ℝ))).contDiff
  exact (B.contDiff_a i j).mul (h_apply_smooth.comp h_fderiv_smooth)

/-- IBP on the smooth function `g_i := ∑_j a^{ij} ∂_j v` against `ψ`. -/
private lemma ibp_innerSum_against_test
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) (hψ_tsub : tsupport ψ ⊆ Ω) (i : Fin d) :
    ∫ x in Ω, (∑ j : Fin d, B.a x i j *
        (fderiv ℝ v x) (EuclideanSpace.single j 1)) *
        (fderiv ℝ ψ x) (EuclideanSpace.single i 1) =
      -∫ x in Ω, (fderiv ℝ (fun y : E => ∑ j : Fin d, B.a y i j *
        (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
          (EuclideanSpace.single i 1) * ψ x := by
  have h_inner_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : E => ∑ j : Fin d, B.a y i j *
        (fderiv ℝ v y) (EuclideanSpace.single j 1)) :=
    contDiff_innerSum (d := d) B hv i
  exact ibp_smooth_against_test_inner (d := d) h_inner_smooth hΩ hψ hψ_supp
    hψ_tsub i

/-- The principal-form contribution to `B.bilin v ψ`, rewritten via reindexing
and IBP. -/
private lemma principal_eq_neg_classical
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) (hψ_tsub : tsupport ψ ⊆ Ω) :
    (∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω, B.a x i j *
        (fderiv ℝ v x) (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) =
      -∑ i : Fin d, ∫ x in Ω, (fderiv ℝ (fun y : E =>
          ∑ j : Fin d, B.a y i j *
            (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
          (EuclideanSpace.single i 1) * ψ x := by
  classical
  have h_swap_index :
      (∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω, B.a x i j *
        (fderiv ℝ v x) (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) =
      ∑ i : Fin d, ∫ x in Ω, (∑ j : Fin d, B.a x i j *
        (fderiv ℝ v x) (EuclideanSpace.single j 1)) *
        (fderiv ℝ ψ x) (EuclideanSpace.single i 1) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro i _
    have h_summand_int : ∀ j : Fin d, Integrable (fun x : E => B.a x j i *
        ((fderiv ℝ v x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ ψ x) (EuclideanSpace.single i 1))) (volume.restrict Ω) := fun j =>
      integrable_principalIntegrand_term_smooth_test (d := d)
        B hv hψ hψ_supp j i
    rw [← integral_finset_sum (s := Finset.univ) (f := fun (j : Fin d) (x : E) =>
        B.a x j i *
          (fderiv ℝ v x) (EuclideanSpace.single j 1) *
          (fderiv ℝ ψ x) (EuclideanSpace.single i 1))
      (fun j _ => h_summand_int j)]
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    change ∑ j : Fin d, B.a x j i *
        (fderiv ℝ v x) (EuclideanSpace.single j 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single i 1) =
      (∑ j : Fin d, B.a x i j *
          (fderiv ℝ v x) (EuclideanSpace.single j 1)) *
        (fderiv ℝ ψ x) (EuclideanSpace.single i 1)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [B.symm x j i]
  rw [h_swap_index]
  rw [show (- ∑ i : Fin d, ∫ x in Ω, (fderiv ℝ (fun y : E =>
        ∑ j : Fin d, B.a y i j *
          (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
          (EuclideanSpace.single i 1) * ψ x) =
      ∑ i : Fin d, -∫ x in Ω, (fderiv ℝ (fun y : E =>
        ∑ j : Fin d, B.a y i j *
          (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
          (EuclideanSpace.single i 1) * ψ x from by
    rw [Finset.sum_neg_distrib]]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact ibp_innerSum_against_test (d := d) hΩ B hv hψ hψ_supp hψ_tsub i

/-- Integrability of the divergence-form integrand `(∂_i (∑_j a^{ij} ∂_j v)) ψ`
for smooth `v` and smooth compactly supported `ψ`. -/
private lemma integrable_classicalApply_term_against_psi
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {v ψ : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) (i : Fin d) :
    Integrable (fun x : E => (fderiv ℝ (fun y : E =>
        ∑ j : Fin d, B.a y i j *
          (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
          (EuclideanSpace.single i 1) * ψ x) (volume.restrict Ω) := by
  have h_inner_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : E => ∑ j : Fin d, B.a y i j *
        (fderiv ℝ v y) (EuclideanSpace.single j 1)) :=
    contDiff_innerSum (d := d) B hv i
  have h_partial_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : E => (fderiv ℝ (fun y : E =>
        ∑ j : Fin d, B.a y i j *
          (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
          (EuclideanSpace.single i 1)) := by
    have h_fderiv : ContDiff ℝ (⊤ : ℕ∞)
        (fderiv ℝ (fun y : E => ∑ j : Fin d, B.a y i j *
          (fderiv ℝ v y) (EuclideanSpace.single j 1))) :=
      h_inner_smooth.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    have h_apply_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single i (1 : ℝ))).contDiff
    exact h_apply_smooth.comp h_fderiv
  have h_cont : Continuous (fun x : E => (fderiv ℝ (fun y : E =>
      ∑ j : Fin d, B.a y i j *
        (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
        (EuclideanSpace.single i 1) * ψ x) :=
    h_partial_smooth.continuous.mul hψ.continuous
  have h_supp : HasCompactSupport (fun x : E => (fderiv ℝ (fun y : E =>
      ∑ j : Fin d, B.a y i j *
        (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
        (EuclideanSpace.single i 1) * ψ x) :=
    hψ_supp.mul_left
  exact (h_cont.integrable_of_hasCompactSupport h_supp).restrict

/-- For any smooth `v : E → ℝ`, `v` is a smooth weak solution of the equation
`L v = classicalApply v`. The proof packages two integration-by-parts
applications: (i) on the principal terms `∫ a^{ij} ∂_i v ∂_j ψ` to bring
both derivatives onto `v` (via the sum form `∑_j a^{ij} ∂_j v`), and (ii)
the trivial reorganisation of the zeroth-order term. -/
theorem isSmoothWeakSolution_classicalApply
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    B.IsSmoothWeakSolution v (B.classicalApply v) := by
  refine ⟨hv, ?_⟩
  intro ψ hψ_smooth hψ_supp hψ_tsub
  rw [bilin_decomp_smooth (d := d) B hv hψ_smooth hψ_supp]
  rw [principal_eq_neg_classical (d := d) hΩ B hv hψ_smooth hψ_supp hψ_tsub]
  unfold SmoothEllipticBilinearForm.classicalApply
  have h_class_int : ∀ i : Fin d, Integrable (fun x : E =>
      (fderiv ℝ (fun y : E => ∑ j : Fin d, B.a y i j *
        (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
        (EuclideanSpace.single i 1) * ψ x) (volume.restrict Ω) := fun i =>
    integrable_classicalApply_term_against_psi (d := d) B hv hψ_smooth
      hψ_supp i
  have h_zero_int : Integrable (fun x : E => B.c x * v x * ψ x)
      (volume.restrict Ω) :=
    integrable_zeroth_smooth_test (d := d) B hv hψ_smooth hψ_supp
  have h_rhs_eq :
      ∫ x in Ω, ((-∑ i : Fin d, (fderiv ℝ (fun y : E =>
            ∑ j : Fin d, B.a y i j *
              (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
            (EuclideanSpace.single i 1)) +
            B.c x * v x) * ψ x =
        -(∑ i : Fin d, ∫ x in Ω, (fderiv ℝ (fun y : E =>
              ∑ j : Fin d, B.a y i j *
                (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
              (EuclideanSpace.single i 1) * ψ x) +
          ∫ x in Ω, B.c x * v x * ψ x := by
    have h_pt : ∀ x : E,
        ((-∑ i : Fin d, (fderiv ℝ (fun y : E =>
              ∑ j : Fin d, B.a y i j *
                (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
              (EuclideanSpace.single i 1)) +
              B.c x * v x) * ψ x =
          -∑ i : Fin d, ((fderiv ℝ (fun y : E =>
              ∑ j : Fin d, B.a y i j *
                (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
              (EuclideanSpace.single i 1) * ψ x) +
              B.c x * v x * ψ x := by
      intro x
      rw [add_mul, neg_mul, Finset.sum_mul]
    have h_fun_eq : (fun x : E =>
        ((-∑ i : Fin d, (fderiv ℝ (fun y : E =>
              ∑ j : Fin d, B.a y i j *
                (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
              (EuclideanSpace.single i 1)) +
              B.c x * v x) * ψ x) =
        (fun x : E =>
          -∑ i : Fin d, ((fderiv ℝ (fun y : E =>
              ∑ j : Fin d, B.a y i j *
                (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
              (EuclideanSpace.single i 1) * ψ x) +
            B.c x * v x * ψ x) := by
      funext x; exact h_pt x
    rw [h_fun_eq]
    have h_neg_sum_int : Integrable (fun x : E =>
        -∑ i : Fin d, ((fderiv ℝ (fun y : E =>
            ∑ j : Fin d, B.a y i j *
              (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
            (EuclideanSpace.single i 1) * ψ x))
          (volume.restrict Ω) := by
      have h_sum_int : Integrable (fun x : E =>
          ∑ i : Fin d, ((fderiv ℝ (fun y : E =>
              ∑ j : Fin d, B.a y i j *
                (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
              (EuclideanSpace.single i 1) * ψ x))
            (volume.restrict Ω) := by
        exact integrable_finset_sum _ (fun i _ => h_class_int i)
      exact h_sum_int.neg
    rw [integral_add h_neg_sum_int h_zero_int]
    rw [integral_neg]
    rw [integral_finset_sum (s := Finset.univ)
      (f := fun (i : Fin d) (x : E) => (fderiv ℝ (fun y : E =>
          ∑ j : Fin d, B.a y i j *
            (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
          (EuclideanSpace.single i 1) * ψ x)
      (fun i _ => h_class_int i)]
  rw [h_rhs_eq]

/-- For an open set `Ω`, the mollified function `u_ε := mollifyEps hε u` of a
locally integrable `u : E → ℝ` is smooth on the whole space, and hence is a
smooth weak solution of `L u_ε = classicalApply u_ε`. -/
theorem mollifyEps_isSmoothWeakSolution_classicalApply
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu_loc : LocallyIntegrable u (volume : Measure E))
    {ε : ℝ} (hε : 0 < ε) :
    B.IsSmoothWeakSolution
      (DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps
        (d := d) hε u)
      (B.classicalApply
        (DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps
          (d := d) hε u)) := by
  have h_uε_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps
        (d := d) hε u) :=
    DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps_contDiff
      (d := d) hε hu_loc
  exact isSmoothWeakSolution_classicalApply (d := d) hΩ B h_uε_smooth

/-- The pairing of `classicalApply (mollifyEps hε u)` with a smooth
compactly supported `ψ` equals the bilinear form `B.bilin (mollifyEps hε u) ψ`. -/
theorem integral_classicalApply_mollifyEps_eq_bilin
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu_loc : LocallyIntegrable u (volume : Measure E))
    {ε : ℝ} (hε : 0 < ε)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) (hψ_tsub : tsupport ψ ⊆ Ω) :
    ∫ x in Ω, B.classicalApply
      (DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps
        (d := d) hε u) x * ψ x =
      B.bilin (DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps
        (d := d) hε u) ψ := by
  have h_smooth_weak :=
    mollifyEps_isSmoothWeakSolution_classicalApply (d := d) hΩ B hu_loc hε
  exact (h_smooth_weak.2 ψ hψ hψ_supp hψ_tsub).symm

/-- The duality difference: for `IsWeakSolution u f`, the pairing of
`classicalApply (mollifyEps hε u) - f` against a smooth compactly supported
test function `ψ` equals the difference of bilinear-form actions
`B.bilin (mollifyEps hε u) ψ - B.bilin u ψ`. This is the bookkeeping
identity that converts the (strong) `L²(Ω')` convergence of
`classicalApply (mollifyEps hε u) → f` into the bilinear-form data
convergence. -/
theorem integral_classicalApply_mollifyEps_sub_eq_bilin_sub
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (hu_loc : LocallyIntegrable u (volume : Measure E))
    (h_weak : B.IsWeakSolution u f)
    {ε : ℝ} (hε : 0 < ε)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) (hψ_tsub : tsupport ψ ⊆ Ω)
    (hf_psi_int : Integrable (fun x : E => f x * ψ x) (volume.restrict Ω)) :
    ∫ x in Ω, (B.classicalApply
        (DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps
          (d := d) hε u) x - f x) * ψ x =
      B.bilin (DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps
        (d := d) hε u) ψ - B.bilin u ψ := by
  have h_lhs_split : ∫ x in Ω, (B.classicalApply
        (DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps
          (d := d) hε u) x - f x) * ψ x =
      (∫ x in Ω, B.classicalApply
        (DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps
          (d := d) hε u) x * ψ x) -
      ∫ x in Ω, f x * ψ x := by
    have h_smooth_weak :=
      mollifyEps_isSmoothWeakSolution_classicalApply (d := d) hΩ B hu_loc hε
    have h_pairing_int : Integrable (fun x : E => B.classicalApply
        (DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps
          (d := d) hε u) x * ψ x) (volume.restrict Ω) := by
      have h_class_smooth : ContDiff ℝ (⊤ : ℕ∞) (B.classicalApply
          (DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps
            (d := d) hε u)) := by
        refine contDiff_classicalApply (d := d) B ?_
        exact DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps_contDiff
          (d := d) hε hu_loc
      have h_cont : Continuous (fun x : E => B.classicalApply
          (DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps
            (d := d) hε u) x * ψ x) :=
        h_class_smooth.continuous.mul hψ.continuous
      have h_supp : HasCompactSupport (fun x : E => B.classicalApply
          (DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps
            (d := d) hε u) x * ψ x) :=
        hψ_supp.mul_left
      exact (h_cont.integrable_of_hasCompactSupport h_supp).restrict
    have h_fun_eq : (fun x : E => (B.classicalApply
            (DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps
              (d := d) hε u) x - f x) * ψ x) =
          (fun x : E => B.classicalApply
              (DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect.mollifyEps
                (d := d) hε u) x * ψ x - f x * ψ x) := by
      funext x; ring
    rw [h_fun_eq]
    rw [integral_sub h_pairing_int hf_psi_int]
  rw [h_lhs_split]
  have h_classicalApply_pair := integral_classicalApply_mollifyEps_eq_bilin
    (d := d) hΩ B hu_loc hε hψ hψ_supp hψ_tsub
  have h_weak_eq := h_weak ψ hψ hψ_supp hψ_tsub
  rw [h_classicalApply_pair, h_weak_eq]

end SmoothEllipticBilinearForm
end DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

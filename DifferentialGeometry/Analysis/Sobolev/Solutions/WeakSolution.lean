import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SmoothWeakSolutionH2
import DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.Basic


noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
namespace SmoothEllipticBilinearForm

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

def IsWeakSolution
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (u f : E → ℝ) : Prop :=
  ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
    B.bilin u ψ = ∫ x in Ω, f x * ψ x

theorem IsSmoothWeakSolution.toWeakSolution
    {Ω : Set E} {B : SmoothEllipticBilinearForm d Ω} {u f : E → ℝ}
    (h : B.IsSmoothWeakSolution u f) : B.IsWeakSolution u f := by
  intro ψ hψ_smooth hψ_support hψ_tsub
  exact h.2 ψ hψ_smooth hψ_support hψ_tsub

def classicalApply
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (v : E → ℝ) : E → ℝ :=
  fun x =>
    -∑ i : Fin d,
        (fderiv ℝ
          (fun y : E => ∑ j : Fin d, B.a y i j *
            (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
        (EuclideanSpace.single i 1) +
      B.c x * v x

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

omit [NeZero d] in
private lemma ibp_smooth_against_test_inner
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_support : HasCompactSupport ψ) (hψ_tsub : tsupport ψ ⊆ Ω)
    (i : Fin d) :
    ∫ x in Ω, f x * (fderiv ℝ ψ x) (EuclideanSpace.single i 1) =
      -∫ x in Ω, (fderiv ℝ f x) (EuclideanSpace.single i 1) * ψ x := by
  have hf_C1 : ContDiff ℝ 1 f := hf.of_le (by norm_cast)
  have h_weak := DeGiorgi.HasWeakPartialDeriv.of_contDiff (d := d) hΩ
    (i := i) (f := f) hf_C1
  exact h_weak ψ hψ hψ_support hψ_tsub

private lemma integrable_principalIntegrand_smooth_test
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {v ψ : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_support : HasCompactSupport ψ) :
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
    have hψ_partial_support : HasCompactSupport
        (fun x : E => (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) :=
      hψ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
    have h_support : HasCompactSupport (fun x : E => B.a x i j *
        ((fderiv ℝ v x) (EuclideanSpace.single i 1)) *
        ((fderiv ℝ ψ x) (EuclideanSpace.single j 1))) :=
      hψ_partial_support.mul_left
    exact (h_cont.integrable_of_hasCompactSupport h_support).restrict
  unfold SmoothEllipticBilinearForm.principalIntegrand
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => h_summand_int i j))

private lemma integrable_zeroth_smooth_test
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {v ψ : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_support : HasCompactSupport ψ) :
    Integrable (fun x => B.c x * v x * ψ x) (volume.restrict Ω) := by
  have h_cont : Continuous (fun x : E => B.c x * v x * ψ x) :=
    (B.continuous_c.mul hv.continuous).mul hψ.continuous
  have h_support : HasCompactSupport (fun x : E => B.c x * v x * ψ x) :=
    hψ_support.mul_left
  exact (h_cont.integrable_of_hasCompactSupport h_support).restrict

private lemma integrable_principalIntegrand_term_smooth_test
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {v ψ : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_support : HasCompactSupport ψ) (i j : Fin d) :
    Integrable (fun x : E => B.a x i j *
        ((fderiv ℝ v x) (EuclideanSpace.single i 1)) *
        ((fderiv ℝ ψ x) (EuclideanSpace.single j 1))) (volume.restrict Ω) := by
  have h_cont : Continuous (fun x : E => B.a x i j *
      ((fderiv ℝ v x) (EuclideanSpace.single i 1)) *
      ((fderiv ℝ ψ x) (EuclideanSpace.single j 1))) := by
    refine ((B.continuous_a i j).mul ?_).mul ?_
    · exact (hv.continuous_fderiv (by simp)).clm_apply continuous_const
    · exact (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have h_support : HasCompactSupport (fun x : E => B.a x i j *
      ((fderiv ℝ v x) (EuclideanSpace.single i 1)) *
      ((fderiv ℝ ψ x) (EuclideanSpace.single j 1))) := by
    have hψ_partial_support : HasCompactSupport
        (fun x : E => (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) :=
      hψ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
    exact hψ_partial_support.mul_left
  exact (h_cont.integrable_of_hasCompactSupport h_support).restrict

private lemma bilin_decomp_smooth
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {v ψ : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_support : HasCompactSupport ψ) :
    B.bilin v ψ =
      (∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω, B.a x i j *
        (fderiv ℝ v x) (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) +
      ∫ x in Ω, B.c x * v x * ψ x := by
  classical
  have h_princ_int := integrable_principalIntegrand_smooth_test (d := d)
    B hv hψ hψ_support
  have h_zero_int := integrable_zeroth_smooth_test (d := d)
    B hv hψ hψ_support
  have h_summand_int := integrable_principalIntegrand_term_smooth_test
    (d := d) B hv hψ hψ_support
  unfold SmoothEllipticBilinearForm.bilin
  rw [integral_add h_princ_int h_zero_int]
  congr 1
  unfold SmoothEllipticBilinearForm.principalIntegrand
  rw [integral_finsetSum (s := Finset.univ) (f := fun (i : Fin d) (x : E) =>
      ∑ j : Fin d, B.a x i j *
        (fderiv ℝ v x) (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1))
    (fun i _ => integrable_finsetSum _ (fun j _ => h_summand_int i j))]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [integral_finsetSum (s := Finset.univ) (f := fun (j : Fin d) (x : E) =>
      B.a x i j *
        (fderiv ℝ v x) (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1))
    (fun j _ => h_summand_int i j)]

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

private lemma ibp_innerSum_against_test
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_support : HasCompactSupport ψ) (hψ_tsub : tsupport ψ ⊆ Ω) (i : Fin d) :
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
  exact ibp_smooth_against_test_inner (d := d) h_inner_smooth hΩ hψ hψ_support
    hψ_tsub i

private lemma principal_eq_neg_classical
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_support : HasCompactSupport ψ) (hψ_tsub : tsupport ψ ⊆ Ω) :
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
        B hv hψ hψ_support j i
    rw [← integral_finsetSum (s := Finset.univ) (f := fun (j : Fin d) (x : E) =>
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
  exact ibp_innerSum_against_test (d := d) hΩ B hv hψ hψ_support hψ_tsub i

private lemma integrable_classicalApply_term_against_psi
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {v ψ : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_support : HasCompactSupport ψ) (i : Fin d) :
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
  have h_support : HasCompactSupport (fun x : E => (fderiv ℝ (fun y : E =>
      ∑ j : Fin d, B.a y i j *
        (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
        (EuclideanSpace.single i 1) * ψ x) :=
    hψ_support.mul_left
  exact (h_cont.integrable_of_hasCompactSupport h_support).restrict

theorem isSmoothWeakSolution_classicalApply
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    B.IsSmoothWeakSolution v (B.classicalApply v) := by
  refine ⟨hv, ?_⟩
  intro ψ hψ_smooth hψ_support hψ_tsub
  rw [bilin_decomp_smooth (d := d) B hv hψ_smooth hψ_support]
  rw [principal_eq_neg_classical (d := d) hΩ B hv hψ_smooth hψ_support hψ_tsub]
  unfold SmoothEllipticBilinearForm.classicalApply
  have h_class_int : ∀ i : Fin d, Integrable (fun x : E =>
      (fderiv ℝ (fun y : E => ∑ j : Fin d, B.a y i j *
        (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
        (EuclideanSpace.single i 1) * ψ x) (volume.restrict Ω) := fun i =>
    integrable_classicalApply_term_against_psi (d := d) B hv hψ_smooth
      hψ_support i
  have h_zero_int : Integrable (fun x : E => B.c x * v x * ψ x)
      (volume.restrict Ω) :=
    integrable_zeroth_smooth_test (d := d) B hv hψ_smooth hψ_support
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
        exact integrable_finsetSum _ (fun i _ => h_class_int i)
      exact h_sum_int.neg
    rw [integral_add h_neg_sum_int h_zero_int]
    rw [integral_neg]
    rw [integral_finsetSum (s := Finset.univ)
      (f := fun (i : Fin d) (x : E) => (fderiv ℝ (fun y : E =>
          ∑ j : Fin d, B.a y i j *
            (fderiv ℝ v y) (EuclideanSpace.single j 1)) x)
          (EuclideanSpace.single i 1) * ψ x)
      (fun i _ => h_class_int i)]
  rw [h_rhs_eq]

theorem mollifyEps_isSmoothWeakSolution_classicalApply
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu_local : LocallyIntegrable u (volume : Measure E))
    {ε : ℝ} (hε : 0 < ε) :
    B.IsSmoothWeakSolution
      (DifferentialGeometry.Analysis.Sobolev.mollifyEps
        (d := d) hε u)
      (B.classicalApply
        (DifferentialGeometry.Analysis.Sobolev.mollifyEps
          (d := d) hε u)) := by
  have h_uε_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (DifferentialGeometry.Analysis.Sobolev.mollifyEps
        (d := d) hε u) :=
    DifferentialGeometry.Analysis.Sobolev.mollifyEps_contDiff
      (d := d) hε hu_local
  exact isSmoothWeakSolution_classicalApply (d := d) hΩ B h_uε_smooth

theorem integral_classicalApply_mollifyEps_eq_bilin
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu_local : LocallyIntegrable u (volume : Measure E))
    {ε : ℝ} (hε : 0 < ε)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_support : HasCompactSupport ψ) (hψ_tsub : tsupport ψ ⊆ Ω) :
    ∫ x in Ω, B.classicalApply
      (DifferentialGeometry.Analysis.Sobolev.mollifyEps
        (d := d) hε u) x * ψ x =
      B.bilin (DifferentialGeometry.Analysis.Sobolev.mollifyEps
        (d := d) hε u) ψ := by
  have h_smooth_weak :=
    mollifyEps_isSmoothWeakSolution_classicalApply (d := d) hΩ B hu_local hε
  exact (h_smooth_weak.2 ψ hψ hψ_support hψ_tsub).symm

theorem integral_classicalApply_mollifyEps_sub_eq_bilin_sub
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (hu_local : LocallyIntegrable u (volume : Measure E))
    (h_weak : B.IsWeakSolution u f)
    {ε : ℝ} (hε : 0 < ε)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_support : HasCompactSupport ψ) (hψ_tsub : tsupport ψ ⊆ Ω)
    (hf_psi_int : Integrable (fun x : E => f x * ψ x) (volume.restrict Ω)) :
    ∫ x in Ω, (B.classicalApply
        (DifferentialGeometry.Analysis.Sobolev.mollifyEps
          (d := d) hε u) x - f x) * ψ x =
      B.bilin (DifferentialGeometry.Analysis.Sobolev.mollifyEps
        (d := d) hε u) ψ - B.bilin u ψ := by
  have h_lhs_split : ∫ x in Ω, (B.classicalApply
        (DifferentialGeometry.Analysis.Sobolev.mollifyEps
          (d := d) hε u) x - f x) * ψ x =
      (∫ x in Ω, B.classicalApply
        (DifferentialGeometry.Analysis.Sobolev.mollifyEps
          (d := d) hε u) x * ψ x) -
      ∫ x in Ω, f x * ψ x := by
    have h_smooth_weak :=
      mollifyEps_isSmoothWeakSolution_classicalApply (d := d) hΩ B hu_local hε
    have h_pairing_int : Integrable (fun x : E => B.classicalApply
        (DifferentialGeometry.Analysis.Sobolev.mollifyEps
          (d := d) hε u) x * ψ x) (volume.restrict Ω) := by
      have h_class_smooth : ContDiff ℝ (⊤ : ℕ∞) (B.classicalApply
          (DifferentialGeometry.Analysis.Sobolev.mollifyEps
            (d := d) hε u)) := by
        refine contDiff_classicalApply (d := d) B ?_
        exact DifferentialGeometry.Analysis.Sobolev.mollifyEps_contDiff
          (d := d) hε hu_local
      have h_cont : Continuous (fun x : E => B.classicalApply
          (DifferentialGeometry.Analysis.Sobolev.mollifyEps
            (d := d) hε u) x * ψ x) :=
        h_class_smooth.continuous.mul hψ.continuous
      have h_support : HasCompactSupport (fun x : E => B.classicalApply
          (DifferentialGeometry.Analysis.Sobolev.mollifyEps
            (d := d) hε u) x * ψ x) :=
        hψ_support.mul_left
      exact (h_cont.integrable_of_hasCompactSupport h_support).restrict
    have h_fun_eq : (fun x : E => (B.classicalApply
            (DifferentialGeometry.Analysis.Sobolev.mollifyEps
              (d := d) hε u) x - f x) * ψ x) =
          (fun x : E => B.classicalApply
              (DifferentialGeometry.Analysis.Sobolev.mollifyEps
                (d := d) hε u) x * ψ x - f x * ψ x) := by
      funext x; ring
    rw [h_fun_eq]
    rw [integral_sub h_pairing_int hf_psi_int]
  rw [h_lhs_split]
  have h_classicalApply_pair := integral_classicalApply_mollifyEps_eq_bilin
    (d := d) hΩ B hu_local hε hψ hψ_support hψ_tsub
  have h_weak_eq := h_weak ψ hψ hψ_support hψ_tsub
  rw [h_classicalApply_pair, h_weak_eq]

end SmoothEllipticBilinearForm
end DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

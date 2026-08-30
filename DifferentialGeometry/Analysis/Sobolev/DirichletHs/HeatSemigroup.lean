import DifferentialGeometry.Analysis.Sobolev.DirichletHs.Inclusion
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SmoothingConst
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.SpectralBounds

private lemma heatHk_weight_term_le {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenindex g)
    (a b : ℝ) {t : ℝ} (ht : 0 < t) (c : ℝ) :
    dirichletSobolevWeight i b *
        (Real.exp (-(dirichletLaplacianEigenvalue i) * t) * c) ^ 2 ≤
      max 1 (spectralSmoothingConst (b - a) * (min t 1) ^ (-(b - a))) *
        (dirichletSobolevWeight i a * c ^ 2) := by
  set lam := dirichletLaplacianEigenvalue i with hlam_def
  have hlam_nn : 0 ≤ lam := dirichletLaplacianEigenvalue_nonneg i
  have hbase_pos : (0 : ℝ) < 1 + lam := by linarith
  set K : ℝ :=
    max 1 (spectralSmoothingConst (b - a) * (min t 1) ^ (-(b - a))) with hK_def
  have hK_ge_one : (1 : ℝ) ≤ K := le_max_left _ _
  have h_weight_split :
      dirichletSobolevWeight i b =
        dirichletSobolevWeight i a *
          (1 + lam) ^ (b - a) := by
    unfold dirichletSobolevWeight
    rw [hlam_def, ← Real.rpow_add hbase_pos]
    congr 1
    ring
  have h_pe_le :
      (1 + lam) ^ (b - a) *
          Real.exp (-(lam * t) * 2) ≤ K := by
    rcases le_or_gt 0 (b - a) with hba | hba
    · have h_arg : -(lam * t) * 2 = -(2 * lam * t) := by ring
      rw [h_arg]
      set t' : ℝ := min t 1 with ht'_def
      have ht'_pos : 0 < t' := lt_min ht one_pos
      have ht'_le_one : t' ≤ 1 := min_le_right _ _
      have ht'_le_t : t' ≤ t := min_le_left _ _
      have h_exp_mono :
          Real.exp (-(2 * lam * t)) ≤ Real.exp (-(2 * lam * t')) := by
        apply Real.exp_le_exp.mpr
        have h : 2 * lam * t' ≤ 2 * lam * t :=
          mul_le_mul_of_nonneg_left ht'_le_t (by positivity)
        linarith
      have hbase_nn : (0 : ℝ) ≤ (1 + lam) ^ (b - a) :=
        Real.rpow_nonneg (by linarith) (b - a)
      have h_at_t' : (1 + lam) ^ (b - a) * Real.exp (-(2 * lam * t')) ≤
          spectralSmoothingConst (b - a) * t' ^ (-(b - a)) :=
        spectralSmoothingScalarBound hba ht'_pos ht'_le_one hlam_nn
      calc
        (1 + lam) ^ (b - a) * Real.exp (-(2 * lam * t))
            ≤ (1 + lam) ^ (b - a) * Real.exp (-(2 * lam * t')) :=
              mul_le_mul_of_nonneg_left h_exp_mono hbase_nn
        _ ≤ spectralSmoothingConst (b - a) * t' ^ (-(b - a)) := h_at_t'
        _ ≤ K := le_max_right _ _
    · have h_w_le_one : (1 + lam) ^ (b - a) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hba.le
      have h_exp_le_one : Real.exp (-(lam * t) * 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ lam * t := mul_nonneg hlam_nn ht.le
        nlinarith
      calc
        (1 + lam) ^ (b - a) * Real.exp (-(lam * t) * 2)
            ≤ 1 * 1 :=
              mul_le_mul (le_trans h_w_le_one (le_refl 1)) h_exp_le_one
                (Real.exp_pos _).le (by norm_num)
        _ = 1 := by norm_num
        _ ≤ K := hK_ge_one
  have hwa_nn : 0 ≤ dirichletSobolevWeight i a :=
    dirichletSobolevWeight_nonneg i a
  have hexp_sq :
      (Real.exp (-lam * t)) ^ 2 = Real.exp (-(lam * t) * 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc
    dirichletSobolevWeight i b *
          (Real.exp (-lam * t) * c) ^ 2
        = (dirichletSobolevWeight i a * c ^ 2) *
            ((1 + lam) ^ (b - a) * (Real.exp (-lam * t)) ^ 2) := by
          rw [h_weight_split]; ring
    _ = (dirichletSobolevWeight i a * c ^ 2) *
          ((1 + lam) ^ (b - a) * Real.exp (-(lam * t) * 2)) := by
          rw [hexp_sq]
    _ ≤ (dirichletSobolevWeight i a * c ^ 2) * K := by
          apply mul_le_mul_of_nonneg_left h_pe_le
          have : 0 ≤ c ^ 2 := sq_nonneg c
          positivity
    _ = K * (dirichletSobolevWeight i a * c ^ 2) := by ring

namespace dirichletHs

variable {g : SmoothRiemannianMetric (I_half n) M}

private lemma heatHk_weighted_summable {a : ℝ} (b : ℝ) {t : ℝ} (ht : 0 < t)
    (T : dirichletHs g a) :
    Summable (fun i : DirichletLaplacianEigenindex g =>
      dirichletSobolevWeight i b *
        (Real.exp (-(dirichletLaplacianEigenvalue i) * t) *
          T.coeff i) ^ 2) := by
  set K : ℝ :=
    max 1 (spectralSmoothingConst (b - a) * (min t 1) ^ (-(b - a))) with hK_def
  refine Summable.of_nonneg_of_le ?_ ?_ (T.weighted_summable.mul_left K)
  · intro i
    have hw : 0 ≤ dirichletSobolevWeight i b :=
      dirichletSobolevWeight_nonneg i b
    positivity
  · intro i
    exact heatHk_weight_term_le i a b ht (T.coeff i)

private def heatHkFun {a : ℝ} (b : ℝ) {t : ℝ} (ht : 0 < t)
    (T : dirichletHs g a) :
    dirichletHs g b where
  coeff i := Real.exp (-(dirichletLaplacianEigenvalue i) * t) *
    T.coeff i
  weighted_summable := heatHk_weighted_summable b ht T

@[simp] private lemma heatHkFun_coeff {a : ℝ} (b : ℝ) {t : ℝ} (ht : 0 < t)
    (T : dirichletHs g a)
    (i : DirichletLaplacianEigenindex g) :
    (heatHkFun b ht T).coeff i =
      Real.exp (-(dirichletLaplacianEigenvalue i) * t) *
        T.coeff i := rfl

private lemma heatHkFun_add {a : ℝ} (b : ℝ) {t : ℝ} (ht : 0 < t)
    (S T : dirichletHs g a) :
    heatHkFun b ht (S + T) =
      heatHkFun b ht S +
        heatHkFun b ht T := by
  ext i
  simp only [heatHkFun_coeff, add_coeff]
  ring

private lemma heatHkFun_smul {a : ℝ} (b : ℝ) {t : ℝ} (ht : 0 < t) (c : ℝ)
    (T : dirichletHs g a) :
    heatHkFun b ht (c • T) =
      c • heatHkFun b ht T := by
  ext i
  simp only [heatHkFun_coeff, smul_coeff]
  ring

private lemma norm_heatHkFun_le_smoothing {a b : ℝ} (hab : a ≤ b) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1)
    (T : dirichletHs g a) :
    ‖heatHkFun b ht T‖ ≤
      Real.sqrt (spectralSmoothingConst (b - a)) *
        t ^ (-((b - a) / 2)) * ‖T‖ := by
  have hba_nn : 0 ≤ b - a := by linarith
  have hC_nn : 0 ≤ spectralSmoothingConst (b - a) :=
    spectralSmoothingConst_nonneg (b - a)
  have h_b_sq : ‖heatHkFun b ht T‖ ^ 2 =
      ∑' i, dirichletSobolevWeight i b *
        (Real.exp (-(dirichletLaplacianEigenvalue i) * t) *
          T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum
      (heatHkFun b ht T)
    simpa only [heatHkFun_coeff] using h
  have h_a_sq : ‖T‖ ^ 2 =
      ∑' i, dirichletSobolevWeight i a * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum T
  have h_term_le : ∀ i : DirichletLaplacianEigenindex g,
      dirichletSobolevWeight i b *
          (Real.exp (-(dirichletLaplacianEigenvalue i) * t) *
            T.coeff i) ^ 2 ≤
        (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
          (dirichletSobolevWeight i a * (T.coeff i) ^ 2) := by
    intro i
    set lam := dirichletLaplacianEigenvalue i with hlam_def
    have hlam_nn : 0 ≤ lam := dirichletLaplacianEigenvalue_nonneg i
    have hbase_pos : (0 : ℝ) < 1 + lam := by linarith
    have h_weight_split :
        dirichletSobolevWeight i b =
          dirichletSobolevWeight i a *
            (1 + lam) ^ (b - a) := by
      unfold dirichletSobolevWeight
      rw [hlam_def, ← Real.rpow_add hbase_pos]
      congr 1
      ring
    have hexp_sq :
        (Real.exp (-lam * t)) ^ 2 = Real.exp (-(2 * lam * t)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h_dirichlet :
        (1 + lam) ^ (b - a) * Real.exp (-(2 * lam * t)) ≤
          spectralSmoothingConst (b - a) * t ^ (-(b - a)) :=
      spectralSmoothingScalarBound hba_nn ht ht1 hlam_nn
    have hwa_nn : 0 ≤ dirichletSobolevWeight i a :=
      dirichletSobolevWeight_nonneg i a
    have hc2_nn : 0 ≤ (T.coeff i) ^ 2 := sq_nonneg _
    calc
      dirichletSobolevWeight i b *
            (Real.exp (-lam * t) * T.coeff i) ^ 2
          = (dirichletSobolevWeight i a * (T.coeff i) ^ 2) *
              ((1 + lam) ^ (b - a) * (Real.exp (-lam * t)) ^ 2) := by
            rw [h_weight_split]; ring
      _ = (dirichletSobolevWeight i a * (T.coeff i) ^ 2) *
            ((1 + lam) ^ (b - a) * Real.exp (-(2 * lam * t))) := by
            rw [hexp_sq]
      _ ≤ (dirichletSobolevWeight i a * (T.coeff i) ^ 2) *
            (spectralSmoothingConst (b - a) * t ^ (-(b - a))) := by
            apply mul_le_mul_of_nonneg_left h_dirichlet
            positivity
      _ = (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
            (dirichletSobolevWeight i a *
              (T.coeff i) ^ 2) := by ring
  have h_summ_b :
      Summable (fun i : DirichletLaplacianEigenindex g =>
        dirichletSobolevWeight i b *
          (Real.exp (-(dirichletLaplacianEigenvalue i) * t) *
            T.coeff i) ^ 2) :=
    heatHk_weighted_summable b ht T
  have h_summ_dom :
      Summable (fun i : DirichletLaplacianEigenindex g =>
        (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
          (dirichletSobolevWeight i a *
            (T.coeff i) ^ 2)) :=
    T.weighted_summable.mul_left _
  have h_tsum_le :
      ∑' i, dirichletSobolevWeight i b *
          (Real.exp (-(dirichletLaplacianEigenvalue i) * t) *
            T.coeff i) ^ 2 ≤
        ∑' i, (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
          (dirichletSobolevWeight i a *
            (T.coeff i) ^ 2) :=
    Summable.tsum_le_tsum h_term_le h_summ_b h_summ_dom
  have h_tsum_factor :
      ∑' i, (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
          (dirichletSobolevWeight i a *
            (T.coeff i) ^ 2) =
        (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
          ∑' i, (dirichletSobolevWeight i a *
            (T.coeff i) ^ 2) :=
    tsum_mul_left
  have h_sq_le : ‖heatHkFun b ht T‖ ^ 2 ≤
      (spectralSmoothingConst (b - a) * t ^ (-(b - a))) * ‖T‖ ^ 2 := by
    rw [h_b_sq, h_a_sq]
    calc
      ∑' i, dirichletSobolevWeight i b *
            (Real.exp (-(dirichletLaplacianEigenvalue i) * t) *
              T.coeff i) ^ 2
          ≤ ∑' i, (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
              (dirichletSobolevWeight i a *
                (T.coeff i) ^ 2) := h_tsum_le
      _ = (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
            ∑' i, (dirichletSobolevWeight i a *
              (T.coeff i) ^ 2) := h_tsum_factor
  have h_rhs_sq :
      (Real.sqrt (spectralSmoothingConst (b - a)) * t ^ (-((b - a) / 2))) ^ 2 =
        spectralSmoothingConst (b - a) * t ^ (-(b - a)) := by
    have h_sqrt_sq :
        Real.sqrt (spectralSmoothingConst (b - a)) ^ 2 =
          spectralSmoothingConst (b - a) :=
      Real.sq_sqrt hC_nn
    have h_t_sq : (t ^ (-((b - a) / 2))) ^ 2 = t ^ (-(b - a)) := by
      rw [← Real.rpow_natCast (t ^ (-((b - a) / 2))) 2,
        ← Real.rpow_mul ht.le]
      congr 1
      push_cast
      ring
    calc
      (Real.sqrt (spectralSmoothingConst (b - a)) * t ^ (-((b - a) / 2))) ^ 2
          = Real.sqrt (spectralSmoothingConst (b - a)) ^ 2 *
              (t ^ (-((b - a) / 2))) ^ 2 := by ring
      _ = spectralSmoothingConst (b - a) * t ^ (-(b - a)) := by
            rw [h_sqrt_sq, h_t_sq]
  have h_final_sq : ‖heatHkFun b ht T‖ ^ 2 ≤
      (Real.sqrt (spectralSmoothingConst (b - a)) * t ^ (-((b - a) / 2)) *
        ‖T‖) ^ 2 := by
    have h_expand :
        (Real.sqrt (spectralSmoothingConst (b - a)) * t ^ (-((b - a) / 2)) *
            ‖T‖) ^ 2 =
          (Real.sqrt (spectralSmoothingConst (b - a)) *
              t ^ (-((b - a) / 2))) ^ 2 * ‖T‖ ^ 2 := by
      ring
    rw [h_expand, h_rhs_sq]
    exact h_sq_le
  have h_lhs_nn : 0 ≤ ‖heatHkFun b ht T‖ := norm_nonneg _
  have h_rhs_nn :
      0 ≤ Real.sqrt (spectralSmoothingConst (b - a)) * t ^ (-((b - a) / 2)) *
        ‖T‖ := by
    have h1 : 0 ≤ Real.sqrt (spectralSmoothingConst (b - a)) :=
      Real.sqrt_nonneg _
    have h2 : 0 ≤ ‖T‖ := norm_nonneg T
    have h3 : 0 ≤ t ^ (-((b - a) / 2)) := (Real.rpow_pos_of_pos ht _).le
    positivity
  nlinarith [h_final_sq, h_lhs_nn, h_rhs_nn]

private lemma norm_heatHkFun_le_self {a : ℝ} {t : ℝ} (ht : 0 < t)
    (T : dirichletHs g a) :
    ‖heatHkFun a ht T‖ ≤ ‖T‖ := by
  have h_a_sq_heat : ‖heatHkFun a ht T‖ ^ 2 =
      ∑' i, dirichletSobolevWeight i a *
        (Real.exp (-(dirichletLaplacianEigenvalue i) * t) *
          T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum
      (heatHkFun a ht T)
    simpa only [heatHkFun_coeff] using h
  have h_a_sq : ‖T‖ ^ 2 =
      ∑' i, dirichletSobolevWeight i a * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum T
  have h_term_le : ∀ i : DirichletLaplacianEigenindex g,
      dirichletSobolevWeight i a *
          (Real.exp (-(dirichletLaplacianEigenvalue i) * t) *
            T.coeff i) ^ 2 ≤
        dirichletSobolevWeight i a * (T.coeff i) ^ 2 := by
    intro i
    set lam := dirichletLaplacianEigenvalue i with hlam_def
    have hlam_nn : 0 ≤ lam := dirichletLaplacianEigenvalue_nonneg i
    have hwa_nn : 0 ≤ dirichletSobolevWeight i a :=
      dirichletSobolevWeight_nonneg i a
    have h_exp_le_one :
        Real.exp (-lam * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ lam * t := mul_nonneg hlam_nn ht.le
      nlinarith
    have h_exp_nn : 0 ≤ Real.exp (-lam * t) := (Real.exp_pos _).le
    have h_sq_le : (Real.exp (-lam * t) * T.coeff i) ^ 2 ≤ (T.coeff i) ^ 2 := by
      have h_exp_sq_le : (Real.exp (-lam * t)) ^ 2 ≤ 1 := by
        nlinarith [h_exp_le_one, h_exp_nn]
      have hc2 : 0 ≤ (T.coeff i) ^ 2 := sq_nonneg _
      calc
        (Real.exp (-lam * t) * T.coeff i) ^ 2
            = (Real.exp (-lam * t)) ^ 2 * (T.coeff i) ^ 2 := by ring
        _ ≤ 1 * (T.coeff i) ^ 2 :=
              mul_le_mul_of_nonneg_right h_exp_sq_le hc2
        _ = (T.coeff i) ^ 2 := one_mul _
    exact mul_le_mul_of_nonneg_left h_sq_le hwa_nn
  have h_summ_heat :
      Summable (fun i : DirichletLaplacianEigenindex g =>
        dirichletSobolevWeight i a *
          (Real.exp (-(dirichletLaplacianEigenvalue i) * t) *
            T.coeff i) ^ 2) :=
    heatHk_weighted_summable a ht T
  have h_tsum_le :
      ∑' i, dirichletSobolevWeight i a *
          (Real.exp (-(dirichletLaplacianEigenvalue i) * t) *
            T.coeff i) ^ 2 ≤
        ∑' i, dirichletSobolevWeight i a * (T.coeff i) ^ 2 :=
    Summable.tsum_le_tsum h_term_le h_summ_heat T.weighted_summable
  have h_sq_le : ‖heatHkFun a ht T‖ ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [h_a_sq_heat, h_a_sq]
    exact h_tsum_le
  have h1 : 0 ≤ ‖heatHkFun a ht T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  nlinarith [h_sq_le, h1, h2]

end dirichletHs

def dirichletHeatSemigroupHs {g : SmoothRiemannianMetric (I_half n) M}
    {t : ℝ} (ht : 0 < t) {a b : ℝ} :
    dirichletHs g a →L[ℝ]
      dirichletHs g b :=
  LinearMap.mkContinuous
    { toFun := dirichletHs.heatHkFun b ht
      map_add' := dirichletHs.heatHkFun_add b ht
      map_smul' := fun c T =>
        dirichletHs.heatHkFun_smul b ht c T }
    (max 1 (spectralSmoothingConst (b - a) * (min t 1) ^ (-(b - a))))
    (fun T => by
      change ‖dirichletHs.heatHkFun b ht T‖ ≤ _
      set K : ℝ :=
        max 1 (spectralSmoothingConst (b - a) * (min t 1) ^ (-(b - a)))
        with hK_def
      have hK_ge_one : (1 : ℝ) ≤ K := le_max_left _ _
      have hK_nn : 0 ≤ K := le_trans zero_le_one hK_ge_one
      have h_b_sq : ‖dirichletHs.heatHkFun b ht T‖ ^ 2 =
          ∑' i, dirichletSobolevWeight i b *
            (Real.exp (-(dirichletLaplacianEigenvalue i) * t) *
              T.coeff i) ^ 2 := by
        have h := dirichletHs.norm_sq_eq_tsum
          (dirichletHs.heatHkFun b ht T)
        simpa only [dirichletHs.heatHkFun_coeff] using h
      have h_a_sq : ‖T‖ ^ 2 =
          ∑' i, dirichletSobolevWeight i a *
            (T.coeff i) ^ 2 :=
        dirichletHs.norm_sq_eq_tsum T
      have h_term_le : ∀ i : DirichletLaplacianEigenindex g,
          dirichletSobolevWeight i b *
              (Real.exp
                  (-(dirichletLaplacianEigenvalue i) * t) *
                T.coeff i) ^ 2 ≤
            K * (dirichletSobolevWeight i a *
              (T.coeff i) ^ 2) := by
        intro i
        exact heatHk_weight_term_le i a b ht (T.coeff i)
      have h_summ_b :
          Summable (fun i : DirichletLaplacianEigenindex g =>
            dirichletSobolevWeight i b *
              (Real.exp
                  (-(dirichletLaplacianEigenvalue i) * t) *
                T.coeff i) ^ 2) :=
        dirichletHs.heatHk_weighted_summable b ht T
      have h_summ_dom :
          Summable (fun i : DirichletLaplacianEigenindex g =>
            K * (dirichletSobolevWeight i a *
              (T.coeff i) ^ 2)) :=
        T.weighted_summable.mul_left K
      have h_tsum_le :
          ∑' i, dirichletSobolevWeight i b *
              (Real.exp
                  (-(dirichletLaplacianEigenvalue i) * t) *
                T.coeff i) ^ 2 ≤
            ∑' i, K * (dirichletSobolevWeight i a *
              (T.coeff i) ^ 2) :=
        Summable.tsum_le_tsum h_term_le h_summ_b h_summ_dom
      have h_tsum_factor :
          ∑' i, K * (dirichletSobolevWeight i a *
              (T.coeff i) ^ 2) =
            K * ∑' i, (dirichletSobolevWeight i a *
              (T.coeff i) ^ 2) :=
        tsum_mul_left
      have h_sq_le :
          ‖dirichletHs.heatHkFun b ht T‖ ^ 2 ≤
            K * ‖T‖ ^ 2 := by
        rw [h_b_sq, h_a_sq]
        rw [← h_tsum_factor]
        exact h_tsum_le
      have h_sqrtK_sq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK_nn
      have h_final_sq :
          ‖dirichletHs.heatHkFun b ht T‖ ^ 2 ≤
            (Real.sqrt K * ‖T‖) ^ 2 := by
        have h_expand : (Real.sqrt K * ‖T‖) ^ 2 = K * ‖T‖ ^ 2 := by
          rw [mul_pow, h_sqrtK_sq]
        rw [h_expand]
        exact h_sq_le
      have h1 : 0 ≤ ‖dirichletHs.heatHkFun b ht T‖ :=
        norm_nonneg _
      have h2 : 0 ≤ ‖T‖ := norm_nonneg T
      have h_sqrtK_nn : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
      have h_norm_le_sqrt :
          ‖dirichletHs.heatHkFun b ht T‖ ≤
            Real.sqrt K * ‖T‖ := by
        nlinarith [h_final_sq, h1, mul_nonneg h_sqrtK_nn h2]
      have h_sqrtK_le_K : Real.sqrt K ≤ K := by
        have h_K_le_sq : K ≤ K ^ 2 := by nlinarith [hK_ge_one]
        calc Real.sqrt K ≤ Real.sqrt (K ^ 2) :=
              Real.sqrt_le_sqrt h_K_le_sq
          _ = K := Real.sqrt_sq hK_nn
      calc
        ‖dirichletHs.heatHkFun b ht T‖ ≤ Real.sqrt K * ‖T‖ :=
          h_norm_le_sqrt
        _ ≤ K * ‖T‖ := mul_le_mul_of_nonneg_right h_sqrtK_le_K h2)

@[simp] private lemma dirichletHeatSemigroupHs_apply {g : SmoothRiemannianMetric (I_half n) M}
    {t : ℝ} (ht : 0 < t) {a b : ℝ}
    (T : dirichletHs g a) :
    dirichletHeatSemigroupHs (g := g) ht (a := a) (b := b) T =
      dirichletHs.heatHkFun b ht T := rfl

@[simp] theorem dirichletHeatSemigroupHs_coeff {g : SmoothRiemannianMetric (I_half n) M}
    {t : ℝ} (ht : 0 < t) {a b : ℝ}
    (T : dirichletHs g a)
    (i : DirichletLaplacianEigenindex g) :
    (dirichletHeatSemigroupHs (g := g) ht (a := a) (b := b)
        T).coeff i =
      Real.exp (-(dirichletLaplacianEigenvalue i) * t) *
        T.coeff i := rfl

theorem dirichletHeatSemigroupHs_opNorm_le {g : SmoothRiemannianMetric (I_half n) M}
    {a b : ℝ} (hab : a ≤ b) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖dirichletHeatSemigroupHs (g := g) ht (a := a) (b := b)‖ ≤
      Real.sqrt (spectralSmoothingConst (b - a)) * t ^ (-((b - a) / 2)) := by
  have h_bound_nn :
      0 ≤ Real.sqrt (spectralSmoothingConst (b - a)) *
        t ^ (-((b - a) / 2)) := by
    have h1 : 0 ≤ Real.sqrt (spectralSmoothingConst (b - a)) :=
      Real.sqrt_nonneg _
    have h2 : 0 ≤ t ^ (-((b - a) / 2)) :=
      (Real.rpow_pos_of_pos ht _).le
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ h_bound_nn (fun T => ?_)
  rw [dirichletHeatSemigroupHs_apply]
  exact dirichletHs.norm_heatHkFun_le_smoothing hab ht ht1 T

theorem dirichletHeatSemigroupHs_opNorm_le_one {g : SmoothRiemannianMetric (I_half n) M}
    {a : ℝ} {t : ℝ} (ht : 0 < t) :
    ‖dirichletHeatSemigroupHs (g := g) ht (a := a) (b := a)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun T => ?_)
  rw [dirichletHeatSemigroupHs_apply, one_mul]
  exact dirichletHs.norm_heatHkFun_le_self ht T

theorem dirichletHeatSemigroupHs_add {g : SmoothRiemannianMetric (I_half n) M}
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) {a : ℝ} :
    dirichletHeatSemigroupHs (g := g)
        (show (0:ℝ) < t + s by linarith) (a := a) (b := a) =
      (dirichletHeatSemigroupHs (g := g) ht (a := a) (b := a)).comp
        (dirichletHeatSemigroupHs (g := g) hs (a := a) (b := a)) := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  rw [ContinuousLinearMap.comp_apply]
  refine dirichletHs.ext ?_
  funext i
  rw [dirichletHeatSemigroupHs_coeff, dirichletHeatSemigroupHs_coeff, dirichletHeatSemigroupHs_coeff]
  set lam := dirichletLaplacianEigenvalue i with hlam_def
  have h_exp_add :
      Real.exp (-lam * (t + s)) =
        Real.exp (-lam * t) * Real.exp (-lam * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_exp_add]
  ring

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end

import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletEigenBasis
import Mathlib.Analysis.InnerProductSpace.l2Space
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

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def dirichletSobolevWeight {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenindex g) (σ : ℝ) : ℝ :=
  (1 + dirichletLaplacianEigenvalue i) ^ σ

lemma one_le_one_add_dirichletLaplacianEigenvalue {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenindex g) :
    (1 : ℝ) ≤ 1 + dirichletLaplacianEigenvalue i := by
  have h := dirichletLaplacianEigenvalue_nonneg i
  linarith

lemma dirichletSobolevWeight_pos {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenindex g) (σ : ℝ) :
    0 < dirichletSobolevWeight i σ := by
  unfold dirichletSobolevWeight
  have h : (1 : ℝ) ≤ 1 + dirichletLaplacianEigenvalue i :=
    one_le_one_add_dirichletLaplacianEigenvalue i
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos h) σ

lemma dirichletSobolevWeight_nonneg {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenindex g) (σ : ℝ) :
    0 ≤ dirichletSobolevWeight i σ :=
  (dirichletSobolevWeight_pos i σ).le

lemma one_le_dirichletSobolevWeight {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenindex g) {σ : ℝ} (hσ : 0 ≤ σ) :
    1 ≤ dirichletSobolevWeight i σ := by
  unfold dirichletSobolevWeight
  exact Real.one_le_rpow (one_le_one_add_dirichletLaplacianEigenvalue i) hσ

@[simp] lemma dirichletSobolevWeight_zero {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenindex g) :
    dirichletSobolevWeight i (0 : ℝ) = 1 := by
  unfold dirichletSobolevWeight
  exact Real.rpow_zero _

lemma sq_sqrt_dirichletSobolevWeight {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenindex g) (σ : ℝ) :
    Real.sqrt (dirichletSobolevWeight i σ) ^ 2 =
      dirichletSobolevWeight i σ :=
  Real.sq_sqrt (dirichletSobolevWeight_nonneg i σ)

def dirichletL2Coeff {g : SmoothRiemannianMetric (I_half n) M}
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (i : DirichletLaplacianEigenindex g) : ℝ :=
  (dirichletLaplacianHilbertBasis g).repr u i

structure dirichletHs (g : SmoothRiemannianMetric (I_half n) M) (σ : ℝ) where
  coeff : DirichletLaplacianEigenindex g → ℝ
  weighted_summable :
    Summable (fun i => dirichletSobolevWeight i σ *
      (coeff i) ^ 2)

namespace dirichletHs

variable {g : SmoothRiemannianMetric (I_half n) M} {σ : ℝ}

@[ext] lemma ext {S T : dirichletHs g σ}
    (h : S.coeff = T.coeff) : S = T := by
  cases S; cases T; cases h; rfl

instance : Zero (dirichletHs g σ) where
  zero := ⟨fun _ => 0, by simp⟩

@[simp] lemma zero_coeff :
    (0 : dirichletHs g σ).coeff =
      (fun _ => 0) := rfl

instance : Add (dirichletHs g σ) where
  add S T :=
    { coeff := fun i => S.coeff i + T.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have hT := T.weighted_summable
        have h_dom : Summable
            (fun i : DirichletLaplacianEigenindex g =>
              2 * (dirichletSobolevWeight i σ *
                  (S.coeff i) ^ 2) +
                2 * (dirichletSobolevWeight i σ *
                  (T.coeff i) ^ 2)) :=
          (hS.mul_left 2).add (hT.mul_left 2)
        refine Summable.of_nonneg_of_le ?_ ?_ h_dom
        · intro i
          have hw : 0 ≤ dirichletSobolevWeight i σ :=
            dirichletSobolevWeight_nonneg i σ
          positivity
        · intro i
          have hw : 0 ≤ dirichletSobolevWeight i σ :=
            dirichletSobolevWeight_nonneg i σ
          have h_sq : (S.coeff i + T.coeff i) ^ 2 ≤
              2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2 := by
            nlinarith [sq_nonneg (S.coeff i - T.coeff i)]
          calc
            dirichletSobolevWeight i σ *
                  (S.coeff i + T.coeff i) ^ 2
                ≤ dirichletSobolevWeight i σ *
                  (2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2) :=
                  mul_le_mul_of_nonneg_left h_sq hw
            _ = 2 * (dirichletSobolevWeight i σ *
                    (S.coeff i) ^ 2) +
                  2 * (dirichletSobolevWeight i σ *
                    (T.coeff i) ^ 2) := by ring }

@[simp] lemma add_coeff
    (S T : dirichletHs g σ) :
    (S + T).coeff = (fun i => S.coeff i + T.coeff i) := rfl

instance : Neg (dirichletHs g σ) where
  neg S :=
    { coeff := fun i => -S.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have h_eq :
            (fun i : DirichletLaplacianEigenindex g =>
              dirichletSobolevWeight i σ *
                (-S.coeff i) ^ 2) =
            (fun i => dirichletSobolevWeight i σ *
                (S.coeff i) ^ 2) := by
          funext i; ring
        rwa [h_eq] }

@[simp] lemma neg_coeff (S : dirichletHs g σ) :
    (-S).coeff = (fun i => -S.coeff i) := rfl

instance : Sub (dirichletHs g σ) where
  sub S T :=
    { coeff := fun i => S.coeff i - T.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have hT := T.weighted_summable
        have h_dom : Summable
            (fun i : DirichletLaplacianEigenindex g =>
              2 * (dirichletSobolevWeight i σ *
                  (S.coeff i) ^ 2) +
                2 * (dirichletSobolevWeight i σ *
                  (T.coeff i) ^ 2)) :=
          (hS.mul_left 2).add (hT.mul_left 2)
        refine Summable.of_nonneg_of_le ?_ ?_ h_dom
        · intro i
          have hw : 0 ≤ dirichletSobolevWeight i σ :=
            dirichletSobolevWeight_nonneg i σ
          positivity
        · intro i
          have hw : 0 ≤ dirichletSobolevWeight i σ :=
            dirichletSobolevWeight_nonneg i σ
          have h_sq : (S.coeff i - T.coeff i) ^ 2 ≤
              2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2 := by
            nlinarith [sq_nonneg (S.coeff i + T.coeff i)]
          calc
            dirichletSobolevWeight i σ *
                  (S.coeff i - T.coeff i) ^ 2
                ≤ dirichletSobolevWeight i σ *
                  (2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2) :=
                  mul_le_mul_of_nonneg_left h_sq hw
            _ = 2 * (dirichletSobolevWeight i σ *
                    (S.coeff i) ^ 2) +
                  2 * (dirichletSobolevWeight i σ *
                    (T.coeff i) ^ 2) := by ring }

@[simp] lemma sub_coeff
    (S T : dirichletHs g σ) :
    (S - T).coeff = (fun i => S.coeff i - T.coeff i) := rfl

instance : SMul ℝ (dirichletHs g σ) where
  smul c S :=
    { coeff := fun i => c * S.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have h_eq :
            (fun i : DirichletLaplacianEigenindex g =>
              dirichletSobolevWeight i σ *
                (c * S.coeff i) ^ 2) =
            (fun i => c ^ 2 * (dirichletSobolevWeight i σ *
                (S.coeff i) ^ 2)) := by
          funext i; ring
        rw [h_eq]
        exact hS.mul_left _ }

@[simp] lemma smul_coeff (c : ℝ)
    (S : dirichletHs g σ) :
    (c • S).coeff = (fun i => c * S.coeff i) := rfl

instance : AddCommGroup (dirichletHs g σ) where
  add_assoc S T U := by ext i; simp [add_assoc]
  zero_add S := by ext i; simp
  add_zero S := by ext i; simp
  add_comm S T := by ext i; simp [add_comm]
  neg_add_cancel S := by ext i; simp
  sub_eq_add_neg S T := by ext i; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℝ (dirichletHs g σ) where
  one_smul S := by ext i; simp
  mul_smul a b S := by ext i; simp [mul_assoc]
  smul_zero c := by ext i; simp
  smul_add c S T := by ext i; simp [mul_add]
  add_smul a b S := by ext i; simp [add_mul]
  zero_smul S := by ext i; simp

lemma weightedProd_summable
    (S T : dirichletHs g σ) :
    Summable (fun i : DirichletLaplacianEigenindex g =>
      dirichletSobolevWeight i σ *
        (S.coeff i * T.coeff i)) := by
  have hS := S.weighted_summable
  have hT := T.weighted_summable
  have h_dom : Summable
      (fun i : DirichletLaplacianEigenindex g =>
        (1 / 2) * (dirichletSobolevWeight i σ *
            (S.coeff i) ^ 2) +
          (1 / 2) * (dirichletSobolevWeight i σ *
            (T.coeff i) ^ 2)) :=
    (hS.mul_left _).add (hT.mul_left _)
  refine Summable.of_norm_bounded h_dom ?_
  intro i
  have hw : 0 ≤ dirichletSobolevWeight i σ :=
    dirichletSobolevWeight_nonneg i σ
  have h_amgm :
      |dirichletSobolevWeight i σ *
          (S.coeff i * T.coeff i)| ≤
        (1 / 2) * (dirichletSobolevWeight i σ *
            (S.coeff i) ^ 2) +
          (1 / 2) * (dirichletSobolevWeight i σ *
            (T.coeff i) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hw]
    have h_prod : |S.coeff i * T.coeff i| ≤
        (1 / 2) * (S.coeff i) ^ 2 + (1 / 2) * (T.coeff i) ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|S.coeff i| - |T.coeff i|),
        abs_nonneg (S.coeff i), abs_nonneg (T.coeff i),
        sq_abs (S.coeff i), sq_abs (T.coeff i)]
    calc
      dirichletSobolevWeight i σ *
            |S.coeff i * T.coeff i|
          ≤ dirichletSobolevWeight i σ *
            ((1 / 2) * (S.coeff i) ^ 2 + (1 / 2) * (T.coeff i) ^ 2) :=
            mul_le_mul_of_nonneg_left h_prod hw
      _ = (1 / 2) * (dirichletSobolevWeight i σ *
              (S.coeff i) ^ 2) +
            (1 / 2) * (dirichletSobolevWeight i σ *
              (T.coeff i) ^ 2) := by ring
  simpa using h_amgm

def innerFun (S T : dirichletHs g σ) : ℝ :=
  ∑' i, dirichletSobolevWeight i σ *
    (S.coeff i * T.coeff i)

lemma innerFun_self (T : dirichletHs g σ) :
    innerFun T T =
      ∑' i, dirichletSobolevWeight i σ *
        (T.coeff i) ^ 2 := by
  unfold innerFun
  refine tsum_congr (fun i => ?_)
  rw [sq]

@[reducible] def innerCore :
    InnerProductSpace.Core ℝ
      (dirichletHs g σ) where
  inner S T := innerFun S T
  conj_inner_symm S T := by
    simp only [conj_trivial]
    unfold innerFun
    refine tsum_congr (fun i => ?_)
    ring
  re_inner_nonneg T := by
    simp only [RCLike.re_to_real]
    rw [show (innerFun T T) =
      ∑' i, dirichletSobolevWeight i σ *
        (T.coeff i) ^ 2 from innerFun_self T]
    refine tsum_nonneg (fun i => ?_)
    have hw : 0 ≤ dirichletSobolevWeight i σ :=
      dirichletSobolevWeight_nonneg i σ
    positivity
  add_left S T U := by
    change innerFun (S + T) U =
      innerFun S U + innerFun T U
    unfold innerFun
    rw [← Summable.tsum_add
      (weightedProd_summable S U)
      (weightedProd_summable T U)]
    refine tsum_congr (fun i => ?_)
    simp only [add_coeff]
    ring
  smul_left S T c := by
    simp only [conj_trivial]
    change innerFun (c • S) T =
      c * innerFun S T
    unfold innerFun
    rw [← tsum_mul_left]
    refine tsum_congr (fun i => ?_)
    simp only [smul_coeff]
    ring
  definite T hT := by
    rw [show (innerFun T T) =
      ∑' i, dirichletSobolevWeight i σ *
        (T.coeff i) ^ 2 from innerFun_self T] at hT
    have h_nonneg : ∀ i : DirichletLaplacianEigenindex g,
        0 ≤ dirichletSobolevWeight i σ * (T.coeff i) ^ 2 := by
      intro i
      have hw : 0 ≤ dirichletSobolevWeight i σ :=
        dirichletSobolevWeight_nonneg i σ
      positivity
    have h_zero : ∀ i : DirichletLaplacianEigenindex g,
        dirichletSobolevWeight i σ * (T.coeff i) ^ 2 = 0 := by
      intro i
      have h_le := Summable.le_tsum T.weighted_summable i
        (fun j _ => h_nonneg j)
      rw [hT] at h_le
      exact le_antisymm h_le (h_nonneg i)
    ext i
    have hwi : dirichletSobolevWeight i σ * (T.coeff i) ^ 2
        = 0 := h_zero i
    have hw_ne : dirichletSobolevWeight i σ ≠ 0 :=
      (dirichletSobolevWeight_pos i σ).ne'
    have h_sq : (T.coeff i) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hwi with h | h
      · exact absurd h hw_ne
      · exact h
    have : T.coeff i = 0 := by nlinarith [h_sq]
    simpa using this

instance instNormedAddCommGroup :
    NormedAddCommGroup (dirichletHs g σ) :=
  InnerProductSpace.Core.toNormedAddCommGroup
    (cd := innerCore (g := g) (σ := σ))

instance instInnerProductSpace :
    InnerProductSpace ℝ (dirichletHs g σ) :=
  InnerProductSpace.ofCore
    (innerCore (g := g) (σ := σ)).1

lemma inner_def (S T : dirichletHs g σ) :
    (inner ℝ S T : ℝ) =
      ∑' i, dirichletSobolevWeight i σ *
        (S.coeff i * T.coeff i) := rfl

lemma inner_self_eq (T : dirichletHs g σ) :
    (inner ℝ T T : ℝ) =
      ∑' i, dirichletSobolevWeight i σ *
        (T.coeff i) ^ 2 :=
  innerFun_self T

theorem norm_sq_eq_tsum
    (T : dirichletHs g σ) :
    ‖T‖ ^ 2 =
      ∑' i, dirichletSobolevWeight i σ *
        (T.coeff i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_self_eq]

theorem norm_eq_sqrt_tsum
    (T : dirichletHs g σ) :
    ‖T‖ =
      Real.sqrt (∑' i, dirichletSobolevWeight i σ *
        (T.coeff i) ^ 2) := by
  rw [← norm_sq_eq_tsum]
  exact (Real.sqrt_sq (norm_nonneg T)).symm

end dirichletHs

namespace dirichletHs

variable {g : SmoothRiemannianMetric (I_half n) M} {σ : ℝ}

lemma rescale_memℓp (T : dirichletHs g σ) :
    Memℓp (fun i : DirichletLaplacianEigenindex g =>
      Real.sqrt (dirichletSobolevWeight i σ) *
        T.coeff i) 2 := by
  apply memℓp_gen
  have h_eq :
      (fun i : DirichletLaplacianEigenindex g =>
        ‖Real.sqrt (dirichletSobolevWeight i σ) *
            T.coeff i‖ ^ (2 : ℝ≥0∞).toReal) =
      (fun i => dirichletSobolevWeight i σ *
          (T.coeff i) ^ 2) := by
    funext i
    have hpr : ‖Real.sqrt (dirichletSobolevWeight i σ) *
          T.coeff i‖ ^ (2 : ℝ≥0∞).toReal =
        ‖Real.sqrt (dirichletSobolevWeight i σ) *
          T.coeff i‖ ^ (2 : ℕ) := by
      rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    have hsq : Real.sqrt (dirichletSobolevWeight i σ) ^ 2 =
        dirichletSobolevWeight i σ :=
      sq_sqrt_dirichletSobolevWeight i σ
    rw [hpr, Real.norm_eq_abs, sq_abs, mul_pow, hsq]
  rw [h_eq]
  exact T.weighted_summable

def rescaleToL2 (T : dirichletHs g σ) :
    lp (fun _ : DirichletLaplacianEigenindex g => ℝ) 2 :=
  ⟨fun i => Real.sqrt (dirichletSobolevWeight i σ) *
      T.coeff i, rescale_memℓp T⟩

@[simp] lemma rescaleToL2_apply
    (T : dirichletHs g σ)
    (i : DirichletLaplacianEigenindex g) :
    (rescaleToL2 T : _ → ℝ) i =
      Real.sqrt (dirichletSobolevWeight i σ) *
        T.coeff i := rfl

lemma rescaleFromL2_weighted_summable
    (f : lp (fun _ : DirichletLaplacianEigenindex g => ℝ) 2) :
    Summable (fun i : DirichletLaplacianEigenindex g =>
      dirichletSobolevWeight i σ *
        ((Real.sqrt (dirichletSobolevWeight i σ))⁻¹ *
          (f : _ → ℝ) i) ^ 2) := by
  have hf : Summable (fun i : DirichletLaplacianEigenindex g =>
      ((f : _ → ℝ) i) ^ 2) := by
    have hmem := lp.memℓp f
    have h := hmem.summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_eq :
        (fun i : DirichletLaplacianEigenindex g =>
          ‖(f : _ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal) =
        (fun i => ((f : _ → ℝ) i) ^ 2) := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_num
    rwa [h_eq] at h
  have h_eq :
      (fun i : DirichletLaplacianEigenindex g =>
        dirichletSobolevWeight i σ *
          ((Real.sqrt (dirichletSobolevWeight i σ))⁻¹ *
            (f : _ → ℝ) i) ^ 2) =
      (fun i => ((f : _ → ℝ) i) ^ 2) := by
    funext i
    have hw_pos : 0 < dirichletSobolevWeight i σ :=
      dirichletSobolevWeight_pos i σ
    have hsq : Real.sqrt (dirichletSobolevWeight i σ) ^ 2 =
        dirichletSobolevWeight i σ :=
      sq_sqrt_dirichletSobolevWeight i σ
    rw [mul_pow, inv_pow, hsq]
    rw [← mul_assoc, mul_inv_cancel₀ hw_pos.ne', one_mul]
  rw [h_eq]
  exact hf

def rescaleFromL2
    (f : lp (fun _ : DirichletLaplacianEigenindex g => ℝ) 2) :
    dirichletHs g σ where
  coeff i := (Real.sqrt (dirichletSobolevWeight i σ))⁻¹ *
    (f : _ → ℝ) i
  weighted_summable := rescaleFromL2_weighted_summable f

@[simp] lemma rescaleFromL2_coeff
    (f : lp (fun _ : DirichletLaplacianEigenindex g => ℝ) 2)
    (i : DirichletLaplacianEigenindex g) :
    (rescaleFromL2 (g := g) (σ := σ) f).coeff i =
      (Real.sqrt (dirichletSobolevWeight i σ))⁻¹ *
        (f : _ → ℝ) i := rfl

def rescaleEquivL2 :
    dirichletHs g σ ≃ₗᵢ[ℝ]
      lp (fun _ : DirichletLaplacianEigenindex g => ℝ) 2 where
  toFun := rescaleToL2
  invFun := rescaleFromL2
  map_add' S T := by
    apply lp.ext
    funext i
    simp only [rescaleToL2, lp.coeFn_add, Pi.add_apply, add_coeff]
    ring
  map_smul' c T := by
    apply lp.ext
    funext i
    simp only [rescaleToL2, lp.coeFn_smul, Pi.smul_apply, smul_coeff,
      smul_eq_mul, RingHom.id_apply]
    ring
  left_inv T := by
    ext i
    simp only [rescaleFromL2_coeff, rescaleToL2_apply]
    have hsqrt_pos :
        0 < Real.sqrt (dirichletSobolevWeight i σ) :=
      Real.sqrt_pos.mpr (dirichletSobolevWeight_pos i σ)
    rw [← mul_assoc, inv_mul_cancel₀ hsqrt_pos.ne', one_mul]
  right_inv f := by
    apply lp.ext
    funext i
    simp only [rescaleToL2_apply, rescaleFromL2_coeff]
    have hsqrt_pos :
        0 < Real.sqrt (dirichletSobolevWeight i σ) :=
      Real.sqrt_pos.mpr (dirichletSobolevWeight_pos i σ)
    rw [← mul_assoc, mul_inv_cancel₀ hsqrt_pos.ne', one_mul]
  norm_map' T := by
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_lp_sq :
        ‖rescaleToL2 T‖ ^ 2 =
          ∑' i, dirichletSobolevWeight i σ *
            (T.coeff i) ^ 2 := by
      have h := lp.norm_rpow_eq_tsum
        (p := 2)
        (E := fun _ : DirichletLaplacianEigenindex g => ℝ)
        (by norm_num) (rescaleToL2 T)
      rw [hpr] at h
      have h_lhs : ‖rescaleToL2 T‖ ^ (2 : ℝ) =
          ‖rescaleToL2 T‖ ^ 2 := by norm_cast
      rw [h_lhs] at h
      rw [h]
      refine tsum_congr (fun i => ?_)
      have hsq :
          Real.sqrt (dirichletSobolevWeight i σ) ^ 2 =
            dirichletSobolevWeight i σ :=
        sq_sqrt_dirichletSobolevWeight i σ
      have hcast :
          ‖(rescaleToL2 T : _ → ℝ) i‖ ^ (2 : ℝ) =
            ‖(rescaleToL2 T : _ → ℝ) i‖ ^ (2 : ℕ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hcast, rescaleToL2_apply, Real.norm_eq_abs, sq_abs, mul_pow, hsq]
    have h_norm_sq : ‖T‖ ^ 2 =
        ∑' i, dirichletSobolevWeight i σ *
          (T.coeff i) ^ 2 :=
      norm_sq_eq_tsum T
    have h_eq_sq :
        ‖rescaleToL2 T‖ ^ 2 = ‖T‖ ^ 2 := by
      rw [h_lp_sq, h_norm_sq]
    have h1 : 0 ≤ ‖rescaleToL2 T‖ := norm_nonneg _
    have h2 : 0 ≤ ‖T‖ := norm_nonneg T
    have := congrArg Real.sqrt h_eq_sq
    rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at this

@[simp] lemma rescaleEquivL2_apply
    (T : dirichletHs g σ) :
    (rescaleEquivL2 (g := g) (σ := σ) T : _ → ℝ) =
      (fun i => Real.sqrt (dirichletSobolevWeight i σ) *
        T.coeff i) := rfl

instance instCompleteSpace :
    CompleteSpace (dirichletHs g σ) :=
  (rescaleEquivL2
    (g := g) (σ := σ)).toIsometryEquiv.completeSpace

end dirichletHs

abbrev DirichletHk (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ) : Type _ :=
  dirichletHs g (k : ℝ)

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end

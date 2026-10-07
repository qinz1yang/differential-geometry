/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.LieGroup.ProjectiveOrthogonal.Lattices.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Metrizable.Urysohn

open DifferentialGeometry.ProjectiveOrthogonalGroup
open MeasureTheory
open scoped ENNReal Pointwise

namespace DifferentialGeometry.ProjectiveOrthogonalGroup.Center

variable {n : ℕ}

local notation "ι" => Fin n ⊕ Fin 1
local notation "M" => MatrixSum (Fin n) (Fin 1) ℝ

open Matrix

theorem pmOneMat_eq_diagonal :
    (pmOneMat : M) = Matrix.diagonal (Sum.elim (fun _ => (1 : ℝ)) fun _ => -1) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [pmOneMat, Matrix.diagonal, Matrix.one_apply, Matrix.neg_apply]
  · have : a = b := Subsingleton.elim a b; subst this; simp

theorem star_diagonal (d : ι → ℝ) :
    (star (Matrix.diagonal d : M) : M) = Matrix.diagonal d := by
  change ((pmOneMat : Matrix ι ι ℝ) * (Matrix.diagonal d)ᴴ * pmOneMat) = Matrix.diagonal d
  rw [pmOneMat_eq_diagonal, Matrix.diagonal_conjTranspose]
  apply Matrix.ext
  intro a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h; rcases a with a | a <;> simp [star_trivial]
  · simp

theorem diagonal_mul_single {d : ι → ℝ} (a b : ι) (x : ℝ) :
    Matrix.diagonal d * Matrix.single a b x = d a • Matrix.single a b x := by
  apply Matrix.ext
  intro a' b'
  rw [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · simp

theorem single_mul_diagonal {d : ι → ℝ} (a b : ι) (x : ℝ) :
    Matrix.single a b x * Matrix.diagonal d = d b • Matrix.single a b x := by
  apply Matrix.ext
  intro a' b'
  rw [Matrix.mul_diagonal, Matrix.smul_apply, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; apply mul_comm
  · simp

theorem single_mul_single_of_ne {a b c d : ι} (h : b ≠ c) (x y : ℝ) :
    Matrix.single a b x * Matrix.single c d y = (0 : Matrix ι ι ℝ) := by
  apply Matrix.ext
  intro a' b'
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro e _
  by_cases h1 : a = a' ∧ b = e
  · obtain ⟨rfl, rfl⟩ := h1
    have h2 : ¬(c = b ∧ d = b') := fun ⟨h2, _⟩ => h h2.symm
    rw [Matrix.single_apply_same,
      show Matrix.single c d y b b' = (0 : ℝ) from Matrix.single_apply_of_ne c d y b b' h2,
      mul_zero]
  · rw [Matrix.single_apply_of_ne a b x a' e h1, zero_mul]

def signMat (k : Fin n) : Matrix ι ι ℝ :=
  Matrix.diagonal (Sum.elim (fun j => if j = k then -1 else 1) (fun _ => 1))

def signMatM (k : Fin n) : M := signMat k

theorem ofMatrix_symm_signMatM (k : Fin n) :
    MatrixSum.ofMatrix.symm (signMatM k) = signMat k := rfl

theorem signMat_sq (k : Fin n) : signMat k * signMat k = (1 : Matrix ι ι ℝ) := by
  have h1 : (1 : Matrix ι ι ℝ) = Matrix.diagonal (fun _ => 1) := Matrix.diagonal_one.symm
  rw [signMat, Matrix.diagonal_mul_diagonal, h1]
  apply congrArg Matrix.diagonal
  funext a
  rcases a with a | a
  · by_cases h : a = k <;> simp [h]
  · simp []

theorem star_signMat (k : Fin n) : (star (signMatM k) : M) = signMat k := star_diagonal _

theorem signMat_mem (k : Fin n) : signMatM k ∈ unitary M := by
  rw [Unitary.mem_iff, star_signMat]
  constructor <;> exact signMat_sq k

def boostD (i : Fin n) (c : ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (Sum.elim (fun j => if j = i then c else 1) (fun _ => c))

def boostS (i : Fin n) : Matrix ι ι ℝ :=
  Matrix.single (Sum.inl i) (Sum.inr 0) 1 + Matrix.single (Sum.inr 0) (Sum.inl i) 1

def boostMat (i : Fin n) (c s : ℝ) : Matrix ι ι ℝ := boostD i c + s • boostS i

def boostMatM (i : Fin n) (c s : ℝ) : M := boostMat i c s

theorem ofMatrix_symm_boostMatM (i : Fin n) (c s : ℝ) :
    MatrixSum.ofMatrix.symm (boostMatM i c s) = boostMat i c s := rfl

theorem boostD_mul_boostS (i : Fin n) (c : ℝ) : boostD i c * boostS i = c • boostS i := by
  rw [boostD, boostS, Matrix.mul_add, diagonal_mul_single, diagonal_mul_single]
  simp only [Sum.elim_inl, Sum.elim_inr, ite_true]
  rw [smul_add]

theorem boostS_mul_boostD (i : Fin n) (c : ℝ) : boostS i * boostD i c = c • boostS i := by
  rw [boostD, boostS, Matrix.add_mul, single_mul_diagonal, single_mul_diagonal]
  simp only [Sum.elim_inl, Sum.elim_inr, ite_true]
  rw [smul_add]

theorem boostS_sq (i : Fin n) :
    boostS i * boostS i =
      Matrix.single (Sum.inl i) (Sum.inl i) 1 + Matrix.single (Sum.inr 0) (Sum.inr 0) 1 := by
  rw [boostS, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.single_mul_single_same, Matrix.single_mul_single_same]
  rw [single_mul_single_of_ne (by exact Sum.inr_ne_inl), single_mul_single_of_ne (by exact Sum.inl_ne_inr)]
  simp

theorem boostD_sq (i : Fin n) (c : ℝ) :
    boostD i c * boostD i c =
      Matrix.diagonal (Sum.elim (fun j => if j = i then c * c else 1) (fun _ => c * c)) := by
  rw [boostD, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext a
  rcases a with a | a
  · by_cases h : a = i <;> simp [h]
  · simp []

theorem boostMat_mul (i : Fin n) (c t u : ℝ) :
    boostMat i c t * boostMat i c u =
      boostD i c * boostD i c + ((t + u) * c) • boostS i + (t * u) • (boostS i * boostS i) := by
  rw [boostMat, boostMat, add_mul, mul_add, mul_add]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, boostD_mul_boostS, boostS_mul_boostD]
  module

theorem boostMat_apply (i : Fin n) (c s : ℝ) (a b : ι) :
    boostMat i c s a b =
      (if a = b then Sum.elim (fun j => if j = i then c else 1) (fun _ => c) a else 0)
        + (if Sum.inl i = a ∧ Sum.inr 0 = b then s else 0)
        + (if Sum.inr 0 = a ∧ Sum.inl i = b then s else 0) := by
  rw [boostMat, boostD, boostS, Matrix.add_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.diagonal_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs <;> simp_all [smul_eq_mul] ; ring

theorem conjTranspose_boostD (i : Fin n) (c : ℝ) : (boostD i c)ᴴ = boostD i c := by
  rw [boostD, Matrix.diagonal_conjTranspose]
  apply congrArg Matrix.diagonal
  funext a
  simp [star_trivial]

theorem conjTranspose_boostS (i : Fin n) : (boostS i)ᴴ = boostS i := by
  rw [boostS, Matrix.conjTranspose_add, Matrix.conjTranspose, Matrix.conjTranspose]
  simp [Matrix.transpose_single, Matrix.map_single, add_comm]

theorem pmOneMat_mul_diagonal_mul_pmOneMat (d : ι → ℝ) :
    (pmOneMat : Matrix ι ι ℝ) * Matrix.diagonal d * pmOneMat = Matrix.diagonal d := by
  rw [pmOneMat_eq_diagonal]
  apply Matrix.ext
  intro a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    rcases a with a | a
    · simp [Sum.elim_inl]
    · simp [Sum.elim_inr]
  · simp

theorem pmOneMat_mul_boostD_mul_pmOneMat (i : Fin n) (c : ℝ) :
    (pmOneMat : Matrix ι ι ℝ) * boostD i c * pmOneMat = boostD i c :=
  pmOneMat_mul_diagonal_mul_pmOneMat _

theorem pmOneMat_mul_boostS_mul_pmOneMat (i : Fin n) :
    (pmOneMat : Matrix ι ι ℝ) * boostS i * pmOneMat = -boostS i := by
  rw [pmOneMat_eq_diagonal, boostS, Matrix.mul_add, add_mul]
  simp only [diagonal_mul_single, single_mul_diagonal, Matrix.smul_mul, smul_smul,
    Sum.elim_inl, Sum.elim_inr]
  rw [show (1 : ℝ) * -1 = -1 from by ring, show (-1 : ℝ) * 1 = -1 from by ring]
  rw [← smul_add, neg_one_smul]

theorem star_boostMat (i : Fin n) (c s : ℝ) :
    (pmOneMat : Matrix ι ι ℝ) * (boostMat i c s)ᴴ * pmOneMat = boostMat i c (-s) := by
  rw [boostMat, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, conjTranspose_boostD,
    conjTranspose_boostS, star_trivial]
  rw [Matrix.mul_add, add_mul, pmOneMat_mul_boostD_mul_pmOneMat, Matrix.mul_smul,
    Matrix.smul_mul, pmOneMat_mul_boostS_mul_pmOneMat]
  change boostD i c + s • (-boostS i) = boostD i c + (-s) • boostS i
  rw [smul_neg, ← neg_smul]

theorem boostD_sq_add_smul_boostS_sq (i : Fin n) {c s : ℝ} (h : c * c - s * s = 1) :
    boostD i c * boostD i c + (-(s * s)) • (boostS i * boostS i) = (1 : Matrix ι ι ℝ) := by
  rw [boostS_sq, boostD_sq]
  apply Matrix.ext
  intro a b
  rcases a with a | a <;> rcases b with b | b
  · by_cases hab : a = b
    · subst hab
      by_cases hai : i = a
      · subst hai
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.single_apply,
          Matrix.one_apply, smul_eq_mul, Sum.elim_inl,
          Sum.inr_ne_inl, ite_true, ite_false, and_self,
          mul_one, add_zero]
        linear_combination h
      · have hai' : ¬ a = i := fun hh => hai hh.symm
        have hai2 : ¬ (i = a ∧ i = a) := fun hh => hai hh.1
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.single_apply,
          Matrix.one_apply, smul_eq_mul, Sum.elim_inl, Sum.inl.injEq,
          Sum.inr_ne_inl, ite_true, ite_false, and_self,
          mul_zero, add_zero, hai, hai']
    · have hab2 : ¬ (i = a ∧ i = b) := fun ⟨h1, h2⟩ => hab (h1 ▸ h2)
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.single_apply,
        Matrix.one_apply, smul_eq_mul, Sum.elim_inl, Sum.inl.injEq,
        Sum.inr_ne_inl, ite_false, and_self,
        mul_zero, add_zero, hab, hab2]
  · have hb : b = 0 := Subsingleton.elim b 0
    subst hb
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.single_apply,
      Matrix.one_apply, smul_eq_mul, Sum.elim_inl, Sum.inl.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, ite_false, false_and, and_false,
      mul_zero, add_zero]
  · have ha : a = 0 := Subsingleton.elim a 0
    subst ha
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.single_apply,
      Matrix.one_apply, smul_eq_mul, Sum.elim_inr, Sum.inl.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, ite_false, false_and, and_false,
      mul_zero, add_zero]
  · have ha : a = 0 := Subsingleton.elim a 0
    have hb : b = 0 := Subsingleton.elim b 0
    subst ha; subst hb
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.single_apply,
      Matrix.one_apply, smul_eq_mul, Sum.elim_inr,
      Sum.inl_ne_inr, ite_true, ite_false, and_self,
      mul_one, zero_add]
    linear_combination h

theorem boostMat_mul_neg (i : Fin n) {c s : ℝ} (h : c * c - s * s = 1) :
    boostMat i c (-s) * boostMat i c s = (1 : Matrix ι ι ℝ) := by
  rw [boostMat_mul, show (-s + s) * c = 0 from by ring, zero_smul, add_zero,
    show -s * s = -(s * s) from by ring]
  exact boostD_sq_add_smul_boostS_sq i h

theorem boostMat_neg_mul (i : Fin n) {c s : ℝ} (h : c * c - s * s = 1) :
    boostMat i c s * boostMat i c (-s) = (1 : Matrix ι ι ℝ) := by
  rw [boostMat_mul, show (s + -s) * c = 0 from by ring, zero_smul, add_zero,
    show s * -s = -(s * s) from by ring]
  exact boostD_sq_add_smul_boostS_sq i h

theorem boostMat_mem (i : Fin n) {c s : ℝ} (h : c * c - s * s = 1) :
    boostMatM i c s ∈ unitary M := by
  rw [Unitary.mem_iff]
  constructor
  · change ((pmOneMat * (boostMat i c s)ᴴ * pmOneMat) * boostMat i c s : Matrix ι ι ℝ) = 1
    rw [star_boostMat]
    exact boostMat_mul_neg i h
  · change (boostMat i c s * (pmOneMat * (boostMat i c s)ᴴ * pmOneMat) : Matrix ι ι ℝ) = 1
    rw [star_boostMat]
    exact boostMat_neg_mul i h

theorem isDiagonal_of_central {z : Matrix ι ι ℝ}
    (hz : ∀ w : M, w ∈ unitary M → (MatrixSum.ofMatrix.symm w) * z = z * (MatrixSum.ofMatrix.symm w)) :
    z = Matrix.diagonal (fun a => z a a) := by
  apply Matrix.ext
  intro a b
  rw [Matrix.diagonal_apply]
  split_ifs with hab
  · subst hab; rfl
  · rcases a with a | a <;> rcases b with b | b
    · have hab' : b ≠ a := fun hh => hab (by rw [hh])
      have hc := hz (signMatM a) (signMat_mem a)
      have e := congrFun (congrFun hc (Sum.inl a)) (Sum.inl b)
      rw [ofMatrix_symm_signMatM] at e
      simp only [signMat, Matrix.diagonal_mul, Matrix.mul_diagonal, Sum.elim_inl, ite_true,
        ite_eq_right hab'] at e
      have : z (Sum.inl a) (Sum.inl b) = 0 := by linarith
      exact this
    · have hb0 : b = 0 := Subsingleton.elim b 0
      subst hb0
      have hc := hz (signMatM a) (signMat_mem a)
      have e := congrFun (congrFun hc (Sum.inl a)) (Sum.inr 0)
      rw [ofMatrix_symm_signMatM] at e
      simp only [signMat, Matrix.diagonal_mul, Matrix.mul_diagonal, Sum.elim_inl, Sum.elim_inr,
        ite_true] at e
      have : z (Sum.inl a) (Sum.inr 0) = 0 := by linarith
      exact this
    · have ha0 : a = 0 := Subsingleton.elim a 0
      subst ha0
      have hc := hz (signMatM b) (signMat_mem b)
      have e := congrFun (congrFun hc (Sum.inr 0)) (Sum.inl b)
      rw [ofMatrix_symm_signMatM] at e
      simp only [signMat, Matrix.diagonal_mul, Matrix.mul_diagonal, Sum.elim_inl, Sum.elim_inr,
        ite_true] at e
      have : z (Sum.inr 0) (Sum.inl b) = 0 := by linarith
      exact this
    · exact absurd (by rw [Subsingleton.elim a b] : (Sum.inr a : ι) = Sum.inr b) hab

theorem diag_eq_of_central {z : Matrix ι ι ℝ} {v : ι → ℝ} (i : Fin n)
    (hz : ∀ w : M, w ∈ unitary M → (MatrixSum.ofMatrix.symm w) * z = z * (MatrixSum.ofMatrix.symm w))
    (hzd : z = Matrix.diagonal v) :
    v (Sum.inl i) = v (Sum.inr 0) := by
  have h54 : (5 / 4 : ℝ) * (5 / 4) - (3 / 4 : ℝ) * (3 / 4) = 1 := by norm_num
  have hc := hz (boostMatM i (5/4) (3/4)) (boostMat_mem i h54)
  have e := congrFun (congrFun hc (Sum.inl i)) (Sum.inr 0)
  rw [ofMatrix_symm_boostMatM, hzd] at e
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at e
  have hb : boostMat i (5/4) (3/4) (Sum.inl i) (Sum.inr 0) = 3/4 := by
    rw [boostMat_apply]
    simp [Sum.inl_ne_inr, Sum.inr_ne_inl]
  rw [hb] at e
  have hne : (3/4 : ℝ) ≠ 0 := by norm_num
  have e' : v (Sum.inl i) * (3/4) = v (Sum.inr 0) * (3/4) := e.symm.trans (mul_comm _ _)
  exact mul_right_cancel₀ hne e'

theorem eq_one_or_neg_one_of_central (hn : 1 ≤ n) {z : M}
    (hzu : z ∈ unitary M)
    (hz : ∀ w : M, w ∈ unitary M → (MatrixSum.ofMatrix.symm w) * (MatrixSum.ofMatrix.symm z)
      = (MatrixSum.ofMatrix.symm z) * (MatrixSum.ofMatrix.symm w)) :
    z = 1 ∨ z = -1 := by
  set zM : Matrix ι ι ℝ := MatrixSum.ofMatrix.symm z with hzM
  have hz' : ∀ w : M, w ∈ unitary M → (MatrixSum.ofMatrix.symm w) * zM = zM * (MatrixSum.ofMatrix.symm w) := hz
  set v : ι → ℝ := fun a => zM a a with hv
  have hzd : zM = Matrix.diagonal v := isDiagonal_of_central hz'
  obtain ⟨i0⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set lam : ℝ := v (Sum.inr 0) with hlam
  have hvc : v = fun _ => lam := by
    funext a
    rcases a with a | a
    · exact diag_eq_of_central a hz' hzd
    · have : a = 0 := Subsingleton.elim a 0
      subst this
      rfl
  have hz1 : zM = lam • (1 : Matrix ι ι ℝ) := by
    rw [hzd, hvc]
    apply Matrix.ext
    intro a b
    simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hstar : (pmOneMat : Matrix ι ι ℝ) * zMᴴ * pmOneMat = lam • (1 : Matrix ι ι ℝ) := by
    rw [hz1, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, pmOneMat_mul_pmOneMat]
  have hu1 := (Unitary.mem_iff.mp hzu).1
  have hu1' : ((pmOneMat * zMᴴ * pmOneMat) * zM : Matrix ι ι ℝ) = 1 := hu1
  rw [hstar, hz1] at hu1'
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one] at hu1'
  have e := congrFun (congrFun hu1' (Sum.inl i0)) (Sum.inl i0)
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ite_true, mul_one] at e
  have hlam2 : lam ^ 2 = 1 := by rw [pow_two]; exact e
  rcases sq_eq_one_iff.mp hlam2 with h | h
  · left
    have hz1' : zM = (1 : Matrix ι ι ℝ) := by rw [hz1, h, one_smul]
    change z = 1
    exact hz1'
  · right
    have hz1' : zM = (-1 : Matrix ι ι ℝ) := by rw [hz1, h, neg_one_smul]
    change z = -1
    exact hz1'

theorem neg_one_mem_unitary : (-1 : M) ∈ unitary M := by
  rw [Unitary.mem_iff]
  simp [star_neg, star_one]

theorem neg_one_mem_center :
    (⟨-1, neg_one_mem_unitary⟩ : ↥(unitary M)) ∈ Subgroup.center ↥(unitary M) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  change ((g * ⟨-1, neg_one_mem_unitary⟩ : ↥(unitary M)) : M) =
    ((⟨-1, neg_one_mem_unitary⟩ * g : ↥(unitary M)) : M)
  rw [Submonoid.coe_mul, Submonoid.coe_mul]
  change (g : M) * (-1 : M) = (-1 : M) * (g : M)
  rw [mul_neg_one, neg_one_mul]

theorem center_coe_eq (hn : 1 ≤ n) {z : ↥(unitary M)} (hz : z ∈ Subgroup.center ↥(unitary M)) :
    (z : M) = 1 ∨ (z : M) = -1 := by
  rw [Subgroup.mem_center_iff] at hz
  have hM : ∀ w : M, w ∈ unitary M → (MatrixSum.ofMatrix.symm w) * (MatrixSum.ofMatrix.symm (z : M))
      = (MatrixSum.ofMatrix.symm (z : M)) * (MatrixSum.ofMatrix.symm w) := by
    intro w hw
    have e := hz ⟨w, hw⟩
    have e2 : ((⟨w, hw⟩ * z : ↥(unitary M)) : M) = ((z * ⟨w, hw⟩ : ↥(unitary M)) : M) :=
      congrArg _ e
    rw [Submonoid.coe_mul, Submonoid.coe_mul] at e2
    exact e2
  exact eq_one_or_neg_one_of_central hn z.2 hM

theorem center_finite (hn : 1 ≤ n) :
    (SetLike.coe (Subgroup.center ↥(unitary M)) : Set ↥(unitary M)).Finite := by
  have hsub : (SetLike.coe (Subgroup.center ↥(unitary M)) : Set ↥(unitary M)) ⊆
      (fun x : ↥(unitary M) => (x : M)) ⁻¹' {1, -1} := by
    intro z hz
    rw [SetLike.mem_coe] at hz
    rw [Subgroup.mem_center_iff] at hz
    have hM : ∀ w : M, w ∈ unitary M → (MatrixSum.ofMatrix.symm w) * (MatrixSum.ofMatrix.symm (z : M))
        = (MatrixSum.ofMatrix.symm (z : M)) * (MatrixSum.ofMatrix.symm w) := by
      intro w hw
      have e := hz ⟨w, hw⟩
      have e2 : ((⟨w, hw⟩ * z : ↥(unitary M)) : M) = ((z * ⟨w, hw⟩ : ↥(unitary M)) : M) :=
        congrArg _ e
      rw [Submonoid.coe_mul, Submonoid.coe_mul] at e2
      exact e2
    rcases eq_one_or_neg_one_of_central hn z.2 hM with hh | hh
    · left; exact hh
    · right; exact hh
  exact Set.Finite.preimage (fun x _ y _ h => Subtype.ext h)
    ((Set.finite_singleton (-1 : M)).insert 1) |>.subset hsub

theorem not_compactSpace_unitary (hn : 1 ≤ n) : ¬ CompactSpace ↥(unitary M) := by
  intro hcomp
  obtain ⟨i0⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hK : IsCompact (Set.univ : Set ↥(unitary M)) := isCompact_univ_iff.mpr hcomp
  set E : M → ℝ := (fun f : (ι → ι → ℝ) => f (Sum.inl i0) (Sum.inl i0)) ∘ MatrixSum.ofMatrix.symm
    with hEdef
  have hEc : Continuous E := by
    rw [hEdef]
    fun_prop
  have hcomp2 : IsCompact ((E ∘ (fun x : ↥(unitary M) => (x : M))) '' Set.univ) :=
    hK.image (hEc.comp continuous_subtype_val)
  obtain ⟨C, hC⟩ := hcomp2.isBounded.exists_norm_le
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 * (C + 1)) one_lt_two
  set a := (2 : ℝ) ^ k with ha
  set c := (a + a⁻¹) / 2 with hc
  set s := (a - a⁻¹) / 2 with hs
  have ha0 : a ≠ 0 := pow_ne_zero _ two_ne_zero
  have hcs : c * c - s * s = 1 := by
    have hcid : c * c - s * s = a * a⁻¹ := by rw [hc, hs]; ring
    rw [hcid, mul_inv_cancel₀ ha0]
  have hmem : boostMatM i0 c s ∈ unitary M := boostMat_mem i0 hcs
  have hCk : (E ∘ (fun x : ↥(unitary M) => (x : M))) ⟨boostMatM i0 c s, hmem⟩ ∈
      (E ∘ (fun x : ↥(unitary M) => (x : M))) '' Set.univ :=
    Set.mem_image_of_mem _ (Set.mem_univ _)
  have hle := hC _ hCk
  have hEval : (E ∘ (fun x : ↥(unitary M) => (x : M))) ⟨boostMatM i0 c s, hmem⟩ = c := by
    change (MatrixSum.ofMatrix.symm (boostMatM i0 c s)) (Sum.inl i0) (Sum.inl i0) = c
    rw [ofMatrix_symm_boostMatM, boostMat_apply]
    simp only [Sum.elim_inl, ite_true, Sum.inr_ne_inl, and_false,
      and_true, ite_false, add_zero]
  rw [hEval] at hle
  have hapos : 0 < a := pow_pos (by norm_num) _
  have hcpos : 0 < c := by rw [hc]; positivity
  rw [Real.norm_eq_abs, abs_of_pos hcpos] at hle
  have hbig : C < c := by
    have h1 : a / 2 > C + 1 := by linarith [hk]
    have h2 : a / 2 ≤ c := by rw [hc]; linarith [(inv_pos.mpr hapos).le]
    linarith
  linarith

theorem not_compactSpace_PO (hn : 1 ≤ n) : ¬ CompactSpace (PO n 1) := by
  intro hcomp
  have hK : IsCompact (Set.univ : Set (PO n 1)) := isCompact_univ_iff.mpr hcomp
  set q : ↥(unitary M) → PO n 1 := QuotientGroup.mk with hqdef
  have hqprop : IsProperMap q := by
    rw [isProperMap_iff_isClosedMap_and_compact_fibers]
    refine ⟨?_, ?_, ?_⟩
    · rw [hqdef]; exact QuotientGroup.continuous_mk
    · intro A hA
      rw [hqdef]
      have hqm : Topology.IsQuotientMap (QuotientGroup.mk : ↥(unitary M) → PO n 1) :=
        QuotientGroup.isOpenQuotientMap_mk.isQuotientMap
      rw [← hqm.isClosed_preimage]
      have hpre : (QuotientGroup.mk : ↥(unitary M) → PO n 1) ⁻¹'
            ((QuotientGroup.mk : ↥(unitary M) → PO n 1) '' A) =
          A ∪ (fun y : ↥(unitary M) => y * ⟨-1, neg_one_mem_unitary⟩) ⁻¹' A := by
        ext y
        constructor
        · intro hy
          obtain ⟨a, ha, hqy⟩ := hy
          rw [QuotientGroup.eq] at hqy
          rcases center_coe_eq hn hqy with hh | hh
          · have hay : a⁻¹ * y = 1 := Subtype.ext (by
              change ((a⁻¹ * y : ↥(unitary M)) : M) = 1
              exact hh)
            have := inv_mul_eq_one.mp hay
            left; rw [← this]; exact ha
          · have hay : a⁻¹ * y = ⟨-1, neg_one_mem_unitary⟩ := Subtype.ext (by
              change ((a⁻¹ * y : ↥(unitary M)) : M) = -1
              exact hh)
            have hya : y = a * ⟨-1, neg_one_mem_unitary⟩ := inv_mul_eq_iff_eq_mul.mp hay
            right
            have hz0sq : (⟨-1, neg_one_mem_unitary⟩ : ↥(unitary M)) * ⟨-1, neg_one_mem_unitary⟩
                = 1 := by
              apply Subtype.ext
              change ((⟨-1, neg_one_mem_unitary⟩ * ⟨-1, neg_one_mem_unitary⟩ : ↥(unitary M)) : M) = 1
              rw [Submonoid.coe_mul]
              change (-1 : M) * (-1 : M) = 1
              rw [neg_mul_neg, one_mul]
            change y * ⟨-1, neg_one_mem_unitary⟩ ∈ A
            rw [hya, mul_assoc, hz0sq, mul_one]
            exact ha
        · intro hy
          rcases hy with hy | hy
          · exact ⟨y, hy, rfl⟩
          · refine ⟨y * ⟨-1, neg_one_mem_unitary⟩, hy, ?_⟩
            rw [QuotientGroup.eq]
            have h1 : (y * ⟨-1, neg_one_mem_unitary⟩)⁻¹ * y =
                (⟨-1, neg_one_mem_unitary⟩ : ↥(unitary M))⁻¹ := by
              rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
            rw [h1]
            exact Subgroup.inv_mem _ (neg_one_mem_center (n := n))
      rw [hpre]
      exact hA.union (hA.preimage (continuous_mul_const _))
    · intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      have hsub : q ⁻¹' {QuotientGroup.mk x} ⊆ {x, x * ⟨-1, neg_one_mem_unitary⟩} := by
        intro y hy
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
        rw [QuotientGroup.eq] at hy
        rcases center_coe_eq hn hy with hh | hh
        · have h1 : y⁻¹ * x = 1 := Subtype.ext (by
            change ((y⁻¹ * x : ↥(unitary M)) : M) = 1
            exact hh)
          left
          exact inv_mul_eq_one.mp h1
        · have h1 : y⁻¹ * x = ⟨-1, neg_one_mem_unitary⟩ := Subtype.ext (by
            change ((y⁻¹ * x : ↥(unitary M)) : M) = -1
            exact hh)
          right
          have hx : x = y * ⟨-1, neg_one_mem_unitary⟩ := inv_mul_eq_iff_eq_mul.mp h1
          have hinv : (⟨-1, neg_one_mem_unitary⟩ : ↥(unitary M))⁻¹ = ⟨-1, neg_one_mem_unitary⟩ := by
            apply Subtype.ext
            change (star (-1 : M) : M) = -1
            rw [star_neg, star_one]
          have hy' : y = x * (⟨-1, neg_one_mem_unitary⟩)⁻¹ :=
            (eq_mul_inv_iff_mul_eq.mpr hx.symm)
          rw [hinv] at hy'
          exact hy'
      exact ((Set.finite_singleton _).insert _).subset hsub |>.isCompact
  have huniv : IsCompact (q ⁻¹' Set.univ) := hqprop.isCompact_preimage hK
  rw [Set.preimage_univ] at huniv
  exact not_compactSpace_unitary hn (isCompact_univ_iff.mp huniv)

theorem infinite_of_finite_covolume (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    [hfd : HasFundamentalDomain Γ (PO n 1)]
    (covol : covolume Γ (PO n 1) ≠ ⊤) : Infinite ↥Γ := by
  have hnc : NoncompactSpace (PO n 1) :=
    ⟨fun hc => not_compactSpace_PO hn (isCompact_univ_iff.mp hc)⟩
  have huniv : (volume : Measure (PO n 1)) Set.univ = ⊤ :=
    measure_univ_of_isMulLeftInvariant _
  by_contra hinf
  rw [not_infinite_iff_finite] at hinf
  set 𝓕 := hfd.ExistsIsFundamentalDomain.choose with h𝓕def
  have h𝓕 : IsFundamentalDomain Γ 𝓕 volume := hfd.ExistsIsFundamentalDomain.choose_spec
  have hvol : volume 𝓕 ≠ ⊤ := by
    have hcv : covolume Γ (PO n 1) = volume 𝓕 := by
      unfold MeasureTheory.covolume
      rw [dite_eq_left hfd]
    rw [hcv] at covol
    exact covol
  have : Finite ↥Γ := hinf
  let : Fintype ↥Γ := Fintype.ofFinite ↥Γ
  have h1 : (Set.univ : Set (PO n 1)) =ᵐ[volume] ⋃ γ : ↥Γ, γ • 𝓕 := h𝓕.iUnion_smul_ae_eq.symm
  have hle : (volume : Measure (PO n 1)) Set.univ ≤ Fintype.card ↥Γ • volume 𝓕 := by
    rw [measure_congr h1]
    calc (volume : Measure (PO n 1)) (⋃ γ : ↥Γ, γ • 𝓕) ≤ ∑' γ : ↥Γ, volume (γ • 𝓕) :=
        measure_iUnion_le _
      _ = ∑' γ : ↥Γ, volume 𝓕 := tsum_congr fun γ => MeasureTheory.measure_smul volume γ 𝓕
      _ = Fintype.card ↥Γ • volume 𝓕 := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ]
  have htop : (⊤ : ℝ≥0∞) ≤ Fintype.card ↥Γ • volume 𝓕 := huniv ▸ hle
  have hfin : Fintype.card ↥Γ • volume 𝓕 ≠ ⊤ := by
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hvol
  exact hfin (top_le_iff.mp htop)

theorem t3Space_PO (hn : 1 ≤ n) : T3Space (PO n 1) := by
  have : IsClosed (SetLike.coe (Subgroup.center ↥(unitary M)) : Set ↥(unitary M)) :=
    (center_finite hn).isClosed
  infer_instance

theorem t2Space_PO (hn : 1 ≤ n) : T2Space (PO n 1) := by
  have := t3Space_PO hn
  infer_instance

theorem isClosed_of_discrete (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) : IsClosed (SetLike.coe Γ) := by
  have : DiscreteTopology ↥Γ := SetLike.isDiscrete_iff_discreteTopology.mp disc
  have := t2Space_PO hn
  exact Subgroup.isClosed_of_discreteTopology

theorem properlyDiscontinuousSMul_of_discrete (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) : ProperlyDiscontinuousSMul Γ (PO n 1) := by
  have := t2Space_PO hn
  exact Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite Γ
    (Subgroup.tendsto_coe_cofinite_of_isDiscrete Γ disc)

theorem t2Space_orbitQuotient (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) :
    T2Space (Quotient (MulAction.orbitRel Γ (PO n 1))) := by
  have := t2Space_PO hn
  have := properlyDiscontinuousSMul_of_discrete hn Γ disc
  infer_instance

end DifferentialGeometry.ProjectiveOrthogonalGroup.Center

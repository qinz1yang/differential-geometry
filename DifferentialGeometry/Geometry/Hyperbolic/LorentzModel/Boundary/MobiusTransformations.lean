/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Topology
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Transitivity
import Mathlib.Algebra.Order.Ring.Star

open DifferentialGeometry.ProjectiveOrthogonalGroup
open Matrix

namespace DifferentialGeometry.MobiusBoundary

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.HyperbolicAction
open DifferentialGeometry.HyperbolicBoundary

variable {m : ℕ}

def normSq (x : Fin m → ℝ) : ℝ := ∑ i, x i ^ 2

theorem normSq_nonneg (x : Fin m → ℝ) : 0 ≤ normSq x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (x i)

theorem normSq_smul (c : ℝ) (x : Fin m → ℝ) : normSq (c • x) = c ^ 2 * normSq x := by
  unfold normSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.smul_apply, smul_eq_mul, mul_pow]

noncomputable def horoVec (x : Fin m → ℝ) : LorVec (m+1) :=
  Sum.elim (fun j : Fin (m+1) => Fin.lastCases (motive := fun _ => ℝ) ((normSq x - 1)/2) x j)
    (fun _ : Fin 1 => (normSq x + 1)/2)

theorem horoVec_castSucc (x : Fin m → ℝ) (i : Fin m) :
    horoVec x (Sum.inl i.castSucc) = x i := by
  simp only [horoVec, Sum.elim_inl, Fin.lastCases_castSucc]

theorem horoVec_last (x : Fin m → ℝ) :
    horoVec x (Sum.inl (Fin.last m)) = (normSq x - 1)/2 := by
  simp only [horoVec, Sum.elim_inl, Fin.lastCases_last]

theorem horoVec_time (x : Fin m → ℝ) :
    horoVec x (Sum.inr 0) = (normSq x + 1)/2 := by
  simp only [horoVec, Sum.elim_inr]

theorem tc_horoVec (x : Fin m → ℝ) : tc (horoVec x) = (normSq x + 1)/2 :=
  horoVec_time x

theorem tc_horoVec_pos (x : Fin m → ℝ) : 0 < tc (horoVec x) := by
  rw [tc_horoVec]
  have h := normSq_nonneg x
  positivity

theorem sdot_horoVec_self (x : Fin m → ℝ) :
    sdot (horoVec x) (horoVec x) = normSq x + ((normSq x - 1)/2)^2 := by
  rw [sdot, Fin.sum_univ_castSucc]
  have h1 : (∑ i : Fin m, horoVec x (Sum.inl i.castSucc) * horoVec x (Sum.inl i.castSucc))
      = normSq x := by
    rw [normSq]
    apply Finset.sum_congr rfl
    intro i _
    rw [horoVec_castSucc, ← pow_two]
  rw [h1, horoVec_last, ← pow_two]

theorem lorB_horoVec_self (x : Fin m → ℝ) : lorB (horoVec x) (horoVec x) = 0 := by
  rw [lorB, sdot_horoVec_self, tc_horoVec]
  ring

noncomputable def horo (x : Fin m → ℝ) : BoundaryH (m+1) :=
  ⟨boundaryRep (horoVec x), lorB_boundaryRep_self (lorB_horoVec_self x),
    tc_boundaryRep (ne_of_gt (tc_horoVec_pos x))⟩

theorem lorGrp_smul_horo_eq (g : LorGrp (m + 1)) {x y : Fin m → ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : matOf g *ᵥ horoVec x = c • horoVec y) :
    g • horo x = horo y := by
  apply BoundaryH.ext
  have htcx : tc (horoVec x) ≠ 0 := ne_of_gt (tc_horoVec_pos x)
  have htcy : tc (horoVec y) ≠ 0 := ne_of_gt (tc_horoVec_pos y)
  have hstep : matOf g *ᵥ (horo x).val = ((tc (horoVec x))⁻¹ * c) • horoVec y := by
    change matOf g *ᵥ boundaryRep (horoVec x) = _
    rw [show boundaryRep (horoVec x) = (tc (horoVec x))⁻¹ • horoVec x from rfl,
      Matrix.mulVec_smul, h, smul_smul]
  change boundaryRep (matOf g *ᵥ (horo x).val) = boundaryRep (horoVec y)
  rw [hstep, boundaryRep_smul _ (mul_ne_zero (inv_ne_zero htcx) hc)]

theorem po_smul_horo_eq (g : LorGrp (m + 1)) {x y : Fin m → ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : matOf g *ᵥ horoVec x = c • horoVec y) :
    (poBoundaryMulAction (Nat.le_add_left 1 m)).smul
      (QuotientGroup.mk' _ g : PO (m+1) 1) (horo x) = horo y := by
  have h1 : (poBoundaryMulAction (Nat.le_add_left 1 m)).smul
      (QuotientGroup.mk' _ g : PO (m+1) 1) (horo x) = g • horo x :=
    po_boundary_smul_mk (Nat.le_add_left 1 m) g (horo x)
  rw [h1]
  exact lorGrp_smul_horo_eq g hc h

theorem normSq_eq_zero {x : Fin m → ℝ} (h : normSq x = 0) : x = 0 := by
  funext i
  have h1 : (∑ j, x j ^ 2) = 0 := h
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)] at h1
  have h2 := h1 i (Finset.mem_univ i)
  rwa [sq_eq_zero_iff] at h2

theorem normSq_inv_smul (x : Fin m → ℝ) (hx : x ≠ 0) :
    normSq ((normSq x)⁻¹ • x) = (normSq x)⁻¹ := by
  rw [normSq_smul]
  have h : normSq x ≠ 0 := fun hh => hx (normSq_eq_zero hh)
  field_simp

noncomputable def dilateLor (lam : ℝ) (hlam : 0 < lam) : LorGrp (m+1) :=
  ⟨DifferentialGeometry.ProjectiveOrthogonalGroup.Center.boostMatM (Fin.last m) ((lam + lam⁻¹)/2) ((lam - lam⁻¹)/2),
    DifferentialGeometry.ProjectiveOrthogonalGroup.Center.boostMat_mem (Fin.last m) (by
      have h0 : lam ≠ 0 := ne_of_gt hlam
      field_simp; ring)⟩

theorem dilateLor_matOf (lam : ℝ) (hlam : 0 < lam) :
    matOf (dilateLor lam hlam)
      = DifferentialGeometry.ProjectiveOrthogonalGroup.Center.boostMat (Fin.last m) ((lam + lam⁻¹)/2) ((lam - lam⁻¹)/2) :=
  rfl

theorem boostMat_last_mulVec_horoVec (lam : ℝ) (hlam : lam ≠ 0) (x : Fin m → ℝ) :
    DifferentialGeometry.ProjectiveOrthogonalGroup.Center.boostMat (Fin.last m) ((lam + lam⁻¹)/2) ((lam - lam⁻¹)/2) *ᵥ horoVec x
      = lam⁻¹ • horoVec (lam • x) := by
  funext a
  rcases a with j | k
  · by_cases hj : j = Fin.last m
    · subst hj
      rw [HyperbolicTransitive.boostMat_mulVec_inl_self, horoVec_last, horoVec_time,
        Pi.smul_apply, smul_eq_mul, horoVec_last, normSq_smul]
      field_simp; ring
    · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      rw [HyperbolicTransitive.boostMat_mulVec_inl_ne _ _ _ _ (Fin.castSucc_ne_last i),
        horoVec_castSucc, Pi.smul_apply, smul_eq_mul, horoVec_castSucc, Pi.smul_apply,
        smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  · have hk0 : k = 0 := Subsingleton.elim k 0
    subst hk0
    rw [HyperbolicTransitive.boostMat_mulVec_inr, horoVec_last, horoVec_time,
      Pi.smul_apply, smul_eq_mul, horoVec_time, normSq_smul]
    field_simp; ring

theorem dilate_po_smul_horo (lam : ℝ) (hlam : 0 < lam) (x : Fin m → ℝ) :
    (poBoundaryMulAction (Nat.le_add_left 1 m)).smul
      (QuotientGroup.mk' _ (dilateLor lam hlam) : PO (m+1) 1) (horo x) = horo (lam • x) :=
  po_smul_horo_eq _ (inv_ne_zero (ne_of_gt hlam)) (by
    rw [dilateLor_matOf]
    exact boostMat_last_mulVec_horoVec lam (ne_of_gt hlam) x)

noncomputable def invertLor : LorGrp (m+1) :=
  ⟨DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMatM (Fin.last m), DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMat_mem (Fin.last m)⟩

theorem invertLor_matOf :
    matOf (invertLor : LorGrp (m+1)) = DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMat (Fin.last m) :=
  rfl

theorem signMat_mulVec_apply (k : Fin (m + 1)) (w : LorVec (m + 1)) (a : Fin (m + 1) ⊕ Fin 1) :
    (DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMat k *ᵥ w) a
      = (Sum.elim (fun j => if j = k then -1 else 1) (fun _ => (1 : ℝ)) a) * w a := by
  rw [DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMat, Matrix.mulVec_diagonal]

theorem signMat_last_mulVec_horoVec (x : Fin m → ℝ) (hx : x ≠ 0) :
    DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMat (Fin.last m) *ᵥ horoVec x
      = normSq x • horoVec ((normSq x)⁻¹ • x) := by
  have hu : normSq x ≠ 0 := fun hh => hx (normSq_eq_zero hh)
  funext a
  rcases a with j | k
  · by_cases hj : j = Fin.last m
    · subst hj
      rw [signMat_mulVec_apply]
      simp only [Sum.elim_inl, ite_true, horoVec_last]
      rw [Pi.smul_apply, smul_eq_mul, horoVec_last, normSq_inv_smul x hx]
      field_simp; ring
    · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      rw [signMat_mulVec_apply]
      simp only [Sum.elim_inl, Fin.castSucc_ne_last i, ite_false, one_mul, horoVec_castSucc]
      rw [Pi.smul_apply, smul_eq_mul, horoVec_castSucc, Pi.smul_apply, smul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
  · have hk0 : k = 0 := Subsingleton.elim k 0
    subst hk0
    rw [signMat_mulVec_apply]
    simp only [Sum.elim_inr, one_mul, horoVec_time]
    rw [Pi.smul_apply, smul_eq_mul, horoVec_time, normSq_inv_smul x hx,
      ← mul_div_assoc, mul_add, mul_inv_cancel₀ hu, mul_one]
    ring

theorem invert_po_smul_horo (x : Fin m → ℝ) (hx : x ≠ 0) :
    (poBoundaryMulAction (Nat.le_add_left 1 m)).smul
      (QuotientGroup.mk' _ invertLor : PO (m+1) 1) (horo x)
      = horo ((normSq x)⁻¹ • x) :=
  po_smul_horo_eq _ (fun hh => hx (normSq_eq_zero hh)) (by
    rw [invertLor_matOf]
    exact signMat_last_mulVec_horoVec x hx)

theorem conjTranspose_eq_transpose (M : Matrix (Fin (m + 1) ⊕ Fin 1) (Fin (m + 1) ⊕ Fin 1) ℝ) :
    Mᴴ = Mᵀ := by
  ext a b
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]

theorem single_dotProduct_mulVec_single
    (N : Matrix (Fin (m + 1) ⊕ Fin 1) (Fin (m + 1) ⊕ Fin 1) ℝ) (a b : Fin (m + 1) ⊕ Fin 1) :
    (Pi.single a (1:ℝ)) ⬝ᵥ (N *ᵥ (Pi.single b (1:ℝ))) = N a b := by
  rw [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply]

theorem lorB_mulVec (M : Matrix (Fin (m + 1) ⊕ Fin 1) (Fin (m + 1) ⊕ Fin 1) ℝ) (v w : LorVec (m + 1)) :
    v ⬝ᵥ ((Mᵀ * pmOneMat * M) *ᵥ w) = lorB (M *ᵥ v) (M *ᵥ w) := by
  have hsplit : (Mᵀ * pmOneMat * M) *ᵥ w = Mᵀ *ᵥ (pmOneMat *ᵥ (M *ᵥ w)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hsplit, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, ← lorB_eq_dotProduct]

theorem exists_lorGrp_of_lorB_preserving
    (M : Matrix (Fin (m + 1) ⊕ Fin 1) (Fin (m + 1) ⊕ Fin 1) ℝ)
    (h : ∀ v w : LorVec (m+1), lorB (M *ᵥ v) (M *ᵥ w) = lorB v w) :
    ∃ g : LorGrp (m+1), matOf g = M := by
  have key : Mᵀ * pmOneMat * M = pmOneMat := by
    apply Matrix.ext
    intro a b
    have hab := h (Pi.single a 1) (Pi.single b 1)
    rw [← lorB_mulVec, single_dotProduct_mulVec_single, lorB_eq_dotProduct,
      single_dotProduct_mulVec_single] at hab
    exact hab
  have hMT : Mᴴ = Mᵀ := conjTranspose_eq_transpose M
  have hQM : pmOneMat * Mᵀ * pmOneMat * M = 1 := by
    have he : pmOneMat * Mᵀ * pmOneMat * M = pmOneMat * (Mᵀ * pmOneMat * M) := by
      simp only [Matrix.mul_assoc]
    rw [he, key, pmOneMat_mul_pmOneMat]
  have hmem : (MatrixSum.ofMatrix M) ∈ unitary (MatrixSum (Fin (m+1)) (Fin 1) ℝ) := by
    rw [Unitary.mem_iff]
    constructor
    · change ((pmOneMat * Mᴴ * pmOneMat) * M
          : Matrix (Fin (m+1) ⊕ Fin 1) (Fin (m+1) ⊕ Fin 1) ℝ) = 1
      rw [hMT]
      exact hQM
    · change (M * (pmOneMat * Mᴴ * pmOneMat)
          : Matrix (Fin (m+1) ⊕ Fin 1) (Fin (m+1) ⊕ Fin 1) ℝ) = 1
      rw [hMT]
      exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hQM
  refine ⟨⟨MatrixSum.ofMatrix M, hmem⟩, ?_⟩
  rfl

inductive Idx3 (m : ℕ) where
  | horiz (i : Fin m) | axis | time

def toIdx3 : Fin (m+1) ⊕ Fin 1 → Idx3 m
  | Sum.inl j => Fin.lastCases (motive := fun _ => Idx3 m) Idx3.axis (fun i => Idx3.horiz i) j
  | Sum.inr _ => Idx3.time

theorem toIdx3_horiz (i : Fin m) : toIdx3 (Sum.inl i.castSucc) = Idx3.horiz i := by
  simp [toIdx3]

theorem toIdx3_axis : toIdx3 (Sum.inl (Fin.last m)) = Idx3.axis := by
  simp [toIdx3]

theorem toIdx3_time : toIdx3 (Sum.inr 0 : Fin (m+1) ⊕ Fin 1) = Idx3.time := rfl

theorem sum_split (g : Fin (m + 1) ⊕ Fin 1 → ℝ) :
    ∑ c, g c = (∑ i : Fin m, g (Sum.inl i.castSucc)) + g (Sum.inl (Fin.last m))
      + g (Sum.inr 0) := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_castSucc, Fin.sum_univ_one, add_assoc]

def matOfIdx3 (f : Idx3 m → Idx3 m → ℝ) :
    Matrix (Fin (m+1) ⊕ Fin 1) (Fin (m+1) ⊕ Fin 1) ℝ :=
  Matrix.of fun a c => f (toIdx3 a) (toIdx3 c)

theorem matOfIdx3_apply (f : Idx3 m → Idx3 m → ℝ) (a c : Fin (m + 1) ⊕ Fin 1) :
    matOfIdx3 f a c = f (toIdx3 a) (toIdx3 c) := rfl

theorem matOfIdx3_mulVec (f : Idx3 m → Idx3 m → ℝ) (v : LorVec (m + 1)) (a : Fin (m + 1) ⊕ Fin 1) :
    (matOfIdx3 f *ᵥ v) a
      = (∑ i : Fin m, f (toIdx3 a) (Idx3.horiz i) * v (Sum.inl i.castSucc))
        + f (toIdx3 a) Idx3.axis * v (Sum.inl (Fin.last m))
        + f (toIdx3 a) Idx3.time * v (Sum.inr 0) := by
  rw [Matrix.mulVec_apply_eq_sum, sum_split (fun c => matOfIdx3 f a c * v c)]
  simp only [matOfIdx3_apply, toIdx3_horiz, toIdx3_axis, toIdx3_time]

def rotBlock (A : Matrix (Fin m) (Fin m) ℝ) : Idx3 m → Idx3 m → ℝ
  | Idx3.horiz i, Idx3.horiz k => A i k
  | Idx3.axis, Idx3.axis => 1
  | Idx3.time, Idx3.time => 1
  | _, _ => 0

def rotMat (A : Matrix (Fin m) (Fin m) ℝ) := matOfIdx3 (rotBlock A)

def horizOf (v : LorVec (m + 1)) : Fin m → ℝ := fun i => v (Sum.inl i.castSucc)

theorem horizOf_horoVec (x : Fin m → ℝ) : horizOf (horoVec x) = x := by
  funext i
  exact horoVec_castSucc x i

theorem dotPreserving_of_orthogonal {A : Matrix (Fin m) (Fin m) ℝ} (hA : Aᵀ * A = 1)
    (x y : Fin m → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y := by
  have hvm : ∀ (z : Fin m → ℝ) (B : Matrix (Fin m) (Fin m) ℝ), z ᵥ* B = Bᵀ *ᵥ z := by
    intro z B
    conv_lhs => rw [← Matrix.transpose_transpose B]
    rw [Matrix.vecMul_transpose]
  have h1 : (A *ᵥ x) ᵥ* A = Aᵀ *ᵥ (A *ᵥ x) := hvm _ _
  rw [Matrix.dotProduct_mulVec, h1, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]

theorem normSq_eq_dotProduct (x : Fin m → ℝ) : normSq x = x ⬝ᵥ x := by
  simp [normSq, dotProduct, pow_two]

theorem normSq_mulVec_orthogonal {A : Matrix (Fin m) (Fin m) ℝ} (hA : Aᵀ * A = 1)
    (x : Fin m → ℝ) :
    normSq (A *ᵥ x) = normSq x := by
  simp only [normSq_eq_dotProduct]
  exact dotPreserving_of_orthogonal hA x x

theorem rotMat_mulVec_horiz (A : Matrix (Fin m) (Fin m) ℝ) (v : LorVec (m + 1)) (i : Fin m) :
    (rotMat A *ᵥ v) (Sum.inl i.castSucc) = (A *ᵥ horizOf v) i := by
  rw [rotMat, matOfIdx3_mulVec, toIdx3_horiz]
  simp only [rotBlock, zero_mul, add_zero]
  rw [Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  rfl

theorem rotMat_mulVec_axis (A : Matrix (Fin m) (Fin m) ℝ) (v : LorVec (m + 1)) :
    (rotMat A *ᵥ v) (Sum.inl (Fin.last m)) = v (Sum.inl (Fin.last m)) := by
  rw [rotMat, matOfIdx3_mulVec, toIdx3_axis]
  simp [rotBlock]

theorem rotMat_mulVec_time (A : Matrix (Fin m) (Fin m) ℝ) (v : LorVec (m + 1)) :
    (rotMat A *ᵥ v) (Sum.inr 0) = v (Sum.inr 0) := by
  rw [rotMat, matOfIdx3_mulVec, toIdx3_time]
  simp [rotBlock]

theorem lorB_rotMat {A : Matrix (Fin m) (Fin m) ℝ} (hA : Aᵀ * A = 1) (v w : LorVec (m + 1)) :
    lorB (rotMat A *ᵥ v) (rotMat A *ᵥ w) = lorB v w := by
  have htv : tc (rotMat A *ᵥ v) = tc v := rotMat_mulVec_time A v
  have htw : tc (rotMat A *ᵥ w) = tc w := rotMat_mulVec_time A w
  have hsum : (∑ i : Fin m, (rotMat A *ᵥ v) (Sum.inl i.castSucc) * (rotMat A *ᵥ w) (Sum.inl i.castSucc))
      = ∑ i : Fin m, v (Sum.inl i.castSucc) * w (Sum.inl i.castSucc) := by
    have hdot : (∑ i : Fin m, (rotMat A *ᵥ v) (Sum.inl i.castSucc) * (rotMat A *ᵥ w) (Sum.inl i.castSucc))
        = (A *ᵥ horizOf v) ⬝ᵥ (A *ᵥ horizOf w) := by
      simp only [rotMat_mulVec_horiz]
      rfl
    rw [hdot, dotPreserving_of_orthogonal hA]
    rfl
  have hsdot : sdot (rotMat A *ᵥ v) (rotMat A *ᵥ w) = sdot v w := by
    rw [sdot, sdot, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, rotMat_mulVec_axis,
      rotMat_mulVec_axis, hsum]
  rw [lorB, lorB, hsdot, htv, htw]

noncomputable def rotLor {A : Matrix (Fin m) (Fin m) ℝ} (hA : Aᵀ * A = 1) : LorGrp (m+1) :=
  (exists_lorGrp_of_lorB_preserving (rotMat A) (lorB_rotMat hA)).choose

theorem rotLor_matOf {A : Matrix (Fin m) (Fin m) ℝ} (hA : Aᵀ * A = 1) :
    matOf (rotLor hA) = rotMat A :=
  (exists_lorGrp_of_lorB_preserving (rotMat A) (lorB_rotMat hA)).choose_spec

theorem rotMat_horoVec {A : Matrix (Fin m) (Fin m) ℝ} (hA : Aᵀ * A = 1) (x : Fin m → ℝ) :
    rotMat A *ᵥ horoVec x = horoVec (A *ᵥ x) := by
  funext a
  rcases a with j | k
  · by_cases hj : j = Fin.last m
    · subst hj
      rw [rotMat_mulVec_axis, horoVec_last, horoVec_last, normSq_mulVec_orthogonal hA]
    · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      rw [rotMat_mulVec_horiz, horizOf_horoVec, horoVec_castSucc]
  · have hk0 : k = 0 := Subsingleton.elim k 0
    subst hk0
    rw [rotMat_mulVec_time, horoVec_time, horoVec_time, normSq_mulVec_orthogonal hA]

theorem rot_po_smul_horo {A : Matrix (Fin m) (Fin m) ℝ} (hA : Aᵀ * A = 1) (x : Fin m → ℝ) :
    (poBoundaryMulAction (Nat.le_add_left 1 m)).smul
      (QuotientGroup.mk' _ (rotLor hA) : PO (m+1) 1) (horo x) = horo (A *ᵥ x) :=
  po_smul_horo_eq _ one_ne_zero (by
    rw [rotLor_matOf, rotMat_horoVec hA x, one_smul])

def dotB (b x : Fin m → ℝ) : ℝ := ∑ i, b i * x i

theorem dotB_comm (b x : Fin m → ℝ) : dotB b x = dotB x b := by
  simp [dotB, mul_comm]

theorem normSq_add (x b : Fin m → ℝ) :
    normSq (x + b) = normSq x + 2 * dotB b x + normSq b := by
  have hexp : ∀ i : Fin m, (x i + b i)^2 = x i^2 + 2 * (b i * x i) + b i^2 := fun i => by ring
  simp only [normSq, dotB, Pi.add_apply]
  rw [Finset.sum_congr rfl (fun i _ => hexp i)]
  simp [Finset.sum_add_distrib, Finset.mul_sum]

theorem sum_horiz_id (v : LorVec (m + 1)) (i : Fin m) :
    (∑ k : Fin m, (if i = k then (1:ℝ) else 0) * v (Sum.inl k.castSucc))
      = v (Sum.inl i.castSucc) := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    rw [ite_eq_right (fun h => hki h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

noncomputable def transBlock (b : Fin m → ℝ) : Idx3 m → Idx3 m → ℝ
  | Idx3.horiz i, Idx3.horiz k => if i = k then 1 else 0
  | Idx3.horiz i, Idx3.axis => -b i
  | Idx3.horiz i, Idx3.time => b i
  | Idx3.axis, Idx3.horiz k => b k
  | Idx3.axis, Idx3.axis => 1 - normSq b / 2
  | Idx3.axis, Idx3.time => normSq b / 2
  | Idx3.time, Idx3.horiz k => b k
  | Idx3.time, Idx3.axis => -normSq b / 2
  | Idx3.time, Idx3.time => 1 + normSq b / 2

noncomputable def transMat (b : Fin m → ℝ) := matOfIdx3 (transBlock b)

theorem transMat_mulVec_horiz (b : Fin m → ℝ) (v : LorVec (m + 1)) (i : Fin m) :
    (transMat b *ᵥ v) (Sum.inl i.castSucc)
      = v (Sum.inl i.castSucc) + b i * (v (Sum.inr 0) - v (Sum.inl (Fin.last m))) := by
  rw [transMat, matOfIdx3_mulVec, toIdx3_horiz]
  simp only [transBlock]
  rw [sum_horiz_id]
  ring

theorem transMat_mulVec_axis (b : Fin m → ℝ) (v : LorVec (m + 1)) :
    (transMat b *ᵥ v) (Sum.inl (Fin.last m))
      = dotB b (horizOf v) + (normSq b / 2) * (v (Sum.inr 0) - v (Sum.inl (Fin.last m)))
        + v (Sum.inl (Fin.last m)) := by
  rw [transMat, matOfIdx3_mulVec, toIdx3_axis]
  simp only [transBlock]
  rw [show (∑ k : Fin m, b k * v (Sum.inl k.castSucc)) = dotB b (horizOf v) from rfl]
  ring

theorem transMat_mulVec_time (b : Fin m → ℝ) (v : LorVec (m + 1)) :
    (transMat b *ᵥ v) (Sum.inr 0)
      = dotB b (horizOf v) + (normSq b / 2) * (v (Sum.inr 0) - v (Sum.inl (Fin.last m)))
        + v (Sum.inr 0) := by
  rw [transMat, matOfIdx3_mulVec, toIdx3_time]
  simp only [transBlock]
  rw [show (∑ k : Fin m, b k * v (Sum.inl k.castSucc)) = dotB b (horizOf v) from rfl]
  ring

theorem sum_horiz_trans (b v w : Fin m → ℝ) (dv dw : ℝ) :
    (∑ i, (v i + b i * dv) * (w i + b i * dw))
      = (∑ i, v i * w i) + dv * (∑ i, b i * w i) + dw * (∑ i, b i * v i)
        + dv * dw * normSq b := by
  have hexp : ∀ i : Fin m, (v i + b i * dv) * (w i + b i * dw)
      = v i * w i + dv * (b i * w i) + dw * (b i * v i) + (dv * dw) * (b i)^2 :=
    fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => hexp i)]
  simp [Finset.sum_add_distrib, Finset.mul_sum, normSq]

theorem lorB_transMat (b : Fin m → ℝ) (v w : LorVec (m + 1)) :
    lorB (transMat b *ᵥ v) (transMat b *ᵥ w) = lorB v w := by
  have hpt : ∀ i : Fin m, (transMat b *ᵥ v) (Sum.inl i.castSucc) * (transMat b *ᵥ w) (Sum.inl i.castSucc)
      = (horizOf v i + b i * (v (Sum.inr 0) - v (Sum.inl (Fin.last m))))
        * (horizOf w i + b i * (w (Sum.inr 0) - w (Sum.inl (Fin.last m)))) := by
    intro i
    rw [transMat_mulVec_horiz, transMat_mulVec_horiz]
    rfl
  rw [lorB, lorB, sdot, sdot, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  rw [sum_horiz_trans]
  rw [transMat_mulVec_axis, transMat_mulVec_axis]
  rw [show tc (transMat b *ᵥ v) = (transMat b *ᵥ v) (Sum.inr 0) from rfl,
    show tc (transMat b *ᵥ w) = (transMat b *ᵥ w) (Sum.inr 0) from rfl,
    transMat_mulVec_time, transMat_mulVec_time,
    show tc v = v (Sum.inr 0) from rfl, show tc w = w (Sum.inr 0) from rfl]
  simp only [dotB, horizOf]
  ring

noncomputable def transLor (b : Fin m → ℝ) : LorGrp (m+1) :=
  (exists_lorGrp_of_lorB_preserving (transMat b) (lorB_transMat b)).choose

theorem transLor_matOf (b : Fin m → ℝ) : matOf (transLor b) = transMat b :=
  (exists_lorGrp_of_lorB_preserving (transMat b) (lorB_transMat b)).choose_spec

theorem transMat_horoVec (b : Fin m → ℝ) (x : Fin m → ℝ) :
    transMat b *ᵥ horoVec x = horoVec (x + b) := by
  funext a
  rcases a with j | k
  · by_cases hj : j = Fin.last m
    · subst hj
      simp only [transMat_mulVec_axis, horizOf_horoVec, horoVec_time, horoVec_last, normSq_add]
      ring
    · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      simp only [transMat_mulVec_horiz, horoVec_castSucc, horoVec_time, horoVec_last,
        Pi.add_apply]
      ring
  · have hk0 : k = 0 := Subsingleton.elim k 0
    subst hk0
    simp only [transMat_mulVec_time, horizOf_horoVec, horoVec_time, horoVec_last, normSq_add]
    ring

theorem trans_po_smul_horo (b : Fin m → ℝ) (x : Fin m → ℝ) :
    (poBoundaryMulAction (Nat.le_add_left 1 m)).smul
      (QuotientGroup.mk' _ (transLor b) : PO (m+1) 1) (horo x) = horo (x + b) :=
  po_smul_horo_eq _ one_ne_zero (by
    rw [transLor_matOf, transMat_horoVec, one_smul])

theorem po_smul_mul (g₁ g₂ : PO (m + 1) 1) (v : BoundaryH (m + 1)) :
    (poBoundaryMulAction (Nat.le_add_left 1 m)).smul (g₁ * g₂) v
      = (poBoundaryMulAction (Nat.le_add_left 1 m)).smul g₁
          ((poBoundaryMulAction (Nat.le_add_left 1 m)).smul g₂ v) :=
  (poBoundaryMulAction (Nat.le_add_left 1 m)).mul_smul g₁ g₂ v

def RealizedByPo (F : (Fin m → ℝ) → (Fin m → ℝ)) : Prop :=
  ∃ g : PO (m+1) 1, ∀ x : Fin m → ℝ,
    (poBoundaryMulAction (Nat.le_add_left 1 m)).smul g (horo x) = horo (F x)

theorem RealizedByPo.comp {F G : (Fin m → ℝ) → (Fin m → ℝ)}
    (hF : RealizedByPo F) (hG : RealizedByPo G) : RealizedByPo (F ∘ G) := by
  obtain ⟨gF, hgF⟩ := hF
  obtain ⟨gG, hgG⟩ := hG
  refine ⟨gF * gG, fun x => ?_⟩
  rw [po_smul_mul, hgG, hgF]
  rfl

theorem realizedByPo_translation (t : Fin m → ℝ) : RealizedByPo (fun z : Fin m → ℝ => z + t) :=
  ⟨QuotientGroup.mk' _ (transLor t), fun x => trans_po_smul_horo t x⟩

theorem realizedByPo_dilation (c : ℝ) (hc : 0 < c) : RealizedByPo (fun z : Fin m → ℝ => c • z) :=
  ⟨QuotientGroup.mk' _ (dilateLor c hc), fun x => dilate_po_smul_horo c hc x⟩

theorem realizedByPo_rotation {A : Matrix (Fin m) (Fin m) ℝ} (hA : Aᵀ * A = 1) :
    RealizedByPo (fun z : Fin m → ℝ => A *ᵥ z) :=
  ⟨QuotientGroup.mk' _ (rotLor hA), fun x => rot_po_smul_horo hA x⟩

theorem RealizedByPo.congr {F G : (Fin m → ℝ) → (Fin m → ℝ)} (h : ∀ x, F x = G x)
    (hF : RealizedByPo F) : RealizedByPo G := by
  obtain ⟨g, hg⟩ := hF
  exact ⟨g, fun x => by rw [← h x]; exact hg x⟩

theorem realizedByPo_similarity {A : Matrix (Fin m) (Fin m) ℝ} (hA : Aᵀ * A = 1)
    (c : ℝ) (hc : 0 < c) (t : Fin m → ℝ) :
    RealizedByPo (fun z : Fin m → ℝ => c • (A *ᵥ z) + t) :=
  RealizedByPo.congr (fun _ => rfl)
    ((realizedByPo_translation t).comp
      ((realizedByPo_dilation c hc).comp (realizedByPo_rotation hA)))

noncomputable def inversionAbout (x₀ z : Fin m → ℝ) : Fin m → ℝ :=
  (normSq (z - x₀))⁻¹ • (z - x₀) + x₀

theorem inversionAbout_po_smul_horo (x₀ x : Fin m → ℝ) (hx : x ≠ x₀) :
    (poBoundaryMulAction (Nat.le_add_left 1 m)).smul
      (QuotientGroup.mk' _ (transLor x₀) * QuotientGroup.mk' _ invertLor
        * QuotientGroup.mk' _ (transLor (-x₀))) (horo x)
      = horo (inversionAbout x₀ x) := by
  have hxx : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  rw [po_smul_mul, po_smul_mul, trans_po_smul_horo]
  rw [show x + -x₀ = x - x₀ from rfl, invert_po_smul_horo (x - x₀) hxx,
    trans_po_smul_horo]
  rfl

theorem realizedByPo_similarity_comp_inversion {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : Aᵀ * A = 1) (c : ℝ) (hc : 0 < c) (t x₀ : Fin m → ℝ) (x : Fin m → ℝ) (hx : x ≠ x₀) :
    (poBoundaryMulAction (Nat.le_add_left 1 m)).smul
      (QuotientGroup.mk' _ (transLor t) * QuotientGroup.mk' _ (dilateLor c hc)
        * QuotientGroup.mk' _ (rotLor hA) * QuotientGroup.mk' _ (transLor x₀)
        * QuotientGroup.mk' _ invertLor * QuotientGroup.mk' _ (transLor (-x₀)))
      (horo x)
      = horo (c • (A *ᵥ (inversionAbout x₀ x)) + t) := by
  have hxx : x + -x₀ ≠ 0 := by
    rw [show x + -x₀ = x - x₀ from rfl]
    exact sub_ne_zero.mpr hx
  rw [po_smul_mul, po_smul_mul, po_smul_mul, po_smul_mul, po_smul_mul]
  rw [trans_po_smul_horo, invert_po_smul_horo _ hxx, trans_po_smul_horo,
    rot_po_smul_horo, dilate_po_smul_horo, trans_po_smul_horo]
  rfl

noncomputable def ptInfty : BoundaryH (m+1) := nullUpB (Fin.last m)

theorem ptInfty_val_last : (ptInfty : BoundaryH (m+1)).val (Sum.inl (Fin.last m)) = 1 :=
  nullUp_inl_self _

theorem ptInfty_val_castSucc (i : Fin m) :
    (ptInfty : BoundaryH (m+1)).val (Sum.inl i.castSucc) = 0 :=
  nullUp_inl_of_ne (Fin.castSucc_ne_last i)

theorem ptInfty_val_time : (ptInfty : BoundaryH (m+1)).val (Sum.inr 0) = 1 :=
  nullUp_inr _

theorem sdot_self_of_boundary (v : BoundaryH (m + 1)) : sdot v.val v.val = 1 := by
  have h := v.is_null
  rw [lorB, v.tc_eq] at h
  linarith

theorem sum_sq_horizontal (v : BoundaryH (m + 1)) :
    (∑ i : Fin m, (v.val (Sum.inl i.castSucc))^2)
      = 1 - (v.val (Sum.inl (Fin.last m)))^2 := by
  have h := sdot_self_of_boundary v
  rw [sdot, Fin.sum_univ_castSucc] at h
  have h2 : (∑ i : Fin m, v.val (Sum.inl i.castSucc) * v.val (Sum.inl i.castSucc))
      = ∑ i : Fin m, (v.val (Sum.inl i.castSucc))^2 := by
    apply Finset.sum_congr rfl; intro i _; rw [pow_two]
  rw [h2] at h
  have h3 : v.val (Sum.inl (Fin.last m)) * v.val (Sum.inl (Fin.last m))
      = (v.val (Sum.inl (Fin.last m)))^2 := by rw [pow_two]
  rw [h3] at h
  linarith

theorem eq_ptInfty_of_axis_eq_one (v : BoundaryH (m + 1))
    (hσ : v.val (Sum.inl (Fin.last m)) = 1) : v = ptInfty := by
  apply BoundaryH.ext
  funext a
  rcases a with j | k
  · by_cases hj : j = Fin.last m
    · subst hj; rw [hσ, ptInfty_val_last]
    · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      have hsum := sum_sq_horizontal v
      rw [hσ] at hsum
      have h0 : (∑ k : Fin m, (v.val (Sum.inl k.castSucc))^2) = 0 := by linarith
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg _)] at h0
      have hii := h0 i (Finset.mem_univ i)
      rw [sq_eq_zero_iff] at hii
      rw [hii, ptInfty_val_castSucc]
  · have hk0 : k = 0 := Subsingleton.elim k 0
    subst hk0
    rw [show v.val (Sum.inr 0) = 1 from v.tc_eq, ptInfty_val_time]

theorem exists_horo_eq_of_ne_ptInfty (v : BoundaryH (m + 1)) (hv : v ≠ ptInfty) :
    ∃ x : Fin m → ℝ, horo x = v := by
  have hσ : v.val (Sum.inl (Fin.last m)) ≠ 1 := fun h => hv (eq_ptInfty_of_axis_eq_one v h)
  set σ := v.val (Sum.inl (Fin.last m)) with hσdef
  have h1σ : (1:ℝ) - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
  have hnormsq : normSq (fun i => v.val (Sum.inl i.castSucc)/(1 - σ)) = (1 + σ)/(1 - σ) := by
    have hsum := sum_sq_horizontal v
    have hent : ∀ i : Fin m, (v.val (Sum.inl i.castSucc)/(1-σ))^2
        = (v.val (Sum.inl i.castSucc))^2/(1-σ)^2 := fun i => by rw [div_pow]
    unfold normSq
    rw [Finset.sum_congr rfl (fun i _ => hent i), ← Finset.sum_div, hsum]
    field_simp [h1σ]
    ring
  refine ⟨fun i => v.val (Sum.inl i.castSucc)/(1 - σ), ?_⟩
  apply BoundaryH.ext
  funext a
  have hTc : tc (horoVec (fun i => v.val (Sum.inl i.castSucc)/(1 - σ))) ≠ 0 :=
    ne_of_gt (tc_horoVec_pos _)
  rw [show (horo _).val = boundaryRep (horoVec _) from rfl]
  rw [boundaryRep]
  rcases a with j | k
  · by_cases hj : j = Fin.last m
    · subst hj
      rw [Pi.smul_apply, smul_eq_mul, horoVec_last, tc_horoVec, hnormsq]
      field_simp [h1σ]
      ring
    · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      rw [Pi.smul_apply, smul_eq_mul, horoVec_castSucc, tc_horoVec, hnormsq]
      field_simp [h1σ]
      ring
  · have hk0 : k = 0 := Subsingleton.elim k 0
    subst hk0
    rw [Pi.smul_apply, smul_eq_mul, horoVec_time, ← tc_horoVec, inv_mul_cancel₀ hTc,
      show v.val (Sum.inr 0) = 1 from v.tc_eq]

theorem horo_ne_ptInfty (x : Fin m → ℝ) : horo x ≠ ptInfty := by
  intro h
  have h1 : (horo x).val (Sum.inl (Fin.last m)) = 1 := by rw [h]; exact ptInfty_val_last
  have h2 : (horo x).val (Sum.inl (Fin.last m)) = (normSq x - 1)/(normSq x + 1) := by
    change boundaryRep (horoVec x) (Sum.inl (Fin.last m)) = _
    rw [boundaryRep, Pi.smul_apply, smul_eq_mul, horoVec_last, tc_horoVec]
    field_simp
  rw [h2] at h1
  have hpos : normSq x + 1 ≠ 0 := by
    have := normSq_nonneg x
    positivity
  field_simp at h1
  linarith

theorem tendsto_axis_ratio :
    Filter.Tendsto (fun u : ℝ => (u - 1)/(u + 1)) Filter.atTop (nhds 1) := by
  have h1 : Filter.Tendsto (fun u : ℝ => u + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id
  have h2 : Filter.Tendsto (fun u : ℝ => (u + 1)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp h1
  have h3 : Filter.Tendsto (fun u : ℝ => 1 - 2 * (u + 1)⁻¹) Filter.atTop (nhds (1 - 2 * 0)) :=
    Filter.Tendsto.sub tendsto_const_nhds (h2.const_mul 2)
  rw [mul_zero, sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with u hu
  have hu1 : u + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem tendsto_two_mul_inv_sqrt :
    Filter.Tendsto (fun u : ℝ => 2 * (Real.sqrt u)⁻¹) Filter.atTop (nhds 0) := by
  have h := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul (2:ℝ)
  rwa [mul_zero] at h

theorem abs_horiz_le_sqrt_normSq (x : Fin m → ℝ) (i : Fin m) :
    |x i| ≤ Real.sqrt (normSq x) := by
  apply Real.abs_le_sqrt
  have h : (∑ j, x j ^ 2) ≥ x i ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  exact h

theorem horo_val_castSucc (x : Fin m → ℝ) (i : Fin m) :
    (horo x).val (Sum.inl i.castSucc) = 2 * x i / (normSq x + 1) := by
  rw [show (horo x).val = boundaryRep (horoVec x) from rfl, boundaryRep, Pi.smul_apply,
    smul_eq_mul, horoVec_castSucc, tc_horoVec, inv_div, div_mul_eq_mul_div₀]

theorem horo_val_last (x : Fin m → ℝ) :
    (horo x).val (Sum.inl (Fin.last m)) = (normSq x - 1)/(normSq x + 1) := by
  rw [show (horo x).val = boundaryRep (horoVec x) from rfl, boundaryRep, Pi.smul_apply,
    smul_eq_mul, horoVec_last, tc_horoVec]
  have hpos : (0:ℝ) < normSq x + 1 := by have h := normSq_nonneg x; linarith
  field_simp

theorem horo_val_time (x : Fin m → ℝ) :
    (horo x).val (Sum.inr 0) = 1 := by
  rw [show (horo x).val = boundaryRep (horoVec x) from rfl, boundaryRep, Pi.smul_apply,
    smul_eq_mul]
  exact inv_mul_cancel₀ (ne_of_gt (tc_horoVec_pos x))

noncomputable def horoSeq (hm : 1 ≤ m) (k : ℕ) : Fin m → ℝ :=
  fun i => if i = ⟨0, hm⟩ then (k : ℝ) + 1 else 0

theorem horoSeq_normSq (hm : 1 ≤ m) (k : ℕ) :
    normSq (horoSeq hm k) = ((k : ℝ) + 1)^2 := by
  have hrs : normSq (horoSeq hm k) = ∑ i : Fin m, (horoSeq hm k i)^2 := rfl
  rw [hrs, Finset.sum_eq_single ⟨0, hm⟩]
  · simp [horoSeq]
  · intro j _ hj
    have h0 : horoSeq hm k j = 0 := ite_eq_right hj
    rw [h0]
    norm_num
  · intro habs
    exact absurd (Finset.mem_univ _) habs

theorem horoSeq_normSq_pos (hm : 1 ≤ m) (k : ℕ) : 0 < normSq (horoSeq hm k) := by
  rw [horoSeq_normSq]
  positivity

theorem tendsto_horoSeq_normSq (hm : 1 ≤ m) :
    Filter.Tendsto (fun k : ℕ => normSq (horoSeq hm k)) Filter.atTop Filter.atTop := by
  simp only [horoSeq_normSq hm]
  have h2 : Filter.Tendsto (fun k : ℕ => (k : ℝ) + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun k => le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  exact (Filter.tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp h2

theorem abs_two_mul_div_add_one_le (u a : ℝ) (hu : 0 < u) (ha : |a| ≤ Real.sqrt u) :
    |2 * a / (u + 1)| ≤ 2 * (Real.sqrt u)⁻¹ := by
  have hu1 : (0:ℝ) < u + 1 := by linarith
  have hsu : (0:ℝ) ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hsqrt_pos : (0:ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu
  have h2 : |2 * a / (u + 1)| = 2 * |a| / (u + 1) := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hu1]
  rw [h2, ← div_eq_mul_inv, div_le_div_iff₀ hu1 hsqrt_pos]
  have hmul : |a| * Real.sqrt u ≤ Real.sqrt u * Real.sqrt u :=
    mul_le_mul_of_nonneg_right ha hsu
  have key : 2 * |a| * Real.sqrt u ≤ 2 * Real.sqrt u * Real.sqrt u := by
    calc 2 * |a| * Real.sqrt u = 2 * (|a| * Real.sqrt u) := by ring
      _ ≤ 2 * (Real.sqrt u * Real.sqrt u) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 2 * Real.sqrt u * Real.sqrt u := by ring
  calc 2 * |a| * Real.sqrt u ≤ 2 * Real.sqrt u * Real.sqrt u := key
    _ = 2 * u := by rw [mul_assoc, Real.mul_self_sqrt (le_of_lt hu)]
    _ ≤ 2 * (u + 1) := by linarith

theorem tendsto_horiz_horoSeq (hm : 1 ≤ m) (i : Fin m) :
    Filter.Tendsto (fun k : ℕ => 2 * horoSeq hm k i / (normSq (horoSeq hm k) + 1))
      Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm (fun k => ?_)
    (tendsto_two_mul_inv_sqrt.comp (tendsto_horoSeq_normSq hm))
  rw [Real.norm_eq_abs]
  exact abs_two_mul_div_add_one_le _ _ (horoSeq_normSq_pos hm k)
    (abs_horiz_le_sqrt_normSq _ i)

theorem tendsto_horo_horoSeq (hm : 1 ≤ m) :
    Filter.Tendsto (fun k : ℕ => horo (horoSeq hm k)) Filter.atTop (nhds ptInfty) := by
  rw [DifferentialGeometry.BoundaryTopology.isEmbedding_val.isInducing.tendsto_nhds_iff,
    tendsto_pi_nhds]
  intro a
  simp only [Function.comp_apply]
  rcases a with j | t
  · by_cases hj : j = Fin.last m
    · subst hj
      rw [ptInfty_val_last]
      have hfun : (fun k : ℕ => (horo (horoSeq hm k)).val (Sum.inl (Fin.last m)))
          = fun k => (normSq (horoSeq hm k) - 1)/(normSq (horoSeq hm k) + 1) :=
        funext fun k => horo_val_last (horoSeq hm k)
      rw [hfun]
      exact tendsto_axis_ratio.comp (tendsto_horoSeq_normSq hm)
    · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      rw [ptInfty_val_castSucc i]
      have hfun : (fun k : ℕ => (horo (horoSeq hm k)).val (Sum.inl i.castSucc))
          = fun k => 2 * horoSeq hm k i / (normSq (horoSeq hm k) + 1) :=
        funext fun k => horo_val_castSucc (horoSeq hm k) i
      rw [hfun]
      exact tendsto_horiz_horoSeq hm i
  · have ht : t = 0 := Subsingleton.elim t 0
    subst ht
    rw [ptInfty_val_time]
    have hfun : (fun k : ℕ => (horo (horoSeq hm k)).val (Sum.inr 0)) = fun _ => (1:ℝ) :=
      funext fun k => horo_val_time (horoSeq hm k)
    rw [hfun]
    exact tendsto_const_nhds

theorem eq_at_ptInfty_of_eq_on_horo {F G : BoundaryH (m + 1) → BoundaryH (m + 1)}
    (hF : Continuous F) (hG : Continuous G) (hm : 1 ≤ m)
    (h : ∀ x : Fin m → ℝ, F (horo x) = G (horo x)) :
    F ptInfty = G ptInfty := by
  have hseq := tendsto_horo_horoSeq hm
  have hFc : Filter.Tendsto (fun k => F (horo (horoSeq hm k))) Filter.atTop
      (nhds (F ptInfty)) :=
    (hF.tendsto ptInfty).comp hseq
  have hGc : Filter.Tendsto (fun k => G (horo (horoSeq hm k))) Filter.atTop
      (nhds (G ptInfty)) :=
    (hG.tendsto ptInfty).comp hseq
  have heq : (fun k => F (horo (horoSeq hm k))) = (fun k => G (horo (horoSeq hm k))) :=
    funext fun k => h _
  rw [← heq] at hGc
  exact tendsto_nhds_unique hFc hGc

theorem eq_on_boundary_of_eq_on_horo {F G : BoundaryH (m + 1) → BoundaryH (m + 1)}
    (hF : Continuous F) (hG : Continuous G) (hm : 1 ≤ m)
    (h : ∀ x : Fin m → ℝ, F (horo x) = G (horo x)) :
    ∀ v : BoundaryH (m+1), F v = G v := by
  intro v
  by_cases hv : v = ptInfty
  · subst hv
    exact eq_at_ptInfty_of_eq_on_horo hF hG hm h
  · obtain ⟨x, rfl⟩ := exists_horo_eq_of_ne_ptInfty v hv
    exact h x

end MobiusBoundary

end DifferentialGeometry

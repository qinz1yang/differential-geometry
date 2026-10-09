/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.Deformation

noncomputable section

open Set Filter Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.LorentzAveraging

open Hyperbolic HyperbolicAction HyperbolicFaithful LorentzExtremal

variable {n : ℕ}

def timelikeCone : Set (LorVec n) :=
  {v | 0 < tc v ∧ lorB v v < 0}

theorem isOpen_timelikeCone : IsOpen (timelikeCone (n := n)) :=
  (isOpen_lt continuous_const (continuous_apply (Sum.inr 0))).inter
    (isOpen_lt HyperbolicGeometry.continuous_lorB_self continuous_const)

def normalize (v : LorVec n) (hv : v ∈ timelikeCone) : HUpper n where
  val := (Real.sqrt (-lorB v v))⁻¹ • v
  is_unit := by
    have hp : 0 < -lorB v v := neg_pos.mpr hv.2
    have hs : Real.sqrt (-lorB v v) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    rw [lorB_smul_left, lorB_smul_right]
    have he := Real.sq_sqrt hp.le
    field_simp
    nlinarith
  future := by
    rw [tc_smul]
    exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (neg_pos.mpr hv.2))) hv.1

theorem normalize_rescale (v : LorVec n) (hv : v ∈ timelikeCone) :
    Real.sqrt (-lorB v v) • (normalize v hv).val = v := by
  change Real.sqrt (-lorB v v) • ((Real.sqrt (-lorB v v))⁻¹ • v) = v
  rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (neg_pos.mpr hv.2)).ne', one_smul]

theorem smul_val_mem_timelikeCone (p : HUpper n) {a : ℝ} (ha : 0 < a) :
    a • p.val ∈ timelikeCone := by
  constructor
  · rw [tc_smul]
    exact mul_pos ha p.future
  · rw [lorB_smul_left, lorB_smul_right, p.is_unit]
    nlinarith

theorem normalize_smul_val (p : HUpper n) {a : ℝ} (ha : 0 < a)
    (hv : a • p.val ∈ timelikeCone) :
    normalize (a • p.val) hv = p := by
  apply HUpper.ext
  change (Real.sqrt (-lorB (a • p.val) (a • p.val)))⁻¹ • (a • p.val) = p.val
  have he : -lorB (a • p.val) (a • p.val) = a ^ 2 := by
    rw [lorB_smul_left, lorB_smul_right, p.is_unit]
    ring
  rw [he, Real.sqrt_sq ha.le, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]

theorem continuous_normalize :
    Continuous (fun v : timelikeCone (n := n) => normalize v.val v.property) := by
  apply StratumDeformation.continuous_of_val
  have hc : Continuous (fun v : timelikeCone (n := n) => -lorB v.val v.val) :=
    (HyperbolicGeometry.continuous_lorB_self.comp continuous_subtype_val).neg
  exact (hc.sqrt.inv₀ (fun v => (Real.sqrt_pos.mpr (neg_pos.mpr v.property.2)).ne')).smul
    continuous_subtype_val

def normalizeOrBase (v : LorVec n) : HUpper n := by
  classical
  exact if hv : v ∈ timelikeCone then normalize v hv else basepointH

theorem normalizeOrBase_eq (v : LorVec n) (hv : v ∈ timelikeCone) :
    normalizeOrBase v = normalize v hv := dite_eq_left hv

theorem continuousAt_normalizeOrBase {v : LorVec n} (hv : v ∈ timelikeCone) :
    ContinuousAt normalizeOrBase v := by
  have hc : ContinuousOn (normalizeOrBase (n := n)) timelikeCone :=
    continuousOn_iff_continuous_domRestrict.mpr
      (continuous_normalize.congr (fun w => (normalizeOrBase_eq w.val w.property).symm))
  exact hc.continuousAt (isOpen_timelikeCone.mem_nhds hv)

theorem normalizeOrBase_smul_val (p : HUpper n) {a : ℝ} (ha : 0 < a) :
    normalizeOrBase (a • p.val) = p := by
  rw [normalizeOrBase_eq _ (smul_val_mem_timelikeCone p ha)]
  exact normalize_smul_val p ha _

theorem exists_linear_lift (hn : 1 ≤ n) (g : PO n 1) :
    ∃ L : LorVec n →ₗ[ℝ] LorVec n,
      (∀ p : HUpper n, L p.val = ((poMulAction hn).smul g p).val) ∧
      ∀ v w, lorB (L v) (L w) = lorB v w := by
  let := poMulAction hn
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (LorGrp n)) g
  have hsign (p : HUpper n) :
      0 < tc (matOf A *ᵥ (basepointH : HUpper n).val) ↔ 0 < tc (matOf A *ᵥ p.val) := by
    apply tc_pos_iff_tc_pos_of_lorB_neg
    · rw [lorB_matOf_mulVec]
      exact basepointH.is_unit
    · rw [lorB_matOf_mulVec]
      exact p.is_unit
    · rw [lorB_matOf_mulVec]
      linarith [HUpper.one_le_neg_lorB basepointH p]
  by_cases hA : 0 < tc (matOf A *ᵥ (basepointH : HUpper n).val)
  · refine ⟨Matrix.mulVecLin (matOf A), fun p => ?_, lorB_matOf_mulVec A⟩
    change matOf A *ᵥ p.val = upperize (matOf A *ᵥ p.val)
    exact (ite_eq_left ((hsign p).mp hA)).symm
  · refine ⟨-(Matrix.mulVecLin (matOf A)), fun p => ?_, fun v w => ?_⟩
    · change -(matOf A *ᵥ p.val) = upperize (matOf A *ᵥ p.val)
      exact (ite_eq_right (fun hp => hA ((hsign p).mpr hp))).symm
    · change lorB (-(matOf A *ᵥ v)) (-(matOf A *ᵥ w)) = lorB v w
      rw [lorB_neg_left, lorB_neg_right, neg_neg, lorB_matOf_mulVec]

theorem normalizeOrBase_linear_lift (hn : 1 ≤ n) (g : PO n 1)
    (L : LorVec n →ₗ[ℝ] LorVec n)
    (hL : ∀ p : HUpper n, L p.val = ((poMulAction hn).smul g p).val)
    {v : LorVec n} (hv : v ∈ timelikeCone) :
    normalizeOrBase (L v) = (poMulAction hn).smul g (normalizeOrBase v) := by
  have he := congrArg L (normalize_rescale v hv)
  rw [map_smul, hL] at he
  rw [← he, normalizeOrBase_smul_val _
    (Real.sqrt_pos.mpr (neg_pos.mpr hv.2)), normalizeOrBase_eq v hv]

theorem lorB_sum_left {ι : Type*} (s : Finset ι) (v : ι → LorVec n) (w : LorVec n) :
    lorB (∑ i ∈ s, v i) w = ∑ i ∈ s, lorB (v i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lorB, sdot, tc]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, lorB_add_left, ih]

theorem lorB_sum_right {ι : Type*} (s : Finset ι) (v : LorVec n) (w : ι → LorVec n) :
    lorB v (∑ i ∈ s, w i) = ∑ i ∈ s, lorB v (w i) := by
  rw [lorB_comm, lorB_sum_left]
  exact Finset.sum_congr rfl (fun _ _ => lorB_comm _ _)

theorem neg_lorB_sum_ge {ι : Type*} (s : Finset ι) (a : ι → ℝ) (p : ι → HUpper n)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i) ^ 2 ≤
      -lorB (∑ i ∈ s, a i • (p i).val) (∑ i ∈ s, a i • (p i).val) := by
  calc
    (∑ i ∈ s, a i) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, a i * a j :=
      by
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, a i * a j * (-lorB (p i).val (p j).val) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (HUpper.one_le_neg_lorB (p i) (p j)) (mul_nonneg (ha i hi) (ha j hj))
    _ = -lorB (∑ i ∈ s, a i • (p i).val) (∑ i ∈ s, a i • (p i).val) := by
      rw [lorB_sum_left, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [lorB_sum_right, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [lorB_smul_left, lorB_smul_right]
      ring

theorem sum_mem_timelikeCone {ι : Type*} (s : Finset ι) (a : ι → ℝ) (p : ι → HUpper n)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hpos : 0 < ∑ i ∈ s, a i) :
    (∑ i ∈ s, a i • (p i).val) ∈ timelikeCone := by
  have he : tc (∑ i ∈ s, a i • (p i).val) = ∑ i ∈ s, a i * tc (p i).val := by
    simp only [tc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · rw [he]
    apply lt_of_lt_of_le hpos
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (HUpper.one_le_tc (p i)) (ha i hi)
  · have hb := neg_lorB_sum_ge s a p ha
    nlinarith [sq_pos_of_pos hpos]

theorem finsum_mem_timelikeCone {ι : Type*} (a : ι → ℝ) (p : ι → HUpper n)
    (hfin : (Function.support a).Finite) (ha : ∀ i, 0 ≤ a i)
    (hpos : 0 < ∑ᶠ i, a i) :
    (∑ᶠ i, a i • (p i).val) ∈ timelikeCone := by
  classical
  have hs : Function.support (fun i => a i • (p i).val) ⊆ ↑hfin.toFinset := by
    intro i hi
    apply hfin.mem_toFinset.mpr
    intro he
    exact hi (by change a i • (p i).val = 0; rw [he, zero_smul])
  rw [finsum_eq_sum_of_support_subset _ hs]
  rw [finsum_eq_sum_of_support_subset a
    (show Function.support a ⊆ ↑hfin.toFinset from fun i hi => hfin.mem_toFinset.mpr hi)] at hpos
  exact sum_mem_timelikeCone _ a p (fun i _ => ha i) hpos

end DifferentialGeometry.LorentzAveraging

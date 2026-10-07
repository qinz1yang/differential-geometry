/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Action
import DifferentialGeometry.Analysis.Matrix.BoundedTorsion

noncomputable section

open Set Filter Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.BoundedTorsion

open HyperbolicAction

variable {n : ℕ}

theorem matOf_pow (A : LorGrp n) (k : ℕ) : matOf (A ^ k) = matOf A ^ k := by
  simp only [matOf, SubmonoidClass.coe_pow, map_pow]

theorem continuous_matOf : Continuous (matOf : LorGrp n →
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :=
  (MatrixSum.continuous_ofMatrix_symm (Fin n) (Fin 1) ℝ).comp continuous_subtype_val

theorem exists_po_nhds_pow_eq_one (hn : 1 ≤ n) (k : ℕ) (hk : 0 < k) :
    ∃ U : Set (PO n 1), IsOpen U ∧ (1 : PO n 1) ∈ U ∧
      ∀ g ∈ U, g ^ k = 1 → g = 1 := by
  obtain ⟨V, hVo, hV1, hV⟩ :=
    exists_matrix_nhds_pow_eq_one (ι := Fin n ⊕ Fin 1) (k * 2) (by omega)
  let q : LorGrp n → PO n 1 := QuotientGroup.mk' _
  refine ⟨q '' (matOf ⁻¹' V),
    QuotientGroup.isOpenMap_coe _ (hVo.preimage continuous_matOf),
    ⟨1, ?_, map_one (QuotientGroup.mk' _)⟩, ?_⟩
  · simpa only [mem_preimage, matOf_one] using hV1
  · rintro g ⟨A, hA, rfl⟩ hg
    have hq : QuotientGroup.mk' (Subgroup.center (LorGrp n)) (A ^ k) = 1 := by
      rw [map_pow]
      exact hg
    have hcenter : A ^ k ∈ Subgroup.center (LorGrp n) :=
      (QuotientGroup.eq_one_iff (A ^ k)).mp hq
    have hpow : matOf A ^ (k * 2) = 1 := by
      rw [pow_mul, ← matOf_pow]
      rcases DifferentialGeometry.ProjectiveOrthogonalGroup.Center.center_coe_eq hn hcenter with h | h
      · change matOf (A ^ k) = 1 at h
        rw [h, one_pow]
      · change matOf (A ^ k) = -1 at h
        rw [h, neg_one_sq]
    have hmat : matOf A = 1 := hV _ hA hpow
    have hA1 : A = 1 := by
      apply Subtype.ext
      exact MatrixSum.ofMatrix.symm.injective (hmat.trans matOf_one.symm)
    rw [hA1]
    exact map_one (QuotientGroup.mk' _)

theorem exists_po_nhds_no_bounded_torsion (hn : 1 ≤ n) (N : ℕ) :
    ∃ U : Set (PO n 1), U ∈ 𝓝 1 ∧
      ∀ g ∈ U, ∀ k : ℕ, 0 < k → k ≤ N → g ^ k = 1 → g = 1 := by
  classical
  have hlocal : ∀ k : {k : ℕ // k ∈ Finset.Icc 1 N},
      ∃ U : Set (PO n 1), U ∈ 𝓝 1 ∧ ∀ g ∈ U, g ^ (k : ℕ) = 1 → g = 1 := by
    intro k
    obtain ⟨U, hU, hU1, hpow⟩ :=
      exists_po_nhds_pow_eq_one hn k (by have := (Finset.mem_Icc.mp k.2).1; omega)
    exact ⟨U, hU.mem_nhds hU1, hpow⟩
  choose U hU hpow using hlocal
  refine ⟨⋂ k, U k, Filter.iInter_mem.mpr hU, fun g hg k hk hNk hgk => ?_⟩
  let i : {k : ℕ // k ∈ Finset.Icc 1 N} := ⟨k, Finset.mem_Icc.mpr ⟨hk, hNk⟩⟩
  exact hpow i g (mem_iInter.mp hg i) hgk

end DifferentialGeometry.BoundedTorsion

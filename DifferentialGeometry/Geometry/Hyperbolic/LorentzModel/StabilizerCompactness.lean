/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Defs

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.StabilizerCompact

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.Hyperbolic.HUpper
open DifferentialGeometry.HyperbolicAction
open DifferentialGeometry.HyperbolicFaithful
open DifferentialGeometry.HyperbolicBoundary
open Matrix

variable {n : ℕ}

noncomputable def eSpat (b : Fin n) : LorVec n := Pi.single (Sum.inl b) 1

theorem tc_eSpat (b : Fin n) : tc (eSpat b : LorVec n) = 0 := by
  change (Pi.single (Sum.inl b) 1 : LorVec n) (Sum.inr 0) = 0
  simp

theorem sdot_eSpat_self (b : Fin n) : sdot (eSpat b : LorVec n) (eSpat b) = 1 := by
  change ∑ i : Fin n, (Pi.single (Sum.inl b) 1 : LorVec n) (Sum.inl i)
      * (Pi.single (Sum.inl b) 1 : LorVec n) (Sum.inl i) = 1
  rw [Finset.sum_eq_single b]
  · rw [Pi.single_eq_same]
    norm_num
  · intro i _ hi
    rw [Pi.single_eq_of_ne (show Sum.inl i ≠ Sum.inl b from fun h => hi (Sum.inl.inj h))]
    norm_num
  · intro hb
    exact absurd (Finset.mem_univ b) hb

theorem sdot_eSpat_eTime (b : Fin n) : sdot (eSpat b : LorVec n) eTime = 0 := by
  change ∑ i : Fin n, (Pi.single (Sum.inl b) 1 : LorVec n) (Sum.inl i)
      * (eTime : LorVec n) (Sum.inl i) = 0
  simp [eTime_apply_inl]

theorem lorB_eSpat_self (b : Fin n) : lorB (eSpat b : LorVec n) (eSpat b) = 1 := by
  change sdot (eSpat b) (eSpat b) - tc (eSpat b) * tc (eSpat b) = 1
  rw [sdot_eSpat_self, tc_eSpat]
  norm_num

theorem lorB_eSpat_eTime (b : Fin n) : lorB (eSpat b : LorVec n) eTime = 0 := by
  change sdot (eSpat b) eTime - tc (eSpat b) * tc eTime = 0
  rw [sdot_eSpat_eTime, tc_eSpat]
  norm_num

theorem mulVec_eSpat (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (b : Fin n)
    (a : Fin n ⊕ Fin 1) :
    (M *ᵥ eSpat b) a = M a (Sum.inl b) := by
  change (M *ᵥ Pi.single (Sum.inl b) 1) a = M a (Sum.inl b)
  rw [Matrix.mulVec_single_one, Matrix.col_apply]

theorem mulVec_eTime (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (a : Fin n ⊕ Fin 1) :
    (M *ᵥ eTime) a = M a (Sum.inr 0) := by
  change (M *ᵥ Pi.single (Sum.inr 0) 1) a = M a (Sum.inr 0)
  rw [Matrix.mulVec_single_one, Matrix.col_apply]

theorem stabilizer_spatial_column {A : LorGrp n}
    (hA : matOf A *ᵥ eTime = eTime ∨ matOf A *ᵥ eTime = -eTime) (b : Fin n) :
    tc (matOf A *ᵥ eSpat b) = 0 ∧ sdot (matOf A *ᵥ eSpat b) (matOf A *ᵥ eSpat b) = 1 := by
  have hlb : lorB (matOf A *ᵥ eSpat b) (matOf A *ᵥ eSpat b) = 1 := by
    rw [lorB_matOf_mulVec]
    exact lorB_eSpat_self b
  have hlbt : lorB (matOf A *ᵥ eSpat b) (matOf A *ᵥ eTime) = 0 := by
    rw [lorB_matOf_mulVec]
    exact lorB_eSpat_eTime b
  have htc0 : tc (matOf A *ᵥ eSpat b) = 0 := by
    rcases hA with h | h
    · rw [h] at hlbt
      have hsd0 : sdot (matOf A *ᵥ eSpat b) (eTime : LorVec n) = 0 := by
        change ∑ i : Fin n, (matOf A *ᵥ eSpat b) (Sum.inl i) * (eTime : LorVec n) (Sum.inl i) = 0
        simp [eTime_apply_inl]
      have h1 : lorB (matOf A *ᵥ eSpat b) eTime = - tc (matOf A *ᵥ eSpat b) := by
        change sdot _ _ - tc _ * tc (eTime : LorVec n) = _
        rw [hsd0, tc_eTime]
        ring
      rw [h1] at hlbt
      linarith
    · rw [h] at hlbt
      have hsd0' : sdot (matOf A *ᵥ eSpat b) (-eTime : LorVec n) = 0 := by
        change ∑ i : Fin n, (matOf A *ᵥ eSpat b) (Sum.inl i) * (-eTime : LorVec n) (Sum.inl i) = 0
        simp [eTime_apply_inl]
      have h1 : lorB (matOf A *ᵥ eSpat b) (-eTime) = tc (matOf A *ᵥ eSpat b) := by
        change sdot _ _ - tc _ * tc (-eTime : LorVec n) = _
        rw [hsd0', tc_neg, tc_eTime]
        ring
      rw [h1] at hlbt
      linarith
  refine ⟨htc0, ?_⟩
  have h2 : sdot (matOf A *ᵥ eSpat b) (matOf A *ᵥ eSpat b)
      = 1 + tc (matOf A *ᵥ eSpat b) * tc (matOf A *ᵥ eSpat b) := by
    have h4 : sdot (matOf A *ᵥ eSpat b) (matOf A *ᵥ eSpat b)
        - tc (matOf A *ᵥ eSpat b) * tc (matOf A *ᵥ eSpat b) = 1 := hlb
    linarith
  rw [h2, htc0]
  norm_num

theorem entry_abs_le_one_of_stabilizer {A : LorGrp n}
    (hA : matOf A *ᵥ eTime = eTime ∨ matOf A *ᵥ eTime = -eTime) (a b : Fin n ⊕ Fin 1) :
    |matOf A a b| ≤ 1 := by
  rcases b with b | b
  · rcases a with a | a
    · have habs : |(matOf A *ᵥ eSpat b) (Sum.inl a)| ≤ 1 := by
        have hsd1 := (stabilizer_spatial_column hA b).2
        have hsq : ((matOf A *ᵥ eSpat b) (Sum.inl a)) ^ 2 ≤ 1 := by
          have hsum : ((matOf A *ᵥ eSpat b) (Sum.inl a)) ^ 2
              ≤ ∑ j : Fin n, ((matOf A *ᵥ eSpat b) (Sum.inl j)) ^ 2 :=
            Finset.single_le_sum (f := fun j => ((matOf A *ᵥ eSpat b) (Sum.inl j)) ^ 2)
              (fun j _ => sq_nonneg _) (Finset.mem_univ a)
          have heq : (∑ j : Fin n, ((matOf A *ᵥ eSpat b) (Sum.inl j)) ^ 2)
              = sdot (matOf A *ᵥ eSpat b) (matOf A *ᵥ eSpat b) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [pow_two]
          rw [heq, hsd1] at hsum
          exact hsum
        have hsq1 : ((matOf A *ᵥ eSpat b) (Sum.inl a)) ^ 2 ≤ (1 : ℝ) ^ 2 := by
          rw [one_pow]
          exact hsq
        exact abs_le_of_sq_le_sq hsq1 zero_le_one
      rwa [mulVec_eSpat] at habs
    · have htc0 := (stabilizer_spatial_column hA b).1
      have h0 : a = 0 := Subsingleton.elim a 0
      subst h0
      rw [← mulVec_eSpat (matOf A) b (Sum.inr 0)]
      change |tc (matOf A *ᵥ eSpat b)| ≤ 1
      rw [htc0]
      norm_num
  · have hb0 : b = 0 := Subsingleton.elim b 0
    subst hb0
    rcases hA with h | h
    · have hent : ∀ c : Fin n ⊕ Fin 1, matOf A c (Sum.inr 0) = (eTime : LorVec n) c := by
        intro c
        rw [← mulVec_eTime (matOf A) c, h]
      rcases a with a | a
      · rw [hent, eTime_apply_inl]
        norm_num
      · have h0 : a = 0 := Subsingleton.elim a 0
        subst h0
        rw [hent, eTime_apply_inr]
        norm_num
    · have hent : ∀ c : Fin n ⊕ Fin 1, matOf A c (Sum.inr 0) = (-eTime : LorVec n) c := by
        intro c
        rw [← mulVec_eTime (matOf A) c, h]
      rcases a with a | a
      · rw [hent, Pi.neg_apply, eTime_apply_inl]
        norm_num
      · have h0 : a = 0 := Subsingleton.elim a 0
        subst h0
        rw [hent, Pi.neg_apply, eTime_apply_inr]
        norm_num

theorem continuous_matOf_mulVec_eTime :
    Continuous fun A : LorGrp n => matOf A *ᵥ eTime := by
  apply Continuous.matrix_mulVec _ continuous_const
  have h1 : Continuous (Subtype.val : LorGrp n → MatrixSum (Fin n) (Fin 1) ℝ) :=
    continuous_subtype_val
  have h2 : Continuous (MatrixSum.ofMatrix.symm :
      MatrixSum (Fin n) (Fin 1) ℝ → Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :=
    MatrixSum.continuous_ofMatrix_symm (Fin n) (Fin 1) ℝ
  exact h2.comp h1

def stabLorSet : Set (LorGrp n) :=
  {A | matOf A *ᵥ eTime = eTime ∨ matOf A *ᵥ eTime = -eTime}

theorem lorGrp_smul_basepoint_iff (A : LorGrp n) :
    A • (basepointH : HUpper n) = basepointH ↔ A ∈ stabLorSet := by
  rw [HUpper.ext_iff]
  change upperize (matOf A *ᵥ eTime) = eTime ↔ _
  constructor
  · intro h
    unfold upperize at h
    by_cases htc : 0 < tc (matOf A *ᵥ eTime)
    · rw [ite_eq_left htc] at h
      exact Or.inl h
    · rw [ite_eq_right htc] at h
      exact Or.inr (neg_eq_iff_eq_neg.mp h)
  · intro h
    rcases h with h | h
    · rw [h]
      unfold upperize
      rw [ite_eq_left (by rw [tc_eTime]; norm_num)]
    · rw [h]
      unfold upperize
      rw [ite_eq_right (by rw [tc_neg, tc_eTime]; norm_num)]
      exact neg_neg eTime

theorem isClosed_stabLorSet : IsClosed (stabLorSet : Set (LorGrp n)) := by
  have heq : stabLorSet
      = (fun A : LorGrp n => matOf A *ᵥ eTime) ⁻¹' {eTime, -eTime} := by
    ext A
    constructor
    · intro h
      exact h
    · intro h
      exact h
  rw [heq, Set.insert_eq]
  exact (isClosed_singleton.union isClosed_singleton).preimage continuous_matOf_mulVec_eTime

theorem isCompact_cubeMatrix :
    IsCompact (Set.pi Set.univ (fun _ : Fin n ⊕ Fin 1 =>
      Set.pi Set.univ fun _ => Set.Icc (-1 : ℝ) 1) :
      Set (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc

noncomputable def matrixSumSymmHomeomorph :
    MatrixSum (Fin n) (Fin 1) ℝ ≃ₜ Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Homeomorph.mk (MatrixSum.ofMatrix.symm.toEquiv)
    (MatrixSum.continuous_ofMatrix_symm (Fin n) (Fin 1) ℝ)
    (MatrixSum.continuous_ofMatrix (Fin n) (Fin 1) ℝ)

theorem isCompact_preimage_cube :
    IsCompact ((fun A : LorGrp n => (A : MatrixSum (Fin n) (Fin 1) ℝ)) ⁻¹'
      (MatrixSum.ofMatrix.symm ⁻¹' (Set.pi Set.univ (fun _ : Fin n ⊕ Fin 1 =>
        Set.pi Set.univ fun _ => Set.Icc (-1 : ℝ) 1) :
        Set (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)))) := by
  have hK : IsCompact (matrixSumSymmHomeomorph ⁻¹' (Set.pi Set.univ (fun _ : Fin n ⊕ Fin 1 =>
      Set.pi Set.univ fun _ => Set.Icc (-1 : ℝ) 1) :
      Set (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ))) := by
    apply matrixSumSymmHomeomorph.isInducing.isCompact_preimage _ isCompact_cubeMatrix
    rw [Set.range_eq_univ.mpr matrixSumSymmHomeomorph.surjective]
    exact isClosed_univ
  have hce : Topology.IsClosedEmbedding (fun A : LorGrp n =>
      (A : MatrixSum (Fin n) (Fin 1) ℝ)) :=
    (MatrixSum.isClosed_unitary (Fin n) (Fin 1) ℝ).isClosedEmbedding_subtypeVal
  exact hce.isInducing.isCompact_preimage hce.isClosed_range hK

theorem stabLorSet_subset_cube :
    stabLorSet ⊆ (fun A : LorGrp n => (A : MatrixSum (Fin n) (Fin 1) ℝ)) ⁻¹'
      (MatrixSum.ofMatrix.symm ⁻¹' (Set.pi Set.univ (fun _ : Fin n ⊕ Fin 1 =>
        Set.pi Set.univ fun _ => Set.Icc (-1 : ℝ) 1) :
        Set (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ))) := by
  intro A hA
  change MatrixSum.ofMatrix.symm (A : MatrixSum (Fin n) (Fin 1) ℝ) ∈
    (Set.pi Set.univ (fun _ : Fin n ⊕ Fin 1 => Set.pi Set.univ fun _ => Set.Icc (-1 : ℝ) 1) :
      Set (Fin n ⊕ Fin 1 → Fin n ⊕ Fin 1 → ℝ))
  refine Set.mem_univ_pi.mpr fun a => Set.mem_univ_pi.mpr fun b => ?_
  rw [Set.mem_Icc]
  exact abs_le.mp (entry_abs_le_one_of_stabilizer hA a b)

theorem isCompact_stabLorSet : IsCompact (stabLorSet : Set (LorGrp n)) :=
  isCompact_preimage_cube.of_isClosed_subset isClosed_stabLorSet stabLorSet_subset_cube

theorem stabilizer_basepoint_po_eq_image (hn : 1 ≤ n) :
    {g : PO n 1 | (poMulAction hn).smul g basepointH = basepointH}
      = (fun A : LorGrp n =>
          (QuotientGroup.mk' (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) A
            : PO n 1)) '' stabLorSet := by
  let := poMulAction hn
  ext g
  constructor
  · intro hg
    rw [Set.mem_ofPred_eq] at hg
    obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) g
    refine ⟨A, (lorGrp_smul_basepoint_iff A).mp ?_, rfl⟩
    have h1 : (poMulAction hn).smul
          (QuotientGroup.mk' (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) A
            : PO n 1) basepointH
          = A • (basepointH : HUpper n) :=
      po_smul_mk hn A basepointH
    rw [← h1]
    exact hg
  · rintro ⟨A, hA, rfl⟩
    have hA' : A • (basepointH : HUpper n) = basepointH :=
      (lorGrp_smul_basepoint_iff A).mpr hA
    have h1 : (poMulAction hn).smul
          (QuotientGroup.mk' (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) A
            : PO n 1) basepointH
          = A • (basepointH : HUpper n) :=
      po_smul_mk hn A basepointH
    change (poMulAction hn).smul
        (QuotientGroup.mk' (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) A
          : PO n 1) basepointH = basepointH
    rw [h1]
    exact hA'

theorem continuous_mk'_to_PO :
    Continuous fun A : LorGrp n =>
      (QuotientGroup.mk' (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) A
        : PO n 1) :=
  QuotientGroup.isOpenQuotientMap_mk.continuous

theorem isCompact_stabilizer_basepoint (hn : 1 ≤ n) :
    IsCompact {g : PO n 1 | (poMulAction hn).smul g basepointH = basepointH} := by
  rw [stabilizer_basepoint_po_eq_image hn]
  exact isCompact_stabLorSet.image continuous_mk'_to_PO

end DifferentialGeometry.StabilizerCompact

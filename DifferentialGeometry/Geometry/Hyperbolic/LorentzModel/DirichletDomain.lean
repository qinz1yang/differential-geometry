/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.ContinuousAction

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.DirichletDomain

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.HyperbolicAction
open DifferentialGeometry.HyperbolicFaithful
open DifferentialGeometry.StabilizerCompact
open DifferentialGeometry.ContinuousAction
open Matrix

variable {n : ℕ}

theorem lorB_eTime_right (w : LorVec n) : lorB w (eTime : LorVec n) = - tc w := by
  have hsd : sdot w (eTime : LorVec n) = 0 := by
    change (∑ i : Fin n, w (Sum.inl i) * (eTime : LorVec n) (Sum.inl i)) = 0
    simp [eTime_apply_inl]
  have htc : tc (eTime : LorVec n) = 1 := eTime_apply_inr
  change sdot w (eTime : LorVec n) - tc w * tc (eTime : LorVec n) = - tc w
  rw [hsd, htc]
  ring

theorem dist_lor_smul_basepoint (A : LorGrp n) :
    dist (A • (basepointH : HUpper n)) basepointH = Real.arcosh |tc (matOf A *ᵥ eTime)| := by
  have h1 : (A • (basepointH : HUpper n)).val = upperize (matOf A *ᵥ eTime) :=
    smul_val A basepointH
  have h2 : (basepointH : HUpper n).val = (eTime : LorVec n) := rfl
  change Real.arcosh (- lorB (A • (basepointH : HUpper n)).val (basepointH : HUpper n).val) = _
  rw [h1, h2, lorB_eTime_right, tc_upperize, neg_neg]

theorem one_le_abs_tc {v : LorVec n} (hv : lorB v v = -1) : 1 ≤ |tc v| := by
  have hs : sdot v v = tc v * tc v - 1 := by
    have h0 := hv
    simp only [lorB] at h0
    linarith
  have h1 : 1 ≤ tc v ^ 2 := by
    have h2 : 0 ≤ sdot v v := sdot_self_nonneg v
    rw [hs] at h2
    have h3 : (0:ℝ) ≤ tc v * tc v := mul_self_nonneg _
    nlinarith [sq_nonneg (tc v)]
  have h4 : (0:ℝ) ≤ tc v * tc v := mul_self_nonneg _
  rw [show (1:ℝ) = |1| by norm_num]
  rw [← sq_le_sq]
  rw [one_pow]
  have h5 : tc v ^ 2 = tc v * tc v := by ring
  nlinarith [h1, h4]

theorem entry_abs_le_cosh_of_dist_le (A : LorGrp n) {R : ℝ}
    (h : dist (A • (basepointH : HUpper n)) basepointH ≤ R) (a b : Fin n ⊕ Fin 1) :
    |matOf A a b| ≤ Real.cosh R := by
  set v : LorVec n := matOf A *ᵥ eTime with hvdef
  have hR : 0 ≤ R := dist_nonneg.trans h
  have hvv : lorB v v = -1 := by rw [hvdef, lorB_matOf_mulVec]; exact lorB_eTime
  have htc : |tc v| ≤ Real.cosh R := by
    have h1 : 1 ≤ |tc v| := one_le_abs_tc hvv
    have h2 : |tc v| = Real.cosh (Real.arcosh |tc v|) := (Real.cosh_arcosh h1).symm
    rw [h2]
    have h3 : Real.arcosh |tc v| ≤ R := by
      rw [hvdef, ← dist_lor_smul_basepoint A]
      exact h
    exact Real.cosh_strictMonoOn.monotoneOn
      (Set.mem_Ici.mpr (Real.arcosh_nonneg h1)) (Set.mem_Ici.mpr hR) h3
  have hsdv : sdot v v = tc v ^ 2 - 1 := by
    have h0 := hvv
    simp only [lorB] at h0
    have h3 : tc v ^ 2 = tc v * tc v := by ring
    rw [h3]
    linarith
  have htc2 : tc v ^ 2 ≤ Real.cosh R ^ 2 := by
    rw [sq_le_sq]
    rwa [abs_of_nonneg ((zero_le_one.trans (Real.one_le_cosh R)))]
  rcases b with b | b
  · set w : LorVec n := matOf A *ᵥ eSpat b with hwdef
    have hww : lorB w w = 1 := by rw [hwdef, lorB_matOf_mulVec]; exact lorB_eSpat_self b
    have hwv : lorB w v = 0 := by rw [hwdef, hvdef, lorB_matOf_mulVec]; exact lorB_eSpat_eTime b
    have hswv : sdot w v = tc w * tc v := by
      have h0 := hwv
      simp only [lorB] at h0
      linarith
    have hcs : sdot w v ^ 2 ≤ sdot w w * sdot v v := sdot_sq_le w v
    have hsww : sdot w w = 1 + tc w ^ 2 := by
      have h0 := hww
      simp only [lorB] at h0
      have h3 : tc w * tc w = sdot w w - 1 := by linarith
      have h4 : tc w ^ 2 = tc w * tc w := by ring
      linarith
    have htcw : tc w ^ 2 ≤ tc v ^ 2 - 1 := by
      rw [hswv, hsww, hsdv, mul_pow] at hcs
      nlinarith [hcs]
    have htcw2 : tc w ^ 2 ≤ Real.cosh R ^ 2 := by
      have h1 : (0:ℝ) ≤ 1 := zero_le_one
      nlinarith [htcw, htc2, (zero_le_one.trans (Real.one_le_cosh R))]
    rcases a with a | a
    · rw [← mulVec_eSpat (matOf A) b (Sum.inl a)]
      change |(matOf A *ᵥ eSpat b) (Sum.inl a)| ≤ Real.cosh R
      have hsq : ((matOf A *ᵥ eSpat b) (Sum.inl a)) ^ 2 ≤ Real.cosh R ^ 2 := by
        have hsum : ((matOf A *ᵥ eSpat b) (Sum.inl a)) ^ 2
            ≤ ∑ j : Fin n, ((matOf A *ᵥ eSpat b) (Sum.inl j)) ^ 2 :=
          Finset.single_le_sum (f := fun j => ((matOf A *ᵥ eSpat b) (Sum.inl j)) ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ a)
        have heq : (∑ j : Fin n, ((matOf A *ᵥ eSpat b) (Sum.inl j)) ^ 2)
            = sdot (matOf A *ᵥ eSpat b) (matOf A *ᵥ eSpat b) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [pow_two]
        rw [heq] at hsum
        calc ((matOf A *ᵥ eSpat b) (Sum.inl a)) ^ 2 ≤ sdot w w := hsum
          _ = 1 + tc w ^ 2 := hsww
          _ ≤ Real.cosh R ^ 2 := by nlinarith [htcw2, (zero_le_one.trans (Real.one_le_cosh R))]
      exact abs_le_of_sq_le_sq hsq ((zero_le_one.trans (Real.one_le_cosh R)))
    · have ha0 : a = 0 := Subsingleton.elim a 0
      subst ha0
      rw [← mulVec_eSpat (matOf A) b (Sum.inr 0)]
      change |tc (matOf A *ᵥ eSpat b)| ≤ Real.cosh R
      exact abs_le_of_sq_le_sq htcw2 ((zero_le_one.trans (Real.one_le_cosh R)))
  · have hb0 : b = 0 := Subsingleton.elim b 0
    subst hb0
    rcases a with a | a
    · rw [← mulVec_eTime (matOf A) (Sum.inl a)]
      change |v (Sum.inl a)| ≤ Real.cosh R
      have hsq : (v (Sum.inl a)) ^ 2 ≤ Real.cosh R ^ 2 := by
        have hsum : (v (Sum.inl a)) ^ 2
            ≤ ∑ j : Fin n, (v (Sum.inl j)) ^ 2 :=
          Finset.single_le_sum (f := fun j => (v (Sum.inl j)) ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ a)
        have heq : (∑ j : Fin n, (v (Sum.inl j)) ^ 2) = sdot v v := by
          apply Finset.sum_congr rfl
          intro j _
          rw [pow_two]
        rw [heq] at hsum
        calc (v (Sum.inl a)) ^ 2 ≤ sdot v v := hsum
          _ = tc v ^ 2 - 1 := hsdv
          _ ≤ Real.cosh R ^ 2 := by nlinarith [htc2, (zero_le_one.trans (Real.one_le_cosh R))]
      exact abs_le_of_sq_le_sq hsq ((zero_le_one.trans (Real.one_le_cosh R)))
    · have ha0 : a = 0 := Subsingleton.elim a 0
      subst ha0
      rw [← mulVec_eTime (matOf A) (Sum.inr 0)]
      change |tc v| ≤ Real.cosh R
      exact htc

theorem isCompact_cube (c : ℝ) :
    IsCompact (Set.pi Set.univ (fun _ : Fin n ⊕ Fin 1 =>
      Set.pi Set.univ fun _ => Set.Icc (-c) c) :
      Set (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc

theorem isCompact_preimage_cube (c : ℝ) :
    IsCompact ((fun A : LorGrp n => (A : MatrixSum (Fin n) (Fin 1) ℝ)) ⁻¹'
      (matrixSumSymmHomeomorph ⁻¹' (Set.pi Set.univ (fun _ : Fin n ⊕ Fin 1 =>
        Set.pi Set.univ fun _ => Set.Icc (-c) c) :
        Set (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)))) := by
  have hK : IsCompact (matrixSumSymmHomeomorph ⁻¹' (Set.pi Set.univ (fun _ : Fin n ⊕ Fin 1 =>
      Set.pi Set.univ fun _ => Set.Icc (-c) c) :
      Set (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ))) :=
    matrixSumSymmHomeomorph.isCompact_preimage.mpr (isCompact_cube c)
  have hce : Topology.IsClosedEmbedding (fun A : LorGrp n =>
      (A : MatrixSum (Fin n) (Fin 1) ℝ)) :=
    (MatrixSum.isClosed_unitary (Fin n) (Fin 1) ℝ).isClosedEmbedding_subtypeVal
  exact hce.isCompact_preimage hK

theorem isCompact_orbit_preimage (hn : 1 ≤ n) (R : ℝ) :
    letI := poMulAction hn
    IsCompact {g : PO n 1 | dist (g • (basepointH : HUpper n)) basepointH ≤ R} := by
  let := poMulAction hn
  set T : Set (LorGrp n) := {A | dist (A • (basepointH : HUpper n)) basepointH ≤ R} with hTdef
  have hTclosed : IsClosed T := by
    have hcont : Continuous fun A : LorGrp n => dist (A • (basepointH : HUpper n)) basepointH :=
      Continuous.dist (continuous_actH.comp
        (Continuous.prodMk continuous_id (continuous_const (y := basepointH))))
        continuous_const
    have hTeq : T = (fun A : LorGrp n => dist (A • (basepointH : HUpper n)) basepointH) ⁻¹'
        Set.Iic R := rfl
    rw [hTeq]
    exact isClosed_Iic.preimage hcont
  have hTsub : T ⊆ (fun A : LorGrp n => (A : MatrixSum (Fin n) (Fin 1) ℝ)) ⁻¹'
      (matrixSumSymmHomeomorph ⁻¹' (Set.pi Set.univ (fun _ : Fin n ⊕ Fin 1 =>
        Set.pi Set.univ fun _ => Set.Icc (-Real.cosh R) (Real.cosh R)) :
        Set (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ))) := by
    intro A hA
    change matrixSumSymmHomeomorph (A : MatrixSum (Fin n) (Fin 1) ℝ) ∈
      (Set.pi Set.univ (fun _ : Fin n ⊕ Fin 1 =>
        Set.pi Set.univ fun _ => Set.Icc (-Real.cosh R) (Real.cosh R)) :
        Set (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ))
    refine Set.mem_univ_pi.mpr fun a => Set.mem_univ_pi.mpr fun b => ?_
    rw [Set.mem_Icc]
    exact abs_le.mp (entry_abs_le_cosh_of_dist_le A hA a b)
  have hTcompact : IsCompact T :=
    (isCompact_preimage_cube (Real.cosh R)).of_isClosed_subset hTclosed hTsub
  have hSeq : {g : PO n 1 | dist (g • (basepointH : HUpper n)) basepointH ≤ R}
      = (fun A : LorGrp n =>
          (QuotientGroup.mk' (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) A
            : PO n 1)) '' T := by
    ext g
    constructor
    · intro hg
      obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective
        (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) g
      refine ⟨A, ?_, rfl⟩
      have hge : dist ((QuotientGroup.mk'
            (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) A
            : PO n 1) • (basepointH : HUpper n)) basepointH ≤ R := hg
      rw [po_smul_mk hn A basepointH] at hge
      exact hge
    · rintro ⟨A, hA, rfl⟩
      have hge : dist ((QuotientGroup.mk'
            (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) A
            : PO n 1) • (basepointH : HUpper n)) basepointH ≤ R := by
        rw [po_smul_mk hn A basepointH]
        exact hA
      exact hge
  rw [hSeq]
  exact hTcompact.image continuous_mk'_to_PO

theorem finite_setOf_coe_le (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) (R : ℝ) :
    letI := poMulAction hn
    Set.Finite {γ : Γ | dist ((γ : PO n 1) • (basepointH : HUpper n)) basepointH ≤ R} := by
  let := poMulAction hn
  have hW : IsCompact {g : PO n 1 | dist (g • (basepointH : HUpper n)) basepointH ≤ R} :=
    isCompact_orbit_preimage hn R
  have himage : (fun γ : ↥Γ => (γ : PO n 1)) ''
      {γ : ↥Γ | dist ((γ : PO n 1) • (basepointH : HUpper n)) basepointH ≤ R}
      ⊆ {g : PO n 1 | dist (g • (basepointH : HUpper n)) basepointH ≤ R} ∩ SetLike.coe Γ := by
    rintro g ⟨⟨γ, hγΓ⟩, hγ, rfl⟩
    exact ⟨hγ, hγΓ⟩
  have hcomp : IsCompact ({g : PO n 1 | dist (g • (basepointH : HUpper n)) basepointH ≤ R}
      ∩ SetLike.coe Γ) :=
    hW.inter_right (DifferentialGeometry.ProjectiveOrthogonalGroup.Center.isClosed_of_discrete hn Γ disc)
  have hfin : ((fun γ : ↥Γ => (γ : PO n 1)) ''
      {γ : ↥Γ | dist ((γ : PO n 1) • (basepointH : HUpper n)) basepointH ≤ R}).Finite :=
    (hcomp.finite (disc.mono Set.inter_subset_right)).subset himage
  exact Set.Finite.of_finite_image hfin Subtype.coe_injective.injOn

theorem finite_exists_smul_inter (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) {K : Set (HUpper n)} (hK : IsCompact K) :
    letI := poMulAction hn
    Set.Finite {γ : Γ | ∃ x ∈ K, ((γ : PO n 1) • x) ∈ K} := by
  let := poMulAction hn
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall basepointH
  apply Set.Finite.subset (finite_setOf_coe_le hn Γ disc (2 * R))
  rintro γ ⟨x, hxK, hγxK⟩
  change dist ((γ : PO n 1) • (basepointH : HUpper n)) basepointH ≤ 2 * R
  have hx : dist basepointH x ≤ R := by
    have hx' := Metric.mem_closedBall.mp (hR hxK)
    rw [dist_comm] at hx'
    exact hx'
  have hγx : dist ((γ : PO n 1) • x) basepointH ≤ R := Metric.mem_closedBall.mp (hR hγxK)
  calc dist ((γ : PO n 1) • basepointH) basepointH
      ≤ dist ((γ : PO n 1) • basepointH) ((γ : PO n 1) • x)
        + dist ((γ : PO n 1) • x) basepointH := dist_triangle _ _ _
    _ = dist basepointH x + dist ((γ : PO n 1) • x) basepointH := by
        rw [po_dist_smul hn (γ : PO n 1) basepointH x]
    _ ≤ R + R := add_le_add hx hγx
    _ = 2 * R := by ring

theorem exists_min_dist (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) (x : HUpper n) :
    letI := poMulAction hn
    ∃ γ₀ : Γ, ∀ γ : Γ, dist x ((γ₀ : PO n 1) • (basepointH : HUpper n))
      ≤ dist x ((γ : PO n 1) • basepointH) := by
  let := poMulAction hn
  set A : Set ↥Γ :=
    {γ | dist x ((γ : PO n 1) • (basepointH : HUpper n)) ≤ dist x basepointH} with hAdef
  have hAsub : A ⊆ {γ : ↥Γ | dist ((γ : PO n 1) • (basepointH : HUpper n)) basepointH
      ≤ 2 * dist x basepointH} := by
    intro γ hγ
    change dist ((γ : PO n 1) • basepointH) basepointH ≤ 2 * dist x basepointH
    calc dist ((γ : PO n 1) • basepointH) basepointH
        ≤ dist ((γ : PO n 1) • basepointH) x + dist x basepointH := dist_triangle _ _ _
      _ = dist x ((γ : PO n 1) • basepointH) + dist x basepointH := by
          rw [dist_comm ((γ : PO n 1) • basepointH) x]
      _ ≤ dist x basepointH + dist x basepointH := add_le_add hγ le_rfl
      _ = 2 * dist x basepointH := by ring
  have hAfin : A.Finite :=
    (finite_setOf_coe_le hn Γ disc (2 * dist x basepointH)).subset hAsub
  have hAne : A.Nonempty := by
    refine ⟨1, ?_⟩
    change dist x (((1 : ↥Γ) : PO n 1) • basepointH) ≤ dist x basepointH
    rw [Subgroup.coe_one, one_smul]
  obtain ⟨γ₀, hγ₀A, hmin⟩ := hAfin.toFinset.exists_min_image
    (fun γ : ↥Γ => dist x ((γ : PO n 1) • (basepointH : HUpper n))) (by simpa using hAne)
  refine ⟨γ₀, fun γ => ?_⟩
  by_cases hγ : γ ∈ A
  · exact hmin γ (by simpa using hγ)
  · have h1 : (1 : ↥Γ) ∈ A := by
      change dist x (((1 : ↥Γ) : PO n 1) • basepointH) ≤ dist x basepointH
      rw [Subgroup.coe_one, one_smul]
    have hle : dist x ((γ₀ : PO n 1) • basepointH) ≤ dist x basepointH :=
      (hmin 1 (by simpa using h1)).trans (by
        change dist x (((1 : ↥Γ) : PO n 1) • basepointH) ≤ dist x basepointH
        rw [Subgroup.coe_one, one_smul])
    have hgt : dist x basepointH < dist x ((γ : PO n 1) • basepointH) := by
      by_contra h
      exact hγ (le_of_not_gt (by simpa using h))
    exact hle.trans hgt.le

def dirichletDomain (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) : Set (HUpper n) :=
  letI := poMulAction hn
  {y | ∀ γ : Γ, dist y basepointH ≤ dist y ((γ : PO n 1) • (basepointH : HUpper n))}

theorem exists_inv_smul_mem_dirichletDomain (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) (x : HUpper n) :
    letI := poMulAction hn
    ∃ γ₀ : Γ, ((γ₀ : PO n 1)⁻¹) • x ∈ dirichletDomain hn Γ := by
  let := poMulAction hn
  obtain ⟨γ₀, hγ₀⟩ := exists_min_dist hn Γ disc x
  refine ⟨γ₀, fun γ => ?_⟩
  change dist (((γ₀ : PO n 1)⁻¹) • x) basepointH
    ≤ dist (((γ₀ : PO n 1)⁻¹) • x) ((γ : PO n 1) • basepointH)
  have e1 : dist (((γ₀ : PO n 1)⁻¹) • x) basepointH
      = dist x ((γ₀ : PO n 1) • basepointH) := by
    have h2 := po_dist_smul hn (γ₀ : PO n 1) (((γ₀ : PO n 1)⁻¹) • x) basepointH
    rw [smul_smul, mul_inv_cancel, one_smul] at h2
    exact h2.symm
  have e2 : dist (((γ₀ : PO n 1)⁻¹) • x) ((γ : PO n 1) • basepointH)
      = dist x (((γ₀ * γ : Γ) : PO n 1) • basepointH) := by
    have h2 := po_dist_smul hn (γ₀ : PO n 1) (((γ₀ : PO n 1)⁻¹) • x) ((γ : PO n 1) • basepointH)
    rw [smul_smul, mul_inv_cancel, one_smul] at h2
    rw [← h2, smul_smul, ← Subgroup.coe_mul]
  rw [e1, e2]
  exact hγ₀ (γ₀ * γ)

end DifferentialGeometry.DirichletDomain

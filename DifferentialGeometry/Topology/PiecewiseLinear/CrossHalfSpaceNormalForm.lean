/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConePairExtension
import DifferentialGeometry.Topology.PiecewiseLinear.CrossQuarterLink
import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeSphere
import DifferentialGeometry.Topology.PiecewiseLinear.LinkSection
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem fourSpokeModelLeaf_dot_nonpos {i j : Fin 4} (hij : i ≠ j) :
    (fourSpokeModelLeaf i).1 * (fourSpokeModelLeaf j).1 +
      (fourSpokeModelLeaf i).2 * (fourSpokeModelLeaf j).2 ≤ 0 := by
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
    rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hij
        | norm_num [fourSpokeModelLeaf]

theorem iUnion_crossQuarter :
    ⋃ i, crossQuarter i = {p : (ℝ × ℝ) × ℝ | p ∈ crossPlanes ∧ 0 ≤ p.2} := by
  ext p
  simp only [mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨i, a, b, ha, hb, rfl⟩
    refine ⟨?_, hb⟩
    change (a • fourSpokeModelLeaf i).1 = 0 ∨ (a • fourSpokeModelLeaf i).2 = 0
    rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;> simp [fourSpokeModelLeaf]
  · rintro ⟨hp | hp, hp2⟩
    · rcases le_total 0 p.1.2 with h | h
      · refine ⟨1, p.1.2, p.2, h, hp2, ?_⟩
        ext <;> simp [fourSpokeModelLeaf, hp]
      · refine ⟨3, -p.1.2, p.2, by linarith, hp2, ?_⟩
        ext <;> simp [fourSpokeModelLeaf, hp]
    · rcases le_total 0 p.1.1 with h | h
      · refine ⟨0, p.1.1, p.2, h, hp2, ?_⟩
        ext <;> simp [fourSpokeModelLeaf, hp]
      · refine ⟨2, -p.1.1, p.2, by linarith, hp2, ?_⟩
        ext <;> simp [fourSpokeModelLeaf, hp]

theorem crossQuarter_inter_crossQuarter {i j : Fin 4} (hij : i ≠ j) :
    crossQuarter i ∩ crossQuarter j = {p : (ℝ × ℝ) × ℝ | p.1 = 0 ∧ 0 ≤ p.2} := by
  ext p
  constructor
  · rintro ⟨⟨a, b, ha, hb, rfl⟩, ⟨a', b', ha', hb', h⟩⟩
    have h1 : a • fourSpokeModelLeaf i = a' • fourSpokeModelLeaf j := congrArg Prod.fst h
    have hdot := congrArg (fun x : ℝ × ℝ =>
      (fourSpokeModelLeaf i).1 * x.1 + (fourSpokeModelLeaf i).2 * x.2) h1
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hdot
    have hii := fourSpokeModelLeaf_dot_self i
    have hij' := fourSpokeModelLeaf_dot_nonpos hij
    have ha0 : a = 0 := by nlinarith
    refine ⟨?_, hb⟩
    change a • fourSpokeModelLeaf i = 0
    rw [ha0, zero_smul]
  · rintro ⟨h1, h2⟩
    refine ⟨⟨0, p.2, le_rfl, h2, ?_⟩, ⟨0, p.2, le_rfl, h2, ?_⟩⟩ <;>
      exact Prod.ext (by rw [h1, zero_smul]) rfl

theorem coneSet_geometricLink_eq_closedStar {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) {p : E}
    (hp : {p} ∈ K.faces) :
    coneSet p (SimplicialComplex.geometricLink K {p}).space = closedStar K p := by
  rw [closedStar_eq_coneComplex_space K hp, coneComplex_space_eq_coneSet]

theorem exists_quarterLink_sphere {G : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ}
    (hG : IsPLHomeomorphOn G univ univ)
    (hhom : ∀ v : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 ≤ s → G (s • v) = s • G v)
    (hpos : ∀ p ∈ crossPlanes, 0 ≤ p.2 → 0 ≤ (G p).2)
    (hzero : ∀ p ∈ crossPlanes, 0 ≤ p.2 → ((G p).2 = 0 ↔ p.2 = 0)) :
    ∃ (K : Geometry.SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) (m : Fin 4 → Set ((ℝ × ℝ) × ℝ))
      (β : Fin 4 → ℝ → (ℝ × ℝ) × ℝ) (c : (ℝ × ℝ) × ℝ) (uP uN : (Fin 3 → ℝ) → (ℝ × ℝ) × ℝ)
      (ρ : ℝ),
      K.faces.Finite ∧ ({0} : Finset ((ℝ × ℝ) × ℝ)) ∈ K.faces ∧ K.space ∈ 𝓝 0 ∧
      IsPLHomeomorphOn uP (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        ((SimplicialComplex.geometricLink K {0}).space ∩ {x | 0 ≤ x.2}) ∧
      IsPLHomeomorphOn uN (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        ((SimplicialComplex.geometricLink K {0}).space ∩ {x | x.2 ≤ 0}) ∧
      uP '' stdSimplexBoundary 2 =
        (SimplicialComplex.geometricLink K {0}).space ∩ {x | x.2 = 0} ∧
      uN '' stdSimplexBoundary 2 =
        (SimplicialComplex.geometricLink K {0}).space ∩ {x | x.2 = 0} ∧
      (∀ i, IsPLHomeomorphOn (β i) (Icc 0 1) (m i)) ∧ (∀ i, β i 0 = c) ∧
      (∀ i, m i ⊆ (SimplicialComplex.geometricLink K {0}).space ∩ {x | 0 ≤ x.2}) ∧
      (∀ i, m i ∩ {x | x.2 = 0} = {β i 1}) ∧ (∀ i j, i ≠ j → m i ∩ m j = {c}) ∧
      (∀ i, β i 1 ∈ G '' {p | ∃ a : ℝ, 0 < a ∧ p = (a • fourSpokeModelLeaf i, 0)}) ∧ 0 < ρ ∧
      (∀ z ∈ ball (0 : (ℝ × ℝ) × ℝ) ρ,
        z ∈ coneSet 0 (⋃ i, m i) ↔ z ∈ G '' {q | q ∈ crossPlanes ∧ 0 ≤ q.2}) ∧
      ∀ z ∈ ball (0 : (ℝ × ℝ) × ℝ) ρ,
        z ∈ coneSet 0 {c} ↔ z ∈ G '' {q | q.1 = 0 ∧ 0 ≤ q.2} := by
  classical
  obtain ⟨K, M, ρ₀, hKfin, h0K, hKn, hside, hMK, h0M, hMsub, hρ₀, hgerm, hβex⟩ :=
    exists_quarterLink_complex hG hhom
  choose β hβ hβ0 hβ1 using hβex
  have : Finite K.faces := hKfin.to_subtype
  have hMfin : ∀ i, Finite (M i).faces := fun i => (hKfin.subset (hMK i)).to_subtype
  have hG0 : G 0 = 0 := by simpa using hhom 0 0 le_rfl
  have hGinj : Function.Injective G := fun x y h => hG.bijOn.injOn (mem_univ x) (mem_univ y) h
  have hQX : ∀ i, crossQuarter i ⊆ {p | p ∈ crossPlanes ∧ 0 ≤ p.2} := fun i =>
    (subset_iUnion crossQuarter i).trans iUnion_crossQuarter.subset
  set Λ := (SimplicialComplex.geometricLink K {0}).space with hΛdef
  have hray : ∀ x ∈ Λ, ∀ y ∈ Λ, ∀ s : ℝ, 0 < s → y = s • x → y = x := by
    intro x hx y hy s hs h
    exact isRadiallyInjective_geometricLink K x hx y hy s hs (by rw [h, zero_add, sub_zero])
  have hmΛ : ∀ i, (SimplicialComplex.geometricLink (M i) {0}).space ⊆ Λ := by
    intro i
    apply space_mono_of_faces_subset
    intro t ht
    obtain ⟨hne, h0t, hins⟩ := (SimplicialComplex.mem_geometricLink_singleton (M i) 0 t).mp ht
    exact (SimplicialComplex.mem_geometricLink_singleton K 0 t).mpr ⟨hne, h0t, hMK i hins⟩
  have hmQ : ∀ i, (SimplicialComplex.geometricLink (M i) {0}).space ⊆ G '' crossQuarter i :=
    fun i => (space_mono_of_faces_subset (SimplicialComplex.geometricLink_le (M i) {0})).trans
      (hMsub i)
  have hm0 : ∀ i, (0 : (ℝ × ℝ) × ℝ) ∉ (SimplicialComplex.geometricLink (M i) {0}).space :=
    fun i => notMem_geometricLink_space (M i)
  have hβmem : ∀ i, ∀ x ∈ Icc (0 : ℝ) 1,
      β i x ∈ (SimplicialComplex.geometricLink (M i) {0}).space :=
    fun i x hx => (hβ i).bijOn.mapsTo hx
  have hsameray : ∀ x ∈ Λ, ∀ y ∈ Λ, ∀ q q' : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 < s → q' = s • q →
      x = G q → y = G q' → y = x := by
    intro x hx y hy q q' s hs hq' hx' hy'
    refine hray x hx y hy s hs ?_
    rw [hy', hq', hhom _ _ hs.le, hx']
  have hc : ∀ i, β i 0 = β 0 0 := by
    intro i
    obtain ⟨q, ⟨hq1, hq2⟩, hq⟩ := hβ0 0
    obtain ⟨q', ⟨hq1', hq2'⟩, hq'⟩ := hβ0 i
    refine hsameray _ (hmΛ 0 (hβmem 0 0 ⟨le_rfl, zero_le_one⟩)) _
      (hmΛ i (hβmem i 0 ⟨le_rfl, zero_le_one⟩)) q q' (q'.2 / q.2) (div_pos hq2' hq2) ?_
      hq.symm hq'.symm
    refine Prod.ext ?_ ?_
    · rw [hq1', Prod.smul_fst, hq1, smul_zero]
    · rw [Prod.smul_snd, smul_eq_mul, div_mul_cancel₀ _ hq2.ne']
  have hm2 : ∀ i, ∀ x ∈ (SimplicialComplex.geometricLink (M i) {0}).space, 0 ≤ x.2 := by
    intro i x hx
    obtain ⟨q, hq, rfl⟩ := hmQ i hx
    exact hpos q (hQX i hq).1 (hQX i hq).2
  have hmC : ∀ i, (SimplicialComplex.geometricLink (M i) {0}).space ∩ {x | x.2 = 0} =
      {β i 1} := by
    intro i
    obtain ⟨q₁, ⟨a₁, ha₁, hq₁⟩, hβq₁⟩ := hβ1 i
    have hq₁X : q₁ ∈ {p | p ∈ crossPlanes ∧ 0 ≤ p.2} :=
      hQX i ⟨a₁, 0, ha₁.le, le_rfl, hq₁⟩
    ext x
    constructor
    · rintro ⟨hx, hx2⟩
      obtain ⟨q, ⟨a, b, ha, hb, rfl⟩, rfl⟩ := hmQ i hx
      have hqX := hQX i ⟨a, b, ha, hb, rfl⟩
      have hb0 : b = 0 := (hzero _ hqX.1 hqX.2).mp hx2
      subst hb0
      have ha0 : 0 < a := by
        rcases ha.lt_or_eq with h | h
        · exact h
        · exfalso
          apply hm0 i
          rw [← h, zero_smul, Prod.mk_zero_zero, hG0] at hx
          exact hx
      refine mem_singleton_iff.mpr (hsameray _ (hmΛ i (hβmem i 1 ⟨zero_le_one, le_rfl⟩)) _
        (hmΛ i hx) q₁ _ (a / a₁) (div_pos ha0 ha₁) ?_ hβq₁.symm rfl)
      rw [hq₁]
      refine Prod.ext ?_ ?_
      · rw [Prod.smul_fst, smul_smul, div_mul_cancel₀ _ ha₁.ne']
      · rw [Prod.smul_snd, smul_zero]
    · rintro rfl
      refine ⟨hβmem i 1 ⟨zero_le_one, le_rfl⟩, ?_⟩
      change (β i 1).2 = 0
      rw [← hβq₁]
      exact (hzero _ hq₁X.1 hq₁X.2).mpr (by rw [hq₁])
  have hmm : ∀ i j, i ≠ j → (SimplicialComplex.geometricLink (M i) {0}).space ∩
      (SimplicialComplex.geometricLink (M j) {0}).space = {β 0 0} := by
    intro i j hij
    obtain ⟨qc, ⟨hqc1, hqc2⟩, hqc⟩ := hβ0 0
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      obtain ⟨q, hq, rfl⟩ := hmQ i hx
      obtain ⟨q', hq', hqq'⟩ := hmQ j hx'
      have hqq : q' = q := hGinj hqq'
      rw [hqq] at hq'
      have hax : q ∈ crossQuarter i ∩ crossQuarter j := ⟨hq, hq'⟩
      rw [crossQuarter_inter_crossQuarter hij] at hax
      have hq2 : 0 < q.2 := by
        rcases hax.2.lt_or_eq with h | h
        · exact h
        · exfalso
          apply hm0 i
          have hq0 : q = 0 := Prod.ext hax.1 h.symm
          rw [hq0, hG0] at hx
          exact hx
      refine mem_singleton_iff.mpr (hsameray _ (hmΛ 0 (hβmem 0 0 ⟨le_rfl, zero_le_one⟩)) _
        (hmΛ i hx) qc q (q.2 / qc.2) (div_pos hq2 hqc2) ?_ hqc.symm rfl)
      refine Prod.ext ?_ ?_
      · rw [hax.1, Prod.smul_fst, hqc1, smul_zero]
      · rw [Prod.smul_snd, smul_eq_mul, div_mul_cancel₀ _ hqc2.ne']
    · rintro rfl
      exact ⟨hc i ▸ hβmem i 0 ⟨le_rfl, zero_le_one⟩, hc j ▸ hβmem j 0 ⟨le_rfl, zero_le_one⟩⟩
  have hℓ : ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ ≠ 0 := by
    intro h
    have := congrArg (fun f : (ℝ × ℝ) × ℝ →L[ℝ] ℝ => f ((0, 0), 1)) h
    simp at this
  have hdim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 1 + 2 := by simp
  obtain ⟨uP, huP, hbP⟩ := exists_isPLHomeomorphOn_geometricLink_halfSpace hdim K h0K hKn
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) hℓ (by simp) hside
  obtain ⟨uN, huN, hbN⟩ := exists_isPLHomeomorphOn_geometricLink_halfSpace hdim K h0K hKn
    (-ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (neg_ne_zero.mpr hℓ) (by simp) (fun s hs =>
      (hside s hs).symm.imp (fun h x hx => by simpa using h hx) (fun h x hx => by simpa using h hx))
  have eN : Λ ∩ {x | 0 ≤ (-ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) x} = Λ ∩ {x | x.2 ≤ 0} := by
    ext x
    simp
  have eNb : Λ ∩ {x | (-ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) x = 0} = Λ ∩ {x | x.2 = 0} := by
    ext x
    simp
  rw [eN] at huN
  rw [eNb] at hbN
  have hcs : ∀ i, coneSet 0 (SimplicialComplex.geometricLink (M i) {0}).space =
      closedStar (M i) 0 := fun i => coneSet_geometricLink_eq_closedStar (M i) (h0M i)
  have hstar : ∀ i, ∃ O ∈ 𝓝 (0 : (ℝ × ℝ) × ℝ), O ∩ (M i).space ⊆ closedStar (M i) 0 := by
    intro i
    obtain ⟨O, hO, hOs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
      (closedStar_mem_nhdsWithin (M i) 0)
    exact ⟨O, hO, hOs⟩
  choose O hO hOs using hstar
  obtain ⟨ρ₁, hρ₁, hρ₁O⟩ := Metric.mem_nhds_iff.mp (Filter.iInter_mem.mpr hO)
  obtain ⟨qc, ⟨hqc1, hqc2⟩, hqc⟩ := hβ0 0
  have hc0 : β 0 0 ≠ 0 := fun h => hm0 0 (h ▸ hβmem 0 0 ⟨le_rfl, zero_le_one⟩)
  have hcn : 0 < ‖β 0 0‖ := norm_pos_iff.mpr hc0
  refine ⟨K, fun i => (SimplicialComplex.geometricLink (M i) {0}).space, β, β 0 0, uP, uN,
    min (min ρ₀ ρ₁) ‖β 0 0‖, hKfin, h0K, hKn, huP, huN, hbP, hbN, hβ, hc,
    fun i x hx => ⟨hmΛ i hx, hm2 i x hx⟩, hmC, hmm, fun i => (hβ1 i).imp fun q hq =>
      ⟨hq.1, hq.2⟩, lt_min (lt_min hρ₀ hρ₁) hcn, ?_, ?_⟩
  · intro z hz
    have hz₀ : z ∈ ball (0 : (ℝ × ℝ) × ℝ) ρ₀ :=
      ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hz
    have hz₁ : z ∈ ball (0 : (ℝ × ℝ) × ℝ) ρ₁ :=
      ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hz
    constructor
    · intro hzc
      rcases mem_coneSet_iff.mp hzc with rfl | ⟨x, hx, s, hs, -, rfl⟩
      · exact ⟨0, ⟨Or.inl rfl, le_rfl⟩, hG0⟩
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
        obtain ⟨q, hq, rfl⟩ := hmQ i hxi
        refine ⟨s • q, hQX i (smul_mem_crossQuarter hq hs.le), ?_⟩
        rw [hhom _ _ hs.le, zero_add, sub_zero]
    · rintro ⟨q, hqX, rfl⟩
      rw [← iUnion_crossQuarter] at hqX
      obtain ⟨i, hqi⟩ := mem_iUnion.mp hqX
      have hzM := hgerm i _ hz₀ ⟨q, hqi, rfl⟩
      have hzO : G q ∈ O i := mem_iInter.mp (hρ₁O hz₁) i
      have hzs := hOs i ⟨hzO, hzM⟩
      rw [← hcs i] at hzs
      exact coneSet_mono 0 (subset_iUnion
        (fun i => (SimplicialComplex.geometricLink (M i) {0}).space) i) hzs
  · intro z hz
    have hzc : ‖z‖ < ‖β 0 0‖ := by
      have := mem_ball_zero_iff.mp hz
      exact this.trans_le (min_le_right _ _)
    constructor
    · intro hzc'
      rcases mem_coneSet_iff.mp hzc' with rfl | ⟨x, hx, s, hs, -, rfl⟩
      · exact ⟨0, ⟨rfl, le_rfl⟩, hG0⟩
      · rw [mem_singleton_iff.mp hx, ← hqc]
        refine ⟨s • qc, ⟨by rw [Prod.smul_fst, hqc1, smul_zero], ?_⟩, ?_⟩
        · rw [Prod.smul_snd, smul_eq_mul]
          exact mul_nonneg hs.le hqc2.le
        · rw [hhom _ _ hs.le, zero_add, sub_zero]
    · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
      rcases hq2.lt_or_eq with hq2 | hq2
      · have hGq : G q = (q.2 / qc.2) • β 0 0 := by
          rw [← hqc, ← hhom _ _ (div_pos hq2 hqc2).le]
          congr 1
          refine Prod.ext ?_ ?_
          · rw [hq1, Prod.smul_fst, hqc1, smul_zero]
          · rw [Prod.smul_snd, smul_eq_mul, div_mul_cancel₀ _ hqc2.ne']
        have hs1 : q.2 / qc.2 ≤ 1 := by
          rw [hGq, norm_smul, Real.norm_of_nonneg (div_pos hq2 hqc2).le] at hzc
          have := (mul_lt_iff_lt_one_left hcn).mp hzc
          exact this.le
        exact Or.inr ⟨β 0 0, rfl, q.2 / qc.2, div_pos hq2 hqc2, hs1, by
          rw [hGq, zero_add, sub_zero]⟩
      · have hq0 : q = 0 := Prod.ext hq1 hq2.symm
        rw [hq0, hG0]
        exact apex_mem_coneSet 0 _

theorem isPLHomeomorphOn_id_univ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : IsPLHomeomorphOn (id : E → E) univ univ := by
  refine ⟨bijOn_id univ, (isPiecewiseAffineOn_of_affine (AffineMap.id ℝ E) isOpen_univ).congr
    fun x _ => rfl, (isPiecewiseAffineOn_of_affine (AffineMap.id ℝ E) isOpen_univ).congr
    fun x hx => ?_⟩
  change Function.invFunOn id univ x = x
  exact (bijOn_id univ).invOn_invFunOn.2 hx

theorem mem_coneSet_inter_snd_iff {S : Set ((ℝ × ℝ) × ℝ)} {z : (ℝ × ℝ) × ℝ}
    (hz : z ∈ coneSet 0 S) :
    (z ∈ coneSet 0 (S ∩ {x | 0 ≤ x.2}) ↔ 0 ≤ z.2) ∧
      (z ∈ coneSet 0 (S ∩ {x | x.2 = 0}) ↔ z.2 = 0) := by
  rcases mem_coneSet_iff.mp hz with rfl | ⟨x, hx, s, hs, hs1, rfl⟩
  · exact ⟨iff_of_true (apex_mem_coneSet 0 _) le_rfl,
      iff_of_true (apex_mem_coneSet 0 _) rfl⟩
  · have hz2 : (0 + s • (x - 0)).2 = s * x.2 := by
      rw [zero_add, sub_zero, Prod.smul_snd, smul_eq_mul]
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
    · rcases mem_coneSet_iff.mp h with h0 | ⟨y, hy, t, ht, -, hyt⟩
      · rw [h0]
        simp
      · rw [hyt, zero_add, sub_zero, Prod.smul_snd, smul_eq_mul]
        exact mul_nonneg ht.le hy.2
    · rw [hz2] at h
      exact Or.inr ⟨x, ⟨hx, nonneg_of_mul_nonneg_right h hs⟩, s, hs, hs1, rfl⟩
    · rcases mem_coneSet_iff.mp h with h0 | ⟨y, hy, t, ht, -, hyt⟩
      · rw [h0]
        rfl
      · rw [hyt, zero_add, sub_zero, Prod.smul_snd, smul_eq_mul, hy.2, mul_zero]
    · rw [hz2] at h
      exact Or.inr ⟨x, ⟨hx, (mul_eq_zero.mp h).resolve_left hs.ne'⟩, s, hs, hs1, rfl⟩

theorem image_smul_mem_iff {G : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ}
    (hhom : ∀ v : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 ≤ s → G (s • v) = s • G v) {S : Set ((ℝ × ℝ) × ℝ)}
    (hS : ∀ v : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 < s → (s • v ∈ S ↔ v ∈ S)) (w : (ℝ × ℝ) × ℝ) {s : ℝ}
    (hs : 0 < s) : s • w ∈ G '' S ↔ w ∈ G '' S := by
  constructor
  · rintro ⟨q, hq, hqw⟩
    refine ⟨s⁻¹ • q, (hS q s⁻¹ (inv_pos.mpr hs)).mpr hq, ?_⟩
    rw [hhom _ _ (inv_pos.mpr hs).le, hqw, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  · rintro ⟨q, hq, rfl⟩
    exact ⟨s • q, (hS q s hs).mpr hq, hhom _ _ hs.le⟩

theorem exists_homogeneous_normalForm_crossHalfSpace {G : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ}
    (hG : IsPLHomeomorphOn G univ univ)
    (hhom : ∀ v : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 ≤ s → G (s • v) = s • G v)
    (hpos : ∀ p ∈ crossPlanes, 0 ≤ p.2 → 0 ≤ (G p).2)
    (hzero : ∀ p ∈ crossPlanes, 0 ≤ p.2 → ((G p).2 = 0 ↔ p.2 = 0)) :
    ∃ Θ : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ, IsPLHomeomorphOn Θ univ univ ∧ Θ 0 = 0 ∧
      (∀ v : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 ≤ s → Θ (s • v) = s • Θ v) ∧
      (∀ p, Θ p ∈ G '' {q | q ∈ crossPlanes ∧ 0 ≤ q.2} ↔ p ∈ crossPlanes ∧ 0 ≤ p.2) ∧
      (∀ p, Θ p ∈ G '' {q | q.1 = 0 ∧ 0 ≤ q.2} ↔ p.1 = 0 ∧ 0 ≤ p.2) ∧
      (∀ p, 0 ≤ (Θ p).2 ↔ 0 ≤ p.2) ∧ ∀ p, (Θ p).2 = 0 ↔ p.2 = 0 := by
  classical
  obtain ⟨K₁, m₁, β₁, c₁, uP₁, uN₁, ρ₁, hK₁fin, h0K₁, hK₁n, huP₁, huN₁, hbP₁, hbN₁, hβ₁, hβ₁c,
    hm₁, hm₁C, hm₁m, hβ₁1, hρ₁, hg₁X, hg₁A⟩ := exists_quarterLink_sphere
      isPLHomeomorphOn_id_univ (fun _ _ _ => rfl) (fun _ _ hp => hp) (fun _ _ _ => Iff.rfl)
  obtain ⟨K₂, m₂, β₂, c₂, uP₂, uN₂, ρ₂, hK₂fin, h0K₂, hK₂n, huP₂, huN₂, hbP₂, hbN₂, hβ₂, hβ₂c,
    hm₂, hm₂C, hm₂m, -, hρ₂, hg₂X, hg₂A⟩ := exists_quarterLink_sphere hG hhom hpos hzero
  have hleaf : ∀ i, ∃ a : ℝ, 0 < a ∧ β₁ i 1 = (a • fourSpokeModelLeaf i, 0) := by
    intro i
    obtain ⟨q, ⟨a, ha, hq⟩, hq'⟩ := hβ₁1 i
    exact ⟨a, ha, by rw [← hq', ← hq]; rfl⟩
  have hΛ₁ : ∀ i, β₁ i 1 ∈ (SimplicialComplex.geometricLink K₁ {0}).space := fun i =>
    (hm₁ i ((hβ₁ i).bijOn.mapsTo ⟨zero_le_one, le_rfl⟩)).1
  have hsep : (SimplicialComplex.geometricLink K₁ {0}).space ∩ {x | x.2 = 0} ∩
      {x : (ℝ × ℝ) × ℝ | x.1.2 = 0} = {β₁ 0 1, β₁ 2 1} := by
    obtain ⟨a₀, ha₀, e₀⟩ := hleaf 0
    obtain ⟨a₂, ha₂, e₂⟩ := hleaf 2
    ext x
    constructor
    · rintro ⟨⟨hx, hx2⟩, hx12⟩
      have hx2' : x.2 = 0 := hx2
      have hx12' : x.1.2 = 0 := hx12
      have hx0 : x ≠ 0 := fun h => notMem_geometricLink_space K₁ (h ▸ hx)
      have hx11 : x.1.1 ≠ 0 := fun h => hx0 (Prod.ext (Prod.ext h hx12') hx2')
      rcases lt_or_gt_of_ne hx11 with h | h
      · right
        refine isRadiallyInjective_geometricLink K₁ _ (hΛ₁ 2) x hx (-x.1.1 / a₂)
          (div_pos (neg_pos.mpr h) ha₂) ?_
        rw [zero_add, sub_zero, e₂]
        refine Prod.ext (Prod.ext ?_ ?_) ?_
        · simp only [Prod.smul_fst, smul_eq_mul, fourSpokeModelLeaf]
          field_simp
        · simp [fourSpokeModelLeaf, hx12']
        · simp [hx2']
      · left
        refine isRadiallyInjective_geometricLink K₁ _ (hΛ₁ 0) x hx (x.1.1 / a₀)
          (div_pos h ha₀) ?_
        rw [zero_add, sub_zero, e₀]
        refine Prod.ext (Prod.ext ?_ ?_) ?_
        · simp only [Prod.smul_fst, smul_eq_mul, fourSpokeModelLeaf]
          field_simp
        · simp [fourSpokeModelLeaf, hx12']
        · simp [hx2']
    · rintro (rfl | rfl)
      · refine ⟨⟨hΛ₁ 0, ?_⟩, ?_⟩
        · change (β₁ 0 1).2 = 0
          rw [e₀]
        · change (β₁ 0 1).1.2 = 0
          rw [e₀]
          simp [fourSpokeModelLeaf]
      · refine ⟨⟨hΛ₁ 2, ?_⟩, ?_⟩
        · change (β₁ 2 1).2 = 0
          rw [e₂]
        · change (β₁ 2 1).1.2 = 0
          rw [e₂]
          simp [fourSpokeModelLeaf]
  have hpos₁ : 0 < (β₁ 1 1).1.2 := by
    obtain ⟨a, ha, e⟩ := hleaf 1
    rw [e]
    simpa [fourSpokeModelLeaf] using ha
  have hneg₃ : (β₁ 3 1).1.2 < 0 := by
    obtain ⟨a, ha, e⟩ := hleaf 3
    rw [e]
    simpa [fourSpokeModelLeaf] using ha
  obtain ⟨φ, hφ, hφP, hφC, hφm, hφc⟩ := exists_isPLHomeomorphOn_fourSpokeSphere
    (t := fun x : (ℝ × ℝ) × ℝ => x.2) (t' := fun x : (ℝ × ℝ) × ℝ => x.2)
    (ℓ := fun x : (ℝ × ℝ) × ℝ => x.1.2) (continuous_snd.comp continuous_fst)
    huP₁ huN₁ hbP₁ hbN₁ huP₂ huN₂ hbP₂ hbN₂ hβ₁ hβ₁c hm₁ hm₁C hm₁m hsep hpos₁ hneg₃ hβ₂ hβ₂c
    hm₂ hm₂C hm₂m
  have : Finite (SimplicialComplex.geometricLink K₁ {0}).faces :=
    (hK₁fin.subset (SimplicialComplex.geometricLink_le K₁ {0})).to_subtype
  have : Finite (SimplicialComplex.geometricLink K₂ {0}).faces :=
    (hK₂fin.subset (SimplicialComplex.geometricLink_le K₂ {0})).to_subtype
  obtain ⟨g, hg, -, hg0, -, hgcone⟩ := exists_isPLHomeomorphOn_coneComplex_pair
    (isConeBase_geometricLink K₁ (p := 0)) (isConeBase_geometricLink K₂ (p := 0)) hφ
  rw [coneComplex_space_eq_coneSet, coneComplex_space_eq_coneSet] at hg
  have hS₁n : coneSet 0 (SimplicialComplex.geometricLink K₁ {0}).space ∈
      𝓝 (0 : (ℝ × ℝ) × ℝ) := by
    rw [coneSet_geometricLink_eq_closedStar K₁ h0K₁]
    have : Finite K₁.faces := hK₁fin.to_subtype
    have h := closedStar_mem_nhdsWithin K₁ (0 : (ℝ × ℝ) × ℝ)
    rwa [nhdsWithin_eq_nhds.mpr hK₁n] at h
  set U := interior (coneSet 0 (SimplicialComplex.geometricLink K₁ {0}).space) with hUdef
  have hU : IsOpen U := isOpen_interior
  have h0U : (0 : (ℝ × ℝ) × ℝ) ∈ U := mem_interior_iff_mem_nhds.mpr hS₁n
  have hUsub : U ⊆ coneSet 0 (SimplicialComplex.geometricLink K₁ {0}).space := interior_subset
  have hgU : IsOpen (g '' U) := invariance_of_domain_isOpen_image_of_finrank_eq rfl hU
    (hg.isPiecewiseAffineOn.continuousOn.mono hUsub) (hg.bijOn.injOn.mono hUsub)
  obtain ⟨Θ, ρ₀, hρ₀, hρ₀U, hΘ, hΘg, hΘhom⟩ :=
    (hg.restrict_isOpen hU hUsub hgU).exists_isPLHomeomorphOn_univ_homogeneous hU hgU h0U
  have hΘ0 : Θ 0 = 0 := by rw [hΘg (mem_ball_self hρ₀), hg0]
  have hΘhom' : ∀ v : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 ≤ s → Θ (s • v) = s • Θ v := by
    intro v s hs
    simpa [hΘ0] using hΘhom v s hs
  have hgc : ContinuousAt g 0 := (hg.isPiecewiseAffineOn.continuousOn 0
    (mem_of_mem_nhds hS₁n)).continuousAt hS₁n
  obtain ⟨ρ₃, hρ₃, hρ₃g⟩ := Metric.mem_nhds_iff.mp
    (hgc.preimage_mem_nhds (by rw [hg0]; exact ball_mem_nhds 0 hρ₂))
  obtain ⟨ρ₄, hρ₄, hρ₄S⟩ := Metric.mem_nhds_iff.mp hS₁n
  set ρ := min (min ρ₀ ρ₁) (min ρ₃ ρ₄) with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hρ₀ hρ₁) (lt_min hρ₃ hρ₄)
  have hball : ∀ z ∈ ball (0 : (ℝ × ℝ) × ℝ) ρ,
      Θ z = g z ∧ z ∈ ball (0 : (ℝ × ℝ) × ℝ) ρ₁ ∧ g z ∈ ball (0 : (ℝ × ℝ) × ℝ) ρ₂ ∧
        z ∈ coneSet 0 (SimplicialComplex.geometricLink K₁ {0}).space := by
    intro z hz
    have h₀ := ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hz
    have h₁ := ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hz
    have h₃ := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz
    have h₄ := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hz
    exact ⟨hΘg h₀, h₁, hρ₃g h₃, hρ₄S h₄⟩
  have hcone : ∀ X ⊆ (SimplicialComplex.geometricLink K₁ {0}).space,
      ∀ z ∈ coneSet 0 (SimplicialComplex.geometricLink K₁ {0}).space,
        z ∈ coneSet 0 X ↔ g z ∈ coneSet 0 (φ '' X) := by
    intro X hX z hz
    rw [← hgcone X hX]
    constructor
    · exact fun h => mem_image_of_mem g h
    · rintro ⟨w, hw, hwz⟩
      rwa [← hg.bijOn.injOn (coneSet_mono 0 hX hw) hz hwz]
  have hm₁sub : (⋃ i, m₁ i) ⊆ (SimplicialComplex.geometricLink K₁ {0}).space :=
    iUnion_subset fun i x hx => (hm₁ i hx).1
  have hc₁sub : ({c₁} : Set ((ℝ × ℝ) × ℝ)) ⊆ (SimplicialComplex.geometricLink K₁ {0}).space := by
    rw [singleton_subset_iff, ← hβ₁c 0]
    exact (hm₁ 0 ((hβ₁ 0).bijOn.mapsTo ⟨le_rfl, zero_le_one⟩)).1
  have hlocX : ∀ z ∈ ball (0 : (ℝ × ℝ) × ℝ) ρ,
      z ∈ {q : (ℝ × ℝ) × ℝ | q ∈ crossPlanes ∧ 0 ≤ q.2} ↔
        Θ z ∈ G '' {q | q ∈ crossPlanes ∧ 0 ≤ q.2} := by
    intro z hz
    obtain ⟨hΘz, hz₁, hgz, hzS⟩ := hball z hz
    rw [hΘz, ← hg₂X _ hgz, ← hφm, ← hcone _ hm₁sub z hzS, hg₁X z hz₁, image_id]
  have hlocA : ∀ z ∈ ball (0 : (ℝ × ℝ) × ℝ) ρ,
      z ∈ {q : (ℝ × ℝ) × ℝ | q.1 = 0 ∧ 0 ≤ q.2} ↔ Θ z ∈ G '' {q | q.1 = 0 ∧ 0 ≤ q.2} := by
    intro z hz
    obtain ⟨hΘz, hz₁, hgz, hzS⟩ := hball z hz
    rw [hΘz, ← hg₂A _ hgz, ← hφc, ← image_singleton, ← hcone _ hc₁sub z hzS, hg₁A z hz₁,
      image_id]
  have hΛ₁sub : ∀ H : Set ((ℝ × ℝ) × ℝ), (SimplicialComplex.geometricLink K₁ {0}).space ∩ H ⊆
      (SimplicialComplex.geometricLink K₁ {0}).space := fun H => inter_subset_left
  have hlocP : ∀ z ∈ ball (0 : (ℝ × ℝ) × ℝ) ρ,
      z ∈ {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2} ↔ Θ z ∈ {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2} := by
    intro z hz
    obtain ⟨hΘz, -, -, hzS⟩ := hball z hz
    have hgzS := hg.bijOn.mapsTo hzS
    change 0 ≤ z.2 ↔ 0 ≤ (Θ z).2
    rw [hΘz, ← (mem_coneSet_inter_snd_iff hzS).1, ← (mem_coneSet_inter_snd_iff hgzS).1,
      ← hφP, ← hcone _ (hΛ₁sub _) z hzS]
  have hlocZ : ∀ z ∈ ball (0 : (ℝ × ℝ) × ℝ) ρ,
      z ∈ {q : (ℝ × ℝ) × ℝ | q.2 = 0} ↔ Θ z ∈ {q : (ℝ × ℝ) × ℝ | q.2 = 0} := by
    intro z hz
    obtain ⟨hΘz, -, -, hzS⟩ := hball z hz
    have hgzS := hg.bijOn.mapsTo hzS
    change z.2 = 0 ↔ (Θ z).2 = 0
    rw [hΘz, ← (mem_coneSet_inter_snd_iff hzS).2, ← (mem_coneSet_inter_snd_iff hgzS).2,
      ← hφC, ← hcone _ (hΛ₁sub _) z hzS]
  have hXcone : ∀ v : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 < s →
      (s • v ∈ {q : (ℝ × ℝ) × ℝ | q ∈ crossPlanes ∧ 0 ≤ q.2} ↔
        v ∈ {q : (ℝ × ℝ) × ℝ | q ∈ crossPlanes ∧ 0 ≤ q.2}) := by
    intro v s hs
    change ((s • v).1.1 = 0 ∨ (s • v).1.2 = 0) ∧ 0 ≤ (s • v).2 ↔
      (v.1.1 = 0 ∨ v.1.2 = 0) ∧ 0 ≤ v.2
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_eq_zero, hs.ne', false_or]
    rw [mul_nonneg_iff_of_pos_left hs]
  have hAcone : ∀ v : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 < s →
      (s • v ∈ {q : (ℝ × ℝ) × ℝ | q.1 = 0 ∧ 0 ≤ q.2} ↔
        v ∈ {q : (ℝ × ℝ) × ℝ | q.1 = 0 ∧ 0 ≤ q.2}) := by
    intro v s hs
    change (s • v).1 = 0 ∧ 0 ≤ (s • v).2 ↔ v.1 = 0 ∧ 0 ≤ v.2
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_zero, hs.ne', false_or, smul_eq_mul]
    rw [mul_nonneg_iff_of_pos_left hs]
  have hPcone : ∀ v : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 < s →
      (s • v ∈ {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2} ↔ v ∈ {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2}) := by
    intro v s hs
    change 0 ≤ (s • v).2 ↔ 0 ≤ v.2
    rw [Prod.smul_snd, smul_eq_mul, mul_nonneg_iff_of_pos_left hs]
  have hZcone : ∀ v : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 < s →
      (s • v ∈ {q : (ℝ × ℝ) × ℝ | q.2 = 0} ↔ v ∈ {q : (ℝ × ℝ) × ℝ | q.2 = 0}) := by
    intro v s hs
    change (s • v).2 = 0 ↔ v.2 = 0
    rw [Prod.smul_snd, smul_eq_mul, mul_eq_zero, or_iff_right hs.ne']
  have glob : ∀ (S S' : Set ((ℝ × ℝ) × ℝ)),
      (∀ v : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 < s → (s • v ∈ S ↔ v ∈ S)) →
      (∀ v : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 < s → (s • v ∈ S' ↔ v ∈ S')) →
      (∀ z ∈ ball (0 : (ℝ × ℝ) × ℝ) ρ, z ∈ S ↔ Θ z ∈ S') → ∀ z, z ∈ S ↔ Θ z ∈ S' := by
    intro S S' hS hS' hloc z
    refine forall_mem_iff_of_homogeneous hΘhom (fun v t ht => ?_) (fun w t ht => ?_) hρ hloc z
    · rw [zero_add, zero_add]
      exact hS v t ht
    · rw [hΘ0, zero_add, zero_add]
      exact hS' w t ht
  refine ⟨Θ, hΘ, hΘ0, hΘhom', fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_⟩
  · exact (glob _ _ hXcone (image_smul_mem_iff hhom hXcone) hlocX p).symm
  · exact (glob _ _ hAcone (image_smul_mem_iff hhom hAcone) hlocA p).symm
  · exact (glob _ _ hPcone hPcone hlocP p).symm
  · exact (glob _ _ hZcone hZcone hlocZ p).symm

end DifferentialGeometry.Topology.PiecewiseLinear

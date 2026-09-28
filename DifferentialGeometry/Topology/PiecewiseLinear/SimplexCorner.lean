/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeHalfSpace
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexAvoiding
import DifferentialGeometry.Topology.PiecewiseLinear.OpenStar
import Mathlib.Analysis.Normed.Module.Convex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem simplexAvoiding_erase_eq_starComplex [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) {a : E} (ha : a ∈ T) :
    simplexAvoiding T hT {T.erase a} = starComplex (simplexBoundary T hT) a := by
  ext s
  constructor
  · rintro ⟨hne, hsT, havoid⟩
    have hF : ¬ T.erase a ⊆ s := havoid _ (Finset.mem_singleton_self _)
    refine ⟨⟨hsT, hne, fun h => hF (h ▸ Finset.erase_subset a T)⟩,
      Finset.insert_subset ha hsT, Finset.insert_nonempty a s, ?_⟩
    intro h
    apply hF
    intro v hv
    have hvi : v ∈ insert a s := h ▸ Finset.mem_of_mem_erase hv
    exact (Finset.mem_insert.mp hvi).resolve_left (Finset.ne_of_mem_erase hv)
  · rintro ⟨hs, hsa⟩
    refine ⟨hs.2.1, hs.1, ?_⟩
    simp only [Finset.mem_singleton, forall_eq]
    intro hF
    apply hsa.2.2
    apply Finset.Subset.antisymm hsa.1
    intro v hv
    by_cases hva : v = a
    · exact Finset.mem_insert.mpr (Or.inl hva)
    · exact Finset.mem_insert_of_mem (hF (Finset.mem_erase.mpr ⟨hva, hv⟩))

theorem simplexBoundary_erase_faces_subset_simplexAvoiding [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (a : E) :
    (simplexBoundary (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T))).faces ⊆
      (simplexAvoiding T hT {T.erase a}).faces := by
  rintro s ⟨hsF, hne, hsne⟩
  refine ⟨hne, hsF.trans (Finset.erase_subset a T), ?_⟩
  simp only [Finset.mem_singleton, forall_eq]
  exact fun h => hsne (Finset.Subset.antisymm hsF h)

theorem simplexAvoiding_space_inter_convexHull_erase [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (a : E) :
    (simplexAvoiding T hT {T.erase a}).space ∩ convexHull ℝ ((T.erase a : Finset E) : Set E) =
      (simplexBoundary (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T))).space
          := by
  apply Subset.antisymm
  · rintro x ⟨hxL, hxF⟩
    obtain ⟨s, hs, hxs⟩ := (simplexAvoiding T hT {T.erase a}).mem_space_iff.mp hxL
    have hxinter : x ∈ convexHull ℝ ((s ∩ T.erase a : Finset E) : Set E) := by
      rw [Finset.coe_inter]
      exact convexHull_inter_subset_of_affineIndependent hT hs.2.1 (Finset.erase_subset a T) ⟨hxs,
          hxF⟩
    have hne : (s ∩ T.erase a).Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.coe_empty, convexHull_empty] at hxinter
      exact hxinter
    refine (simplexBoundary (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a
        T))).convexHull_subset_space
      ⟨Finset.inter_subset_right, hne, ?_⟩ hxinter
    intro he
    exact hs.2.2 _ (Finset.mem_singleton_self _) (he ▸ Finset.inter_subset_left)
  · intro x hx
    refine ⟨space_mono_of_faces_subset (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a)
        hx, ?_⟩
    exact simplexComplex_space_subset _ _
      (space_mono_of_faces_subset (simplexBoundary_faces_subset_simplexComplex _ _) hx)

theorem simplexBoundary_space_eq_starComplex_union_opposite_face [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card)
    {a : E} (ha : a ∈ T) :
    (simplexBoundary T hT).space = (starComplex (simplexBoundary T hT) a).space ∪
      convexHull ℝ ((T.erase a : Finset E) : Set E) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := (simplexBoundary T hT).mem_space_iff.mp hx
    by_cases has : a ∈ s
    · exact Or.inl ((starComplex (simplexBoundary T hT) a).convexHull_subset_space
        ⟨hs, by rwa [Finset.insert_eq_of_mem has]⟩ hxs)
    · exact Or.inr (convexHull_mono
        (Finset.coe_subset.mpr (Finset.subset_erase.mpr ⟨hs.1, has⟩)) hxs)
  · apply union_subset (space_mono_of_faces_subset (starComplex_faces_subset _ _))
    exact (simplexBoundary T hT).convexHull_subset_space
      (erase_mem_simplexBoundary_faces hT hcard ha)

theorem avoidingUnion_simplexBoundary_eq_convexHull_erase [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card)
    {a : E} (ha : a ∈ T) :
    avoidingUnion (simplexBoundary T hT) a = convexHull ℝ ((T.erase a : Finset E) : Set E) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, ⟨hs, has⟩, hxs⟩ := mem_iUnion₂.mp hx
    exact convexHull_mono (Finset.coe_subset.mpr (Finset.subset_erase.mpr ⟨hs.1, has⟩)) hxs
  · intro x hx
    exact mem_iUnion₂.mpr ⟨T.erase a,
      ⟨erase_mem_simplexBoundary_faces hT hcard ha, Finset.notMem_erase a T⟩, hx⟩

theorem openStar_simplexBoundary_eq_sdiff_boundary [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card)
    {a : E} (ha : a ∈ T) :
    openStar (simplexBoundary T hT) a = (starComplex (simplexBoundary T hT) a).space \
      (simplexBoundary (T.erase a)
        (affineIndependent_of_subset hT (Finset.erase_subset a T))).space := by
  have hinter := simplexAvoiding_space_inter_convexHull_erase T hT a
  rw [simplexAvoiding_erase_eq_starComplex T hT ha] at hinter
  rw [openStar, avoidingUnion_simplexBoundary_eq_convexHull_erase T hT hcard ha,
    simplexBoundary_space_eq_starComplex_union_opposite_face T hT hcard ha, ← hinter]
  ext x
  simp only [mem_sdiff, mem_union, mem_inter_iff]
  tauto

theorem exists_simplex_vertex_star_face_convexHull_subset [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (a : E)
    {s : Finset E} (hs : s.Nonempty)
    (hsub : convexHull ℝ (s : Set E) ⊆ openStar (simplexBoundary T hT) a) :
    ∃ t ∈ (starComplex (simplexBoundary T hT) a).faces,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  have hcent : s.centroid ℝ id ∈ openSimplex s := centroid_mem_openSimplex hs
  have hx := hsub (openSimplex_subset_convexHull s hcent)
  obtain ⟨t, ht, hxt⟩ := (simplexBoundary T hT).mem_space_iff.mp hx.1
  have hat : a ∈ t := by
    by_contra hat
    exact hx.2 (mem_iUnion₂.mpr ⟨t, ⟨ht, hat⟩, hxt⟩)
  have hBC : (simplexBoundary T hT).space ⊆ convexHull ℝ (T : Set E) :=
    (space_mono_of_faces_subset (simplexBoundary_faces_subset_simplexComplex T hT)).trans
      (simplexComplex_space_subset T hT)
  have hsT : (s : Set E) ⊆ convexHull ℝ (T : Set E) :=
    fun x hx => hBC (hsub (subset_convexHull ℝ _ hx)).1
  refine ⟨t, ⟨ht, by rwa [Finset.insert_eq_of_mem hat]⟩, ?_⟩
  exact convexHull_min (subset_convexHull_of_mem_openSimplex hT ht.1 hsT hcent hxt)
    (convex_convexHull ℝ _)

open Classical in
theorem exists_isConeBase_simplexAvoiding_near_vertex [FiniteDimensional ℝ E] [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card)
    {a : E} (ha : a ∈ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : E, dist p a < ε ∧ dist q a < ε ∧ p ∈ openSimplex T ∧
      q ∉ convexHull ℝ (T : Set E) ∧
      AffineIndependent ℝ ((↑) : ↥(insert q (T.erase a) : Finset E) → E) ∧
      a ∈ openSimplex (insert q (T.erase a)) ∧
      ∃ (hp : IsConeBase p (simplexAvoiding T hT {T.erase a}))
        (hq : IsConeBase q (simplexAvoiding T hT {T.erase a})),
        (coneComplex hp).space ∩ (coneComplex hq).space = (simplexAvoiding T hT {T.erase a}).space ∧
        (coneComplex hp).space ⊆ convexHull ℝ (T : Set E) ∧
        (coneComplex hq).space ∩ convexHull ℝ (T : Set E) =
          (simplexAvoiding T hT {T.erase a}).space := by
  have hne : (T.erase a).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem ha]
    omega
  have : Nonempty (T.erase a) := hne.to_subtype
  choose A hA using fun i : T.erase a =>
    exists_affineMap_eqOn hT (fun v => if v = (i : E) then (1 : ℝ) else 0)
  have hcoord (x : E) (hx : x ∈ convexHull ℝ (T : Set E)) (i : T.erase a) :
      A i x = weights T x i := by
    calc A i x = A i (∑ v ∈ T, weights T x v • v) := congrArg (A i) (sum_weights_smul hx).symm
      _ = ∑ v ∈ T, weights T x v • A i v := affineMap_apply_sum_smul _ (sum_weights hx)
      _ = ∑ v ∈ T, weights T x v • (if v = (i : E) then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun v hv => by rw [hA i v hv]
      _ = weights T x i := by simp [Finset.mem_of_mem_erase i.2]
  have hAa (i : T.erase a) : A i a = 0 := by
    rw [hA i a ha, ite_eq_right (Finset.ne_of_mem_erase i.2).symm]
  let c := T.centroid ℝ id
  have hc : c ∈ openSimplex T := centroid_mem_openSimplex (Finset.card_pos.mp (by omega))
  have hcT : c ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull _ hc
  have hcpos (i : T.erase a) : 0 < A i c := by
    rw [hcoord c hcT i]
    exact (mem_openSimplex_self_iff hT hcT).mp hc i (Finset.mem_of_mem_erase i.2)
  let t : ℝ := min (1 / 2) (ε / (‖c - a‖ + 1))
  have hn : 0 < ‖c - a‖ + 1 := by positivity
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε hn)
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have htε : t * ‖c - a‖ < ε := by
    have h := (le_div_iff₀ hn).mp (min_le_right (1 / 2) (ε / (‖c - a‖ + 1)))
    change t * (‖c - a‖ + 1) ≤ ε at h
    nlinarith
  let p := a + t • (c - a)
  let q := a + (-t) • (c - a)
  have hpdist : dist p a < ε := by
    simpa only [p, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        using htε
  have hqdist : dist q a < ε := by
    simpa only [q, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos ht] using htε
  have haT : a ∈ convexHull ℝ (T : Set E) := subset_convexHull ℝ _ ha
  have hpT : p ∈ convexHull ℝ (T : Set E) := by
    dsimp [p]
    rw [add_smul_sub_eq_combo]
    exact (convex_convexHull ℝ _) haT hcT (sub_nonneg.mpr ht1) ht.le (by ring)
  have hpopen : p ∈ openSimplex T := by
    apply (mem_openSimplex_self_iff hT hpT).mpr
    intro v hv
    have hw := weights_combo hT haT hcT (sub_nonneg.mpr ht1) ht.le (by ring : 1 - t + t = 1) v hv
    rw [← add_smul_sub_eq_combo] at hw
    change weights T p v = _ at hw
    rw [hw]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht1) (weights_nonneg haT hv))
      (mul_pos ht ((mem_openSimplex_self_iff hT hcT).mp hc v hv))
  have hpA (i : T.erase a) : 0 < A i p := by
    dsimp [p]
    rw [affineMap_apply_add_smul_sub, hAa, zero_add, sub_zero]
    exact mul_pos ht (hcpos i)
  have hqA (i : T.erase a) : A i q < 0 := by
    dsimp [q]
    rw [affineMap_apply_add_smul_sub, hAa, zero_add, sub_zero]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos ht) (hcpos i)
  have hnonneg (x : E) (hx : x ∈ convexHull ℝ (T : Set E)) (i : T.erase a) : 0 ≤ A i x := by
    rw [hcoord x hx i]
    exact weights_nonneg hx (Finset.mem_of_mem_erase i.2)
  have hqT : q ∉ convexHull ℝ (T : Set E) := by
    obtain ⟨i⟩ := ‹Nonempty (T.erase a)›
    exact fun hq => not_lt_of_ge (hnonneg q hq i) (hqA i)
  obtain ⟨A₀, hA₀⟩ := exists_affineMap_eqOn hT (fun v => if v = a then (1 : ℝ) else 0)
  have hA₀a : A₀ a = 1 := by simpa using hA₀ a ha
  have hA₀c : A₀ c = weights T c a := by
    calc A₀ c = A₀ (∑ v ∈ T, weights T c v • v) := congrArg A₀ (sum_weights_smul hcT).symm
      _ = ∑ v ∈ T, weights T c v • A₀ v := affineMap_apply_sum_smul _ (sum_weights hcT)
      _ = ∑ v ∈ T, weights T c v • (if v = a then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun v hv => by rw [hA₀ v hv]
      _ = weights T c a := by simp [ha]
  have hwa : weights T c a ≤ 1 := by
    rw [← sum_weights hcT]
    exact Finset.single_le_sum (fun v hv => weights_nonneg hcT hv) ha
  let β := A₀ q
  have hβ : β = 1 + t - t * weights T c a := by
    dsimp [β, q]
    rw [affineMap_apply_add_smul_sub, hA₀a, hA₀c]
    ring
  have hβpos : 0 < β := by rw [hβ]; nlinarith
  have hqF : q ∉ T.erase a := fun hqmem => hqT
    (subset_convexHull ℝ _ (Finset.mem_of_mem_erase hqmem))
  have hqind : AffineIndependent ℝ ((↑) : ↥(insert q (T.erase a) : Finset E) → E) := by
    apply (affineIndependent_insert_iff hqF
      (affineIndependent_of_subset hT (Finset.erase_subset a T))).mpr
    rintro ⟨w, hw, hwq⟩
    have hzero : A₀ q = 0 := by
      rw [← hwq, affineMap_apply_sum_smul _ hw]
      apply Finset.sum_eq_zero
      intro v hv
      rw [hA₀ v (Finset.mem_of_mem_erase hv), ite_eq_right (Finset.ne_of_mem_erase hv), smul_zero]
    exact hβpos.ne' hzero
  have hsumF : ∑ v ∈ T.erase a, weights T c v = 1 - weights T c a := by
    have h := Finset.add_sum_erase T (weights T c) ha
    rw [sum_weights hcT] at h
    linarith
  have hsmulF : ∑ v ∈ T.erase a, weights T c v • v = c - weights T c a • a := by
    rw [eq_sub_iff_add_eq, add_comm, Finset.add_sum_erase T (fun v => weights T c v • v) ha,
        sum_weights_smul hcT]
  have haopen : a ∈ openSimplex (insert q (T.erase a)) := by
    let w : E → ℝ := fun v => if v = q then β⁻¹ else t / β * weights T c v
    have hwq : w q = β⁻¹ := ite_eq_left rfl
    have hwF : ∀ v ∈ T.erase a, w v = t / β * weights T c v :=
      fun v hv => ite_eq_right (ne_of_mem_of_not_mem hv hqF)
    refine ⟨w, ?_, ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_insert.mp hv with hv | hv
      · rw [hv, hwq]
        exact inv_pos.mpr hβpos
      · rw [hwF v hv]
        exact mul_pos (div_pos ht hβpos)
          ((mem_openSimplex_self_iff hT hcT).mp hc v (Finset.mem_of_mem_erase hv))
    · rw [Finset.sum_insert hqF, hwq, Finset.sum_congr rfl hwF, ← Finset.mul_sum, hsumF]
      field_simp
      nlinarith [hβ]
    · rw [Finset.sum_insert hqF, hwq,
        Finset.sum_congr rfl (fun v hv => by rw [hwF v hv])]
      simp_rw [mul_smul]
      rw [← Finset.smul_sum, hsmulF]
      calc β⁻¹ • q + (t / β) • (c - weights T c a • a)
          = β⁻¹ • (q + t • (c - weights T c a • a)) := by
            rw [div_eq_inv_mul, mul_smul]
            exact (smul_add _ _ _).symm
        _ = β⁻¹ • (β • a) := by
          congr 1
          dsimp [q]
          rw [hβ]
          simp only [smul_sub, sub_smul, add_smul, one_smul, neg_smul, mul_smul]
          abel
        _ = a := by rw [smul_smul, inv_mul_cancel₀ hβpos.ne', one_smul]
  let L := simplexAvoiding T hT {T.erase a}
  have hLC : L.space ⊆ convexHull ℝ (T : Set E) := simplexAvoiding_space_subset T hT _
  have hface : ∀ s ∈ L.faces, ∃ i : T.erase a, ∀ v ∈ s, A i v = 0 := by
    intro s hs
    obtain ⟨v, hv, hvs⟩ := Finset.not_subset.mp (hs.2.2 _ (Finset.mem_singleton_self _))
    refine ⟨⟨v, hv⟩, fun w hw => ?_⟩
    rw [hA _ w (hs.2.1 hw), ite_eq_right (ne_of_mem_of_not_mem hw hvs)]
  let hp : IsConeBase p L := isConeBase_of_affine_halfSpaces A L
    (fun x hx => hnonneg x (hLC hx)) hface (Or.inl hpA)
  let hq : IsConeBase q L := isConeBase_of_affine_halfSpaces A L
    (fun x hx => hnonneg x (hLC hx)) hface (Or.inr hqA)
  have hzero (x : E) (hx : x ∈ L.space) : ∃ i : T.erase a, A i x = 0 := by
    obtain ⟨v, hv, hv0⟩ := exists_weights_eq_zero_of_mem_simplexAvoiding_space hT
      (Finset.mem_singleton_self (T.erase a)) (Finset.erase_subset a T) hx
    exact ⟨⟨v, hv⟩, (hcoord x (hLC hx) ⟨v, hv⟩).trans hv0⟩
  refine ⟨p, q, hpdist, hqdist, hpopen, hqT, hqind, haopen, hp, hq,
    coneComplex_space_inter_of_affine_halfSpaces A (fun x hx => hnonneg x (hLC hx))
      hzero hp hq (fun i => (hpA i).le) hqA, ?_,
    coneComplex_space_inter_eq_of_affine_halfSpaces A hLC hnonneg hzero hq hqA⟩
  intro x hx
  rcases (mem_coneComplex_space_iff hp).mp hx with rfl | ⟨z, hz, r, hr, hr', rfl⟩
  · exact hpT
  · rw [add_smul_sub_eq_combo]
    exact (convex_convexHull ℝ _) hpT (hLC hz) (sub_nonneg.mpr hr') hr.le (by ring)

open Classical in
theorem exists_isConeBase_simplexAvoiding_in_neighborhood [FiniteDimensional ℝ E] [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card)
    {a : E} (ha : a ∈ T) {U : Set E} (hU : IsOpen U) (hTU : convexHull ℝ (T : Set E) ⊆ U) :
    ∃ p q : E, p ∈ openSimplex T ∧ q ∉ convexHull ℝ (T : Set E) ∧
      AffineIndependent ℝ ((↑) : ↥(insert q (T.erase a) : Finset E) → E) ∧
      a ∈ openSimplex (insert q (T.erase a)) ∧
      ∃ (hp : IsConeBase p (simplexAvoiding T hT {T.erase a}))
        (hq : IsConeBase q (simplexAvoiding T hT {T.erase a})),
        (coneComplex hp).space ∩ (coneComplex hq).space = (simplexAvoiding T hT {T.erase a}).space ∧
        (coneComplex hp).space ⊆ convexHull ℝ (T : Set E) ∧
        (coneComplex hq).space ∩ convexHull ℝ (T : Set E) =
          (simplexAvoiding T hT {T.erase a}).space ∧
        (coneComplex hp).space ∪ (coneComplex hq).space ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := (T.finite_toSet.isCompact_convexHull ℝ).exists_thickening_subset_open hU
      hTU
  obtain ⟨p, q, -, hqdist, hpopen, hqT, hqind, haopen, hp, hq, hinter, hpT, hqinter⟩ :=
    exists_isConeBase_simplexAvoiding_near_vertex T hT hcard ha hε
  refine ⟨p, q, hpopen, hqT, hqind, haopen, hp, hq, hinter, hpT, hqinter, union_subset (hpT.trans
      hTU) ?_⟩
  have hqε : q ∈ Metric.thickening ε (convexHull ℝ (T : Set E)) :=
    Metric.mem_thickening_iff.mpr ⟨a, subset_convexHull ℝ _ ha, hqdist⟩
  intro x hx
  apply hεU
  rcases (mem_coneComplex_space_iff hq).mp hx with rfl | ⟨z, hz, r, hr, hr', rfl⟩
  · exact hqε
  · rw [add_smul_sub_eq_combo]
    exact ((convex_convexHull ℝ _).thickening ε) hqε
      (Metric.self_subset_thickening hε _ (simplexAvoiding_space_subset T hT _ hz))
      (sub_nonneg.mpr hr') hr.le (by ring)

open Classical in
theorem coneComplex_simplexAvoiding_union_convexHull [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) {a : E} (ha : a ∈ T)
    {p : E} (hpopen : p ∈ openSimplex T)
    (hp : IsConeBase p (simplexAvoiding T hT {T.erase a})) :
    (coneComplex hp).space ∪ convexHull ℝ ((insert p (T.erase a) : Finset E) : Set E) =
      convexHull ℝ (T : Set E) := by
  have hpT : p ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull _ hpopen
  apply Subset.antisymm
  · apply union_subset
    · intro x hx
      rcases (mem_coneComplex_space_iff hp).mp hx with rfl | ⟨z, hz, r, hr, hr', rfl⟩
      · exact hpT
      · rw [add_smul_sub_eq_combo]
        exact (convex_convexHull ℝ _) hpT (simplexAvoiding_space_subset T hT _ hz)
          (sub_nonneg.mpr hr') hr.le (by ring)
    · apply convexHull_min _ (convex_convexHull ℝ _)
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hpT
      · exact subset_convexHull ℝ _ (Finset.mem_of_mem_erase hx)
  · intro x hx
    obtain ⟨v, hv, hxv⟩ := exists_mem_convexHull_insert_erase hT hpopen hx
    by_cases hva : v = a
    · exact Or.inr (hva ▸ hxv)
    · have hae : a ∈ T.erase v := Finset.mem_erase.mpr ⟨Ne.symm hva, ha⟩
      have hface : T.erase v ∈ (simplexAvoiding T hT {T.erase a}).faces := by
        refine ⟨⟨a, hae⟩, Finset.erase_subset v T, ?_⟩
        simp only [Finset.mem_singleton, forall_eq]
        exact fun h => Finset.notMem_erase v T (h (Finset.mem_erase.mpr ⟨hva, hv⟩))
      exact Or.inl ((coneComplex hp).convexHull_subset_space (Or.inr (Or.inr ⟨_, hface, rfl⟩)) hxv)

end DifferentialGeometry.Topology.PiecewiseLinear

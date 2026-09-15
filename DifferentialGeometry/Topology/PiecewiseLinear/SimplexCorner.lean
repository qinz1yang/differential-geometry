import DifferentialGeometry.Topology.PiecewiseLinear.ConeHalfSpace
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexAvoiding
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
      (simplexBoundary (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T))).space := by
  apply Subset.antisymm
  · rintro x ⟨hxL, hxF⟩
    obtain ⟨s, hs, hxs⟩ := (simplexAvoiding T hT {T.erase a}).mem_space_iff.mp hxL
    have hxinter : x ∈ convexHull ℝ ((s ∩ T.erase a : Finset E) : Set E) := by
      rw [Finset.coe_inter]
      exact convexHull_inter_subset_of_affineIndependent hT hs.2.1 (Finset.erase_subset a T) ⟨hxs, hxF⟩
    have hne : (s ∩ T.erase a).Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.coe_empty, convexHull_empty] at hxinter
      exact hxinter
    refine (simplexBoundary (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T))).convexHull_subset_space
      ⟨Finset.inter_subset_right, hne, ?_⟩ hxinter
    intro he
    exact hs.2.2 _ (Finset.mem_singleton_self _) (he ▸ Finset.inter_subset_left)
  · intro x hx
    refine ⟨space_mono_of_faces_subset (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a) hx, ?_⟩
    exact simplexComplex_space_subset _ _
      (space_mono_of_faces_subset (simplexBoundary_faces_subset_simplexComplex _ _) hx)

open Classical in
theorem exists_isConeBase_simplexAvoiding_near_vertex [FiniteDimensional ℝ E] [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card)
    {a : E} (ha : a ∈ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : E, dist p a < ε ∧ dist q a < ε ∧ p ∈ openSimplex T ∧
      q ∉ convexHull ℝ (T : Set E) ∧
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
    rw [hA i a ha, if_neg (Finset.ne_of_mem_erase i.2).symm]
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
    simpa only [p, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht] using htε
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
  let L := simplexAvoiding T hT {T.erase a}
  have hLC : L.space ⊆ convexHull ℝ (T : Set E) := simplexAvoiding_space_subset T hT _
  have hface : ∀ s ∈ L.faces, ∃ i : T.erase a, ∀ v ∈ s, A i v = 0 := by
    intro s hs
    obtain ⟨v, hv, hvs⟩ := Finset.not_subset.mp (hs.2.2 _ (Finset.mem_singleton_self _))
    refine ⟨⟨v, hv⟩, fun w hw => ?_⟩
    rw [hA _ w (hs.2.1 hw), if_neg (ne_of_mem_of_not_mem hw hvs)]
  let hp : IsConeBase p L := isConeBase_of_affine_halfSpaces A L
    (fun x hx => hnonneg x (hLC hx)) hface (Or.inl hpA)
  let hq : IsConeBase q L := isConeBase_of_affine_halfSpaces A L
    (fun x hx => hnonneg x (hLC hx)) hface (Or.inr hqA)
  have hzero (x : E) (hx : x ∈ L.space) : ∃ i : T.erase a, A i x = 0 := by
    obtain ⟨v, hv, hv0⟩ := exists_weights_eq_zero_of_mem_simplexAvoiding_space hT
      (Finset.mem_singleton_self (T.erase a)) (Finset.erase_subset a T) hx
    exact ⟨⟨v, hv⟩, (hcoord x (hLC hx) ⟨v, hv⟩).trans hv0⟩
  refine ⟨p, q, hpdist, hqdist, hpopen, hqT, hp, hq,
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
      ∃ (hp : IsConeBase p (simplexAvoiding T hT {T.erase a}))
        (hq : IsConeBase q (simplexAvoiding T hT {T.erase a})),
        (coneComplex hp).space ∩ (coneComplex hq).space = (simplexAvoiding T hT {T.erase a}).space ∧
        (coneComplex hp).space ⊆ convexHull ℝ (T : Set E) ∧
        (coneComplex hq).space ∩ convexHull ℝ (T : Set E) =
          (simplexAvoiding T hT {T.erase a}).space ∧
        (coneComplex hp).space ∪ (coneComplex hq).space ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := (T.finite_toSet.isCompact_convexHull ℝ).exists_thickening_subset_open hU hTU
  obtain ⟨p, q, -, hqdist, hpopen, hqT, hp, hq, hinter, hpT, hqinter⟩ :=
    exists_isConeBase_simplexAvoiding_near_vertex T hT hcard ha hε
  refine ⟨p, q, hpopen, hqT, hp, hq, hinter, hpT, hqinter, union_subset (hpT.trans hTU) ?_⟩
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

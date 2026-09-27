import DifferentialGeometry.Topology.Ends.FiniteEnds
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Function

namespace DifferentialGeometry.Geometry.Topology

variable {X : Type*} [TopologicalSpace X]

theorem exists_compact_box_of_isCompact {C : Set (X × ℝ)} (hC : IsCompact C) :
    ∃ K : Set X, IsCompact K ∧ ∃ R : ℝ, 0 < R ∧ C ⊆ K ×ˢ Icc (-R) R := by
  obtain ⟨R, hR, hbound⟩ := (hC.image continuous_snd).isBounded.subset_closedBall_lt 0 0
  refine ⟨Prod.fst '' C, hC.image continuous_fst, R, hR, ?_⟩
  intro q hq
  refine ⟨mem_image_of_mem _ hq, ?_⟩
  have h := hbound (mem_image_of_mem Prod.snd hq)
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le, mem_Icc] using h

theorem isConnected_compl_prod_Icc [ConnectedSpace X] {K : Set X} {z : X}
    (hz : z ∉ K) (R : ℝ) : IsConnected (K ×ˢ Icc (-R) R)ᶜ := by
  refine ⟨⟨(z, R + 1), fun h => hz h.1⟩, isPreconnected_of_forall (z, R + 1) ?_⟩
  intro q hq
  by_cases hqK : q.1 ∈ K
  · let A : Set (X × ℝ) := univ ×ˢ {q.2}
    let B : Set (X × ℝ) := {z} ×ˢ univ
    have hA : IsPreconnected A := isPreconnected_univ.prod isPreconnected_singleton
    have hB : IsPreconnected B := isPreconnected_singleton.prod isPreconnected_univ
    refine ⟨A ∪ B, ?_, Or.inr ⟨rfl, trivial⟩, Or.inl ⟨trivial, rfl⟩,
      hA.union (z, q.2) ⟨trivial, rfl⟩ ⟨rfl, trivial⟩ hB⟩
    intro w hw hbox
    rcases hw with hw | hw
    · exact hq ⟨hqK, hw.2 ▸ hbox.2⟩
    · exact hz (hw.1 ▸ hbox.1)
  · let A : Set (X × ℝ) := {q.1} ×ˢ univ
    let B : Set (X × ℝ) := univ ×ˢ {R + 1}
    have hA : IsPreconnected A := isPreconnected_singleton.prod isPreconnected_univ
    have hB : IsPreconnected B := isPreconnected_univ.prod isPreconnected_singleton
    refine ⟨A ∪ B, ?_, Or.inr ⟨trivial, rfl⟩, Or.inl ⟨rfl, trivial⟩,
      hA.union (q.1, R + 1) ⟨rfl, trivial⟩ ⟨trivial, rfl⟩ hB⟩
    intro w hw hbox
    rcases hw with hw | hw
    · exact hqK (hw.1 ▸ hbox.1)
    · have h : R + 1 ≤ R := hw.2 ▸ hbox.2.2
      linarith

private theorem noncompact_component_meets_compl [T2Space X]
    {C B : Set X} (hB : IsCompact B) (x : X)
    (hnc : ¬ IsCompact (closure (connectedComponentIn Cᶜ x))) :
    (connectedComponentIn Cᶜ x ∩ Bᶜ).Nonempty := by
  by_contra hnone
  have hsub : connectedComponentIn Cᶜ x ⊆ B := by
    intro y hy
    by_contra hyB
    exact hnone ⟨y, hy, hyB⟩
  exact hnc (hB.of_isClosed_subset isClosed_closure (closure_minimal hsub hB.isClosed))

private theorem component_eq_of_common_preconnected {C A : Set X}
    (hA : IsPreconnected A) (hAC : A ⊆ Cᶜ) {x y : X}
    (hx : (connectedComponentIn Cᶜ x ∩ A).Nonempty)
    (hy : (connectedComponentIn Cᶜ y ∩ A).Nonempty) :
    connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ y := by
  obtain ⟨a, ha, haA⟩ := hx
  obtain ⟨b, hb, hbA⟩ := hy
  have hab := hA.subset_connectedComponentIn haA hAC hbA
  exact (connectedComponentIn_eq ha).trans
    ((connectedComponentIn_eq hab).trans (connectedComponentIn_eq hb).symm)

private theorem not_isCompact_closure_of_unbounded_snd_above {A : Set (X × ℝ)}
    (hA : ∀ R : ℝ, ∃ q ∈ A, R < q.2) : ¬ IsCompact (closure A) := by
  intro h
  obtain ⟨R, hR⟩ := (h.image continuous_snd).bddAbove
  obtain ⟨q, hq, hqR⟩ := hA R
  exact hqR.not_ge (hR (mem_image_of_mem _ (subset_closure hq)))

private theorem not_isCompact_closure_of_unbounded_snd_below {A : Set (X × ℝ)}
    (hA : ∀ R : ℝ, ∃ q ∈ A, q.2 < R) : ¬ IsCompact (closure A) := by
  intro h
  obtain ⟨R, hR⟩ := (h.image continuous_snd).bddBelow
  obtain ⟨q, hq, hqR⟩ := hA R
  exact hqR.not_ge (hR (mem_image_of_mem _ (subset_closure hq)))

theorem hasExactlyEnds_prod_real_of_noncompact [T2Space X] [ConnectedSpace X]
    (hX : ¬ CompactSpace X) : HasExactlyEnds (X × ℝ) 1 := by
  classical
  obtain ⟨z⟩ := (inferInstance : Nonempty X)
  constructor
  · refine ⟨∅, isCompact_empty, fun _ => (z, 0), by simp,
      fun i j _ => Subsingleton.elim i j, ?_⟩
    intro i
    have hc : connectedComponentIn (∅ : Set (X × ℝ))ᶜ (z, 0) = univ := by
      rw [compl_empty]
      exact isPreconnected_univ.connectedComponentIn trivial
    rw [hc]
    exact not_isCompact_closure_of_unbounded_snd_above fun R =>
      ⟨(z, R + 1), trivial, by dsimp; linarith⟩
  · rintro ⟨C, hC, x, _, hinj, hnc⟩
    obtain ⟨K, hK, R, _, hbox⟩ := exists_compact_box_of_isCompact hC
    obtain ⟨w, hw⟩ : ∃ w : X, w ∉ K := by
      by_contra hnone
      have hKu : K = univ := eq_univ_of_forall fun w => by
        by_contra hw
        exact hnone ⟨w, hw⟩
      exact hX (isCompact_univ_iff.mp (hKu ▸ hK))
    have hB : IsCompact (K ×ˢ Icc (-R) R) := hK.prod isCompact_Icc
    have hO := isConnected_compl_prod_Icc hw R
    have hsub : (K ×ˢ Icc (-R) R)ᶜ ⊆ Cᶜ := compl_subset_compl.mpr hbox
    have heq := component_eq_of_common_preconnected hO.isPreconnected hsub
      (noncompact_component_meets_compl hB (x 0) (hnc 0))
      (noncompact_component_meets_compl hB (x 1) (hnc 1))
    have h01 := hinj heq
    norm_num at h01

theorem hasAtMostTwoEnds_prod_real_of_compact [T2Space X] [ConnectedSpace X]
    [CompactSpace X] : HasAtMostTwoEnds (X × ℝ) := by
  classical
  rintro ⟨C, hC, x, _, hinj, hnc⟩
  obtain ⟨K, _, R, _, hbox⟩ := exists_compact_box_of_isCompact hC
  have hslab : C ⊆ (univ : Set X) ×ˢ Icc (-R) R :=
    fun q hq => ⟨trivial, (hbox hq).2⟩
  have hB : IsCompact ((univ : Set X) ×ˢ Icc (-R) R) :=
    isCompact_univ.prod isCompact_Icc
  let U : Fin 2 → Set (X × ℝ) := fun i =>
    univ ×ˢ (if i = 0 then Ioi R else Iio (-R))
  have hUconn (i : Fin 2) : IsPreconnected (U i) := by
    by_cases hi : i = 0
    · simpa only [U, hi, ite_true] using isPreconnected_univ.prod (isPreconnected_Ioi (a := R))
    · simpa only [U, hi, ite_false] using isPreconnected_univ.prod (isPreconnected_Iio (a := -R))
  have hUsub (i : Fin 2) : U i ⊆ Cᶜ := by
    intro q hq hqC
    have hbound := (hslab hqC).2
    by_cases hi : i = 0
    · have hlt : R < q.2 := by simpa only [U, hi, ite_true, mem_Ioi] using hq.2
      exact hlt.not_ge hbound.2
    · have hlt : q.2 < -R := by simpa only [U, hi, ite_false, mem_Iio] using hq.2
      exact hlt.not_ge hbound.1
  have hmeet (i : Fin 3) : ∃ b : Fin 2, (connectedComponentIn Cᶜ (x i) ∩ U b).Nonempty := by
    obtain ⟨q, hq, hout⟩ := noncompact_component_meets_compl hB (x i) (hnc i)
    rcases lt_or_ge q.2 (-R) with hlow | hlow
    · refine ⟨1, q, hq, ?_⟩
      change q ∈ (univ : Set X) ×ˢ Iio (-R)
      exact ⟨trivial, hlow⟩
    · have hhigh : R < q.2 := lt_of_not_ge fun h => hout ⟨trivial, hlow, h⟩
      refine ⟨0, q, hq, ?_⟩
      change q ∈ (univ : Set X) ×ˢ Ioi R
      exact ⟨trivial, hhigh⟩
  choose b hb using hmeet
  have hbinj : Injective b := by
    intro i j hij
    apply hinj
    apply component_eq_of_common_preconnected (hUconn (b i)) (hUsub (b i)) (hb i)
    rw [hij]
    exact hb j
  have hcard := Fintype.card_le_of_injective b hbinj
  norm_num at hcard

private theorem product_zero_component_pos [ConnectedSpace X] (z : X) {t : ℝ} (ht : 0 < t) :
    connectedComponentIn ((univ : Set X) ×ˢ ({0} : Set ℝ))ᶜ (z, t) = univ ×ˢ Ioi 0 := by
  have hbase : (z, t) ∈ ((univ : Set X) ×ˢ ({0} : Set ℝ))ᶜ :=
    fun h => ht.ne' h.2
  have hzero : ∀ q ∈ connectedComponentIn ((univ : Set X) ×ˢ ({0} : Set ℝ))ᶜ (z, t),
      q.2 ≠ 0 := by
    intro q hq heq
    exact connectedComponentIn_subset _ _ hq ⟨trivial, heq⟩
  apply Subset.antisymm
  · intro q hq
    refine ⟨trivial, ?_⟩
    exact isPreconnected_connectedComponentIn.lt_of_ne continuous_snd.continuousOn hzero
      ⟨(z, t), mem_connectedComponentIn hbase, ht⟩ hq
  · apply (isPreconnected_univ.prod (isPreconnected_Ioi (a := (0 : ℝ)))).subset_connectedComponentIn
      (x := (z, t)) ⟨trivial, ht⟩
    intro q hq hC
    exact hq.2.ne' hC.2

private theorem product_zero_component_neg [ConnectedSpace X] (z : X) {t : ℝ} (ht : t < 0) :
    connectedComponentIn ((univ : Set X) ×ˢ ({0} : Set ℝ))ᶜ (z, t) = univ ×ˢ Iio 0 := by
  have hbase : (z, t) ∈ ((univ : Set X) ×ˢ ({0} : Set ℝ))ᶜ :=
    fun h => ht.ne h.2
  have hzero : ∀ q ∈ connectedComponentIn ((univ : Set X) ×ˢ ({0} : Set ℝ))ᶜ (z, t),
      q.2 ≠ 0 := by
    intro q hq heq
    exact connectedComponentIn_subset _ _ hq ⟨trivial, heq⟩
  apply Subset.antisymm
  · intro q hq
    refine ⟨trivial, ?_⟩
    exact isPreconnected_connectedComponentIn.gt_of_ne continuous_snd.continuousOn hzero
      ⟨(z, t), mem_connectedComponentIn hbase, ht⟩ hq
  · apply (isPreconnected_univ.prod (isPreconnected_Iio (a := (0 : ℝ)))).subset_connectedComponentIn
      (x := (z, t)) ⟨trivial, ht⟩
    intro q hq hC
    exact hq.2.ne hC.2

theorem hasExactlyEnds_prod_real_of_compact [T2Space X] [ConnectedSpace X]
    [CompactSpace X] : HasExactlyEnds (X × ℝ) 2 := by
  classical
  refine ⟨?_, hasAtMostTwoEnds_prod_real_of_compact⟩
  obtain ⟨z⟩ := (inferInstance : Nonempty X)
  let C : Set (X × ℝ) := univ ×ˢ {0}
  let x : Fin 2 → X × ℝ := fun i => if i = 0 then (z, 1) else (z, -1)
  have hC : IsCompact C := isCompact_univ.prod isCompact_singleton
  have hc (i : Fin 2) : connectedComponentIn Cᶜ (x i) =
      if i = 0 then univ ×ˢ Ioi 0 else univ ×ˢ Iio 0 := by
    by_cases hi : i = 0
    · simp only [x, hi, ite_true]
      exact product_zero_component_pos z (by norm_num)
    · simp only [x, hi, ite_false]
      exact product_zero_component_neg z (by norm_num)
  refine ⟨C, hC, x, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0 <;> simp [C, x, hi]
  · intro i j hij
    by_contra hne
    fin_cases i <;> fin_cases j
    · exact hne rfl
    · change connectedComponentIn Cᶜ (x 0) = connectedComponentIn Cᶜ (x 1) at hij
      rw [hc 0, hc 1] at hij
      have hmem : (z, (1 : ℝ)) ∈ (univ : Set X) ×ˢ Ioi 0 := ⟨trivial, by norm_num⟩
      have heq : (univ : Set X) ×ˢ Ioi (0 : ℝ) = univ ×ˢ Iio 0 := by simpa using hij
      rw [heq] at hmem
      norm_num at hmem
    · change connectedComponentIn Cᶜ (x 1) = connectedComponentIn Cᶜ (x 0) at hij
      rw [hc 1, hc 0] at hij
      have hmem : (z, (1 : ℝ)) ∈ (univ : Set X) ×ˢ Ioi 0 := ⟨trivial, by norm_num⟩
      have heq : (univ : Set X) ×ˢ Ioi (0 : ℝ) = univ ×ˢ Iio 0 := by simpa using hij.symm
      rw [heq] at hmem
      norm_num at hmem
    · exact hne rfl
  · intro i
    rw [hc i]
    by_cases hi : i = 0
    · rw [if_pos hi]
      apply not_isCompact_closure_of_unbounded_snd_above
      intro R
      exact ⟨(z, max R 0 + 1), ⟨trivial, by change 0 < max R 0 + 1; linarith [le_max_right R 0]⟩,
        by dsimp; linarith [le_max_left R 0]⟩
    · rw [if_neg hi]
      apply not_isCompact_closure_of_unbounded_snd_below
      intro R
      exact ⟨(z, min R 0 - 1), ⟨trivial, by change min R 0 - 1 < 0; linarith [min_le_right R 0]⟩,
        by dsimp; linarith [min_le_left R 0]⟩

end DifferentialGeometry.Geometry.Topology

import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
open Set
open Set Metric

namespace Metric
section

variable {X : Type*} [MetricSpace X]

theorem exists_finite_disjoint_ball_selection {P : Set X} (hP : TotallyBounded P)
    (r : X → ℝ) {rmin R : ℝ} (hmin : 0 < rmin)
    (hlower : ∀ p ∈ P, rmin ≤ r p) (hupper : ∀ p ∈ P, r p ≤ R) :
    ∃ I : Set X, I ⊆ P ∧ I.Finite ∧ I.PairwiseDisjoint (fun p => ball p (r p)) ∧
      ∀ p ∈ P, ∃ i ∈ I, (ball p (r p) ∩ ball i (r i)).Nonempty ∧
        r p ≤ 2 * r i ∧ dist p i < 3 * r i ∧ ball p (r p) ⊆ ball i (5 * r i) := by
  obtain ⟨I, hIP, hdisj, hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun p => ball p (r p)) P r 2 (by norm_num)
    (fun p hp => (hmin.trans_le (hlower p hp)).le) R hupper
    (fun p hp => nonempty_ball.mpr (hmin.trans_le (hlower p hp)))
  obtain ⟨S, hS, hScover⟩ := totallyBounded_iff.mp hP (rmin / 3) (by positivity)
  have hsmall (z : X) : (I ∩ ball z (rmin / 3)).Subsingleton := by
    intro p hp q hq
    by_contra hpq
    have hpqdist : dist q p < r p := by
      have ht := dist_triangle q z p
      rw [dist_comm z p] at ht
      have hqz := hq.2
      have hpz := hp.2
      change dist q z < rmin / 3 at hqz
      change dist p z < rmin / 3 at hpz
      linarith [hlower p (hIP hp.1)]
    exact Set.disjoint_left.mp (hdisj hp.1 hq.1 hpq) hpqdist
      (mem_ball_self (hmin.trans_le (hlower q (hIP hq.1))))
  have hIfin : I.Finite := by
    apply (hS.biUnion (fun z _ => (hsmall z).finite)).subset
    intro p hp
    obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp (hScover (hIP hp))
    exact mem_iUnion₂.mpr ⟨z, hz, hp, hpz⟩
  refine ⟨I, hIP, hIfin, hdisj, ?_⟩
  intro p hp
  obtain ⟨i, hi, hinter, hri⟩ := hcover p hp
  obtain ⟨z, hzp, hzi⟩ := hinter
  have hpi : dist p i < 3 * r i := by
    have ht := dist_triangle p z i
    rw [dist_comm p z] at ht
    change dist z p < r p at hzp
    change dist z i < r i at hzi
    linarith
  refine ⟨i, hi, ⟨z, hzp, hzi⟩, hri, hpi, ?_⟩
  intro x hx
  have ht := dist_triangle x p i
  change dist x p < r p at hx
  change dist x i < 5 * r i
  linarith

theorem exists_maximal_doubling_ball (r : X → ℝ) (Z : Set X)
    (hpos : ∀ p, 0 < r p) {R : ℝ} (hupper : ∀ p, r p ≤ R)
    {p : X} (hp : (ball p (r p) ∩ Z).Nonempty) :
    ∃ v, (ball v (r v) ∩ Z).Nonempty ∧
      (p = v ∨ 2 * r p < r v ∧ ball p (r p) ⊆ ball v (r v)) ∧
      ∀ q, (ball q (r q) ∩ Z).Nonempty →
        ball v (r v) ⊆ ball q (r q) → r q ≤ 2 * r v := by
  let A : Set X := {q | (ball q (r q) ∩ Z).Nonempty ∧
    (p = q ∨ 2 * r p < r q ∧ ball p (r p) ⊆ ball q (r q))}
  have hpA : p ∈ A := ⟨hp, Or.inl rfl⟩
  have hne : (r '' A).Nonempty := ⟨r p, mem_image_of_mem r hpA⟩
  have hbd : BddAbove (r '' A) := ⟨R, by rintro t ⟨q, _, rfl⟩; exact hupper q⟩
  have hsup : 0 < sSup (r '' A) := (hpos p).trans_le (le_csSup hbd (mem_image_of_mem r hpA))
  obtain ⟨t, ⟨v, hv, rfl⟩, hvt⟩ := exists_lt_of_lt_csSup hne (half_lt_self hsup)
  refine ⟨v, hv.1, hv.2, ?_⟩
  intro q hq hvq
  by_contra! hqv
  have hqA : q ∈ A := by
    refine ⟨hq, Or.inr ?_⟩
    rcases hv.2 with rfl | ⟨hpv, hpvball⟩
    · exact ⟨hqv, hvq⟩
    · exact ⟨by linarith [hpos v], hpvball.trans hvq⟩
  have hqs := le_csSup hbd (mem_image_of_mem r hqA)
  linarith

theorem radius_le_of_maximal_doubling_ball (r : X → ℝ) (Z : Set X)
    {v : X} (hv : (ball v (r v) ∩ Z).Nonempty) (hrv : 0 < r v)
    (hmax : ∀ q, (ball q (r q) ∩ Z).Nonempty →
      ball v (r v) ⊆ ball q (r q) → r q ≤ 2 * r v)
    {q : X} (hq : dist v q ≤ 10 * r v) : r q ≤ 20 * r v := by
  by_contra! h
  have hsub : ball v (r v) ⊆ ball q (r q) := by
    intro x hx
    have ht := dist_triangle x v q
    change dist x v < r v at hx
    change dist x q < r q
    linarith
  have hqZ : (ball q (r q) ∩ Z).Nonempty := by
    obtain ⟨z, hz, hzZ⟩ := hv
    exact ⟨z, hsub hz, hzZ⟩
  have := hmax q hqZ hsub
  linarith

theorem exists_finite_disjoint_ball_cover_of_bounded_radii
    (htot : TotallyBounded (Set.univ : Set X)) (Z : Set X) (r : X → ℝ)
    {rmin R : ℝ} (hmin : 0 < rmin) (hlower : ∀ p, rmin ≤ r p)
    (hupper : ∀ p, r p ≤ R) :
    ∃ I : Set X, I.Finite ∧ I.PairwiseDisjoint (fun i => ball i (r i)) ∧
      (∀ i ∈ I, (ball i (r i) ∩ Z).Nonempty ∧
        ∀ q, dist i q ≤ 10 * r i → r q ≤ 20 * r i) ∧
      Z ⊆ ⋃ i ∈ I, ball i (5 * r i) := by
  let V : Set X := {v | (ball v (r v) ∩ Z).Nonempty ∧
    ∀ q, (ball q (r q) ∩ Z).Nonempty →
      ball v (r v) ⊆ ball q (r q) → r q ≤ 2 * r v}
  have hpos : ∀ p, 0 < r p := fun p => hmin.trans_le (hlower p)
  obtain ⟨I, hIV, hfin, hdisj, hcover⟩ := exists_finite_disjoint_ball_selection
    (htot.subset (subset_univ V)) r hmin (fun p _ => hlower p) (fun p _ => hupper p)
  refine ⟨I, hfin, hdisj, ?_, ?_⟩
  · intro i hi
    exact ⟨(hIV hi).1, fun q hq =>
      radius_le_of_maximal_doubling_ball r Z (hIV hi).1 (hpos i) (hIV hi).2 hq⟩
  · intro z hz
    obtain ⟨v, hvZ, hzv, hmax⟩ := exists_maximal_doubling_ball r Z hpos hupper
      (show (ball z (r z) ∩ Z).Nonempty from ⟨z, mem_ball_self (hpos z), hz⟩)
    have hzball : z ∈ ball v (r v) := by
      rcases hzv with rfl | ⟨_, hsub⟩
      · exact mem_ball_self (hpos z)
      · exact hsub (mem_ball_self (hpos z))
    obtain ⟨i, hi, _, _, _, hsub⟩ := hcover v ⟨hvZ, hmax⟩
    exact mem_iUnion₂.mpr ⟨i, hi, hsub hzball⟩

theorem subset_small_balls_of_annular_exclusion (Z I : Set X) (r : X → ℝ)
    (hcover : Z ⊆ ⋃ i ∈ I, ball i (5 * r i))
    (hexclude : ∀ i ∈ I, ∀ z ∈ Z, ¬ (r i / 10 ≤ dist i z ∧ dist i z ≤ 10 * r i)) :
    Z ⊆ ⋃ i ∈ I, ball i (r i / 10) := by
  intro z hz
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcover hz)
  have hdist : dist i z < 5 * r i := by simpa only [mem_ball, dist_comm] using hzi
  refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
  change dist z i < r i / 10
  rw [dist_comm]
  by_contra! h
  exact hexclude i hi z hz ⟨h, by linarith [dist_nonneg (x := i) (y := z)]⟩

theorem exists_finite_disjoint_ball_cover_of_continuous_scale [CompactSpace X]
    (Z : Set X) (r ρ : X → ℝ) (hρ : Continuous ρ) (hρpos : ∀ p, 0 < ρ p)
    {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U)
    (hlower : ∀ p, T * ρ p ≤ r p) (hupper : ∀ p, r p ≤ U * ρ p) :
    ∃ I : Set X, I.Finite ∧ I.PairwiseDisjoint (fun i => ball i (r i)) ∧
      (∀ i ∈ I, (ball i (r i) ∩ Z).Nonempty ∧
        ∀ q, dist i q ≤ 10 * r i → r q ≤ 20 * r i ∧ T / 20 ≤ r i / ρ q) ∧
      Z ⊆ ⋃ i ∈ I, ball i (5 * r i) := by
  classical
  by_cases hX : Nonempty X
  · let := hX
    obtain ⟨pmin, _, hmin⟩ := isCompact_univ.exists_isMinOn
      (Set.univ_nonempty : (Set.univ : Set X).Nonempty) hρ.continuousOn
    obtain ⟨pmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn
      (Set.univ_nonempty : (Set.univ : Set X).Nonempty) hρ.continuousOn
    obtain ⟨I, hfin, hdisj, hlocal, hcover⟩ := exists_finite_disjoint_ball_cover_of_bounded_radii
      isCompact_univ.totallyBounded Z r (mul_pos hT (hρpos pmin))
      (fun p => (mul_le_mul_of_nonneg_left (hmin (mem_univ p)) hT.le).trans (hlower p))
      (fun p => (hupper p).trans
        (mul_le_mul_of_nonneg_left (hmax (mem_univ p)) (hT.le.trans hTU)))
    refine ⟨I, hfin, hdisj, ?_, hcover⟩
    intro i hi
    refine ⟨(hlocal i hi).1, ?_⟩
    intro q hq
    have hr := (hlocal i hi).2 q hq
    refine ⟨hr, (le_div_iff₀ (hρpos q)).mpr ?_⟩
    linarith [hlower q]
  · have hZ : Z = ∅ := eq_empty_iff_forall_notMem.mpr (fun x _ => hX ⟨x⟩)
    exact ⟨∅, finite_empty, by simp, by simp, by simp [hZ]⟩

end
end Metric

namespace Metric
section

theorem exists_finite_disjoint_ball_selection_all_enlargements
    {X : Type*} [MetricSpace X] (S : Set X) (hS : TotallyBounded S)
    (r : X → ℝ) {rmin R : ℝ} (hmin : 0 < rmin)
    (hlower : ∀ x ∈ S, rmin ≤ r x) (hupper : ∀ x ∈ S, r x ≤ R) :
    ∃ I : Set X, I ⊆ S ∧ I.Finite ∧ I.PairwiseDisjoint (fun i => ball i (r i)) ∧
      (∀ x ∈ S, ∃ i ∈ I, r x ≤ 2*r i ∧ dist x i < 3*r i) ∧
      ∀ a : ℝ, 0 ≤ a →
        (⋃ x ∈ S, ball x (a*r x)) ⊆ ⋃ i ∈ I, ball i ((2*a+3)*r i) := by
  obtain ⟨I,hIS,hI,hdisj,hcover⟩ :=
    exists_finite_disjoint_ball_selection hS r hmin hlower hupper
  refine ⟨I,hIS,hI,hdisj,?_,?_⟩
  · intro x hx
    obtain ⟨i,hi,_hmeet,hscale,hdist,_hball⟩ := hcover x hx
    exact ⟨i,hi,hscale,hdist⟩
  · intro a ha z hz
    obtain ⟨x,hx,hzx⟩ := mem_iUnion₂.mp hz
    obtain ⟨i,hi,_hmeet,hscale,hdist,_hball⟩ := hcover x hx
    refine mem_iUnion₂.mpr ⟨i,hi,?_⟩
    have htriangle := dist_triangle z x i
    have hrscale := mul_le_mul_of_nonneg_left hscale ha
    change dist z x < a*r x at hzx
    change dist z i < (2*a+3)*r i
    nlinarith

end
end Metric

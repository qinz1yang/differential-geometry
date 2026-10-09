import DifferentialGeometry.Topology.MetricSpace.LipschitzBallSelection
import Mathlib.Data.Set.Card
import Mathlib.Order.Zorn

/-!
# Maximal disjoint scale-ball families (LC86, metric part)

Blueprint row LC86 (`lem:collapse-local-selection-packet`, master207A): on a compact metric space
with a positive continuous scale `ρ`, every pairwise disjoint family of `a ρ`-balls is finite with a
uniform cardinality bound; maximal families with centres in a prescribed set exist; and when
intersecting `a ρ`-balls have centres in each other's `b ρ`-balls, the `b ρ`-balls of any maximal
family cover the prescribed set.  For a `Λ`-Lipschitz scale with `Λ a ≤ 1 / 2` one may take
`b = 4 a`.
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

variable {X : Type*} [MetricSpace X]

/-- LC86: on a compact space, the cardinality of a pairwise disjoint family of `a ρ`-balls is
bounded uniformly, for any positive continuous scale `ρ`. -/
theorem exists_ncard_bound_of_pairwiseDisjoint_scale_balls [CompactSpace X]
    {ρ : X → ℝ} (hρ : Continuous ρ) (hρpos : ∀ p, 0 < ρ p) {a : ℝ} (ha : 0 < a) :
    ∃ N : ℕ, ∀ I : Set X, I.PairwiseDisjoint (fun i => ball i (a * ρ i)) →
      I.Finite ∧ I.ncard ≤ N := by
  classical
  by_cases hX : Nonempty X
  · obtain ⟨pmin, _, hmin⟩ := isCompact_univ.exists_isMinOn
      (Set.univ_nonempty : (Set.univ : Set X).Nonempty) hρ.continuousOn
    set r := a * ρ pmin with hr
    have hrpos : 0 < r := mul_pos ha (hρpos pmin)
    have hrle (p : X) : r ≤ a * ρ p :=
      mul_le_mul_of_nonneg_left (hmin (mem_univ p)) ha.le
    obtain ⟨T, hTfin, hT⟩ := totallyBounded_iff.mp (isCompact_univ (X := X)).totallyBounded (r / 2)
      (by positivity)
    have hmem (x : X) : ∃ z ∈ T, x ∈ ball z (r / 2) :=
      by simpa only [mem_iUnion₂, exists_prop] using hT (mem_univ x)
    choose f hfT hf using hmem
    refine ⟨T.ncard, fun I hI => ?_⟩
    have hinj : InjOn f I := by
      intro i hi j hj hij
      by_contra hne
      have hdist : dist i j < a * ρ j := by
        have h1 := hf i
        have h2 := hf j
        rw [hij] at h1
        change dist i (f j) < r / 2 at h1
        change dist j (f j) < r / 2 at h2
        have ht := dist_triangle i (f j) j
        rw [dist_comm (f j) j] at ht
        linarith [hrle j]
      exact Set.disjoint_left.mp (hI hi hj hne) (mem_ball_self (mul_pos ha (hρpos i)))
        (show dist i j < a * ρ j from hdist)
    refine ⟨Finite.of_finite_image (hTfin.subset ?_) hinj,
      ncard_le_ncard_of_injOn f (fun i _ => hfT i) hinj hTfin⟩
    rintro _ ⟨i, _, rfl⟩
    exact hfT i
  · refine ⟨0, fun I _ => ?_⟩
    have hI : I = ∅ := eq_empty_of_forall_notMem fun x _ => hX ⟨x⟩
    subst hI
    exact ⟨finite_empty, by simp⟩

/-- LC86: maximal pairwise disjoint families of `a ρ`-balls with centres in `S` exist. -/
theorem exists_maximal_pairwiseDisjoint_scale_family (S : Set X) (ρ : X → ℝ) (a : ℝ) :
    ∃ I : Set X, Maximal (fun J : Set X => J ⊆ S ∧
      J.PairwiseDisjoint (fun i => ball i (a * ρ i))) I := by
  obtain ⟨I, hI⟩ := zorn_subset {J : Set X | J ⊆ S ∧
      J.PairwiseDisjoint (fun i => ball i (a * ρ i))} (by
    intro c hcS hc
    refine ⟨⋃₀ c, ⟨sUnion_subset fun J hJ => (hcS hJ).1, ?_⟩, fun J hJ => subset_sUnion_of_mem hJ⟩
    exact (pairwiseDisjoint_sUnion hc.directedOn).mpr fun J hJ => (hcS hJ).2)
  exact ⟨I, hI⟩

/-- LC86: if intersecting `a ρ`-balls have centres in each other's `b ρ`-balls, the `b ρ`-balls of
a maximal pairwise disjoint family with centres in `S` cover `S`. -/
theorem subset_iUnion_ball_of_maximal_pairwiseDisjoint
    {ρ : X → ℝ} {a b : ℝ} {S I : Set X} (ha : 0 < a) (hρpos : ∀ p, 0 < ρ p)
    (hcomp : ∀ p q, (ball p (a * ρ p) ∩ ball q (a * ρ q)).Nonempty → dist p q < b * ρ q)
    (hmax : Maximal (fun J : Set X => J ⊆ S ∧
      J.PairwiseDisjoint (fun i => ball i (a * ρ i))) I) :
    S ⊆ ⋃ i ∈ I, ball i (b * ρ i) := by
  intro p hp
  by_contra hnot
  have hfar : ∀ i ∈ I, ¬ dist p i < b * ρ i := fun i hi h =>
    hnot (mem_iUnion₂.mpr ⟨i, hi, h⟩)
  have hins : insert p I ⊆ S ∧
      (insert p I).PairwiseDisjoint (fun i => ball i (a * ρ i)) := by
    refine ⟨insert_subset hp hmax.1.1, hmax.1.2.insert fun j hj _ => ?_⟩
    by_contra hnd
    exact hfar j hj (hcomp p j (Set.not_disjoint_iff_nonempty_inter.mp hnd))
  have hpI : p ∈ I := hmax.2 hins (subset_insert p I) (mem_insert p I)
  have hself : p ∈ ball p (a * ρ p) := mem_ball_self (mul_pos ha (hρpos p))
  exact hfar p hpI (hcomp p p ⟨p, hself, hself⟩)

/-- For a `Λ`-Lipschitz scale with `Λ a ≤ 1 / 2`, intersecting `a ρ`-balls have centres in each
other's `4 a ρ`-balls. -/
theorem dist_lt_of_inter_lipschitz_scale_balls
    {ρ : X → ℝ} {Λ : NNReal} {a : ℝ} {p q : X}
    (hρ : LipschitzWith Λ ρ) (ha : 0 < a) (hsmall : (Λ : ℝ) * a ≤ 1 / 2)
    (hinter : (ball p (a * ρ p) ∩ ball q (a * ρ q)).Nonempty) :
    dist p q < 4 * a * ρ q := by
  obtain ⟨z, hzp, hzq⟩ := hinter
  have hd : dist p q < a * ρ p + a * ρ q := by
    have htri := dist_triangle p z q
    rw [dist_comm p z] at htri
    change dist z p < a * ρ p at hzp
    change dist z q < a * ρ q at hzq
    linarith only [htri, hzp, hzq]
  have hlip := (abs_le.mp (show |ρ p - ρ q| ≤ (Λ : ℝ) * dist p q by
    simpa only [Real.dist_eq] using hρ.dist_le_mul p q)).2
  have hr := mul_le_mul_of_nonneg_left hlip ha.le
  have hs := mul_le_mul_of_nonneg_right hsmall (dist_nonneg : 0 ≤ dist p q)
  nlinarith only [hd, hr, hs]

/-- LC86, metric part, for a Lipschitz scale: on a compact space with a positive `Λ`-Lipschitz
scale and `Λ a ≤ 1 / 2`, there is a uniform bound on disjoint `a ρ`-families, a maximal family
with centres in `S` exists, and every maximal family is finite and its `4 a ρ`-balls cover `S`. -/
theorem lipschitz_scale_maximal_selection [CompactSpace X]
    (S : Set X) {ρ : X → ℝ} {Λ : NNReal} {a : ℝ}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ p, 0 < ρ p) (ha : 0 < a)
    (hsmall : (Λ : ℝ) * a ≤ 1 / 2) :
    (∃ N : ℕ, ∀ I : Set X, I.PairwiseDisjoint (fun i => ball i (a * ρ i)) →
      I.Finite ∧ I.ncard ≤ N) ∧
    (∃ I : Set X, Maximal (fun J : Set X => J ⊆ S ∧
      J.PairwiseDisjoint (fun i => ball i (a * ρ i))) I) ∧
    ∀ I : Set X, Maximal (fun J : Set X => J ⊆ S ∧
      J.PairwiseDisjoint (fun i => ball i (a * ρ i))) I →
      I.Finite ∧ S ⊆ ⋃ i ∈ I, ball i (4 * a * ρ i) := by
  obtain ⟨N, hN⟩ := exists_ncard_bound_of_pairwiseDisjoint_scale_balls hρ.continuous hρpos ha
  refine ⟨⟨N, hN⟩, exists_maximal_pairwiseDisjoint_scale_family S ρ a, fun I hI => ?_⟩
  refine ⟨(hN I hI.1.2).1, ?_⟩
  have h := subset_iUnion_ball_of_maximal_pairwiseDisjoint (b := 4 * a) ha hρpos
    (fun p q hpq => dist_lt_of_inter_lipschitz_scale_balls hρ ha hsmall hpq) hI
  simpa only [mul_assoc] using h

end GC.MetricGeometry

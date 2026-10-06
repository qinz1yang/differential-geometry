import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# A closed subset of `[0, 1]` with finite frontier and no isolated point (lane S-BD2d, `_OBDd`)

Lane O-BD1 (by S-BD2d), group G10c, real-analysis kernel. A closed `A ⊆ [0, 1]` whose frontier lies
in a finite set `F` and which has no isolated point is a finite disjoint union of NONDEGENERATE
closed intervals `[s i, e i]` whose endpoints lie in the frontier of `A`:

* `isPreconnected_Ioo_subset_of_inter_frontier_eq_empty_OBDd`: an open interval missing the
  frontier of `A` lies in `A` as soon as it meets `A`;
* `exists_Icc_decomposition_OBDd`: the decomposition (components of `A`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology

namespace DifferentialGeometry.Topology

/-- An open interval missing the frontier of `A` that meets `A` lies in `A`. -/
theorem Ioo_subset_of_meets_of_inter_frontier_eq_empty_OBDd {A : Set ℝ} {a b : ℝ}
    (hfr : Ioo a b ∩ frontier A = ∅) {x : ℝ} (hxA : x ∈ A) (hx : x ∈ Ioo a b) :
    Ioo a b ⊆ A := by
  intro y hy
  by_contra hyA
  have hpre : IsPreconnected (Ioo a b) := isPreconnected_Ioo
  have hcov : Ioo a b ⊆ interior A ∪ (closure A)ᶜ := by
    intro z hz
    by_cases hzc : z ∈ closure A
    · left
      by_contra hzi
      have : z ∈ frontier A := ⟨hzc, hzi⟩
      have h2 : z ∈ Ioo a b ∩ frontier A := ⟨hz, this⟩
      rw [hfr] at h2
      exact h2
    · right
      exact hzc
  have h1 : (Ioo a b ∩ interior A).Nonempty := by
    refine ⟨x, hx, ?_⟩
    by_contra hxi
    have : x ∈ frontier A := ⟨subset_closure hxA, hxi⟩
    have h2 : x ∈ Ioo a b ∩ frontier A := ⟨hx, this⟩
    rw [hfr] at h2
    exact h2
  have h2 : (Ioo a b ∩ (closure A)ᶜ).Nonempty := by
    refine ⟨y, hy, ?_⟩
    intro hyc
    have hyi : y ∈ interior A := by
      by_contra hyi
      have : y ∈ frontier A := ⟨hyc, hyi⟩
      have h3 : y ∈ Ioo a b ∩ frontier A := ⟨hy, this⟩
      rw [hfr] at h3
      exact h3
    exact hyA (interior_subset hyi)
  obtain ⟨z, hz, hzi, hzc⟩ := hpre (interior A) (closure A)ᶜ isOpen_interior
    isClosed_closure.isOpen_compl hcov h1 h2
  exact hzc (subset_closure (interior_subset hzi))

/-- An open interval around a point of a component, inside `A`, lies in the component. -/
theorem Ioo_subset_connectedComponentIn_OBDd {A : Set ℝ} {x c ε : ℝ}
    (hc : c ∈ connectedComponentIn A x) (hε : 0 < ε) (hIoo : Ioo (c - ε) (c + ε) ⊆ A) :
    Ioo (c - ε) (c + ε) ⊆ connectedComponentIn A x := by
  have h := isPreconnected_Ioo.subset_connectedComponentIn (x := c)
    ⟨by linarith, by linarith⟩ hIoo
  rwa [← connectedComponentIn_eq hc] at h

/-- The component of a point of a closed subset of `[0, 1]` is a closed interval with its
endpoints. -/
theorem connectedComponentIn_eq_Icc_OBDd {A : Set ℝ} (hA : IsClosed A) (hAb : A ⊆ Icc 0 1) {x : ℝ}
    (hx : x ∈ A) :
    sInf (connectedComponentIn A x) ∈ connectedComponentIn A x ∧
      sSup (connectedComponentIn A x) ∈ connectedComponentIn A x ∧
      connectedComponentIn A x =
        Icc (sInf (connectedComponentIn A x)) (sSup (connectedComponentIn A x)) := by
  set K := connectedComponentIn A x with hK
  have hKA : K ⊆ A := connectedComponentIn_subset A x
  have hKne : K.Nonempty := ⟨x, mem_connectedComponentIn hx⟩
  have hKpre : IsPreconnected K := isPreconnected_connectedComponentIn
  have hKcl : IsClosed K := by
    have h1 : closure K ⊆ K := by
      have h2 : closure K ⊆ A := closure_minimal hKA hA
      exact hKpre.closure.subset_connectedComponentIn (subset_closure (mem_connectedComponentIn hx))
        h2
    exact closure_subset_iff_isClosed.1 h1
  have hbdd : BddAbove K := ⟨1, fun y hy => (hAb (hKA hy)).2⟩
  have hbdd' : BddBelow K := ⟨0, fun y hy => (hAb (hKA hy)).1⟩
  have hs : sInf K ∈ K := hKcl.csInf_mem hKne hbdd'
  have he : sSup K ∈ K := hKcl.csSup_mem hKne hbdd
  refine ⟨hs, he, Subset.antisymm (fun y hy => ⟨csInf_le hbdd' hy, le_csSup hbdd hy⟩) ?_⟩
  exact hKpre.Icc_subset hs he

/-- **A closed `A ⊆ [0, 1]` with finite frontier and no isolated point is a finite disjoint union
of nondegenerate closed intervals with endpoints in the frontier.** -/
theorem exists_Icc_decomposition_OBDd {A F : Set ℝ} (hA : IsClosed A) (hAb : A ⊆ Icc 0 1)
    (hF : F.Finite) (hfr : frontier A ⊆ F)
    (hiso : ∀ t ∈ A, ∀ δ > 0, ∃ t' ∈ A, t' ≠ t ∧ |t' - t| < δ) :
    ∃ (N : ℕ) (s e : Fin N → ℝ), (∀ i, s i < e i) ∧
      (∀ i, s i ∈ frontier A ∧ e i ∈ frontier A) ∧ A = ⋃ i, Icc (s i) (e i) ∧
      Pairwise fun i j => Disjoint (Icc (s i) (e i)) (Icc (s j) (e j)) := by
  classical
  let P : Set (ℝ × ℝ) := {p | ∃ x ∈ A, p = (sInf (connectedComponentIn A x),
    sSup (connectedComponentIn A x))}
  have hbdd : ∀ x, BddBelow (connectedComponentIn A x) := fun x =>
    ⟨0, fun y hy => (hAb (connectedComponentIn_subset A x hy)).1⟩
  have hbdd' : ∀ x, BddAbove (connectedComponentIn A x) := fun x =>
    ⟨1, fun y hy => (hAb (connectedComponentIn_subset A x hy)).2⟩
  -- the endpoints are frontier points
  have hfrs : ∀ x ∈ A, sInf (connectedComponentIn A x) ∈ frontier A := fun x hx => by
    obtain ⟨hinf, -, -⟩ := connectedComponentIn_eq_Icc_OBDd hA hAb hx
    have hsA : sInf (connectedComponentIn A x) ∈ A := connectedComponentIn_subset A x hinf
    refine ⟨subset_closure hsA, fun hint => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior _ hint
    have hIoo : Ioo (sInf (connectedComponentIn A x) - ε) (sInf (connectedComponentIn A x) + ε) ⊆
        A := fun z hz => interior_subset (hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hz.1, hz.2]))
    have hsub : Ioo (sInf (connectedComponentIn A x) - ε)
        (sInf (connectedComponentIn A x) + ε) ⊆ connectedComponentIn A x :=
      Ioo_subset_connectedComponentIn_OBDd hinf hε hIoo
    have hmem : sInf (connectedComponentIn A x) - ε / 2 ∈ connectedComponentIn A x :=
      hsub ⟨by linarith, by linarith⟩
    have := csInf_le (hbdd x) hmem
    linarith
  have hfre : ∀ x ∈ A, sSup (connectedComponentIn A x) ∈ frontier A := fun x hx => by
    obtain ⟨-, hsup, -⟩ := connectedComponentIn_eq_Icc_OBDd hA hAb hx
    have hsA : sSup (connectedComponentIn A x) ∈ A := connectedComponentIn_subset A x hsup
    refine ⟨subset_closure hsA, fun hint => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior _ hint
    have hIoo : Ioo (sSup (connectedComponentIn A x) - ε) (sSup (connectedComponentIn A x) + ε) ⊆
        A := fun z hz => interior_subset (hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hz.1, hz.2]))
    have hsub : Ioo (sSup (connectedComponentIn A x) - ε)
        (sSup (connectedComponentIn A x) + ε) ⊆ connectedComponentIn A x :=
      Ioo_subset_connectedComponentIn_OBDd hsup hε hIoo
    have hmem : sSup (connectedComponentIn A x) + ε / 2 ∈ connectedComponentIn A x :=
      hsub ⟨by linarith, by linarith⟩
    have := le_csSup (hbdd' x) hmem
    linarith
  -- nondegeneracy
  have hlt : ∀ x ∈ A, sInf (connectedComponentIn A x) < sSup (connectedComponentIn A x) := by
    intro x hx
    by_contra hnlt
    have hle : sInf (connectedComponentIn A x) ≤ sSup (connectedComponentIn A x) :=
      (csInf_le (hbdd x) (mem_connectedComponentIn hx)).trans
        (le_csSup (hbdd' x) (mem_connectedComponentIn hx))
    have heq : sInf (connectedComponentIn A x) = sSup (connectedComponentIn A x) :=
      le_antisymm hle (not_lt.1 hnlt)
    obtain ⟨hinf, -, hcomp⟩ := connectedComponentIn_eq_Icc_OBDd hA hAb hx
    set c := sInf (connectedComponentIn A x) with hc
    have hcA : c ∈ A := connectedComponentIn_subset A x hinf
    have hcF : c ∈ F := hfr (hfrs x hx)
    have hKc : connectedComponentIn A x = {c} := by
      rw [hcomp, ← heq]
      exact Icc_self c
    have hxc : x = c := by
      have : x ∈ connectedComponentIn A x := mem_connectedComponentIn hx
      rw [hKc] at this
      exact this
    have hFc : IsClosed (F \ {c}) := (hF.sdiff).isClosed
    obtain ⟨δ, hδ, hδF⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl c (fun h => h.2 rfl)
    have hnoF : ∀ z, |z - c| < δ → z ≠ c → z ∉ F := by
      intro z hz hzc hzF
      have hzball : z ∈ Metric.ball c δ := by
        rw [Metric.mem_ball, Real.dist_eq]
        exact hz
      exact hδF hzball ⟨hzF, hzc⟩
    obtain ⟨t', ht'A, ht'ne, ht'δ⟩ := hiso c hcA δ hδ
    have ht'abs := abs_lt.1 ht'δ
    rcases lt_or_gt_of_ne ht'ne with hlt' | hgt'
    · have hfr' : Ioo (c - δ) c ∩ frontier A = ∅ := by
        apply eq_empty_of_forall_notMem
        rintro z ⟨hz, hzf⟩
        exact hnoF z (by rw [abs_lt]; constructor <;> linarith [hz.1, hz.2]) (ne_of_lt hz.2)
          (hfr hzf)
      have hsub1 := Ioo_subset_of_meets_of_inter_frontier_eq_empty_OBDd hfr' ht'A
        ⟨by linarith [ht'abs.1], hlt'⟩
      have hIcc : Icc t' c ⊆ A := by
        intro z hz
        rcases eq_or_lt_of_le hz.2 with hzc | hzc
        · rw [hzc]; exact hcA
        · rcases eq_or_lt_of_le hz.1 with hzt | hzt
          · rw [← hzt]; exact ht'A
          · exact hsub1 ⟨by linarith [ht'abs.1], hzc⟩
      have hsub2 : Icc t' c ⊆ connectedComponentIn A x := by
        rw [hxc]
        exact isPreconnected_Icc.subset_connectedComponentIn ⟨hlt'.le, le_rfl⟩ hIcc
      rw [hKc] at hsub2
      exact ht'ne (hsub2 ⟨le_rfl, hlt'.le⟩)
    · have hfr' : Ioo c (c + δ) ∩ frontier A = ∅ := by
        apply eq_empty_of_forall_notMem
        rintro z ⟨hz, hzf⟩
        exact hnoF z (by rw [abs_lt]; constructor <;> linarith [hz.1, hz.2]) (ne_of_gt hz.1)
          (hfr hzf)
      have hsub1 := Ioo_subset_of_meets_of_inter_frontier_eq_empty_OBDd hfr' ht'A
        ⟨hgt', by linarith [ht'abs.2]⟩
      have hIcc : Icc c t' ⊆ A := by
        intro z hz
        rcases eq_or_lt_of_le hz.1 with hzc | hzc
        · rw [← hzc]; exact hcA
        · rcases eq_or_lt_of_le hz.2 with hzt | hzt
          · rw [hzt]; exact ht'A
          · exact hsub1 ⟨hzc, by linarith [ht'abs.2]⟩
      have hsub2 : Icc c t' ⊆ connectedComponentIn A x := by
        rw [hxc]
        exact isPreconnected_Icc.subset_connectedComponentIn ⟨le_rfl, hgt'.le⟩ hIcc
      rw [hKc] at hsub2
      exact ht'ne.symm (hsub2 ⟨hgt'.le, le_rfl⟩).symm
  have hPfin : P.Finite := by
    refine (hF.prod hF).subset ?_
    rintro p ⟨x, hx, rfl⟩
    exact ⟨hfr (hfrs x hx), hfr (hfre x hx)⟩
  have hdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (Icc p.1 p.2) (Icc q.1 q.2) := by
    rintro p ⟨x, hx, rfl⟩ q ⟨x', hx', rfl⟩ hpq
    rw [Set.disjoint_left]
    intro y hy hy'
    apply hpq
    obtain ⟨-, -, hc1⟩ := connectedComponentIn_eq_Icc_OBDd hA hAb hx
    obtain ⟨-, -, hc2⟩ := connectedComponentIn_eq_Icc_OBDd hA hAb hx'
    have hy1 : y ∈ connectedComponentIn A x := by rw [hc1]; exact hy
    have hy2 : y ∈ connectedComponentIn A x' := by rw [hc2]; exact hy'
    have := (connectedComponentIn_eq hy1).trans (connectedComponentIn_eq hy2).symm
    rw [this]
  have : Finite ↥P := hPfin.to_subtype
  obtain ⟨N, ⟨eq⟩⟩ := Finite.exists_equiv_fin ↥P
  have hP : ∀ i, ∃ x ∈ A, ((eq.symm i : P) : ℝ × ℝ) =
      (sInf (connectedComponentIn A x), sSup (connectedComponentIn A x)) :=
    fun i => (eq.symm i).2
  refine ⟨N, fun i => ((eq.symm i : P) : ℝ × ℝ).1, fun i => ((eq.symm i : P) : ℝ × ℝ).2,
    fun i => ?_, fun i => ?_, ?_, fun i j hij => ?_⟩
  · obtain ⟨x, hx, hp⟩ := hP i
    change ((eq.symm i : P) : ℝ × ℝ).1 < ((eq.symm i : P) : ℝ × ℝ).2
    rw [hp]
    exact hlt x hx
  · obtain ⟨x, hx, hp⟩ := hP i
    change ((eq.symm i : P) : ℝ × ℝ).1 ∈ frontier A ∧ ((eq.symm i : P) : ℝ × ℝ).2 ∈ frontier A
    rw [hp]
    exact ⟨hfrs x hx, hfre x hx⟩
  · ext y
    constructor
    · intro hy
      obtain ⟨-, -, hc⟩ := connectedComponentIn_eq_Icc_OBDd hA hAb hy
      let q : P := ⟨(sInf (connectedComponentIn A y), sSup (connectedComponentIn A y)), y, hy, rfl⟩
      refine mem_iUnion.2 ⟨eq q, ?_⟩
      change y ∈ Icc ((eq.symm (eq q) : P) : ℝ × ℝ).1 ((eq.symm (eq q) : P) : ℝ × ℝ).2
      rw [Equiv.symm_apply_apply]
      change y ∈ Icc (sInf (connectedComponentIn A y)) (sSup (connectedComponentIn A y))
      rw [← hc]
      exact mem_connectedComponentIn hy
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.1 hy
      obtain ⟨x, hx, hp⟩ := hP i
      obtain ⟨-, -, hc⟩ := connectedComponentIn_eq_Icc_OBDd hA hAb hx
      have h1 : y ∈ connectedComponentIn A x := by
        rw [hc]
        change y ∈ Icc ((eq.symm i : P) : ℝ × ℝ).1 ((eq.symm i : P) : ℝ × ℝ).2 at hi
        rw [hp] at hi
        exact hi
      exact connectedComponentIn_subset A x h1
  · exact hdisj _ (eq.symm i).2 _ (eq.symm j).2 (fun h => hij (eq.symm.injective (Subtype.ext h)))

end DifferentialGeometry.Topology

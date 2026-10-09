/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallVocabulary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂} {f₁ : M₁ → M₂}

omit [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem finite_setOf_section34Incident (t : Section34SimplexIndex 𝒦 4) :
    {s : Section34SimplexIndex 𝒦 3 | Section34Incident s.1 t.1}.Finite := by
  have hsub : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 → s.1 ⊆ t.1 :=
    fun s hs v hv => mem_of_mem_convexHull_of_singleton_mem 𝒦.complex
      (𝒦.complex.down_closed s.2.1 (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)) t.2.1 (hs (Finset.mem_coe.mpr hv))
  exact (t.1.powerset.finite_toSet.preimage Subtype.val_injective.injOn).subset
    fun s hs => Finset.mem_coe.mpr (Finset.mem_powerset.mpr (hsub s hs))

theorem exists_section34FaceBallInvariants_forall_not_rank_lt
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂} {tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd fbl fblBd) :
    ∃ fbl' fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd fbl' fblBd' ∧
      ∀ (g gBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3),
        Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd g gBd →
        (∀ s', s' ≠ s → g s' = fbl' s' ∧ gBd s' = fblBd' s') →
        ¬ section34FaceBallRank tgtV tgtEBd gBd s <
          section34FaceBallRank tgtV tgtEBd fblBd' s := by
  classical
  let P := {x : (Section34SimplexIndex 𝒦 3 → Set M₂) × (Section34SimplexIndex 𝒦 3 → Set M₂) //
    Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd x.1 x.2}
  let rk : P → Section34SimplexIndex 𝒦 3 → ℕ := fun p s =>
    section34FaceBallRank tgtV tgtEBd p.1.2 s
  let r : P → P → Prop := fun p q => ∀ s,
    (q.1.1 s = p.1.1 s ∧ q.1.2 s = p.1.2 s) ∨ rk q s < rk p s
  have hrk : ∀ (p q : P) (s : Section34SimplexIndex 𝒦 3), p.1.2 s = q.1.2 s → rk p s = rk q s :=
    fun p q s hs => section34FaceBallRank_congr hs
  have htrans : ∀ {a b d : P}, r a b → r b d → r a d := by
    intro a b d hab hbd s
    rcases hab s with ⟨h1, h2⟩ | h1 <;> rcases hbd s with ⟨h3, h4⟩ | h3
    · exact Or.inl ⟨h3.trans h1, h4.trans h2⟩
    · exact Or.inr (h3.trans_eq (hrk b a s h2))
    · exact Or.inr ((hrk d b s h4).trans_lt h1)
    · exact Or.inr (h3.trans h1)
  have hbound : ∀ c : Set P, IsChain r c → ∃ ub, ∀ a ∈ c, r a ub := by
    intro c hc
    rcases c.eq_empty_or_nonempty with hce | hce
    · exact ⟨⟨(fbl, fblBd), hinv⟩, fun a ha => by rw [hce] at ha; exact ha.elim⟩
    have hmin : ∀ s, ∃ p ∈ c, ∀ q ∈ c, rk p s ≤ rk q s := by
      intro s
      obtain ⟨n, ⟨p, hp, rfl⟩, hn⟩ :=
        (wellFounded_lt (α := ℕ)).has_min ((fun p => rk p s) '' c) (hce.image _)
      exact ⟨p, hp, fun q hq => not_lt.mp (hn _ ⟨q, hq, rfl⟩)⟩
    choose pm hpm hpmin using hmin
    obtain ⟨ub1, hub1⟩ : ∃ f : Section34SimplexIndex 𝒦 3 → Set M₂,
        ∀ s, f s = (pm s).1.1 s := ⟨_, fun _ => rfl⟩
    obtain ⟨ub2, hub2⟩ : ∃ f : Section34SimplexIndex 𝒦 3 → Set M₂,
        ∀ s, f s = (pm s).1.2 s := ⟨_, fun _ => rfl⟩
    have hprop : ∀ p ∈ c, ∀ q ∈ c, ∀ s, (p.1.1 s = ub1 s ∧ p.1.2 s = ub2 s) → r p q →
        (q.1.1 s = ub1 s ∧ q.1.2 s = ub2 s) := by
      intro p hp q hq s ⟨h1, h2⟩ hpq
      rcases hpq s with ⟨h3, h4⟩ | h3
      · exact ⟨h3.trans h1, h4.trans h2⟩
      · have hps : rk p s = rk (pm s) s := hrk p (pm s) s (h2.trans (hub2 s))
        exact absurd (hpmin s q hq) (not_le.mpr (h3.trans_eq hps))
    have hpmub : ∀ s, (pm s).1.1 s = ub1 s ∧ (pm s).1.2 s = ub2 s :=
      fun s => ⟨(hub1 s).symm, (hub2 s).symm⟩
    have hloc : ∀ F : Finset (Section34SimplexIndex 𝒦 3),
        ∃ q ∈ c, ∀ s ∈ F, q.1.1 s = ub1 s ∧ q.1.2 s = ub2 s := by
      intro F
      induction F using Finset.induction_on with
      | empty =>
        obtain ⟨q, hq⟩ := hce
        exact ⟨q, hq, fun s hs => absurd hs (Finset.notMem_empty s)⟩
      | @insert a F _ ih =>
        obtain ⟨q, hq, hqF⟩ := ih
        by_cases hqa : q = pm a
        · refine ⟨q, hq, fun s hs => ?_⟩
          rcases Finset.mem_insert.mp hs with hsa | hs
          · rw [hsa, hqa]
            exact hpmub a
          · exact hqF s hs
        rcases hc hq (hpm a) hqa with hr | hr
        · refine ⟨pm a, hpm a, fun s hs => ?_⟩
          rcases Finset.mem_insert.mp hs with hsa | hs
          · rw [hsa]
            exact hpmub a
          · exact hprop q hq (pm a) (hpm a) s (hqF s hs) hr
        · refine ⟨q, hq, fun s hs => ?_⟩
          rcases Finset.mem_insert.mp hs with hsa | hs
          · rw [hsa]
            exact hprop (pm a) (hpm a) q hq a (hpmub a) hr
          · exact hqF s hs
    have hget : ∀ F : Finset (Section34SimplexIndex 𝒦 3),
        ∃ q : P, ∀ s ∈ F, q.1.1 s = ub1 s ∧ q.1.2 s = ub2 s := fun F => by
      obtain ⟨q, -, hq⟩ := hloc F
      exact ⟨q, hq⟩
    have hinvub : Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd ub1 ub2 := by
      obtain ⟨q₀, -⟩ := hget ∅
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hext₀, -⟩ := q₀.2
      refine ⟨fun s => ?_, fun s => ?_, fun s w hsw => ?_, fun s s' hss' => ?_, fun s => ?_,
        fun s e => ?_, fun s => ?_, fun s => ?_, fun s => ?_, ?_, hext₀, ?_⟩
      · obtain ⟨q, hq⟩ := hget {s}
        obtain ⟨h1, h2⟩ := hq s (Finset.mem_singleton_self s)
        rw [← h1, ← h2]
        exact q.2.1 s
      · obtain ⟨q, hq⟩ := hget {s}
        obtain ⟨h1, -⟩ := hq s (Finset.mem_singleton_self s)
        rw [← h1]
        exact q.2.2.1 s
      · obtain ⟨q, hq⟩ := hget {s}
        obtain ⟨h1, -⟩ := hq s (Finset.mem_singleton_self s)
        rw [← h1]
        exact q.2.2.2.1 s w hsw
      · obtain ⟨q, hq⟩ := hget {s, s'}
        obtain ⟨h1, -⟩ := hq s (Finset.mem_insert_self s {s'})
        obtain ⟨h1', -⟩ := hq s' (Finset.mem_insert_of_mem (Finset.mem_singleton_self s'))
        rw [← h1, ← h1']
        exact q.2.2.2.2.1 s s' hss'
      · obtain ⟨q, hq⟩ := hget {s}
        obtain ⟨-, h2⟩ := hq s (Finset.mem_singleton_self s)
        rw [← h2]
        exact q.2.2.2.2.2.1 s
      · obtain ⟨q, hq⟩ := hget {s}
        obtain ⟨-, h2⟩ := hq s (Finset.mem_singleton_self s)
        rw [← h2]
        exact q.2.2.2.2.2.2.1 s e
      · obtain ⟨q, hq⟩ := hget {s}
        obtain ⟨-, h2⟩ := hq s (Finset.mem_singleton_self s)
        rw [← h2]
        exact q.2.2.2.2.2.2.2.1 s
      · obtain ⟨q, hq⟩ := hget {s}
        obtain ⟨-, h2⟩ := hq s (Finset.mem_singleton_self s)
        rw [← h2]
        exact q.2.2.2.2.2.2.2.2.1 s
      · obtain ⟨q, hq⟩ := hget {s}
        obtain ⟨-, h2⟩ := hq s (Finset.mem_singleton_self s)
        have hfin := q.2.2.2.2.2.2.2.2.2.1 s
        simp only [section34TraceComponents] at hfin ⊢
        rwa [← h2]
      · intro t y hy
        rw [section34TetraObstacle, mem_union] at hy
        rcases hy with hy | hy
        · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
          exact q₀.2.2.2.2.2.2.2.2.2.2.1 t (Or.inl (mem_iUnion₂.mpr ⟨x, hx, hyx⟩))
        · obtain ⟨s, hs, hys⟩ := mem_iUnion₂.mp hy
          obtain ⟨q, hq⟩ := hget {s}
          obtain ⟨h1, -⟩ := hq s (Finset.mem_singleton_self s)
          rw [← h1] at hys
          exact q.2.2.2.2.2.2.2.2.2.2.1 t (Or.inr (mem_iUnion₂.mpr ⟨s, hs, hys⟩))
      · intro t w hw y hy hyH
        have hfin := finite_setOf_section34Incident (𝒦 := 𝒦) t
        obtain ⟨q, hq⟩ := hget hfin.toFinset
        have hobs : section34TetraObstacle tgtV ub1 t = section34TetraObstacle tgtV q.1.1 t := by
          simp only [section34TetraObstacle]
          congr 1
          exact iUnion₂_congr fun s hs => (hq s (hfin.mem_toFinset.mpr hs)).1.symm
        rw [hobs]
        exact q.2.2.2.2.2.2.2.2.2.2.2.2 t w hw y hy hyH
    refine ⟨⟨(ub1, ub2), hinvub⟩, fun a ha s => ?_⟩
    have hubs : rk ⟨(ub1, ub2), hinvub⟩ s = rk (pm s) s := hrk _ (pm s) s (hub2 s)
    by_cases hap : a = pm s
    · subst hap
      exact Or.inl ⟨hub1 s, hub2 s⟩
    rcases hc ha (hpm s) hap with hr | hr
    · rcases hr s with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨(hub1 s).trans h1, (hub2 s).trans h2⟩
      · exact Or.inr (hubs.trans_lt h1)
    · rcases hr s with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨(hub1 s).trans h1.symm, (hub2 s).trans h2.symm⟩
      · exact absurd (hpmin s a ha) (not_le.mpr h1)
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hbound htrans
  refine ⟨m.1.1, m.1.2, m.2, fun g gBd s hg hoff hlt => ?_⟩
  have hr : r m ⟨(g, gBd), hg⟩ := by
    intro s'
    by_cases hs : s' = s
    · subst hs
      exact Or.inr hlt
    · exact Or.inl (hoff s' hs)
  rcases hm _ hr s with ⟨-, h2⟩ | h1
  · exact absurd (hrk m ⟨(g, gBd), hg⟩ s h2) (ne_of_lt hlt).symm
  · exact lt_asymm hlt h1

theorem exists_section34TerminalFaceBalls
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcomp : ∀ (g gBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3),
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) g gBd →
      Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
        (section34SplitDiskImage src f₁) g gBd s →
      ∃ g' gBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
        Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
          (section34SplitDiskImage srcBd f₁) g' gBd' ∧
        (∀ s', s' ≠ s → g' s' = g s' ∧ gBd' s' = gBd s') ∧
        section34FaceBallRank (section34VertexBallImage src f₁)
            (section34SplitDiskImage srcBd f₁) gBd' s <
          section34FaceBallRank (section34VertexBallImage src f₁)
            (section34SplitDiskImage srcBd f₁) gBd s)
    (hslide : ∀ (g gBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3),
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) g gBd →
      Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage src f₁)
        (section34VertexBallImage srcBd f₁) (section34SplitDiskImage src f₁)
        (section34SplitDiskImage srcBd f₁) gBd s →
      ∃ g' gBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
        Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
          (section34SplitDiskImage srcBd f₁) g' gBd' ∧
        (∀ s', s' ≠ s → g' s' = g s' ∧ gBd' s' = gBd s') ∧
        section34FaceBallRank (section34VertexBallImage src f₁)
            (section34SplitDiskImage srcBd f₁) gBd' s <
          section34FaceBallRank (section34VertexBallImage src f₁)
            (section34SplitDiskImage srcBd f₁) gBd s) :
    ∃ fbl' fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s, ¬ Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
        (section34SplitDiskImage src f₁) fbl' fblBd' s) ∧
      ∀ s, ¬ Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage src f₁)
        (section34VertexBallImage srcBd f₁) (section34SplitDiskImage src f₁)
        (section34SplitDiskImage srcBd f₁) fblBd' s := by
  obtain ⟨fbl', fblBd', hinv', hmax⟩ := exists_section34FaceBallInvariants_forall_not_rank_lt hinv
  refine ⟨fbl', fblBd', hinv', fun s hop => ?_, fun s hop => ?_⟩
  · obtain ⟨g', gBd', hg', hoff, hlt⟩ := hcomp fbl' fblBd' s hinv' hop
    exact hmax g' gBd' s hg' hoff hlt
  · obtain ⟨g', gBd', hg', hoff, hlt⟩ := hslide fbl' fblBd' s hinv' hop
    exact hmax g' gBd' s hg' hoff hlt

end DifferentialGeometry.Topology.PiecewiseLinear

import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe v

section Descent

variable {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {tgtV tgtVBd : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {tgtE tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}

theorem exists_face_ball_family_without_admissible_moves (hK : K.faces.Finite)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hinv : Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl fblBd)
    (hcomp : ∀ (g gBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
      (s : Section34CompactSimplexIndex K 3),
      Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd g gBd →
      Section34CompactCompression K K' tgtVBd tgtE g gBd s →
      ∃ g' gBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
        Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd g' gBd' ∧
        (∀ s', s' ≠ s → g' s' = g s' ∧ gBd' s' = gBd s') ∧
        section34CompactFaceBallRank tgtV tgtEBd gBd' s <
          section34CompactFaceBallRank tgtV tgtEBd gBd s)
    (hslide : ∀ (g gBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
      (s : Section34CompactSimplexIndex K 3),
      Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd g gBd →
      Section34CompactBigonSlide K K' tgtV tgtVBd tgtE tgtEBd gBd s →
      ∃ g' gBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
        Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd g' gBd' ∧
        (∀ s', s' ≠ s → g' s' = g s' ∧ gBd' s' = gBd s') ∧
        section34CompactFaceBallRank tgtV tgtEBd gBd' s <
          section34CompactFaceBallRank tgtV tgtEBd gBd s) :
    ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
      Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl' fblBd' ∧
      (∀ s, ¬ Section34CompactCompression K K' tgtVBd tgtE fbl' fblBd' s) ∧
      ∀ s, ¬ Section34CompactBigonSlide K K' tgtV tgtVBd tgtE tgtEBd fblBd' s := by
  classical
  have hfin := finite_section34CompactSimplexIndex hK 3
  let _ : Fintype (Section34CompactSimplexIndex K 3) := Fintype.ofFinite _
  have hdrop : ∀ (gBd gBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
      (s : Section34CompactSimplexIndex K 3), (∀ s', s' ≠ s → gBd' s' = gBd s') →
      section34CompactFaceBallRank tgtV tgtEBd gBd' s <
        section34CompactFaceBallRank tgtV tgtEBd gBd s →
      ∑ s', section34CompactFaceBallRank tgtV tgtEBd gBd' s' <
        ∑ s', section34CompactFaceBallRank tgtV tgtEBd gBd s' := by
    intro gBd gBd' s hoff hlt
    refine Finset.sum_lt_sum (fun s' _ => ?_) ⟨s, Finset.mem_univ s, hlt⟩
    by_cases hs : s' = s
    · subst hs
      exact hlt.le
    · exact (section34CompactFaceBallRank_congr (hoff s' hs)).le
  suffices key : ∀ n : ℕ,
      ∀ g gBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
        ∑ s', section34CompactFaceBallRank tgtV tgtEBd gBd s' = n →
        Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd g gBd →
        ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
          Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl' fblBd' ∧
          (∀ s, ¬ Section34CompactCompression K K' tgtVBd tgtE fbl' fblBd' s) ∧
          ∀ s, ¬ Section34CompactBigonSlide K K' tgtV tgtVBd tgtE tgtEBd fblBd' s from
    key _ fbl fblBd rfl hinv
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g gBd hn hg
    by_cases hc : ∃ s, Section34CompactCompression K K' tgtVBd tgtE g gBd s
    · obtain ⟨s, hs⟩ := hc
      obtain ⟨g', gBd', hinv', hoff, hlt⟩ := hcomp g gBd s hg hs
      exact ih _ (hn ▸ hdrop gBd gBd' s (fun s' hs' => (hoff s' hs').2) hlt) g' gBd' rfl hinv'
    · by_cases hb : ∃ s, Section34CompactBigonSlide K K' tgtV tgtVBd tgtE tgtEBd gBd s
      · obtain ⟨s, hs⟩ := hb
        obtain ⟨g', gBd', hinv', hoff, hlt⟩ := hslide g gBd s hg hs
        exact ih _ (hn ▸ hdrop gBd gBd' s (fun s' hs' => (hoff s' hs').2) hlt) g' gBd' rfl
          hinv'
      · exact ⟨g, gBd, hg, not_exists.mp hc, not_exists.mp hb⟩

end Descent

end DifferentialGeometry.Topology.PiecewiseLinear

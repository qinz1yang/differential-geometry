import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacets
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem mem_boundaryComplex_iff_of_delete_facet [dE : DecidableEq E] {n : ℕ}
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L) (hLK : L.faces ⊆ K.faces)
    {t : Finset E} (ht : t ∈ K.faces) (htcard : t.card = n + 2)
    (hdelete : ∀ u ∈ K.faces, u.card = n + 2 → (u ∈ L.faces ↔ u ≠ t))
    {s : Finset E} (hscard : s.card = n + 1) :
    s ∈ (boundaryComplex (n + 1) L).faces ↔ s ∈ K.faces ∧
      if s ⊆ t then s ∉ (boundaryComplex (n + 1) K).faces
      else s ∈ (boundaryComplex (n + 1) K).faces := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  by_cases hs : s ∈ K.faces
  · simp only [hs, true_and]
    rw [hL.mem_boundaryComplex_iff_unique_coface L hscard,
      hK.mem_boundaryComplex_iff_unique_coface K hscard]
    have hcoface (w : E) :
        (w ∉ s ∧ insert w s ∈ L.faces) ↔
          w ∉ s ∧ insert w s ∈ K.faces ∧ insert w s ≠ t := by
      constructor
      · rintro ⟨hws, hw⟩
        exact ⟨hws, hLK hw, (hdelete _ (hLK hw) (by
          rw [Finset.card_insert_of_notMem hws, hscard])).mp hw⟩
      · rintro ⟨hws, hw, hwt⟩
        exact ⟨hws, (hdelete _ hw (by rw [Finset.card_insert_of_notMem hws, hscard])).mpr hwt⟩
    by_cases hst : s ⊆ t
    · rw [if_pos hst]
      obtain ⟨a, has, hat⟩ := Finset.exists_eq_insert_iff.mpr ⟨hst, by omega⟩
      have haV : a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces} := ⟨has, hat.symm ▸ ht⟩
      have heq : {w | w ∉ s ∧ insert w s ∈ L.faces} =
          {w | w ∉ s ∧ insert w s ∈ K.faces} \ {a} := by
        ext w
        simp only [mem_ofPred_eq, mem_sdiff, mem_singleton_iff, hcoface]
        by_cases hws : w ∈ s
        · simp only [hws, not_true_eq_false, false_and]
        · constructor
          · rintro ⟨hw, hwK, hwt⟩
            exact ⟨⟨hw, hwK⟩, fun hwa => hwt (hwa.symm ▸ hat)⟩
          · rintro ⟨⟨hw, hwK⟩, hwa⟩
            exact ⟨hw, hwK, fun hwt => hwa ((Finset.insert_inj hws).mp (hwt.trans hat.symm))⟩
      rw [heq]
      rcases hK.codimension_one_cofaces K hs hscard with ⟨b, hb⟩ | ⟨b, c, hbc, hV⟩
      · have hab : a = b := by simpa only [hb, mem_singleton_iff] using haV
        subst b
        rw [hb]
        simp
      · have ha : a = b ∨ a = c := by simpa only [hV, mem_insert_iff, mem_singleton_iff] using haV
        have hnot : ¬∃ z, ({b, c} : Set E) = {z} := by
          rintro ⟨z, hz⟩
          have hbz : b = z := by
            have hmem : b ∈ ({b, c} : Set E) := mem_insert b {c}
            simpa only [hz, mem_singleton_iff] using hmem
          have hcz : c = z := by
            have hmem : c ∈ ({b, c} : Set E) := mem_insert_of_mem b (mem_singleton c)
            simpa only [hz, mem_singleton_iff] using hmem
          exact hbc (hbz.trans hcz.symm)
        rw [hV]
        refine ⟨fun _ => hnot, fun _ => ?_⟩
        rcases ha with rfl | rfl
        · refine ⟨c, ?_⟩
          ext x
          simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
          aesop
        · refine ⟨b, ?_⟩
          ext x
          simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
          aesop
    · rw [if_neg hst]
      have heq : {w | w ∉ s ∧ insert w s ∈ L.faces} =
          {w | w ∉ s ∧ insert w s ∈ K.faces} := by
        ext w
        simp only [mem_ofPred_eq, hcoface]
        have hwt : insert w s ≠ t := fun h => hst (h ▸ Finset.subset_insert w s)
        exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hwt⟩⟩
      rw [heq]
  · simp only [hs, false_and, iff_false]
    exact fun h => hs (hLK (boundaryComplex_faces_subset (n + 1) L h))

theorem boundaryComplex_space_of_delete_facet [dE : DecidableEq E] {n : ℕ}
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsPLBall (n + 1) K.space) (hL : IsPLBall (n + 1) L.space)
    (hLK : L.faces ⊆ K.faces) {t : Finset E} (ht : t ∈ K.faces) (htcard : t.card = n + 2)
    (hdelete : ∀ u ∈ K.faces, u.card = n + 2 → (u ∈ L.faces ↔ u ≠ t)) :
    (boundaryComplex (n + 1) L).space =
      closure ((boundaryComplex (n + 1) K).space \ convexHull ℝ (t : Set E)) ∪
        closure ((simplexBoundary t (K.indep ht)).space \ (boundaryComplex (n + 1) K).space) := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  let B := boundaryComplex (n + 1) K
  let B' := boundaryComplex (n + 1) L
  let T := simplexBoundary t (K.indep ht)
  have hBfin : Finite B.faces := (boundaryComplex_faces_finite (n + 1) K).to_subtype
  have hB'fin : Finite B'.faces := (boundaryComplex_faces_finite (n + 1) L).to_subtype
  have hTfin : Finite T.faces := (simplexBoundary_faces_finite t (K.indep ht)).to_subtype
  have hB := isPLSphere_boundaryComplex_space_of_isPLBall (n := n) K hK
  have hB' := isPLSphere_boundaryComplex_space_of_isPLBall (n := n) L hL
  have hT : IsPLSphere n T.space := by
    let M := simplexComplex t (K.indep ht)
    have hMfin : Finite M.faces := (simplexComplex_faces_finite t (K.indep ht)).to_subtype
    have hM : IsPLBall (n + 1) M.space := by
      rw [show M.space = convexHull ℝ (t : Set E) from
        simplexComplex_space t (K.indep ht) (K.nonempty_of_mem_faces ht)]
      exact isPLBall_convexHull_of_affineIndependent t (K.indep ht) htcard
    have h := isPLSphere_boundaryComplex_space_of_isPLBall (n := n) M hM
    rwa [show M = simplexComplex t (K.indep ht) from rfl,
      boundaryComplex_simplexComplex (K.indep ht) htcard] at h
  have hTK : T.faces ⊆ K.faces := fun s hs => K.down_closed ht hs.1 hs.2.1
  have hmem {s : Finset E} (hscard : s.card = n + 1) :
      s ∈ B'.faces ↔ s ∈ K.faces ∧ if s ⊆ t then s ∉ B.faces else s ∈ B.faces :=
    mem_boundaryComplex_iff_of_delete_facet K L hK.isCombinatorialManifoldWithBoundary
      hL.isCombinatorialManifoldWithBoundary hLK ht htcard hdelete hscard
  change B'.space = closure (B.space \ convexHull ℝ (t : Set E)) ∪ closure (T.space \ B.space)
  rw [closure_space_sdiff_convexHull_eq_subcomplexGeneratedBy K B
      (boundaryComplex_faces_subset (n + 1) K) ht,
    closure_space_sdiff_space_eq_subcomplexGeneratedBy K T B hTK
      (boundaryComplex_faces_subset (n + 1) K), subcomplexGeneratedBy_space,
    subcomplexGeneratedBy_space]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := B'.mem_space_iff.mp hx
    obtain ⟨u, hu, hsu, hucard⟩ := exists_face_superset_card_eq_of_isPLSphere B' hB' hs
    have hxu := convexHull_mono (Finset.coe_subset.mpr hsu) hxs
    obtain ⟨huK, huB⟩ := (hmem hucard).mp hu
    by_cases hut : u ⊆ t
    · have huT : u ∈ T.faces := ⟨hut, K.nonempty_of_mem_faces huK, fun heq => by
        have hc := congrArg Finset.card heq
        omega⟩
      exact Or.inr (mem_iUnion₂.mpr ⟨u, ⟨huT, by
        change u ∉ B.faces
        simpa only [if_pos hut] using huB⟩, hxu⟩)
    · exact Or.inl (mem_iUnion₂.mpr ⟨u, ⟨by simpa only [if_neg hut] using huB, hut⟩, hxu⟩)
  · rintro x (hx | hx)
    · obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
      obtain ⟨u, hu, hsu, hucard⟩ := exists_face_superset_card_eq_of_isPLSphere B hB hs.1
      have hut : ¬u ⊆ t := fun h => hs.2 (hsu.trans h)
      have huL : u ∈ B'.faces := (hmem hucard).mpr
        ⟨boundaryComplex_faces_subset (n + 1) K hu, by simpa only [if_neg hut] using hu⟩
      exact B'.convexHull_subset_space huL (convexHull_mono (Finset.coe_subset.mpr hsu) hxs)
    · obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
      obtain ⟨u, hu, hsu, hucard⟩ := exists_face_superset_card_eq_of_isPLSphere T hT hs.1
      have huB : u ∉ B.faces := fun h => hs.2 (B.down_closed h hsu (T.nonempty_of_mem_faces hs.1))
      have huL : u ∈ B'.faces := (hmem hucard).mpr
        ⟨hTK hu, by simpa only [if_pos hu.1] using huB⟩
      exact B'.convexHull_subset_space huL (convexHull_mono (Finset.coe_subset.mpr hsu) hxs)

end DifferentialGeometry.Topology.PiecewiseLinear

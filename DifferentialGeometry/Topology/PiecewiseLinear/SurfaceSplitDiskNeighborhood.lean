/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FreeTriangleNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitDerivedCellBase

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
private theorem isPLBall_triangle_subcomplex_cells
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3) :
    IsPLBall 3 (((derivedNeighborhoodCell K s).space ∪
      ⋃ e ∈ s.powersetCard 2, (derivedNeighborhoodCell K e).space) ∪
        ⋃ v ∈ s, (derivedNeighborhoodCell K {v}).space) := by
  classical
  let C := fun t : Finset E => (derivedNeighborhoodCell K t).space
  let edges := s.powersetCard 2
  let B := C s ∪ ⋃ e ∈ edges, C e
  have hedges (e : Finset E) (he : e ∈ edges) :
      e ⊆ s ∧ e.card = 2 := Finset.mem_powersetCard.mp he
  have heK (e : Finset E) (he : e ∈ edges) : e ∈ K.faces :=
    K.down_closed hs (hedges e he).1
      (Finset.card_pos.mp (by rw [(hedges e he).2]; decide))
  have hB : IsPLBall 3 B := hK.isPLBall_union_derivedNeighborhoodCells_of_card hs edges
    (by decide : 0 < 2) (by omega) (fun e he => (hedges e he).1)
    (fun e he => (hedges e he).2)
  suffices h : ∀ a : Finset E, a ⊆ s →
      IsPLBall 3 (B ∪ ⋃ v ∈ a, C {v}) from h s Finset.Subset.rfl
  intro a
  induction a using Finset.induction_on with
  | empty => intro _; simpa using hB
  | @insert v a hva ih =>
    intro has
    have hvs : v ∈ s := has (Finset.mem_insert_self _ _)
    have ha : a ⊆ s := (Finset.subset_insert _ _).trans has
    have hprev := ih ha
    have hvK : {v} ∈ K.faces := K.down_closed hs (Finset.singleton_subset_iff.mpr hvs)
      (Finset.singleton_nonempty v)
    have hvne : ({v} : Finset E) ≠ s := by
      intro heq
      have hc := congrArg Finset.card heq
      simp only [Finset.card_singleton, hcard] at hc
      omega
    let arms := edges.filter (fun e => v ∈ e)
    have harme (e : Finset E) (he : e ∈ arms) : e ∈ edges :=
      Finset.mem_of_mem_filter e he
    have harms (e : Finset E) (he : e ∈ arms) :
        e ≠ {v} ∧ e ≠ s := by
      have hc := (hedges e (harme e he)).2
      constructor <;> intro heq <;> rw [heq] at hc
      · simp only [Finset.card_singleton] at hc
        omega
      · omega
    have hcomp (e : Finset E) (he : e ∈ arms) :
        ({v} ⊆ e ∨ e ⊆ {v}) ∧ (s ⊆ e ∨ e ⊆ s) :=
      ⟨Or.inl (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp he).2),
        Or.inr (hedges e (harme e he)).1⟩
    have hincomp (e : Finset E) (he : e ∈ arms)
        (f : Finset E) (hf : f ∈ arms) (hne : e ≠ f) :
        ¬e ⊆ f ∧ ¬f ⊆ e := by
      have hec := (hedges e (harme e he)).2
      have hfc := (hedges f (harme f hf)).2
      exact ⟨fun h => hne (Finset.eq_of_subset_of_card_le h (by omega)),
        fun h => hne (Finset.eq_of_subset_of_card_le h (by omega)).symm⟩
    have hattach : IsPLBall 2 (C {v} ∩ (C s ∪ ⋃ e ∈ arms, C e)) :=
      hK.isPLBall_derivedNeighborhoodCell_inter_union_of_mem_faces hvK hs hvne
        (Or.inl (Finset.singleton_subset_iff.mpr hvs)) arms
        (fun e he => heK e (harme e he)) harms hcomp hincomp
    have hinter :
        (B ∪ ⋃ w ∈ a, C {w}) ∩ C {v} = C {v} ∩ (C s ∪ ⋃ e ∈ arms, C e) := by
      apply Subset.antisymm
      · rintro x ⟨hx | hx, hxv⟩
        · rcases hx with hxs | hxe
          · exact ⟨hxv, Or.inl hxs⟩
          · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxe
            have hve : v ∈ e := by
              rcases subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K hvK
                  (heK e he) ⟨x, hxv, hxe⟩ with h | h
              · exact Finset.singleton_subset_iff.mp h
              · have hc := Finset.card_le_card h
                rw [(hedges e he).2, Finset.card_singleton] at hc
                omega
            exact ⟨hxv, Or.inr
              (mem_iUnion₂.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hve⟩, hxe⟩)⟩
        · obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hx
          have hwK : {w} ∈ K.faces := K.down_closed hs
            (Finset.singleton_subset_iff.mpr (ha hw)) (Finset.singleton_nonempty w)
          have hwv : w ≠ v := ne_of_mem_of_not_mem hw hva
          have hdis := disjoint_derivedNeighborhoodCell_space K hwK hvK
            (by simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using hwv)
            (by
              simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using hwv.symm)
          exact (hdis.le_bot ⟨hxw, hxv⟩).elim
      · rintro x ⟨hxv, hxs | hxarms⟩
        · exact ⟨Or.inl (Or.inl hxs), hxv⟩
        · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxarms
          exact ⟨Or.inl (Or.inr (mem_iUnion₂.mpr ⟨e, harme e he, hxe⟩)), hxv⟩
    have hI : IsPLBall 2 ((B ∪ ⋃ w ∈ a, C {w}) ∩ C {v}) := hinter.symm ▸ hattach
    have hvball : IsPLBall 3 (C {v}) := hK.isPLBall_derivedNeighborhoodCell hvK
    have hprevK : (B ∪ ⋃ w ∈ a, C {w}) ⊆ K.space :=
      union_subset (union_subset (derivedNeighborhoodCell_space_subset K s)
        (iUnion₂_subset fun e _ => derivedNeighborhoodCell_space_subset K e))
        (iUnion₂_subset fun w _ => derivedNeighborhoodCell_space_subset K {w})
    have h := hK.isPLBall_union_of_inter_isPLBall_two hprev hvball hprevK
      (derivedNeighborhoodCell_space_subset K {v}) hI
    simpa only [Finset.set_biUnion_insert, union_assoc, union_left_comm, union_comm] using h

open Classical in
private theorem IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_triangle_subcomplex
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3) :
    IsPLBall 3 (PiecewiseLinear.derivedNeighborhood K
      (simplexComplex s (K.indep hs))).space := by
  rw [derivedNeighborhood_simplex_space_eq_of_card_le_three K hs (by omega)]
  exact isPLBall_triangle_subcomplex_cells hK hs hcard

section

variable [dE : DecidableEq E] [dP : DecidableEq (EuclideanSpace ℝ (Fin 2))]

open Classical in
private theorem isPLBall_derivedNeighborhood_of_isGlueIso_planar_subcomplex_aux
    (K A : Geometry.SimplicialComplex ℝ E)
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    [Finite K.faces] [Finite A.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hAK : A.faces ⊆ K.faces)
    {φ : E → EuclideanSpace ℝ (Fin 2)} {ψ : EuclideanSpace ℝ (Fin 2) → E}
    (hL : IsPLBall 2 L.space) (hIso : IsGlueIso A L φ ψ)
    {t₀ : Finset E} (ht₀ : t₀ ∈ A.faces) (ht₀card : t₀.card = 3) :
    IsPLBall 3 (derivedNeighborhood K A).space := by
  have hdE : dE = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have hdP : dP = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst dE
  subst dP
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 2)) := Classical.decEq _
  generalize hn : {u ∈ A.faces | u.card = 3}.ncard = n
  induction n using Nat.strong_induction_on generalizing A L with
  | h n ih =>
    have hA := hL.of_isPLHomeomorphOn hIso.symm.isPLHomeomorphOn
    by_cases heq : A.space = convexHull ℝ (t₀ : Set E)
    · have hAsimplex : A = simplexComplex t₀ (A.indep ht₀) := by
        apply Geometry.SimplicialComplex.ext
        ext s
        change s ∈ A.faces ↔ s.Nonempty ∧ s ⊆ t₀
        constructor
        · intro hs
          have hx := centroid_mem_openSimplex_of_mem_faces A s hs
          have hxt : s.centroid ℝ id ∈ convexHull ℝ (t₀ : Set E) :=
            heq ▸ A.convexHull_subset_space hs (openSimplex_subset_convexHull s hx)
          exact ⟨A.nonempty_of_mem_faces hs,
            face_subset_of_mem_openSimplex_of_mem_convexHull A hs ht₀ hx hxt⟩
        · rintro ⟨hsne, hst⟩
          exact A.down_closed ht₀ hst hsne
      rw [hAsimplex]
      exact hK.isPLBall_derivedNeighborhood_triangle_subcomplex (hAK ht₀) ht₀card
    · obtain ⟨t, s, ht, htcard, htt₀, -, hst, hscard, htrace, hinter, hball⟩ :=
        exists_isPLBall_eraseTriangleComplex_of_isGlueIso_planar A L hIso hL ht₀ ht₀card heq
      let A' := eraseTriangleComplex A t
      let L' := eraseTriangleComplex L (t.image φ)
      let _ : Finite A'.faces := (eraseTriangleComplex_faces_finite A t).to_subtype
      let _ : Finite L'.faces :=
        (eraseTriangleComplex_faces_finite L (t.image φ)).to_subtype
      have hA'K : A'.faces ⊆ K.faces :=
        (eraseTriangleComplex_faces_subset A t).trans hAK
      have hIso' : IsGlueIso A' L' φ ψ := hIso.eraseTriangleComplex ht
      have hL' : IsPLBall 2 L'.space := hball.of_isPLHomeomorphOn hIso'.isPLHomeomorphOn
      have ht₀' : t₀ ∈ A'.faces :=
        (mem_eraseTriangleComplex_triangle_iff A t
          (fun u hu => card_le_of_isPLBall A hA hu) ht₀card).mpr ⟨ht₀, htt₀.symm⟩
      have hlt : {u ∈ A'.faces | u.card = 3}.ncard < n := by
        rw [← hn]
        exact ncard_triangles_eraseTriangleComplex_lt A t ht htcard
          (fun u hu => card_le_of_isPLBall A hA hu)
      have hprev := ih _ hlt (A := A') (L := L') (hAK := hA'K)
        (hL := hL') (hIso := hIso') (ht₀ := ht₀') rfl
      exact hK.isPLBall_derivedNeighborhood_of_free_triangle_subcomplex hA hAK ht htcard
        hst hscard htrace hinter hprev

open Classical in
theorem
    IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_of_isGlueIso_planar_subcomplex
    {K A : Geometry.SimplicialComplex ℝ E}
    {L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    [Finite K.faces] [Finite A.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hAK : A.faces ⊆ K.faces)
    {φ : E → EuclideanSpace ℝ (Fin 2)} {ψ : EuclideanSpace ℝ (Fin 2) → E}
    (hL : IsPLBall 2 L.space) (hIso : IsGlueIso A L φ ψ) :
    IsPLBall 3 (PiecewiseLinear.derivedNeighborhood K A).space := by
  classical
  have hA := hL.of_isPLHomeomorphOn hIso.symm.isPLHomeomorphOn
  obtain ⟨x, hx⟩ := hA.nonempty
  obtain ⟨s, hs, -⟩ := A.mem_space_iff.mp hx
  obtain ⟨t, ht, -, htc⟩ := exists_face_superset_card_eq_of_isPLBall A hA hs
  exact isPLBall_derivedNeighborhood_of_isGlueIso_planar_subcomplex_aux K A L hK hAK
    hL hIso ht htc

end

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLBall_derivedNeighborhood_disk
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {D : Set E}
    (hD : IsPLBall 2 D) (hDK : D ⊆ K.space) :
    ∃ R A : Geometry.SimplicialComplex ℝ E,
      IsSubdivision R K ∧ R.faces.Finite ∧ A.faces ⊆ R.faces ∧ A.faces.Finite ∧
      A.space = D ∧ IsPLBall 3 (PiecewiseLinear.derivedNeighborhood R A).space ∧
      D ⊆ (PiecewiseLinear.derivedNeighborhood R A).space ∧
      (PiecewiseLinear.derivedNeighborhood R A).space ⊆ K.space ∧
      ∀ x ∈ D, (PiecewiseLinear.derivedNeighborhood R A).space ∈ 𝓝[K.space] x := by
  classical
  obtain ⟨R, A, L, φ, ψ, hR, hRfin, hAR, hAfin, hAD, hLfin, hL, hIso, -⟩ :=
    exists_isSubdivision_subcomplex_isGlueIso_planar K hD hDK
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hball :=
    (hK.of_isSubdivision hR).isPLBall_derivedNeighborhood_of_isGlueIso_planar_subcomplex
      hAR hL hIso
  have hcontains : A.space ⊆ (PiecewiseLinear.derivedNeighborhood R A).space := by
    rw [← iUnion_derivedNeighborhoodCell_space R A hAR]
    exact space_subset_iUnion_derivedNeighborhoodCell_space R A hAR
  refine ⟨R, A, hR, hRfin, hAR, hAfin, hAD, hball, hAD ▸ hcontains,
    (derivedNeighborhood_space_subset R A).trans hR.space_eq.subset, ?_⟩
  intro x hxD
  have hxA : x ∈ A.space := hAD.symm ▸ hxD
  have hx := derivedNeighborhood_mem_nhdsWithin hAR hxA
  rwa [hR.space_eq] at hx
end DifferentialGeometry.Topology.PiecewiseLinear

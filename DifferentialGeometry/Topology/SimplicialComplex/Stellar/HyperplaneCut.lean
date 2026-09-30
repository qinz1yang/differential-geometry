import DifferentialGeometry.Topology.SimplicialComplex.Stellar.StellarEdge
import Mathlib.Data.Set.Card

namespace DifferentialGeometry.Topology.Engulfing

set_option linter.unusedSectionVars false

open Set _root_.Geometry

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

def respectsAffineHyperplane (K : SimplicialComplex ℝ E) (f : E →ᵃ[ℝ] ℝ) : Prop :=
  ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ {x | f x ≤ 0} ∨
    convexHull ℝ (s : Set E) ⊆ {x | 0 ≤ f x}

omit [DecidableEq E] in
theorem respectsAffineHyperplane.refines {K L : SimplicialComplex ℝ E} {f : E →ᵃ[ℝ] ℝ}
    (hK : respectsAffineHyperplane K f) (hLK : simplicialRefines L K) :
    respectsAffineHyperplane L f := by
  classical
  intro s hs
  obtain ⟨t, ht, hst⟩ := hLK s hs
  exact (hK t ht).imp (fun h => hst.trans h) (fun h => hst.trans h)

def crossingEdges (K : SimplicialComplex ℝ E) (f : E →ᵃ[ℝ] ℝ) : Set (Finset E) :=
  {s | s ∈ K.faces ∧ ∃ a b, s = {a, b} ∧ f a < 0 ∧ 0 < f b}

theorem crossingEdges_finite (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (f : E →ᵃ[ℝ] ℝ) : (crossingEdges K f).Finite := hK.subset (fun _ h => h.1)

theorem respectsAffineHyperplane_of_crossingEdges_empty (K : SimplicialComplex ℝ E)
    (f : E →ᵃ[ℝ] ℝ) (h : crossingEdges K f = ∅) : respectsAffineHyperplane K f := by
  intro s hs
  by_cases hle : ∀ a ∈ s, f a ≤ 0
  · exact Or.inl (convexHull_min hle ((convex_Iic (0 : ℝ)).affine_preimage f))
  · push Not at hle
    obtain ⟨b, hb, hbpos⟩ := hle
    apply Or.inr
    apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage f)
    intro a ha
    by_contra han
    have ha_neg : f a < 0 := lt_of_not_ge han
    have hedge : {a, b} ∈ K.faces := K.down_closed hs
      (Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩)
      (Finset.insert_nonempty _ _)
    have hm : {a, b} ∈ crossingEdges K f := ⟨hedge, a, b, rfl, ha_neg, hbpos⟩
    simp [h] at hm

theorem exists_edgeSubdivisionPoint_on_hyperplane {K : SimplicialComplex ℝ E}
    (f : E →ᵃ[ℝ] ℝ) {s : Finset E} (hs : s ∈ crossingEdges K f) :
    ∃ d : EdgeSubdivisionPoint K, {d.a, d.b} = s ∧ f d.p = 0 := by
  obtain ⟨hsK, a, b, rfl, ha, hb⟩ := hs
  have hab : a ≠ b := by intro he; simpa [he] using ha.trans hb
  have hden : 0 < f b - f a := by linarith
  let t := -f a / (f b - f a)
  have htpos : 0 < t := div_pos (neg_pos.mpr ha) hden
  have htlt : t < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  let d : EdgeSubdivisionPoint K :=
    { a := a, b := b, p := AffineMap.lineMap a b t, alpha := 1 - t, beta := t,
      endpoints_ne := hab, edge_mem := hsK, alpha_pos := sub_pos.mpr htlt,
      beta_pos := htpos, total := by ring,
      point_eq := AffineMap.lineMap_apply_module a b t }
  refine ⟨d, rfl, ?_⟩
  change f (AffineMap.lineMap a b t) = 0
  rw [f.apply_lineMap, AffineMap.lineMap_apply_ring']
  dsimp [t]
  field_simp
  ring

theorem EdgeSubdivisionPoint.crossingEdges_subset {K : SimplicialComplex ℝ E}
    (d : EdgeSubdivisionPoint K) (f : E →ᵃ[ℝ] ℝ) (hp : f d.p = 0) :
    crossingEdges d.subdivision f ⊆ crossingEdges K f := by
  rintro s ⟨hs, a, b, rfl, ha, hb⟩
  have hnot : d.p ∉ ({a, b} : Finset E) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun he => by simp [← he, hp] at ha,
      fun he => by simp [← he, hp] at hb⟩
  exact ⟨hs.mem_original_of_point_not_mem d hnot, a, b, rfl, ha, hb⟩

theorem EdgeSubdivisionPoint.crossingEdges_ssubset {K : SimplicialComplex ℝ E}
    (d : EdgeSubdivisionPoint K) (f : E →ᵃ[ℝ] ℝ) (hp : f d.p = 0)
    (he : {d.a, d.b} ∈ crossingEdges K f) :
    crossingEdges d.subdivision f ⊂ crossingEdges K f := by
  refine (d.crossingEdges_subset f hp).ssubset_of_mem_notMem he ?_
  intro hs
  rcases hs.1.2.1 with ha | hb
  · exact ha (Finset.mem_insert_self _ _)
  · exact hb (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

omit [DecidableEq E] in
theorem exists_subdivision_respects_affineHyperplane (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (f : E →ᵃ[ℝ] ℝ) {n : ℕ}
    (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ respectsAffineHyperplane L f ∧
      ∀ s ∈ L.faces, s.card ≤ n + 1 := by
  classical
  generalize hcount : (crossingEdges K f).ncard = N
  induction N using Nat.strong_induction_on generalizing K with
  | h N ih =>
    by_cases hempty : crossingEdges K f = ∅
    · exact ⟨K, hK, rfl, simplicialRefines.refl K,
        respectsAffineHyperplane_of_crossingEdges_empty K f hempty, hd⟩
    · obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨d, hedge, hp⟩ := exists_edgeSubdivisionPoint_on_hyperplane f hs
      have he : {d.a, d.b} ∈ crossingEdges K f := hedge ▸ hs
      have hlt : (crossingEdges d.subdivision f).ncard < N := by
        rw [← hcount]
        exact Set.ncard_lt_ncard (d.crossingEdges_ssubset f hp he) (crossingEdges_finite K hK f)
      obtain ⟨L, hL, hspace, href, hcut, hdim⟩ :=
        ih _ hlt d.subdivision (d.subdivision_finite_faces hK)
          (d.subdivision_face_card_le hd) rfl
      exact ⟨L, hL, hspace.trans d.subdivision_space,
        href.trans d.subdivision_refines, hcut, hdim⟩

omit [DecidableEq E] in
theorem exists_subdivision_respects_affineHyperplanes {ι : Type*}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (I : Finset ι)
    (f : ι → E →ᵃ[ℝ] ℝ) {n : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ (∀ i ∈ I, respectsAffineHyperplane L (f i)) ∧
      ∀ s ∈ L.faces, s.card ≤ n + 1 := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨K, hK, rfl, simplicialRefines.refl K, by simp, hd⟩
  | @insert i I hi ih =>
    obtain ⟨J, hJ, hJK, hJref, hJI, hJdim⟩ := ih
    obtain ⟨L, hL, hLJ, hLref, hLi, hLdim⟩ :=
      exists_subdivision_respects_affineHyperplane J hJ (f i) hJdim
    refine ⟨L, hL, hLJ.trans hJK, hLref.trans hJref, ?_, hLdim⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hLi
    · exact (hJI j hj).refines hLref

end DifferentialGeometry.Topology.Engulfing

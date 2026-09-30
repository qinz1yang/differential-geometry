import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryTraceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarFreeFace

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise (Plane)

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [dE : DecidableEq E] [dP : DecidableEq Plane]

open Classical in
theorem exists_isPLBall_eraseTriangleComplex_of_isGlueIso_planar
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ Plane)
    [Finite K.faces] [Finite L.faces] {φ : E → Plane} {ψ : Plane → E}
    (h : IsGlueIso K L φ ψ) (hL : IsPLBall 2 L.space)
    {t₀ : Finset E} (ht₀ : t₀ ∈ K.faces) (ht₀card : t₀.card = 3)
    (hne : K.space ≠ convexHull ℝ (t₀ : Set E)) :
    ∃ t s : Finset E, t ∈ K.faces ∧ t.card = 3 ∧ t ≠ t₀ ∧
      s ∈ K.faces ∧ s ⊆ t ∧ (s.card = 1 ∨ s.card = 2) ∧
      (boundaryComplex 2 K).space ∩ convexHull ℝ (t : Set E) =
        ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E) ∧
      (∀ u ∈ K.faces, u.card = 3 → ¬s ⊆ u →
        (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s)) ∧
      IsPLBall 2 (eraseTriangleComplex K t).space := by
  have hdE : dE = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have hdP : dP = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst dE
  subst dP
  let _ : DecidableEq Plane := Classical.decEq _
  have hf := h.isPLHomeomorphOn
  have hneL : L.space ≠ convexHull ℝ ((t₀.image φ : Finset Plane) : Set Plane) := by
    intro heq
    apply hne
    apply Subset.antisymm ?_ (K.convexHull_subset_space ht₀)
    intro x hx
    have hy : simplicialMap K φ x ∈ simplicialMap K φ '' convexHull ℝ (t₀ : Set E) := by
      rw [h.image_convexHull ht₀, ← heq]
      exact hf.bijOn.mapsTo hx
    obtain ⟨y, hy, heqxy⟩ := hy
    exact (hf.bijOn.injOn (K.convexHull_subset_space ht₀ hy) hx heqxy) ▸ hy
  obtain ⟨t', s', ht', ht'card, ht't₀, hs', hs't', hs'card, htrace, hinter, hball, -⟩ :=
    exists_isPLBall_eraseTriangleComplex_with_intersections L hL (h.image₁ _ ht₀)
      ((h.card_image_left ht₀).trans ht₀card) hneL
  let t := t'.image ψ
  let s := s'.image ψ
  have ht : t ∈ K.faces := h.image₂ t' ht'
  have hs : s ∈ K.faces := h.image₂ s' hs'
  have htback : t.image φ = t' := h.image_image_right ht'
  have hsback : s.image φ = s' := h.image_image_right hs'
  have htcard : t.card = 3 := (h.card_image_right ht').trans ht'card
  have hscard : s.card = s'.card := h.card_image_right hs'
  have htt₀ : t ≠ t₀ := by
    intro heq
    apply ht't₀
    exact htback.symm.trans (congrArg (Finset.image φ) heq)
  have htrace' : (boundaryComplex 2 L).space ∩ convexHull ℝ (t' : Set Plane) =
      ⋃ v ∈ s', convexHull ℝ ((t'.erase v : Finset Plane) : Set Plane) := by
    rw [← frontier_space_eq_boundaryComplex_space hL.isCombinatorialManifoldWithBoundary]
    simpa only [Finset.coe_erase] using htrace
  have htraceK := h.symm.boundaryComplex_inter_convexHull_image
    hL.isCombinatorialManifoldWithBoundary ht' hs't' (by omega) htrace'
  have hinterK : ∀ u ∈ K.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s) := by
    intro u hu hucard hsu
    have hnot : ¬s' ⊆ u.image φ := by
      intro hsub
      apply hsu
      have hback := Finset.image_mono ψ hsub
      rwa [h.image_image_left hu] at hback
    have hi := hinter (u.image φ) (h.image₁ u hu)
      ((h.card_image_left hu).trans hucard) hnot
    have hi' : (u.image φ ∩ t.image φ).card ≤ 1 ∧
        (s'.card = 2 → u.image φ ∩ t.image φ ⊆ s.image φ) := by
      constructor
      · rw [htback]
        convert hi.1 using 2
        ext v
        simp only [Finset.mem_inter]
      · intro hsc
        simpa only [htback, hsback, Finset.subset_iff, Finset.mem_inter] using hi.2 hsc
    refine ⟨?_, fun hsc => ?_⟩
    · have hiCard := hi'.1
      rwa [h.card_inter_image_left hu ht] at hiCard
    · have hiSub := hi'.2 (hscard ▸ hsc)
      rw [← h.image_inter_left hu ht] at hiSub
      have hback := Finset.image_mono ψ hiSub
      have hcancel : ((u ∩ t).image φ).image ψ = u ∩ t := by
        rw [Finset.image_image]
        calc
          (u ∩ t).image (ψ ∘ φ) = (u ∩ t).image id :=
            Finset.image_congr fun v hv => h.left u hu v (Finset.mem_inter.mp hv).1
          _ = u ∩ t := Finset.image_id
      rwa [hcancel, h.image_image_left hs] at hback
  let _ : Finite (eraseTriangleComplex L t').faces :=
    (eraseTriangleComplex_faces_finite L t').to_subtype
  let _ : Finite (eraseTriangleComplex K t).faces :=
    (eraseTriangleComplex_faces_finite K t).to_subtype
  have herase := (h.symm.eraseTriangleComplex ht').isPLHomeomorphOn
  refine ⟨t, s, ht, htcard, htt₀, hs, Finset.image_mono ψ hs't', ?_, htraceK, hinterK,
    hball.of_isPLHomeomorphOn herase⟩
  rcases hs'card with hc | hc
  · exact Or.inl (hscard.trans hc)
  · exact Or.inr (hscard.trans hc)

end DifferentialGeometry.Topology.PiecewiseLinear

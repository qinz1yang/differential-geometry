import DifferentialGeometry.Topology.PiecewiseLinear.AffineImageTransport
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryTraceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.FaceStarBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarRelativeSubcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [dE : DecidableEq E]

open Classical in
theorem exists_isPLHomeomorphOn_eraseTriangleComplex_in_planar_chart
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hpure : ∀ u ∈ K.faces, ∃ v ∈ K.faces, u ⊆ v ∧ v.card = 3)
    {t s : Finset E} (ht : t ∈ K.faces) (htcard : t.card = 3)
    (hs : s ∈ K.faces) (hst : s ⊆ t) (hscard : s.card = 1 ∨ s.card = 2)
    (hP : IsPLBall 2 (faceStarComplex K s).space)
    (htrace : (boundaryComplex 2 (faceStarComplex K s)).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hne : (faceStarComplex K s).space ≠ convexHull ℝ (t : Set E))
    (hinter : ∀ u ∈ K.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s))
    {f : E → EuclideanSpace ℝ (Fin 2)}
    (hAff : ∀ u ∈ K.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2),
      EqOn f A (convexHull ℝ (u : Set E))) (hinj : InjOn f K.space)
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (htU : f '' convexHull ℝ (t : Set E) ⊆ U) :
    ∃ g : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn g univ univ ∧ EqOn g id Uᶜ ∧
      g '' (f '' K.space) = f '' (eraseTriangleComplex K t).space := by
  have hdE : dE = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst dE
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 2)) := Classical.decEq _
  obtain ⟨M, ψ, hMfin, hMspace, hIso, -, hsm⟩ := exists_isGlueIso_of_affineOn_faces K hAff hinj
  let _ : Finite M.faces := hMfin.to_subtype
  let P := faceStarComplex K s
  let N := faceStarComplex M (s.image f)
  let _ : Finite P.faces := (faceStarComplex_faces_finite K s).to_subtype
  let _ : Finite N.faces := (faceStarComplex_faces_finite M (s.image f)).to_subtype
  have hPN : IsGlueIso P N f ψ := hIso.faceStarComplex hs
  have hN : IsPLBall 2 N.space := hP.of_isPLHomeomorphOn hPN.isPLHomeomorphOn
  have htP : t ∈ P.faces := mem_faceStarComplex_faces_of_subset K ht hst
  have htN := hPN.image₁ _ htP
  have htM := hIso.image₁ _ ht
  have htMcard : (t.image f).card = 3 := (hIso.card_image_left ht).trans htcard
  have hstM := Finset.image_mono f hst
  have hsMcard : (s.image f).card = 1 ∨ (s.image f).card = 2 := by
    rwa [hIso.card_image_left hs]
  have hpureM : ∀ u ∈ M.faces, ∃ v ∈ M.faces, u ⊆ v ∧ v.card = 3 := by
    intro u hu
    obtain ⟨v, hv, huv, hvcard⟩ := hpure (u.image ψ) (hIso.image₂ u hu)
    refine ⟨v.image f, hIso.image₁ _ hv, ?_, (hIso.card_image_left hv).trans hvcard⟩
    have himage := Finset.image_mono f huv
    rwa [hIso.image_image_right hu] at himage
  have htraceN : frontier N.space ∩ convexHull ℝ ((t.image f : Finset _) : Set _) =
      ⋃ v ∈ s.image f, convexHull ℝ (((t.image f).erase v : Finset _) : Set _) := by
    rw [frontier_space_eq_boundaryComplex_space hN.isCombinatorialManifoldWithBoundary]
    exact hPN.boundaryComplex_inter_convexHull_image
      hP.isCombinatorialManifoldWithBoundary htP hst (by omega) htrace
  have hneN : N.space ≠ convexHull ℝ ((t.image f : Finset _) : Set _) := by
    intro heq
    apply hne
    rw [← hPN.symm.image_left, heq]
    simpa only [hIso.image_image_left ht] using hPN.symm.image_convexHull htN
  have hinterM : ∀ u ∈ M.faces, u.card = 3 → u ∉ N.faces →
      (u ∩ t.image f).card ≤ 1 ∧ ((s.image f).card = 2 → u ∩ t.image f ⊆ s.image f) := by
    intro u hu hucard hun
    have huK := hIso.image₂ _ hu
    have hnot : ¬s ⊆ u.image ψ := by
      intro hsub
      apply hun
      apply mem_faceStarComplex_faces_of_subset M hu
      have himage := Finset.image_mono f hsub
      rwa [hIso.image_image_right hu] at himage
    have hi := hinter (u.image ψ) huK ((hIso.card_image_right hu).trans hucard) hnot
    have hcard := hIso.card_inter_image_left huK ht
    rw [hIso.image_image_right hu] at hcard
    refine ⟨?_, fun hsc => ?_⟩
    · rw [hcard]
      exact hi.1
    · have himage := Finset.image_mono f (hi.2 ((hIso.card_image_left hs).symm.trans hsc))
      rw [hIso.image_inter_left huK ht, hIso.image_image_right hu] at himage
      exact himage
  have htImage : f '' convexHull ℝ (t : Set E) =
      convexHull ℝ ((t.image f : Finset _) : Set _) :=
    ((hsm.mono (K.convexHull_subset_space ht)).image_eq).symm.trans (hIso.image_convexHull ht)
  have htU' : convexHull ℝ ((t.image f : Finset _) : Set _) ⊆ U := htImage ▸ htU
  have herase : f '' (eraseTriangleComplex K t).space =
      (eraseTriangleComplex M (t.image f)).space := by
    have hsm' := simplicialMap_eq_of_forall_affineOn (eraseTriangleComplex K t) f
      (fun u hu => hAff u (eraseTriangleComplex_faces_subset K t hu))
    exact hsm'.image_eq.symm.trans (hIso.eraseTriangleComplex ht).image_left
  obtain ⟨g, hg, hfix, -, hMimage, -, -⟩ :=
    exists_isPLHomeomorphOn_eraseTriangleComplex_subcomplex M N
      (faceStarComplex_faces_subset M (s.image f)) hpureM hN htN htMcard hstM hsMcard
      (by simpa only [Finset.coe_erase] using htraceN) hneN
      (fun u hu _ hsub => mem_faceStarComplex_faces_of_subset M hu hsub)
      (by
        intro u hu hucard hun
        have hi := hinterM u hu hucard hun
        constructor
        · convert hi.1 using 2
          ext v
          simp only [Finset.mem_inter]
        · intro hsc
          simpa only [Finset.subset_iff, Finset.mem_inter] using hi.2 hsc) hU htU'
  refine ⟨g, hg, hfix, ?_⟩
  rwa [hMspace, ← herase] at hMimage

end DifferentialGeometry.Topology.PiecewiseLinear

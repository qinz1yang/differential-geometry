import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleDeletion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [dE : DecidableEq E] [dF : DecidableEq F]
  {K : Geometry.SimplicialComplex ℝ E} {L : Geometry.SimplicialComplex ℝ F}
  {φ : E → F} {ψ : F → E}

theorem IsGlueIso.image_subset_image_left_iff (h : IsGlueIso K L φ ψ)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    s.image φ ⊆ t.image φ ↔ s ⊆ t := by
  constructor
  · intro hsub
    have hback := Finset.image_mono ψ hsub
    rwa [h.image_image_left hs, h.image_image_left ht] at hback
  · intro hsub
    exact Finset.image_mono φ hsub

theorem IsGlueIso.image_inter_left (h : IsGlueIso K L φ ψ)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    (s ∩ t).image φ = s.image φ ∩ t.image φ := by
  have hinv : LeftInvOn ψ φ ((s : Set E) ∪ t) := by
    intro x hx
    rcases hx with hx | hx
    · exact h.left s hs x hx
    · exact h.left t ht x hx
  exact Finset.image_inter_of_injOn s t hinv.injOn

theorem IsGlueIso.card_inter_image_left (h : IsGlueIso K L φ ψ)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    (s.image φ ∩ t.image φ).card = (s ∩ t).card := by
  rw [← h.image_inter_left hs ht]
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  have hxs : x ∈ s := (Finset.mem_inter.mp hx).1
  have hys : y ∈ s := (Finset.mem_inter.mp hy).1
  rw [← h.left s hs x hxs, ← h.left s hs y hys, hxy]

theorem IsGlueIso.image_erase_left (h : IsGlueIso K L φ ψ)
    {s : Finset E} (hs : s ∈ K.faces) {v : E} (hv : v ∈ s) :
    (s.erase v).image φ = (s.image φ).erase (φ v) := by
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hwv, hws⟩ := Finset.mem_erase.mp hw
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image.mpr ⟨w, hws, rfl⟩⟩
    intro hφ
    apply hwv
    rw [← h.left s hs w hws, ← h.left s hs v hv, hφ]
  · exact Finset.erase_image_subset_image_erase φ s v

theorem IsGlueIso.image_convexHull (h : IsGlueIso K L φ ψ)
    {s : Finset E} (hs : s ∈ K.faces) :
    simplicialMap K φ '' convexHull ℝ (s : Set E) =
      convexHull ℝ ((s.image φ : Finset F) : Set F) := by
  apply image_convexHull_simplicialMap K φ hs
  intro x hx y hy hxy
  rw [← h.left s hs x hx, ← h.left s hs y hy, hxy]

open Classical in
theorem IsGlueIso.faceStarComplex (h : IsGlueIso K L φ ψ)
    {s : Finset E} (hs : s ∈ K.faces) :
    IsGlueIso (faceStarComplex K s) (faceStarComplex L (s.image φ)) φ ψ := by
  have hdE : dE = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have hdF : dF = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst dE
  subst dF
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro t ⟨ht, hts⟩
    refine ⟨h.image₁ t ht, ?_⟩
    simpa only [Finset.image_union] using h.image₁ (t ∪ s) hts
  · rintro t ⟨ht, hts⟩
    refine ⟨h.image₂ t ht, ?_⟩
    have hback := h.image₂ (t ∪ s.image φ) hts
    simpa only [Finset.image_union, h.image_image_left hs] using hback
  · intro t ht v hv
    exact h.left t ht.1 v hv
  · intro t ht v hv
    exact h.right t ht.1 v hv

end DifferentialGeometry.Topology.PiecewiseLinear

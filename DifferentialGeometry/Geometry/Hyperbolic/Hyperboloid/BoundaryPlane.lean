import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryEquiv
import DifferentialGeometry.Geometry.Coordinates.StereographicComplex

noncomputable section

namespace DifferentialGeometry.Hyperboloid

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable (f g : C(Hyperboloid E3, Hyperboloid E3))
  (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E3,
    L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
  (hg : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E3,
    L⁻¹ * dist x y - C ≤ dist (g x) (g y) ∧ dist (g x) (g y) ≤ L * dist x y + C)
  (hgf : ∃ C : ℝ, ∀ x : Hyperboloid E3, dist (g (f x)) x ≤ C)
  (hfg : ∃ C : ℝ, ∀ x : Hyperboloid E3, dist (f (g x)) x ≤ C)
  (hnorth : boundaryMap f hf sphereNorthPole = sphereNorthPole)

include hnorth in
private theorem boundaryHomeomorph_nonpole_iff (ξ : Metric.sphere (0 : E3) 1) :
    ξ ≠ sphereNorthPole ↔ boundaryHomeomorphOfCoarseInverse f g hf hg hgf hfg ξ ≠ sphereNorthPole := by
  have hp : boundaryHomeomorphOfCoarseInverse f g hf hg hgf hfg sphereNorthPole = sphereNorthPole := hnorth
  constructor
  · intro hξ heq
    exact hξ ((boundaryHomeomorphOfCoarseInverse f g hf hg hgf hfg).injective (heq.trans hp.symm))
  · intro hξ heq
    exact hξ (heq ▸ hp)

def boundaryPlaneHomeomorph : ℂ ≃ₜ ℂ :=
  stereographicComplex.symm.trans
    (((boundaryHomeomorphOfCoarseInverse f g hf hg hgf hfg).subtype
      (boundaryHomeomorph_nonpole_iff f g hf hg hgf hfg hnorth)).trans stereographicComplex)

theorem stereographicComplex_symm_boundaryPlaneHomeomorph (z : ℂ) :
    (stereographicComplex.symm (boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth z)).val =
      boundaryMap f hf (stereographicComplex.symm z).val := by
  exact congrArg Subtype.val (stereographicComplex.symm_apply_apply
    ((boundaryHomeomorphOfCoarseInverse f g hf hg hgf hfg).subtype
      (boundaryHomeomorph_nonpole_iff f g hf hg hgf hfg hnorth) (stereographicComplex.symm z)))

theorem stereographicComplex_symm_boundaryPlaneHomeomorph_symm (z : ℂ) :
    (stereographicComplex.symm ((boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth).symm z)).val =
      boundaryMap g hg (stereographicComplex.symm z).val := by
  exact congrArg Subtype.val (stereographicComplex.symm_apply_apply
    (((boundaryHomeomorphOfCoarseInverse f g hf hg hgf hfg).subtype
      (boundaryHomeomorph_nonpole_iff f g hf hg hgf hfg hnorth)).symm (stereographicComplex.symm z)))

include hgf hfg hnorth in
theorem boundaryMap_coarseInverse_northPole : boundaryMap g hg sphereNorthPole = sphereNorthPole := by
  have h := (boundaryHomeomorphOfCoarseInverse f g hf hg hgf hfg).symm_apply_apply sphereNorthPole
  change boundaryMap g hg (boundaryMap f hf sphereNorthPole) = sphereNorthPole at h
  rwa [hnorth] at h

theorem boundaryPlaneHomeomorph_symm :
    (boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth).symm =
      boundaryPlaneHomeomorph g f hg hf hfg hgf
        (boundaryMap_coarseInverse_northPole f g hf hg hgf hfg hnorth) := by
  apply Homeomorph.ext
  intro z
  apply stereographicComplex.symm.injective
  apply Subtype.ext
  rw [stereographicComplex_symm_boundaryPlaneHomeomorph_symm,
    stereographicComplex_symm_boundaryPlaneHomeomorph]

end DifferentialGeometry.Hyperboloid

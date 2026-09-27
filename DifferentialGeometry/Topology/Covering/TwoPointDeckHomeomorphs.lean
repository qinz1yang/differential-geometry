import DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotientSmoothModels
import Mathlib.Topology.Covering.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [PreconnectedSpace X] [Nonempty X]

theorem covering_deck_iff_self_or_fibre_swap
    (pi : X → Y) (hcover : IsCoveringMap pi) (tau : X ≃ₜ X)
    (hfibres : ∀ p q : X, pi p = pi q ↔ q = p ∨ q = tau p)
    (d : X ≃ₜ X) :
    pi ∘ d = pi ↔ d = Homeomorph.refl X ∨ d = tau := by
  classical
  have htau : pi ∘ tau = pi := by
    funext x
    exact ((hfibres x (tau x)).mpr (Or.inr rfl)).symm
  constructor
  · intro hd
    let p : X := Classical.choice inferInstance
    rcases (hfibres p (d p)).mp (congrFun hd p).symm with hp | hp
    · left
      have heq : (d : X → X) = id :=
        hcover.eq_of_comp_eq d.continuous continuous_id
          (by simpa only [Function.comp_id] using hd) p hp
      exact Homeomorph.ext (congrFun heq)
    · right
      have heq : (d : X → X) = tau :=
        hcover.eq_of_comp_eq d.continuous tau.continuous (hd.trans htau.symm) p hp
      exact Homeomorph.ext (congrFun heq)
  · rintro (rfl | rfl)
    · rfl
    · exact htau

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

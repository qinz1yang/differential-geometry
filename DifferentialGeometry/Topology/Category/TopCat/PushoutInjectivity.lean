import DifferentialGeometry.Topology.Category.TopCat.PushoutClosedEmbedding

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace Poincare.TopCat.Pushout
universe u
variable {A D X P Z : TopCat.{u}} {f : A ⟶ D} {g : A ⟶ X}
  {r : D ⟶ P} {b : X ⟶ P} (h : IsPushout f g r b) (F : P ⟶ Z)

include h

theorem injective_of_cell_overlap (hD : Function.Injective (F ∘ r))
    (hX : Function.Injective (F ∘ b))
    (hoverlap : ∀ d x, F (r d) = F (b x) → d ∈ Set.range f) : Function.Injective F := by
  have hcross (d : D) (x : X) (he : F (r d) = F (b x)) : r d = b x := by
    obtain ⟨a, ha⟩ := hoverlap d x he
    have hw := ConcreteCategory.congr_hom h.w a
    change r (f a) = b (g a) at hw
    rw [ha] at hw
    have hg : g a = x := hX (by change F (b (g a)) = F (b x); rw [← hw]; exact he)
    exact hw.trans (congrArg b hg)
  intro p q hpq
  rcases jointly_surjective h p with ⟨d, rfl⟩ | ⟨x, rfl⟩
  · rcases jointly_surjective h q with ⟨e, rfl⟩ | ⟨y, rfl⟩
    · exact congrArg r (hD hpq)
    · exact hcross d y hpq
  · rcases jointly_surjective h q with ⟨e, rfl⟩ | ⟨y, rfl⟩
    · exact (hcross e x hpq.symm).symm
    · exact congrArg b (hX hpq)

end Poincare.TopCat.Pushout

import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Products

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace Poincare.CategoryTheory
universe v u w
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C]
  {ι : Type w} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
  (a : Cofan A) (b : Cofan B) (F : a.pt ⟶ b.pt)
  (hF : ∀ i, a.inj i ≫ F = f i ≫ b.inj i)


def cokernelCofan : Cofan (fun i => cokernel (f i)) :=
  Cofan.mk (cokernel F) (fun i => cokernel.map (f i) F (a.inj i) (b.inj i) (hF i).symm)


def cokernelCofanIsColimit (ha : IsColimit a) (hb : IsColimit b) :
    IsColimit (cokernelCofan f a b F hF) := by
  have H : ∀ s : Cofan (fun i => cokernel (f i)), ∃ l : cokernel F ⟶ s.pt,
      (∀ i, (cokernelCofan f a b F hF).inj i ≫ l = s.inj i) ∧
      ∀ m, (∀ i, (cokernelCofan f a b F hF).inj i ≫ m = s.inj i) → m = l := by
    intro s
    let L : b.pt ⟶ s.pt := hb.desc (Cofan.mk s.pt (fun i => cokernel.π (f i) ≫ s.inj i))
    have hL (i : ι) : b.inj i ≫ L = cokernel.π (f i) ≫ s.inj i := hb.fac _ ⟨i⟩
    have hz : F ≫ L = 0 := by
      apply ha.hom_ext
      rintro ⟨i⟩
      change a.inj i ≫ (F ≫ L) = a.inj i ≫ 0
      rw [← Category.assoc, hF, Category.assoc, hL, ← Category.assoc, cokernel.condition]
      simp
    refine ⟨cokernel.desc F L hz, ?_, ?_⟩
    · intro i
      apply (cancel_epi (cokernel.π (f i))).mp
      change cokernel.π (f i) ≫ cokernel.map (f i) F (a.inj i) (b.inj i) (hF i).symm ≫ _ = _
      rw [cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc, hL]
    · intro m hm
      change cokernel F ⟶ s.pt at m
      apply (cancel_epi (cokernel.π F)).mp
      rw [cokernel.π_desc]
      apply hb.hom_ext
      rintro ⟨i⟩
      change b.inj i ≫ cokernel.π F ≫ m = b.inj i ≫ L
      rw [hL]
      have hh := congrArg (fun k => cokernel.π (f i) ≫ k) (hm i)
      change cokernel.π (f i) ≫ cokernel.map (f i) F (a.inj i) (b.inj i) (hF i).symm ≫ m = _ at hh
      rw [cokernel.π_desc_assoc] at hh
      simpa only [Category.assoc] using hh
  choose l hl hu using H
  exact Cofan.IsColimit.mk _ l hl hu
end Poincare.CategoryTheory

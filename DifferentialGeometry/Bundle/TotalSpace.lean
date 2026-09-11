import Mathlib.Data.Bundle
import Mathlib.Algebra.Group.Action.Defs

namespace Bundle.TotalSpace

variable {G F B : Type*} {P : B → Type*} [Monoid G] [∀ x, MulAction G (P x)]

instance instMulAction : MulAction G (TotalSpace F P) where
  smul g p := ⟨p.proj, g • p.snd⟩
  one_smul p := by
    change (⟨p.proj, (1 : G) • p.snd⟩ : TotalSpace F P) = p
    rw [one_smul]
  mul_smul g h p := by
    change (⟨p.proj, (g * h) • p.snd⟩ : TotalSpace F P) = ⟨p.proj, g • h • p.snd⟩
    rw [mul_smul]

end Bundle.TotalSpace

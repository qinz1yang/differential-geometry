import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Quotient

namespace ContinuousMap

variable {G K X Y : Type*} [Group G] [Group K]
  [TopologicalSpace X] [TopologicalSpace Y] [MulAction G X] [MulAction K Y]

def orbitQuotientMap (f : C(X, Y)) (φ : G → K)
    (hf : ∀ γ x, f (γ • x) = φ γ • f x) :
    C(MulAction.orbitRel.Quotient G X, MulAction.orbitRel.Quotient K Y) where
  toFun := Quotient.map' f (by
    rintro a b ⟨γ, rfl⟩
    exact ⟨φ γ, (hf γ b).symm⟩)
  continuous_toFun := f.continuous.quotient_map' _

@[simp]
theorem orbitQuotientMap_mk (f : C(X, Y)) (φ : G → K)
    (hf : ∀ γ x, f (γ • x) = φ γ • f x) (x : X) :
    f.orbitQuotientMap φ hf (Quotient.mk (MulAction.orbitRel G X) x) =
      Quotient.mk (MulAction.orbitRel K Y) (f x) := rfl

end ContinuousMap

namespace Homeomorph

variable {G K X Y : Type*} [Group G] [Group K]
  [TopologicalSpace X] [TopologicalSpace Y] [MulAction G X] [MulAction K Y]

def orbitQuotient (e : X ≃ₜ Y) (φ : G → K) (hφ : Function.Surjective φ)
    (he : ∀ γ x, e (γ • x) = φ γ • e x) :
    MulAction.orbitRel.Quotient G X ≃ₜ MulAction.orbitRel.Quotient K Y :=
  Homeomorph.Quotient.congr e fun a b => by
    constructor
    · rintro ⟨γ, hγ⟩
      exact ⟨φ γ, (he γ b).symm.trans (congrArg e hγ)⟩
    · rintro ⟨k, hk⟩
      obtain ⟨γ, rfl⟩ := hφ k
      exact ⟨γ, e.injective ((he γ b).trans hk)⟩

@[simp]
theorem orbitQuotient_apply_mk (e : X ≃ₜ Y) (φ : G → K) (hφ : Function.Surjective φ)
    (he : ∀ γ x, e (γ • x) = φ γ • e x) (x : X) :
    e.orbitQuotient φ hφ he (Quotient.mk (MulAction.orbitRel G X) x) =
      Quotient.mk (MulAction.orbitRel K Y) (e x) := rfl

@[simp]
theorem orbitQuotient_symm_apply_mk (e : X ≃ₜ Y) (φ : G → K) (hφ : Function.Surjective φ)
    (he : ∀ γ x, e (γ • x) = φ γ • e x) (y : Y) :
    (e.orbitQuotient φ hφ he).symm (Quotient.mk (MulAction.orbitRel K Y) y) =
      Quotient.mk (MulAction.orbitRel G X) (e.symm y) := rfl

end Homeomorph

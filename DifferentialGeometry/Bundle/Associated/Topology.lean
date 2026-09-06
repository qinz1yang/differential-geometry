import DifferentialGeometry.Bundle.Associated.Equivariant
import DifferentialGeometry.Topology.GroupAction.Hom
import Mathlib.Topology.Algebra.Module.Equiv

open Set

namespace MulActionHom

variable {G N P W : Type*} [Group G] [Monoid N] [Torsor G P] [MulAction N W]
  [TopologicalSpace W]

def evalHomeomorph (φ : G →* N) (hφ : ∀ g, Continuous (fun w : W => φ g • w)) (p : P) :
    (P →ₑ[φ] W) ≃ₜ W where
  __ := evalEquiv φ p
  continuous_toFun := continuous_eval p
  continuous_invFun := continuous_iff.mpr (fun q => hφ (q /ₛ p))

@[simp]
theorem evalHomeomorph_apply (φ : G →* N)
    (hφ : ∀ g, Continuous (fun w : W => φ g • w)) (p : P) (f : P →ₑ[φ] W) :
    evalHomeomorph φ hφ p f = f p := rfl

@[simp]
theorem evalHomeomorph_symm_apply (φ : G →* N)
    (hφ : ∀ g, Continuous (fun w : W => φ g • w)) (p q : P) (w : W) :
    (evalHomeomorph φ hφ p).symm w q = φ (q /ₛ p) • w := rfl

end MulActionHom

namespace Representation

section Monoid

variable {k G P W W' : Type*} [Semiring k] [Monoid G] [SMul G P]
  [AddCommMonoid W] [Module k W] [TopologicalSpace W]
  [AddCommMonoid W'] [Module k W'] [TopologicalSpace W']

theorem isClosed_associatedSet (ρ : Representation k G W) {C : Set W} (hC : IsClosed C) :
    IsClosed (ρ.associatedSet P C) := by
  have heq : ρ.associatedSet P C = ⋂ p : P, (fun f : P →ₑ[ρ] W => f p) ⁻¹' C := by
    ext f
    simp only [associatedSet, mem_ofPred_eq, mem_iInter, mem_preimage]
  rw [heq]
  exact isClosed_iInter (fun p => hC.preimage (MulActionHom.continuous_eval p))

@[fun_prop]
theorem continuous_associatedMap (ρ : Representation k G W) (σ : Representation k G W')
    (f : W → W') (hf : ∀ g w, f (ρ g w) = σ g (f w)) (hcont : Continuous f) :
    Continuous (ρ.associatedMap (P := P) σ f hf) :=
  MulActionHom.continuous_iff.mpr (fun p => hcont.comp (MulActionHom.continuous_eval p))

end Monoid

section Group

variable {k G P W : Type*} [Semiring k] [Group G] [Torsor G P]
  [AddCommMonoid W] [Module k W] [TopologicalSpace W]

def evalContinuousLinearEquiv (ρ : Representation k G W) (hρ : ∀ g, Continuous (ρ g))
    (p : P) : (P →ₑ[ρ] W) ≃L[k] W where
  __ := ρ.evalLinearEquiv p
  continuous_toFun := MulActionHom.continuous_eval p
  continuous_invFun := MulActionHom.continuous_iff.mpr (fun q => hρ (q /ₛ p))

@[simp]
theorem evalContinuousLinearEquiv_apply (ρ : Representation k G W)
    (hρ : ∀ g, Continuous (ρ g)) (p : P) (f : P →ₑ[ρ] W) :
    ρ.evalContinuousLinearEquiv hρ p f = f p := rfl

@[simp]
theorem evalContinuousLinearEquiv_symm_apply (ρ : Representation k G W)
    (hρ : ∀ g, Continuous (ρ g)) (p q : P) (w : W) :
    (ρ.evalContinuousLinearEquiv hρ p).symm w q = ρ (q /ₛ p) w := rfl

theorem isClosed_associatedSet_iff (ρ : Representation k G W) (hρ : ∀ g, Continuous (ρ g))
    {C : Set W} (hC : ∀ g : G, MapsTo (ρ g) C C) :
    IsClosed (ρ.associatedSet P C) ↔ IsClosed C := by
  obtain ⟨p⟩ := (inferInstance : Nonempty P)
  rw [ρ.associatedSet_eq_preimage hC p]
  exact (ρ.evalContinuousLinearEquiv hρ p).toHomeomorph.isClosed_preimage

end Group

end Representation

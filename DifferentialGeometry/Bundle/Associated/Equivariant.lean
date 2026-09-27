import Mathlib.Algebra.Torsor.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.RepresentationTheory.Basic
import Mathlib.Analysis.Convex.Basic

open Set

namespace MulActionHom

variable {G N P W : Type*} [Group G] [Monoid N] [Torsor G P] [MulAction N W]

def evalEquiv (φ : G →* N) (p : P) : (P →ₑ[φ] W) ≃ W where
  toFun f := f p
  invFun w :=
    { toFun := fun q => φ (q /ₛ p) • w
      map_smul' := fun g q => by rw [smul_sdiv_assoc, map_mul, mul_smul] }
  left_inv f := by
    ext q
    exact (map_smulₛₗ f (q /ₛ p) p).symm.trans (congrArg f (sdiv_smul q p))
  right_inv w := by
    change φ (p /ₛ p) • w = w
    simp

@[simp]
theorem evalEquiv_apply (φ : G →* N) (p : P) (f : P →ₑ[φ] W) :
    evalEquiv φ p f = f p := rfl

@[simp]
theorem evalEquiv_symm_apply (φ : G →* N) (p q : P) (w : W) :
    (evalEquiv φ p).symm w q = φ (q /ₛ p) • w := rfl

theorem evalEquiv_symm_smul (φ : G →* N) (p : P) (g : G) (w : W) :
    (evalEquiv φ (g • p)).symm (φ g • w) = (evalEquiv φ p).symm w := by
  apply (evalEquiv φ (g • p)).injective
  simp

theorem evalEquiv_symm_eq_iff (φ : G →* N) (p q : P) (w z : W) :
    (evalEquiv φ p).symm w = (evalEquiv φ q).symm z ↔ z = φ (q /ₛ p) • w := by
  rw [← (evalEquiv φ q).injective.eq_iff]
  simp only [Equiv.apply_symm_apply, evalEquiv_apply, evalEquiv_symm_apply, eq_comm]

theorem evalEquiv_symm_eq_iff_exists_smul (φ : G →* N) (p q : P) (w z : W) :
    (evalEquiv φ p).symm w = (evalEquiv φ q).symm z ↔
      ∃ g : G, q = g • p ∧ z = φ g • w := by
  rw [evalEquiv_symm_eq_iff]
  constructor
  · intro h
    exact ⟨q /ₛ p, (sdiv_smul q p).symm, h⟩
  · rintro ⟨g, rfl, h⟩
    simpa only [smul_sdiv] using h

end MulActionHom

namespace Representation

section Monoid

variable {k G P W : Type*} [Semiring k] [Monoid G] [SMul G P]
  [AddCommMonoid W] [Module k W]

def associatedSet (ρ : Representation k G W) (P : Type*) [SMul G P] (C : Set W) :
    Set (P →ₑ[ρ] W) := {f | ∀ p, f p ∈ C}

variable {W' : Type*} [AddCommMonoid W'] [Module k W']

def associatedMap (ρ : Representation k G W) (σ : Representation k G W')
    (f : W → W') (hf : ∀ g w, f (ρ g w) = σ g (f w)) :
    (P →ₑ[ρ] W) → (P →ₑ[σ] W') :=
  fun z =>
    { toFun := fun p => f (z p)
      map_smul' := fun g p => by
        rw [map_smulₛₗ z]
        simpa only [Module.End.smul_def] using hf g (z p) }

@[simp]
theorem associatedMap_apply (ρ : Representation k G W) (σ : Representation k G W')
    (f : W → W') (hf : ∀ g w, f (ρ g w) = σ g (f w)) (z : P →ₑ[ρ] W) (p : P) :
    ρ.associatedMap σ f hf z p = f (z p) := rfl

@[simp]
theorem associatedMap_id (ρ : Representation k G W) :
    ρ.associatedMap (P := P) ρ id (fun _ _ => rfl) = id := by
  funext z
  ext p
  rfl

theorem associatedMap_comp {W'' : Type*} [AddCommMonoid W''] [Module k W'']
    (ρ : Representation k G W) (σ : Representation k G W') (τ : Representation k G W'')
    (f : W → W') (g : W' → W'')
    (hf : ∀ a w, f (ρ a w) = σ a (f w)) (hg : ∀ a w, g (σ a w) = τ a (g w)) :
    σ.associatedMap (P := P) τ g hg ∘ ρ.associatedMap σ f hf =
      ρ.associatedMap τ (g ∘ f) (fun a w => by
        change g (f (ρ a w)) = τ a (g (f w))
        rw [hf, hg]) := by
  funext z
  ext p
  rfl

theorem mapsTo_associatedSet (ρ : Representation k G W) (σ : Representation k G W')
    (f : W → W') (hf : ∀ g w, f (ρ g w) = σ g (f w))
    {C : Set W} {D : Set W'} (hmap : MapsTo f C D) :
    MapsTo (ρ.associatedMap σ f hf) (ρ.associatedSet P C) (σ.associatedSet P D) :=
  fun _ hz p => hmap (hz p)

theorem convex_associatedSet [PartialOrder k] (ρ : Representation k G W) {C : Set W}
    (hC : Convex k C) : Convex k (ρ.associatedSet P C) := by
  intro f hf g hg a b ha hb hab p
  exact hC (hf p) (hg p) ha hb hab

end Monoid

section Group

variable {k G P W : Type*} [Semiring k] [Group G] [Torsor G P]
  [AddCommMonoid W] [Module k W]

def evalLinearEquiv (ρ : Representation k G W) (p : P) : (P →ₑ[ρ] W) ≃ₗ[k] W where
  __ := MulActionHom.evalEquiv ρ p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evalLinearEquiv_apply (ρ : Representation k G W) (p : P) (f : P →ₑ[ρ] W) :
    evalLinearEquiv ρ p f = f p := rfl

@[simp]
theorem evalLinearEquiv_symm_apply (ρ : Representation k G W) (p q : P) (w : W) :
    (evalLinearEquiv ρ p).symm w q = ρ (q /ₛ p) w := rfl

theorem mem_associatedSet_iff (ρ : Representation k G W) {C : Set W}
    (hC : ∀ g : G, MapsTo (ρ g) C C) (p : P) (f : P →ₑ[ρ] W) :
    f ∈ ρ.associatedSet P C ↔ f p ∈ C := by
  refine ⟨fun h => h p, fun h q => ?_⟩
  have heq : f q = ρ (q /ₛ p) (f p) := by
    simpa only [sdiv_smul, Module.End.smul_def] using map_smulₛₗ f (q /ₛ p) p
  rw [heq]
  exact hC (q /ₛ p) h

theorem associatedSet_eq_preimage (ρ : Representation k G W) {C : Set W}
    (hC : ∀ g : G, MapsTo (ρ g) C C) (p : P) :
    ρ.associatedSet P C = (ρ.evalLinearEquiv p) ⁻¹' C := by
  ext f
  exact ρ.mem_associatedSet_iff hC p f

theorem image_associatedSet (ρ : Representation k G W) {C : Set W}
    (hC : ∀ g : G, MapsTo (ρ g) C C) (p : P) :
    ρ.evalLinearEquiv p '' ρ.associatedSet P C = C := by
  rw [ρ.associatedSet_eq_preimage hC p]
  exact (ρ.evalLinearEquiv p).surjective.image_preimage C

theorem associatedSet_nonempty_iff (ρ : Representation k G W) {C : Set W}
    (hC : ∀ g : G, MapsTo (ρ g) C C) :
    (ρ.associatedSet P C).Nonempty ↔ C.Nonempty := by
  obtain ⟨p⟩ := (inferInstance : Nonempty P)
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f p, hf p⟩
  · rintro ⟨w, hw⟩
    exact ⟨(ρ.evalLinearEquiv p).symm w,
      (ρ.mem_associatedSet_iff hC p _).mpr (by simpa using hw)⟩

variable {W' : Type*} [AddCommMonoid W'] [Module k W']

theorem evalLinearEquiv_associatedMap (ρ : Representation k G W) (σ : Representation k G W')
    (f : W → W') (hf : ∀ g w, f (ρ g w) = σ g (f w)) (p : P) :
    ρ.associatedMap σ f hf =
      fun z => (σ.evalLinearEquiv p).symm (f (ρ.evalLinearEquiv p z)) := by
  funext z
  apply (σ.evalLinearEquiv p).injective
  simp

end Group

end Representation

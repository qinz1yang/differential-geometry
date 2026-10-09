import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrDef_O19
import DifferentialGeometry.Topology.Embedding.Lift

/-!
# CH12-S76 G2a: smoothness of `invFunOn φ U' ∘ f` on an open set

If `φ|U'` is a smooth embedding and `f p ∈ φ '' U'` for `p` in an open `V` on which `f` is smooth,
then `p ↦ invFunOn φ U' (f p)` is smooth on `V`, takes values in `U'`, and `φ` of it is `f`
(`IsSmoothEmbedding.lift`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic Set Manifold
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- **`invFunOn` lift.** -/
theorem invFunOn_lift_S76 (H H' : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (U' : TopologicalSpace.Opens H'.Carrier) (f : H.Carrier → N) (φ : H'.Carrier → N)
    (V : TopologicalSpace.Opens H.Carrier)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V)
    (hφ : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x))
    (hrange : ∀ p ∈ V, f p ∈ φ '' (U' : Set H'.Carrier)) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => Function.invFunOn φ U' (f p)) V ∧
      ∀ p ∈ V, Function.invFunOn φ U' (f p) ∈ U' ∧
        φ (Function.invFunOn φ U' (f p)) = f p := by
  have hinjOn : InjOn φ (U' : Set H'.Carrier) := by
    intro a ha b hb hab
    have := hφ.isEmbedding.injective (a₁ := (⟨a, ha⟩ : U')) (a₂ := ⟨b, hb⟩) hab
    exact congrArg Subtype.val this
  have hrg : Set.range (fun x : V => f x) ⊆ Set.range (fun x : U' => φ x) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨q, hq, hqf⟩ := hrange x x.2
    exact ⟨⟨q, hq⟩, hqf⟩
  have gV : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : V => f x) := fun x =>
    contMDiffAt_subtype_iff.mpr (hf.contMDiffAt (V.isOpen.mem_nhds x.2))
  have hℓ := hφ.contMDiff_lift gV hrg
  have key : ∀ x : V, Function.invFunOn φ U' (f x) = ((hφ.lift (fun x : V => f x) hrg x : U') :
      H'.Carrier) := by
    intro x
    have hc : φ ((hφ.lift (fun x : V => f x) hrg x : U') : H'.Carrier) = f x :=
      hφ.comp_lift hrg x
    rw [← hc]
    exact hinjOn.leftInvOn_invFunOn (hφ.lift (fun x : V => f x) hrg x).2
  refine ⟨?_, ?_⟩
  · intro p hp
    have h1 : ContMDiff (𝓡 3) (𝓡 3) ∞
        (fun x : V => Function.invFunOn φ U' (f x)) := by
      have : (fun x : V => Function.invFunOn φ U' (f x)) =
          fun x => ((hφ.lift (fun x : V => f x) hrg x : U') : H'.Carrier) := funext key
      rw [this]
      exact contMDiff_subtype_val.comp hℓ
    have h2 := (contMDiffAt_subtype_iff (I := 𝓡 3) (I' := 𝓡 3) (n := ∞) (U := V)
      (f := fun p => Function.invFunOn φ U' (f p)) (x := ⟨p, hp⟩)).mp (h1 ⟨p, hp⟩)
    exact h2.contMDiffWithinAt
  · intro p hp
    have hk := key ⟨p, hp⟩
    have hq := (hφ.lift (fun x : V => f x) hrg ⟨p, hp⟩).2
    refine ⟨?_, ?_⟩
    · rw [hk]; exact hq
    · rw [hk]; exact hφ.comp_lift hrg ⟨p, hp⟩

end GC.LongTime.Ch12

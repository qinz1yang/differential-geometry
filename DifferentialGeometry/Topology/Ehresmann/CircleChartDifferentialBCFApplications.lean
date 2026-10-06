import DifferentialGeometry.Topology.Ehresmann.CircleChartDifferentialBCF

/-!
# Consumer of `surjective_base_differential_BCF`: the trivial circle chart (lane S-BCF03)

`M = ℝ² × S¹` with its product model, `φ = id`, one face function `F = x₀ ∘ fst` (`Ψ = x₀`): the
differential of `F` is onto (it is the first coordinate), and so is the base differential of `Ψ`.
-/

set_option autoImplicit false

open Set Function Manifold
open scoped ContDiff Manifold

noncomputable section

namespace DifferentialGeometry.Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem surjective_base_differential_example_BCF :
    Surjective fun v : E2 => fun _ : Unit => fderiv ℝ (fun x : E2 => x 0) 0 v := by
  refine surjective_base_differential_BCF (I := (𝓡 2).prod (𝓡 1)) (M := E2 × Circle)
    (fun _ q => q.1 0) (fun _ x => x 0) id IsSmoothEmbedding.id (by simp) (0 : E2) (1 : Circle)
    (fun _ => (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).differentiableAt)
    (fun _ _ _ => rfl) ?_
  intro b
  have hder : ∀ v : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1),
      mvfderiv ((𝓡 2).prod (𝓡 1)) (fun q : E2 × Circle => q.1 0) ((0 : E2), (1 : Circle)) v =
        v.1 0 := by
    intro v
    have hΨm : MDiffAt (fun x : E2 => x 0) (0 : E2) :=
      (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).differentiableAt.mdifferentiableAt
    have hc := mfderiv_comp (I := (𝓡 2).prod (𝓡 1)) (I' := 𝓡 2) (I'' := 𝓘(ℝ, ℝ))
      ((0 : E2), (1 : Circle)) (g := fun x : E2 => x 0) (f := Prod.fst) hΨm mdifferentiableAt_fst
    have h1 : mfderiv ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, ℝ) (fun q : E2 × Circle => q.1 0)
        ((0 : E2), (1 : Circle)) v = v.1 0 := by
      change mfderiv ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, ℝ) ((fun x : E2 => x 0) ∘ Prod.fst)
        ((0 : E2), (1 : Circle)) v = _
      rw [hc]
      have hd : fderiv ℝ (fun x : E2 => x 0) 0 = (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ) :=
        (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).fderiv
      simp [mfderiv_fst, mfderiv_eq_fderiv, hd]
      rfl
    exact h1
  refine ⟨((EuclideanSpace.single 0 (b ()) : E2), (0 : EuclideanSpace ℝ (Fin 1))), ?_⟩
  funext f
  change mvfderiv ((𝓡 2).prod (𝓡 1)) (fun q : E2 × Circle => q.1 0) ((0 : E2), (1 : Circle)) _ = _
  rw [hder]
  simp

end DifferentialGeometry.Topology

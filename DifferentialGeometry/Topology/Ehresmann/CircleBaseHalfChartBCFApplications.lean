import DifferentialGeometry.Topology.Ehresmann.CircleBaseHalfChartBCF

/-!
# Consumer of the circle-base half chart lemmas (lane S-BCF03b)

`M = ℝ² × S¹` with its product model, the trivial circle chart `σ = id`, `φ = id`, `f = fst` and the
coordinate face functions `ψ i = x_i`: the half-plane edge `{x₀ = 0}` has an interior half chart
at `0` (positive coordinate) and the quadrant ray `{x₀ = 0, x₁ ≤ 0}` a corner half chart at `0`
(coordinate `0`).
-/

set_option autoImplicit false

open Set Function Manifold Topology
open scoped ContDiff Manifold

noncomputable section

namespace DifferentialGeometry.Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- The `mvfderiv` of a coordinate function through `fst` on `ℝ² × S¹` is the coordinate. -/
theorem mvfderiv_coord_BCF (i : Fin 2) (v : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) :
    mvfderiv ((𝓡 2).prod (𝓡 1)) (fun q : E2 × Circle => q.1 i) ((0 : E2), (1 : Circle)) v =
      v.1 i := by
  have hΨm : MDiffAt (fun x : E2 => x i) (0 : E2) :=
    (EuclideanSpace.proj i : E2 →L[ℝ] ℝ).differentiableAt.mdifferentiableAt
  have hc := mfderiv_comp (I := (𝓡 2).prod (𝓡 1)) (I' := 𝓡 2) (I'' := 𝓘(ℝ, ℝ))
    ((0 : E2), (1 : Circle)) (g := fun x : E2 => x i) (f := Prod.fst) hΨm mdifferentiableAt_fst
  change mfderiv ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, ℝ) ((fun x : E2 => x i) ∘ Prod.fst)
    ((0 : E2), (1 : Circle)) v = _
  rw [hc]
  have hd : fderiv ℝ (fun x : E2 => x i) 0 = (EuclideanSpace.proj i : E2 →L[ℝ] ℝ) :=
    (EuclideanSpace.proj i : E2 →L[ℝ] ℝ).fderiv
  simp [mfderiv_fst, mfderiv_eq_fderiv, hd]
  rfl

theorem exists_halfChart_circleInterior_example_BCF :
    ∃ (B : Set E2) (d : HalfChart_BCF B {x : E2 | x 0 = 0}), (0 : E2) ∈ d.O ∧
      0 < d.L 0 + d.κ := by
  refine exists_halfChart_of_circleInterior_BCF (I := (𝓡 2).prod (𝓡 1)) (M := E2 × Circle)
    (f := Prod.fst) (B₀ := univ) (σ := id) (φ := id) (Oσ := univ) (O := univ) (ι := Unit)
    (ψ := fun _ x => x 0) rfl contDiff_id Topology.IsEmbedding.id
    (fun x => by simpa using Function.injective_id) isOpen_univ (by simp) IsSmoothEmbedding.id
    (by simp) (fun _ _ => rfl) (subset_univ _) isOpen_univ (mem_univ _)
    (fun _ => (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).contDiff.contDiffOn) (fun _ => rfl)
    () (1 : Circle) ?_ (fun y' _ => Iff.rfl)
  intro b
  refine ⟨((EuclideanSpace.single 0 (b ()) : E2), (0 : EuclideanSpace ℝ (Fin 1))), ?_⟩
  funext f
  change mvfderiv ((𝓡 2).prod (𝓡 1)) (fun q : E2 × Circle => q.1 0) ((0 : E2), (1 : Circle)) _ = _
  rw [mvfderiv_coord_BCF]
  simp

theorem exists_halfChart_circleCorner_example_BCF :
    ∃ (B : Set E2) (d : HalfChart_BCF B {x : E2 | x 0 = 0 ∧ x 1 ≤ 0}), (0 : E2) ∈ d.O ∧
      d.L 0 + d.κ = 0 := by
  refine exists_halfChart_of_circleCorner_BCF (I := (𝓡 2).prod (𝓡 1)) (M := E2 × Circle)
    (f := Prod.fst) (B₀ := univ) (σ := id) (φ := id) (Oσ := univ) (O := univ) (ι := Fin 2)
    (ψ := fun i x => x i) rfl contDiff_id Topology.IsEmbedding.id
    (fun x => by simpa using Function.injective_id) isOpen_univ (by simp) IsSmoothEmbedding.id
    (by simp) (fun _ _ => rfl) (subset_univ _) isOpen_univ (mem_univ _)
    (fun i => (EuclideanSpace.proj i : E2 →L[ℝ] ℝ).contDiff.contDiffOn) (fun _ => rfl)
    0 1 (by decide) (fun i => by fin_cases i <;> simp) (1 : Circle) ?_ (fun y' _ => Iff.rfl)
  intro b
  refine ⟨((WithLp.toLp 2 b : E2), (0 : EuclideanSpace ℝ (Fin 1))), ?_⟩
  funext i
  change mvfderiv ((𝓡 2).prod (𝓡 1)) (fun q : E2 × Circle => q.1 i) ((0 : E2), (1 : Circle)) _ = _
  rw [mvfderiv_coord_BCF]

end DifferentialGeometry.Topology

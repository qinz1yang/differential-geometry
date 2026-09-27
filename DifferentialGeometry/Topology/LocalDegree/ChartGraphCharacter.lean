/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.ChartParity
import Mathlib.Tactic.Abel

open Set

noncomputable section

namespace DifferentialGeometry.LocalDegree

variable {n : ℕ} {M V E : Type*} [TopologicalSpace M]

local notation "Model" => EuclideanSpace ℝ (Fin (n + 1))

def chartGraphCharacter (ends : E → V × V)
    (c : V → OpenPartialHomeomorph M Model)
    (ce : E → OpenPartialHomeomorph M Model) (p : V → M)
    (hpc : ∀ v, p v ∈ (c v).source)
    (hpe : ∀ e, p (ends e).1 ∈ (ce e).source ∧ p (ends e).2 ∈ (ce e).source)
    (e : E) : ZMod 2 :=
  chartOrientationParity (c (ends e).1) (ce e) (p (ends e).1) (hpc _) (hpe e).1 +
    chartOrientationParity (c (ends e).2) (ce e) (p (ends e).2) (hpc _) (hpe e).2 + 1

theorem exists_vertex_signs_of_connected_chart_carriers
    (ends : E → V × V) (A : V → Set M)
    (hA : ∀ v, IsPreconnected (A v))
    (b c d : V → OpenPartialHomeomorph M Model)
    (ce : E → OpenPartialHomeomorph M Model)
    (hAb : ∀ v, A v ⊆ (b v).source)
    (hAe : ∀ e, A (ends e).1 ∪ A (ends e).2 ⊆ (ce e).source)
    (p q : V → M) (hp : ∀ v, p v ∈ A v) (hq : ∀ v, q v ∈ A v)
    (hpc : ∀ v, p v ∈ (c v).source) (hqd : ∀ v, q v ∈ (d v).source) :
    ∃ σ : V → ZMod 2, ∀ e,
      chartGraphCharacter ends c ce p hpc
          (fun e => ⟨hAe e (Or.inl (hp _)), hAe e (Or.inr (hp _))⟩) e +
        chartGraphCharacter ends d ce q hqd
          (fun e => ⟨hAe e (Or.inl (hq _)), hAe e (Or.inr (hq _))⟩) e =
        σ (ends e).1 + σ (ends e).2 := by
  let σ : V → ZMod 2 := fun v =>
    chartOrientationParity (c v) (b v) (p v) (hpc v) (hAb v (hp v)) +
      chartOrientationParity (d v) (b v) (q v) (hqd v) (hAb v (hq v))
  refine ⟨σ, fun e => ?_⟩
  have hz : ∀ z : ZMod 2, z + z = 0 := by decide
  have hlocal (v : V) (hv : A v ⊆ (ce e).source) :
      chartOrientationParity (c v) (ce e) (p v) (hpc v) (hv (hp v)) +
        chartOrientationParity (d v) (ce e) (q v) (hqd v) (hv (hq v)) = σ v := by
    have hconst := chartOrientationParity_eq_of_isPreconnected
      (b v) (ce e) (hA v) (hAb v) hv (hp v) (hq v)
    have hcoc := chartOrientationParity_add (c v) (b v) (ce e)
      (p v) (hpc v) (hAb v (hp v)) (hv (hp v))
    have hdoc := chartOrientationParity_add (d v) (b v) (ce e)
      (q v) (hqd v) (hAb v (hq v)) (hv (hq v))
    rw [← hcoc, ← hdoc, ← hconst]
    calc
      _ = σ v + (chartOrientationParity (b v) (ce e) (p v) _ _ +
        chartOrientationParity (b v) (ce e) (p v) _ _) := by dsimp [σ]; abel
      _ = σ v := by rw [hz, add_zero]
  have h₁ := hlocal (ends e).1 (subset_union_left.trans (hAe e))
  have h₂ := hlocal (ends e).2 (subset_union_right.trans (hAe e))
  unfold chartGraphCharacter
  calc
    _ =
        (chartOrientationParity (c (ends e).1) (ce e) (p (ends e).1) _ _ +
          chartOrientationParity (d (ends e).1) (ce e) (q (ends e).1) _ _) +
        (chartOrientationParity (c (ends e).2) (ce e) (p (ends e).2) _ _ +
          chartOrientationParity (d (ends e).2) (ce e) (q (ends e).2) _ _) +
        (1 + 1) := by abel
    _ = σ (ends e).1 + σ (ends e).2 := by rw [h₁, h₂, hz, add_zero]

end DifferentialGeometry.LocalDegree

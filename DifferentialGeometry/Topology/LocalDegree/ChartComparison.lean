/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.ChartParityTransport
import DifferentialGeometry.Topology.LocalDegree.ChartParityGerm

open Filter
open scoped Topology Manifold

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))

theorem chartOrientationParity_comparison
    (H T₁ T₂ : OpenPartialHomeomorph M N) (K : OpenPartialHomeomorph N N)
    (c : OpenPartialHomeomorph N E) (x : M)
    (hxH : x ∈ H.source) (hx₁ : x ∈ T₁.source) (hx₂ : x ∈ T₂.source)
    (hxK : T₂ x ∈ K.source)
    (hcH : H x ∈ c.source) (hc₁ : T₁ x ∈ c.source) (hc₂ : T₂ x ∈ c.source)
    (hcomp : (K ∘ T₂) =ᶠ[𝓝 x] T₁) :
    chartOrientationParity c (K ≫ₕ c) (T₂ x) hc₂
        ⟨hxK, by
          change (K ∘ T₂) x ∈ c.source
          rw [hcomp.self_of_nhds]
          exact hc₁⟩ =
      chartOrientationParity (H ≫ₕ c) (T₁ ≫ₕ c) x ⟨hxH, hcH⟩ ⟨hx₁, hc₁⟩ +
        chartOrientationParity (H ≫ₕ c) (T₂ ≫ₕ c) x ⟨hxH, hcH⟩ ⟨hx₂, hc₂⟩ := by
  have hcK : K (T₂ x) ∈ c.source := by
    change (K ∘ T₂) x ∈ c.source
    rw [hcomp.self_of_nhds]
    exact hc₁
  have hpull := chartOrientationParity_pullback T₂ c (K ≫ₕ c) x hx₂ hc₂ ⟨hxK, hcK⟩
  have heq : (T₂ ≫ₕ (K ≫ₕ c)) =ᶠ[𝓝 x] (T₁ ≫ₕ c) := by
    filter_upwards [hcomp] with y hy
    exact congrArg c hy
  have hchange := chartOrientationParity_right_congr (T₂ ≫ₕ c) (T₂ ≫ₕ (K ≫ₕ c))
    (T₁ ≫ₕ c) x ⟨hx₂, hc₂⟩ ⟨hx₂, hxK, hcK⟩ ⟨hx₁, hc₁⟩ heq
  have hadd := chartOrientationParity_add (H ≫ₕ c) (T₂ ≫ₕ c) (T₁ ≫ₕ c) x
    ⟨hxH, hcH⟩ ⟨hx₂, hc₂⟩ ⟨hx₁, hc₁⟩
  have hsum := congrArg
    (fun z => chartOrientationParity (H ≫ₕ c) (T₂ ≫ₕ c) x ⟨hxH, hcH⟩ ⟨hx₂, hc₂⟩ + z) hadd
  have hz : ∀ s : ZMod 2, s + s = 0 := by decide
  rw [← add_assoc, hz, zero_add] at hsum
  exact hpull.symm.trans (hchange.trans (hsum.trans (add_comm _ _)))

end DifferentialGeometry.LocalDegree

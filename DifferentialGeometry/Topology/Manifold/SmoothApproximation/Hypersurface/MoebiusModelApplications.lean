import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Hypersurface.MoebiusModel

/-!
# Consumer: a smooth one-sided core circle of the open Möbius band

W-SUB's `exists_smooth_hypersurface_one_sided` applied to the Möbius data
(`moebius_one_sided_data`): for every `δ > 0` there is a compact smooth one-sided embedded circle
in the `δ`-tube of the core of `NormalLineBundle (-1)`, the graph of an antisymmetric function over
the double cover, smoothly diffeomorphic to the base circle `ℝ/ℤ` by the normal projection.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold.SmoothHypersurface

open DifferentialGeometry.Geometry.FiniteSoul
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Topology

/-- **A smooth one-sided core circle of the Möbius band.** For every `n ≥ 1` and `δ > 0` the open
Möbius band contains a compact smooth embedded circle `Ŝ` inside the `δ`-tube of its core: the
graph `{Φ (v, h v)}` of a `C^n` function `h` on the double cover, antisymmetric under the deck
involution and `δ`-small, with the normal projection a `C^n` diffeomorphism `β : Ŝ ≃ ℝ/ℤ` onto
the base circle. -/
theorem exists_smooth_moebius_core_hypersurface {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Ŝ : Set (NormalLineBundle (-1)), ∃ hŜ : IsEmbeddedSlice 𝓘(ℝ, ℝ × ℝ) 1 Ŝ, IsCompact Ŝ ∧
      Ŝ ⊆ moebiusTube '' (univ ×ˢ Ioo (-δ) δ) ∧
      let _ := embeddedSliceChartedSpace hŜ
      ∃ β : Diffeomorph 𝓘(ℝ, Fin 1 → ℝ) 𝓘(ℝ, ℝ) Ŝ (AddCircle (1 : ℝ)) n,
        ∃ h : AddCircle (1 : ℝ) → ℝ, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n h ∧
          (∀ v, h (moebiusHalf v) = -h v) ∧ (∀ v, |h v| < δ) ∧
          (∀ v, (β.symm (moebiusDouble v) : NormalLineBundle (-1)) = moebiusTube (v, h v)) ∧
          ∀ (x : Ŝ) (v : AddCircle (1 : ℝ)) (t : ℝ), t ∈ Ioo (-δ) δ →
            moebiusTube (v, t) = x → β x = moebiusDouble v := by
  obtain ⟨hloc, hσ, hσσ, hequiv, hinj, hπ, hπs, hπσ⟩ := moebius_one_sided_data n δ
  exact exists_smooth_hypersurface_one_sided (I := 𝓘(ℝ, ℝ × ℝ)) (IS := 𝓘(ℝ, ℝ))
    (IS' := 𝓘(ℝ, ℝ)) (by simp : Module.finrank ℝ (ℝ × ℝ) = 1 + 1) hn hδ le_rfl hloc hσ hσσ
    hequiv hinj hπ hπs hπσ

end DifferentialGeometry.Topology.Manifold.SmoothHypersurface

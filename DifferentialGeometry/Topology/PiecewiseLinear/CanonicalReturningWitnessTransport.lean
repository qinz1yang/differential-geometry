/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalBridgeWitnesses

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable [DecidableEq E3] {X Y : ℤ → Geometry.SimplicialComplex ℝ E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem HasCanonicalBridgeWitnesses.of_returning_component_deletion
    (hX : HasCanonicalBridgeWitnesses X T'')
    (hstate : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (i : ℤ) (c₀ : ConnectedComponents (X i).space)
    (hreturn : IsCanonicalReturningComponent X T'' i c₀)
    (hd : IsCanonicalComponentDeletion i X Y c₀) : HasCanonicalBridgeWitnesses Y T'' := by
  intro j
  obtain ⟨c, G₀, G₁, h₀, h₁, he₀, he₁⟩ := hX j
  by_cases hji : j = i
  · subst j
    have hne : c ≠ c₀ := by
      intro hc
      exact hstate.not_returning_component_of_opposite_seams htw i c h₀ h₁ (hc.symm ▸ hreturn)
    obtain ⟨e, he⟩ := hd.retained
    refine ⟨e ⟨c, hne⟩, G₀, G₁, ?_, ?_, he₀, he₁⟩
    · simpa only [he ⟨c, hne⟩] using h₀
    · simpa only [he ⟨c, hne⟩] using h₁
  · rw [hd.unchanged j hji]
    exact ⟨c, G₀, G₁, h₀, h₁, he₀, he₁⟩

end DifferentialGeometry.Topology.PiecewiseLinear

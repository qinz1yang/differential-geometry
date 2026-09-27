/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceEssentialBoundaryTransport
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalComponentMarkRetention
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalBridgeWindowReduction

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def HasCanonicalBridgeWitnesses
    (X : ℤ → Geometry.SimplicialComplex ℝ E3) (T : ℤ → Set E3) : Prop :=
  ∀ i, ∃ (c : ConnectedComponents (X i).space) (G₀ G₁ : Set E3),
    G₀ ∈ traceCircles (connectedComponentComplex (X i) c).space (T (2 * i)) ∧
    G₁ ∈ traceCircles (connectedComponentComplex (X i) c).space (T (2 * (i + 1))) ∧
    ¬ boundsDiskIn G₀ (T (2 * i + 1)) ∧ ¬ boundsDiskIn G₁ (T (2 * i + 1))

variable [DecidableEq E3] {X Y : ℤ → Geometry.SimplicialComplex ℝ E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I F : Set E3} {P' a b : E3} {rows : Finset ℤ}

theorem HasCanonicalBridgeWitnesses.of_null_splits
    (hX : HasCanonicalBridgeWitnesses X T'')
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (window : Finset ℤ)
    (hpath : Relation.ReflTransGen (fun U V =>
      IsCanonicalSurface U (fun j => φ '' S j) T'' I P' a b ∧
      IsCanonicalSurface V (fun j => φ '' S j) T'' I P' a b ∧
      ∃ i ∈ window, IsCanonicalNullSplit (fun j => φ '' S j) T'' i U V) X Y) :
    HasCanonicalBridgeWitnesses Y T'' := by
  intro i
  obtain ⟨c, G₀, G₁, h₀, h₁, he₀, he₁⟩ := hX i
  obtain ⟨d, hd₀, hd₁⟩ :=
    htw.exists_component_containing_essential_seams_of_null_splits h314 window hpath i
      ⟨c, h₀, h₁⟩ he₀ he₁
  exact ⟨d, G₀, G₁, hd₀, hd₁, he₀, he₁⟩

theorem HasCanonicalBridgeWitnesses.of_closed_reduction
    (hX : HasCanonicalBridgeWitnesses X T'')
    (hred : IsCanonicalClosedWindowReduction X Y (fun j => φ '' S j) T'' I P' a b rows F) :
    HasCanonicalBridgeWitnesses Y T'' := by
  intro i
  obtain ⟨c, G₀, G₁, h₀, h₁, he₀, he₁⟩ := hX i
  obtain ⟨d, hd₀, hd₁⟩ := hred.exists_component_containing_opposite_seams i ⟨c, h₀, h₁⟩
  exact ⟨d, G₀, G₁, hd₀, hd₁, he₀, he₁⟩

theorem HasCanonicalBridgeWitnesses.of_returning_reduction
    (hX : HasCanonicalBridgeWitnesses X T'')
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hred : IsCanonicalReturningWindowReduction X Y (fun j => φ '' S j) S'' T''
      I P' a b rows F) : HasCanonicalBridgeWitnesses Y T'' := by
  intro i
  obtain ⟨c, G₀, G₁, h₀, h₁, he₀, he₁⟩ := hX i
  obtain ⟨d, hd₀, hd₁⟩ := hred.exists_component_containing_opposite_seams htw i ⟨c, h₀, h₁⟩
  exact ⟨d, G₀, G₁, hd₀, hd₁, he₀, he₁⟩

theorem HasCanonicalBridgeWitnesses.of_bridge_reduction
    (hX : HasCanonicalBridgeWitnesses X T'')
    (hred : IsCanonicalBridgeWindowReduction X Y (fun j => φ '' S j) S'' T''
      I P' a b rows F) : HasCanonicalBridgeWitnesses Y T'' := by
  intro i
  by_cases hi : i ∈ rows
  · obtain ⟨c, -⟩ := Nat.card_eq_one_iff_exists.mp (hred.singleComponent i hi)
    obtain ⟨G₀, G₁, -, h₀, h₁, he₀, he₁⟩ := hred.bridgeComponents i hi c
    exact ⟨c, G₀, G₁, h₀, h₁, he₀, he₁⟩
  · rw [hred.unchanged i hi]
    exact hX i

omit [DecidableEq E3] in
theorem HasCanonicalBridgeWitnesses.nonempty_components
    (hX : HasCanonicalBridgeWitnesses X T'') (i : ℤ) :
    Nonempty (ConnectedComponents (X i).space) := by
  obtain ⟨c, -⟩ := hX i
  exact ⟨c⟩

end DifferentialGeometry.Topology.PiecewiseLinear

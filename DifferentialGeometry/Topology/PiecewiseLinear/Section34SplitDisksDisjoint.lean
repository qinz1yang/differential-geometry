/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}

theorem section34_splitDisks_disjoint
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    {e d : Section34EdgeIndex 𝒦 𝒦'} (hne : e ≠ d) :
    Disjoint (src (.splitDisk e)) (src (.splitDisk d)) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hvertexEdge, hends, -, -⟩ := hframe
  refine disjoint_left.mpr ?_
  intro x hxe hxd
  obtain ⟨a, b, -, hab, hd⟩ := hends d
  rw [hd] at hxd
  have hae : (a.1 : Set Ea) ⊆ (e.1 : Set Ea) :=
    hvertexEdge a e ⟨x, hxd.1, hxe⟩
  have hbe : (b.1 : Set Ea) ⊆ (e.1 : Set Ea) :=
    hvertexEdge b e ⟨x, hxd.2, hxe⟩
  have hde : d.1 ⊆ e.1 := by
    intro y hy
    have hy' : y ∈ (d.1 : Set Ea) := hy
    rw [hab] at hy'
    exact hy'.elim (hae ·) (hbe ·)
  have hcard : e.1.card ≤ d.1.card := by rw [e.2.2.1, d.2.2.1]
  exact hne (Subtype.ext (Finset.eq_of_subset_of_card_le hde hcard).symm)

end DifferentialGeometry.Topology.PiecewiseLinear

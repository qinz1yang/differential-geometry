/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPairMap
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}

theorem exists_section34_shared_splitDisk_maps
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e)) :
    ∃ φ : Section34EdgeIndex 𝒦 𝒦' → M₁ → M₂,
      (∀ e, IsPLHomeomorphInto 3 (φ e) (src (.splitDisk e))) ∧
      (∀ e, φ e '' src (.splitDisk e) = Dd e) ∧
      ∀ e, φ e '' srcBd (.splitDisk e) = DdBd e := by
  choose φ hφ hφD hφB using fun e =>
    exists_isPLHomeomorphInto_cells (hframe.2.2.2.1 (.splitDisk e)) (hDd e)
  exact ⟨φ, hφ, hφD, hφB⟩

end DifferentialGeometry.Topology.PiecewiseLinear

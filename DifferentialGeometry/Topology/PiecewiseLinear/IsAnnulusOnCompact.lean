/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {X : Type*} [TopologicalSpace X] {A A₀ A₁ : Set X}

theorem IsAnnulusOn.isCompact (hann : IsAnnulusOn A A₀ A₁) : IsCompact A := by
  obtain ⟨φ, -, -⟩ := hann
  have : CompactSpace A := φ.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

theorem IsAnnulusOn.isCompact_first (hann : IsAnnulusOn A A₀ A₁) : IsCompact A₀ := by
  obtain ⟨φ, h₀, -⟩ := hann
  rw [h₀]
  apply IsCompact.image _ continuous_subtype_val
  apply IsCompact.image _ φ.continuous
  exact (isClosed_eq continuous_snd.subtype_val continuous_const).isCompact

theorem IsAnnulusOn.isCompact_second (hann : IsAnnulusOn A A₀ A₁) : IsCompact A₁ := by
  obtain ⟨φ, -, h₁⟩ := hann
  rw [h₁]
  apply IsCompact.image _ continuous_subtype_val
  apply IsCompact.image _ φ.continuous
  exact (isClosed_eq continuous_snd.subtype_val continuous_const).isCompact

end DifferentialGeometry.Topology.PiecewiseLinear

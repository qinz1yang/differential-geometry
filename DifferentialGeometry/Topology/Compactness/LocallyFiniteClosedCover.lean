/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.NhdsSet
import Mathlib.Topology.Compactness.Compact

open Set Topology

namespace DifferentialGeometry.Topology

theorem mem_interior_of_locally_finite_closed_cover_unique
    {ι X : Type*} [TopologicalSpace X] {D Q : ι → Set X}
    {x : X} {i₀ : ι}
    (hDclosed : ∀ i, IsClosed (D i))
    (hDQ : ∀ i, D i ⊆ Q i)
    (hfinite : ∃ V ∈ 𝓝 x, {i | (Q i ∩ V).Nonempty}.Finite)
    (hother : ∀ i, i ≠ i₀ → x ∉ D i)
    (hint : x ∈ interior (⋃ i, D i)) :
    x ∈ interior (D i₀) := by
  classical
  obtain ⟨V, hV, hF⟩ := hfinite
  let F : Set ι := {i | (Q i ∩ V).Nonempty}
  let B : Set ι := {i | i ∈ F ∧ i ≠ i₀}
  have hB : B.Finite := hF.subset fun i hi => hi.1
  have : Finite B := hB.to_subtype
  have hclosed : IsClosed (⋃ i : B, D i.1) :=
    isClosed_iUnion_of_finite fun i => hDclosed i.1
  have hxB : x ∉ ⋃ i : B, D i.1 := by
    intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hother i.1 i.2.2 hi
  let O : Set X := interior V ∩ (⋃ i : B, D i.1)ᶜ ∩ interior (⋃ i, D i)
  have hOopen : IsOpen O := (isOpen_interior.inter hclosed.isOpen_compl).inter isOpen_interior
  have hxO : x ∈ O := ⟨⟨mem_interior_iff_mem_nhds.mpr hV, hxB⟩, hint⟩
  have hOsub : O ⊆ D i₀ := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (interior_subset hy.2)
    have hiF : i ∈ F := ⟨y, hDQ i hi, interior_subset hy.1.1⟩
    by_cases hii : i = i₀
    · exact hii ▸ hi
    · exact False.elim (hy.1.2 (mem_iUnion.mpr ⟨⟨i, hiF, hii⟩, hi⟩))
  exact interior_maximal hOsub hOopen hxO

end DifferentialGeometry.Topology

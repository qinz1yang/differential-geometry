/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Connected.Basic

open Set

namespace DifferentialGeometry.Topology

variable {X ι : Type*} [TopologicalSpace X]

theorem isClosed_sdiff_connectedComponentIn_of_finite_closed_cover
    {S : Set X} {t : Set ι} (ht : t.Finite) (C : ι → Set X)
    (hclosed : ∀ i ∈ t, IsClosed (C i)) (hconn : ∀ i ∈ t, IsPreconnected (C i))
    (hcover : S = ⋃ i ∈ t, C i) (x : X) :
    IsClosed (S \ connectedComponentIn S x) := by
  classical
  let d := {i ∈ t | ¬C i ⊆ connectedComponentIn S x}
  have hsub (i : ι) (hi : i ∈ t) : C i ⊆ S := by
    rw [hcover]
    exact subset_iUnion_of_subset i (subset_iUnion_of_subset hi Subset.rfl)
  have hdis (i : ι) (hi : i ∈ d) : Disjoint (C i) (connectedComponentIn S x) := by
    rw [disjoint_left]
    intro p hpC hp
    apply hi.2
    have hCp := (hconn i hi.1).subset_connectedComponentIn hpC (hsub i hi.1)
    rwa [← connectedComponentIn_eq hp] at hCp
  have heq : S \ connectedComponentIn S x = ⋃ i ∈ d, C i := by
    ext p
    constructor
    · rintro ⟨hpS, hpnot⟩
      rw [hcover] at hpS
      obtain ⟨i, hi, hpC⟩ := mem_iUnion₂.mp hpS
      exact mem_iUnion₂.mpr ⟨i, ⟨hi, fun h => hpnot (h hpC)⟩, hpC⟩
    · intro hp
      obtain ⟨i, hi, hpC⟩ := mem_iUnion₂.mp hp
      exact ⟨hsub i hi.1 hpC, fun h => Set.disjoint_left.mp (hdis i hi) hpC h⟩
  rw [heq]
  exact (ht.subset fun _ hi => hi.1).isClosed_biUnion fun i hi => hclosed i hi.1

end DifferentialGeometry.Topology

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentPartitionEquivalence

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sdiff_connectedComponentComplex_space (K : Geometry.SimplicialComplex ℝ E)
    (c : ConnectedComponents K.space) :
    K.space \ (connectedComponentComplex K c).space =
      ⋃ d : {d : ConnectedComponents K.space // d ≠ c}, (connectedComponentComplex K d).space := by
  classical
  ext x
  constructor
  · rintro ⟨hxK, hxc⟩
    obtain ⟨d, hxd⟩ := mem_iUnion.mp ((iUnion_connectedComponentComplex_space K).symm.subset hxK)
    have hdc : d ≠ c := fun heq => hxc (heq ▸ hxd)
    exact mem_iUnion.mpr ⟨⟨d, hdc⟩, hxd⟩
  · intro hx
    obtain ⟨d, hxd⟩ := mem_iUnion.mp hx
    exact ⟨(iUnion_connectedComponentComplex_space K).subset (mem_iUnion.mpr ⟨d, hxd⟩),
      disjoint_left.mp (pairwise_disjoint_connectedComponentComplex_space K d.property) hxd⟩

theorem isPolyhedron_sdiff_connectedComponentComplex [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (c : ConnectedComponents K.space) :
    IsPolyhedron (K.space \ (connectedComponentComplex K c).space) := by
  let _ : Finite (ConnectedComponents K.space) := finite_connectedComponents_space K
  let _ (d : ConnectedComponents K.space) : Finite (connectedComponentComplex K d).faces :=
    (connectedComponentComplex_faces_finite K d).to_subtype
  rw [sdiff_connectedComponentComplex_space]
  exact IsPolyhedron.iUnion fun d => isPolyhedron_space (connectedComponentComplex K d)

theorem boundaryComplex_space_connectedComponentComplex [DecidableEq E]
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) (c : ConnectedComponents K.space) :
    (boundaryComplex n (connectedComponentComplex K c)).space =
      (boundaryComplex n K).space ∩ (connectedComponentComplex K c).space := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [connectedComponentComplex_mk, boundaryComplex_space_restrict_connectedComponentIn,
    restrict_connectedComponentIn_space]

end General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_polyhedral_component_complement
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (c₀ : ConnectedComponents K.space) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      R.space = K.space \ (connectedComponentComplex K c₀).space ∧
      (∃ e : {c : ConnectedComponents K.space // c ≠ c₀} ≃ ConnectedComponents R.space,
        ∀ c, (connectedComponentComplex R (e c)).space = (connectedComponentComplex K c).space) ∧
      Nat.card (ConnectedComponents R.space) + 1 = Nat.card (ConnectedComponents K.space) := by
  classical
  let _ : Finite (ConnectedComponents K.space) := finite_connectedComponents_space K
  let _ (c : ConnectedComponents K.space) : Finite (connectedComponentComplex K c).faces :=
    (connectedComponentComplex_faces_finite K c).to_subtype
  obtain ⟨R, hRfin, hRspace⟩ :=
    (isPolyhedron_sdiff_connectedComponentComplex K c₀).exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite (ConnectedComponents R.space) := finite_connectedComponents_space R
  obtain ⟨e, he⟩ := exists_equiv_connectedComponents_of_finite_partition R
    (fun c : {c : ConnectedComponents K.space // c ≠ c₀} => (connectedComponentComplex K c).space)
    (fun c => isConnected_connectedComponentComplex_space K c)
    (fun c => (isPolyhedron_space (connectedComponentComplex K c)).isClosed)
    (fun c d hcd => pairwise_disjoint_connectedComponentComplex_space K
      (fun h => hcd (Subtype.ext h)))
    (hRspace.trans (sdiff_connectedComponentComplex_space K c₀))
  refine ⟨R, hRfin, hRspace, ⟨e, he⟩, ?_⟩
  let _ : Fintype (ConnectedComponents K.space) := Fintype.ofFinite _
  let _ : Nonempty (ConnectedComponents K.space) := ⟨c₀⟩
  let _ : Unique {c : ConnectedComponents K.space // c = c₀} :=
    ⟨⟨⟨c₀, rfl⟩⟩, fun c => Subtype.ext c.property⟩
  have hcard : Nat.card {c : ConnectedComponents K.space // c ≠ c₀} =
      Nat.card (ConnectedComponents K.space) - 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_unique] using
      Fintype.card_subtype_compl (fun c : ConnectedComponents K.space => c = c₀)
  have hpos : 0 < Nat.card (ConnectedComponents K.space) := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_pos : 0 < Fintype.card (ConnectedComponents K.space))
  have hecard := Nat.card_congr e
  omega

end DifferentialGeometry.Topology.PiecewiseLinear

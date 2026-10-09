/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BigonDrag
import DifferentialGeometry.Topology.PiecewiseLinear.BigonDragHomeomorph
import DifferentialGeometry.Topology.PiecewiseLinear.FirstHomologyCarrying

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem CarriesFirstHomologyOnto.bigonDrag_image {X : Type*} [TopologicalSpace X] [T2Space X]
    {J Y : Set X} (h : CarriesFirstHomologyOnto J Y)
    (e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)) (hsupp : slideSupport ⊆ e.target)
    (hY : ∀ x ∈ e.source, x ∈ Y ↔ 0 ≤ (e x).2.2) :
    CarriesFirstHomologyOnto (e.conjugateMap slideMap '' J) Y := by
  obtain ⟨H, hH, h0, h1, -, -, hHY, -, -⟩ := exists_bigonDrag e hsupp
    (Sf := {x | (e x).2.2 = 0}) (C := {x | (e x).1 = 0 ∧ (e x).2.2 = 0})
    (Tr := {x | (e x).2.2 = 0 ∧ (e x).1 = (1 / 2 - |(e x).2.1|) / 2})
    (fun _ _ => Iff.rfl) hY (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
  have himage : e.conjugateMap slideMap '' J ⊆ Y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← h1 x]
    exact (hHY x 1).mpr (h.1 hx)
  let g : C(J, e.conjugateMap slideMap '' J) :=
    ⟨fun x => ⟨e.conjugateMap slideMap x, x, x.2, rfl⟩,
      ((bigonDragHomeomorph e hsupp).continuous.comp continuous_subtype_val).subtype_mk _⟩
  apply h.of_homotopic himage g
  refine ⟨{ toFun := fun q => ⟨H (q.2.1, q.1), (hHY q.2.1 q.1).mpr (h.1 q.2.2)⟩
            continuous_toFun := ?_
            map_zero_left := fun x => Subtype.ext (h0 x)
            map_one_left := fun x => Subtype.ext (h1 x) }⟩
  exact (hH.comp ((continuous_subtype_val.comp continuous_snd).prodMk
    continuous_fst)).subtype_mk _

end DifferentialGeometry.Topology.PiecewiseLinear

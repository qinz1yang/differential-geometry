/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartSlide
import Mathlib.Data.Set.Card
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def slideHomeomorph : (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ) := by
  have ht : Filter.Tendsto slideMap (Filter.cocompact (ℝ × ℝ × ℝ))
      (Filter.cocompact (ℝ × ℝ × ℝ)) := by
    apply Filter.Tendsto.congr' _ Filter.tendsto_id
    filter_upwards [isCompact_slideSupport.compl_mem_cocompact] with p hp
    exact (eqOn_slideMap_id_compl hp).symm
  exact (Equiv.ofBijective slideMap bijective_slideMap).toHomeomorphOfContinuousClosed
    continuous_slideMap
    (isProperMap_iff_tendsto_cocompact.mpr ⟨continuous_slideMap, ht⟩).isClosedMap

theorem slideHomeomorph_apply (p : ℝ × ℝ × ℝ) : slideHomeomorph p = slideMap p := rfl

noncomputable def bigonDragHomeomorph {X : Type*} [TopologicalSpace X] [T2Space X]
    (e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)) (hsupp : slideSupport ⊆ e.target) : X ≃ₜ X :=
  e.conjugateHomeomorph slideHomeomorph isCompact_slideSupport hsupp eqOn_slideMap_id_compl

theorem bigonDragHomeomorph_apply {X : Type*} [TopologicalSpace X] [T2Space X]
    (e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)) (hsupp : slideSupport ⊆ e.target) (x : X) :
    bigonDragHomeomorph e hsupp x = e.conjugateMap slideMap x := rfl

theorem bigonDragHomeomorph_eqOn_compl {X : Type*} [TopologicalSpace X] [T2Space X]
    (e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)) (hsupp : slideSupport ⊆ e.target) :
    EqOn (bigonDragHomeomorph e hsupp) id (e.symm '' slideSupport)ᶜ :=
  e.conjugateMap_eqOn_compl eqOn_slideMap_id_compl

theorem isPLHomeomorphOn_bigonDragHomeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph E (ℝ × ℝ × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    (hsupp : slideSupport ⊆ e.target) :
    IsPLHomeomorphOn (bigonDragHomeomorph e hsupp) univ univ := by
  exact isPLHomeomorphOn_openPartialHomeomorph
    (bigonDragHomeomorph e hsupp).toOpenPartialHomeomorph
    (isPiecewiseAffineOn_chartSlide e he hei hsupp)

theorem bigonDrag_ncard_trace_components {X : Type*} [TopologicalSpace X] [T2Space X]
    (e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)) (hsupp : slideSupport ⊆ e.target) (Tr : Set X) :
    ((fun x => connectedComponentIn (e.conjugateMap slideMap '' Tr) x) ''
      (e.conjugateMap slideMap '' Tr)).ncard =
        ((fun x => connectedComponentIn Tr x) '' Tr).ncard := by
  let Φ := bigonDragHomeomorph e hsupp
  change ((fun x => connectedComponentIn (Φ '' Tr) x) '' (Φ '' Tr)).ncard = _
  have himage : (fun x => connectedComponentIn (Φ '' Tr) x) '' (Φ '' Tr) =
      (fun S : Set X => Φ '' S) '' ((fun x => connectedComponentIn Tr x) '' Tr) := by
    rw [image_image, image_image]
    apply image_congr
    intro x hx
    exact (Φ.image_connectedComponentIn hx).symm
  rw [himage]
  exact ncard_image_of_injective _ Φ.injective.image_injective

end DifferentialGeometry.Topology.PiecewiseLinear

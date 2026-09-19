/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Homeomorph.Conjugate

/-! Continuous compactly supported ambient families transported through a fixed chart. -/

open Set Topology

namespace OpenPartialHomeomorph

theorem continuous_conjugateMap_family
    {P X Y : Type*} [TopologicalSpace P] [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    {f : P × Y → Y} (hf : Continuous f)
    (hmap : ∀ p, MapsTo (fun y => f (p, y)) e.target e.target)
    {C : Set Y} (hC : IsCompact C) (hCt : C ⊆ e.target)
    (hfix : ∀ p, EqOn (fun y => f (p, y)) id Cᶜ) :
    Continuous (fun q : P × X => e.conjugateMap (fun y => f (q.1, y)) q.2) := by
  have hclosed : IsClosed (e.symm '' C) :=
    (hC.image_of_continuousOn (e.continuousOn_symm.mono hCt)).isClosed
  rw [continuous_iff_continuousAt]
  intro q
  by_cases hq : q.2 ∈ e.source
  · have hinput : ContinuousAt (fun z : P × X => (z.1, e z.2)) q :=
      continuousAt_fst.prodMk ((e.continuousAt hq).comp continuousAt_snd)
    have hmiddle : ContinuousAt (fun z : P × X => f (z.1, e z.2)) q :=
      hf.continuousAt.comp hinput
    have hc : ContinuousAt (fun z : P × X => e.symm (f (z.1, e z.2))) q :=
      (e.continuousAt_symm (hmap q.1 (e.map_source hq))).comp
        (f := fun z : P × X => f (z.1, e z.2)) (x := q) hmiddle
    apply hc.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hq)] with z hz
    exact e.conjugateMap_of_mem _ hz
  · have hqC : q.2 ∉ e.symm '' C := by
      rintro ⟨y, hy, heq⟩
      exact hq (heq ▸ e.map_target (hCt hy))
    apply continuousAt_snd.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (hclosed.isOpen_compl.mem_nhds hqC)] with z hz
    exact e.conjugateMap_eqOn_compl (hfix z.1) hz

theorem exists_conjugate_homeomorph_family
    {P X Y : Type*} [TopologicalSpace P] [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y) (D : P → Y ≃ₜ Y)
    (hD : Continuous (fun q : P × Y => D q.1 q.2))
    (hDi : Continuous (fun q : P × Y => (D q.1).symm q.2))
    {C : Set Y} (hC : IsCompact C) (hCt : C ⊆ e.target)
    (hfix : ∀ p, EqOn (D p) id Cᶜ ∧ EqOn (D p).symm id Cᶜ) :
    ∃ J : P → X ≃ₜ X,
      Continuous (fun q : P × X => J q.1 q.2) ∧
      Continuous (fun q : P × X => (J q.1).symm q.2) ∧
      (∀ p x, J p x = e.conjugateMap (D p) x ∧
        (J p).symm x = e.conjugateMap (D p).symm x) ∧
      ∀ p, EqOn (J p) id (e.symm '' C)ᶜ ∧ EqOn (J p).symm id (e.symm '' C)ᶜ := by
  have hmaps (k : Y ≃ₜ Y) (hk : EqOn k id Cᶜ) : MapsTo k e.target e.target := by
    intro y hy
    by_contra hnot
    have hyC : k y ∉ C := fun hky => hnot (hCt hky)
    have heq : k y = y := k.injective (hk hyC)
    exact hnot (heq.symm ▸ hy)
  let J (p : P) : X ≃ₜ X := e.conjugateHomeomorph (D p) hC hCt (hfix p).1
  exact ⟨J, e.continuous_conjugateMap_family hD (fun p => hmaps _ (hfix p).1)
      hC hCt (fun p => (hfix p).1),
    e.continuous_conjugateMap_family hDi (fun p => hmaps _ (hfix p).2)
      hC hCt (fun p => (hfix p).2),
    fun _ _ => ⟨rfl, rfl⟩,
    fun p => ⟨e.conjugateMap_eqOn_compl (hfix p).1,
      e.conjugateMap_eqOn_compl (hfix p).2⟩⟩

end OpenPartialHomeomorph

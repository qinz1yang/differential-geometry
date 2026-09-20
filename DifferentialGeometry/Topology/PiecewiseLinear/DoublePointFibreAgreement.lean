/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

/-!
# Double points under fibre agreement off a set

The general position producers of the tree perturb a map only over a prescribed set `V`
and record the effect as an equality of fibres, `∀ z ∉ V, g ⁻¹' {z} = f ⁻¹' {z}`, rather
than as an agreement of the two maps.  This file records what that clause buys for the
double point set, in the shape a finite cover normalisation consumes.

* `doublePointSet_sdiff_eq_of_inter_preimage_singleton_eq_off` is the statement under the
  weakest hypothesis: only the parts of the fibres lying in the source set `P` have to
  agree, because `doublePointSet f P` reads the values of `f` on `P` alone.
* `doublePointSet_sdiff_eq_of_preimage_singleton_eq_off` is the specialisation to the full
  preimage equality that the producers deliver.
* `preimage_singleton_eq_off_iff` identifies that clause with the conjunction of two
  conditions on the maps: `g` agrees with `f` wherever the `f` image avoids `V`, and the
  `g` image stays inside `V` wherever the `f` image is inside `V`.  The second condition is
  not a consequence of the first, and the equality of fibres needs both.
* `doublePointSet_subset_of_preimage_singleton_eq_off` is the step a cover induction uses:
  a perturbation localised in `V` cannot push a double point outside a set containing both
  the old double point set and `V`.

No smallness of the perturbation and no injectivity scale enters anywhere; the equality of
fibres alone carries all four statements.
-/

namespace DifferentialGeometry.Topology.PiecewiseLinear

/-- **Double points away from `V` are unchanged by a perturbation whose fibres inside the
source set agree off `V`.**  This is the weakest hypothesis giving the conclusion, since
`doublePointSet f P` only reads the values of `f` on `P`. -/
theorem doublePointSet_sdiff_eq_of_inter_preimage_singleton_eq_off {X Y : Type*}
    {f g : X → Y} {P : Set X} {V : Set Y}
    (h : ∀ z ∉ V, P ∩ g ⁻¹' {z} = P ∩ f ⁻¹' {z}) :
    doublePointSet g P \ V = doublePointSet f P \ V := by
  have key : ∀ u v : X → Y, (∀ z ∉ V, P ∩ u ⁻¹' {z} = P ∩ v ⁻¹' {z}) →
      doublePointSet u P \ V ⊆ doublePointSet v P \ V := by
    rintro u v huv y ⟨⟨a, ha, b, hb, hab, hau, hbu⟩, hyV⟩
    have hfibre : ∀ x ∈ P, u x = y → v x = y := by
      intro x hx hxy
      have hx' : x ∈ P ∩ u ⁻¹' {y} :=
        ⟨hx, Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hxy)⟩
      rw [huv y hyV] at hx'
      exact Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx'.2)
    exact ⟨⟨a, ha, b, hb, hab, hfibre a ha hau, hfibre b hb hbu⟩, hyV⟩
  exact Set.Subset.antisymm (key g f h) (key f g (fun z hz => (h z hz).symm))

/-- **Double points away from `V` are unchanged by a perturbation whose fibres agree off
`V`.**  This is the form the general position producers of the tree deliver, comparing the
fibres as subsets of the whole source type. -/
theorem doublePointSet_sdiff_eq_of_preimage_singleton_eq_off {X Y : Type*} {f g : X → Y}
    (P : Set X) {V : Set Y} (h : ∀ z ∉ V, g ⁻¹' {z} = f ⁻¹' {z}) :
    doublePointSet g P \ V = doublePointSet f P \ V :=
  doublePointSet_sdiff_eq_of_inter_preimage_singleton_eq_off (fun z hz => by rw [h z hz])

/-- **Fibre agreement off `V`, unpacked into two conditions on the maps.**  Equality of the
fibres over every point outside `V` holds exactly when `g` agrees with `f` at every source
point whose `f` image avoids `V`, and the `g` image of a source point lies in `V` whenever
its `f` image does.  The second condition is not implied by the first. -/
theorem preimage_singleton_eq_off_iff {X Y : Type*} {f g : X → Y} {V : Set Y} :
    (∀ z ∉ V, g ⁻¹' {z} = f ⁻¹' {z}) ↔
      (∀ x, f x ∉ V → g x = f x) ∧ ∀ x, f x ∈ V → g x ∈ V := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have hmem : x ∈ f ⁻¹' {f x} := Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr rfl)
      rw [← h (f x) hx] at hmem
      exact Set.mem_singleton_iff.mp (Set.mem_preimage.mp hmem)
    · by_contra hgx
      have hmem : x ∈ g ⁻¹' {g x} := Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr rfl)
      rw [h (g x) hgx] at hmem
      have hfg : f x = g x := Set.mem_singleton_iff.mp (Set.mem_preimage.mp hmem)
      exact hgx (hfg ▸ hx)
  · rintro ⟨hone, htwo⟩ z hz
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hgx
      have hfx : f x ∉ V := fun hf => hz (hgx ▸ htwo x hf)
      exact (hone x hfx).symm.trans hgx
    · intro hfx
      have hfV : f x ∉ V := fun hf => hz (hfx ▸ hf)
      exact (hone x hfV).trans hfx

/-- **A perturbation localised in `V` keeps the double point set inside any set containing
both the old double point set and `V`.**  This is the clause that makes the invariant of a
finite cover normalisation reproduce itself from one step to the next. -/
theorem doublePointSet_subset_of_preimage_singleton_eq_off {X Y : Type*} {f g : X → Y}
    (P : Set X) {U V : Set Y} (h : ∀ z ∉ V, g ⁻¹' {z} = f ⁻¹' {z})
    (hf : doublePointSet f P ⊆ U) (hVU : V ⊆ U) : doublePointSet g P ⊆ U := by
  intro y hy
  by_cases hyV : y ∈ V
  · exact hVU hyV
  · have hmem : y ∈ doublePointSet g P \ V := ⟨hy, hyV⟩
    rw [doublePointSet_sdiff_eq_of_preimage_singleton_eq_off P h] at hmem
    exact hf hmem.1

end DifferentialGeometry.Topology.PiecewiseLinear

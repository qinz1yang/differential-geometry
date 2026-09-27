/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ModelSlideLong
import DifferentialGeometry.Topology.PiecewiseLinear.ChartConjugate

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]

theorem isPiecewiseAffineOn_chartSlideLong {d R : ℝ} (hd : 0 ≤ d)
    (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    (hsub : slideSupportLong R ⊆ e.target) :
    IsPiecewiseAffineOn (e.conjugateMap (slideMapLong d R)) univ :=
  isPiecewiseAffineOn_conjugateMap e he hei
    (isPiecewiseAffineOn_slideMapLong.mono e.open_target (subset_univ _))
    (mapsTo_slideMapLong_of_subset hd hsub) (isCompact_slideSupportLong R) hsub
    (eqOn_slideMapLong_id_compl hd)

omit [NormedSpace ℝ M] [FiniteDimensional ℝ M] in
theorem injective_chartSlideLong {d R : ℝ} (hd : 0 ≤ d)
    (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)) (hsub : slideSupportLong R ⊆ e.target) :
    Function.Injective (e.conjugateMap (slideMapLong d R)) := by
  have hmaps := mapsTo_slideMapLong_of_subset (d := d) hd hsub
  intro x y hxy
  by_cases hx : x ∈ e.source
  · by_cases hy : y ∈ e.source
    · rw [e.conjugateMap_of_mem _ hx, e.conjugateMap_of_mem _ hy] at hxy
      have h1 : slideMapLong d R (e x) ∈ e.target := hmaps (e.map_source hx)
      have h2 : slideMapLong d R (e y) ∈ e.target := hmaps (e.map_source hy)
      have hslide : slideMapLong d R (e x) = slideMapLong d R (e y) := by
        have := congrArg e hxy
        rwa [e.right_inv h1, e.right_inv h2] at this
      have hex : e x = e y := injective_slideMapLong hslide
      have := congrArg e.symm hex
      rwa [e.left_inv hx, e.left_inv hy] at this
    · rw [e.conjugateMap_of_mem _ hx, e.conjugateMap_of_notMem _ hy] at hxy
      exact absurd (hxy ▸ e.map_target (hmaps (e.map_source hx))) hy
  · by_cases hy : y ∈ e.source
    · rw [e.conjugateMap_of_notMem _ hx, e.conjugateMap_of_mem _ hy] at hxy
      exact absurd (hxy.symm ▸ e.map_target (hmaps (e.map_source hy))) hx
    · rwa [e.conjugateMap_of_notMem _ hx, e.conjugateMap_of_notMem _ hy] at hxy

omit [NormedSpace ℝ M] [FiniteDimensional ℝ M] in
theorem disjoint_chartSlideLong_image {d R a b c : ℝ} (hd : 0 ≤ d) (hR : c + 2 * d ≤ R)
    (hca : c - d < a) (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ))
    (hsub : slideSupportLong R ⊆ e.target) (hA : slideBandA c ⊆ e.target)
    (hQ : slideBandQ a b ⊆ e.target) :
    Disjoint (e.conjugateMap (slideMapLong d R) '' (e.symm '' slideBandA c))
      (e.symm '' slideBandQ a b) := by
  have hmaps := mapsTo_slideMapLong_of_subset (d := d) hd hsub
  rw [Set.disjoint_left]
  rintro w ⟨u, ⟨p, hp, rfl⟩, rfl⟩ ⟨q, hq, hqe⟩
  have hps : e.symm p ∈ e.source := e.map_target (hA hp)
  have hval : e.conjugateMap (slideMapLong d R) (e.symm p) = e.symm (slideMapLong d R p) := by
    rw [e.conjugateMap_of_mem _ hps, e.right_inv (hA hp)]
  rw [hval] at hqe
  have h1 : slideMapLong d R p ∈ e.target := hmaps (hA hp)
  have hpq : slideMapLong d R p = q := by
    have hcong := congrArg e hqe
    rw [e.right_inv h1, e.right_inv (hQ hq)] at hcong
    exact hcong.symm
  exact Set.disjoint_left.mp (disjoint_slideMapLong_image_slideBandA (b := b) hd hR hca)
    ⟨p, hp, rfl⟩ (hpq ▸ hq)

end DifferentialGeometry.Topology.PiecewiseLinear

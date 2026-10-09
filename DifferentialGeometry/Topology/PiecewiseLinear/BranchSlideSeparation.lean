/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartSlideLong

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

structure IsBranchSlideChart (R c a b : ℝ) (P Q : Set M)
    (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)) : Prop where
  isPiecewiseAffineOn_chart : IsPiecewiseAffineOn e e.source
  isPiecewiseAffineOn_symm : IsPiecewiseAffineOn e.symm e.target
  slideSupportLong_subset : slideSupportLong R ⊆ e.target
  slideBandA_subset : slideBandA c ⊆ e.target
  slideBandQ_subset : slideBandQ a b ⊆ e.target
  sheet_eq : P = e.symm '' slideBandA c
  crossing_eq : Q = e.symm '' slideBandQ a b

def HasBranchSlideChart (R c a b : ℝ) (P Q : Set M) : Prop :=
  ∃ e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ), IsBranchSlideChart R c a b P Q e

omit [NormedSpace ℝ M] in
theorem isCompact_symm_image_slideSupportLong {R : ℝ}
    {e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)} (hsub : slideSupportLong R ⊆ e.target) :
    IsCompact (e.symm '' slideSupportLong R) :=
  (isCompact_slideSupportLong R).image_of_continuousOn (e.continuousOn_symm.mono hsub)

omit [NormedSpace ℝ M] in
theorem symm_image_subset_source {T : Set (ℝ × ℝ × ℝ)}
    {e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)} (hsub : T ⊆ e.target) :
    e.symm '' T ⊆ e.source := by
  rintro x ⟨p, hp, rfl⟩
  exact e.map_target (hsub hp)

namespace IsBranchSlideChart

variable {R c a b : ℝ} {P Q : Set M} {e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)}

theorem sheet_subset_source (h : IsBranchSlideChart R c a b P Q e) : P ⊆ e.source := by
  rw [h.sheet_eq]
  exact symm_image_subset_source h.slideBandA_subset

theorem crossing_subset_source (h : IsBranchSlideChart R c a b P Q e) : Q ⊆ e.source := by
  rw [h.crossing_eq]
  exact symm_image_subset_source h.slideBandQ_subset

theorem support_subset_source (h : IsBranchSlideChart R c a b P Q e) :
    e.symm '' slideSupportLong R ⊆ e.source :=
  symm_image_subset_source h.slideSupportLong_subset

theorem isCompact_support (h : IsBranchSlideChart R c a b P Q e) :
    IsCompact (e.symm '' slideSupportLong R) :=
  isCompact_symm_image_slideSupportLong h.slideSupportLong_subset

end IsBranchSlideChart

omit [NormedSpace ℝ M] in
theorem eqOn_chartSlideLong_id_compl {d R : ℝ} (hd : 0 ≤ d)
    (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)) :
    EqOn (e.conjugateMap (slideMapLong d R)) id (e.symm '' slideSupportLong R)ᶜ :=
  e.conjugateMap_eqOn_compl (eqOn_slideMapLong_id_compl hd)

omit [NormedSpace ℝ M] in
theorem mapsTo_chartSlideLong_of_forall_mem_iff {d R : ℝ} (hd : 0 ≤ d)
    (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)) (hsub : slideSupportLong R ⊆ e.target)
    {T : Set (ℝ × ℝ)} {B : Set M} (hB : ∀ x ∈ e.source, x ∈ B ↔ (e x).2 ∈ T) :
    MapsTo (e.conjugateMap (slideMapLong d R)) B B := by
  intro x hx
  by_cases hxs : x ∈ e.source
  · rw [e.conjugateMap_of_mem _ hxs]
    have hmem : slideMapLong d R (e x) ∈ e.target :=
      mapsTo_slideMapLong_of_subset hd hsub (e.map_source hxs)
    refine (hB _ (e.map_target hmem)).mpr ?_
    rw [e.right_inv hmem]
    exact mapsTo_slideMapLong_prod (d := d) (R := R) T ((hB x hxs).mp hx)
  · rw [e.conjugateMap_of_notMem _ hxs]
    exact hx

omit [NormedSpace ℝ M] in
theorem mapsTo_chartSlideLong_boundary {d R : ℝ} (hd : 0 ≤ d)
    (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)) (hsub : slideSupportLong R ⊆ e.target)
    {B : Set M} (hB : ∀ x ∈ e.source, x ∈ B ↔ (e x).2.2 = 0) :
    MapsTo (e.conjugateMap (slideMapLong d R)) B B :=
  mapsTo_chartSlideLong_of_forall_mem_iff hd e hsub (T := {q : ℝ × ℝ | q.2 = 0}) hB

omit [NormedSpace ℝ M] in
theorem mapsTo_chartSlideLong_halfSpace {d R : ℝ} (hd : 0 ≤ d)
    (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)) (hsub : slideSupportLong R ⊆ e.target)
    {N : Set M} (hN : ∀ x ∈ e.source, x ∈ N ↔ 0 ≤ (e x).2.2) :
    MapsTo (e.conjugateMap (slideMapLong d R)) N N :=
  mapsTo_chartSlideLong_of_forall_mem_iff hd e hsub (T := {q : ℝ × ℝ | 0 ≤ q.2}) hN

variable [FiniteDimensional ℝ M]

theorem exists_supported_separation_of_isBranchSlideChart {R c a b d : ℝ} {P Q : Set M}
    {e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)} (hchart : IsBranchSlideChart R c a b P Q e)
    (hd : 0 ≤ d) (hR : c + 2 * d ≤ R) (hca : c - d < a) :
    ∃ h : M → M, IsPiecewiseAffineOn h univ ∧ Function.Injective h ∧
      EqOn h id (e.symm '' slideSupportLong R)ᶜ ∧ Disjoint (h '' P) Q := by
  refine ⟨e.conjugateMap (slideMapLong d R), isPiecewiseAffineOn_chartSlideLong hd e
    hchart.isPiecewiseAffineOn_chart hchart.isPiecewiseAffineOn_symm
    hchart.slideSupportLong_subset, injective_chartSlideLong hd e hchart.slideSupportLong_subset,
    eqOn_chartSlideLong_id_compl hd e, ?_⟩
  rw [hchart.sheet_eq, hchart.crossing_eq]
  exact disjoint_chartSlideLong_image hd hR hca e hchart.slideSupportLong_subset
    hchart.slideBandA_subset hchart.slideBandQ_subset

theorem exists_supported_separation_of_isBranchSlideChart_boundary {R c a b d : ℝ}
    {P Q B : Set M} {e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)}
    (hchart : IsBranchSlideChart R c a b P Q e) (hd : 0 ≤ d) (hR : c + 2 * d ≤ R)
    (hca : c - d < a) (hB : ∀ x ∈ e.source, x ∈ B ↔ (e x).2.2 = 0) :
    ∃ h : M → M, IsPiecewiseAffineOn h univ ∧ Function.Injective h ∧
      EqOn h id (e.symm '' slideSupportLong R)ᶜ ∧ Disjoint (h '' P) Q ∧
      h '' (e.symm '' slideSupportLong R ∩ B) ⊆ B := by
  have hmaps := mapsTo_chartSlideLong_boundary (d := d) hd e hchart.slideSupportLong_subset hB
  refine ⟨e.conjugateMap (slideMapLong d R), isPiecewiseAffineOn_chartSlideLong hd e
    hchart.isPiecewiseAffineOn_chart hchart.isPiecewiseAffineOn_symm
    hchart.slideSupportLong_subset, injective_chartSlideLong hd e hchart.slideSupportLong_subset,
    eqOn_chartSlideLong_id_compl hd e, ?_, ?_⟩
  · rw [hchart.sheet_eq, hchart.crossing_eq]
    exact disjoint_chartSlideLong_image hd hR hca e hchart.slideSupportLong_subset
      hchart.slideBandA_subset hchart.slideBandQ_subset
  · rintro y ⟨x, hx, rfl⟩
    exact hmaps hx.2

end DifferentialGeometry.Topology.PiecewiseLinear

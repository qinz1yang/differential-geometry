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

end DifferentialGeometry.Topology.PiecewiseLinear

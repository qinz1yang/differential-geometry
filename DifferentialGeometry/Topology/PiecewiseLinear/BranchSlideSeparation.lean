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

end DifferentialGeometry.Topology.PiecewiseLinear

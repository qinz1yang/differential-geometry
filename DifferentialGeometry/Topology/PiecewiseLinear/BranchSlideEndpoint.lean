import DifferentialGeometry.Topology.PiecewiseLinear.BranchSlideSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.ModelSlideFwd

open Set Topology

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem mapsTo_conjugateMap (e : _root_.OpenPartialHomeomorph X Y) {k : Y → Y}
    (hmap : MapsTo k e.target e.target) {A : Set X} {B : Set Y}
    (hcoord : ∀ x ∈ e.source, x ∈ A ↔ e x ∈ B) (hB : MapsTo k (e.target ∩ B) B) :
    MapsTo (e.conjugateMap k) A A := by
  intro x hx
  by_cases hxs : x ∈ e.source
  · rw [e.conjugateMap_of_mem _ hxs]
    have hmem : k (e x) ∈ e.target := hmap (e.map_source hxs)
    refine (hcoord _ (e.map_target hmem)).mpr ?_
    rw [e.right_inv hmem]
    exact hB ⟨e.map_source hxs, (hcoord x hxs).mp hx⟩
  · rw [e.conjugateMap_of_notMem _ hxs]
    exact hx

end OpenPartialHomeomorph

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Topological

variable {X : Type*} [TopologicalSpace X]

theorem injective_chartSlideFwd {d R : ℝ} (hd : 0 ≤ d)
    (e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)) (hsub : slideSupportLong R ⊆ e.target) :
    Function.Injective (e.conjugateMap (slideMapFwd d R)) := by
  have hmaps := mapsTo_slideMapFwd_of_subset (d := d) hd hsub
  intro x y hxy
  by_cases hx : x ∈ e.source
  · by_cases hy : y ∈ e.source
    · rw [e.conjugateMap_of_mem _ hx, e.conjugateMap_of_mem _ hy] at hxy
      have h1 : slideMapFwd d R (e x) ∈ e.target := hmaps (e.map_source hx)
      have h2 : slideMapFwd d R (e y) ∈ e.target := hmaps (e.map_source hy)
      have hslide : slideMapFwd d R (e x) = slideMapFwd d R (e y) := by
        have hc := congrArg e hxy
        rwa [e.right_inv h1, e.right_inv h2] at hc
      have hex : e x = e y := injective_slideMapFwd hslide
      have hs := congrArg e.symm hex
      rwa [e.left_inv hx, e.left_inv hy] at hs
    · rw [e.conjugateMap_of_mem _ hx, e.conjugateMap_of_notMem _ hy] at hxy
      exact absurd (hxy ▸ e.map_target (hmaps (e.map_source hx))) hy
  · by_cases hy : y ∈ e.source
    · rw [e.conjugateMap_of_notMem _ hx, e.conjugateMap_of_mem _ hy] at hxy
      exact absurd (hxy.symm ▸ e.map_target (hmaps (e.map_source hy))) hx
    · rwa [e.conjugateMap_of_notMem _ hx, e.conjugateMap_of_notMem _ hy] at hxy

theorem eqOn_chartSlideFwd_id_compl {d R : ℝ} (hd : 0 ≤ d)
    (e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)) :
    EqOn (e.conjugateMap (slideMapFwd d R)) id (e.symm '' slideSupportLong R)ᶜ :=
  e.conjugateMap_eqOn_compl (eqOn_slideMapFwd_id_compl hd)

theorem disjoint_chartSlideFwd_image {d R a b c : ℝ} (hd : 0 ≤ d) (hR : c + 2 * d ≤ R)
    (hb : b < d) (e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ))
    (hsub : slideSupportLong R ⊆ e.target) (hA : slideBandA c ⊆ e.target)
    (hQ : slideBandQ a b ⊆ e.target) :
    Disjoint (e.conjugateMap (slideMapFwd d R) '' (e.symm '' slideBandA c))
      (e.symm '' slideBandQ a b) := by
  have hmaps := mapsTo_slideMapFwd_of_subset (d := d) hd hsub
  rw [Set.disjoint_left]
  rintro w ⟨u, ⟨p, hp, rfl⟩, rfl⟩ ⟨q, hq, hqe⟩
  have hps : e.symm p ∈ e.source := e.map_target (hA hp)
  have hval : e.conjugateMap (slideMapFwd d R) (e.symm p) = e.symm (slideMapFwd d R p) := by
    rw [e.conjugateMap_of_mem _ hps, e.right_inv (hA hp)]
  rw [hval] at hqe
  have h1 : slideMapFwd d R p ∈ e.target := hmaps (hA hp)
  have hpq : slideMapFwd d R p = q := by
    have hcong := congrArg e hqe
    rw [e.right_inv h1, e.right_inv (hQ hq)] at hcong
    exact hcong.symm
  exact Set.disjoint_left.mp (disjoint_slideMapFwd_image_slideBandA (a := a) hd hR hb)
    ⟨p, hp, rfl⟩ (hpq ▸ hq)

theorem mapsTo_chartSlideFwd_of_forall_mem_iff {d R : ℝ} (hd : 0 ≤ d)
    (e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)) (hsub : slideSupportLong R ⊆ e.target)
    {T : Set (ℝ × ℝ)} {B : Set X} (hB : ∀ x ∈ e.source, x ∈ B ↔ (e x).2 ∈ T) :
    MapsTo (e.conjugateMap (slideMapFwd d R)) B B :=
  e.mapsTo_conjugateMap (B := {p : ℝ × ℝ × ℝ | p.2 ∈ T})
    (mapsTo_slideMapFwd_of_subset hd hsub) hB
    fun _ hp => mapsTo_slideMapFwd_prod (d := d) (R := R) T hp.2

theorem mapsTo_chartSlideFwd_halfSpace {d R : ℝ} (hd : 0 ≤ d)
    (e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)) (hsub : slideSupportLong R ⊆ e.target)
    {N : Set X} (hN : ∀ x ∈ e.source, x ∈ N ↔ 0 ≤ (e x).1) :
    MapsTo (e.conjugateMap (slideMapFwd d R)) N N :=
  e.mapsTo_conjugateMap (B := slideEndpointHalfSpace)
    (mapsTo_slideMapFwd_of_subset hd hsub) hN
    fun _ hp => mapsTo_slideMapFwd_slideEndpointHalfSpace (d := d) (R := R) hp.2

theorem not_mapsTo_chartSlideFwd_boundaryPlane {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)) (hsub : slideSupportLong R ⊆ e.target)
    {B : Set X} (hB : ∀ x ∈ e.source, x ∈ B ↔ (e x).1 = 0) :
    ¬MapsTo (e.conjugateMap (slideMapFwd d R)) B B := by
  intro hmapsB
  have h0 : ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ slideSupportLong R := by
    refine ⟨?_, ?_⟩
    · change |(0 : ℝ)| + |(0 : ℝ)| ≤ 1
      rw [abs_zero]
      norm_num
    · change |(0 : ℝ)| ≤ R
      rw [abs_zero]
      exact hR.le
  have h0t : ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ e.target := hsub h0
  have hxs : e.symm ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ e.source := e.map_target h0t
  have hex : e (e.symm ((0 : ℝ), (0 : ℝ), (0 : ℝ))) = ((0 : ℝ), (0 : ℝ), (0 : ℝ)) :=
    e.right_inv h0t
  have hxB : e.symm ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ B := by
    refine (hB _ hxs).mpr ?_
    rw [hex]
  have himg := hmapsB hxB
  rw [e.conjugateMap_of_mem _ hxs, hex] at himg
  have hmem : slideMapFwd d R ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ e.target :=
    mapsTo_slideMapFwd_of_subset hd.le hsub h0t
  have hval := (hB _ (e.map_target hmem)).mp himg
  rw [e.right_inv hmem, slideMapFwd_fst] at hval
  have ha : slideAmountLong d R ((0 : ℝ), (0 : ℝ), (0 : ℝ)) = 0 := by
    have hz : ((0 : ℝ), (0 : ℝ), (0 : ℝ)).1 = 0 := rfl
    rw [hz] at hval
    linarith
  have hw := (slideAmountLong_eq_zero_iff_of_fst_eq_zero (d := d) (R := R)
    (p := ((0 : ℝ), (0 : ℝ), (0 : ℝ))) hd hR rfl).mp ha
  norm_num at hw

end Topological

section Normed

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]

theorem isPiecewiseAffineOn_chartSlideFwd {d R : ℝ} (hd : 0 ≤ d)
    (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    (hsub : slideSupportLong R ⊆ e.target) :
    IsPiecewiseAffineOn (e.conjugateMap (slideMapFwd d R)) univ :=
  isPiecewiseAffineOn_conjugateMap e he hei
    (isPiecewiseAffineOn_slideMapFwd.mono e.open_target (subset_univ _))
    (mapsTo_slideMapFwd_of_subset hd hsub) (isCompact_slideSupportLong R) hsub
    (eqOn_slideMapFwd_id_compl hd)

theorem exists_supported_separation_of_isBranchSlideChart_endpoint {R c a b d : ℝ}
    {P Q N : Set M} {e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)}
    (hchart : IsBranchSlideChart R c a b P Q e) (hd : 0 ≤ d) (hR : c + 2 * d ≤ R) (hb : b < d)
    (hN : ∀ x ∈ e.source, x ∈ N ↔ 0 ≤ (e x).1) :
    ∃ h : M → M, IsPiecewiseAffineOn h univ ∧ Function.Injective h ∧
      EqOn h id (e.symm '' slideSupportLong R)ᶜ ∧ Disjoint (h '' P) Q ∧ MapsTo h N N := by
  refine ⟨e.conjugateMap (slideMapFwd d R), isPiecewiseAffineOn_chartSlideFwd hd e
    hchart.isPiecewiseAffineOn_chart hchart.isPiecewiseAffineOn_symm
    hchart.slideSupportLong_subset, injective_chartSlideFwd hd e hchart.slideSupportLong_subset,
    eqOn_chartSlideFwd_id_compl hd e, ?_,
    mapsTo_chartSlideFwd_halfSpace hd e hchart.slideSupportLong_subset hN⟩
  rw [hchart.sheet_eq, hchart.crossing_eq]
  exact disjoint_chartSlideFwd_image hd hR hb e hchart.slideSupportLong_subset
    hchart.slideBandA_subset hchart.slideBandQ_subset

omit [FiniteDimensional ℝ M] in
theorem not_mapsTo_boundary_of_isBranchSlideChart_endpoint {R c a b d : ℝ} {P Q B : Set M}
    {e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)} (hchart : IsBranchSlideChart R c a b P Q e)
    (hd : 0 < d) (hR : 0 < R) (hB : ∀ x ∈ e.source, x ∈ B ↔ (e x).1 = 0) :
    ¬MapsTo (e.conjugateMap (slideMapFwd d R)) B B :=
  not_mapsTo_chartSlideFwd_boundaryPlane hd hR e hchart.slideSupportLong_subset hB

end Normed

end DifferentialGeometry.Topology.PiecewiseLinear

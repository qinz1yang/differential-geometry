/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.CrossSections

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.AxialThinCompactness

open Hyperbolic HyperbolicAction HyperbolicBoundary HyperbolicFaithful
open HyperbolicConvexity AxisGeometry BoundaryStabilizer
open OrbifoldStrata ElementaryEnds OrbifoldThinRegions CuspCrossSections

variable {n : ℕ}

theorem axisFoot_normal_geod (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (y : HUpper n) (hy : axisFoot ξ η hne y ≠ y) (t : ℝ) :
    axisFoot ξ η hne (geodFromTo (axisFoot ξ η hne y) y hy t) = axisFoot ξ η hne y := by
  apply Eq.symm
  apply eq_axisFoot_of_dist_le ξ η hne _ _ (axisFoot_mem ξ η hne y)
  apply (Real.cosh_strictMonoOn.le_iff_le dist_nonneg dist_nonneg).mp
  rw [cosh_dist_normal_geod ξ η hne y hy _ (axisFoot_mem ξ η hne y),
    cosh_dist_normal_geod ξ η hne y hy _ (axisFoot_mem ξ η hne _),
    dist_self, Real.cosh_zero, mul_one]
  exact le_mul_of_one_le_right (Real.cosh_pos _).le (Real.one_le_cosh _)

theorem dist_normal_axisFoot (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (y : HUpper n) (hy : axisFoot ξ η hne y ≠ y) (t : ℝ) :
    dist (geodFromTo (axisFoot ξ η hne y) y hy t)
      (axisFoot ξ η hne (geodFromTo (axisFoot ξ η hne y) y hy t)) = |t| := by
  rw [axisFoot_normal_geod]
  simpa only [geodFromTo_zero, sub_zero] using dist_geodFromTo hy t 0

theorem exists_frontier_ge_of_eventually_notMem
    {X : Type*} [TopologicalSpace X] {Z : Set X} (hZ : IsClosed Z)
    {q : ℝ → X} (hq : Continuous q) {s : ℝ} (hs : q s ∈ Z)
    (hexit : ∀ᶠ t : ℝ in atTop, q t ∉ Z) :
    ∃ t : ℝ, s ≤ t ∧ q t ∈ frontier Z := by
  let A : Set ℝ := q ⁻¹' Z ∩ Ici s
  have hA : IsClosed A := (hZ.preimage hq).inter isClosed_Ici
  have hAne : A.Nonempty := ⟨s, hs, by simp⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hexit
  have hAb : BddAbove A := ⟨T, fun t ht =>
    le_of_not_ge (fun h => hT t h ht.1)⟩
  let t := sSup A
  have htA : t ∈ A := hA.csSup_mem hAne hAb
  refine ⟨t, htA.2, subset_closure htA.1, ?_⟩
  intro hint
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp
    (hq.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint))
  have htd : t + d / 2 ∈ Metric.ball t d := by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hd)]
    linarith
  have hqt : q (t + d / 2) ∈ Z :=
    interior_subset (show q (t + d / 2) ∈ interior Z from hball htd)
  have hst : s ≤ t := htA.2
  have hm : t + d / 2 ∈ A :=
    ⟨hqt, by change s ≤ t + d / 2; linarith⟩
  have hle : t + d / 2 ≤ t := le_csSup hAb hm
  linarith

theorem pair_of_image_eq (hn : 1 ≤ n) (g : PO n 1) (ξ η : BoundaryH n)
    (he : (fun ζ : BoundaryH n => (poBoundaryMulAction hn).smul g ζ) '' {ξ, η} = {ξ, η}) :
    (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n)) :=
  ⟨he ▸ mem_image_of_mem _ (mem_insert ξ {η}),
    he ▸ mem_image_of_mem _ (mem_insert_of_mem ξ (mem_singleton η))⟩

theorem exists_frontier_on_normal (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {r : ℝ} (hr : 0 ≤ r)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (closedSmallSubgroup hn Γ r x))
    (ξ η : BoundaryH n) (hne : ξ ≠ η) {y : HUpper n}
    (hyT : y ∈ thinRegion hn Γ r {ξ, η}) (hy : axisFoot ξ η hne y ≠ y) :
    ∃ t : ℝ, dist (axisFoot ξ η hne y) y ≤ t ∧
      geodFromTo (axisFoot ξ η hne y) y hy t ∈ frontier (thinRegion hn Γ r {ξ, η}) := by
  let P := endStabilizer hn Γ {ξ, η}
  have hpair (g : P) :
      (poBoundaryMulAction hn).smul (g : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul (g : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n)) :=
    pair_of_image_eq hn g ξ η ((mem_setStabilizer hn _ _).mp g.property.2)
  have he := thinRegion_eq_stabilizer_infiniteLocus hn Γ hΓ r hgeom ⟨y, hyT⟩
  have hfinite := ElementaryThickPoint.eventually_finite_axial hn P
    (hΓ.mono inf_le_left) hr ξ η hne hpair y hy
  have hexit : ∀ᶠ t : ℝ in atTop,
      geodFromTo (axisFoot ξ η hne y) y hy t ∉ thinRegion hn Γ r {ξ, η} := by
    filter_upwards [hfinite] with t ht
    rw [he]
    exact fun h => h ht
  exact exists_frontier_ge_of_eventually_notMem
    (isClosed_thinRegion hn Γ hΓ r hgeom {ξ, η}) (continuous_geodFromTo (hd := hy))
      (by simpa only [geodFromTo_dist] using hyT) hexit

theorem exists_frontier_dist_le_of_off_axis (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {r : ℝ} (hr : 0 ≤ r)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (closedSmallSubgroup hn Γ r x))
    (ξ η : BoundaryH n) (hne : ξ ≠ η) (B : ℝ)
    (hB : ∀ q ∈ frontier (thinRegion hn Γ r {ξ, η}), dist q (axisFoot ξ η hne q) ≤ B)
    {y : HUpper n} (hyT : y ∈ thinRegion hn Γ r {ξ, η}) (hy : axisFoot ξ η hne y ≠ y) :
    ∃ q ∈ frontier (thinRegion hn Γ r {ξ, η}), dist y q ≤ B := by
  obtain ⟨t, ht, hq⟩ := exists_frontier_on_normal hn Γ hΓ hr hgeom ξ η hne hyT hy
  have ht0 : 0 ≤ t := dist_nonneg.trans ht
  have hrad := hB _ hq
  rw [dist_normal_axisFoot, abs_of_nonneg ht0] at hrad
  refine ⟨_, hq, ?_⟩
  have hd := dist_geodFromTo hy (dist (axisFoot ξ η hne y) y) t
  rw [geodFromTo_dist, abs_of_nonpos (sub_nonpos.mpr ht)] at hd
  linarith [dist_nonneg (x := axisFoot ξ η hne y) (y := y)]

theorem exists_frontier_dist_le (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {r : ℝ} (hr : 0 ≤ r)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (closedSmallSubgroup hn Γ r x))
    (ξ η : BoundaryH n) (hne : ξ ≠ η) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ q ∈ frontier (thinRegion hn Γ r {ξ, η}), dist q (axisFoot ξ η hne q) ≤ B)
    {y : HUpper n} (hyT : y ∈ thinRegion hn Γ r {ξ, η}) :
    ∃ q ∈ frontier (thinRegion hn Γ r {ξ, η}), dist y q ≤ B + 1 := by
  by_cases hyint : y ∈ interior (thinRegion hn Γ r {ξ, η})
  · have hdense : Dense (axis ξ η)ᶜ :=
      interior_eq_empty_iff_dense_compl.mp (StratumMaximum.interior_axis_eq_empty hdim ξ η)
    obtain ⟨z, hz, hzaxis⟩ := mem_closure_iff_nhds.mp (hdense y) _
      (inter_mem (mem_interior_iff_mem_nhds.mp hyint) (Metric.ball_mem_nhds y zero_lt_one))
    have hzT : z ∈ thinRegion hn Γ r {ξ, η} := hz.1
    have hzoff : axisFoot ξ η hne z ≠ z := fun he => hzaxis (he ▸ axisFoot_mem ξ η hne z)
    obtain ⟨q, hq, hd⟩ := exists_frontier_dist_le_of_off_axis hn Γ hΓ hr hgeom ξ η hne B hB hzT hzoff
    refine ⟨q, hq, ?_⟩
    have hzy : dist z y < 1 := hz.2
    have htri := dist_triangle y z q
    rw [dist_comm y z] at htri
    linarith
  · exact ⟨y, ⟨subset_closure hyT, hyint⟩,
      by simpa only [dist_self] using (by linarith : 0 ≤ B + 1)⟩

theorem exists_compact_axial_core (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    (ξ η : BoundaryH n) (hne : ξ ≠ η) :
    ∃ C : Set (HUpper n), IsCompact C ∧ C ⊆ thinRegion hn Γ r {ξ, η} ∧
      ∀ p ∈ thinRegion hn Γ r {ξ, η}, ∃ γ : Γ,
        (fun ζ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ζ) '' {ξ, η} = {ξ, η} ∧
        (poMulAction hn).smul (γ : PO n 1) p ∈ C := by
  have hcgeom (x : HUpper n) := closedSmallSubgroup_geometry hn Γ hre x (hgeom x)
  obtain ⟨K, hK, _, hcover⟩ := exists_compact_frontier_core hn hdim Γ hΓ hcov hr hre hgeom {ξ, η}
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    (continuous_id.dist (continuous_axisFoot ξ η hne)).continuousOn
  have hBfull (q : HUpper n) (hq : q ∈ frontier (thinRegion hn Γ r {ξ, η})) :
      dist q (axisFoot ξ η hne q) ≤ max 0 B := by
    obtain ⟨γ, hlabel, hγK⟩ := hcover q hq
    have hb : dist ((poMulAction hn).smul (γ : PO n 1) q)
        (axisFoot ξ η hne ((poMulAction hn).smul (γ : PO n 1) q)) ≤ B :=
      hB (mem_image_of_mem _ hγK)
    have he := axisFoot_smul hn (γ : PO n 1) ξ η hne (pair_of_image_eq hn γ ξ η hlabel) q
    rw [he] at hb
    have hd : dist ((poMulAction hn).smul (γ : PO n 1) q)
        ((poMulAction hn).smul (γ : PO n 1) (axisFoot ξ η hne q)) = dist q (axisFoot ξ η hne q) :=
      po_dist_smul hn γ q (axisFoot ξ η hne q)
    rw [hd] at hb
    exact hb.trans (le_max_right _ _)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (basepointH : HUpper n)
  let C := Metric.closedBall (basepointH : HUpper n) (R + max 0 B + 1) ∩ thinRegion hn Γ r {ξ, η}
  refine ⟨C, (isCompact_closedBall _ _).inter_right
    (isClosed_thinRegion hn Γ hΓ r hcgeom {ξ, η}), inter_subset_right, ?_⟩
  intro p hp
  obtain ⟨q, hq, hpq⟩ := exists_frontier_dist_le hn hdim Γ hΓ hr.le hcgeom ξ η hne
    (max 0 B) (le_max_left _ _) hBfull hp
  obtain ⟨γ, hlabel, hγK⟩ := hcover q hq
  refine ⟨γ, hlabel, ?_, ?_⟩
  · change dist ((poMulAction hn).smul (γ : PO n 1) p) basepointH ≤ R + max 0 B + 1
    have h1 := dist_triangle ((poMulAction hn).smul (γ : PO n 1) p)
      ((poMulAction hn).smul (γ : PO n 1) q) basepointH
    have h2 : dist ((poMulAction hn).smul (γ : PO n 1) p)
        ((poMulAction hn).smul (γ : PO n 1) q) = dist p q := po_dist_smul hn γ p q
    have h3 : dist ((poMulAction hn).smul (γ : PO n 1) q) basepointH ≤ R :=
      Metric.mem_closedBall.mp (hR hγK)
    linarith
  · have h := smul_mem_thinRegion hn Γ r hp γ
    rwa [hlabel] at h

end DifferentialGeometry.AxialThinCompactness

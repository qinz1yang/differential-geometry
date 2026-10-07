/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.Axis

noncomputable section

open Set Filter
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.AxialStratumDeformation

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary
open HyperbolicConvexity AsymptoticRays BoundaryStabilizer
open OrbifoldStrata FixedLocusGeometry LorentzExtremal StratumDeformation AxisGeometry

variable {n : ℕ}

def normalExpand (ξ η : BoundaryH n) (hne : ξ ≠ η) (s : ℝ) (y : HUpper n) : HUpper n :=
  radialExpand (axisFoot ξ η hne y) s y

theorem normalExpand_of_ne (ξ η : BoundaryH n) (hne : ξ ≠ η)
    {y : HUpper n} (hy : axisFoot ξ η hne y ≠ y) (s : ℝ) :
    normalExpand ξ η hne s y =
      geodFromTo (axisFoot ξ η hne y) y hy (dist (axisFoot ξ η hne y) y + s) :=
  radialExpand_of_ne hy s

theorem continuousAt_normalExpand (ξ η : BoundaryH n) (hne : ξ ≠ η)
    {x : HUpper n} (hx : axisFoot ξ η hne x ≠ x) (s : ℝ) :
    ContinuousAt (normalExpand ξ η hne s) x := by
  let S := {y : HUpper n // axisFoot ξ η hne y ≠ y}
  have hp : Continuous (fun y : S => axisFoot ξ η hne y.val) :=
    (continuous_axisFoot ξ η hne).comp continuous_subtype_val
  have hd : Continuous (fun y : S => dist (axisFoot ξ η hne y.val) y.val) :=
    hp.dist continuous_subtype_val
  have hv : Continuous (fun y : S => y.val.val) := continuous_val.comp continuous_subtype_val
  have hpv : Continuous (fun y : S => (axisFoot ξ η hne y.val).val) :=
    continuous_val.comp hp
  have hinv : Continuous (fun y : S => (Real.sinh (dist (axisFoot ξ η hne y.val) y.val))⁻¹) :=
    (Real.continuous_sinh.comp hd).inv₀
      (fun y => (Real.sinh_pos_iff.mpr (dist_pos.mpr y.property)).ne')
  have hval : Continuous (fun y : S => (normalExpand ξ η hne s y.val).val) := by
    have hc : Continuous (fun y : S =>
        Real.cosh (dist (axisFoot ξ η hne y.val) y.val + s) • (axisFoot ξ η hne y.val).val +
          Real.sinh (dist (axisFoot ξ η hne y.val) y.val + s) •
            ((Real.sinh (dist (axisFoot ξ η hne y.val) y.val))⁻¹ •
              (y.val.val - Real.cosh (dist (axisFoot ξ η hne y.val) y.val) •
                (axisFoot ξ η hne y.val).val))) :=
      ((Real.continuous_cosh.comp (hd.add_const s)).smul hpv).add
        ((Real.continuous_sinh.comp (hd.add_const s)).smul
          (hinv.smul (hv.sub ((Real.continuous_cosh.comp hd).smul hpv))))
    exact hc.congr (fun y => by rw [normalExpand_of_ne ξ η hne y.property]; rfl)
  have hco : ContinuousOn (normalExpand ξ η hne s)
      {y : HUpper n | axisFoot ξ η hne y ≠ y} :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_of_val hval)
  exact hco.continuousAt
    ((isOpen_ne_fun (continuous_axisFoot ξ η hne) continuous_id).mem_nhds hx)

theorem closedSmallSubgroup_normal_le (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (D : Subgroup (PO n 1)) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : ∀ γ : D,
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul (γ : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n)))
    (y : HUpper n) (hy : axisFoot ξ η hne y ≠ y)
    {t : ℝ} (ht : dist (axisFoot ξ η hne y) y ≤ t)
    (hle : closedSmallSubgroup hn Γ ε (geodFromTo (axisFoot ξ η hne y) y hy t) ≤ D) :
    closedSmallSubgroup hn Γ ε (geodFromTo (axisFoot ξ η hne y) y hy t) ≤
      closedSmallSubgroup hn Γ ε y := by
  apply Subgroup.closure_mono
  intro g hg
  have hgD : g ∈ D := hle (Subgroup.subset_closure hg)
  exact ⟨hg.1, (displacement_le_normal_geod hn g ξ η hne (hpair ⟨g, hgD⟩) y hy ht).trans hg.2⟩

theorem not_isOpen_of_axial_exit (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {σ : Set (HUpper n)} {x : HUpper n}
    (hx : x ∈ closure (fixedStratum hn Γ ε σ))
    (ξ η : BoundaryH n) (hne : ξ ≠ η) (hxaxis : axisFoot ξ η hne x ≠ x)
    (hpair : ∀ γ : closedSmallSubgroup hn Γ ε x,
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul (γ : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n)))
    (hexit : ∀ s : ℝ, 0 < s →
      normalExpand ξ η hne s x ∉ closure (fixedStratum hn Γ ε σ)) :
    ¬IsOpen (fixedStratum hn Γ ε σ) := by
  intro hopen
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (eventually_closedSmallSubgroup_le hn Γ hΓ ε x)
  let s : ℝ := r / 4
  have hs : 0 < s := by dsimp [s]; positivity
  have hout : {y : HUpper n |
      normalExpand ξ η hne s y ∉ closure (fixedStratum hn Γ ε σ)} ∈ 𝓝 x :=
    (continuousAt_normalExpand ξ η hne hxaxis s).preimage_mem_nhds
      (isClosed_closure.isOpen_compl.mem_nhds (hexit s hs))
  have hoff : {y : HUpper n | axisFoot ξ η hne y ≠ y} ∈ 𝓝 x :=
    (isOpen_ne_fun (continuous_axisFoot ξ η hne) continuous_id).mem_nhds hxaxis
  obtain ⟨y, hy, hyF⟩ := mem_closure_iff_nhds.mp hx _
    (inter_mem (Metric.ball_mem_nhds x hs) (inter_mem hout hoff))
  have hyclose : dist y x < s := hy.1
  have hpy : axisFoot ξ η hne y ≠ y := hy.2.2
  let p := axisFoot ξ η hne y
  let q : ℝ → HUpper n := fun t => geodFromTo p y hpy (dist p y + t)
  have hqcont : Continuous q :=
    (continuous_geodFromTo (hd := hpy)).comp (continuous_const.add continuous_id)
  have hqzero : q 0 = y := by dsimp [q]; rw [add_zero, geodFromTo_dist]
  have hqball : ∀ t ∈ Icc 0 s, q t ∈ Metric.ball x r := by
    intro t ht
    have hd : dist (q t) y = t := by
      have h := dist_geodFromTo hpy (dist p y + t) (dist p y)
      simpa only [p, geodFromTo_dist, add_sub_cancel_left, abs_of_nonneg ht.1] using h
    have h := dist_triangle (q t) y x
    rw [hd] at h
    change dist (q t) x < r
    dsimp [s] at ht hyclose
    linarith [ht.2]
  have hqclosed : ∀ t ∈ Icc 0 s, q t ∈ closure (fixedStratum hn Γ ε σ) →
      q t ∈ fixedStratum hn Γ ε σ := by
    intro t ht hcl
    have hle := closedSmallSubgroup_normal_le hn Γ ε
      (closedSmallSubgroup hn Γ ε x) ξ η hne hpair y hpy
      (le_add_of_nonneg_right ht.1) (hball (hqball t ht))
    have hsub := fixedLocus_antitone hn hle
    have hsup := fixedLocus_subset_of_incident hn Γ hΓ ε (x := q t) rfl hcl
    change fixedLocus hn (closedSmallSubgroup hn Γ ε (q t)) = σ
    apply Subset.antisymm hsup
    simpa only [show fixedLocus hn (closedSmallSubgroup hn Γ ε y) = σ from hyF] using hsub
  have hconn : IsPreconnected (q '' Icc 0 s) :=
    isPreconnected_Icc.image q hqcont.continuousOn
  have hstart : ((q '' Icc 0 s) ∩ fixedStratum hn Γ ε σ).Nonempty :=
    ⟨y, ⟨0, ⟨le_rfl, hs.le⟩, hqzero⟩, hyF⟩
  have hwhole : q '' Icc 0 s ⊆ fixedStratum hn Γ ε σ :=
    hconn.subset_of_closure_inter_subset hopen hstart (by
      rintro z ⟨hz, t, ht, rfl⟩
      exact hqclosed t ht hz)
  apply hy.2.1
  rw [normalExpand_of_ne ξ η hne hpy]
  exact subset_closure (hwhole ⟨s, ⟨hs.le, le_rfl⟩, rfl⟩)

theorem not_isOpen_of_axial_extremal_of_foot_mem (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {σ : Set (HUpper n)} {x : HUpper n}
    (hx : x ∈ closure (fixedStratum hn Γ ε σ)) (hxσ : x ∉ σ)
    (hext : ∀ y ∈ closure (fixedStratum hn Γ ε σ), ∀ c : ℝ, 1 < c →
      ∀ w ∈ locusSpan σ, w ∈ futureCone → y.val ≠ c • x.val - w)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : ∀ γ : closedSmallSubgroup hn Γ ε x,
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul (γ : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n)))
    (hfoot : axisFoot ξ η hne x ∈ σ) :
    ¬IsOpen (fixedStratum hn Γ ε σ) := by
  have hpx : axisFoot ξ η hne x ≠ x := fun he => hxσ (he ▸ hfoot)
  apply not_isOpen_of_axial_exit hn Γ hΓ ε hx ξ η hne hpx hpair
  intro s hs
  rw [normalExpand_of_ne ξ η hne hpx]
  exact geodFromTo_notMem_of_extremal (locusSpan σ) hext
    (val_mem_locusSpan hfoot) hpx (lt_add_of_pos_right _ hs)

theorem axisFoot_mem_fixedLocus (hn : 1 ≤ n) (D : Subgroup (PO n 1))
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : ∀ γ : D,
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul (γ : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n)))
    {p : HUpper n} (hp : p ∈ fixedLocus hn D) :
    axisFoot ξ η hne p ∈ fixedLocus hn D := by
  intro γ
  rw [← axisFoot_smul hn γ ξ η hne (hpair γ) p, hp γ]

theorem axis_subset_fixedLocus_of_pointwise (hn : 1 ≤ n) (D : Subgroup (PO n 1))
    (hD : (fixedLocus hn D).Nonempty) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hξ : ∀ γ : D, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ)
    (hη : ∀ γ : D, (poBoundaryMulAction hn).smul (γ : PO n 1) η = η) :
    axis ξ η ⊆ fixedLocus hn D := by
  obtain ⟨p, hp⟩ := hD
  rw [axis_eq_range_rayTo ξ η hne]
  rintro _ ⟨t, rfl⟩ γ
  have hc := BoundaryFixedPoints.poConfFactor_eq_one_of_interior_fixed hn γ ξ (hξ γ) p (hp γ)
  simpa only [hc, Real.log_one, add_zero] using
    smul_axis_ray hn γ ξ η hne (hξ γ) (hη γ) t

theorem exists_exchange_of_axis_not_subset (hn : 1 ≤ n) (D : Subgroup (PO n 1))
    (hD : (fixedLocus hn D).Nonempty) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : ∀ γ : D,
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul (γ : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n)))
    (hnot : ¬axis ξ η ⊆ fixedLocus hn D) :
    ∃ γ : D, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = η ∧
      (poBoundaryMulAction hn).smul (γ : PO n 1) η = ξ := by
  by_contra hex
  have hpoint (γ : D) :
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
        (poBoundaryMulAction hn).smul (γ : PO n 1) η = η := by
    rcases boundary_pair_cases hn γ ξ η hne (hpair γ) with h | h
    · exact h
    · exact (hex ⟨γ, h⟩).elim
  exact hnot (axis_subset_fixedLocus_of_pointwise hn D hD ξ η hne
    (fun γ => (hpoint γ).1) (fun γ => (hpoint γ).2))

theorem axis_inter_label_nonempty_at_closure (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {σ : Set (HUpper n)} (hσ : σ.Nonempty) {x : HUpper n}
    (hx : x ∈ closure (fixedStratum hn Γ ε σ))
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : ∀ γ : closedSmallSubgroup hn Γ ε x,
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul (γ : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n))) :
    (axis ξ η ∩ σ).Nonempty := by
  obtain ⟨y, hy, hyF⟩ := mem_closure_iff_nhds.mp hx _
    (eventually_closedSmallSubgroup_le hn Γ hΓ ε x)
  obtain ⟨p, hp⟩ := hσ
  have he : fixedLocus hn (closedSmallSubgroup hn Γ ε y) = σ := hyF
  have hfix := axisFoot_mem_fixedLocus hn (closedSmallSubgroup hn Γ ε y) ξ η hne
    (fun γ => hpair ⟨γ, hy γ.property⟩) (he.symm ▸ hp)
  exact ⟨axisFoot ξ η hne p, axisFoot_mem ξ η hne p, he ▸ hfix⟩

theorem exists_exchanging_axial_extremal_of_isOpen (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hgeometry : ∀ x : HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (closedSmallSubgroup hn Γ ε x))
    {σ : Set (HUpper n)} (hσ : σ.Nonempty)
    (hF : (fixedStratum hn Γ ε σ).Nonempty) (hproper : σ ≠ univ)
    (hopen : IsOpen (fixedStratum hn Γ ε σ)) :
    ∃ x ∈ closure (fixedStratum hn Γ ε σ), x ∉ σ ∧
      (∀ y ∈ closure (fixedStratum hn Γ ε σ), ∀ c : ℝ, 1 < c →
        ∀ w ∈ locusSpan σ, w ∈ futureCone → y.val ≠ c • x.val - w) ∧
      Infinite (closedSmallSubgroup hn Γ ε x) ∧
      ∃ (ξ η : BoundaryH n) (hne : ξ ≠ η),
        (∀ γ : closedSmallSubgroup hn Γ ε x,
          (poBoundaryMulAction hn).smul (γ : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
          (poBoundaryMulAction hn).smul (γ : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n))) ∧
        axisFoot ξ η hne x ∉ σ ∧ (axis ξ η ∩ σ).Nonempty ∧
        ∀ y ∈ fixedStratum hn Γ ε σ,
          closedSmallSubgroup hn Γ ε y ≤ closedSmallSubgroup hn Γ ε x →
            ∃ γ : closedSmallSubgroup hn Γ ε y,
              (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = η ∧
              (poBoundaryMulAction hn).smul (γ : PO n 1) η = ξ := by
  obtain ⟨x, hx, hxσ, hext, hinf, ξ, η, hne, hpair⟩ :=
    exists_axial_extremal_of_isOpen hn Γ hΓ hε hgeometry hσ hF hproper hopen
  have hfoot : axisFoot ξ η hne x ∉ σ := fun hp =>
    not_isOpen_of_axial_extremal_of_foot_mem hn Γ hΓ ε hx hxσ hext ξ η hne hpair hp hopen
  refine ⟨x, hx, hxσ, hext, hinf, ξ, η, hne, hpair, hfoot,
    axis_inter_label_nonempty_at_closure hn Γ hΓ ε hσ hx ξ η hne hpair, ?_⟩
  intro y hy hle
  have he : fixedLocus hn (closedSmallSubgroup hn Γ ε y) = σ := hy
  apply exists_exchange_of_axis_not_subset hn (closedSmallSubgroup hn Γ ε y)
    (he.symm ▸ hσ) ξ η hne (fun γ => hpair ⟨γ, hle γ.property⟩)
  intro hsub
  exact hfoot (he ▸ hsub (axisFoot_mem ξ η hne x))

end DifferentialGeometry.AxialStratumDeformation

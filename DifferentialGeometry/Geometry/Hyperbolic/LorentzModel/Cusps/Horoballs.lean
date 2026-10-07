/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.CrossSections

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.CuspHoroballs

open Hyperbolic HyperbolicAction HyperbolicBoundary HyperbolicFaithful
open AsymptoticRays Busemann BusemannCocycle BoundaryStabilizer
open OrbifoldStrata ElementaryEnds OrbifoldThinRegions HorosphereProjection CuspCrossSections

variable {n : ℕ}

theorem displacement_rayTo_lt (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n)
    (hfix : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hscale : poConfFactor hn g ξ = 1) (p : HUpper n)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hshort : dist ((poMulAction hn).smul g p) p ≤ r) :
    dist ((poMulAction hn).smul g (rayTo p ξ t)) (rayTo p ξ t) < r := by
  have he := ParabolicRegions.cosh_displacement_rayTo_sub_one hn g ξ hfix hscale p t
  have hB : 0 < Real.cosh r - 1 := by
    have h := Real.cosh_strictMonoOn (by norm_num : (0 : ℝ) ∈ Ici 0) hr.le hr
    simpa only [Real.cosh_zero, sub_pos] using h
  have hC := Real.cosh_strictMonoOn.monotoneOn dist_nonneg hr.le hshort
  have hE : Real.exp (-(2 * t)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hEp := Real.exp_pos (-(2 * t))
  have hmul := mul_le_mul_of_nonneg_right (show
      Real.cosh (dist ((poMulAction hn).smul g p) p) - 1 ≤ Real.cosh r - 1 by linarith) hEp.le
  have hstrict := mul_lt_mul_of_pos_left hE hB
  apply (Real.cosh_strictMonoOn.lt_iff_lt dist_nonneg hr.le).mp
  nlinarith

theorem rayTo_mem_interior_thinRegion (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {r : ℝ} (hr : 0 < r)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (closedSmallSubgroup hn Γ r x))
    {ξ : BoundaryH n} {p : HUpper n} (hp : p ∈ thinRegion hn Γ r {ξ})
    {t : ℝ} (ht : 0 < t) : rayTo p ξ t ∈ interior (thinRegion hn Γ r {ξ}) := by
  let := hp.1
  have hfix := hp.2.horospherical
  have hshort : ∀ᶠ y in 𝓝 (rayTo p ξ t), ∀ g ∈ closedSmallElements hn Γ r p,
      dist ((poMulAction hn).smul g y) y < r := by
    apply (finite_closedSmallElements hn Γ hΓ r p).eventually_all.mpr
    intro g hg
    have hf := hfix ⟨g, Subgroup.subset_closure hg⟩
    have hc : Continuous (fun y : HUpper n => dist ((poMulAction hn).smul g y) y) := by
      simpa only [dist_comm] using LatticeCompactness.continuous_displacement hn g
    exact (hc.tendsto _).eventually (Iio_mem_nhds
      (displacement_rayTo_lt hn g ξ hf.1 hf.2 p hr ht hg.2))
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hshort] with y hy
  have hle : closedSmallSubgroup hn Γ r p ≤ closedSmallSubgroup hn Γ r y :=
    Subgroup.closure_mono (fun g hg => ⟨hg.1, (hy g hg).le⟩)
  exact ⟨Infinite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _),
    hp.2.of_le (hΓ.mono (closedSmallSubgroup_le hn Γ r y)) hle (hgeom y)⟩

theorem busemann_smul_of_center_fixed (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) {r : ℝ} {ξ : BoundaryH n}
    (hξ : (thinRegion hn Γ r {ξ}).Nonempty) (γ : Γ)
    (hfix : (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ) (p : HUpper n) :
    busemann ξ ((poMulAction hn).smul (γ : PO n 1) p) = busemann ξ p := by
  have hg : (γ : PO n 1) ∈ endStabilizer hn Γ {ξ} :=
    (mem_endStabilizer_singleton hn Γ ξ γ).mpr ⟨γ.property, hfix⟩
  have hscale := (horospherical_endStabilizer hn Γ hΓ hξ ⟨γ, hg⟩).2
  have hb := po_busemann_smul hn γ ξ p
  simpa only [hfix, hscale, Real.log_one, sub_zero] using hb

theorem exists_frontier_busemann_bounds (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {ξ : BoundaryH n} (hξ : (thinRegion hn Γ r {ξ}).Nonempty) :
    ∃ L U : ℝ, L ≤ U ∧ ∀ p ∈ frontier (thinRegion hn Γ r {ξ}),
      L ≤ busemann ξ p ∧ busemann ξ p ≤ U := by
  obtain ⟨K, hK, _, hcover⟩ := exists_compact_frontier_core hn hdim Γ hΓ hcov hr hre hgeom {ξ}
  obtain ⟨x, hx⟩ := frontier_nonempty hn hdim Γ hΓ hr.le hξ
  obtain ⟨γ, _, hγ⟩ := hcover x hx
  have hKne : K.Nonempty := ⟨(poMulAction hn).smul (γ : PO n 1) x, hγ⟩
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hKne (continuous_busemann ξ).continuousOn
  obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hKne (continuous_busemann ξ).continuousOn
  refine ⟨busemann ξ p, busemann ξ q, hmin hq, ?_⟩
  intro y hy
  obtain ⟨δ, hδlabel, hδK⟩ := hcover y hy
  have hfix : (poBoundaryMulAction hn).smul (δ : PO n 1) ξ = ξ :=
    singleton_injective (by simpa only [image_singleton] using hδlabel)
  have hb := busemann_smul_of_center_fixed hn Γ hΓ hξ δ hfix y
  have hlo : busemann ξ p ≤ busemann ξ ((poMulAction hn).smul (δ : PO n 1) y) := hmin hδK
  have hhi : busemann ξ ((poMulAction hn).smul (δ : PO n 1) y) ≤ busemann ξ q := hmax hδK
  exact ⟨by simpa only [hb] using hlo, by simpa only [hb] using hhi⟩

theorem exists_horoball_subset_interior (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {ξ : BoundaryH n} (hξ : (thinRegion hn Γ r {ξ}).Nonempty) :
    ∃ c : ℝ, horoball ξ c ⊆ interior (thinRegion hn Γ r {ξ}) := by
  have hcgeom (x : HUpper n) := closedSmallSubgroup_geometry hn Γ hre x (hgeom x)
  obtain ⟨L, U, _, hbounds⟩ := exists_frontier_busemann_bounds hn hdim Γ hΓ hcov hr hre hgeom hξ
  refine ⟨L - 1, fun y hy => ?_⟩
  have hyb : busemann ξ y ≤ L - 1 := hy
  obtain ⟨s, hs⟩ := exists_frontier_on_ray hn Γ hΓ hr hcgeom hξ y
  have hLb := (hbounds _ hs).1
  rw [busemann_rayTo] at hLb
  have hsneg : 0 < -s := by linarith
  have hsR : rayTo y ξ s ∈ thinRegion hn Γ r {ξ} :=
    (isClosed_thinRegion hn Γ hΓ r hcgeom {ξ}).closure_eq ▸ hs.1
  have h := rayTo_mem_interior_thinRegion hn Γ hΓ hr hcgeom hsR hsneg
  simpa only [rayTo_add, add_neg_cancel, rayTo_zero] using h

theorem precisely_invariant_of_subset (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {r : ℝ} {ξ : BoundaryH n} (hξ : (thinRegion hn Γ r {ξ}).Nonempty)
    (c : ℝ) (hsub : horoball ξ c ⊆ thinRegion hn Γ r {ξ}) (γ : Γ) :
    ((poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ →
      (fun p : HUpper n => (poMulAction hn).smul (γ : PO n 1) p) '' horoball ξ c = horoball ξ c) ∧
    ((poBoundaryMulAction hn).smul (γ : PO n 1) ξ ≠ ξ →
      Disjoint ((fun p : HUpper n => (poMulAction hn).smul (γ : PO n 1) p) '' horoball ξ c)
        (horoball ξ c)) := by
  let := poMulAction hn
  let := poBoundaryMulAction hn
  constructor
  · intro hfix
    have hmem (p : HUpper n) : (γ : PO n 1) • p ∈ horoball ξ c ↔ p ∈ horoball ξ c := by
      change busemann ξ ((γ : PO n 1) • p) ≤ c ↔ busemann ξ p ≤ c
      exact Iff.of_eq (congrArg (fun b : ℝ => b ≤ c)
        (busemann_smul_of_center_fixed hn Γ hΓ hξ γ hfix p))
    apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      exact (hmem p).mpr hp
    · intro p hp
      exact ⟨(γ : PO n 1)⁻¹ • p,
        (hmem _).mp (by simpa only [smul_inv_smul] using hp), smul_inv_smul _ _⟩
  · intro hne
    apply Set.disjoint_left.mpr
    rintro p ⟨y, hy, rfl⟩ hp
    have hleft := smul_mem_thinRegion hn Γ r (hsub hy) γ
    have hright := hsub hp
    let := hright.1
    have he := hleft.2.unique (hΓ.mono (closedSmallSubgroup_le hn Γ r _)) hright.2
    exact hne (singleton_injective (by simpa only [image_singleton] using he))

theorem exists_precisely_invariant_horoball (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {ξ : BoundaryH n} (hξ : (thinRegion hn Γ r {ξ}).Nonempty) :
    ∃ c : ℝ, horoball ξ c ⊆ interior (thinRegion hn Γ r {ξ}) ∧ ∀ γ : Γ,
      ((poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ →
        (fun p : HUpper n => (poMulAction hn).smul (γ : PO n 1) p) '' horoball ξ c = horoball ξ c) ∧
      ((poBoundaryMulAction hn).smul (γ : PO n 1) ξ ≠ ξ →
        Disjoint ((fun p : HUpper n => (poMulAction hn).smul (γ : PO n 1) p) '' horoball ξ c)
          (horoball ξ c)) := by
  obtain ⟨c, hc⟩ := exists_horoball_subset_interior hn hdim Γ hΓ hcov hr hre hgeom hξ
  exact ⟨c, hc, precisely_invariant_of_subset hn Γ hΓ hξ c (hc.trans interior_subset)⟩

def closedCuspCollar (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (r : ℝ) (ξ : BoundaryH n) (c : ℝ) : Set (HUpper n) :=
  thinRegion hn Γ r {ξ} ∩ {p | c ≤ busemann ξ p}

theorem isClosed_closedCuspCollar (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (closedSmallSubgroup hn Γ r x))
    (ξ : BoundaryH n) (c : ℝ) : IsClosed (closedCuspCollar hn Γ r ξ c) :=
  (isClosed_thinRegion hn Γ hΓ r hgeom {ξ}).inter
    (isClosed_le continuous_const (continuous_busemann ξ))

theorem exists_compact_cuspCollar_core (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {ξ : BoundaryH n} (hξ : (thinRegion hn Γ r {ξ}).Nonempty) (c : ℝ) :
    ∃ C : Set (HUpper n), IsCompact C ∧ C ⊆ closedCuspCollar hn Γ r ξ c ∧
      ∀ p ∈ closedCuspCollar hn Γ r ξ c, ∃ γ : Γ,
        (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
        (poMulAction hn).smul (γ : PO n 1) p ∈ C := by
  have hcgeom (x : HUpper n) := closedSmallSubgroup_geometry hn Γ hre x (hgeom x)
  obtain ⟨K, hK, _, hcover⟩ := exists_compact_frontier_core hn hdim Γ hΓ hcov hr hre hgeom {ξ}
  obtain ⟨L, U, _, hbounds⟩ := exists_frontier_busemann_bounds hn hdim Γ hΓ hcov hr hre hgeom hξ
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (basepointH : HUpper n)
  let C := Metric.closedBall (basepointH : HUpper n) (R + max 0 (U - c)) ∩
    closedCuspCollar hn Γ r ξ c
  refine ⟨C, (isCompact_closedBall _ _).inter_right
    (isClosed_closedCuspCollar hn Γ hΓ r hcgeom ξ c), inter_subset_right, ?_⟩
  intro p hp
  obtain ⟨s, hs⟩ := exists_frontier_on_ray hn Γ hΓ hr hcgeom hξ p
  have hsnonpos : s ≤ 0 := by
    by_contra h
    exact hs.2 (rayTo_mem_interior_thinRegion hn Γ hΓ hr hcgeom hp.1 (lt_of_not_ge h))
  have hbU := (hbounds _ hs).2
  rw [busemann_rayTo] at hbU
  have hdist : dist p (rayTo p ξ s) ≤ U - c := by
    rw [dist_rayTo_self, abs_of_nonpos hsnonpos]
    have hpc : c ≤ busemann ξ p := hp.2
    linarith
  obtain ⟨γ, hlabel, hγK⟩ := hcover _ hs
  have hfix : (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ :=
    singleton_injective (by simpa only [image_singleton] using hlabel)
  have hb := busemann_smul_of_center_fixed hn Γ hΓ hξ γ hfix p
  refine ⟨γ, hfix, ?_, ?_⟩
  · change dist ((poMulAction hn).smul (γ : PO n 1) p) basepointH ≤ R + max 0 (U - c)
    have h1 := dist_triangle ((poMulAction hn).smul (γ : PO n 1) p)
      ((poMulAction hn).smul (γ : PO n 1) (rayTo p ξ s)) basepointH
    have h2 : dist ((poMulAction hn).smul (γ : PO n 1) p)
        ((poMulAction hn).smul (γ : PO n 1) (rayTo p ξ s)) = dist p (rayTo p ξ s) :=
      po_dist_smul hn (γ : PO n 1) p (rayTo p ξ s)
    have h3 : dist ((poMulAction hn).smul (γ : PO n 1) (rayTo p ξ s)) basepointH ≤ R :=
      Metric.mem_closedBall.mp (hR hγK)
    linarith [le_max_right 0 (U - c)]
  · constructor
    · have h := smul_mem_thinRegion hn Γ r hp.1 γ
      simpa only [image_singleton, hfix] using h
    · change c ≤ busemann ξ ((poMulAction hn).smul (γ : PO n 1) p)
      rw [hb]
      exact hp.2

end DifferentialGeometry.CuspHoroballs

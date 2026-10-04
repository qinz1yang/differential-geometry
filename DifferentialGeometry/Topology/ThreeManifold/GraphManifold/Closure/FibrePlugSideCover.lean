import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugSideSolid

/-!
The complete native lift and produced cap map cover the actual bounded fibre plug components.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.ElementaryPresentation

open SplitTube

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
  (hlin : E.IsLinearSeam j)

theorem boundedPlugSideSolid_lift_cover (t : Bool) {z : ℂ} (hz : ‖z‖ ≤ 3) (w : Circle)
    (hside : E.boundedPlugSideSolidMap h (z, w) ∈ E.fibrePlugSide h hlin t)
    (hn : E.toTorus.pairing.count = 1) :
    ∃ q : ℂ × Circle, E.boundedPlugSideDom h t q ∧
      0 < sgnR t * E.boundedPlugSideLevel h t q ∧
      E.boundedPlugSideLiftMap h hlin t q = E.boundedPlugSideSolidMap h (z, w) := by
  have he₀ := (E.boundedSplitCharts h hlin).he₀
  set q : ℂ × Circle := ((1 / 2 : ℝ) • z, w ^ (E.boundedSplitCharts h hlin).e₀) with hqdef
  have hq32 : ‖q.1‖ ≤ 3 / 2 := by
    change ‖(1 / 2 : ℝ) • z‖ ≤ 3 / 2
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith
  have hq3 : ‖q.1‖ ≤ 3 := by linarith
  have hs := (E.fibrePlug_solid_side_iff h hlin hn (clampDisc z, w) t).mp hside
  have hlev : 0 < sgnR t * E.boundedPlugSideLevel h t q := by
    rw [E.boundedPlugSideLevel_of_le h t (by linarith)]
    have hR : 2 ≤ vRadius (E.boundedPlugSideHost h) (2 * ‖q.1‖) :=
      two_le_vRadius _ (by positivity) (by linarith)
    have hh := (fibrePlug_strip_boundary_sign (E.boundedPlugSideHost h) t hR
      (w ^ (E.boundedSplitCharts h hlin).e₀)).mpr hs
    convert hh using 1
  refine ⟨q, ⟨hq3, by linarith⟩, hlev, ?_⟩
  unfold boundedPlugSideLiftMap boundedPlugSideLiftPoint
  rw [ite_eq_left hq32]
  have e1 : (2 : ℝ) • q.1 = z := by
    change (2 : ℝ) • (1 / 2 : ℝ) • z = z
    rw [smul_smul]
    norm_num
  have e2 : q.2 ^ (E.boundedSplitCharts h hlin).e₀ = w := zpow_zpow_unit he₀ w
  rw [e1, e2]
  rfl

theorem boundedPlugSideSolidMap_host_boundary (τ : Torus) :
    E.boundedPlugSideSolidMap h ((3 : ℝ) • (τ.1 : ℂ), τ.2) =
      E.boundedPlugSideHostMap h (planarCollarFormula 3 (E.boundedPlugSideHost h)
        (((E.crossMap j b τ).1 : ℂ), 0), (E.crossMap j b τ).2) := by
  change E.toTorus.cutMap (E.boundedPlugSideSolidPoint h ((3 : ℝ) • (τ.1 : ℂ)) τ.2) =
    E.toTorus.cutMap (E.boundedPlugSideHostPoint h
      (planarCollarFormula 3 (E.boundedPlugSideHost h) (((E.crossMap j b τ).1 : ℂ), 0))
      (E.crossMap j b τ).2)
  rw [E.boundedPlugSideSolidPoint_boundary h, E.boundedPlugSideHostPoint_collar h,
    E.boundedPlugSidePortHost h]
  have e0 := E.cutMap_sideCollar_eq_seam j b τ 0 le_rfl zero_lt_one
  have e1 := E.cutMap_sideCollar_eq_seam j (!b) (E.crossMap j b τ) 0 le_rfl zero_lt_one
  rw [E.leftOfSide_not_crossMap, sideHeight_not] at e1
  change E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j b) (τ, halfPoint 0 le_rfl)) =
    E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j !b)
      (E.crossMap j b τ, halfPoint 0 le_rfl))
  rw [e0, e1]
  cases b <;> simp [sideHeight]

theorem boundedPlugSideHost_lift_cover (t : Bool) {z : ℂ} (hz : z ∈ planarModel 3)
    (ν : Circle) (hside : E.boundedPlugSideHostMap h (z, ν) ∈ E.fibrePlugSide h hlin t)
    (hn : E.toTorus.pairing.count = 1) :
    ∃ q : ℂ × Circle, E.boundedPlugSideDom h t q ∧
      0 < sgnR t * E.boundedPlugSideLevel h t q ∧
      E.boundedPlugSideLiftMap h hlin t q = E.boundedPlugSideHostMap h (z, ν) := by
  have he₁ := (E.boundedSplitCharts h hlin).he₁
  set l := E.boundedPlugSideHost h with hl
  have ht : 0 < sgnR t * stripLevel l (hostInv l z) := by
    have hh := (E.fibrePlug_host_side_iff h hlin hn (clampPants z, ν) t).mp hside
    change 0 < sgnR t * stripLevel l (hostInv l (clampPants z).val.down) at hh
    simpa only [clampPants_val hz] using hh
  obtain ⟨⟨u, ρ⟩, hρ, hpt⟩ := exists_point_eq l t hz
  simp only at hρ hpt
  rcases eq_or_lt_of_le hρ.1 with h32 | h32
  · subst h32
    have key : hostChart l ((sideData l t).point (u, 3 / 2)) =
        planarCollarFormula 3 l ((u : ℂ), (4 * (3 / 2) - 6) / 3) :=
      (E.boundedPlugSideCharts h hlin).hostChart_point_of_le t (by norm_num) (by norm_num)
    rw [hpt, hostChart_hostInv, show (4 * (3 / 2 : ℝ) - 6) / 3 = 0 by norm_num] at key
    set τ := (E.crossMap j b).symm (u, ν) with hτ
    have hc : E.crossMap j b τ = (u, ν) := (E.crossMap j b).apply_symm_apply _
    have hglue := E.boundedPlugSideSolidMap_host_boundary h τ
    rw [hc, ← key] at hglue
    have hz3 : ‖(3 : ℝ) • (τ.1 : ℂ)‖ ≤ 3 := by
      rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by norm_num)]
    obtain ⟨q, hq, hs, he⟩ := E.boundedPlugSideSolid_lift_cover h hlin t hz3 τ.2
      (hglue.symm ▸ hside) hn
    exact ⟨q, hq, hs, he.trans hglue⟩
  · set θ : Circle := (ν * (u ^ ((E.boundedSplitCharts h hlin).e₀ *
      (E.boundedSplitCharts h hlin).d))⁻¹) ^ (E.boundedSplitCharts h hlin).e₁ with hθ
    set q : ℂ × Circle := (ρ • (θ : ℂ), u) with hqdef
    have hnorm : ‖q.1‖ = ρ := by
      change ‖ρ • (θ : ℂ)‖ = ρ
      rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by linarith)]
    have hu : unitOf q.1 = θ := unitOf_smul (by linarith) θ
    have hlev : E.boundedPlugSideLevel h t q = stripLevel l (hostInv l z) := by
      unfold boundedPlugSideLevel
      rw [hnorm]
      change stripLevel l ((sideData l t).point (u, ρ)) = _
      rw [hpt]
    refine ⟨q, ⟨by rw [hnorm]; exact hρ.2, ?_⟩, by rw [hlev]; exact ht, ?_⟩
    · rw [hlev]
      linarith
    · unfold boundedPlugSideLiftMap boundedPlugSideLiftPoint
      rw [ite_eq_right (by rw [hnorm]; linarith)]
      have e1 : hostChart (E.boundedPlugSideHost h)
          ((sideData (E.boundedPlugSideHost h) t).point (q.2, ‖q.1‖)) = z := by
        rw [hnorm]
        change hostChart l ((sideData l t).point (u, ρ)) = z
        rw [hpt, hostChart_hostInv]
      have e2 : E.boundedPlugSideFibre h hlin q = ν := by
        unfold boundedPlugSideFibre
        rw [hu, hθ, zpow_zpow_unit he₁, mul_comm ν, mul_inv_cancel_left]
      rw [e1, e2]
      rfl

theorem boundedPlugSide_lift_cover (hn : E.toTorus.pairing.count = 1) (t : Bool)
    {y : W.Carrier} (hy : y ∈ E.fibrePlugSide h hlin t) :
    ∃ q : ℂ × Circle, E.boundedPlugSideDom h t q ∧
      0 < sgnR t * E.boundedPlugSideLevel h t q ∧ E.boundedPlugSideLiftMap h hlin t q = y := by
  rcases hy with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  · have hz : v.1.val.down ∈ planarModel 3 :=
      (mem_planarSet_iff (Or.inr rfl) _).mp v.1.property
    have hcl : clampPants.{u} v.1.val.down = v.1 := by
      apply Subtype.ext
      exact clampPants_val hz
    have he : E.boundedPlugSideHostMap h (v.1.val.down, v.2) =
        E.toTorus.cutMap ((E.splitData h).ΘH v).val := by
      unfold boundedPlugSideHostMap boundedPlugSideHostPoint boundedModelHostPoint
      rw [hcl]
    have hm : E.boundedPlugSideHostMap h (v.1.val.down, v.2) ∈ E.fibrePlugSide h hlin t :=
      he.symm ▸ Or.inl ⟨v, hv, rfl⟩
    obtain ⟨q, hq, hl, hqv⟩ := E.boundedPlugSideHost_lift_cover h hlin t hz v.2 hm hn
    exact ⟨q, hq, hl, hqv.trans he⟩
  · have hz : ‖v.1.val.down‖ ≤ 3 := (mem_discSet_iff _).mp v.1.property
    have hcl : clampDisc.{u} v.1.val.down = v.1 := by
      apply Subtype.ext
      exact clampDisc_val hz
    have he : E.boundedPlugSideSolidMap h (v.1.val.down, v.2) =
        E.toTorus.cutMap ((E.splitData h).ΘV v).val := by
      unfold boundedPlugSideSolidMap boundedPlugSideSolidPoint
      rw [hcl]
    have hm : E.boundedPlugSideSolidMap h (v.1.val.down, v.2) ∈ E.fibrePlugSide h hlin t :=
      he.symm ▸ Or.inr ⟨v, hv, rfl⟩
    obtain ⟨q, hq, hl, hqv⟩ := E.boundedPlugSideSolid_lift_cover h hlin t hz v.2 hm hn
    exact ⟨q, hq, hl, hqv.trans he⟩

theorem boundedPlugSideLift_mem_side (hn : E.toTorus.pairing.count = 1) (t : Bool)
    (q : ℂ × Circle) (hq : E.boundedPlugSideDom h t q)
    (hl : 0 < sgnR t * E.boundedPlugSideLevel h t q) :
    E.boundedPlugSideLiftMap h hlin t q ∈ E.fibrePlugSide h hlin t := by
  by_cases h32 : ‖q.1‖ ≤ 3 / 2
  · unfold boundedPlugSideLiftMap boundedPlugSideLiftPoint
    rw [ite_eq_left h32]
    apply (E.fibrePlug_solid_side_iff h hlin hn
      (clampDisc ((2 : ℝ) • q.1), q.2 ^ (E.boundedSplitCharts h hlin).e₀) t).mpr
    rw [zpow_zpow_unit (E.boundedSplitCharts h hlin).he₀]
    rw [E.boundedPlugSideLevel_of_le h t (by linarith)] at hl
    have hR : 2 ≤ vRadius (E.boundedPlugSideHost h) (2 * ‖q.1‖) :=
      two_le_vRadius _ (by positivity) (by linarith)
    apply (fibrePlug_strip_boundary_sign (E.boundedPlugSideHost h) t hR q.2).mp
    convert hl using 1
  · have hz := E.boundedPlugSide_hostPoint_planar h hq (lt_of_not_ge h32).le
    unfold boundedPlugSideLiftMap boundedPlugSideLiftPoint
    rw [ite_eq_right h32]
    apply (E.fibrePlug_host_side_iff h hlin hn
      (clampPants (hostChart (E.boundedPlugSideHost h)
        ((sideData (E.boundedPlugSideHost h) t).point (q.2, ‖q.1‖))),
        E.boundedPlugSideFibre h hlin q) t).mpr
    change 0 < sgnR t * stripLevel (E.boundedPlugSideHost h)
      (hostInv (E.boundedPlugSideHost h) (clampPants (hostChart (E.boundedPlugSideHost h)
        ((sideData (E.boundedPlugSideHost h) t).point (q.2, ‖q.1‖)))).val.down)
    rw [clampPants_val hz, hostInv_hostChart]
    exact hl

variable (d : PartialDiffeomorph sphereSignedCollarModel W.model
  (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior) {n : ℕ} (A : BoundaryTori W n)
  (hA : W.model.boundary W.Carrier = A.image)
  (hav : ∀ i, Disjoint (A.collar i).target d.target)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))

theorem boundedPlugSideCappedMap_cover_ballMap (t : Bool) (x : EuclideanSpace ℝ (Fin 3))
    (hx : ‖x‖ ≤ 2) :
    ∃ q : ℂ × Circle, ‖q.1‖ ≤ 3 ∧
      E.boundedPlugSideCappedMap h hlin d hs hI A hA hav t q =
        boundedPlugSideBallMap d hs hI A hA hav E h hlin (boundedPlugSideSolidIndex t) x := by
  have hz : ‖(1 / 2 : ℝ) • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith
  obtain ⟨q, h3, h2, hG⟩ := (E.exists_boundedPlugSideFill h hlin t).choose_spec.2.1
    ((1 / 2 : ℝ) • x) hz
  change E.boundedPlugSideFillDiffeomorph h hlin t ((1 / 2 : ℝ) • x) = torusPD q at hG
  refine ⟨q, h3.le, ?_⟩
  rw [E.boundedPlugSideCappedMap_fake h hlin d hs hI A hA hav h3 h2]
  change boundedPlugSideBallMap d hs hI A hA hav E h hlin (boundedPlugSideSolidIndex t)
    ((2 : ℝ) • (E.boundedPlugSideFillDiffeomorph h hlin t).symm (torusPD q)) = _
  rw [← hG, Diffeomorph.symm_apply_apply, smul_smul]
  norm_num

theorem boundedPlugSideBallMap_cover_tube (t : Bool) (z : SphereTwo) {s : ℝ}
    (hs0 : 0 < s) (hs2 : s ≤ 2) :
    ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 2 ∧
      boundedPlugSideBallMap d hs hI A hA hav E h hlin (boundedPlugSideSolidIndex t) x =
        (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCore
          (sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
            (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)
            (E.boundedSplitTubeMap h hlin (z, sgnR t * s))) := by
  let r := boundedPlugCapProfileDiffeomorph.symm s
  have hr : boundedPlugCapProfile r = s := boundedPlugCapProfileDiffeomorph.apply_symm_apply s
  have hr1 : 1 < r := by
    by_contra hn
    have hh := boundedPlugCapProfile_strictMono.monotone (le_of_not_gt hn)
    rw [hr, boundedPlugCapProfile_inner (by norm_num : (1 : ℝ) ≤ 5 / 4)] at hh
    linarith
  have hr2 : r ≤ 2 := by
    by_contra hn
    have hh := boundedPlugCapProfile_strictMono (lt_of_not_ge hn)
    rw [hr, boundedPlugCapProfile_outer (by norm_num : (3 / 2 : ℝ) ≤ 2)] at hh
    linarith
  have hnorm : ‖r • (z : EuclideanSpace ℝ (Fin 3))‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ r), norm_eq_of_mem_sphere z, mul_one]
  refine ⟨r • (z : EuclideanSpace ℝ (Fin 3)), by rw [hnorm]; exact hr2, ?_⟩
  have hmap := boundedPlugSideBallMap_shell d hs hI A hA hav E h hlin
    (boundedPlugSideSolidIndex t) (r • (z : EuclideanSpace ℝ (Fin 3))) (by rw [hnorm]; exact hr1)
  have hp : (ULift.up (sphereDirection poleS2 (r • (z : EuclideanSpace ℝ (Fin 3)))),
      ‖r • (z : EuclideanSpace ℝ (Fin 3))‖) = (ULift.up z, r) := by
    refine Prod.ext ?_ hnorm
    exact congrArg ULift.up (sphereDirection_pos_smul poleS2 z (by linarith))
  have hraw : (z, boundedPlugCapShellSign (boundedPlugSideSolidIndex t) *
      boundedPlugCapProfile r) = (z, sgnR t * s) := by
    rw [boundedPlugSideSolidIndex_sign, hr]
  exact hmap.trans ((congrArg (boundedPlugCapShell d hs hI A hA hav E h hlin
    (boundedPlugSideSolidIndex t)) hp).trans
      (congrArg (fun q : SphereTwo × ℝ => (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCore
        (sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
          (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)
          (E.boundedSplitTubeMap h hlin q))) hraw))

theorem boundedPlugSideCappedMap_cover_real {t : Bool} {q : ℂ × Circle}
    (hq : E.boundedPlugSideDom h t q) (hl : 0 < sgnR t * E.boundedPlugSideLevel h t q) :
    ∃ q' : ℂ × Circle, ‖q'.1‖ ≤ 3 ∧
      E.boundedPlugSideCappedMap h hlin d hs hI A hA hav t q' =
        E.boundedPlugSideRealMap h hlin d hs hI A hA hav t q := by
  by_cases hgt : 2 < sgnR t * E.boundedPlugSideLevel h t q
  · exact ⟨q, hq.1, E.boundedPlugSideCappedMap_real h hlin d hs hI A hA hav hgt⟩
  · have h2 := le_of_not_gt hgt
    have h3 : ‖q.1‖ < 3 := by
      by_contra hn
      have hh := E.boundedPlugSideLevel_gt_three h t (q := q) (by linarith) hq.1
      linarith
    have ha : |E.boundedPlugSideLevel h t q| < 3 := by
      rw [← SplitCharts.abs_sgnR_mul t, abs_of_pos hl]
      linarith
    obtain ⟨z, hz⟩ := E.boundedPlugSideTube_cover h hlin t hq h3 ha
    obtain ⟨x, hx, hm⟩ := E.boundedPlugSideBallMap_cover_tube h hlin d hs hI A hA hav
      t z hl h2
    obtain ⟨q', hq', he⟩ := E.boundedPlugSideCappedMap_cover_ballMap h hlin d hs hI A hA hav
      t x hx
    have hraw : sgnR t * (sgnR t * E.boundedPlugSideLevel h t q) =
        E.boundedPlugSideLevel h t q := by rw [← mul_assoc, sgnR_mul_self, one_mul]
    have hpoint : (z, sgnR t * (sgnR t * E.boundedPlugSideLevel h t q)) =
        (z, E.boundedPlugSideLevel h t q) := Prod.ext rfl hraw
    have htube : E.boundedSplitTubeMap h hlin
        (z, sgnR t * (sgnR t * E.boundedPlugSideLevel h t q)) =
        E.boundedPlugSideLiftMap h hlin t q :=
      (congrArg (E.boundedSplitTubeMap h hlin) hpoint).trans hz
    refine ⟨q', hq', he.trans (hm.trans ?_)⟩
    exact congrArg (fun y : W.Carrier => (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCore
      (sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
        (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d) y)) htube
variable (hc : E.toTorus.components.count = 2) (hn : E.toTorus.pairing.count = 1)
  {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
  (havρ : ∀ r, Disjoint ((E.toTorus.external.shrink hρ hρ1).collar r).target d.target)

abbrev boundedPlugSideCanonicalMap (t : Bool) :=
  E.boundedPlugSideCappedMap h hlin d hs hI (E.toTorus.external.shrink hρ hρ1)
    (E.toTorus.external_exhausted.trans (E.toTorus.external.shrink_image hρ hρ1).symm) havρ t

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugSideSolidIndex_side (t : Bool) :
    (!sphereCutBoundarySide (boundedPlugSideSolidIndex t)) = t := by
  cases t <;> rfl

include heq in
set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugSideRealMap_mem_component {t : Bool} {q : ℂ × Circle}
    (hq : E.boundedPlugSideDom h t q) (hl : 0 < sgnR t * E.boundedPlugSideLevel h t q) :
    E.boundedPlugSideRealMap h hlin d hs hI (E.toTorus.external.shrink hρ hρ1)
      (E.toTorus.external_exhausted.trans (E.toTorus.external.shrink_image hρ hρ1).symm)
      havρ t q ∈ (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).piece
        (boundedPlugSideSolidIndex t) := by
  apply (E.fibrePlugCapComponents_core_mem h hlin hc hn d hs heq hρ hρ1 hI havρ _ _).mpr
  apply (E.fibrePlugCutComponents_piece h hlin hc hn d hs heq
    (boundedPlugSideSolidIndex t)).symm.subset
  apply Or.inl
  change sphereCutFold (boundedPlugCutCollars d) (E.boundedPlugSideRealLift h hlin d hs t q) ∈
    E.fibrePlugSide h hlin (!sphereCutBoundarySide (boundedPlugSideSolidIndex t))
  rw [boundedPlugSideSolidIndex_side, E.boundedPlugSideRealLift_fold h hlin d hs heq hq (by
    have hg : sgnR t * E.boundedPlugSideLevel h t q ≠ 0 := ne_of_gt hl
    exact fun he => hg (by rw [he, mul_zero]))]
  exact E.boundedPlugSideLift_mem_side h hlin hn t q hq hl

include heq in
set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugSideBallMap_mem_component (t : Bool) (x : EuclideanSpace ℝ (Fin 3))
    (hx : ‖x‖ ≤ 2) :
    boundedPlugSideBallMap d hs hI (E.toTorus.external.shrink hρ hρ1)
      (E.toTorus.external_exhausted.trans (E.toTorus.external.shrink_image hρ hρ1).symm)
      havρ E h hlin (boundedPlugSideSolidIndex t) x ∈
        (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).piece
          (boundedPlugSideSolidIndex t) := by
  by_cases hx1 : ‖x‖ ≤ 1
  · rw [boundedPlugSideBallMap_cap _ _ _ _ _ _ _ _ _ _ _ hx1]
    exact E.fibrePlugCapComponents_wholeCap_owned h hlin hc hn d hs heq hρ hρ1 hI havρ _ _
  · rw [boundedPlugSideBallMap_shell _ _ _ _ _ _ _ _ _ _ _ (lt_of_not_ge hx1)]
    apply (E.fibrePlugCapComponents_core_mem h hlin hc hn d hs heq hρ hρ1 hI havρ _ _).mpr
    apply (E.fibrePlugCutComponents_piece h hlin hc hn d hs heq
      (boundedPlugSideSolidIndex t)).symm.subset
    apply Or.inl
    change sphereCutFold (boundedPlugCutCollars d)
      (boundedPlugCapShellLift d hs E h hlin (boundedPlugSideSolidIndex t)
        (ULift.up (sphereDirection poleS2 x), ‖x‖)) ∈
        E.fibrePlugSide h hlin (!sphereCutBoundarySide (boundedPlugSideSolidIndex t))
    rw [boundedPlugSideSolidIndex_side, boundedPlugCapShellLift_fold d hs E h hlin heq _ _
      (lt_of_not_ge hx1)
      (by change ‖x‖ < 5 / 2; linarith)]
    change E.boundedSplitTubeMap h hlin
      ((sphereDirection poleS2 x), boundedPlugCapShellSign (boundedPlugSideSolidIndex t) *
        boundedPlugCapProfile ‖x‖) ∈ E.fibrePlugSide h hlin t
    rw [boundedPlugSideSolidIndex_sign]
    have hp0 : 0 < boundedPlugCapProfile ‖x‖ := by
      have hh := boundedPlugCapProfile_strictMono (lt_of_not_ge hx1)
      rw [boundedPlugCapProfile_inner (by norm_num : (1 : ℝ) ≤ 5 / 4)] at hh
      linarith
    have hp2 : boundedPlugCapProfile ‖x‖ ≤ 2 := by
      have hh := boundedPlugCapProfile_strictMono.monotone hx
      rwa [boundedPlugCapProfile_outer (by norm_num : (3 / 2 : ℝ) ≤ 2)] at hh
    apply E.fibrePlug_tube_side h hlin t
    · rw [SplitCharts.abs_sgnR_mul, abs_of_pos hp0]; linarith
    · rw [← mul_assoc, sgnR_mul_self, one_mul]; exact hp0

include heq in
set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugSideCanonicalMap_mem_component (t : Bool) {q : ℂ × Circle}
    (hq : ‖q.1‖ ≤ 3) :
    E.boundedPlugSideCanonicalMap h hlin d hs hI hρ hρ1 havρ t q ∈
      (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).piece
        (boundedPlugSideSolidIndex t) := by
  by_cases hf : ‖q.1‖ < 3 ∧ sgnR t * E.boundedPlugSideLevel h t q ≤ 2
  · rw [boundedPlugSideCanonicalMap, E.boundedPlugSideCappedMap_fake h hlin d hs hI
      (E.toTorus.external.shrink hρ hρ1) _ havρ hf.1 hf.2]
    apply E.boundedPlugSideBallMap_mem_component h hlin d hs hI heq hc hn hρ hρ1 havρ
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hh := E.boundedPlugSideFill_inverse_bound h hlin t q hf.1 hf.2
    linarith
  · have hl : 2 < sgnR t * E.boundedPlugSideLevel h t q := by
      by_cases h3 : ‖q.1‖ < 3
      · exact lt_of_not_ge (fun h2 => hf ⟨h3, h2⟩)
      · have hh := E.boundedPlugSideLevel_gt_three h t (q := q) (by linarith) hq
        linarith
    rw [boundedPlugSideCanonicalMap, E.boundedPlugSideCappedMap_real h hlin d hs hI
      (E.toTorus.external.shrink hρ hρ1) _ havρ hl]
    exact E.boundedPlugSideRealMap_mem_component h hlin d hs hI heq hc hn hρ hρ1 havρ
      ⟨hq, by linarith⟩ (by linarith)
include heq in
set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugSideCore_cover_component (t : Bool)
    (x : (boundedPlugCutCarrier d hs).Carrier)
    (hx : x ∈ (E.fibrePlugCutComponents h hlin hc hn d hs heq).piece
      (boundedPlugSideSolidIndex t)) :
    ∃ q : ℂ × Circle, ‖q.1‖ ≤ 3 ∧
      E.boundedPlugSideCanonicalMap h hlin d hs hI hρ hρ1 havρ t q =
        (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCore x := by
  let B := E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ
  let A' := E.toTorus.external.shrink hρ hρ1
  have hA' := E.toTorus.external_exhausted.trans (E.toTorus.external.shrink_image hρ hρ1).symm
  have hx' := (E.fibrePlugCutComponents_piece h hlin hc hn d hs heq
    (boundedPlugSideSolidIndex t)).subset hx
  rw [boundedPlugSideSolidIndex_side] at hx'
  rcases hx' with hx | ⟨z, rfl⟩
  · obtain ⟨q, hq, hl, he⟩ := E.boundedPlugSide_lift_cover h hlin hn t hx
    have hlev : E.boundedPlugSideLevel h t q ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hl
      exact lt_irrefl _ hl
    have ho : x ∈ sphereCutOffZero (boundedPlugCutCollars d) := by
      intro hz
      obtain ⟨k, z, hz⟩ := mem_iUnion.mp hz
      change d (z, 0) = sphereCutFold (boundedPlugCutCollars d) x at hz
      rw [heq] at hz
      have hnot : sphereCutFold (boundedPlugCutCollars d) x ∉
          range (fun z : SphereTwo => E.boundedSplitTubeMap h hlin (z, 0)) := by
        apply (E.fibrePlug_sphere_complement h hlin hn hc).symm.subset
        cases t
        · exact Or.inl hx
        · exact Or.inr hx
      exact hnot ⟨z.down, hz⟩
    have hreal : E.boundedPlugSideRealLift h hlin d hs t q = x := by
      refine sphereCutFold_injOn_offZero (boundedPlugCutCollars d)
        (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d) ?_ ho ?_
      · change sphereCutFold (boundedPlugCutCollars d)
          (E.boundedPlugSideRealLift h hlin d hs t q) ∉
            sphereCutAmbientZero (boundedPlugCutCollars d)
        rw [E.boundedPlugSideRealLift_fold h hlin d hs heq hq hlev]
        exact E.boundedPlugSideLift_offZero h hlin d heq hq hlev
      · exact (E.boundedPlugSideRealLift_fold h hlin d hs heq hq hlev).trans he
    obtain ⟨q', hq', hh⟩ := E.boundedPlugSideCappedMap_cover_real h hlin d hs hI A' hA' havρ
      hq hl
    refine ⟨q', hq', hh.trans ?_⟩
    exact congrArg B.sphereCapCore hreal
  · have hsphere : B.sphereMap (boundedPlugSideSolidIndex t) z =
        sphereCutZero (boundedPlugCutCollars d) 0
          (sphereCutBoundarySide (boundedPlugSideSolidIndex t)) z :=
      sphereCutFullCollar_zero _ _ _ _ _ _
    have ha := B.sphereCap_attachment (boundedPlugSideSolidIndex t) z
    rw [hsphere] at ha
    obtain ⟨y, hy, hm⟩ := (boundedPlugSideBallMap_cap_image d hs hI A' hA' havρ E h hlin
      (boundedPlugSideSolidIndex t)).symm.subset
        (mem_range_self (closureSphereToBall z))
    obtain ⟨q, hq, he⟩ := E.boundedPlugSideCappedMap_cover_ballMap h hlin d hs hI A' hA' havρ
      t y (by have hh := mem_closedBall_zero_iff.mp hy; linarith)
    exact ⟨q, hq, he.trans (hm.trans ha.symm)⟩

include heq in
set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugSideCanonicalMap_image (t : Bool) :
    E.boundedPlugSideCanonicalMap h hlin d hs hI hρ hρ1 havρ t ''
      {q : ℂ × Circle | ‖q.1‖ ≤ 3} =
        ((E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).piece
          (boundedPlugSideSolidIndex t) :
            Set (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.Carrier) := by
  let B := E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ
  let D := E.fibrePlugCutComponents h hlin hc hn d hs heq
  let A' := E.toTorus.external.shrink hρ hρ1
  have hA' := E.toTorus.external_exhausted.trans (E.toTorus.external.shrink_image hρ hρ1).symm
  apply Subset.antisymm
  · rintro y ⟨q, hq, rfl⟩
    exact E.boundedPlugSideCanonicalMap_mem_component h hlin d hs hI heq hc hn hρ hρ1 havρ t hq
  · intro y hy
    change y ∈ (B.sphereCapComponents D).piece (boundedPlugSideSolidIndex t) at hy
    have hy' := (B.sphereCapComponents_piece D (boundedPlugSideSolidIndex t)).subset hy
    rcases hy' with ⟨x, hx, rfl⟩ | hy
    · exact E.boundedPlugSideCore_cover_component h hlin d hs hI heq hc hn hρ hρ1 havρ t x hx
    · obtain ⟨k, hk, z, rfl⟩ := mem_iUnion.mp hy
      have howner := E.fibrePlugCutBoundary_sphere_owner h hlin hc hn d hs heq
        hρ hρ1 hI havρ k
      change B.sphereCapComponentOwner D k = k at howner
      rw [howner] at hk
      subst k
      obtain ⟨x, hx, hm⟩ := (boundedPlugSideBallMap_cap_image d hs hI A' hA' havρ E h hlin
        (boundedPlugSideSolidIndex t)).symm.subset (mem_range_self z)
      obtain ⟨q, hq, he⟩ := E.boundedPlugSideCappedMap_cover_ballMap h hlin d hs hI A' hA' havρ
        t x (by have hh := mem_closedBall_zero_iff.mp hx; linarith)
      exact ⟨q, hq, he.trans hm⟩

end GC.Seifert.ElementaryPresentation

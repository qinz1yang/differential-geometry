import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugSideFill
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugCutComponents

/-!
The actual bounded side solid map with its genuine produced filling and retained collar.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace GC.Seifert.ElementaryPresentation

open SplitTube

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
  (hlin : E.IsLinearSeam j)

def boundedPlugSideFillDiffeomorph (t : Bool) : E3 ≃ₘ[ℝ] E3 :=
  (E.exists_boundedPlugSideFill h hlin t).choose

theorem boundedPlugSideFill_inverse_bound (t : Bool) (q : ℂ × Circle) (h3 : ‖q.1‖ < 3)
    (h2 : sgnR t * E.boundedPlugSideLevel h t q ≤ 2) :
    ‖(E.boundedPlugSideFillDiffeomorph h hlin t).symm (torusPD q)‖ ≤ 1 :=
  (E.exists_boundedPlugSideFill h hlin t).choose_spec.1 q h3 h2

def boundedPlugSideFillGerm (t : Bool) : Set E3 :=
  (E.exists_boundedPlugSideFill h hlin t).choose_spec.2.2.choose

theorem boundedPlugSideFillGerm_spec (t : Bool) :
    IsOpen (E.boundedPlugSideFillGerm h hlin t) ∧
      sphere (0 : E3) 1 ⊆ E.boundedPlugSideFillGerm h hlin t ∧
      E.boundedPlugSideFillGerm h hlin t ⊆ shellSet ∧
      ∀ x ∈ E.boundedPlugSideFillGerm h hlin t,
        E.boundedPlugSideFillDiffeomorph h hlin t x = E.boundedPlugSideShellMap h hlin t x :=
  (E.exists_boundedPlugSideFill h hlin t).choose_spec.2.2.choose_spec

theorem boundedPlugSideLift_ne_tube {t : Bool} {q : ℂ × Circle}
    (hq : E.boundedPlugSideDom h t q) {z : S2} {lv : ℝ} (hlv : |lv| < 3)
    (hne : E.boundedPlugSideLevel h t q ≠ lv) :
    E.boundedPlugSideLiftMap h hlin t q ≠ E.boundedSplitTubeMap h hlin (z, lv) := by
  intro he
  obtain ⟨q', hq', h3, hlev, he'⟩ := E.boundedPlugSideLift_cover h hlin t z hlv
  rw [← he'] at he
  have hh := E.boundedPlugSideLiftMap_injOn h hlin t hq hq' he
  rw [hh] at hne
  exact hne hlev

variable (d : PartialDiffeomorph sphereSignedCollarModel W.model
  (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior) {n : ℕ} (A : BoundaryTori W n)
  (hA : W.model.boundary W.Carrier = A.image)
  (hav : ∀ i, Disjoint (A.collar i).target d.target)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))

def boundedPlugSideSolidIndex (t : Bool) : Fin 2 := if t then 0 else 1

theorem boundedPlugSideSolidIndex_sign (t : Bool) :
    boundedPlugCapShellSign (boundedPlugSideSolidIndex t) = sgnR t := by
  cases t <;> rfl

include heq in
theorem boundedPlugSideLift_offZero {t : Bool} {q : ℂ × Circle}
    (hq : E.boundedPlugSideDom h t q) (hlev : E.boundedPlugSideLevel h t q ≠ 0) :
    E.boundedPlugSideLiftMap h hlin t q ∉ sphereCutAmbientZero (boundedPlugCutCollars d) := by
  intro hz
  obtain ⟨k, z, he⟩ := mem_iUnion.mp hz
  change d (z, 0) = _ at he
  rw [heq] at he
  exact E.boundedPlugSideLift_ne_tube h hlin hq (by norm_num) hlev he.symm

def boundedPlugSideRealLift (t : Bool) (q : ℂ × Circle) :
    (boundedPlugCutCarrier d hs).Carrier :=
  sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
    (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)
    (E.boundedPlugSideLiftMap h hlin t q)

include heq in
theorem boundedPlugSideRealLift_fold {t : Bool} {q : ℂ × Circle}
    (hq : E.boundedPlugSideDom h t q) (hlev : E.boundedPlugSideLevel h t q ≠ 0) :
    sphereCutFold (boundedPlugCutCollars d) (E.boundedPlugSideRealLift h hlin d hs t q) =
      E.boundedPlugSideLiftMap h hlin t q :=
  sphereCutAmbientPartialDiffeomorph_fold _ _ _ _
    (E.boundedPlugSideLift_offZero h hlin d heq hq hlev)

include heq in
theorem boundedPlugSideRealLift_coreOpen {t : Bool} {q : ℂ × Circle}
    (hq : E.boundedPlugSideDom h t q) (hlev : E.boundedPlugSideLevel h t q ≠ 0) :
    E.boundedPlugSideRealLift h hlin d hs t q ∈
      (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCoreOpen := by
  intro hx
  obtain ⟨k, z, hz⟩ := mem_iUnion.mp hx
  have hf := congrArg (sphereCutFold (boundedPlugCutCollars d)) hz
  have hp : (z, halfZero) ∈ sphereHalfCollarSource := by change (0 : ℝ) < 1; norm_num
  change sphereCutFold (boundedPlugCutCollars d)
    (sphereCutFullCollar (boundedPlugCutCollars d) (boundedPlugCutCollars_source d hs)
      (boundedPlugCutCollars_disjoint d) 0 (sphereCutBoundarySide k) (z, halfZero)) = _ at hf
  rw [sphereCutFullCollar_fold _ _ _ _ _ _ hp] at hf
  rw [E.boundedPlugSideRealLift_fold h hlin d hs heq hq hlev] at hf
  have hh : d (z, 0) = E.boundedPlugSideLiftMap h hlin t q := by
    change d (z, if sphereCutBoundarySide k then -(0 : ℝ) else 0) = _ at hf
    simpa only [neg_zero, ite_self] using hf
  apply E.boundedPlugSideLift_offZero h hlin d heq hq hlev
  exact mem_iUnion.mpr ⟨0, z, hh⟩

def boundedPlugSideRealMap (t : Bool) (q : ℂ × Circle) :
    (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCarrier.Carrier :=
  (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCore
    (E.boundedPlugSideRealLift h hlin d hs t q)

def boundedPlugSideFakeMap (t : Bool) (q : ℂ × Circle) :
    (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCarrier.Carrier :=
  boundedPlugSideBallMap d hs hI A hA hav E h hlin (boundedPlugSideSolidIndex t)
    ((2 : ℝ) • (E.boundedPlugSideFillDiffeomorph h hlin t).symm (torusPD q))

def boundedPlugSideCappedMap (t : Bool) (q : ℂ × Circle) :
    (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCarrier.Carrier :=
  if ‖q.1‖ < 3 ∧ sgnR t * E.boundedPlugSideLevel h t q ≤ 2 then
    E.boundedPlugSideFakeMap h hlin d hs hI A hA hav t q
  else E.boundedPlugSideRealMap h hlin d hs hI A hA hav t q

include heq in
theorem boundedPlugSideRealLift_local {t : Bool} {q : ℂ × Circle}
    (hq : E.boundedPlugSideDom h t q) (h3 : ‖q.1‖ < 3)
    (hlev : E.boundedPlugSideLevel h t q ≠ 0) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (boundedPlugCutCarrier d hs).model ∞
      (E.boundedPlugSideRealLift h hlin d hs t) q := by
  have hx := E.boundedPlugSideLift_offZero h hlin d heq hq hlev
  have hsource : E.boundedPlugSideLiftMap h hlin t q ∈
      (sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
        (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)).source := by
    rw [sphereCutAmbientPartialDiffeomorph_source]
    exact hx
  exact (E.boundedPlugSideLiftMap_local h hlin t q hq h3).comp _ _
    ((sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
      (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)).isLocalDiffeomorphAt
        W.model (boundedPlugCutCarrier d hs).model ∞ hsource)

include heq in
theorem boundedPlugSideRealMap_local {t : Bool} {q : ℂ × Circle}
    (hq : E.boundedPlugSideDom h t q) (h3 : ‖q.1‖ < 3)
    (hlev : E.boundedPlugSideLevel h t q ≠ 0) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1))
      (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCarrier.model ∞
      (E.boundedPlugSideRealMap h hlin d hs hI A hA hav t) q := by
  let B := boundedPlugCutBoundary d hs hI A hA hav
  let := B.sphereCapQuotientChartedSpace
  let hx := E.boundedPlugSideRealLift_coreOpen h hlin d hs hI A hA hav heq hq hlev
  let y : B.sphereCapCoreOpen := ⟨E.boundedPlugSideRealLift h hlin d hs t q, hx⟩
  let P := B.sphereCapCoreOpenDiffeomorph B.exists_sphereCapQuotientAtlas.choose_spec.2 y
  have hys : E.boundedPlugSideRealLift h hlin d hs t q ∈ P.source := by
    rw [B.sphereCapCoreOpenDiffeomorph_source]
    exact hx
  have hl := E.boundedPlugSideRealLift_local h hlin d hs heq hq h3 hlev
  have hp := P.isLocalDiffeomorphAt (boundedPlugCutCarrier d hs).model (𝓡∂ 3) ∞ hys
  have hc := hl.comp (𝓡∂ 3) B.SphereCapQuotient hp
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (hg := hc)
  filter_upwards [hl.contMDiffAt.continuousAt.preimage_mem_nhds
    (B.sphereCapCoreOpen.isOpen.mem_nhds hx)] with x hx
  exact (B.sphereCapCoreOpenDiffeomorph_apply
    B.exists_sphereCapQuotientAtlas.choose_spec.2 y hx).symm

theorem boundedPlugSideFake_eq_real {t : Bool} {q : ℂ × Circle} (h3 : ‖q.1‖ < 3)
    (hV : (E.boundedPlugSideFillDiffeomorph h hlin t).symm (torusPD q) ∈
      E.boundedPlugSideFillGerm h hlin t) :
    E.boundedPlugSideFakeMap h hlin d hs hI A hA hav t q =
      E.boundedPlugSideRealMap h hlin d hs hI A hA hav t q := by
  set x := (E.boundedPlugSideFillDiffeomorph h hlin t).symm (torusPD q) with hx
  have hg := E.boundedPlugSideFillGerm_spec h hlin t
  have hxs := hg.2.2.1 hV
  obtain ⟨h1, h2, hlev⟩ := E.boundedPlugSideShellMap_spec h hlin t hxs
  have hGx : E.boundedPlugSideFillDiffeomorph h hlin t x = torusPD q :=
    (E.boundedPlugSideFillDiffeomorph h hlin t).apply_symm_apply _
  rw [hg.2.2.2 x hV] at hGx
  have hx4 : ‖(E.boundedPlugSideLiftInverse h hlin t
      (E.boundedSplitTubeMap h hlin (shellDir t x))).1‖ < 4 := by linarith [h1.1]
  have hq4 : ‖q.1‖ < 4 := by linarith
  have hq : E.boundedPlugSideLiftInverse h hlin t
      (E.boundedSplitTubeMap h hlin (shellDir t x)) = q := torusPD_injOn hx4 hq4 hGx
  rw [hq] at h2
  have hx0 : x ≠ 0 := fun hz => by have hh := hxs.1; rw [hz, norm_zero] at hh; linarith
  have hn : ‖(2 : ℝ) • x‖ = 2 * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  change boundedPlugSideBallMap d hs hI A hA hav E h hlin (boundedPlugSideSolidIndex t)
    ((2 : ℝ) • x) = _
  rw [boundedPlugSideBallMap_outer d hs hI A hA hav E h hlin _ _
    (by rw [hn]; linarith [hxs.1]), boundedPlugSideSolidIndex_sign]
  have hraw : (sphereDirection poleS2 ((2 : ℝ) • x), sgnR t * ‖(2 : ℝ) • x‖) =
      shellDir t x := by
    refine Prod.ext ?_ ?_
    · conv_lhs => rw [← norm_smul_sphereDirection poleS2 hx0, smul_smul]
      exact sphereDirection_pos_smul poleS2 _ (by positivity)
    · change sgnR t * ‖(2 : ℝ) • x‖ = 2 * sgnR t * ‖x‖
      rw [hn]
      ring
  exact congrArg (fun y : W.Carrier =>
    (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCore
      (sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
        (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d) y))
    ((congrArg (E.boundedSplitTubeMap h hlin) hraw).trans h2.symm)

theorem boundedPlugSideCappedMap_fake {t : Bool} {q : ℂ × Circle} (h3 : ‖q.1‖ < 3)
    (h2 : sgnR t * E.boundedPlugSideLevel h t q ≤ 2) :
    E.boundedPlugSideCappedMap h hlin d hs hI A hA hav t q =
      E.boundedPlugSideFakeMap h hlin d hs hI A hA hav t q :=
  ite_eq_left ⟨h3, h2⟩

theorem boundedPlugSideCappedMap_real {t : Bool} {q : ℂ × Circle}
    (h2 : 2 < sgnR t * E.boundedPlugSideLevel h t q) :
    E.boundedPlugSideCappedMap h hlin d hs hI A hA hav t q =
      E.boundedPlugSideRealMap h hlin d hs hI A hA hav t q :=
  ite_eq_right (fun hc => (not_le.mpr h2) hc.2)

theorem boundedPlugSideFillGerm_of_level {t : Bool} {q : ℂ × Circle} (h3 : ‖q.1‖ < 3)
    (h2 : sgnR t * E.boundedPlugSideLevel h t q = 2) :
    (E.boundedPlugSideFillDiffeomorph h hlin t).symm (torusPD q) ∈
      E.boundedPlugSideFillGerm h hlin t := by
  have hL : E.boundedPlugSideLevel h t q = 2 * sgnR t := by
    have hh := sgnR_mul_self t
    linear_combination sgnR t * h2 - E.boundedPlugSideLevel h t q * hh
  have hlev3 : |E.boundedPlugSideLevel h t q| < 3 := by
    rw [hL, mul_comm, SplitCharts.abs_sgnR_mul]
    norm_num
  have hqd : q ∈ E.boundedPlugSideLiftDomain h t := ⟨h3, by rw [h2]; norm_num⟩
  obtain ⟨p, hp⟩ := E.boundedPlugSideTube_cover h hlin t
    (E.boundedPlugSideDom_of_mem_domain h hqd) h3 hlev3
  have hpn : ‖(p : E3)‖ = 1 := norm_eq_of_mem_sphere p
  have hdir : shellDir t (p : E3) = (p, E.boundedPlugSideLevel h t q) := by
    refine Prod.ext ?_ ?_
    · change sphereDirection poleS2 (p : E3) = p
      have hh := sphereDirection_pos_smul poleS2 p one_pos
      rwa [one_smul] at hh
    · change 2 * sgnR t * ‖(p : E3)‖ = _
      rw [hpn, hL]
      ring
  have hg := E.boundedPlugSideFillGerm_spec h hlin t
  have hpV := hg.2.1 p.2
  have hG : E.boundedPlugSideFillDiffeomorph h hlin t (p : E3) = torusPD q := by
    rw [hg.2.2.2 _ hpV, boundedPlugSideShellMap, hdir, hp,
      E.boundedPlugSideLiftInverse_lift h hlin hqd]
  rw [← hG, Diffeomorph.symm_apply_apply]
  exact hpV

include heq in
theorem boundedPlugSideFakeMap_local {t : Bool} {q : ℂ × Circle} (h4 : ‖q.1‖ < 4)
    (h5 : ‖(2 : ℝ) • (E.boundedPlugSideFillDiffeomorph h hlin t).symm (torusPD q)‖ < 5 / 2) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1))
      (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCarrier.model ∞
      (E.boundedPlugSideFakeMap h hlin d hs hI A hA hav t) q := by
  let L : E3 ≃L[ℝ] E3 :=
    (LinearEquiv.smulOfUnit (Units.mk0 (2 : ℝ) (by norm_num))).toContinuousLinearEquiv
  have a1 := isLocalDiffeomorphAt_torusPD h4
  have a2 := a1.comp _ _ ((E.boundedPlugSideFillDiffeomorph h hlin t).symm.isLocalDiffeomorph
    (torusPD q))
  have a3 := a2.comp _ _ (L.toDiffeomorph.isLocalDiffeomorph
    ((E.boundedPlugSideFillDiffeomorph h hlin t).symm (torusPD q)))
  exact a3.comp _ _ (boundedPlugSideBallMap_local d hs hI A hA hav E h hlin heq
    (boundedPlugSideSolidIndex t) _ h5)

theorem boundedPlugSideCappedMap_eq_fake {t : Bool} {q : ℂ × Circle} (h3 : ‖q.1‖ < 3)
    (hV : (E.boundedPlugSideFillDiffeomorph h hlin t).symm (torusPD q) ∈
      E.boundedPlugSideFillGerm h hlin t) :
    E.boundedPlugSideCappedMap h hlin d hs hI A hA hav t q =
      E.boundedPlugSideFakeMap h hlin d hs hI A hA hav t q := by
  by_cases h2 : sgnR t * E.boundedPlugSideLevel h t q ≤ 2
  · exact E.boundedPlugSideCappedMap_fake h hlin d hs hI A hA hav h3 h2
  · rw [E.boundedPlugSideCappedMap_real h hlin d hs hI A hA hav (not_le.mp h2)]
    exact (E.boundedPlugSideFake_eq_real h hlin d hs hI A hA hav h3 hV).symm

include heq in
theorem boundedPlugSideCappedMap_local (t : Bool) (q : ℂ × Circle) (h3 : ‖q.1‖ < 3) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1))
      (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCarrier.model ∞
      (E.boundedPlugSideCappedMap h hlin d hs hI A hA hav t) q := by
  have hg := E.boundedPlugSideFillGerm_spec h hlin t
  have hct : ContinuousOn (fun q : ℂ × Circle =>
      (E.boundedPlugSideFillDiffeomorph h hlin t).symm (torusPD q)) {q | ‖q.1‖ < 4} :=
    (E.boundedPlugSideFillDiffeomorph h hlin t).symm.continuous.comp_continuousOn
      torusPD.toOpenPartialHomeomorph.continuousOn
  have hcn : Continuous fun q : ℂ × Circle => ‖q.1‖ := continuous_norm.comp continuous_fst
  have hO3 : IsOpen {q : ℂ × Circle | ‖q.1‖ < 3} := isOpen_lt hcn continuous_const
  by_cases hV : (E.boundedPlugSideFillDiffeomorph h hlin t).symm (torusPD q) ∈
      E.boundedPlugSideFillGerm h hlin t
  · have hU : IsOpen ({q : ℂ × Circle | ‖q.1‖ < 3} ∩
        (fun q : ℂ × Circle => (E.boundedPlugSideFillDiffeomorph h hlin t).symm (torusPD q)) ⁻¹'
          E.boundedPlugSideFillGerm h hlin t) :=
      (hct.mono fun q (hq : ‖q.1‖ < 3) => show ‖q.1‖ < 4 by linarith).isOpen_inter_preimage
        hO3 hg.1
    refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_
      (E.boundedPlugSideFakeMap_local h hlin d hs hI A hA hav heq
        (t := t) (q := q) (by linarith) ?_)
    · exact eventuallyEq_of_mem (hU.mem_nhds ⟨h3, hV⟩) fun q' hq' =>
        E.boundedPlugSideCappedMap_eq_fake h hlin d hs hI A hA hav hq'.1 hq'.2
    · rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith [(hg.2.2.1 hV).2]
  · rcases lt_trichotomy (sgnR t * E.boundedPlugSideLevel h t q) 2 with hlt | he | hgt
    · refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_
        (E.boundedPlugSideFakeMap_local h hlin d hs hI A hA hav heq
        (t := t) (q := q) (by linarith) ?_)
      · exact eventuallyEq_of_mem ((E.boundedPlugSideFakeSet_open h t).mem_nhds ⟨h3, hlt⟩)
          fun q' hq' => E.boundedPlugSideCappedMap_fake h hlin d hs hI A hA hav hq'.1 hq'.2.le
      · rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith [E.boundedPlugSideFill_inverse_bound h hlin t q h3 hlt.le]
    · exact absurd (E.boundedPlugSideFillGerm_of_level h hlin h3 he) hV
    · have hc : ContinuousOn (fun q : ℂ × Circle => sgnR t * E.boundedPlugSideLevel h t q)
          {q | ‖q.1‖ < 3} :=
        (continuousOn_const.mul (E.boundedPlugSideLevel_continuousOn h t)).mono fun q hq =>
          show ‖q.1‖ ≤ 3 from le_of_lt hq
      have hU : IsOpen ({q : ℂ × Circle | ‖q.1‖ < 3} ∩
          (fun q : ℂ × Circle => sgnR t * E.boundedPlugSideLevel h t q) ⁻¹' Ioi 2) :=
        hc.isOpen_inter_preimage hO3 isOpen_Ioi
      have hqd : E.boundedPlugSideDom h t q := ⟨h3.le, by linarith⟩
      have hne : E.boundedPlugSideLevel h t q ≠ 0 := by
        intro he
        rw [he, mul_zero] at hgt
        linarith
      refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_
        (E.boundedPlugSideRealMap_local h hlin d hs hI A hA hav heq hqd h3 hne)
      exact eventuallyEq_of_mem (hU.mem_nhds ⟨h3, hgt⟩) fun q' hq' =>
        E.boundedPlugSideCappedMap_real h hlin d hs hI A hA hav hq'.2

include heq in
theorem boundedPlugSideRealMap_injOn (t : Bool) :
    InjOn (E.boundedPlugSideRealMap h hlin d hs hI A hA hav t)
      {q | E.boundedPlugSideDom h t q ∧ E.boundedPlugSideLevel h t q ≠ 0} := by
  intro q hq q' hq' he
  let B := boundedPlugCutBoundary d hs hI A hA hav
  have hl : E.boundedPlugSideRealLift h hlin d hs t q =
      E.boundedPlugSideRealLift h hlin d hs t q' := B.sphereCapCore_injective he
  have hf := congrArg (sphereCutFold (boundedPlugCutCollars d)) hl
  rw [E.boundedPlugSideRealLift_fold h hlin d hs heq hq.1 hq.2,
    E.boundedPlugSideRealLift_fold h hlin d hs heq hq'.1 hq'.2] at hf
  exact E.boundedPlugSideLiftMap_injOn h hlin t hq.1 hq'.1 hf

include heq in
theorem boundedPlugSideRealMap_ne_ball {t : Bool} {q : ℂ × Circle}
    (hq : E.boundedPlugSideDom h t q) (hlev : E.boundedPlugSideLevel h t q ≠ 0)
    (i : Fin 2) (w : ClosedCell 3) :
    E.boundedPlugSideRealMap h hlin d hs hI A hA hav t q ≠
      (boundedPlugCutBoundary d hs hI A hA hav).sphereCapBall i w := by
  intro he
  let B := boundedPlugCutBoundary d hs hI A hA hav
  have hm : B.sphereCapCore (E.boundedPlugSideRealLift h hlin d hs t q) ∈
      range B.sphereCapCore ∩ range (B.sphereCapBall i) :=
    ⟨mem_range_self _, ⟨w, he.symm⟩⟩
  obtain ⟨z, hz⟩ := (B.sphereCapCore_ball_intersection i).subset hm
  have hc := B.sphereCapCore_injective hz
  exact E.boundedPlugSideRealLift_coreOpen h hlin d hs hI A hA hav heq hq hlev
    (mem_iUnion.mpr ⟨i, z, hc⟩)

include heq in
theorem boundedPlugSideFakeMap_ne_real {t : Bool} {q q' : ℂ × Circle} (h3 : ‖q.1‖ < 3)
    (h2 : sgnR t * E.boundedPlugSideLevel h t q ≤ 2)
    (hq' : E.boundedPlugSideDom h t q')
    (hgt : 2 < sgnR t * E.boundedPlugSideLevel h t q') :
    E.boundedPlugSideFakeMap h hlin d hs hI A hA hav t q ≠
      E.boundedPlugSideRealMap h hlin d hs hI A hA hav t q' := by
  intro he
  let B := boundedPlugCutBoundary d hs hI A hA hav
  let x := (2 : ℝ) • (E.boundedPlugSideFillDiffeomorph h hlin t).symm (torusPD q)
  have hx2 : ‖x‖ ≤ 2 := by
    dsimp only [x]
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [E.boundedPlugSideFill_inverse_bound h hlin t q h3 h2]
  have hne : E.boundedPlugSideLevel h t q' ≠ 0 := by
    intro he
    rw [he, mul_zero] at hgt
    linarith
  by_cases hx1 : ‖x‖ ≤ 1
  · have hm := boundedPlugSideBallMap_cap d hs hI A hA hav E h hlin
      (boundedPlugSideSolidIndex t) x hx1
    have hb := B.boundedPlugWholeCap_eq (boundedPlugSideSolidIndex t) ⟨x, hx1⟩
    exact E.boundedPlugSideRealMap_ne_ball h hlin d hs hI A hA hav heq hq' hne
      (boundedPlugSideSolidIndex t) (boundedPlugCapBallDiffeomorph ⟨x, hx1⟩)
        (he.symm.trans (hm.trans hb))
  · have hx1 : 1 < ‖x‖ := lt_of_not_ge hx1
    have hsh := boundedPlugSideBallMap_shell d hs hI A hA hav E h hlin
      (boundedPlugSideSolidIndex t) x hx1
    have hcore : B.sphereCapCore (boundedPlugCapShellLift d hs E h hlin
        (boundedPlugSideSolidIndex t) (ULift.up (sphereDirection poleS2 x), ‖x‖)) =
        B.sphereCapCore (E.boundedPlugSideRealLift h hlin d hs t q') := hsh.symm.trans he
    have hl := B.sphereCapCore_injective hcore
    have hf := congrArg (sphereCutFold (boundedPlugCutCollars d)) hl
    rw [boundedPlugCapShellLift_fold d hs E h hlin heq _ _ hx1 (by linarith),
      E.boundedPlugSideRealLift_fold h hlin d hs heq hq' hne] at hf
    have hp := boundedPlugCapShell_profile_bounds hx1 (by linarith : ‖x‖ < 5 / 2)
    have hp2 : boundedPlugCapProfile ‖x‖ ≤ 2 := by
      have hh := boundedPlugCapProfile_strictMono.monotone hx2
      rwa [boundedPlugCapProfile_outer (by norm_num : (3 / 2 : ℝ) ≤ 2)] at hh
    have ha : |sgnR t * boundedPlugCapProfile ‖x‖| < 3 := by
      rw [SplitCharts.abs_sgnR_mul, abs_of_pos hp.1]
      linarith
    have hlev : E.boundedPlugSideLevel h t q' ≠ sgnR t * boundedPlugCapProfile ‖x‖ := by
      intro he
      rw [he, ← mul_assoc, sgnR_mul_self, one_mul] at hgt
      linarith
    exact E.boundedPlugSideLift_ne_tube h hlin hq' ha hlev
      (hf.symm.trans (congrArg (E.boundedSplitTubeMap h hlin) (Prod.ext rfl (by
        exact congrArg (fun v => v * boundedPlugCapProfile ‖x‖)
          (boundedPlugSideSolidIndex_sign t)))))

include heq in
theorem boundedPlugSideCappedMap_injOn (t : Bool) :
    InjOn (E.boundedPlugSideCappedMap h hlin d hs hI A hA hav t)
      {q : ℂ × Circle | ‖q.1‖ ≤ 3} := by
  intro q hq q' hq' he
  have hcases (q : ℂ × Circle) (hq : ‖q.1‖ ≤ 3) :
      (‖q.1‖ < 3 ∧ sgnR t * E.boundedPlugSideLevel h t q ≤ 2 ∧
        E.boundedPlugSideCappedMap h hlin d hs hI A hA hav t q =
          E.boundedPlugSideFakeMap h hlin d hs hI A hA hav t q) ∨
      (E.boundedPlugSideDom h t q ∧ 2 < sgnR t * E.boundedPlugSideLevel h t q ∧
        E.boundedPlugSideCappedMap h hlin d hs hI A hA hav t q =
          E.boundedPlugSideRealMap h hlin d hs hI A hA hav t q) := by
    by_cases hc : ‖q.1‖ < 3 ∧ sgnR t * E.boundedPlugSideLevel h t q ≤ 2
    · exact Or.inl ⟨hc.1, hc.2, E.boundedPlugSideCappedMap_fake h hlin d hs hI A hA hav
        hc.1 hc.2⟩
    · have hgt : 2 < sgnR t * E.boundedPlugSideLevel h t q := by
        by_cases hr : ‖q.1‖ < 3
        · exact lt_of_not_ge (fun h2 => hc ⟨hr, h2⟩)
        · linarith [E.boundedPlugSideLevel_gt_three h t (by linarith) hq]
      exact Or.inr ⟨⟨hq, by linarith⟩, hgt,
        E.boundedPlugSideCappedMap_real h hlin d hs hI A hA hav hgt⟩
  rcases hcases q hq with ⟨h3, h2, hqv⟩ | ⟨hd, hgt, hqv⟩ <;>
    rcases hcases q' hq' with ⟨h3', h2', hqv'⟩ | ⟨hd', hgt', hqv'⟩ <;> rw [hqv, hqv'] at he
  · have hn (r : ℂ × Circle) (hr : ‖r.1‖ < 3)
        (h2r : sgnR t * E.boundedPlugSideLevel h t r ≤ 2) :
        (2 : ℝ) • (E.boundedPlugSideFillDiffeomorph h hlin t).symm (torusPD r) ∈
          ball (0 : E3) (5 / 2) := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith [E.boundedPlugSideFill_inverse_bound h hlin t r hr h2r]
    have hh := boundedPlugSideBallMap_injOn d hs hI A hA hav E h hlin heq
      (boundedPlugSideSolidIndex t) (hn q h3 h2) (hn q' h3' h2') he
    have hs := smul_right_injective E3 (by norm_num : (2 : ℝ) ≠ 0) hh
    have ht := (E.boundedPlugSideFillDiffeomorph h hlin t).symm.injective hs
    have hq4 : ‖q.1‖ < 4 := by linarith
    have hq4' : ‖q'.1‖ < 4 := by linarith
    exact torusPD_injOn hq4 hq4' ht
  · exact (E.boundedPlugSideFakeMap_ne_real h hlin d hs hI A hA hav heq
      h3 h2 hd' hgt' he).elim
  · exact (E.boundedPlugSideFakeMap_ne_real h hlin d hs hI A hA hav heq
      h3' h2' hd hgt he.symm).elim
  · have hn (r : ℂ × Circle) (hg : 2 < sgnR t * E.boundedPlugSideLevel h t r) :
        E.boundedPlugSideLevel h t r ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hg
      linarith
    exact E.boundedPlugSideRealMap_injOn h hlin d hs hI A hA hav heq t
      ⟨hd, hn q hgt⟩ ⟨hd', hn q' hgt'⟩ he

theorem boundedPlugSideCappedMap_collar (t : Bool) (p : Torus) {s : ℝ}
    (hs0 : 0 ≤ s) (hs3 : s < 1 / 3) (hδ : s < (E.splitData h).δ) :
    E.boundedPlugSideCappedMap h hlin d hs hI A hA hav t
      ((3 - 3 * s / 2 : ℝ) • (p.1 : ℂ), p.2) =
        (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCore
          (sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
            (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)
            (E.toTorus.cutMap (E.toTorus.sideCollar (E.boundedPlugSidePort h t)
              (germHol ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
                (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁ p,
                halfPoint s hs0)))) := by
  have hn := norm_three_sub_smul (s := s) (by linarith) p.1
  have hlev := E.boundedPlugSideLevel_gt_three h t (q :=
    ((3 - 3 * s / 2 : ℝ) • (p.1 : ℂ), p.2)) (by dsimp only; rw [hn]; linarith)
      (by dsimp only; rw [hn]; linarith)
  rw [E.boundedPlugSideCappedMap_real h hlin d hs hI A hA hav (by linarith)]
  exact congrArg (fun y : W.Carrier =>
    (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCore
      (sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
        (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d) y))
    (E.boundedPlugSideLiftMap_collar h hlin t p hs0 hs3 hδ)

theorem boundedPlugSideLiftMap_external (hc : E.toTorus.components.count = 2)
    (hn : E.toTorus.pairing.count = 1) (t : Bool) (p : Torus) {s : ℝ}
    (hs0 : 0 ≤ s) (hs3 : s < 1 / 3) (hδ : s < (E.splitData h).δ) :
    E.boundedPlugSideLiftMap h hlin t ((3 - 3 * s / 2 : ℝ) • (p.1 : ℂ), p.2) =
      E.toTorus.external.collar (E.fibrePlugSideExternalEquiv h hc hn t)
        (germHol ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
          (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁ p,
          halfPoint s hs0) := by
  let τ := germHol ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
    (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁ p
  have hp : (τ, halfPoint s hs0) ∈ halfCollarSource := by change s < 1; linarith
  have hh := (E.splitData h).hH (sidePort (E.boundedPlugSideHost h) t)
    (τ, halfPoint s hs0) hp hδ
  have hv := congrArg (fun z => E.toTorus.cutMap z.val) hh
  rw [E.toTorus.pieceCollar_apply _ _ hp] at hv
  have he := E.fibrePlug_external_germ h hc (E.fibrePlugSideExternalEquiv h hc hn t)
    (τ, halfPoint s hs0) hp hδ
  rw [E.fibrePlugSideExternalEquiv_port h hc hn] at he
  exact (E.boundedPlugSideLiftMap_collar h hlin t p hs0 hs3 hδ).trans (hv.trans he.symm)

theorem boundedPlugSideCappedMap_retained_collar (hc : E.toTorus.components.count = 2)
    (hn : E.toTorus.pairing.count = 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (havρ : ∀ r, Disjoint ((E.toTorus.external.shrink hρ hρ1).collar r).target d.target)
    (t : Bool) (p : Torus) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hs3 : ρ * s < 1 / 3) (hδ : ρ * s < (E.splitData h).δ) :
    let B := E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ
    E.boundedPlugSideCappedMap h hlin d hs hI (E.toTorus.external.shrink hρ hρ1)
      (E.toTorus.external_exhausted.trans
        (E.toTorus.external.shrink_image hρ hρ1).symm) havρ t
      ((3 - 3 * (ρ * s) / 2 : ℝ) • (p.1 : ℂ), p.2) =
        B.sphereCapRetained.collar (E.fibrePlugSideExternalEquiv h hc hn t)
          (germHol ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
            (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁ p,
            halfPoint s hs0) := by
  let B := E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ
  let τ := germHol ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
    (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁ p
  let r := E.fibrePlugSideExternalEquiv h hc hn t
  have hp : (τ, halfPoint s hs0) ∈ halfCollarSource := hs1
  have hl := E.boundedPlugSideLiftMap_external h hlin hc hn t p
    (mul_nonneg hρ.le hs0) hs3 hδ
  have hret := B.sphereCapRetained_collar r hp
  have hcEq : B.tori.collar r (τ, halfPoint s hs0) =
      sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
        (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)
        (E.toTorus.external.collar r (τ, halfPoint (ρ * s) (mul_nonneg hρ.le hs0))) := by
    change sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
      (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)
      ((E.toTorus.external.shrink hρ hρ1).collar r (τ, halfPoint s hs0)) = _
    rw [BoundaryTori.shrink_collar_apply, halfSpaceScale_halfPoint]
  have hnative : E.boundedPlugSideCappedMap h hlin d hs hI
      (E.toTorus.external.shrink hρ hρ1)
      (E.toTorus.external_exhausted.trans
        (E.toTorus.external.shrink_image hρ hρ1).symm) havρ t
      ((3 - 3 * (ρ * s) / 2 : ℝ) • (p.1 : ℂ), p.2) =
        B.sphereCapCore (sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
          (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)
          (E.toTorus.external.collar r (τ, halfPoint (ρ * s) (mul_nonneg hρ.le hs0)))) := by
    have hn := norm_three_sub_smul (s := ρ * s) (by linarith [mul_nonneg hρ.le hs0]) p.1
    have hgt := E.boundedPlugSideLevel_gt_three h t (q :=
      ((3 - 3 * (ρ * s) / 2 : ℝ) • (p.1 : ℂ), p.2))
      (by dsimp only; rw [hn]; linarith) (by dsimp only; rw [hn]; linarith [mul_nonneg hρ.le hs0])
    rw [E.boundedPlugSideCappedMap_real h hlin d hs hI
      (E.toTorus.external.shrink hρ hρ1)
      (E.toTorus.external_exhausted.trans
        (E.toTorus.external.shrink_image hρ hρ1).symm) havρ (by linarith)]
    exact congrArg (fun y : W.Carrier => B.sphereCapCore
      (sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
        (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d) y)) hl
  exact hnative.trans ((congrArg B.sphereCapCore hcEq).symm.trans hret.symm)

end GC.Seifert.ElementaryPresentation

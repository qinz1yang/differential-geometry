import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSideDataFill
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelSolidInj

/-!
# Local diffeomorphism, collar and injectivity of the capped solid torus of a mixed split

Lane N2f, tier 2. The texts of `MoveSplitCappedSideModelSolidLocal` and
`MoveSplitCappedSideModelSolidInj` for a mixed split site: `solMap` is a local diffeomorphism on
the open model solid torus (`isLocalDiffeomorphAt_solMap`), reads the host collar of the port near
radius three (`solMap_collar`), is injective on the closed model solid torus (`solMap_injOn`), and
the two sides take a common value only at boundary points of both model solid tori
(`solMap_cross`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace GC.Seifert.RelativeNormalization.MixedStage

open GC.Seifert.ElementaryPresentation (clampDisc clampPants clampDisc_val clampPants_val
  discCollar_eq pantsCollar_eq isLocalDiffeomorphAt_clampDisc isLocalDiffeomorphAt_clampPants
  sideHeight sideHeight_not sideHeight_neg seamRadius_one OnSolidBoundary neg_three_lt_sgnR_mul
  sgnR_mul_lt_three sqrt_three_half_sq sqrt_three_half_lt_one seamHeight_pos_of_lt
  seamHeight_sqrt_three_half seamHeight_neg_sqrt_three_half exists_bandHeight_eq
  abs_sgnR_mul_of_pos sgnR_false sgnR_true)

section

open SplitTube

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q}
  {j : Fin σ.toTorus.pairing.count} {b : Bool} {h : σ.IsSplitSeam j b} {SD : σ.SplitData h}
  {hlin : σ.IsLinearSeam j}
  {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N (σ.splitSeamTube SD hlin)}

namespace SideCap

variable {t : Bool} (S : σ.SideCap h SD hlin K t)

theorem symm_mem_V_of_level {q : ℂ × Circle} (h3 : ‖q.1‖ < 3)
    (h2 : sgnR t * σ.sideLevel h t q = 2) : S.G.symm (torusPD q) ∈ S.V := by
  have hL : σ.sideLevel h t q = 2 * sgnR t := by
    have := sgnR_mul_self t
    linear_combination sgnR t * h2 - σ.sideLevel h t q * this
  have hlev3 : |σ.sideLevel h t q| < 3 := by
    rw [hL, mul_comm, SplitCharts.abs_sgnR_mul]
    norm_num
  have hqd : q ∈ σ.liftDom h t := ⟨h3, by rw [h2]; norm_num⟩
  obtain ⟨p, hp⟩ := σ.exists_tubeMap_eq_liftMap h SD hlin t (σ.sideDom_of_mem_liftDom h hqd) hlev3
  have hpn : ‖(p : E3)‖ = 1 := norm_eq_of_mem_sphere p
  have hdir : shellDir t (p : E3) = (p, σ.sideLevel h t q) := by
    refine Prod.ext ?_ ?_
    · change Manifold.sphereDirection poleS2 (p : E3) = p
      have := Manifold.sphereDirection_pos_smul poleS2 p one_pos
      rwa [one_smul] at this
    · change 2 * sgnR t * ‖(p : E3)‖ = _
      rw [hpn, hL]
      ring
  have hpV : (p : E3) ∈ S.V := S.V_sphere p.2
  have hG : S.G (p : E3) = torusPD q := by
    rw [S.G_shell _ hpV, shellMap, hdir, hp, σ.liftInv_liftMap h SD hlin hqd]
  rw [← hG, S.G.symm_apply_apply]
  exact hpV

def fakeMap (q : ℂ × Circle) : N.Carrier := S.Φ ((2 : ℝ) • S.G.symm (torusPD q))

theorem norm_two_smul (x : E3) : ‖(2 : ℝ) • x‖ = 2 * ‖x‖ := by
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

theorem isLocalDiffeomorphAt_fakeMap {q : ℂ × Circle} (h4 : ‖q.1‖ < 4)
    (h5 : ‖(2 : ℝ) • S.G.symm (torusPD q)‖ < 5 / 2) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ S.fakeMap q := by
  let L : E3 ≃L[ℝ] E3 :=
    (LinearEquiv.smulOfUnit (Units.mk0 (2 : ℝ) (by norm_num))).toContinuousLinearEquiv
  have a1 : IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ torusPD q :=
    isLocalDiffeomorphAt_torusPD h4
  have a2 := a1.comp _ _ (S.G.symm.isLocalDiffeomorph (torusPD q))
  have a3 := a2.comp _ _ (L.toDiffeomorph.isLocalDiffeomorph (S.G.symm (torusPD q)))
  exact a3.comp _ _ (S.loc _ h5)

theorem solMap_eq_fakeMap_of_mem {q : ℂ × Circle} (h3 : ‖q.1‖ < 3)
    (hV : S.G.symm (torusPD q) ∈ S.V) : S.solMap q = S.fakeMap q := by
  by_cases h2 : sgnR t * σ.sideLevel h t q ≤ 2
  · exact S.solMap_of_fake h3 h2
  · rw [S.solMap_of_real (not_le.mp h2)]
    exact (S.fake_eq_real h3 hV).symm

theorem continuousOn_symm_torusPD :
    ContinuousOn (fun q : ℂ × Circle => S.G.symm (torusPD q)) {q | ‖q.1‖ < 4} :=
  S.G.symm.continuous.comp_continuousOn torusPD.toOpenPartialHomeomorph.continuousOn

theorem isLocalDiffeomorphAt_solMap {q : ℂ × Circle} (h3 : ‖q.1‖ < 3) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ S.solMap q := by
  have hcn : Continuous fun q : ℂ × Circle => ‖q.1‖ := continuous_norm.comp continuous_fst
  have hO3 : IsOpen {q : ℂ × Circle | ‖q.1‖ < 3} := isOpen_lt hcn continuous_const
  by_cases hV : S.G.symm (torusPD q) ∈ S.V
  · have hU : IsOpen ({q : ℂ × Circle | ‖q.1‖ < 3} ∩
        (fun q : ℂ × Circle => S.G.symm (torusPD q)) ⁻¹' S.V) :=
      (S.continuousOn_symm_torusPD.mono fun q (hq : ‖q.1‖ < 3) =>
        show ‖q.1‖ < 4 by linarith).isOpen_inter_preimage hO3 S.V_open
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (S.isLocalDiffeomorphAt_fakeMap
      (by linarith) ?_)
    · exact eventuallyEq_of_mem (hU.mem_nhds ⟨h3, hV⟩) fun q' hq' =>
        S.solMap_eq_fakeMap_of_mem hq'.1 hq'.2
    · rw [norm_two_smul]
      linarith [(S.V_shell hV).2]
  · rcases lt_trichotomy (sgnR t * σ.sideLevel h t q) 2 with hlt | heq | hgt
    · refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (S.isLocalDiffeomorphAt_fakeMap
        (by linarith) ?_)
      · exact eventuallyEq_of_mem ((σ.isOpen_fakeSet h t).mem_nhds ⟨h3, hlt⟩) fun q' hq' =>
          S.solMap_of_fake hq'.1 hq'.2.le
      · linarith [S.norm_two_smul_le h3 hlt.le]
    · exact absurd (S.symm_mem_V_of_level h3 heq) hV
    · have hc : ContinuousOn (fun q : ℂ × Circle => sgnR t * σ.sideLevel h t q)
          {q | ‖q.1‖ < 3} :=
        (continuousOn_const.mul (σ.continuousOn_sideLevel h t)).mono fun q hq =>
          show ‖q.1‖ ≤ 3 from le_of_lt hq
      have hU : IsOpen ({q : ℂ × Circle | ‖q.1‖ < 3} ∩
          (fun q : ℂ × Circle => sgnR t * σ.sideLevel h t q) ⁻¹' Ioi 2) :=
        hc.isOpen_inter_preimage hO3 isOpen_Ioi
      have hqd : q ∈ σ.liftDom h t := ⟨h3, by linarith⟩
      have hlev : 1 < |σ.sideLevel h t q| := by
        rw [← SplitCharts.abs_sgnR_mul t]
        exact lt_of_lt_of_le (by linarith) (le_abs_self _)
      refine IsLocalDiffeomorphAt.of_eventuallyEq ?_
        (isLocalDiffeomorphAt_coreMap_liftMap (hlin := hlin) (K := K) hqd hlev)
      exact eventuallyEq_of_mem (hU.mem_nhds ⟨h3, hgt⟩) fun q' hq' =>
        S.solMap_of_real (hq'.2 : sgnR t * σ.sideLevel h t q' ∈ Ioi 2)

theorem solMap_collar {q : ℂ × Circle} (h1 : 5 / 2 ≤ ‖q.1‖) (h3 : ‖q.1‖ ≤ 3) :
    S.solMap q = coreMap K (σ.hostMap SD (planarCollarFormula 3 (sidePort (σ.hostSide h) t)
      (((q.2⁻¹ : Circle) : ℂ), collarDepth ‖q.1‖), σ.liftFib h SD hlin q)) := by
  have hlev := σ.three_lt_sideLevel_of_ge h t h1 h3
  rw [S.solMap_of_real (by linarith), SplitCharts.liftMap_of_gt _ t (by linarith)]
  unfold SplitCharts.liftH
  rw [sideData_point_collar _ t h1 (by linarith), hostChart_hostInv]
  rfl

end SideCap

end

section

open SplitTube

section Cross

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {j : Fin σ.toTorus.pairing.count} {b : Bool} (h : σ.IsSplitSeam j b) (SD : σ.SplitData h)
  (hlin : σ.IsLinearSeam j)

theorem sideLevel_eq_of_le (t t' : Bool) {q : ℂ × Circle} (h2 : ‖q.1‖ ≤ 2) :
    σ.sideLevel h t q = σ.sideLevel h t' q := by
  rw [σ.sideLevel_of_le h t h2, σ.sideLevel_of_le h t' h2]

theorem sideLevel_eq_of_liftPt_eq {t t' : Bool} {q q' : ℂ × Circle} (hq : σ.sideDom h t q)
    (hq' : σ.sideDom h t' q') (he : σ.liftPt h SD hlin t q = σ.liftPt h SD hlin t' q') :
    σ.sideLevel h t q = σ.sideLevel h t' q' := by
  have he₀ := (σ.splitCharts SD hlin).he₀
  unfold liftPt at he
  by_cases h1 : ‖q.1‖ ≤ 3 / 2 <;> by_cases h1' : ‖q'.1‖ ≤ 3 / 2
  · simp only [h1, h1', ↓reduceIte] at he
    have hn : ∀ z : ℂ, ‖z‖ ≤ 3 / 2 → ‖(2 : ℝ) • z‖ ≤ 3 := fun z hz => by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    obtain ⟨e1, e2⟩ := σ.solidPt_inj h SD (hn _ h1) (hn _ h1') he
    have hqq : q = q' := by
      refine Prod.ext (smul_right_injective ℂ (by norm_num : (2 : ℝ) ≠ 0) e1) ?_
      rw [← zpow_zpow_unit he₀ q.2, e2, zpow_zpow_unit he₀]
    subst hqq
    exact σ.sideLevel_eq_of_le h t t' (by linarith)
  · simp only [h1, h1', ↓reduceIte] at he
    exact absurd he (σ.solidPt_ne_hostPt h SD _ _ _ _)
  · simp only [h1, h1', ↓reduceIte] at he
    exact absurd he.symm (σ.solidPt_ne_hostPt h SD _ _ _ _)
  · simp only [h1, h1', ↓reduceIte] at he
    push Not at h1 h1'
    obtain ⟨e1, -⟩ := σ.hostPt_inj h SD (σ.hostChart_point_mem_planarModel h hq h1.le)
      (σ.hostChart_point_mem_planarModel h hq' h1'.le) he
    have e3 := congrArg (hostInv (σ.hostSide h)) e1
    rw [hostInv_hostChart, hostInv_hostChart] at e3
    unfold sideLevel
    rw [e3]

theorem liftMap_cross {t t' : Bool} {q q' : ℂ × Circle} (hq : σ.sideDom h t q)
    (hq' : σ.sideDom h t' q')
    (he : (σ.splitCharts SD hlin).liftMap t q = (σ.splitCharts SD hlin).liftMap t' q') :
    σ.sideLevel h t q = σ.sideLevel h t' q' ∨ (‖q.1‖ = 3 ∧ ‖q'.1‖ = 3) := by
  have he₀ := (σ.splitCharts SD hlin).he₀
  rw [σ.liftMap_eq_cutMap, σ.liftMap_eq_cutMap] at he
  by_cases hi : σ.toTorus.cutCarrier.model.IsInteriorPoint (σ.liftPt h SD hlin t q)
  · exact Or.inl (σ.sideLevel_eq_of_liftPt_eq h SD hlin hq hq'
      (σ.toTorus.cutMap_eq_of_isInteriorPoint hi he))
  by_cases hi' : σ.toTorus.cutCarrier.model.IsInteriorPoint (σ.liftPt h SD hlin t' q')
  · exact Or.inl (σ.sideLevel_eq_of_liftPt_eq h SD hlin hq' hq
      (σ.toTorus.cutMap_eq_of_isInteriorPoint hi' he.symm)).symm
  rcases σ.liftPt_radius h SD hlin hq hi with h1 | h1 <;>
    rcases σ.liftPt_radius h SD hlin hq' hi' with h1' | h1'
  · left
    rw [σ.liftPt_of_three_halves h SD hlin t h1, σ.liftPt_of_three_halves h SD hlin t' h1'] at he
    have e := Prod.ext_iff.mp (σ.toTorus.eq_of_cutMap_sideCollar_eq he)
    have e2 : q.2 ^ (σ.splitCharts SD hlin).e₀ = q'.2 ^ (σ.splitCharts SD hlin).e₀ := e.2
    have hqq : q = q' := by
      refine Prod.ext (eq_of_norm_eq_of_unitOf_eq (by rw [h1, h1']) e.1) ?_
      rw [← zpow_zpow_unit he₀ q.2, e2, zpow_zpow_unit he₀]
    subst hqq
    exact σ.sideLevel_eq_of_le h t t' (by linarith)
  · rw [σ.liftPt_of_three_halves h SD hlin t h1, σ.liftPt_of_three h SD hlin t' h1'] at he
    exact absurd he (σ.cutMap_seamSide_ne_portSide h t' _ _)
  · rw [σ.liftPt_of_three h SD hlin t h1, σ.liftPt_of_three_halves h SD hlin t' h1'] at he
    exact absurd he.symm (σ.cutMap_seamSide_ne_portSide h t _ _)
  · exact Or.inr ⟨h1, h1'⟩

end Cross

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q}
  {j : Fin σ.toTorus.pairing.count} {b : Bool} {h : σ.IsSplitSeam j b} {SD : σ.SplitData h}
  {hlin : σ.IsLinearSeam j}
  {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N (σ.splitSeamTube SD hlin)}

theorem one_lt_abs_sideLevel {t : Bool} {q : ℂ × Circle} (h2 : 2 < sgnR t * σ.sideLevel h t q) :
    1 < |σ.sideLevel h t q| := by
  rw [← SplitCharts.abs_sgnR_mul t]
  exact lt_of_lt_of_le (by linarith) (le_abs_self _)

theorem coreMap_liftMap_ne_cap {t : Bool} {q : ℂ × Circle} (hq : σ.sideDom h t q)
    (hlev : 1 < |σ.sideLevel h t q|) (c : (σ.splitSeamTube SD hlin).Boundary)
    (w : ClosedCell 3) : coreMap K ((σ.splitCharts SD hlin).liftMap t q) ≠ K.cap c w := by
  rw [coreMap_of_mem K (liftMap_mem_core hq hlev)]
  exact coreInclusion_ne_cap_of_forall_ne K _ (fun c' z => liftMap_ne_boundarySphere hq hlev c' z)
    c w

theorem coreMap_liftMap_ne_tubeMap {t : Bool} {q : ℂ × Circle} (hq : σ.sideDom h t q)
    (hlev : 1 < |σ.sideLevel h t q|) {z : S2} {lv : ℝ} (h1 : 1 ≤ |lv|) (h3 : |lv| < 3)
    (hne : σ.sideLevel h t q ≠ lv) :
    coreMap K ((σ.splitCharts SD hlin).liftMap t q) ≠
      coreMap K ((σ.splitCharts SD hlin).tubeMap (z, lv)) := by
  intro he
  exact liftMap_ne_tubeMap hq h3 hne (coreMap_injOn K (liftMap_mem_core hq hlev)
    ((σ.splitCharts SD hlin).tubeMap_mem_core (q := (z, lv)) h1 h3) he)

namespace SideCap

variable {t : Bool} (S : σ.SideCap h SD hlin K t)

theorem ball_cases {x : E3} (hx : ‖x‖ ≤ 2) :
    (∃ w, S.Φ x = K.cap ((), t) w) ∨ ∃ z : S2, 1 < ‖x‖ ∧
      S.Φ x = coreMap K ((σ.splitCharts SD hlin).tubeMap (z, sgnR t * ‖x‖)) := by
  by_cases h1 : ‖x‖ ≤ 1
  · exact Or.inl (S.cap_in x h1)
  · push Not at h1
    obtain ⟨z, hz⟩ := S.shell x h1.le (by linarith)
    exact Or.inr ⟨z, h1, hz⟩

theorem fakeMap_cases {q : ℂ × Circle} (h3 : ‖q.1‖ < 3) (h2 : sgnR t * σ.sideLevel h t q ≤ 2) :
    (∃ w, S.fakeMap q = K.cap ((), t) w) ∨ ∃ z : S2, ∃ r : ℝ, 1 < r ∧ r ≤ 2 ∧
      S.fakeMap q = coreMap K ((σ.splitCharts SD hlin).tubeMap (z, sgnR t * r)) := by
  rcases S.ball_cases (S.norm_two_smul_le h3 h2) with hc | ⟨z, h1, hz⟩
  · exact Or.inl hc
  · exact Or.inr ⟨z, _, h1, S.norm_two_smul_le h3 h2, hz⟩

theorem fakeMap_ne_coreMap_liftMap {t' : Bool} {q q' : ℂ × Circle} (h3 : ‖q.1‖ < 3)
    (h2 : sgnR t * σ.sideLevel h t q ≤ 2) (hq' : σ.sideDom h t' q')
    (hlev : 1 < |σ.sideLevel h t' q'|)
    (hne : ∀ r : ℝ, 1 < r → r ≤ 2 → σ.sideLevel h t' q' ≠ sgnR t * r) :
    S.fakeMap q ≠ coreMap K ((σ.splitCharts SD hlin).liftMap t' q') := by
  rcases S.fakeMap_cases h3 h2 with ⟨w, hw⟩ | ⟨z, r, h1, hr2, hz⟩
  · rw [hw]
    exact (coreMap_liftMap_ne_cap hq' hlev _ w).symm
  · rw [hz]
    have habs := abs_sgnR_mul_of_pos t (show 0 < r by linarith)
    exact (coreMap_liftMap_ne_tubeMap hq' hlev (by rw [habs]; linarith) (by rw [habs]; linarith)
      (hne r h1 hr2)).symm

theorem fakeMap_inj {q q' : ℂ × Circle} (h3 : ‖q.1‖ < 3) (h2 : sgnR t * σ.sideLevel h t q ≤ 2)
    (h3' : ‖q'.1‖ < 3) (h2' : sgnR t * σ.sideLevel h t q' ≤ 2)
    (he : S.fakeMap q = S.fakeMap q') : q = q' := by
  have hb := S.norm_two_smul_le h3 h2
  have hb' := S.norm_two_smul_le h3' h2'
  have e1 := S.inj (mem_ball_zero_iff.mpr (by linarith)) (mem_ball_zero_iff.mpr (by linarith)) he
  have e2 := smul_right_injective E3 (by norm_num : (2 : ℝ) ≠ 0) e1
  have e3 := S.G.symm.injective e2
  exact torusPD_injOn (show ‖q.1‖ < 4 by linarith) (show ‖q'.1‖ < 4 by linarith) e3

theorem solMap_cases {q : ℂ × Circle} (h3 : ‖q.1‖ ≤ 3) :
    (‖q.1‖ < 3 ∧ sgnR t * σ.sideLevel h t q ≤ 2 ∧ S.solMap q = S.fakeMap q) ∨
      (σ.sideDom h t q ∧ 2 < sgnR t * σ.sideLevel h t q ∧
        S.solMap q = coreMap K ((σ.splitCharts SD hlin).liftMap t q)) := by
  by_cases hc : ‖q.1‖ < 3 ∧ sgnR t * σ.sideLevel h t q ≤ 2
  · exact Or.inl ⟨hc.1, hc.2, S.solMap_of_fake hc.1 hc.2⟩
  · have h2 : 2 < sgnR t * σ.sideLevel h t q := by
      by_cases h3' : ‖q.1‖ < 3
      · exact not_le.mp fun h2 => hc ⟨h3', h2⟩
      · have he : ‖q.1‖ = 3 := le_antisymm h3 (not_lt.mp h3')
        linarith [σ.three_lt_sideLevel_of_ge h t (q := q) (by linarith) h3]
    exact Or.inr ⟨(σ.sideDom_iff h).mpr ⟨h3, by linarith⟩, h2, S.solMap_of_real h2⟩

theorem solMap_injOn : InjOn S.solMap {q : ℂ × Circle | ‖q.1‖ ≤ 3} := by
  intro q hq q' hq' he
  have hss := sgnR_mul_self t
  rcases S.solMap_cases hq with ⟨h3, h2, e⟩ | ⟨hd, h2, e⟩ <;>
    rcases S.solMap_cases hq' with ⟨h3', h2', e'⟩ | ⟨hd', h2', e'⟩ <;> rw [e, e'] at he
  · exact S.fakeMap_inj h3 h2 h3' h2' he
  · refine absurd he (S.fakeMap_ne_coreMap_liftMap h3 h2 hd' (one_lt_abs_sideLevel h2')
      fun r _ hr hc => ?_)
    rw [hc, ← mul_assoc, hss, one_mul] at h2'
    linarith
  · refine absurd he.symm (S.fakeMap_ne_coreMap_liftMap h3' h2' hd (one_lt_abs_sideLevel h2)
      fun r _ hr hc => ?_)
    rw [hc, ← mul_assoc, hss, one_mul] at h2
    linarith
  · exact σ.liftMap_injOn h SD hlin t hd hd' (coreMap_injOn K
      (liftMap_mem_core hd (one_lt_abs_sideLevel h2))
      (liftMap_mem_core hd' (one_lt_abs_sideLevel h2')) he)

end SideCap

theorem solMap_cross (S : σ.SideCap h SD hlin K false) (S' : σ.SideCap h SD hlin K true)
    {q q' : ℂ × Circle} (hq : ‖q.1‖ ≤ 3) (hq' : ‖q'.1‖ ≤ 3) (he : S.solMap q = S'.solMap q') :
    ‖q.1‖ = 3 ∧ ‖q'.1‖ = 3 := by
  rcases S.solMap_cases hq with ⟨h3, h2, e⟩ | ⟨hd, h2, e⟩ <;>
    rcases S'.solMap_cases hq' with ⟨h3', h2', e'⟩ | ⟨hd', h2', e'⟩ <;> rw [e, e'] at he
  · exfalso
    rcases S.fakeMap_cases h3 h2 with ⟨w, hw⟩ | ⟨z, r, h1, hr2, hz⟩ <;>
      rcases S'.fakeMap_cases h3' h2' with ⟨w', hw'⟩ | ⟨z', r', h1', hr2', hz'⟩
    · rw [hw, hw'] at he
      exact Set.disjoint_left.mp (K.cap_disjoint (show ((), false) ≠ ((), true) by simp))
        ⟨w, rfl⟩ ⟨w', he.symm⟩
    · rw [hw, hz'] at he
      exact (σ.splitCharts SD hlin).coreMap_tubeMap_ne_cap K (q := (z', sgnR true * r'))
        (by change 1 < |sgnR true * r'|; rw [abs_sgnR_mul_of_pos true (by linarith)]; exact h1')
        (by change |sgnR true * r'| < 3; rw [abs_sgnR_mul_of_pos true (by linarith)]; linarith)
        _ w he.symm
    · rw [hz, hw'] at he
      exact (σ.splitCharts SD hlin).coreMap_tubeMap_ne_cap K (q := (z, sgnR false * r))
        (by change 1 < |sgnR false * r|; rw [abs_sgnR_mul_of_pos false (by linarith)]; exact h1)
        (by change |sgnR false * r| < 3; rw [abs_sgnR_mul_of_pos false (by linarith)]; linarith)
        _ w' he
    · rw [hz, hz'] at he
      have hqq := (σ.splitCharts SD hlin).coreMap_tubeMap_inj K (q := (z, sgnR false * r))
        (q' := (z', sgnR true * r'))
        (by change 1 ≤ |sgnR false * r|; rw [abs_sgnR_mul_of_pos false (by linarith)]; linarith)
        (by change |sgnR false * r| < 3; rw [abs_sgnR_mul_of_pos false (by linarith)]; linarith)
        (by change 1 ≤ |sgnR true * r'|; rw [abs_sgnR_mul_of_pos true (by linarith)]; linarith)
        (by change |sgnR true * r'| < 3; rw [abs_sgnR_mul_of_pos true (by linarith)]; linarith) he
      have e2 := congrArg Prod.snd hqq
      simp only [sgnR_false, sgnR_true] at e2
      linarith
  · refine absurd he (S.fakeMap_ne_coreMap_liftMap h3 h2 hd' (one_lt_abs_sideLevel h2')
      fun r hr _ hc => ?_)
    rw [hc, sgnR_true, sgnR_false] at h2'
    linarith
  · refine absurd he.symm (S'.fakeMap_ne_coreMap_liftMap h3' h2' hd (one_lt_abs_sideLevel h2)
      fun r hr _ hc => ?_)
    rw [hc, sgnR_true, sgnR_false] at h2
    linarith
  · have hl := coreMap_injOn K (liftMap_mem_core hd (one_lt_abs_sideLevel h2))
      (liftMap_mem_core hd' (one_lt_abs_sideLevel h2')) he
    rcases σ.liftMap_cross h SD hlin hd hd' hl with hlev | hb
    · rw [hlev, sgnR_false] at h2
      rw [sgnR_true] at h2'
      linarith
    · exact hb

end

end GC.Seifert.RelativeNormalization.MixedStage

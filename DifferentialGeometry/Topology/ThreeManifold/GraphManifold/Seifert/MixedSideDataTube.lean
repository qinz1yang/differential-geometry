import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSideDataPoints
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelShell

/-!
# The tube and the shell of the fake ball of a mixed split

Lane N2f, tier 2. The texts of `MoveSplitCappedSideModelTube` and
`MoveSplitCappedSideModelShell` for a mixed split site `(σ, h, SD)`: the side level `sideLevel`,
the correspondence between tube points of level `|h| < 3` and lifted model points
(`exists_tubeMap_eq_liftMap`, `exists_liftMap_eq_tubeMap`), the inverse `liftInv` of the lift and
the shell map `shellMap` of the fake ball (`exists_shellPD`).
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
  seamHeight_sqrt_three_half seamHeight_neg_sqrt_three_half exists_bandHeight_eq)

section

open SplitTube

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {j : Fin σ.toTorus.pairing.count} {b : Bool} (h : σ.IsSplitSeam j b) (SD : σ.SplitData h)

def sideLevel (t : Bool) (q : ℂ × Circle) : ℝ :=
  stripLevel (σ.hostSide h) ((sideData (σ.hostSide h) t).point (q.2, ‖q.1‖))

theorem sideDom_iff {t : Bool} {q : ℂ × Circle} :
    σ.sideDom h t q ↔ ‖q.1‖ ≤ 3 ∧ -3 < sgnR t * σ.sideLevel h t q :=
  Iff.rfl

theorem sideLevel_of_le (t : Bool) {q : ℂ × Circle} (h2 : ‖q.1‖ ≤ 2) :
    σ.sideLevel h t q =
      stripLevel (σ.hostSide h) ((vRadius (σ.hostSide h) (2 * ‖q.1‖) : ℂ) * (q.2 : ℂ)) := by
  unfold sideLevel
  rw [(sideData (σ.hostSide h) t).point_of_le_two (q := (q.2, ‖q.1‖)) h2]



section Lift

variable (hlin : σ.IsLinearSeam j)

theorem exists_tubeMap_eq_liftMap (t : Bool) {q : ℂ × Circle} (hq : σ.sideDom h t q)
    (hlev : |σ.sideLevel h t q| < 3) :
    ∃ p : S2, (σ.splitCharts SD hlin).tubeMap (p, σ.sideLevel h t q) =
      (σ.splitCharts SD hlin).liftMap t q := by
  have he₁ := (σ.splitCharts SD hlin).he₁
  by_cases h32 : ‖q.1‖ ≤ 3 / 2
  · have hR : 2 ≤ vRadius (σ.hostSide h) (2 * ‖q.1‖) :=
      two_le_vRadius _ (by positivity) (by linarith)
    rw [σ.sideLevel_of_le h t (by linarith)] at hlev ⊢
    have hu := eq_exp_of_level hR hlev
    set s := decide (0 < ((q.2 : Circle) : ℂ).im)
    have hz : ‖(1 / 3 : ℝ) • q.1‖ < 1 := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      linarith
    refine ⟨capPoint s ((1 / 3 : ℝ) • q.1), ?_⟩
    have hsp : seamHeight (heightOf (capPoint s ((1 / 3 : ℝ) • q.1))) ≤ 0 := by
      rw [seamHeight, latRadius_heightOf, planeOf_capPoint s hz, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)]
      linarith
    rw [SplitCharts.tubeMap_of_nonpos _ (σ.splitCharts_seam_zero h SD hlin) _ hsp,
      planeOf_capPoint s hz, SplitCharts.liftMap_of_le _ t h32]
    have hside : SplitCharts.side (capPoint s ((1 / 3 : ℝ) • q.1),
        stripLevel (σ.hostSide h) ((vRadius (σ.hostSide h) (2 * ‖q.1‖) : ℂ) * (q.2 : ℂ))) = s := by
      apply SplitCharts.side_eq_of_sgnR
      rw [heightOf_capPoint s hz, ← mul_assoc, sgnR_mul_self, one_mul]
      exact Real.sqrt_pos.mpr (by nlinarith [norm_nonneg ((1 / 3 : ℝ) • q.1)])
    rw [hside, ← exp_zpow_eq_tubeFibre, ← hu, smul_smul]
    unfold SplitCharts.liftV
    norm_num
  · push Not at h32
    set l := σ.hostSide h with hl
    have hwn : ‖(sideData l t).point (q.2, ‖q.1‖)‖ < hostRadius l.val 0 :=
      (norm_point_le l t (q := (q.2, ‖q.1‖)) h32.le hq.1).2 h32
    have hY : |((sideData l t).point (q.2, ‖q.1‖)).im| * angleScale (σ.sideLevel h t q) <
        hostRadius l.val 0 := by
      by_cases h1 : 1 ≤ |((sideData l t).point (q.2, ‖q.1‖)).im|
      · exact (norm_eq_of_one_le_im l h1).symm.trans_lt hwn
      · push Not at h1
        have hA := angleScale_lt_two hlev
        have h2 := two_le_hostRadius l.val
        nlinarith [abs_nonneg ((sideData l t).point (q.2, ‖q.1‖)).im, angleScale_pos
          (σ.sideLevel h t q)]
    obtain ⟨x, hx, hxe⟩ := exists_bandHeight_eq l.val (y := ((sideData l t).point
      (q.2, ‖q.1‖)).im * angleScale (σ.sideLevel h t q)) (by
        rw [abs_mul, abs_of_pos (angleScale_pos _)]
        exact hY)
    have hx1 : |x| < 1 := hx.trans sqrt_three_half_lt_one
    have hpos := seamHeight_pos_of_lt hx
    set φ : Circle := (σ.liftFib h SD hlin q *
      (bandPhase (σ.splitCharts SD hlin).e₀ (σ.splitCharts SD hlin).d x
        (σ.sideLevel h t q))⁻¹) ^ (σ.splitCharts SD hlin).e₁ with hφ
    refine ⟨bandPoint (x, φ), ?_⟩
    rw [SplitCharts.tubeMap_of_pos' _ _ (by rwa [heightOf_bandPoint hx1]),
      heightOf_bandPoint hx1, planeOf_bandPoint hx1, unitOf_smul (latRadius_pos hx1),
      hφ, zpow_zpow_unit he₁, inv_mul_cancel_right, SplitCharts.liftMap_of_gt _ t h32]
    change (σ.splitCharts SD hlin).hostMap (hostChart l (strip l (bandHeight l.val x /
      angleScale (σ.sideLevel h t q), σ.sideLevel h t q)), σ.liftFib h SD hlin q) = _
    rw [hxe, mul_div_cancel_right₀ _ (angleScale_pos _).ne']
    unfold sideLevel
    rw [strip_stripLevel]
    rfl

theorem exists_liftMap_eq_tubeMap (t : Bool) (p : S2) {lv : ℝ} (hlv : |lv| < 3) :
    ∃ q : ℂ × Circle, σ.sideDom h t q ∧ ‖q.1‖ < 3 ∧ σ.sideLevel h t q = lv ∧
      (σ.splitCharts SD hlin).liftMap t q = (σ.splitCharts SD hlin).tubeMap (p, lv) := by
  have he₁ := (σ.splitCharts SD hlin).he₁
  have hε := neg_three_lt_sgnR_mul (t := t) hlv
  set l := σ.hostSide h with hl
  by_cases hsp : seamHeight (heightOf p) ≤ 0
  · set s := SplitCharts.side (p, lv)
    have hpl : ‖planeOf p‖ ≤ 1 / 2 := by
      have := latRadius_heightOf p
      rw [seamHeight] at hsp
      linarith
    set ζ : ℂ := (3 : ℝ) • planeOf p with hζ
    have hζn : ‖ζ‖ ≤ 3 / 2 := by
      rw [hζ, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      linarith
    have hR : 2 ≤ vRadius l (2 * ‖ζ‖) := two_le_vRadius _ (by positivity) (by linarith)
    obtain ⟨hL, -⟩ := stripLevel_exp l hR s hlv
    have hlev : σ.sideLevel h t (ζ, Circle.exp (sgnR s * hostTheta lv)) = lv := by
      rw [σ.sideLevel_of_le h t (by dsimp only; linarith)]
      exact hL
    refine ⟨(ζ, Circle.exp (sgnR s * hostTheta lv)), ⟨by dsimp only; linarith, ?_⟩,
      by dsimp only; linarith, hlev, ?_⟩
    · change -3 < sgnR t * σ.sideLevel h t _
      rw [hlev]
      exact hε
    · rw [SplitCharts.liftMap_of_le _ t hζn,
        SplitCharts.tubeMap_of_nonpos _ (σ.splitCharts_seam_zero h SD hlin) lv hsp]
      unfold SplitCharts.liftV
      rw [exp_zpow_eq_tubeFibre, hζ, smul_smul]
      norm_num
      rfl
  · push Not at hsp
    have hx1 := abs_heightOf_lt_of_seamHeight_pos hsp
    obtain ⟨hmem, hne⟩ := hostChart_strip_mem l hx1 hsp hlv
    set w := strip l (bandHeight l.val (heightOf p) / angleScale lv, lv) with hw
    have hwl : stripLevel l w = lv := stripLevel_strip l _
    have hwn : ‖w‖ < hostRadius l.val 0 := by
      refine norm_lt_of_level (by rw [hwl]; exact hlv) fun _ => ?_
      rw [hwl]
      change |bandHeight l.val (heightOf p) / angleScale lv| * angleScale lv < _
      rw [abs_div, abs_of_pos (angleScale_pos lv), div_mul_cancel₀ _ (angleScale_pos lv).ne']
      exact abs_bandHeight_lt l.val hx1 hsp
    have hout : (sideData l t).famR 3 < ‖w - (sideData l t).famC 3‖ := by
      by_contra hc
      push Not at hc
      have := three_lt_of_inside_port l t hne hc
      rw [hwl] at this
      linarith [sgnR_mul_lt_three (t := t) hlv]
    have hv3 : vRadius l 3 = hostRadius l.val 0 := by
      rw [vRadius_of_two_le l (by norm_num)]
      norm_num
    have h0 : ‖w - (sideData l t).famC 0‖ ≤ (sideData l t).famR 0 := by
      rw [(sideData l t).famC_of_le (by norm_num), (sideData l t).famR_of_le (by norm_num),
        sub_zero, mul_zero]
      have := (strictAntiOn_vRadius l).antitoneOn (mem_Ici.mpr le_rfl)
        (mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 3)) (by norm_num : (0 : ℝ) ≤ 3)
      linarith
    obtain ⟨⟨u, ρ⟩, hρ, hpt⟩ := exists_nestedPoint_eq (μ := (sideData l t).famMu)
      (a := (sideData l t).famA) (sideData l t).continuousOn_famC
      (sideData l t).continuousOn_famR (fun _ hρ => (sideData l t).famR_pos hρ)
      (fun _ hρ => (sideData l t).famA_lt' hρ) h0 hout.le
    change (sideData l t).point (u, ρ) = w at hpt
    have hρ3 : ρ < 3 := by
      refine lt_of_le_of_ne hρ.2 fun he => ?_
      have := norm_nestedPoint_sub (c := (sideData l t).famC) (μ := (sideData l t).famMu)
        (a := (sideData l t).famA) (q := (u, ρ)) ((sideData l t).famR_pos hρ).le
      change ‖(sideData l t).point (u, ρ) - _‖ = _ at this
      rw [hpt] at this
      dsimp only at this
      rw [he] at this
      linarith
    have hρ32 : 3 / 2 < ρ := by
      by_contra hc
      push Not at hc
      have e := (sideData l t).point_of_le_two (q := (u, ρ)) (by dsimp only; linarith)
      rw [hpt] at e
      have hv : 2 ≤ vRadius l (2 * ρ) := two_le_vRadius l (by linarith [hρ.1]) (by linarith)
      have hn : ‖w‖ = vRadius l (2 * ρ) := by
        rw [e, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (by linarith)]
      have := (strictAntiOn_vRadius l).antitoneOn (mem_Ici.mpr (by linarith [hρ.1]))
        (mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 3)) (by linarith : 2 * ρ ≤ 3)
      linarith
    have hρ0 : 0 < ρ := by linarith
    set X : Circle := unitOf (planeOf p) ^ (σ.splitCharts SD hlin).e₁ *
      bandPhase (σ.splitCharts SD hlin).e₀ (σ.splitCharts SD hlin).d (heightOf p) lv with hX
    set φ : Circle := (X * (u ^ ((σ.splitCharts SD hlin).e₀ * (σ.splitCharts SD hlin).d))⁻¹) ^
      (σ.splitCharts SD hlin).e₁ with hφ
    set ζ : ℂ := (ρ : ℝ) • (φ : ℂ) with hζ
    have hζn : ‖ζ‖ = ρ := by
      rw [hζ, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hρ0.le]
    have hζu : unitOf ζ = φ := unitOf_smul hρ0 φ
    have hpt' : (sideData l t).point (u, ‖ζ‖) = w := by rw [hζn]; exact hpt
    have hlev : σ.sideLevel h t (ζ, u) = lv := by
      change stripLevel l ((sideData l t).point (u, ‖ζ‖)) = lv
      rw [hpt', hwl]
    refine ⟨(ζ, u), ⟨by dsimp only; linarith, ?_⟩, by dsimp only; linarith, hlev, ?_⟩
    · change -3 < sgnR t * σ.sideLevel h t _
      rw [hlev]
      exact hε
    · rw [SplitCharts.liftMap_of_gt _ t (by dsimp only; linarith),
        SplitCharts.tubeMap_of_pos' _ lv hsp]
      unfold SplitCharts.liftH
      dsimp only
      change (σ.splitCharts SD hlin).hostMap (hostChart l ((sideData l t).point (u, ‖ζ‖)),
        u ^ ((σ.splitCharts SD hlin).e₀ * (σ.splitCharts SD hlin).d) * unitOf ζ ^
          (σ.splitCharts SD hlin).e₁) = (σ.splitCharts SD hlin).hostMap (hostChart l w, X)
      rw [hpt', hζu, hφ, zpow_zpow_unit he₁, mul_comm X, mul_inv_cancel_left]

end Lift

end

section

open SplitTube

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {j : Fin σ.toTorus.pairing.count} {b : Bool} (h : σ.IsSplitSeam j b) (SD : σ.SplitData h)

section Lift

variable (hlin : σ.IsLinearSeam j)

def liftDom (t : Bool) : Set (ℂ × Circle) :=
  {q | ‖q.1‖ < 3 ∧ -3 < sgnR t * σ.sideLevel h t q}

theorem isOpen_liftDom (t : Bool) : IsOpen (σ.liftDom h t) :=
  σ.isOpen_sideDom_interior h t

theorem sideDom_of_mem_liftDom {t : Bool} {q : ℂ × Circle} (hq : q ∈ σ.liftDom h t) :
    σ.sideDom h t q :=
  ⟨hq.1.le, hq.2⟩

theorem liftMap_injOn_liftDom (t : Bool) :
    InjOn ((σ.splitCharts SD hlin).liftMap t) (σ.liftDom h t) := fun _ hq _ hq' he =>
  σ.liftMap_injOn h SD hlin t (σ.sideDom_of_mem_liftDom h hq) (σ.sideDom_of_mem_liftDom h hq') he

theorem isLocalDiffeomorphAt_liftMap_of_mem {t : Bool} {q : ℂ × Circle}
    (hq : q ∈ σ.liftDom h t) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ ((σ.splitCharts SD hlin).liftMap t) q :=
  (σ.splitCharts SD hlin).isLocalDiffeomorphAt_liftMap (σ.splitCharts_seam_zero h SD hlin) t hq.1
    fun h32 => ⟨σ.hostChart_point_mem_pantsInterior h (σ.sideDom_of_mem_liftDom h hq) h32 hq.1,
      σ.point_ne_zero h (σ.sideDom_of_mem_liftDom h hq)⟩

def liftInv (t : Bool) : Q.Carrier → ℂ × Circle :=
  invFunOn ((σ.splitCharts SD hlin).liftMap t) (σ.liftDom h t)

theorem liftInv_liftMap {t : Bool} {q : ℂ × Circle} (hq : q ∈ σ.liftDom h t) :
    σ.liftInv h SD hlin t ((σ.splitCharts SD hlin).liftMap t q) = q :=
  (σ.liftMap_injOn_liftDom h SD hlin t).leftInvOn_invFunOn hq

theorem liftInv_tubeMap (t : Bool) (p : S2) {lv : ℝ} (hlv : |lv| < 3) :
    σ.liftInv h SD hlin t ((σ.splitCharts SD hlin).tubeMap (p, lv)) ∈ σ.liftDom h t ∧
      (σ.splitCharts SD hlin).liftMap t (σ.liftInv h SD hlin t
        ((σ.splitCharts SD hlin).tubeMap (p, lv))) = (σ.splitCharts SD hlin).tubeMap (p, lv) ∧
      σ.sideLevel h t (σ.liftInv h SD hlin t ((σ.splitCharts SD hlin).tubeMap (p, lv))) = lv := by
  obtain ⟨q, hq, hq3, hlev, he⟩ := σ.exists_liftMap_eq_tubeMap h SD hlin t p hlv
  have hqd : q ∈ σ.liftDom h t := ⟨hq3, hq.2⟩
  rw [← he, σ.liftInv_liftMap h SD hlin hqd]
  exact ⟨hqd, rfl, hlev⟩

def shellMap (t : Bool) (x : E3) : E3 :=
  torusPD (σ.liftInv h SD hlin t ((σ.splitCharts SD hlin).tubeMap (shellDir t x)))

theorem shellMap_spec (t : Bool) {x : E3} (hx : x ∈ shellSet) :
    σ.liftInv h SD hlin t ((σ.splitCharts SD hlin).tubeMap (shellDir t x)) ∈ σ.liftDom h t ∧
      (σ.splitCharts SD hlin).liftMap t (σ.liftInv h SD hlin t
        ((σ.splitCharts SD hlin).tubeMap (shellDir t x))) =
        (σ.splitCharts SD hlin).tubeMap (shellDir t x) ∧
      sgnR t * σ.sideLevel h t (σ.liftInv h SD hlin t
        ((σ.splitCharts SD hlin).tubeMap (shellDir t x))) = 2 * ‖x‖ := by
  obtain ⟨h1, h2, h3⟩ := σ.liftInv_tubeMap h SD hlin t (shellDir t x).1 (abs_shellDir_lt t hx)
  refine ⟨h1, h2, ?_⟩
  rw [h3]
  change sgnR t * (2 * sgnR t * ‖x‖) = _
  have := sgnR_mul_self t
  linear_combination (2 * ‖x‖) * this

theorem isLocalDiffeomorphAt_shellMap (t : Bool) {x : E3} (hx : x ∈ shellSet) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (σ.shellMap h SD hlin t) x := by
  obtain ⟨h1, h2, -⟩ := σ.shellMap_spec h SD hlin t hx
  have hx0 : x ≠ 0 := fun h0 => by have := hx.1; rw [h0, norm_zero] at this; linarith
  have a1 := isLocalDiffeomorphAt_shellDir t hx0
  have a2 := (σ.splitCharts SD hlin).isLocalDiffeomorphAt_tubeMap (abs_shellDir_lt t hx)
  have a3 := isLocalDiffeomorphAt_invFunOn (σ.isOpen_liftDom h t)
    (σ.liftMap_injOn_liftDom h SD hlin t) h1 (σ.isLocalDiffeomorphAt_liftMap_of_mem h SD hlin h1)
  rw [h2] at a3
  have a4 := isLocalDiffeomorphAt_torusPD (q := σ.liftInv h SD hlin t
    ((σ.splitCharts SD hlin).tubeMap (shellDir t x))) (by linarith [h1.1])
  exact ((a1.comp (𝓡 3) Q.Carrier a2).comp (𝓘(ℝ, ℂ).prod (𝓡 1)) (ℂ × Circle) a3).comp
    (𝓡 3) E3 a4

theorem shellMap_injOn (t : Bool) : InjOn (σ.shellMap h SD hlin t) shellSet := by
  intro x hx y hy he
  obtain ⟨hx1, hx2, -⟩ := σ.shellMap_spec h SD hlin t hx
  obtain ⟨hy1, hy2, -⟩ := σ.shellMap_spec h SD hlin t hy
  have hx4 : ‖(σ.liftInv h SD hlin t ((σ.splitCharts SD hlin).tubeMap (shellDir t x))).1‖ < 4 := by
    linarith [hx1.1]
  have hy4 : ‖(σ.liftInv h SD hlin t ((σ.splitCharts SD hlin).tubeMap (shellDir t y))).1‖ < 4 := by
    linarith [hy1.1]
  have e1 := torusPD_injOn hx4 hy4 he
  have e2 := congrArg ((σ.splitCharts SD hlin).liftMap t) e1
  rw [hx2, hy2] at e2
  have e3 := (σ.splitCharts SD hlin).tubeMap_injOn (abs_shellDir_lt t hx) (abs_shellDir_lt t hy) e2
  have hn : ‖x‖ = ‖y‖ := by
    have := congrArg (fun p : S2 × ℝ => |p.2|) e3
    simp only [abs_shellDir_snd] at this
    linarith
  have hd : Manifold.sphereDirection poleS2 x = Manifold.sphereDirection poleS2 y :=
    congrArg Prod.fst e3
  have hx0 : x ≠ 0 := fun h0 => by have := hx.1; rw [h0, norm_zero] at this; linarith
  have hy0 : y ≠ 0 := fun h0 => by have := hy.1; rw [h0, norm_zero] at this; linarith
  rw [← Manifold.norm_smul_sphereDirection poleS2 hx0, ← Manifold.norm_smul_sphereDirection
    poleS2 hy0, hn, hd]

theorem exists_shellPD (t : Bool) :
    ∃ F : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      F.toPartialEquiv.source = shellSet ∧ ∀ x, F x = σ.shellMap h SD hlin t x := by
  obtain ⟨F, hs, -, hf⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (fun x => σ.isLocalDiffeomorphAt_shellMap h SD hlin t x.2) isOpen_shellSet
    ⟨(EuclideanSpace.single 0 1 : E3), by simp [shellSet]; norm_num⟩ (σ.shellMap_injOn h SD hlin t)
  exact ⟨F, hs, fun x => congrFun hf x⟩

end Lift

end

end GC.Seifert.RelativeNormalization.MixedStage

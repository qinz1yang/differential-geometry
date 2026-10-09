import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugSideLift

/-!
The actual bounded side shell and its genuine smooth ball filling.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace GC.Seifert.ElementaryPresentation

open SplitTube

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)

theorem boundedPlugSideLevel_of_le (t : Bool) {q : ℂ × Circle} (h2 : ‖q.1‖ ≤ 2) :
    E.boundedPlugSideLevel h t q = stripLevel (E.boundedPlugSideHost h)
      ((vRadius (E.boundedPlugSideHost h) (2 * ‖q.1‖) : ℂ) * (q.2 : ℂ)) := by
  unfold boundedPlugSideLevel
  rw [(sideData (E.boundedPlugSideHost h) t).point_of_le_two (q := (q.2, ‖q.1‖)) h2]

variable (hlin : E.IsLinearSeam j)

theorem boundedPlugSideCharts_tube_cover (t : Bool) {q : ℂ × Circle} (hq : E.boundedPlugSideDom
    h t q)
    (hlev : |E.boundedPlugSideLevel h t q| < 3) :
    ∃ p : S2, (E.boundedPlugSideCharts h hlin).tubeMap (p, E.boundedPlugSideLevel h t q) =
      (E.boundedPlugSideCharts h hlin).liftMap t q := by
  have he₁ := (E.boundedPlugSideCharts h hlin).he₁
  by_cases h32 : ‖q.1‖ ≤ 3 / 2
  · have hR : 2 ≤ vRadius (E.boundedPlugSideHost h) (2 * ‖q.1‖) :=
      two_le_vRadius _ (by positivity) (by linarith)
    rw [E.boundedPlugSideLevel_of_le h t (by linarith)] at hlev ⊢
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
    rw [SplitCharts.tubeMap_of_nonpos _ (E.boundedPlugSideCharts_seam_zero h hlin) _ hsp,
      planeOf_capPoint s hz, SplitCharts.liftMap_of_le _ t h32]
    have hside : SplitCharts.side (capPoint s ((1 / 3 : ℝ) • q.1),
        stripLevel (E.boundedPlugSideHost h) ((vRadius (E.boundedPlugSideHost h) (2 * ‖q.1‖) :
            ℂ) * (q.2 : ℂ))) = s := by
      apply SplitCharts.side_eq_of_sgnR
      rw [heightOf_capPoint s hz, ← mul_assoc, sgnR_mul_self, one_mul]
      exact Real.sqrt_pos.mpr (by nlinarith [norm_nonneg ((1 / 3 : ℝ) • q.1)])
    rw [hside, ← exp_zpow_eq_tubeFibre, ← hu, smul_smul]
    unfold SplitCharts.liftV
    norm_num
  · push Not at h32
    set l := E.boundedPlugSideHost h with hl
    have hwn : ‖(sideData l t).point (q.2, ‖q.1‖)‖ < hostRadius l.val 0 :=
      (norm_point_le l t (q := (q.2, ‖q.1‖)) h32.le hq.1).2 h32
    have hY : |((sideData l t).point (q.2, ‖q.1‖)).im| * angleScale (E.boundedPlugSideLevel h t q) <
        hostRadius l.val 0 := by
      by_cases h1 : 1 ≤ |((sideData l t).point (q.2, ‖q.1‖)).im|
      · exact (norm_eq_of_one_le_im l h1).symm.trans_lt hwn
      · push Not at h1
        have hA := angleScale_lt_two hlev
        have h2 := two_le_hostRadius l.val
        nlinarith [abs_nonneg ((sideData l t).point (q.2, ‖q.1‖)).im, angleScale_pos
          (E.boundedPlugSideLevel h t q)]
    obtain ⟨x, hx, hxe⟩ := exists_bandHeight_eq l.val (y := ((sideData l t).point
      (q.2, ‖q.1‖)).im * angleScale (E.boundedPlugSideLevel h t q)) (by
        rw [abs_mul, abs_of_pos (angleScale_pos _)]
        exact hY)
    have hx1 : |x| < 1 := hx.trans sqrt_three_half_lt_one
    have hpos := seamHeight_pos_of_lt hx
    set φ : Circle := (E.boundedPlugSideFibre h hlin q *
      (bandPhase (E.boundedPlugSideCharts h hlin).e₀ (E.boundedPlugSideCharts h hlin).d x
        (E.boundedPlugSideLevel h t q))⁻¹) ^ (E.boundedPlugSideCharts h hlin).e₁ with hφ
    refine ⟨bandPoint (x, φ), ?_⟩
    rw [SplitCharts.tubeMap_of_pos' _ _ (by rwa [heightOf_bandPoint hx1]),
      heightOf_bandPoint hx1, planeOf_bandPoint hx1, unitOf_smul (latRadius_pos hx1),
      hφ, zpow_zpow_unit he₁, inv_mul_cancel_right, SplitCharts.liftMap_of_gt _ t h32]
    change (E.boundedPlugSideCharts h hlin).hostMap (hostChart l (strip l (bandHeight l.val x /
      angleScale (E.boundedPlugSideLevel h t q), E.boundedPlugSideLevel h t q)),
          E.boundedPlugSideFibre h hlin q) = _
    rw [hxe, mul_div_cancel_right₀ _ (angleScale_pos _).ne']
    unfold boundedPlugSideLevel
    rw [strip_stripLevel]
    rfl

theorem boundedPlugSideCharts_lift_cover (t : Bool) (p : S2) {lv : ℝ} (hlv : |lv| < 3) :
    ∃ q : ℂ × Circle, E.boundedPlugSideDom h t q ∧ ‖q.1‖ < 3 ∧ E.boundedPlugSideLevel h t q = lv ∧
      (E.boundedPlugSideCharts h hlin).liftMap t q = (E.boundedPlugSideCharts h hlin).tubeMap
          (p, lv) := by
  have he₁ := (E.boundedPlugSideCharts h hlin).he₁
  have hε := neg_three_lt_sgnR_mul (t := t) hlv
  set l := E.boundedPlugSideHost h with hl
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
    have hlev : E.boundedPlugSideLevel h t (ζ, Circle.exp (sgnR s * hostTheta lv)) = lv := by
      rw [E.boundedPlugSideLevel_of_le h t (by dsimp only; linarith)]
      exact hL
    refine ⟨(ζ, Circle.exp (sgnR s * hostTheta lv)), ⟨by dsimp only; linarith, ?_⟩,
      by dsimp only; linarith, hlev, ?_⟩
    · change -3 < sgnR t * E.boundedPlugSideLevel h t _
      rw [hlev]
      exact hε
    · rw [SplitCharts.liftMap_of_le _ t hζn,
        SplitCharts.tubeMap_of_nonpos _ (E.boundedPlugSideCharts_seam_zero h hlin) lv hsp]
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
      refine norm_lt_of_level (by rw [hwl]; exact hlv) fun hzero => ?_
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
      (sideData l t).continuousOn_famR (fun radius hρ => (sideData l t).famR_pos hρ)
      (fun radius hρ => (sideData l t).famA_lt' hρ) h0 hout.le
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
    set X : Circle := unitOf (planeOf p) ^ (E.boundedPlugSideCharts h hlin).e₁ *
      bandPhase (E.boundedPlugSideCharts h hlin).e₀ (E.boundedPlugSideCharts h hlin).d (heightOf
          p) lv with hX
    set φ : Circle := (X * (u ^ ((E.boundedPlugSideCharts h hlin).e₀ * (E.boundedPlugSideCharts
        h hlin).d))⁻¹) ^
      (E.boundedPlugSideCharts h hlin).e₁ with hφ
    set ζ : ℂ := (ρ : ℝ) • (φ : ℂ) with hζ
    have hζn : ‖ζ‖ = ρ := by
      rw [hζ, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hρ0.le]
    have hζu : unitOf ζ = φ := unitOf_smul hρ0 φ
    have hpt' : (sideData l t).point (u, ‖ζ‖) = w := by rw [hζn]; exact hpt
    have hlev : E.boundedPlugSideLevel h t (ζ, u) = lv := by
      change stripLevel l ((sideData l t).point (u, ‖ζ‖)) = lv
      rw [hpt', hwl]
    refine ⟨(ζ, u), ⟨by dsimp only; linarith, ?_⟩, by dsimp only; linarith, hlev, ?_⟩
    · change -3 < sgnR t * E.boundedPlugSideLevel h t _
      rw [hlev]
      exact hε
    · rw [SplitCharts.liftMap_of_gt _ t (by dsimp only; linarith),
        SplitCharts.tubeMap_of_pos' _ lv hsp]
      unfold SplitCharts.liftH
      dsimp only
      change (E.boundedPlugSideCharts h hlin).hostMap (hostChart l ((sideData l t).point (u, ‖ζ‖)),
        u ^ ((E.boundedPlugSideCharts h hlin).e₀ * (E.boundedPlugSideCharts h hlin).d) * unitOf ζ ^
          (E.boundedPlugSideCharts h hlin).e₁) = (E.boundedPlugSideCharts h hlin).hostMap
              (hostChart l w, X)
      rw [hpt', hζu, hφ, zpow_zpow_unit he₁, mul_comm X, mul_inv_cancel_left]


theorem boundedPlugSideTube_cover (t : Bool) {q : ℂ × Circle}
    (hq : E.boundedPlugSideDom h t q) (h3 : ‖q.1‖ < 3)
    (hlev : |E.boundedPlugSideLevel h t q| < 3) :
    ∃ p : S2, E.boundedSplitTubeMap h hlin (p, E.boundedPlugSideLevel h t q) =
      E.boundedPlugSideLiftMap h hlin t q := by
  obtain ⟨p, hp⟩ := E.boundedPlugSideCharts_tube_cover h hlin t hq hlev
  refine ⟨p, ?_⟩
  exact (E.boundedPlugSideCharts_tubeMap_val h hlin _).symm.trans
    ((congrArg (boundedSplitInteriorVal W) hp).trans
      (E.boundedPlugSideCharts_liftMap_val h hlin t hq h3))

theorem boundedPlugSideLift_cover (t : Bool) (p : S2) {lv : ℝ} (hlv : |lv| < 3) :
    ∃ q : ℂ × Circle, E.boundedPlugSideDom h t q ∧ ‖q.1‖ < 3 ∧
      E.boundedPlugSideLevel h t q = lv ∧
      E.boundedPlugSideLiftMap h hlin t q = E.boundedSplitTubeMap h hlin (p, lv) := by
  obtain ⟨q, hq, h3, he, hp⟩ := E.boundedPlugSideCharts_lift_cover h hlin t p hlv
  refine ⟨q, hq, h3, he, ?_⟩
  exact (E.boundedPlugSideCharts_liftMap_val h hlin t hq h3).symm.trans
    ((congrArg (boundedSplitInteriorVal W) hp).trans
      (E.boundedPlugSideCharts_tubeMap_val h hlin _))

def boundedPlugSideLiftDomain (t : Bool) : Set (ℂ × Circle) :=
  {q | ‖q.1‖ < 3 ∧ -3 < sgnR t * E.boundedPlugSideLevel h t q}

theorem boundedPlugSideLiftDomain_open (t : Bool) : IsOpen (E.boundedPlugSideLiftDomain h t) :=
  E.boundedPlugSide_isOpen_domain h t

theorem boundedPlugSideDom_of_mem_domain {t : Bool} {q : ℂ × Circle} (hq : q ∈
    E.boundedPlugSideLiftDomain h t) :
    E.boundedPlugSideDom h t q :=
  ⟨hq.1.le, hq.2⟩

theorem boundedPlugSideLift_injOn_domain (t : Bool) :
    InjOn (E.boundedPlugSideLiftMap h hlin t) (E.boundedPlugSideLiftDomain h t) := fun q hq q'
        hq' he =>
  E.boundedPlugSideLiftMap_injOn h hlin t (x₁ := q) (x₂ := q')
    (E.boundedPlugSideDom_of_mem_domain h hq) (E.boundedPlugSideDom_of_mem_domain h hq') he

theorem boundedPlugSideLift_local_domain {t : Bool} {q : ℂ × Circle}
    (hq : q ∈ E.boundedPlugSideLiftDomain h t) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) W.model ∞ (E.boundedPlugSideLiftMap h hlin t) q :=
  E.boundedPlugSideLiftMap_local h hlin t q
    (E.boundedPlugSideDom_of_mem_domain h hq) hq.1

def boundedPlugSideLiftInverse (t : Bool) : W.Carrier → ℂ × Circle :=
  invFunOn (E.boundedPlugSideLiftMap h hlin t) (E.boundedPlugSideLiftDomain h t)

theorem boundedPlugSideLiftInverse_lift {t : Bool} {q : ℂ × Circle} (hq : q ∈
    E.boundedPlugSideLiftDomain h t) :
    E.boundedPlugSideLiftInverse h hlin t (E.boundedPlugSideLiftMap h hlin t q) = q :=
  (E.boundedPlugSideLift_injOn_domain h hlin t).leftInvOn_invFunOn hq

theorem boundedPlugSideLiftInverse_tube (t : Bool) (p : S2) {lv : ℝ} (hlv : |lv| < 3) :
    E.boundedPlugSideLiftInverse h hlin t (E.boundedSplitTubeMap h hlin (p, lv)) ∈
        E.boundedPlugSideLiftDomain h t ∧
      E.boundedPlugSideLiftMap h hlin t (E.boundedPlugSideLiftInverse h hlin t
        (E.boundedSplitTubeMap h hlin (p, lv))) = E.boundedSplitTubeMap h hlin (p, lv) ∧
      E.boundedPlugSideLevel h t (E.boundedPlugSideLiftInverse h hlin t (E.boundedSplitTubeMap h
          hlin (p, lv))) = lv := by
  obtain ⟨q, hq, hq3, hlev, he⟩ := E.boundedPlugSideLift_cover h hlin t p hlv
  have hqd : q ∈ E.boundedPlugSideLiftDomain h t := ⟨hq3, hq.2⟩
  rw [← he, E.boundedPlugSideLiftInverse_lift h hlin hqd]
  exact ⟨hqd, rfl, hlev⟩

def boundedPlugSideShellMap (t : Bool) (x : E3) : E3 :=
  torusPD (E.boundedPlugSideLiftInverse h hlin t (E.boundedSplitTubeMap h hlin (shellDir t x)))

theorem boundedPlugSideShellMap_spec (t : Bool) {x : E3} (hx : x ∈ shellSet) :
    E.boundedPlugSideLiftInverse h hlin t (E.boundedSplitTubeMap h hlin (shellDir t x)) ∈
        E.boundedPlugSideLiftDomain h t ∧
      E.boundedPlugSideLiftMap h hlin t (E.boundedPlugSideLiftInverse h hlin t
        (E.boundedSplitTubeMap h hlin (shellDir t x))) =
        E.boundedSplitTubeMap h hlin (shellDir t x) ∧
      sgnR t * E.boundedPlugSideLevel h t (E.boundedPlugSideLiftInverse h hlin t
        (E.boundedSplitTubeMap h hlin (shellDir t x))) = 2 * ‖x‖ := by
  obtain ⟨h1, h2, h3⟩ := E.boundedPlugSideLiftInverse_tube h hlin t (shellDir t x).1
      (abs_shellDir_lt t hx)
  refine ⟨h1, h2, ?_⟩
  rw [h3]
  change sgnR t * (2 * sgnR t * ‖x‖) = _
  have := sgnR_mul_self t
  linear_combination (2 * ‖x‖) * this

theorem boundedPlugSideShellMap_local (t : Bool) {x : E3} (hx : x ∈ shellSet) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (E.boundedPlugSideShellMap h hlin t) x := by
  obtain ⟨h1, h2, -⟩ := E.boundedPlugSideShellMap_spec h hlin t hx
  have hx0 : x ≠ 0 := fun h0 => by have := hx.1; rw [h0, norm_zero] at this; linarith
  have a1 := isLocalDiffeomorphAt_shellDir t hx0
  have a2 := E.boundedSplitTubeMap_local h hlin (abs_shellDir_lt t hx)
  have a3 := isLocalDiffeomorphAt_invFunOn (E.boundedPlugSideLiftDomain_open h t)
    (E.boundedPlugSideLift_injOn_domain h hlin t) h1 (E.boundedPlugSideLift_local_domain h hlin h1)
  rw [h2] at a3
  have a4 := isLocalDiffeomorphAt_torusPD (q := E.boundedPlugSideLiftInverse h hlin t
    (E.boundedSplitTubeMap h hlin (shellDir t x))) (by linarith [h1.1])
  exact ((a1.comp W.model W.Carrier a2).comp (𝓘(ℝ, ℂ).prod (𝓡 1)) (ℂ × Circle) a3).comp
    (𝓡 3) E3 a4

theorem boundedPlugSideShellMap_injOn (t : Bool) : InjOn (E.boundedPlugSideShellMap h hlin t)
    shellSet := by
  intro x hx y hy he
  obtain ⟨hx1, hx2, -⟩ := E.boundedPlugSideShellMap_spec h hlin t hx
  obtain ⟨hy1, hy2, -⟩ := E.boundedPlugSideShellMap_spec h hlin t hy
  have hx4 : ‖(E.boundedPlugSideLiftInverse h hlin t (E.boundedSplitTubeMap h hlin (shellDir t
      x))).1‖ < 4 := by
    linarith [hx1.1]
  have hy4 : ‖(E.boundedPlugSideLiftInverse h hlin t (E.boundedSplitTubeMap h hlin (shellDir t
      y))).1‖ < 4 := by
    linarith [hy1.1]
  have e1 := torusPD_injOn hx4 hy4 he
  have e2 := congrArg (E.boundedPlugSideLiftMap h hlin t) e1
  rw [hx2, hy2] at e2
  have e3 := E.boundedSplitTubeMap_injOn h hlin (abs_shellDir_lt t hx) (abs_shellDir_lt t hy) e2
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

theorem exists_boundedPlugSideShellPD (t : Bool) :
    ∃ F : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      F.toPartialEquiv.source = shellSet ∧ ∀ x, F x = E.boundedPlugSideShellMap h hlin t x := by
  obtain ⟨F, hs, -, hf⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (fun x => E.boundedPlugSideShellMap_local h hlin t x.2) isOpen_shellSet
    ⟨(EuclideanSpace.single 0 1 : E3), by simp [shellSet]; norm_num⟩
        (E.boundedPlugSideShellMap_injOn h hlin t)
  exact ⟨F, hs, fun x => congrFun hf x⟩


theorem boundedPlugSideLevel_continuousOn (t : Bool) :
    ContinuousOn (E.boundedPlugSideLevel h t) {q : ℂ × Circle | ‖q.1‖ ≤ 3} := by
  have hcn : Continuous fun q : ℂ × Circle => ‖q.1‖ := continuous_norm.comp continuous_fst
  refine (contDiff_stripLevel _).continuous.comp_continuousOn ?_
  exact (sideData (E.boundedPlugSideHost h) t).continuousOn_point.comp
    (continuous_snd.prodMk hcn).continuousOn fun q hq => ⟨mem_univ _, norm_nonneg _, hq⟩

theorem boundedPlugSideLevel_gt_three (t : Bool) {q : ℂ × Circle} (h1 : 5 / 2 ≤ ‖q.1‖)
    (h3 : ‖q.1‖ ≤ 3) : 3 < sgnR t * E.boundedPlugSideLevel h t q :=
  three_lt_level_of_ge _ t h1 h3

def boundedPlugSideFakeSet (t : Bool) : Set (ℂ × Circle) :=
  {q | ‖q.1‖ < 3 ∧ sgnR t * E.boundedPlugSideLevel h t q < 2}

theorem boundedPlugSideFakeSet_open (t : Bool) : IsOpen (E.boundedPlugSideFakeSet h t) := by
  have hcn : Continuous fun q : ℂ × Circle => ‖q.1‖ := continuous_norm.comp continuous_fst
  have hc : ContinuousOn (fun q : ℂ × Circle => sgnR t * E.boundedPlugSideLevel h t q)
      {q | ‖q.1‖ < 3} :=
    (continuousOn_const.mul (E.boundedPlugSideLevel_continuousOn h t)).mono fun q hq =>
      show ‖q.1‖ ≤ 3 from le_of_lt hq
  exact hc.isOpen_inter_preimage (isOpen_lt hcn continuous_const)
    (isOpen_lt continuous_id continuous_const)

theorem boundedPlugSideFakeSet_preconnected (t : Bool) : IsPreconnected
    (E.boundedPlugSideFakeSet h t) := by
  set l := E.boundedPlugSideHost h
  have hS := isPreconnected_levelPoints l t
  have himg : (fun x : Circle × (Circle × ℝ) => ((x.2.2 : ℝ) • (x.1 : ℂ), x.2.1)) ''
      (univ ×ˢ {p : Circle × ℝ | p.2 ∈ Icc (0 : ℝ) 3 ∧
        sgnR t * stripLevel l ((sideData l t).point p) < 2}) = E.boundedPlugSideFakeSet h t := by
    ext q
    constructor
    · rintro ⟨⟨φ, ⟨u, ρ⟩⟩, ⟨-, hρ, hlev⟩, rfl⟩
      have hn : ‖(ρ • (φ : ℂ))‖ = ρ := by
        rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hρ.1]
      have hρ3 : ρ < 3 := by
        by_contra hc
        push Not at hc
        have := three_lt_level_of_ge l t (u := u) (by linarith) hρ.2
        dsimp only at hlev
        linarith
      refine ⟨by dsimp only; rw [hn]; exact hρ3, ?_⟩
      change sgnR t * stripLevel l ((sideData l t).point (u, ‖ρ • (φ : ℂ)‖)) < 2
      rw [hn]
      exact hlev
    · rintro ⟨hq3, hlev⟩
      refine ⟨(unitOf q.1, (q.2, ‖q.1‖)), ⟨mem_univ _, ⟨norm_nonneg _, hq3.le⟩, hlev⟩, ?_⟩
      exact Prod.ext (norm_smul_unitOf q.1) rfl
  rw [← himg]
  refine (isPreconnected_univ.prod hS).image _ (Continuous.continuousOn ?_)
  exact ((continuous_snd.comp continuous_snd).smul
    (continuous_subtype_val.comp continuous_fst)).prodMk (continuous_fst.comp continuous_snd)



theorem exists_boundedPlugSideFill (t : Bool) :
    ∃ G : E3 ≃ₘ[ℝ] E3,
      (∀ q : ℂ × Circle, ‖q.1‖ < 3 → sgnR t * E.boundedPlugSideLevel h t q ≤ 2 →
        ‖G.symm (torusPD q)‖ ≤ 1) ∧
      (∀ x : E3, ‖x‖ ≤ 1 → ∃ q : ℂ × Circle, ‖q.1‖ < 3 ∧ sgnR t * E.boundedPlugSideLevel h t q ≤ 2 ∧
        G x = torusPD q) ∧
      ∃ V : Set E3, IsOpen V ∧ sphere (0 : E3) 1 ⊆ V ∧ V ⊆ shellSet ∧
        ∀ x ∈ V, G x = E.boundedPlugSideShellMap h hlin t x := by
  obtain ⟨F, hFs, hF⟩ := E.exists_boundedPlugSideShellPD h hlin t
  set D := E.boundedPlugSideFakeSet h t with hD
  set U := torusPD '' D with hU
  have hDsrc : D ⊆ torusPD.source := fun q hq => show ‖q.1‖ < 4 by linarith [hq.1]
  have hUo : IsOpen U := torusPD.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (E.boundedPlugSideFakeSet_open h t) hDsrc
  have hUb : Bornology.IsBounded U := (isBounded_closedBall (x := (0 : E3)) (r := 10)).subset
    (by rintro _ ⟨q, hq, rfl⟩; exact mem_closedBall_zero_iff.mpr (norm_torusPD_le hq.1.le))
  have hUc : IsPreconnected U := (E.boundedPlugSideFakeSet_preconnected h t).image _
    (torusPD.toOpenPartialHomeomorph.continuousOn.mono hDsrc)
  set Dc : Set (ℂ × Circle) := {q | ‖q.1‖ ≤ 3 ∧ sgnR t * E.boundedPlugSideLevel h t q ≤ 2} with hDc
  have hDc_lt : ∀ q ∈ Dc, ‖q.1‖ < 3 := by
    intro q hq
    by_contra hc
    push Not at hc
    linarith [E.boundedPlugSideLevel_gt_three h t (q := q) (by linarith) hq.1, hq.2]
  have hDc_closed : IsClosed Dc :=
    (continuousOn_const.mul (E.boundedPlugSideLevel_continuousOn h t)).preimage_isClosed_of_isClosed
      (isClosed_le (continuous_norm.comp continuous_fst) continuous_const) isClosed_Iic
  have hDc_compact : IsCompact Dc :=
    ((isCompact_closedBall (0 : ℂ) 3).prod isCompact_univ).of_isClosed_subset hDc_closed
      fun q hq => ⟨mem_closedBall_zero_iff.mpr hq.1, mem_univ _⟩
  have hDcsrc : Dc ⊆ torusPD.source := fun q hq => show ‖q.1‖ < 4 by linarith [hq.1]
  have hcl : closure U ⊆ torusPD '' Dc := closure_minimal
    (image_mono fun q hq => ⟨hq.1.le, hq.2.le⟩)
    (hDc_compact.image_of_continuousOn
      (torusPD.toOpenPartialHomeomorph.continuousOn.mono hDcsrc)).isClosed
  have hinj : ∀ q ∈ Dc, ∀ q' : ℂ × Circle, ‖q'.1‖ < 3 → torusPD q = torusPD q' → q = q' :=
    fun q hq q' hq' he => torusPD_injOn (show ‖q.1‖ < 4 by linarith [hq.1])
      (show ‖q'.1‖ < 4 by linarith) he
  have hshell : ∀ x ∈ shellSet, ∃ q ∈ E.boundedPlugSideLiftDomain h t, F x = torusPD q ∧
      sgnR t * E.boundedPlugSideLevel h t q = 2 * ‖x‖ := by
    intro x hx
    obtain ⟨h1, -, h3⟩ := E.boundedPlugSideShellMap_spec h hlin t hx
    exact ⟨_, h1, hF x, h3⟩
  have hin : ∀ x ∈ F.source, ‖x‖ < 1 → F x ∈ U := by
    intro x hx hx1
    rw [show F.source = shellSet from hFs] at hx
    obtain ⟨q, hq, hFq, hlev⟩ := hshell x hx
    exact ⟨q, ⟨hq.1, by rw [hlev]; linarith⟩, hFq.symm⟩
  have hout : ∀ x ∈ F.source, 1 < ‖x‖ → F x ∉ closure U := by
    intro x hx hx1 hmem
    rw [show F.source = shellSet from hFs] at hx
    obtain ⟨q, hq, hFq, hlev⟩ := hshell x hx
    obtain ⟨q', hq', he⟩ := hcl hmem
    rw [hFq] at he
    have := hinj q' hq' q hq.1 he
    rw [← this] at hlev
    linarith [hq'.2]
  have hlevel2 : ∀ q : ℂ × Circle, ‖q.1‖ < 3 → sgnR t * E.boundedPlugSideLevel h t q = 2 →
      torusPD q ∈ F '' sphere (0 : E3) 1 := by
    intro q hq3 hq2
    have hL : E.boundedPlugSideLevel h t q = 2 * sgnR t := by
      have := sgnR_mul_self t
      linear_combination sgnR t * hq2 - E.boundedPlugSideLevel h t q * this
    have hlev3 : |E.boundedPlugSideLevel h t q| < 3 := by
      rw [hL, mul_comm, SplitCharts.abs_sgnR_mul]
      norm_num
    have hqd : q ∈ E.boundedPlugSideLiftDomain h t := ⟨hq3, by rw [hq2]; norm_num⟩
    obtain ⟨p, hp⟩ := E.boundedPlugSideTube_cover h hlin t (E.boundedPlugSideDom_of_mem_domain h
        hqd) hq3 hlev3
    have hpn : ‖(p : E3)‖ = 1 := norm_eq_of_mem_sphere p
    have hdir : shellDir t (p : E3) = (p, E.boundedPlugSideLevel h t q) := by
      refine Prod.ext ?_ ?_
      · change Manifold.sphereDirection poleS2 (p : E3) = p
        have := Manifold.sphereDirection_pos_smul poleS2 p one_pos
        rwa [one_smul] at this
      · change 2 * sgnR t * ‖(p : E3)‖ = _
        rw [hpn, hL]
        ring
    refine ⟨(p : E3), p.2, ?_⟩
    rw [hF, boundedPlugSideShellMap, hdir, hp, E.boundedPlugSideLiftInverse_lift h hlin hqd]
  have hfront : frontier U = F '' sphere (0 : E3) 1 := by
    apply Subset.antisymm
    · intro y hy
      rw [hUo.frontier_eq] at hy
      obtain ⟨q, hq, rfl⟩ := hcl hy.1
      have h2 : sgnR t * E.boundedPlugSideLevel h t q = 2 :=
        le_antisymm hq.2 (not_lt.mp fun hlt => hy.2 ⟨q, ⟨hDc_lt q hq, hlt⟩, rfl⟩)
      exact hlevel2 q (hDc_lt q hq) h2
    · rintro _ ⟨x, hx, rfl⟩
      have hxs : x ∈ shellSet := sphere_subset_shellSet hx
      have hxn : ‖x‖ = 1 := norm_eq_of_mem_sphere ⟨x, hx⟩
      rw [hUo.frontier_eq]
      refine ⟨?_, ?_⟩
      · have hc1 : ContinuousAt F x :=
          F.toOpenPartialHomeomorph.continuousAt (show x ∈ F.source by rw [hFs]; exact hxs)
        have hc : ContinuousAt (fun s : ℝ => F (s • x)) 1 :=
          hc1.comp_of_eq (continuous_id.smul continuous_const).continuousAt (one_smul ℝ x)
        have ht : Tendsto (fun s : ℝ => F (s • x)) (𝓝[<] (1 : ℝ)) (𝓝 (F x)) := by
          have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
          rwa [one_smul] at this
        refine mem_closure_of_tendsto ht ?_
        · have hI : Ioo (3 / 4 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
          filter_upwards [hI] with s hs
          have hsn : ‖s • x‖ = s := by
            rw [norm_smul, hxn, mul_one, Real.norm_of_nonneg (by linarith [hs.1])]
          exact hin _ (by rw [hFs]; exact ⟨by rw [hsn]; exact hs.1, by rw [hsn]; linarith [hs.2]⟩)
            (by rw [hsn]; exact hs.2)
      · rintro ⟨q', hq', he⟩
        obtain ⟨q, hq, hFq, hlev⟩ := hshell x hxs
        rw [hFq] at he
        have := hinj q ⟨hq.1.le, by rw [hlev, hxn]; norm_num⟩ q' hq'.1 he.symm
        rw [this, hxn] at hlev
        linarith [hq'.2]
  obtain ⟨G, -, hGcb, V, hV, hSV, hVs, hGV⟩ := exists_ballFill_of_shell F
    (by rw [hFs]; exact sphere_subset_shellSet) hUo hUb hUc hfront hin hout
  refine ⟨G, ?_, ?_, V, hV, hSV, by rwa [hFs] at hVs, fun x hx => (hGV hx).trans (hF x)⟩
  · intro q hq3 hq2
    have hmem : torusPD q ∈ closure U := by
      rcases lt_or_eq_of_le hq2 with hlt | heq
      · exact subset_closure ⟨q, ⟨hq3, hlt⟩, rfl⟩
      · have := hlevel2 q hq3 heq
        rw [← hfront] at this
        exact frontier_subset_closure this
    rw [← hGcb] at hmem
    obtain ⟨x, hx, hxe⟩ := hmem
    rw [← hxe, G.symm_apply_apply]
    exact mem_closedBall_zero_iff.mp hx
  · intro x hx
    have : G x ∈ closure U := hGcb ▸ ⟨x, mem_closedBall_zero_iff.mpr hx, rfl⟩
    obtain ⟨q, hq, hqe⟩ := hcl this
    exact ⟨q, hDc_lt q hq, hq.2, hqe.symm⟩


end GC.Seifert.ElementaryPresentation

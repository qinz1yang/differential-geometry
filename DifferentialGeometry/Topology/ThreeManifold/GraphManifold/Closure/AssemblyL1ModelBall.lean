import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelZone
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1StandardFacts

/-!
# Chapter-14 assembly, item L1, group G3a: the balls of the model cycle

A point `x` of `ℝ³` has ball coordinates `ballCoord x = (J (π x), ⟪N, x⟫)` (`π` the orthogonal
projection onto the plane orthogonal to the north pole `N`, `J` the isometry of that plane with
`ℝ²` used by the stereographic charts). The model ball centred at height `c` is the fibrewise
radial map `ballMap ε c x = (ballRatioSq ε ‖ξ‖² h • ξ, c - h)` (`(ξ, h) = ballCoord x`): it is smooth,
injective and has injective differential on all of `ℝ³` (`ballMap_injective`,
`injective_fderiv_ballMap`), and on the cap regions it is the zone map read in the cap charts
(`ballMap_eq_zoneChartMap_south`, `ballMap_eq_zoneChartMap_north`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold
open scoped ContDiff Topology Manifold InnerProductSpace

namespace GC.GraphManifold.Assembly

local instance fact_finrank_three_ASML1d :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

/-- The north pole as a vector. -/
abbrev northVec : EuclideanSpace ℝ (Fin 3) := (northPole : EuclideanSpace ℝ (Fin 3))

/-- The isometry of the plane orthogonal to the north pole with `ℝ²` (stereographic charts). -/
def ballPlaneIso : (ℝ ∙ northVec)ᗮ ≃ₗᵢ[ℝ] ModelPlane :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere northPole)).repr

/-- The ball coordinates of a point of `ℝ³`. -/
def ballCoord : EuclideanSpace ℝ (Fin 3) →L[ℝ] ModelSpace :=
  ((ballPlaneIso.toContinuousLinearEquiv : (ℝ ∙ northVec)ᗮ →L[ℝ] ModelPlane).comp
    (ℝ ∙ northVec)ᗮ.orthogonalProjectionOnto).prod (innerSL ℝ northVec)

theorem ballCoord_fst (x : EuclideanSpace ℝ (Fin 3)) :
    (ballCoord x).1 = ballPlaneIso ((ℝ ∙ northVec)ᗮ.orthogonalProjectionOnto x) := rfl

theorem ballCoord_snd (x : EuclideanSpace ℝ (Fin 3)) : (ballCoord x).2 = ⟪northVec, x⟫_ℝ := rfl

theorem norm_northVec : ‖northVec‖ = 1 := norm_eq_of_mem_sphere northPole

/-- The decomposition of a point along the north pole. -/
theorem coe_orthogonalProjectionOnto_north (x : EuclideanSpace ℝ (Fin 3)) :
    (((ℝ ∙ northVec)ᗮ.orthogonalProjectionOnto x : (ℝ ∙ northVec)ᗮ) :
      EuclideanSpace ℝ (Fin 3)) = x - ⟪northVec, x⟫_ℝ • northVec := by
  have h1 := (ℝ ∙ northVec).starProjection_add_starProjection_orthogonal x
  have h2 := Submodule.starProjection_unit_singleton ℝ norm_northVec x
  change (ℝ ∙ northVec)ᗮ.starProjection x = _
  rw [← h2]
  exact eq_sub_of_add_eq' h1

theorem norm_sq_ballCoord (x : EuclideanSpace ℝ (Fin 3)) :
    ‖(ballCoord x).1‖ ^ 2 + (ballCoord x).2 ^ 2 = ‖x‖ ^ 2 := by
  rw [ballCoord_fst, ballCoord_snd, LinearIsometryEquiv.norm_map, ← Submodule.norm_coe,
    coe_orthogonalProjectionOnto_north]
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  have hNN : ⟪northVec, northVec⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_northVec]
    norm_num
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hNN,
    RCLike.conj_to_real, real_inner_comm x northVec]
  ring

theorem ballCoord_injective : Injective ballCoord := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  rw [ballCoord_fst, ballCoord_fst] at h1
  rw [ballCoord_snd, ballCoord_snd] at h2
  have h3 := congrArg Subtype.val (ballPlaneIso.injective h1)
  rw [coe_orthogonalProjectionOnto_north, coe_orthogonalProjectionOnto_north, h2] at h3
  exact sub_left_injective h3

/-- The reflection through the equatorial plane fixes the projection and negates the height. -/
theorem ballCoord_reflectThree (x : EuclideanSpace ℝ (Fin 3)) :
    ballCoord (reflectThree x) = ((ballCoord x).1, -(ballCoord x).2) := by
  have hN : reflectThree northVec = -northVec := by
    rw [northVec, reflectThree_north, southPole_val, northPole_val]
  have hh : ⟪northVec, reflectThree x⟫_ℝ = -⟪northVec, x⟫_ℝ := by
    rw [real_inner_comm, inner_reflectThree, real_inner_comm, hN, inner_neg_left]
  refine Prod.ext ?_ ?_
  · rw [ballCoord_fst, ballCoord_fst]
    congr 1
    apply Subtype.ext
    rw [coe_orthogonalProjectionOnto_north, coe_orthogonalProjectionOnto_north, hh]
    -- `reflectThree x = x - 2 ⟪N, x⟫ N`
    have hr : reflectThree x = x - (2 * ⟪northVec, x⟫_ℝ) • northVec := by
      have hx : x = (x - ⟪northVec, x⟫_ℝ • northVec) + ⟪northVec, x⟫_ℝ • northVec := by abel
      have hperp : x - ⟪northVec, x⟫_ℝ • northVec ∈ (ℝ ∙ (EuclideanSpace.single 2 1 :
          EuclideanSpace ℝ (Fin 3)))ᗮ := by
        rw [← northPole_val, Submodule.mem_orthogonal_singleton_iff_inner_right]
        rw [inner_sub_right, inner_smul_right]
        have hNN : ⟪northVec, northVec⟫_ℝ = 1 := by
          rw [real_inner_self_eq_norm_sq, norm_northVec]
          norm_num
        rw [hNN, mul_one, sub_self]
      have hfix : reflectThree (x - ⟪northVec, x⟫_ℝ • northVec) =
          x - ⟪northVec, x⟫_ℝ • northVec := (Submodule.reflection_eq_self_iff _).mpr hperp
      conv_lhs => rw [hx]
      rw [map_add, map_smul, hN, hfix]
      rw [smul_neg]
      have : (2 * ⟪northVec, x⟫_ℝ) • northVec = ⟪northVec, x⟫_ℝ • northVec +
          ⟪northVec, x⟫_ℝ • northVec := by rw [two_mul, add_smul]
      rw [this]
      abel
    rw [hr]
    simp only [neg_smul, sub_neg_eq_add]
    rw [sub_add_eq_add_sub, show (2 * ⟪northVec, x⟫_ℝ) • northVec = ⟪northVec, x⟫_ℝ • northVec +
      ⟪northVec, x⟫_ℝ • northVec by rw [two_mul, add_smul]]
    abel
  · rw [ballCoord_snd, ballCoord_snd, hh]

/-! ## The cap charts in ball coordinates -/

theorem stereoChart_north_apply (θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    DifferentialGeometry.Topology.Handle.stereoChart northPole θ =
      ballPlaneIso ((2 / (1 - ⟪northVec, (θ : EuclideanSpace ℝ (Fin 3))⟫_ℝ)) •
        (ℝ ∙ northVec)ᗮ.orthogonalProjectionOnto (θ : EuclideanSpace ℝ (Fin 3))) := rfl

/-- The south cap chart in ball coordinates. -/
theorem southCapMap_eq {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0)
    (hxh : ‖x‖ - ⟪northVec, x⟫_ℝ ≠ 0) :
    southCapMap x = ((2 / (‖x‖ - (ballCoord x).2)) • (ballCoord x).1, ‖x‖ - 1) := by
  rw [southCapMap_apply]
  congr 1
  rw [stereoChart_north_apply,
    DifferentialGeometry.Topology.Manifold.coe_sphereDirection _ hx, ballCoord_fst, ballCoord_snd]
  simp only [map_smul, inner_smul_right, smul_smul]
  congr 1
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp

theorem capMap_false_eq {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0)
    (hxh : ‖x‖ - ⟪northVec, x⟫_ℝ ≠ 0) :
    capMap false x = ((2 / (‖x‖ - (ballCoord x).2)) • (ballCoord x).1, ‖x‖ - 1) :=
  southCapMap_eq hx hxh

theorem capMap_true_eq {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0)
    (hxh : ‖x‖ + ⟪northVec, x⟫_ℝ ≠ 0) :
    capMap true x = ((2 / (‖x‖ + (ballCoord x).2)) • (ballCoord x).1, ‖x‖ - 1) := by
  rw [capMap_true]
  have hx' : reflectThree x ≠ 0 := by
    intro h
    apply hx
    have := congrArg reflectThree h
    rwa [reflectThree_reflectThree, map_zero] at this
  have hnorm := norm_reflectThree x
  have hc := ballCoord_reflectThree x
  rw [ballCoord_snd] at hc
  have hh : ⟪northVec, reflectThree x⟫_ℝ = -⟪northVec, x⟫_ℝ := by
    have := congrArg Prod.snd hc
    simpa [ballCoord_snd] using this
  rw [southCapMap_eq hx' (by rw [hnorm, hh, sub_neg_eq_add]; exact hxh), hnorm, ballCoord_reflectThree]
  simp only [sub_neg_eq_add]

/-! ## The model ball -/

variable {ε : ℝ}

/-- The radial part of the model ball centred at height `c`. -/
def ballRadial (ε c : ℝ) : ModelSpace → ModelSpace :=
  modelRadialMap (fun y => ballRatioSq ε (‖y.1‖ ^ 2) y.2) c (-1)

/-- **The model ball** centred at height `c`. -/
def ballMap (ε c : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : ModelSpace := ballRadial ε c (ballCoord x)

theorem ballMap_apply (ε c : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    ballMap ε c x = (ballRatioSq ε (‖(ballCoord x).1‖ ^ 2) (ballCoord x).2 • (ballCoord x).1,
      c - (ballCoord x).2) := by
  simp only [ballMap, ballRadial, modelRadialMap]
  congr 1
  ring

theorem ballRatioSq_pos (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (σ h : ℝ) : 0 < ballRatioSq ε σ h := by
  have hD := ballDen_pos σ h
  have hc := ballCutSq_ge (σ + h ^ 2)
  refine mul_pos ?_ (by positivity)
  apply neckRatio_pos hε hε'
  norm_num [ballCutCentre] at hc ⊢
  linarith

theorem norm_ballMap_fst (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖(ballMap ε c x).1‖ = ballRadius ε ‖(ballCoord x).1‖ (ballCoord x).2 := by
  rw [ballMap_apply, norm_smul, Real.norm_of_nonneg (ballRatioSq_pos hε hε' _ _).le, ballRadius,
    mul_comm]

theorem ballMap_snd (ε c : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    (ballMap ε c x).2 = c - (ballCoord x).2 := by
  rw [ballMap_apply]

theorem contDiff_ballRadial (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) :
    ContDiff ℝ ∞ (ballRadial ε c) := by
  have hin : ContDiff ℝ ∞ (fun y : ModelSpace => (‖y.1‖ ^ 2, y.2)) :=
    ((contDiff_norm_sq ℝ).comp contDiff_fst).prodMk contDiff_snd
  have hm : ContDiff ℝ ∞ (fun y : ModelSpace => ballRatioSq ε (‖y.1‖ ^ 2) y.2) :=
    ContDiff.comp (g := fun q : ℝ × ℝ => ballRatioSq ε q.1 q.2)
      (f := fun y : ModelSpace => (‖y.1‖ ^ 2, y.2)) (contDiff_ballRatioSq hε hε') hin
  exact (hm.smul contDiff_fst).prodMk (contDiff_const.add (contDiff_const.mul contDiff_snd))

theorem contDiff_ballMap (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) : ContDiff ℝ ∞ (ballMap ε c) :=
  (contDiff_ballRadial hε hε' c).comp ballCoord.contDiff

theorem ballMap_injective (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) : Injective (ballMap ε c) := by
  intro x y hxy
  have h2 := congrArg Prod.snd hxy
  rw [ballMap_snd, ballMap_snd] at h2
  have hh : (ballCoord x).2 = (ballCoord y).2 := by linarith
  have hn : ‖(ballMap ε c x).1‖ = ‖(ballMap ε c y).1‖ := by rw [hxy]
  rw [norm_ballMap_fst hε hε', norm_ballMap_fst hε hε', hh] at hn
  have hρ : ‖(ballCoord x).1‖ = ‖(ballCoord y).1‖ :=
    (ballRadius_strictMonoOn hε hε' (ballCoord y).2).injOn (norm_nonneg _) (norm_nonneg _) hn
  have h1 := congrArg Prod.fst hxy
  rw [ballMap_apply, ballMap_apply] at h1
  simp only at h1
  rw [hρ, hh] at h1
  have hξ : (ballCoord x).1 = (ballCoord y).1 :=
    smul_right_injective _ (ballRatioSq_pos hε hε' _ _).ne' h1
  exact ballCoord_injective (Prod.ext hξ hh)

theorem injective_fderiv_ballRadial (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) (p : ModelSpace) :
    Injective (fderiv ℝ (ballRadial ε c) p) := by
  have hin : ContDiff ℝ ∞ (fun y : ModelSpace => (‖y.1‖ ^ 2, y.2)) :=
    ((contDiff_norm_sq ℝ).comp contDiff_fst).prodMk contDiff_snd
  have hm : ContDiff ℝ ∞ (fun y : ModelSpace => ballRatioSq ε (‖y.1‖ ^ 2) y.2) :=
    ContDiff.comp (g := fun q : ℝ × ℝ => ballRatioSq ε q.1 q.2)
      (f := fun y : ModelSpace => (‖y.1‖ ^ 2, y.2)) (contDiff_ballRatioSq hε hε') hin
  apply injective_fderiv_modelRadialMap ((hm.differentiable (by simp)) p).hasFDerivAt
  · intro y y' hn h2
    simp only [hn, h2]
  · exact (ballRatioSq_pos hε hε' _ _).ne'
  · norm_num
  · intro hz
    set ρ := ‖p.1‖ with hρdef
    have hρ : 0 < ρ := norm_pos_iff.mpr hz
    obtain ⟨d, hd, hder⟩ := hasDerivAt_ballRadius hε hε' hρ p.2
    have hline : HasDerivAt (fun t : ℝ => t * ρ) ρ 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).mul_const ρ
    have hder1 : HasDerivAt (fun ρ' => ballRadius ε ρ' p.2) d (1 * ρ) := by
      rw [one_mul]
      exact hder
    have hcomp := (hder1.comp (1 : ℝ) hline).div_const ρ
    refine ⟨d, hd.ne', ?_⟩
    have heq : (fun t : ℝ => t * ballRatioSq ε (‖t • p.1‖ ^ 2) p.2) =
        fun t => ballRadius ε (t * ρ) p.2 / ρ := by
      funext t
      rw [ballRadius, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← hρdef, ← mul_pow]
      field_simp
    rw [heq]
    simpa [Function.comp_def, hρ.ne'] using hcomp

theorem injective_fderiv_ballMap (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : Injective (fderiv ℝ (ballMap ε c) x) := by
  have hcomp : ballMap ε c = ballRadial ε c ∘ ballCoord := rfl
  rw [hcomp, fderiv_comp x (((contDiff_ballRadial hε hε' c).differentiable (by simp)) _)
    ballCoord.differentiableAt, ballCoord.fderiv]
  exact (injective_fderiv_ballRadial hε hε' c _).comp ballCoord_injective

/-! ## The ball in the cap charts -/

theorem sqrt_ballCoord (x : EuclideanSpace ℝ (Fin 3)) :
    Real.sqrt (‖(ballCoord x).1‖ ^ 2 + (ballCoord x).2 ^ 2) = ‖x‖ := by
  rw [norm_sq_ballCoord, Real.sqrt_sq (norm_nonneg x)]

theorem abs_ballCoord_snd_le (x : EuclideanSpace ℝ (Fin 3)) : |(ballCoord x).2| ≤ ‖x‖ := by
  have h := norm_sq_ballCoord x
  have h0 := sq_nonneg ‖(ballCoord x).1‖
  exact abs_le_of_sq_le_sq' (by nlinarith) (norm_nonneg x) |> fun h => abs_le.mpr h

/-- **The ball is the lower neck in the south cap chart.** -/
theorem ballMap_eq_zoneChartMap_south (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hR : 3 / 4 < ‖x‖) (hR' : ‖x‖ ≤ 4 / 3)
    (hh : (ballCoord x).2 ≤ -1 / 4) (hz : ‖(capMap false x).1‖ < 13 / 10) :
    ballMap ε c x = zoneChartMap ε c (capMap false x) := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hR
    linarith
  have hRh : 0 < ‖x‖ - (ballCoord x).2 := by linarith
  have hcap := capMap_false_eq hx0 (by rw [← ballCoord_snd]; exact hRh.ne')
  set ξ := (ballCoord x).1
  set h := (ballCoord x).2
  set R := ‖x‖
  set s := 2 * ‖ξ‖ / (R - h) with hs
  have hzs : ‖(capMap false x).1‖ = s := by
    rw [hcap, norm_smul, Real.norm_of_nonneg (by positivity), hs]
    ring
  rw [hzs] at hz
  have hnorm : ‖(2 / (R - h)) • ξ‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), hs]
    ring
  rw [hcap, zoneChartMap_neck hε hε' c (by rw [hnorm]; exact hz) (by linarith) (by linarith)]
  rw [hnorm, ballMap_apply]
  have hR2 : R ^ 2 = ‖ξ‖ ^ 2 + h ^ 2 := (norm_sq_ballCoord x).symm
  have hcos : (1 + (R - 1)) * capCos s = -h := by
    rw [add_sub_cancel, hs]
    exact mul_capCos_south hR2 (norm_nonneg x) hRh
  refine Prod.ext ?_ ?_
  · simp only
    rw [smul_smul]
    congr 1
    have hhabs : |h| = -h := abs_of_neg (by linarith)
    have hcut : ballCutCentre + ballCutWidth ≤ Real.sqrt (‖ξ‖ ^ 2 + h ^ 2) := by
      rw [sqrt_ballCoord]
      norm_num [ballCutCentre, ballCutWidth]
      linarith
    rw [ballRatioSq, ballDen, ballCutSq, ballCut_eq_self hcut, sqrt_ballCoord,
      ballHeightAbs_eq (by rw [hhabs]; linarith), hhabs, neckRatioSq,
      show 4 * ‖ξ‖ ^ 2 / (R + -h) ^ 2 = s ^ 2 by
        rw [hs, div_pow, show R + -h = R - h by ring]; ring,
      Real.sqrt_sq (by positivity), ← sub_eq_add_neg]
  · simp only
    rw [hcos]
    ring

/-- **The ball is the flipped upper neck in the north cap chart.** -/
theorem ballMap_eq_zoneChartMap_north (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hR : 3 / 4 < ‖x‖) (hR' : ‖x‖ ≤ 4 / 3)
    (hh : 1 / 4 ≤ (ballCoord x).2) (hz : ‖(capMap true x).1‖ < 13 / 10) :
    ballMap ε (c + 4) x = zoneChartMap ε c ((capMap true x).1, 1 - (capMap true x).2) := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hR
    linarith
  have hRh : 0 < ‖x‖ + (ballCoord x).2 := by linarith
  have hcap := capMap_true_eq hx0 (by rw [← ballCoord_snd]; exact hRh.ne')
  set ξ := (ballCoord x).1
  set h := (ballCoord x).2
  set R := ‖x‖
  set s := 2 * ‖ξ‖ / (R + h) with hs
  have hzs : ‖(capMap true x).1‖ = s := by
    rw [hcap, norm_smul, Real.norm_of_nonneg (by positivity), hs]
    ring
  rw [hzs] at hz
  rw [hcap]
  simp only
  have hnorm : ‖(2 / (R + h)) • ξ‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), hs]
    ring
  rw [zoneChartMap_neck_flip hε hε' c (by rw [hnorm]; exact hz) (by linarith) (by linarith)]
  rw [hnorm, ballMap_apply]
  have hR2 : R ^ 2 = ‖ξ‖ ^ 2 + (-h) ^ 2 := by rw [neg_sq]; exact (norm_sq_ballCoord x).symm
  have hcos : (1 + (R - 1)) * capCos s = h := by
    rw [add_sub_cancel, hs, show R + h = R - -h by ring]
    have := mul_capCos_south hR2 (norm_nonneg x) (by linarith)
    linarith
  refine Prod.ext ?_ ?_
  · simp only
    rw [smul_smul]
    congr 1
    have hhabs : |h| = h := abs_of_pos (by linarith)
    have hcut : ballCutCentre + ballCutWidth ≤ Real.sqrt (‖ξ‖ ^ 2 + h ^ 2) := by
      rw [sqrt_ballCoord]
      norm_num [ballCutCentre, ballCutWidth]
      linarith
    rw [ballRatioSq, ballDen, ballCutSq, ballCut_eq_self hcut, sqrt_ballCoord,
      ballHeightAbs_eq (by rw [hhabs]; linarith), hhabs, neckRatioSq,
      show 4 * ‖ξ‖ ^ 2 / (R + h) ^ 2 = s ^ 2 by rw [hs, div_pow]; ring,
      Real.sqrt_sq (by positivity)]
  · simp only
    rw [hcos]

/-! ## Slices of the ball -/

/-- The radius of the model ball at a point is at most the radius on the sphere at the same height. -/
theorem norm_ballMap_fst_le (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ ≤ 1) :
    ‖(ballMap ε c x).1‖ ≤
      ballRadius ε (Real.sqrt (1 - (ballCoord x).2 ^ 2)) (ballCoord x).2 := by
  rw [norm_ballMap_fst hε hε']
  apply (ballRadius_strictMonoOn hε hε' _).monotoneOn (norm_nonneg _) (Real.sqrt_nonneg _)
  apply Real.le_sqrt_of_sq_le
  have h := norm_sq_ballCoord x
  have h1 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  linarith

/-- The sphere radius of the model ball at a height `|h| ≥ 1/4` is the neck radius at the polar
stereographic radius. -/
theorem ballRadius_sphere (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {h : ℝ} (hh : 1 / 4 ≤ |h|)
    (hh' : |h| ≤ 1) :
    ballRadius ε (Real.sqrt (1 - h ^ 2)) h =
      neckRadius ε (2 * Real.sqrt (1 - h ^ 2) / (1 + |h|)) 0 ∧
    capCos (2 * Real.sqrt (1 - h ^ 2) / (1 + |h|)) = |h| := by
  have h1 : 0 ≤ 1 - h ^ 2 := by nlinarith [sq_abs h, abs_nonneg h]
  have hsq : Real.sqrt (Real.sqrt (1 - h ^ 2) ^ 2 + h ^ 2) = 1 := by
    rw [Real.sq_sqrt h1]
    simp
  refine ⟨?_, ?_⟩
  · rw [ballRadius_eq_cap hε hε' (Real.sqrt_nonneg _) hh (by rw [hsq]; norm_num [ballCutCentre,
      ballCutWidth]), hsq, sub_self]
  · have := mul_capCos_south (ρ := Real.sqrt (1 - h ^ 2)) (h := -|h|) (R := 1)
      (by rw [Real.sq_sqrt h1, neg_sq, sq_abs]; ring) zero_le_one (by linarith)
    rw [one_mul, sub_neg_eq_add, neg_neg] at this
    exact this

end GC.GraphManifold.Assembly

import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugSignSides
import Mathlib.Topology.Order.IntermediateValue

/-!
The middle sphere of the fixed bounded fibre plug is exactly the union of the
actual host strip-zero cylinder and the actual solid meridian discs.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.SplitTube

def fibrePlugJunctionHeight : ℝ := Real.sqrt 3 / 2

theorem fibrePlugJunctionHeight_bounds :
    1 / 2 < fibrePlugJunctionHeight ∧ fibrePlugJunctionHeight < 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  unfold fibrePlugJunctionHeight
  constructor <;> nlinarith

theorem fibrePlugJunctionHeight_sq : fibrePlugJunctionHeight ^ 2 = 3 / 4 := by
  unfold fibrePlugJunctionHeight
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem fibrePlugJunctionHeight_seam : seamHeight fibrePlugJunctionHeight = 0 := by
  have he : latRadius fibrePlugJunctionHeight = 1 / 2 := by
    unfold latRadius
    rw [fibrePlugJunctionHeight_sq]
    norm_num
  rw [seamHeight, he]
  norm_num

theorem fibrePlugJunctionHeight_band (l : ℕ) :
    bandHeight l fibrePlugJunctionHeight = hostRadius l 0 ∧
      bandHeight l (-fibrePlugJunctionHeight) = -hostRadius l 0 := by
  have hn : seamHeight (-fibrePlugJunctionHeight) = 0 := by
    simpa [seamHeight, latRadius] using fibrePlugJunctionHeight_seam
  constructor
  · rw [bandHeight_of_ge l fibrePlugJunctionHeight_bounds.1.le,
      fibrePlugJunctionHeight_seam]
  · rw [bandHeight_of_le l (by linarith [fibrePlugJunctionHeight_bounds.1]), hn]

theorem fibrePlug_bandHeight_covers (l : ℕ) {Y : ℝ}
    (hY : |Y| ≤ hostRadius l 0) :
    ∃ x ∈ Icc (-fibrePlugJunctionHeight) fibrePlugJunctionHeight, bandHeight l x = Y := by
  have hb := fibrePlugJunctionHeight_bounds
  have hc : ContinuousOn (bandHeight l) (Icc (-fibrePlugJunctionHeight)
      fibrePlugJunctionHeight) := by
    intro x hx
    have hx1 : |x| < 1 := abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact (hasDerivAt_bandHeight l hx1).continuousAt.continuousWithinAt
  have hm := intermediate_value_Icc (by linarith :
    -fibrePlugJunctionHeight ≤ fibrePlugJunctionHeight) hc
  rw [fibrePlugJunctionHeight_band l |>.1, fibrePlugJunctionHeight_band l |>.2] at hm
  obtain ⟨x, hx, he⟩ := hm (abs_le.mp hY)
  exact ⟨x, hx, he⟩

theorem fibrePlug_circle_zero_phase {e : ℤ} (he : e = 1 ∨ e = -1) (ν : Circle)
    (hν : (((ν ^ e : Circle) : ℂ).re) = 0) : ∃ s : Bool, tubeFibre e s 0 = ν := by
  have hr : (ν : ℂ).re = 0 := (fibrePlug_circlePower_re e he ν).symm.trans hν
  have hn := Circle.normSq_coe ν
  rw [Complex.normSq_apply, hr] at hn
  have hi : (ν : ℂ).im = 1 ∨ (ν : ℂ).im = -1 :=
    mul_self_eq_one_iff.mp (by nlinarith [hn])
  rcases he with rfl | rfl <;> rcases hi with hi | hi
  · refine ⟨true, ?_⟩
    apply Circle.ext
    apply Complex.ext <;> simp [tubeFibre, hostTheta, Circle.coe_exp, hr, hi]
  · refine ⟨false, ?_⟩
    apply Circle.ext
    apply Complex.ext <;> simp [tubeFibre, hostTheta, Circle.coe_exp, hr, hi]
  · refine ⟨false, ?_⟩
    apply Circle.ext
    apply Complex.ext <;> simp [tubeFibre, hostTheta, Circle.coe_exp, hr, hi]
  · refine ⟨true, ?_⟩
    apply Circle.ext
    apply Complex.ext <;> simp [tubeFibre, hostTheta, Circle.coe_exp, hr, hi]

theorem fibrePlug_hostInv_norm_le (l : Fin 3) {z : ℂ} (hz : z ∈ planarModel 3) :
    ‖hostInv l z‖ ≤ hostRadius l.val 0 := by
  by_cases hl : l.val = 0
  · simpa only [hostInv, hostRadius, hl, ite_true, zero_div, sub_zero] using hz.1
  · have hr := hz.2 l hl
    have hp : 0 < ‖z - (planarCenter 3 l : ℂ)‖ := by linarith
    rw [hostInv_of_ne hl, norm_inv]
    simp only [hostRadius, hl, ite_false]
    norm_num
    exact (inv_le_comm₀ hp (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)

theorem fibrePlug_band_zero_covers (e₀ e₁ d : ℤ) (he₁ : e₁ = 1 ∨ e₁ = -1)
    (l : Fin 3) (z : ℂ) (hz : z ∈ planarModel 3) (ν : Circle)
    (hzero : stripLevel l (hostInv l z) = 0) :
    ∃ p : SphereTwo, 0 ≤ seamHeight (heightOf p) ∧ bandModel e₀ e₁ d l (p, 0) = (z, ν) := by
  let w := hostInv l z
  have hn : |w.im| ≤ hostRadius l.val 0 :=
    (Complex.abs_im_le_norm w).trans (fibrePlug_hostInv_norm_le l hz)
  obtain ⟨x, hx, hY⟩ := fibrePlug_bandHeight_covers l.val hn
  have hb := fibrePlugJunctionHeight_bounds
  have hx1 : |x| < 1 := abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  let θ := (ν * (bandPhase e₀ d x 0)⁻¹) ^ e₁
  let p := bandPoint (x, θ)
  have hp : heightOf p = x := heightOf_bandPoint hx1
  have hu : unitOf (planeOf p) = θ := by
    rw [planeOf_bandPoint hx1]
    exact unitOf_smul (latRadius_pos hx1) θ
  refine ⟨p, ?_, ?_⟩
  · have hsq : x ^ 2 ≤ 3 / 4 := by
      have hxa : |x| ≤ fibrePlugJunctionHeight := abs_le.mpr hx
      nlinarith [sq_abs x, fibrePlugJunctionHeight_sq, abs_nonneg x]
    have hr := latRadius_sq hx1.le
    have hr0 := latRadius_pos hx1
    rw [hp, seamHeight]
    nlinarith
  · unfold bandModel bandBase
    rw [hp, hu, zpow_zpow_unit he₁, inv_mul_cancel_right]
    apply Prod.ext
    swap
    · rfl
    have hscale : angleScale 0 = 1 := by norm_num [angleScale]
    rw [hscale, div_one, hY]
    rw [← hzero, strip_stripLevel, hostChart_hostInv]

theorem fibrePlug_cap_zero_covers {e : ℤ} (he : e = 1 ∨ e = -1)
    (z : ℂ) (hz : ‖z‖ ≤ 3) (ν : Circle) (hzero : (((ν ^ e : Circle) : ℂ).re) = 0) :
    ∃ p : SphereTwo, seamHeight (heightOf p) ≤ 0 ∧
      capModel e (SplitCharts.side (p, 0)) (p, 0) = (z, ν) := by
  obtain ⟨s, hs⟩ := fibrePlug_circle_zero_phase he ν hzero
  let w : ℂ := (1 / 6 : ℝ) • z
  have hn : ‖w‖ = ‖z‖ / 6 := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)]
    ring
  have hw : ‖w‖ < 1 := by rw [hn]; linarith
  let p := capPoint s w
  have hp : planeOf p = w := planeOf_capPoint s hw
  have hside : SplitCharts.side (p, 0) = s := by
    apply SplitCharts.side_eq_of_sgnR
    rw [heightOf_capPoint s hw, ← mul_assoc, sgnR_mul_self, one_mul]
    apply Real.sqrt_pos.mpr
    nlinarith [norm_nonneg w]
  refine ⟨p, ?_, ?_⟩
  · rw [seamHeight, latRadius_heightOf, hp, hn]
    linarith
  · rw [capModel, hp, hside, hs]
    apply Prod.ext
    swap
    · rfl
    change (6 : ℝ) • ((1 / 6 : ℝ) • z) = z
    rw [smul_smul]
    norm_num

theorem fibrePlug_band_junction (e₀ e₁ d : ℤ) (he₀ : e₀ = 1 ∨ e₀ = -1)
    (l : Fin 3) (p : SphereTwo) (hp : seamHeight (heightOf p) = 0) :
    bandModel e₀ e₁ d l (p, 0) =
      (planarCircleMap 3 l (tubeFibre e₀ (SplitCharts.side (p, 0)) 0 ^ e₀),
        unitOf (planeOf p) ^ e₁ * tubeFibre e₀ (SplitCharts.side (p, 0)) 0 ^ d) := by
  have hx := heightOf_ne_zero_of_seamHeight_lt (p := p) (by linarith)
  have hxp : heightOf p ≠ 0 := by intro he; rw [he, abs_zero] at hx; linarith
  have hR : angleScale 0 ≤ hostRadius l.val 0 := by
    norm_num [angleScale, hostRadius]
    split_ifs <;> norm_num
  have hcircle (θ : Circle) :
      planarCollarFormula 3 l ((θ : ℂ), 0) = planarCircleMap 3 l θ := by
    simp [planarCollarFormula, planarCircleMap, planarTwist, Complex.real_smul]
  unfold bandModel bandBase
  rcases lt_or_gt_of_ne hxp with hn | hn
  · have hs : SplitCharts.side (p, 0) = false := by
      simp [SplitCharts.side, not_lt.mpr hn.le]
    have hhalf : heightOf p ≤ -1 / 2 := by rw [abs_of_neg hn] at hx; linarith
    rw [hs, bandHeight_of_le l.val hhalf, hp, neg_div, strip_bot l hR,
      tubeFibre_zpow he₀, bandPhase, smoothSign_of_le hhalf]
    apply Prod.ext
    · have hc := hostChart_collar l (Circle.exp (-hostTheta 0))
        (by norm_num : (-2 : ℝ) < 0)
      have hf := hc.trans (hcircle (Circle.exp (-hostTheta 0)))
      simpa only [Circle.coe_exp, Bool.false_eq_true, ite_false, neg_one_mul] using hf
    · rw [tubeFibre_zpow_d]
      simp
  · have hs : SplitCharts.side (p, 0) = true := by simp [SplitCharts.side, hn]
    have hhalf : 1 / 2 ≤ heightOf p := by rw [abs_of_pos hn] at hx; linarith
    rw [hs, bandHeight_of_ge l.val hhalf, hp, strip_top l hR,
      tubeFibre_zpow he₀, bandPhase, smoothSign_of_ge hhalf]
    apply Prod.ext
    · have hc := hostChart_collar l (Circle.exp (hostTheta 0))
        (by norm_num : (-2 : ℝ) < 0)
      have hf := hc.trans (hcircle (Circle.exp (hostTheta 0)))
      simpa only [Circle.coe_exp, ite_true, one_mul] using hf
    · rw [tubeFibre_zpow_d]
      simp

theorem fibrePlug_tube_junction {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (C : SplitCharts M)
    (p : SphereTwo) (hp : seamHeight (heightOf p) = 0) :
    C.tubeMap (p, 0) = C.seam
      ((unitOf (planeOf p), tubeFibre C.e₀ (SplitCharts.side (p, 0)) 0), 0) := by
  simp only [SplitCharts.tubeMap, seamModel, hp, lt_self_iff_false, ite_false]

end GC.Seifert.SplitTube

namespace GC.Seifert.ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
variable {j : Fin E.toTorus.pairing.count} {b : Bool}
variable (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)

def fibrePlugHostZero : Set W.Carrier :=
  (fun q : pantsPlanarBase.{u}.surface.Carrier × Circle =>
    E.toTorus.cutMap ((E.splitData h).ΘH q).val) ''
      {q | SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
        (SplitTube.hostInv (E.fibrePlugFilledHostPort h) q.1.val.down) = 0}

def fibrePlugSolidZero : Set W.Carrier :=
  (fun q : (discPlanarBase.{u} 1).surface.Carrier × Circle =>
    E.toTorus.cutMap ((E.splitData h).ΘV q).val) ''
      {q | (((q.2 ^ (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re) = 0}

theorem fibrePlug_solid_zero_seam (τ : Torus) :
    E.toTorus.seam j (E.seamCoord j b (τ, 0)) =
      E.toTorus.cutMap ((E.splitData h).ΘV
        ((discPlanarBase.{u} 1).collar 0 (τ.1, halfZero), τ.2)).val := by
  have hpV : E.standardPort (E.seamPiece j b) h.1 0 =
      ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩ := by
    let : Subsingleton (E.toTorus.OwnedSide (E.seamPiece j b)) :=
      Fintype.card_le_one_iff_subsingleton.mp (E.card_ownedSide_seamPiece h).le
    exact Subsingleton.elim _ _
  have hV := (E.splitData h).hV 0 (τ, halfZero)
    (zero_mem_halfCollarSource τ) (E.splitData h).hδ
  rw [← hV, hpV, E.toTorus.pieceCollar_apply _ _ (zero_mem_halfCollarSource τ)]
  rw [seamCoord_apply, neg_zero]
  exact (E.cutMap_sideCollar_eq_seam j b τ 0 le_rfl zero_lt_one).symm

theorem fibrePlug_middle_cap_closed (p : SphereTwo)
    (hp : SplitTube.seamHeight (SplitTube.heightOf p) ≤ 0) :
    E.boundedSplitTubeMap h hlin (p, 0) =
      E.toTorus.pieceChart (E.seamPiece j b) (discPlanarBase 1)
        (E.splitData h).ΘV clampDisc
          (SplitTube.capModel (E.boundedSplitCharts h hlin).e₀
            (SplitTube.SplitCharts.side (p, 0)) (p, 0)) := by
  rcases lt_or_eq_of_le hp with hneg | hz
  · exact (E.fibrePlug_middle_cap h hlin p hneg).1
  · let τ : Torus := (unitOf (SplitTube.planeOf p),
      SplitTube.tubeFibre (E.boundedSplitCharts h hlin).e₀
        (SplitTube.SplitCharts.side (p, 0)) 0)
    have ht := SplitTube.fibrePlug_tube_junction (E.boundedSplitCharts h hlin) p hz
    have hτ : |(τ, (0 : ℝ)).2| < 1 := by norm_num
    have hv := E.boundedSplitCharts_seam_val h hlin (τ, 0) hτ
    have he : E.boundedSplitTubeMap h hlin (p, 0) =
        E.toTorus.cutMap ((E.splitData h).ΘV
          ((discPlanarBase.{u} 1).collar 0 (τ.1, halfZero), τ.2)).val :=
      (congrArg (boundedSplitInteriorVal W) ht).trans
        (hv.trans (E.fibrePlug_solid_zero_seam h τ))
    rw [he]
    change E.toTorus.cutMap ((E.splitData h).ΘV
      ((discPlanarBase.{u} 1).collar 0 (τ.1, halfZero), τ.2)).val =
        E.toTorus.cutMap ((E.splitData h).ΘV
          (clampDisc ((6 : ℝ) • SplitTube.planeOf p), τ.2)).val
    congr 3
    apply Prod.ext
    · have hd := discCollar_eq.{u} (θ := unitOf (SplitTube.planeOf p)) le_rfl zero_lt_one
      change (discPlanarBase.{u} 1).collar 0 (unitOf (SplitTube.planeOf p), halfZero) = _
      change (discPlanarBase.{u} 1).collar 0 (unitOf (SplitTube.planeOf p), halfZero) =
        clampDisc ((3 - 3 * (0 : ℝ) / 2 : ℝ) • (unitOf (SplitTube.planeOf p) : ℂ)) at hd
      apply hd.trans
      apply congrArg clampDisc
      have hn : ‖SplitTube.planeOf p‖ = 1 / 2 := by
        rw [SplitTube.seamHeight, SplitTube.latRadius_heightOf] at hz
        linarith
      rw [show (3 - 3 * (0 : ℝ) / 2 : ℝ) = 3 by norm_num]
      calc
        (3 : ℝ) • (unitOf (SplitTube.planeOf p) : ℂ) =
            (6 : ℝ) • (‖SplitTube.planeOf p‖ •
              (unitOf (SplitTube.planeOf p) : ℂ)) := by rw [hn, smul_smul]; norm_num
        _ = (6 : ℝ) • SplitTube.planeOf p :=
          congrArg (fun w : ℂ => (6 : ℝ) • w) (norm_smul_unitOf _)
    · rfl

theorem fibrePlug_band_cross_junction (p : SphereTwo)
    (hp : SplitTube.seamHeight (SplitTube.heightOf p) = 0) :
    SplitTube.bandModel (E.boundedSplitCharts h hlin).e₀
      (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).d
      (E.boundedSplitCharts h hlin).host (p, 0) =
        (planarCircleMap 3 (E.fibrePlugFilledHostPort h)
          (E.crossMap j b (unitOf (SplitTube.planeOf p),
            SplitTube.tubeFibre (E.boundedSplitCharts h hlin).e₀
              (SplitTube.SplitCharts.side (p, 0)) 0)).1,
          (E.crossMap j b (unitOf (SplitTube.planeOf p),
            SplitTube.tubeFibre (E.boundedSplitCharts h hlin).e₀
              (SplitTube.SplitCharts.side (p, 0)) 0)).2) := by
  have h0 := h.2.2
  rw [fillingDistance_eq_crossUnit, delta_smul_meridianSlope, Int.natAbs_eq_zero] at h0
  rw [SplitTube.fibrePlug_band_junction _ _ _ (E.boundedSplitCharts h hlin).he₀ _ _ hp,
    hlin.crossMap_apply]
  simp only [linearTorusMap, h0, zpow_zero, one_mul]
  rfl

theorem fibrePlug_middle_band_closed (p : SphereTwo)
    (hp : 0 ≤ SplitTube.seamHeight (SplitTube.heightOf p)) :
    E.boundedSplitTubeMap h hlin (p, 0) =
      E.toTorus.pieceChart (E.hostPiece j b) pantsPlanarBase
        (E.splitData h).ΘH clampPants
          (SplitTube.bandModel (E.boundedSplitCharts h hlin).e₀
            (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).d
            (E.boundedSplitCharts h hlin).host (p, 0)) := by
  rcases eq_or_lt_of_le hp with hz | hpos
  · let τ : Torus := (unitOf (SplitTube.planeOf p),
      SplitTube.tubeFibre (E.boundedSplitCharts h hlin).e₀
        (SplitTube.SplitCharts.side (p, 0)) 0)
    have ht := SplitTube.fibrePlug_tube_junction (E.boundedSplitCharts h hlin) p hz.symm
    have hτ : |(τ, (0 : ℝ)).2| < 1 := by norm_num
    have hv := E.boundedSplitCharts_seam_val h hlin (τ, 0) hτ
    have hm := E.fibrePlug_band_cross_junction h hlin p hz.symm
    have hcl (θ : Circle) :
        clampPants.{u} (planarCircleMap 3 (E.fibrePlugFilledHostPort h) θ) =
          pantsPlanarBase.collar (E.fibrePlugFilledHostPort h) (θ, halfZero) := by
      apply Subtype.ext
      apply ULift.ext
      have hc := clampPants_val.{u}
        (planarCircleMap_mem_planarModel le_rfl (E.fibrePlugFilledHostPort h) θ)
      exact (congrArg ULift.down hc).trans
        (planarCollar_zero_val.{u} (Or.inr rfl) _ _).symm
    have he := (congrArg (boundedSplitInteriorVal W) ht).trans
      (hv.trans ((E.fibrePlug_solid_zero_seam h τ).trans
        (E.fibrePlug_product_boundary_pair h τ)))
    rw [hm]
    change E.boundedSplitTubeMap h hlin (p, 0) =
      E.toTorus.cutMap ((E.splitData h).ΘH
        (clampPants (planarCircleMap 3 (E.fibrePlugFilledHostPort h)
          (E.crossMap j b τ).1), (E.crossMap j b τ).2)).val
    rw [hcl]
    exact he
  · exact (E.fibrePlug_middle_band h hlin p hpos).1

theorem fibrePlug_middle_zero_image :
    range (fun z : SphereTwo => E.boundedSplitTubeMap h hlin (z, 0)) =
      E.fibrePlugHostZero h ∪ E.fibrePlugSolidZero h hlin := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    by_cases hp : SplitTube.seamHeight (SplitTube.heightOf p) ≤ 0
    · right
      let q := SplitTube.capModel (E.boundedSplitCharts h hlin).e₀
        (SplitTube.SplitCharts.side (p, 0)) (p, 0)
      refine ⟨(clampDisc q.1, q.2), ?_, (E.fibrePlug_middle_cap_closed h hlin p hp).symm⟩
      change (((SplitTube.tubeFibre (E.boundedSplitCharts h hlin).e₀
        (SplitTube.SplitCharts.side (p, 0)) 0 ^
          (E.boundedSplitCharts h hlin).e₀ : Circle) : ℂ).re) = 0
      rw [SplitTube.fibrePlug_circlePower_re _ (E.boundedSplitCharts h hlin).he₀]
      exact SplitTube.fibrePlug_cap_fibre_zero _ (E.boundedSplitCharts h hlin).he₀ _
    · left
      have hp' : 0 < SplitTube.seamHeight (SplitTube.heightOf p) := lt_of_not_ge hp
      let q := SplitTube.bandModel (E.boundedSplitCharts h hlin).e₀
        (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).d
        (E.boundedSplitCharts h hlin).host (p, 0)
      have hq : q.1 ∈ planarModel 3 := SplitTube.pantsInterior_subset
        (SplitTube.hostChart_strip_mem (E.boundedSplitCharts h hlin).host
          (SplitTube.abs_heightOf_lt_of_seamHeight_pos hp') hp'
            (by norm_num : |(0 : ℝ)| < 3)).1
      refine ⟨(clampPants q.1, q.2), ?_, (E.fibrePlug_middle_band h hlin p hp').1.symm⟩
      change SplitTube.stripLevel (E.fibrePlugFilledHostPort h)
        (SplitTube.hostInv (E.fibrePlugFilledHostPort h) (clampPants q.1).val.down) = 0
      rw [clampPants_val hq]
      exact (E.fibrePlug_middle_band h hlin p hp').2
  · rintro (hx | hx)
    · obtain ⟨q, hq, rfl⟩ := hx
      have hbase : q.1.val.down ∈ planarModel 3 :=
        (mem_planarSet_iff (Or.inr rfl) _).mp q.1.property
      obtain ⟨p, hp, he⟩ := SplitTube.fibrePlug_band_zero_covers
        (E.boundedSplitCharts h hlin).e₀ (E.boundedSplitCharts h hlin).e₁
        (E.boundedSplitCharts h hlin).d (E.boundedSplitCharts h hlin).he₁
        (E.fibrePlugFilledHostPort h) q.1.val.down hbase q.2 hq
      refine ⟨p, ?_⟩
      change E.boundedSplitTubeMap h hlin (p, 0) =
        E.toTorus.cutMap ((E.splitData h).ΘH q).val
      change SplitTube.bandModel (E.boundedSplitCharts h hlin).e₀
        (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).d
        (E.boundedSplitCharts h hlin).host (p, 0) = (q.1.val.down, q.2) at he
      rw [E.fibrePlug_middle_band_closed h hlin p hp, he]
      change E.toTorus.cutMap ((E.splitData h).ΘH
        (clampPants q.1.val.down, q.2)).val = E.toTorus.cutMap ((E.splitData h).ΘH q).val
      have hcl : clampPants.{u} q.1.val.down = q.1 := by
        apply Subtype.ext
        exact clampPants_val hbase
      rw [hcl]
    · obtain ⟨q, hq, rfl⟩ := hx
      have hbase : ‖q.1.val.down‖ ≤ 3 := (mem_discSet_iff _).mp q.1.property
      obtain ⟨p, hp, he⟩ := SplitTube.fibrePlug_cap_zero_covers
        (E.boundedSplitCharts h hlin).he₀ q.1.val.down hbase q.2 hq
      refine ⟨p, ?_⟩
      change E.boundedSplitTubeMap h hlin (p, 0) =
        E.toTorus.cutMap ((E.splitData h).ΘV q).val
      rw [E.fibrePlug_middle_cap_closed h hlin p hp, he]
      change E.toTorus.cutMap ((E.splitData h).ΘV
        (clampDisc q.1.val.down, q.2)).val = E.toTorus.cutMap ((E.splitData h).ΘV q).val
      have hcl : clampDisc.{u} q.1.val.down = q.1 := by
        apply Subtype.ext
        exact clampDisc_val hbase
      rw [hcl]

end GC.Seifert.ElementaryPresentation

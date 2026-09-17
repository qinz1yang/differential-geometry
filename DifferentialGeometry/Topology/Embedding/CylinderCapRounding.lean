import DifferentialGeometry.Topology.Embedding.CylinderCap
import DifferentialGeometry.Topology.Diffeomorph.Graph
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import DifferentialGeometry.Topology.Diffeomorph.LocalizedGraph
import Mathlib.Topology.Order.IntermediateValue

open Set Metric
open scoped ContDiff Manifold Topology

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def cylinderCapCoordinates (a : ℝ) : (E × ℝ) ≃ₘ[ℝ] (E × ℝ) := by
  let g : E → ℝ := fun x => a * (‖x‖ ^ 2 - 1)
  have hg : ContDiff ℝ ∞ g := contDiff_const.mul ((contDiff_norm_sq ℝ).sub contDiff_const)
  let k : ℝ → ℝ := fun t => (Real.sqrt (Real.smoothMax (1 / 4) (1 / 2) (1 + t / a)))⁻¹
  have hpos (t : ℝ) : 0 < Real.smoothMax (1 / 4) (1 / 2) (1 + t / a) :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      ((le_max_left _ _).trans (Real.smoothMax.max_le (by norm_num) _ _))
  have hk : ContDiff ℝ ∞ k :=
    (((Real.smoothMax.contDiff (1 / 4)).comp
      (contDiff_const.prodMk (contDiff_const.add (contDiff_id.div_const a)))).sqrt
        (fun t => (hpos t).ne')).inv (fun t => (Real.sqrt_pos.mpr (hpos t)).ne')
  exact (graphShear (f := fun _ : E => (0 : ℝ)) contDiff_const hg).trans
    (fiberwiseSmul hk (fun t => inv_ne_zero (Real.sqrt_pos.mpr (hpos t)).ne'))

theorem cylinderCapCoordinates_apply (a : ℝ) (p : E × ℝ) :
    cylinderCapCoordinates a p =
      ((Real.sqrt (Real.smoothMax (1 / 4) (1 / 2)
        (1 + (p.2 + a * (‖p.1‖ ^ 2 - 1)) / a)))⁻¹ • p.1,
        p.2 + a * (‖p.1‖ ^ 2 - 1)) := by
  simp [cylinderCapCoordinates, graphShear_apply, fiberwiseSmul_apply, Diffeomorph.coe_trans]

theorem cylinderCapCoordinates_apply_zero {a : ℝ} (ha : a ≠ 0) (x : E) :
    cylinderCapCoordinates a (x, 0) = EuclideanGeometry.cylinderCap a x := by
  rw [cylinderCapCoordinates_apply]
  have h : 1 + (0 + a * (‖x‖ ^ 2 - 1)) / a = ‖x‖ ^ 2 := by field_simp; ring
  change ((Real.sqrt (Real.smoothMax (1 / 4) (1 / 2)
    (1 + (0 + a * (‖x‖ ^ 2 - 1)) / a)))⁻¹ • x, 0 + a * (‖x‖ ^ 2 - 1)) = _
  rw [h, zero_add]
  rfl

theorem cylinderCapCoordinates_symm_apply (a : ℝ) (p : E × ℝ) :
    (cylinderCapCoordinates a).symm p =
      (Real.sqrt (Real.smoothMax (1 / 4) (1 / 2) (1 + p.2 / a)) • p.1,
        p.2 - a * (‖Real.sqrt (Real.smoothMax (1 / 4) (1 / 2) (1 + p.2 / a)) • p.1‖ ^ 2 - 1)) := by
  simp [cylinderCapCoordinates, Diffeomorph.symm_trans', Diffeomorph.coe_trans]

theorem cylinderCapCoordinates_symm_apply_of_snd_nonneg {a : ℝ} (ha : 0 < a)
    {p : E × ℝ} (hp : 0 ≤ p.2) :
    (cylinderCapCoordinates a).symm p =
      (Real.sqrt (1 + p.2 / a) • p.1, (a + p.2) * (1 - ‖p.1‖ ^ 2)) := by
  have ht : 0 ≤ p.2 / a := div_nonneg hp ha.le
  have hmax : Real.smoothMax (1 / 4) (1 / 2) (1 + p.2 / a) = 1 + p.2 / a := by
    rw [Real.smoothMax.eq_max_of_le (by norm_num), max_eq_right (by linarith)]
    rw [abs_of_nonpos (by linarith)]
    linarith
  rw [cylinderCapCoordinates_symm_apply, hmax]
  refine Prod.ext rfl ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by linarith)]
  dsimp
  field_simp
  ring

end Diffeomorph

namespace EuclideanGeometry

private noncomputable def roundedCapRadiusSq (a ε w : ℝ) : ℝ :=
  (1 + ((Real.smoothAbs ε w - w) / 2) / a) * (1 - (w + Real.smoothAbs ε w) / 2)

private theorem contDiff_roundedCapRadiusSq (a ε : ℝ) :
    ContDiff ℝ ∞ (roundedCapRadiusSq a ε) :=
  (contDiff_const.add (((Real.smoothAbs.contDiff ε).sub contDiff_id).div_const 2 |>.div_const a)).mul
    (contDiff_const.sub ((contDiff_id.add (Real.smoothAbs.contDiff ε)).div_const 2))

private theorem roundedCapRadiusSq_eq_of_le {a ε w : ℝ} (hε : 0 < ε) (hw : ε ≤ w) :
    roundedCapRadiusSq a ε w = 1 - w := by
  rw [roundedCapRadiusSq, Real.smoothAbs.eq_self_of_le hε hw]
  ring

private theorem roundedCapRadiusSq_eq_of_neg_le {a ε w : ℝ} (hε : 0 < ε) (hw : w ≤ -ε) :
    roundedCapRadiusSq a ε w = 1 - w / a := by
  rw [roundedCapRadiusSq, Real.smoothAbs.eq_neg_of_le hε hw]
  ring

private theorem hasDerivAt_roundedCapRadiusSq (a ε w : ℝ) :
    HasDerivAt (roundedCapRadiusSq a ε)
      ((((deriv (Real.smoothAbs ε) w - 1) / 2) / a) * (1 - (w + Real.smoothAbs ε w) / 2) -
        (1 + ((Real.smoothAbs ε w - w) / 2) / a) * ((1 + deriv (Real.smoothAbs ε) w) / 2)) w := by
  have hd := ((Real.smoothAbs.contDiff ε).differentiable (by simp) w).hasDerivAt
  have hA := (hasDerivAt_const w (1 : ℝ)).add
    (((hd.sub (hasDerivAt_id w)).div_const 2).div_const a)
  have hB := (hasDerivAt_const w (1 : ℝ)).sub (((hasDerivAt_id w).add hd).div_const 2)
  convert! hA.mul hB using 1
  dsimp [roundedCapRadiusSq]
  ring

private theorem deriv_roundedCapRadiusSq_neg {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hε1 : ε < 1) (w : ℝ) : deriv (roundedCapRadiusSq a ε) w < 0 := by
  rw [(hasDerivAt_roundedCapRadiusSq a ε w).deriv]
  by_cases hw : ε ≤ w
  · have hd : deriv (Real.smoothAbs ε) w = 1 := by
      rw [Real.smoothAbs.deriv, Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hw) (by positivity))]
      norm_num
    rw [hd, Real.smoothAbs.eq_self_of_le hε hw]
    norm_num
  · have hU : (w + Real.smoothAbs ε w) / 2 ≤ ε := by
      have h := Real.smoothMax.monotone_left ε 0 (le_of_not_ge hw)
      simp only [Real.smoothMax] at h
      simp only [add_zero, sub_zero, Real.smoothAbs.eq_self_of_le hε le_rfl] at h
      linarith
    have hV : 0 ≤ (Real.smoothAbs ε w - w) / 2 := by
      have h := (Real.smoothAbs.sub_abs_mem_Icc hε w).1
      linarith [le_abs_self w]
    have hA : 0 < 1 + ((Real.smoothAbs ε w - w) / 2) / a := by
      have := div_nonneg hV ha.le
      linarith
    have hC : 0 < (1 - (w + Real.smoothAbs ε w) / 2) / a := div_pos (by linarith) ha
    obtain ⟨hdlow, hdup⟩ := abs_le.mp (Real.smoothAbs.abs_deriv_le_one ε w)
    have hpos : 0 < (1 + ((Real.smoothAbs ε w - w) / 2) / a) *
        (1 + deriv (Real.smoothAbs ε) w) + ((1 - (w + Real.smoothAbs ε w) / 2) / a) *
          (1 - deriv (Real.smoothAbs ε) w) := by
      rcases lt_or_eq_of_le hdup with hd | hd
      · have := mul_pos hC (sub_pos.mpr hd)
        have := mul_nonneg hA.le (by linarith : 0 ≤ 1 + deriv (Real.smoothAbs ε) w)
        linarith
      · rw [hd]
        nlinarith
    convert! (div_neg_of_neg_of_pos (neg_neg_of_pos hpos) (by norm_num : (0 : ℝ) < 2)) using 1
    ring

private theorem bijective_roundedCapRadiusSq {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hε1 : ε < 1) : Function.Bijective (roundedCapRadiusSq a ε) := by
  refine ⟨(strictAnti_of_deriv_neg (deriv_roundedCapRadiusSq_neg ha hε hε1)).injective, ?_⟩
  intro y
  let l := min (-ε) (a * (1 - y))
  let u := max ε (1 - y)
  have hlu : l ≤ u := (min_le_left _ _).trans
    ((by linarith : -ε ≤ ε).trans (le_max_left _ _))
  have hyl : y ≤ roundedCapRadiusSq a ε l := by
    rw [roundedCapRadiusSq_eq_of_neg_le hε (min_le_left _ _)]
    have h := min_le_right (-ε) (a * (1 - y))
    have hh : l / a ≤ 1 - y := (div_le_iff₀ ha).mpr (by dsimp [l]; nlinarith [h])
    linarith
  have hyu : roundedCapRadiusSq a ε u ≤ y := by
    rw [roundedCapRadiusSq_eq_of_le hε (le_max_left _ _)]
    have h := le_max_right ε (1 - y)
    linarith
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc' hlu
    (contDiff_roundedCapRadiusSq a ε).continuous.continuousOn ⟨hyu, hyl⟩
  exact ⟨x, hx⟩

private noncomputable def roundedCapRadiusDiffeomorph {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hε1 : ε < 1) : ℝ ≃ₘ[ℝ] ℝ := by
  have hlocal : IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) ∞ (roundedCapRadiusSq a ε) := by
    intro w
    let d := deriv (roundedCapRadiusSq a ε) w
    have hd : d ≠ 0 := (deriv_roundedCapRadiusSq_neg ha hε hε1 w).ne
    let L : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ d hd).toContinuousLinearEquiv
    have hL : (L : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.toSpanSingleton ℝ d := by
      apply ContinuousLinearMap.ext
      intro x
      change d * x = x * d
      ring
    apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
      (roundedCapRadiusSq a ε) (contDiff_roundedCapRadiusSq a ε).contMDiff.contMDiffOn
      isOpen_univ w (mem_univ _) L
    rw [hL]
    exact (((contDiff_roundedCapRadiusSq a ε).differentiable (by simp) w).hasDerivAt.hasFDerivAt).hasMFDerivAt
  exact hlocal.diffeomorphOfBijective (bijective_roundedCapRadiusSq ha hε hε1)

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def roundedCylinderCapGraph {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hε1 : ε < 1) (x : E) : ℝ :=
  let w := (roundedCapRadiusDiffeomorph ha hε hε1).symm (‖x‖ ^ 2)
  (a + (Real.smoothAbs ε w - w) / 2) * ((w + Real.smoothAbs ε w) / 2)

theorem contDiff_roundedCylinderCapGraph [InnerProductSpace ℝ E] {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hε1 : ε < 1) : ContDiff ℝ ∞ (roundedCylinderCapGraph (E := E) ha hε hε1) := by
  have hw := (roundedCapRadiusDiffeomorph ha hε hε1).symm.contMDiff.contDiff.comp
    (contDiff_norm_sq ℝ : ContDiff ℝ ∞ (fun x : E => ‖x‖ ^ 2))
  exact (contDiff_const.add (((Real.smoothAbs.contDiff ε).comp hw).sub hw |>.div_const 2)).mul
    ((hw.add ((Real.smoothAbs.contDiff ε).comp hw)).div_const 2)

private theorem smoothAbs_sector_nonneg {ε : ℝ} (hε : 0 < ε) (w : ℝ) :
    0 ≤ (w + Real.smoothAbs ε w) / 2 ∧ 0 ≤ (Real.smoothAbs ε w - w) / 2 := by
  have h := (Real.smoothAbs.sub_abs_mem_Icc hε w).1
  constructor <;> linarith [le_abs_self w, neg_le_abs w]

private theorem roundedCapRadiusDiffeomorph_apply {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hε1 : ε < 1) (w : ℝ) :
    roundedCapRadiusDiffeomorph ha hε hε1 w = roundedCapRadiusSq a ε w := rfl

theorem roundedCylinderCapGraph_eq_zero_of_le {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hε1 : ε < 1) {x : E} (hx : 1 + ε / a ≤ ‖x‖ ^ 2) :
    roundedCylinderCapGraph ha hε hε1 x = 0 := by
  let B := roundedCapRadiusDiffeomorph ha hε hε1
  let w := B.symm (‖x‖ ^ 2)
  have hw : roundedCapRadiusSq a ε w = ‖x‖ ^ 2 := B.apply_symm_apply _
  have hb : roundedCapRadiusSq a ε (-ε) ≤ roundedCapRadiusSq a ε w := by
    rw [hw, roundedCapRadiusSq_eq_of_neg_le hε le_rfl]
    simpa only [neg_div, sub_neg_eq_add] using hx
  have hwle : w ≤ -ε :=
    (strictAnti_of_deriv_neg (deriv_roundedCapRadiusSq_neg ha hε hε1)).le_iff_ge.mp hb
  change (a + (Real.smoothAbs ε w - w) / 2) * ((w + Real.smoothAbs ε w) / 2) = 0
  rw [Real.smoothAbs.eq_neg_of_le hε hwle]
  ring

private theorem cylinderCapCoordinates_apply_rounded_graph [InnerProductSpace ℝ E] {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1) (x : E) :
    let w := (roundedCapRadiusDiffeomorph ha hε hε1).symm (‖x‖ ^ 2)
    Diffeomorph.cylinderCapCoordinates a (x, roundedCylinderCapGraph ha hε hε1 x) =
      ((Real.sqrt (1 + ((Real.smoothAbs ε w - w) / 2) / a))⁻¹ • x,
        (Real.smoothAbs ε w - w) / 2) := by
  let B := roundedCapRadiusDiffeomorph ha hε hε1
  let w := B.symm (‖x‖ ^ 2)
  have hw : roundedCapRadiusSq a ε w = ‖x‖ ^ 2 := B.apply_symm_apply _
  let u := (w + Real.smoothAbs ε w) / 2
  let v := (Real.smoothAbs ε w - w) / 2
  have huv : (1 + v / a) * (1 - u) = ‖x‖ ^ 2 := hw
  have hv : 0 ≤ v := (smoothAbs_sector_nonneg hε w).2
  have hsecond : roundedCylinderCapGraph ha hε hε1 x + a * (‖x‖ ^ 2 - 1) = v := by
    change (a + v) * u + a * (‖x‖ ^ 2 - 1) = v
    rw [← huv]
    field_simp
    ring
  have hmax : Real.smoothMax (1 / 4) (1 / 2) (1 + v / a) = 1 + v / a := by
    have ht := div_nonneg hv ha.le
    rw [Real.smoothMax.eq_max_of_le (by norm_num), max_eq_right (by linarith)]
    rw [abs_of_nonpos (by linarith)]
    linarith
  change Diffeomorph.cylinderCapCoordinates a (x, roundedCylinderCapGraph ha hε hε1 x) = _
  rw [Diffeomorph.cylinderCapCoordinates_apply]
  change ((Real.sqrt (Real.smoothMax (1 / 4) (1 / 2)
    (1 + (roundedCylinderCapGraph ha hε hε1 x + a * (‖x‖ ^ 2 - 1)) / a)))⁻¹ • x,
      roundedCylinderCapGraph ha hε hε1 x + a * (‖x‖ ^ 2 - 1)) = _
  rw [hsecond, hmax]

theorem cylinderCapCoordinates_image_graph_roundedCylinderCapGraph [InnerProductSpace ℝ E]
    {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1) :
    Diffeomorph.cylinderCapCoordinates a '' graphOn (roundedCylinderCapGraph ha hε hε1) univ =
      {p : E × ℝ | Real.smoothAbs ε (1 - ‖p.1‖ ^ 2 - p.2) = 1 - ‖p.1‖ ^ 2 + p.2} := by
  let B := roundedCapRadiusDiffeomorph ha hε hε1
  ext p
  constructor
  · rintro ⟨_, ⟨x, _, rfl⟩, rfl⟩
    rw [cylinderCapCoordinates_apply_rounded_graph ha hε hε1]
    let w := B.symm (‖x‖ ^ 2)
    let u := (w + Real.smoothAbs ε w) / 2
    let v := (Real.smoothAbs ε w - w) / 2
    have hw : (1 + v / a) * (1 - u) = ‖x‖ ^ 2 := B.apply_symm_apply _
    have hv : 0 ≤ v := (smoothAbs_sector_nonneg hε w).2
    have hA : 0 < 1 + v / a := by have := div_nonneg hv ha.le; linarith
    have hn : ‖(Real.sqrt (1 + v / a))⁻¹ • x‖ ^ 2 = 1 - u := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (Real.sqrt_pos.mpr hA),
        mul_pow, inv_pow, Real.sq_sqrt hA.le, ← hw]
      field_simp
    change Real.smoothAbs ε (1 - ‖(Real.sqrt (1 + v / a))⁻¹ • x‖ ^ 2 - v) =
      1 - ‖(Real.sqrt (1 + v / a))⁻¹ • x‖ ^ 2 + v
    rw [hn]
    have huw : 1 - (1 - u) - v = w := by dsimp [u, v]; ring
    rw [huw]
    dsimp [u, v]
    ring
  · intro hp
    change Real.smoothAbs ε (1 - ‖p.1‖ ^ 2 - p.2) = 1 - ‖p.1‖ ^ 2 + p.2 at hp
    let w := 1 - ‖p.1‖ ^ 2 - p.2
    have hu : (w + Real.smoothAbs ε w) / 2 = 1 - ‖p.1‖ ^ 2 := by
      dsimp [w]
      rw [hp]
      ring
    have hv : (Real.smoothAbs ε w - w) / 2 = p.2 := by
      dsimp [w]
      rw [hp]
      ring
    have ht : 0 ≤ p.2 := hv ▸ (smoothAbs_sector_nonneg hε w).2
    have hA : 0 ≤ 1 + p.2 / a := by have := div_nonneg ht ha.le; linarith
    let q := (Diffeomorph.cylinderCapCoordinates a).symm p
    have hq : q = (Real.sqrt (1 + p.2 / a) • p.1, (a + p.2) * (1 - ‖p.1‖ ^ 2)) :=
      Diffeomorph.cylinderCapCoordinates_symm_apply_of_snd_nonneg ha ht
    have hn : ‖q.1‖ ^ 2 = B w := by
      rw [hq]
      change ‖Real.sqrt (1 + p.2 / a) • p.1‖ ^ 2 = roundedCapRadiusSq a ε w
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
        Real.sq_sqrt hA, roundedCapRadiusSq, hu, hv]
      ring
    have hgraph : roundedCylinderCapGraph ha hε hε1 q.1 = q.2 := by
      change (a + (Real.smoothAbs ε (B.symm (‖q.1‖ ^ 2)) - B.symm (‖q.1‖ ^ 2)) / 2) *
        ((B.symm (‖q.1‖ ^ 2) + Real.smoothAbs ε (B.symm (‖q.1‖ ^ 2))) / 2) = q.2
      rw [hn, B.symm_apply_apply, hu, hv, hq]
    refine ⟨q, ⟨q.1, mem_univ _, ?_⟩, (Diffeomorph.cylinderCapCoordinates a).apply_symm_apply p⟩
    exact Prod.ext rfl hgraph

theorem roundedCylinderCapGraph_nonneg {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hε1 : ε < 1) (x : E) : 0 ≤ roundedCylinderCapGraph ha hε hε1 x := by
  let w := (roundedCapRadiusDiffeomorph ha hε hε1).symm (‖x‖ ^ 2)
  exact mul_nonneg (add_nonneg ha.le (smoothAbs_sector_nonneg hε w).2)
    (smoothAbs_sector_nonneg hε w).1

theorem roundedCylinderCapGraph_trace_mem_slab [InnerProductSpace ℝ E]
    {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : E} (hx : ‖x‖ ^ 2 ≤ 1 + ε / a) :
    Diffeomorph.cylinderCapCoordinates a (x, t * roundedCylinderCapGraph ha hε hε1 x) ∈
      closedBall (0 : E) 1 ×ˢ Icc (-a) ε := by
  let B := roundedCapRadiusDiffeomorph ha hε hε1
  let w := B.symm (‖x‖ ^ 2)
  let u := (w + Real.smoothAbs ε w) / 2
  let v := (Real.smoothAbs ε w - w) / 2
  have hw : (1 + v / a) * (1 - u) = ‖x‖ ^ 2 := B.apply_symm_apply _
  have hv : 0 ≤ v := (smoothAbs_sector_nonneg hε w).2
  have hwlower : -ε ≤ w := by
    apply (strictAnti_of_deriv_neg (deriv_roundedCapRadiusSq_neg ha hε hε1)).le_iff_ge.mp
    change roundedCapRadiusSq a ε w ≤ roundedCapRadiusSq a ε (-ε)
    rw [show roundedCapRadiusSq a ε w = ‖x‖ ^ 2 from hw,
      roundedCapRadiusSq_eq_of_neg_le hε le_rfl]
    simpa only [neg_div, sub_neg_eq_add] using hx
  have hvupper : v ≤ ε := by
    have heq := Real.smoothAbs.eq_self_of_le hε (le_refl ε)
    have hv' : v = Real.smoothMax ε 0 (-w) := by
      rw [Real.smoothMax, zero_add, zero_sub, neg_neg]
      dsimp [v]
      ring
    rw [hv']
    have hm := Real.smoothMax.monotone_right ε 0 (neg_le_of_neg_le hwlower)
    have hend : Real.smoothMax ε 0 ε = ε := by
      rw [Real.smoothMax, zero_add, zero_sub, Real.smoothAbs.neg hε.ne', heq]
      ring
    exact hm.trans_eq hend
  let g := roundedCylinderCapGraph ha hε hε1 x
  have hg : 0 ≤ g := roundedCylinderCapGraph_nonneg ha hε hε1 x
  have hgv : g + a * (‖x‖ ^ 2 - 1) = v := by
    change (a + v) * u + a * (‖x‖ ^ 2 - 1) = v
    rw [← hw]
    field_simp
    ring
  let z := t * g + a * (‖x‖ ^ 2 - 1)
  have hzl : -a ≤ z := by
    have := mul_nonneg ht.1 hg
    have := mul_nonneg ha.le (sq_nonneg ‖x‖)
    dsimp [z]
    nlinarith
  have hzu : z ≤ ε := by
    have := mul_le_mul_of_nonneg_right ht.2 hg
    dsimp [z]
    linarith
  have hzq : ‖x‖ ^ 2 ≤ 1 + z / a := by
    have hz' : ‖x‖ ^ 2 - 1 ≤ z / a := (le_div_iff₀ ha).mpr (by
      have := mul_nonneg ht.1 hg
      dsimp [z]
      nlinarith)
    linarith
  have hM : 0 < Real.smoothMax (1 / 4) (1 / 2) (1 + z / a) :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      ((le_max_left _ _).trans (Real.smoothMax.max_le (by norm_num) _ _))
  have hxM : ‖x‖ ^ 2 ≤ Real.smoothMax (1 / 4) (1 / 2) (1 + z / a) :=
    hzq.trans ((le_max_right _ _).trans (Real.smoothMax.max_le (by norm_num) _ _))
  rw [Diffeomorph.cylinderCapCoordinates_apply]
  refine ⟨?_, hzl, hzu⟩
  rw [mem_closedBall_zero_iff]
  change ‖(Real.sqrt (Real.smoothMax (1 / 4) (1 / 2) (1 + z / a)))⁻¹ • x‖ ≤ 1
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (Real.sqrt_pos.mpr hM),
    inv_mul_le_iff₀ (Real.sqrt_pos.mpr hM), mul_one]
  exact (Real.le_sqrt (norm_nonneg x) hM.le).mpr hxM

end EuclideanGeometry

namespace Diffeomorph

open EuclideanGeometry

theorem exists_diffeomorph_cylinderCap_rounding
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1)
    {U : Set (E × ℝ)} (hU : IsOpen U)
    (hslab : closedBall (0 : E) 1 ×ˢ Icc (-a) ε ⊆ U) :
    ∃ Φ : (E × ℝ) ≃ₘ[ℝ] (E × ℝ),
      Φ '' range (EuclideanGeometry.cylinderCap (E := E) a) =
        {p : E × ℝ | Real.smoothAbs ε (1 - ‖p.1‖ ^ 2 - p.2) = 1 - ‖p.1‖ ^ 2 + p.2} ∧
      ∃ C : Set (E × ℝ), IsCompact C ∧ C ⊆ U ∧ EqOn Φ id Cᶜ ∧ EqOn Φ.symm id Cᶜ := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let G := roundedCylinderCapGraph (E := E) ha hε hε1
  let D := cylinderCapCoordinates (E := E) a
  let K := closedBall (0 : E) (Real.sqrt (1 + ε / a))
  have hA : 0 < 1 + ε / a := by have := div_pos hε ha; linarith
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKsq {x : E} : x ∈ K ↔ ‖x‖ ^ 2 ≤ 1 + ε / a := by
    rw [mem_closedBall_zero_iff, Real.le_sqrt (norm_nonneg x) hA.le]
  let g : ℝ × E → ℝ := fun p => p.1 * G p.2
  have hg : ContDiff ℝ ∞ g := contDiff_fst.mul
    ((contDiff_roundedCylinderCapGraph ha hε hε1).comp contDiff_snd)
  have hfixed : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∉ K, g (t, x) = g (0, x) := by
    intro t ht x hx
    have hzero : G x = 0 := roundedCylinderCapGraph_eq_zero_of_le ha hε hε1
      (le_of_lt (not_le.mp (hKsq.not.mp hx)))
    simp only [g, hzero, mul_zero]
  let O := D ⁻¹' U
  have hO : IsOpen O := hU.preimage D.continuous
  have htrace : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, (x, g (t, x)) ∈ O := by
    intro t ht x hx
    exact hslab (roundedCylinderCapGraph_trace_mem_slab ha hε hε1 ht (hKsq.mp hx))
  obtain ⟨H, _, _, _, _, hgraph, _, _, C, hC, hCO, hfix⟩ :=
    exists_isotopy_graphOn_endpoints_in_open hg hK hfixed hO htrace
  let Φ := D.symm.trans ((H 1).trans D)
  have hpoint (x : E) : Φ (EuclideanGeometry.cylinderCap a x) = D (x, G x) := by
    change D (H 1 (D.symm (EuclideanGeometry.cylinderCap a x))) = D (x, G x)
    rw [← cylinderCapCoordinates_apply_zero ha.ne' x, D.symm_apply_apply]
    exact congrArg D (by simpa only [g, zero_mul, one_mul] using hgraph x)
  have himage : Φ '' range (EuclideanGeometry.cylinderCap (E := E) a) =
      D '' graphOn G univ := by
    rw [← Set.range_comp]
    calc
      range (Φ ∘ EuclideanGeometry.cylinderCap a) = range (fun x => D (x, G x)) :=
        congrArg range (funext hpoint)
      _ = D '' graphOn G univ := by rw [graphOn, image_image, image_univ]
  refine ⟨Φ, himage.trans (cylinderCapCoordinates_image_graph_roundedCylinderCapGraph ha hε hε1),
    D '' C, hC.image D.continuous, ?_, ?_, ?_⟩
  · rintro p ⟨q, hq, rfl⟩
    exact hCO hq
  · intro p hp
    have hq : D.symm p ∉ C := by
      intro hq
      exact hp ⟨D.symm p, hq, D.apply_symm_apply p⟩
    change D (H 1 (D.symm p)) = p
    rw [(hfix 1).1 hq, id_eq, D.apply_symm_apply]
  · intro p hp
    have hq : D.symm p ∉ C := by
      intro hq
      exact hp ⟨D.symm p, hq, D.apply_symm_apply p⟩
    change D ((H 1).symm (D.symm p)) = p
    rw [(hfix 1).2 hq, id_eq, D.apply_symm_apply]

end Diffeomorph

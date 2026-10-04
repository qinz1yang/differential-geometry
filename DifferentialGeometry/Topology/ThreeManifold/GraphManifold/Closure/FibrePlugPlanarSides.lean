import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugSeparation
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelRegion
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelFill
import Mathlib.Analysis.Convex.PathConnected

/-!
Connected strict sides of the original planar strip in the bounded fibre plug.
The radial exterior construction retains the original boundary circles.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Topology

namespace GC.Seifert.SplitTube

def fibrePlugPlanarSide (l : Fin 3) (t : Bool) : Set ℂ :=
  {z | z ∈ planarModel 3 ∧ 0 < sgnR t * stripLevel l (hostInv l z)}

theorem fibrePlug_convex_exterior_connected (A : Set ℂ) (hA : Convex ℝ A)
    (c : ℂ) (r : ℝ) (hr : 0 < r) (hs : Metric.sphere c r ⊆ A) :
    IsConnected {x : ℂ | x ∈ A ∧ r ≤ ‖x - c‖} := by
  let f : Circle → ℂ := fun t => c + r • (t : ℂ)
  have hf : Continuous f := continuous_const.add
    (contMDiff_circle_coe.continuous.const_smul r)
  have hfs : range f ⊆ {x : ℂ | x ∈ A ∧ r ≤ ‖x - c‖} := by
    rintro x ⟨t, rfl⟩
    have he : ‖f t - c‖ = r := by
      simp [f, Circle.norm_coe, abs_of_pos hr]
    exact ⟨hs (mem_sphere_iff_norm.mpr he), he.ge⟩
  refine ⟨⟨f 1, hfs ⟨1, rfl⟩⟩, isPreconnected_of_forall (f 1) ?_⟩
  intro x hx
  let t := unitOf (x - c)
  let y := f t
  have hy : y ∈ range f := ⟨t, rfl⟩
  have hyA := (hfs hy).1
  have hrad : x = c + ‖x - c‖ • (t : ℂ) := by
    calc
      x = c + (x - c) := by abel
      _ = c + ‖x - c‖ • (t : ℂ) :=
        congrArg (fun v : ℂ => c + v) (norm_smul_unitOf (x - c)).symm
  have hseg : segment ℝ x y ⊆ {z : ℂ | z ∈ A ∧ r ≤ ‖z - c‖} := by
    intro z hz
    refine ⟨hA.segment_subset hx.1 hyA hz, ?_⟩
    rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
    have he : a • x + b • y - c =
        (a * ‖x - c‖ + b * r) • (t : ℂ) := by
      calc
        a • x + b • y - c =
            (a + b) • c + (a * ‖x - c‖ + b * r) • (t : ℂ) - c := by
          nth_rw 1 [hrad]
          change a • (c + ‖x - c‖ • (t : ℂ)) +
            b • (c + r • (t : ℂ)) - c = _
          module
        _ = (a * ‖x - c‖ + b * r) • (t : ℂ) := by
          rw [hab, one_smul]
          abel
    have hm : r ≤ a * ‖x - c‖ + b * r := by nlinarith [hx.2]
    rw [he, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by linarith)]
    exact hm
  refine ⟨range f ∪ segment ℝ x y, union_subset hfs hseg,
    Or.inl ⟨1, rfl⟩, Or.inr (left_mem_segment ℝ x y), ?_⟩
  exact (isPreconnected_range hf).union y hy (right_mem_segment ℝ x y)
    (convex_segment x y).isPreconnected

theorem fibrePlugPlanarSide_zero_false_eq :
    fibrePlugPlanarSide 0 false =
      {z : ℂ | ‖z‖ ≤ 3 ∧ 0 < z.re ∧
        1 / 2 ≤ ‖z - ((3 / 2 : ℝ) : ℂ)‖} := by
  ext z
  have hd : 0 < tubeSlope * stripWidth z.im :=
    mul_pos (by norm_num [tubeSlope]) (stripWidth_pos z.im)
  have he : 0 < sgnR false * stripLevel 0 (hostInv 0 z) ↔ 0 < z.re := by
    change 0 < -1 * ((0 * stripBump z.im - z.re) /
      (tubeSlope * stripWidth z.im)) ↔ _
    have hf : -1 * ((0 * stripBump z.im - z.re) /
        (tubeSlope * stripWidth z.im)) = z.re / (tubeSlope * stripWidth z.im) := by ring
    rw [hf, div_pos_iff_of_pos_right hd]
  simp only [fibrePlugPlanarSide, mem_ofPred_eq, mem_planarModel_three, he]
  constructor
  · rintro ⟨⟨hz, hp, hn⟩, hr⟩
    exact ⟨hz, hr, hp⟩
  · rintro ⟨hz, hr, hp⟩
    have hb := Complex.re_le_norm (z - ((-(3 / 2) : ℝ) : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at hb
    exact ⟨⟨hz, hp, by linarith⟩, hr⟩

theorem fibrePlugPlanarSide_zero_false_connected :
    IsConnected (fibrePlugPlanarSide 0 false) := by
  let A : Set ℂ := {z | ‖z‖ ≤ 3 ∧ 0 < z.re}
  have hA : Convex ℝ A := by
    have hb := convex_closedBall (0 : ℂ) (3 : ℝ)
    have hh := convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear (0 : ℝ)
    convert hb.inter hh using 1
    ext z
    simp [A]
  have hs : sphere (((3 / 2 : ℝ) : ℂ)) (1 / 2) ⊆ A := by
    intro z hz
    have he := mem_sphere_iff_norm.mp hz
    have hn := norm_add_le (z - ((3 / 2 : ℝ) : ℂ)) (((3 / 2 : ℝ) : ℂ))
    have hc : ‖((3 / 2 : ℝ) : ℂ)‖ = 3 / 2 := by norm_num
    have hb := Complex.re_le_norm (-(z - ((3 / 2 : ℝ) : ℂ)))
    rw [norm_neg, he] at hb
    simp only [Complex.neg_re, Complex.sub_re, Complex.ofReal_re] at hb
    rw [sub_add_cancel, he, hc] at hn
    exact ⟨by linarith, by linarith⟩
  have h := fibrePlug_convex_exterior_connected A hA (((3 / 2 : ℝ) : ℂ))
    (1 / 2) (by norm_num) hs
  rw [fibrePlugPlanarSide_zero_false_eq]
  convert h using 1
  ext z
  change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ _)
  exact and_assoc.symm

theorem fibrePlug_planar_neg_mem (z : ℂ) (hz : z ∈ planarModel 3) :
    -z ∈ planarModel 3 := by
  rw [mem_planarModel_three] at hz ⊢
  have he1 : -z - ((3 / 2 : ℝ) : ℂ) = -(z - ((-(3 / 2) : ℝ) : ℂ)) := by
    push_cast
    ring
  have he2 : -z - ((-(3 / 2) : ℝ) : ℂ) = -(z - ((3 / 2 : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [norm_neg, he1, he2, norm_neg, norm_neg]
  exact ⟨hz.1, hz.2.2, hz.2.1⟩

theorem fibrePlugPlanarSide_zero_true_eq :
    fibrePlugPlanarSide 0 true = Neg.neg '' fibrePlugPlanarSide 0 false := by
  have sign : ∀ z : ℂ, 0 < sgnR true * stripLevel 0 (hostInv 0 z) ↔ z.re < 0 := by
    intro z
    have hd : 0 < tubeSlope * stripWidth z.im :=
      mul_pos (by norm_num [tubeSlope]) (stripWidth_pos z.im)
    change 0 < 1 * ((0 * stripBump z.im - z.re) /
      (tubeSlope * stripWidth z.im)) ↔ _
    rw [one_mul, zero_mul, zero_sub, div_pos_iff_of_pos_right hd]
    exact neg_pos
  have sign' : ∀ z : ℂ, 0 < sgnR false * stripLevel 0 (hostInv 0 z) ↔ 0 < z.re := by
    intro z
    have hd : 0 < tubeSlope * stripWidth z.im :=
      mul_pos (by norm_num [tubeSlope]) (stripWidth_pos z.im)
    change 0 < -1 * ((0 * stripBump z.im - z.re) /
      (tubeSlope * stripWidth z.im)) ↔ _
    have he : -1 * ((0 * stripBump z.im - z.re) /
        (tubeSlope * stripWidth z.im)) = z.re / (tubeSlope * stripWidth z.im) := by ring
    rw [he, div_pos_iff_of_pos_right hd]
  ext z
  constructor
  · intro hz
    refine ⟨-z, ⟨fibrePlug_planar_neg_mem z hz.1, ?_⟩, neg_neg z⟩
    rw [sign', Complex.neg_re, neg_pos]
    exact (sign z).mp hz.2
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fibrePlug_planar_neg_mem x hx.1, ?_⟩
    rw [sign, Complex.neg_re, neg_lt_zero]
    exact (sign' x).mp hx.2

theorem fibrePlugPlanarSide_zero_connected (t : Bool) :
    IsConnected (fibrePlugPlanarSide 0 t) := by
  cases t
  · exact fibrePlugPlanarSide_zero_false_connected
  · rw [fibrePlugPlanarSide_zero_true_eq]
    exact fibrePlugPlanarSide_zero_false_connected.image Neg.neg continuous_neg.continuousOn

theorem fibrePlug_inner_chart_domain {w : ℂ} (hw : w ≠ 0) :
    hostChart 1 w ∈ planarModel 3 ↔
      ‖w‖ ≤ 2 ∧ 4 / 9 ≤ ‖w - ((2 / 9 : ℝ) : ℂ)‖ ∧
        2 / 35 ≤ ‖w - ((-(12 / 35) : ℝ) : ℂ)‖ := by
  have hn := Complex.normSq_pos.mpr hw
  have hn0 := norm_pos_iff.mpr hw
  have he0 := normSq_add_inv_mul (3 / 2) hw
  have he2 := normSq_add_inv_mul 3 hw
  have hf0 := normSq_sub_ofReal w (2 / 9)
  have hf2 := normSq_sub_ofReal w (-(12 / 35))
  rw [← Complex.sq_norm] at hf0 hf2
  rw [← Complex.sq_norm ((3 / 2 : ℝ) + w⁻¹)] at he0
  rw [← Complex.sq_norm ((3 : ℝ) + w⁻¹)] at he2
  norm_num at he2
  have h0 : ‖((3 / 2 : ℝ) : ℂ) + w⁻¹‖ ≤ 3 ↔
      4 / 9 ≤ ‖w - ((2 / 9 : ℝ) : ℂ)‖ := by
    constructor
    · intro h
      have hsq : ‖((3 / 2 : ℝ) : ℂ) + w⁻¹‖ ^ 2 ≤ 9 := by
        nlinarith [norm_nonneg (((3 / 2 : ℝ) : ℂ) + w⁻¹)]
      have hm := mul_le_mul_of_nonneg_right hsq hn.le
      nlinarith [norm_nonneg (w - ((2 / 9 : ℝ) : ℂ))]
    · intro h
      apply norm_add_inv_le_of (3 / 2) 3 hw (by norm_num)
      have hsq : (4 / 9 : ℝ) ^ 2 ≤ ‖w - ((2 / 9 : ℝ) : ℂ)‖ ^ 2 := by
        nlinarith [norm_nonneg (w - ((2 / 9 : ℝ) : ℂ))]
      nlinarith
  have h2 : 1 / 2 ≤ ‖(3 : ℂ) + w⁻¹‖ ↔
      2 / 35 ≤ ‖w - ((-(12 / 35) : ℝ) : ℂ)‖ := by
    constructor
    · intro h
      have hsq : (1 / 2 : ℝ) ^ 2 ≤ ‖(3 : ℂ) + w⁻¹‖ ^ 2 := by
        nlinarith [norm_nonneg ((3 : ℂ) + w⁻¹)]
      have hm := mul_le_mul_of_nonneg_right hsq hn.le
      nlinarith [norm_nonneg (w - ((-(12 / 35) : ℝ) : ℂ))]
    · intro h
      apply le_norm_add_inv_of 3 (1 / 2) hw (by norm_num)
      have hsq : (2 / 35 : ℝ) ^ 2 ≤ ‖w - ((-(12 / 35) : ℝ) : ℂ)‖ ^ 2 := by
        nlinarith [norm_nonneg (w - ((-(12 / 35) : ℝ) : ℂ))]
      nlinarith
  rw [mem_planarModel_three]
  have hchart : hostChart 1 w = ((3 / 2 : ℝ) : ℂ) + w⁻¹ := by
    simp [hostChart, planarCenter]
  rw [hchart, add_sub_cancel_left, norm_inv, h0]
  have hs : ((3 / 2 : ℝ) : ℂ) + w⁻¹ - ((-(3 / 2) : ℝ) : ℂ) =
      (3 : ℂ) + w⁻¹ := by push_cast; ring
  rw [hs, h2]
  have hi : (1 / 2 : ℝ) ≤ ‖w‖⁻¹ ↔ ‖w‖ ≤ 2 := by
    rw [le_inv_comm₀ (by norm_num) hn0]
    norm_num
  rw [hi]
  tauto

def fibrePlugInnerChartSide (t : Bool) : Set ℂ :=
  {w | ‖w‖ ≤ 2 ∧ 4 / 9 ≤ ‖w - ((2 / 9 : ℝ) : ℂ)‖ ∧
    2 / 35 ≤ ‖w - ((-(12 / 35) : ℝ) : ℂ)‖ ∧ 0 < sgnR t * stripLevel 1 w}

def fibrePlugInnerCentral (t : Bool) : Set ℂ :=
  {w | ‖w‖ ≤ 2 ∧ |w.im| ≤ 1 / 2 ∧ 0 < sgnR t * (-(1 / 4) - w.re)}

theorem fibrePlugInnerCentral_convex (t : Bool) : Convex ℝ (fibrePlugInnerCentral t) := by
  have hb := convex_closedBall (0 : ℂ) (2 : ℝ)
  have hi := (convex_halfSpace_ge Complex.imCLM.toLinearMap.isLinear (-(1 / 2) : ℝ)).inter
    (convex_halfSpace_le Complex.imCLM.toLinearMap.isLinear (1 / 2 : ℝ))
  cases t
  · have hr := convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear (-(1 / 4) : ℝ)
    convert hb.inter (hi.inter hr) using 1
    ext w
    simp only [mem_inter_iff, mem_closedBall, dist_zero_right, mem_ofPred_eq]
    change (‖w‖ ≤ 2 ∧ |w.im| ≤ 1 / 2 ∧ 0 < -1 * (-(1 / 4) - w.re)) ↔
      (‖w‖ ≤ 2 ∧ (-(1 / 2) ≤ w.im ∧ w.im ≤ 1 / 2) ∧ -(1 / 4) < w.re)
    rw [abs_le]
    constructor <;> rintro ⟨hN, hI, hR⟩ <;> exact ⟨hN, hI, by linarith⟩
  · have hr := convex_halfSpace_lt Complex.reCLM.toLinearMap.isLinear (-(1 / 4) : ℝ)
    convert hb.inter (hi.inter hr) using 1
    ext w
    simp only [mem_inter_iff, mem_closedBall, dist_zero_right, mem_ofPred_eq]
    change (‖w‖ ≤ 2 ∧ |w.im| ≤ 1 / 2 ∧ 0 < 1 * (-(1 / 4) - w.re)) ↔
      (‖w‖ ≤ 2 ∧ (-(1 / 2) ≤ w.im ∧ w.im ≤ 1 / 2) ∧ w.re < -(1 / 4))
    rw [abs_le]
    constructor <;> rintro ⟨hN, hI, hR⟩ <;> exact ⟨hN, hI, by linarith⟩


theorem fibrePlugInnerCentral_sphere (t : Bool) :
    sphere ((if t then -(12 / 35) else 2 / 9 : ℝ) : ℂ)
      (if t then 2 / 35 else 4 / 9) ⊆ fibrePlugInnerCentral t := by
  intro w hw
  have he := mem_sphere_iff_norm.mp hw
  have hn := norm_add_le
    (w - ((if t then -(12 / 35) else 2 / 9 : ℝ) : ℂ))
    (((if t then -(12 / 35) else 2 / 9 : ℝ) : ℂ))
  rw [sub_add_cancel, he] at hn
  have hr := Complex.abs_re_le_norm
    (w - ((if t then -(12 / 35) else 2 / 9 : ℝ) : ℂ))
  have hi := Complex.abs_im_le_norm
    (w - ((if t then -(12 / 35) else 2 / 9 : ℝ) : ℂ))
  rw [he] at hr hi
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
    sub_zero] at hr hi
  have hr' := abs_le.mp hr
  cases t <;> norm_num [fibrePlugInnerCentral, sgnR] at hn hi hr' ⊢ <;>
    exact ⟨by linarith, hi.trans (by norm_num), by linarith⟩

theorem fibrePlugInnerChartSide_central_eq (t : Bool) :
    fibrePlugInnerChartSide t ∩ {w : ℂ | |w.im| ≤ 1 / 2} =
      {w : ℂ | w ∈ fibrePlugInnerCentral t ∧
        (if t then 2 / 35 else 4 / 9) ≤
          ‖w - ((if t then -(12 / 35) else 2 / 9 : ℝ) : ℂ)‖} := by
  ext w
  have hsign (hi : |w.im| ≤ 1 / 2) :
      0 < sgnR t * stripLevel 1 w ↔ 0 < sgnR t * (-(1 / 4) - w.re) := by
    rw [stripLevel_eq, stripBump_of_le_half hi]
    have hd : 0 < tubeSlope * stripWidth w.im :=
      mul_pos (by norm_num [tubeSlope]) (stripWidth_pos w.im)
    simp only [stripCenter, Fin.val_one, ↓reduceIte, mul_one]
    rw [← mul_div_assoc, div_pos_iff_of_pos_right hd]
  cases t
  · constructor
    · rintro ⟨⟨hN, hR, hL, hS⟩, hI⟩
      exact ⟨⟨hN, hI, (hsign hI).mp hS⟩, hR⟩
    · rintro ⟨⟨hN, hI, hS⟩, hR⟩
      have hr : -(1 / 4 : ℝ) < w.re := by
        change 0 < -1 * (-(1 / 4) - w.re) at hS
        linarith
      have hb := Complex.re_le_norm (w - ((-(12 / 35) : ℝ) : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re] at hb
      exact ⟨⟨hN, hR, by linarith, (hsign hI).mpr hS⟩, hI⟩
  · constructor
    · rintro ⟨⟨hN, hR, hL, hS⟩, hI⟩
      exact ⟨⟨hN, hI, (hsign hI).mp hS⟩, hL⟩
    · rintro ⟨⟨hN, hI, hS⟩, hL⟩
      have hr : w.re < -(1 / 4 : ℝ) := by simpa [sgnR] using hS
      have hb := Complex.re_le_norm (-(w - ((2 / 9 : ℝ) : ℂ)))
      rw [norm_neg] at hb
      simp only [Complex.neg_re, Complex.sub_re, Complex.ofReal_re] at hb
      exact ⟨⟨hN, by linarith, hL, (hsign hI).mpr hS⟩, hI⟩

theorem fibrePlugInnerChartSide_central_connected (t : Bool) :
    IsConnected (fibrePlugInnerChartSide t ∩ {w : ℂ | |w.im| ≤ 1 / 2}) := by
  rw [fibrePlugInnerChartSide_central_eq]
  exact fibrePlug_convex_exterior_connected _ (fibrePlugInnerCentral_convex t) _ _
    (by cases t <;> norm_num) (fibrePlugInnerCentral_sphere t)

def fibrePlugInnerArc (t : Bool) (Y : ℝ) : ℂ :=
  ⟨-sgnR t * Real.sqrt (4 - Y ^ 2), Y⟩

theorem fibrePlugInnerArc_norm (t : Bool) {Y : ℝ} (hY : |Y| ≤ 2) :
    ‖fibrePlugInnerArc t Y‖ = 2 := by
  have hY2 : Y ^ 2 ≤ 4 := by nlinarith [sq_abs Y, abs_nonneg Y]
  have hs := Real.sq_sqrt (show 0 ≤ 4 - Y ^ 2 by linarith)
  have ht := sgnR_mul_self t
  have hn := Complex.sq_norm (fibrePlugInnerArc t Y)
  simp only [Complex.normSq_apply, fibrePlugInnerArc] at hn
  have hsg : (-sgnR t) ^ 2 = 1 := by nlinarith
  have he : -sgnR t * √(4 - Y ^ 2) * (-sgnR t * √(4 - Y ^ 2)) + Y * Y =
      (-sgnR t * √(4 - Y ^ 2)) ^ 2 + Y ^ 2 := by ring
  rw [he, mul_pow, hsg, one_mul, hs] at hn
  change ‖fibrePlugInnerArc t Y‖ ^ 2 = 4 - Y ^ 2 + Y ^ 2 at hn
  nlinarith [norm_nonneg (fibrePlugInnerArc t Y)]

theorem fibrePlugInnerArc_mem (t : Bool) {Y : ℝ} (hY : |Y| < 2) :
    fibrePlugInnerArc t Y ∈ fibrePlugInnerChartSide t := by
  have hn := fibrePlugInnerArc_norm t hY.le
  have hb0 := norm_sub_norm_le (fibrePlugInnerArc t Y) (((2 / 9 : ℝ) : ℂ))
  have hb2 := norm_sub_norm_le (fibrePlugInnerArc t Y) (((-(12 / 35) : ℝ) : ℂ))
  have hc0 : ‖((2 / 9 : ℝ) : ℂ)‖ = 2 / 9 := by norm_num
  have hc2 : ‖((-(12 / 35) : ℝ) : ℂ)‖ = 12 / 35 := by norm_num
  rw [hn, hc0] at hb0
  rw [hn, hc2] at hb2
  refine ⟨hn.le, by linarith, by linarith, ?_⟩
  have hd : 0 < tubeSlope * stripWidth Y :=
    mul_pos (by norm_num [tubeSlope]) (stripWidth_pos Y)
  rw [stripLevel_eq]
  change 0 < sgnR t * ((-(1 / 4) * stripBump Y -
    (-sgnR t * √(4 - Y ^ 2))) / (tubeSlope * stripWidth Y))
  rw [← mul_div_assoc, div_pos_iff_of_pos_right hd]
  have he : sgnR t * (-(1 / 4) * stripBump Y - (-sgnR t * √(4 - Y ^ 2))) =
      sgnR t * (-(1 / 4) * stripBump Y) + √(4 - Y ^ 2) := by
    linear_combination (√(4 - Y ^ 2)) * sgnR_mul_self t
  rw [he]
  by_cases h1 : 1 ≤ |Y|
  · rw [stripBump_of_one_le h1, mul_zero, mul_zero, zero_add]
    apply Real.sqrt_pos.mpr
    nlinarith [sq_abs Y, abs_nonneg Y]
  · have h1' : |Y| < 1 := lt_of_not_ge h1
    have hs : 1 < √(4 - Y ^ 2) := by
      apply (Real.lt_sqrt (by norm_num)).mpr
      nlinarith [sq_abs Y, abs_nonneg Y]
    rcases sgnR_eq t with ht | ht <;> rw [ht] <;>
      nlinarith [stripBump_le_one Y, stripBump_nonneg Y]

theorem fibrePlugInnerChartSide_height {t : Bool} {w : ℂ}
    (hw : w ∈ fibrePlugInnerChartSide t) : |w.im| < 2 := by
  have hle := (Complex.abs_im_le_norm w).trans hw.1
  by_contra h
  have he : |w.im| = 2 := le_antisymm hle (le_of_not_gt h)
  have hn := Complex.sq_norm w
  rw [Complex.normSq_apply] at hn
  have him : w.im ^ 2 = 4 := by nlinarith [sq_abs w.im]
  have hre : w.re = 0 := by nlinarith [norm_nonneg w, hw.1]
  have hs := hw.2.2.2
  rw [stripLevel_eq, stripBump_of_one_le (by rw [he]; norm_num), hre] at hs
  simp at hs

theorem fibrePlugInnerChartSide_far_segment {t : Bool} {w : ℂ}
    (hw : w ∈ fibrePlugInnerChartSide t) (hI : 1 / 2 < |w.im|) :
    segment ℝ w (fibrePlugInnerArc t w.im) ⊆ fibrePlugInnerChartSide t := by
  have hy := fibrePlugInnerArc_mem t (fibrePlugInnerChartSide_height hw)
  intro z hz
  have hN : ‖z‖ ≤ 2 := by
    have hconv := convex_closedBall (0 : ℂ) (2 : ℝ)
    exact mem_closedBall_zero_iff.mp (hconv.segment_subset
      (mem_closedBall_zero_iff.mpr hw.1) (mem_closedBall_zero_iff.mpr hy.1) hz)
  rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
  have hIm : (a • w + b • fibrePlugInnerArc t w.im).im = w.im := by
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, fibrePlugInnerArc]
    rw [← add_mul, hab, one_mul]
  have hR := Complex.abs_im_le_norm
    (a • w + b • fibrePlugInnerArc t w.im - ((2 / 9 : ℝ) : ℂ))
  have hL := Complex.abs_im_le_norm
    (a • w + b • fibrePlugInnerArc t w.im - ((-(12 / 35) : ℝ) : ℂ))
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, hIm] at hR hL
  refine ⟨hN, by linarith, by linarith, ?_⟩
  rw [stripLevel_affine 1 (by rfl) hab]
  have he : sgnR t * (a * stripLevel 1 w +
      b * stripLevel 1 (fibrePlugInnerArc t w.im)) =
      a * (sgnR t * stripLevel 1 w) +
        b * (sgnR t * stripLevel 1 (fibrePlugInnerArc t w.im)) := by ring
  rw [he]
  have hp := hw.2.2.2
  have hq := hy.2.2.2
  rcases eq_or_lt_of_le ha with hzero | hpos
  · rw [← hzero] at hab ⊢
    rw [zero_add] at hab
    rw [hab]
    linarith
  · nlinarith [mul_pos hpos hp, mul_nonneg hb hq.le]

theorem fibrePlugInnerChartSide_connected (t : Bool) :
    IsConnected (fibrePlugInnerChartSide t) := by
  let Γ := fibrePlugInnerArc t '' Ioo (-2 : ℝ) 2
  have hcont : Continuous (fibrePlugInnerArc t) := by
    have he : fibrePlugInnerArc t = fun Y : ℝ =>
        ((-sgnR t * √(4 - Y ^ 2) : ℝ) : ℂ) + (Y : ℂ) * Complex.I := by
      funext Y
      apply Complex.ext <;> simp [fibrePlugInnerArc]
    rw [he]
    fun_prop
  have hΓc : IsPreconnected Γ := isPreconnected_Ioo.image _ hcont.continuousOn
  have hΓs : Γ ⊆ fibrePlugInnerChartSide t := by
    rintro z ⟨Y, hY, rfl⟩
    exact fibrePlugInnerArc_mem t (abs_lt.mpr hY)
  have ha : fibrePlugInnerArc t 0 ∈ Γ := ⟨0, by norm_num, rfl⟩
  have hAc : IsPreconnected
      ((fibrePlugInnerChartSide t ∩ {w : ℂ | |w.im| ≤ 1 / 2}) ∪ Γ) :=
    (fibrePlugInnerChartSide_central_connected t).isPreconnected.union
      (fibrePlugInnerArc t 0) ⟨hΓs ha, by simp [fibrePlugInnerArc]⟩ ha hΓc
  refine ⟨⟨fibrePlugInnerArc t 0, hΓs ha⟩,
    isPreconnected_of_forall (fibrePlugInnerArc t 0) ?_⟩
  intro w hw
  by_cases hI : |w.im| ≤ 1 / 2
  · exact ⟨(fibrePlugInnerChartSide t ∩ {w : ℂ | |w.im| ≤ 1 / 2}) ∪ Γ,
      union_subset inter_subset_left hΓs, Or.inr ha, Or.inl ⟨hw, hI⟩, hAc⟩
  · have hy : fibrePlugInnerArc t w.im ∈ Γ :=
      ⟨w.im, abs_lt.mp (fibrePlugInnerChartSide_height hw), rfl⟩
    refine ⟨Γ ∪ segment ℝ w (fibrePlugInnerArc t w.im),
      union_subset hΓs (fibrePlugInnerChartSide_far_segment hw (lt_of_not_ge hI)),
      Or.inl ha, Or.inr (left_mem_segment ℝ w (fibrePlugInnerArc t w.im)), ?_⟩
    exact hΓc.union (fibrePlugInnerArc t w.im) hy (right_mem_segment ℝ _ _)
      (convex_segment w (fibrePlugInnerArc t w.im)).isPreconnected

theorem fibrePlugInnerChartSide_ne_zero {t : Bool} {w : ℂ}
    (hw : w ∈ fibrePlugInnerChartSide t) : w ≠ 0 := by
  intro he
  have h := hw.2.1
  rw [he] at h
  norm_num at h

theorem fibrePlugPlanarSide_one_eq (t : Bool) :
    fibrePlugPlanarSide 1 t = hostChart 1 '' fibrePlugInnerChartSide t := by
  ext z
  constructor
  · intro hz
    have hn : hostInv 1 z ≠ 0 := by
      have hp := ((mem_planarModel_three z).mp hz.1).2.1
      change (z - ((3 / 2 : ℝ) : ℂ))⁻¹ ≠ 0
      exact inv_ne_zero (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hp))
    refine ⟨hostInv 1 z, ?_, hostChart_hostInv 1 z⟩
    have hd := (fibrePlug_inner_chart_domain hn).mp
      (by rw [hostChart_hostInv]; exact hz.1)
    exact ⟨hd.1, hd.2.1, hd.2.2, hz.2⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(fibrePlug_inner_chart_domain (fibrePlugInnerChartSide_ne_zero hw)).mpr
      ⟨hw.1, hw.2.1, hw.2.2.1⟩, ?_⟩
    rw [hostInv_hostChart]
    exact hw.2.2.2

theorem fibrePlugPlanarSide_one_connected (t : Bool) :
    IsConnected (fibrePlugPlanarSide 1 t) := by
  have he : hostChart 1 = fun w : ℂ => ((3 / 2 : ℝ) : ℂ) + w⁻¹ := by
    funext w
    simp [hostChart, planarCenter]
  have hc : ContinuousOn (hostChart 1) (fibrePlugInnerChartSide t) := by
    rw [he]
    exact continuousOn_const.add (continuousOn_id.inv₀
      fun w hw => fibrePlugInnerChartSide_ne_zero hw)
  rw [fibrePlugPlanarSide_one_eq]
  exact (fibrePlugInnerChartSide_connected t).image _ hc

theorem fibrePlug_strip_neg (w : ℂ) : stripLevel 2 (-w) = -stripLevel 1 w := by
  have hb : stripBump (-w.im) = stripBump w.im := by simp [stripBump]
  have hW : stripWidth (-w.im) = stripWidth w.im := by simp [stripWidth, hb]
  rw [stripLevel_eq, stripLevel_eq]
  simp only [stripCenter, Complex.neg_re, Complex.neg_im, hb, hW]
  norm_num
  ring

theorem fibrePlug_hostInv_neg (z : ℂ) : hostInv 2 (-z) = -hostInv 1 z := by
  change (-z - ((-(3 / 2) : ℝ) : ℂ))⁻¹ = -(z - ((3 / 2 : ℝ) : ℂ))⁻¹
  rw [show -z - ((-(3 / 2) : ℝ) : ℂ) = -(z - ((3 / 2 : ℝ) : ℂ)) by push_cast; ring]
  exact inv_neg

theorem fibrePlugPlanarSide_two_eq (t : Bool) :
    fibrePlugPlanarSide 2 t = Neg.neg '' fibrePlugPlanarSide 1 (!t) := by
  have hs : sgnR (!t) = -sgnR t := by cases t <;> simp [sgnR]
  have hf (z : ℂ) :
      sgnR t * stripLevel 2 (hostInv 2 (-z)) =
        sgnR (!t) * stripLevel 1 (hostInv 1 z) := by
    rw [fibrePlug_hostInv_neg, fibrePlug_strip_neg, hs]
    ring
  ext z
  constructor
  · intro hz
    refine ⟨-z, ⟨fibrePlug_planar_neg_mem z hz.1, ?_⟩, neg_neg z⟩
    rw [← hf, neg_neg]
    exact hz.2
  · rintro ⟨w, hw, rfl⟩
    exact ⟨fibrePlug_planar_neg_mem w hw.1, by rw [hf]; exact hw.2⟩

theorem fibrePlugPlanarSide_connected (l : Fin 3) (t : Bool) :
    IsConnected (fibrePlugPlanarSide l t) := by
  fin_cases l
  · exact fibrePlugPlanarSide_zero_connected t
  · exact fibrePlugPlanarSide_one_connected t
  · change IsConnected (fibrePlugPlanarSide 2 t)
    rw [fibrePlugPlanarSide_two_eq]
    exact (fibrePlugPlanarSide_one_connected (!t)).image Neg.neg continuous_neg.continuousOn

end GC.Seifert.SplitTube

namespace GC.Seifert.ElementaryPresentation

universe u

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
variable {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)

theorem fibrePlugHostSide_connected (t : Bool) : IsConnected (E.fibrePlugHostSide h t) := by
  let A := SplitTube.fibrePlugPlanarSide (E.fibrePlugFilledHostPort h) t
  let : ConnectedSpace A := isConnected_iff_connectedSpace.mp
    (SplitTube.fibrePlugPlanarSide_connected (E.fibrePlugFilledHostPort h) t)
  let g : A × Circle → pantsPlanarBase.{u}.surface.Carrier × Circle := fun q =>
    (⟨ULift.up q.1.val, (mem_planarSet_iff (Or.inr rfl) (ULift.up q.1.val)).mpr
      q.1.property.1⟩, q.2)
  have hg : Continuous g := by
    exact ((contMDiff_planeLift_up.continuous.comp
      (continuous_subtype_val.comp continuous_fst)).subtype_mk
      fun q => (mem_planarSet_iff (Or.inr rfl) (ULift.up q.1.val)).mpr
        q.1.property.1).prodMk continuous_snd
  let f : A × Circle → W.Carrier := fun q =>
    E.toTorus.cutMap ((E.splitData h).ΘH (g q)).val
  have hf : Continuous f := E.toTorus.quotient_smooth.continuous.comp
    (continuous_subtype_val.comp ((E.splitData h).ΘH.continuous.comp hg))
  have he : range f = E.fibrePlugHostSide h t := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨g q, q.1.property.2, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      let z : A := ⟨q.1.val.down, ⟨(mem_planarSet_iff (Or.inr rfl) q.1.val).mp
        q.1.property, hq⟩⟩
      refine ⟨(z, q.2), ?_⟩
      have hgz : g (z, q.2) = q := by
        apply Prod.ext
        · exact Subtype.ext (ULift.ext rfl)
        · rfl
      change E.toTorus.cutMap ((E.splitData h).ΘH (g (z, q.2))).val = _
      rw [hgz]
  rw [← he]
  exact isConnected_range hf

end GC.Seifert.ElementaryPresentation

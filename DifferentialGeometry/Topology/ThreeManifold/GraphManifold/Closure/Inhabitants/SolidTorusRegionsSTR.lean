import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusRatioSTR
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusEdgeBaseSTR
import DifferentialGeometry.Topology.Manifold.BoundaryExtrema
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Junctions
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialTorusCores

/-!
# S-SOLIDTORUS2 (suffix `_STR`), G3 part 3: the regions `M₁`, `M^edge`, `M₃` of the instance

With `u = Re z₂` and the height `h = 2‖z₁‖² - 1`: the ball is `{u ≥ κ}`, the cusp `{h ≥ -1/4}`;
`M₁ = {u ≤ κ, h ≤ -1/4}`, the edge piece `M^edge = {u ≤ κ, h ≤ -7/8}`, and
`M₃ = {u ≤ κ, -7/8 ≤ h ≤ -1/4}`. The frontier points are handled by the regularity of the zero
functions (`isBoundaryPoint_of_isLocalMin_of_mfderiv_ne_zero`): a function with nonzero
differential at an interior point takes both smaller and larger values in every neighbourhood.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_RegionsSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_RegionsSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

/-- `u = Re z₂` on the carrier. -/
def uW_STR (p : Wc.Carrier) : ℝ := (sphereSecond p.val).re

theorem continuous_uW_STR : Continuous uW_STR :=
  Complex.continuous_re.comp (contMDiff_sphereSecond.continuous.comp continuous_subtype_val)

theorem isInteriorPoint_of_height_STR {p : Wc.Carrier} (h : X135Radial.height p < 0) :
    (𝓡∂ 3).IsInteriorPoint p :=
  (solidTorus_isInteriorPoint_iff p).mpr h

theorem norm_second_sq_STR (p : Wc.Carrier) :
    ‖sphereSecond p.val‖ ^ 2 = (1 - X135Radial.height p) / 2 :=
  norm_sphereSecond_sq_eq p.val

theorem uW_le_norm_STR (p : Wc.Carrier) : uW_STR p ≤ ‖sphereSecond p.val‖ :=
  Complex.re_le_norm _

/-- A function with nonzero differential at an interior point takes smaller values near it. -/
theorem frequently_lt_of_mfderiv_STR {f : Wc.Carrier → ℝ} {p : Wc.Carrier}
    (hp : (𝓡∂ 3).IsInteriorPoint p) (hreg : mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) f p ≠ 0) :
    ∃ᶠ y in nhds p, f y < f p := by
  intro h
  have hmin : IsLocalMin f p := h.mono fun y hy => not_lt.mp hy
  have hb := DifferentialGeometry.Topology.Manifold.isBoundaryPoint_of_isLocalMin_of_mfderiv_ne_zero
    hmin hreg
  exact ((𝓡∂ 3).isBoundaryPoint_iff_not_isInteriorPoint p).mp hb hp

/-- … and larger values. -/
theorem frequently_gt_of_mfderiv_STR {f : Wc.Carrier → ℝ} {p : Wc.Carrier}
    (hp : (𝓡∂ 3).IsInteriorPoint p) (hreg : mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) f p ≠ 0) :
    ∃ᶠ y in nhds p, f p < f y := by
  intro h
  have hmax : IsLocalMax f p := h.mono fun y hy => not_lt.mp hy
  have hb := DifferentialGeometry.Topology.Manifold.isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero
    hmax hreg
  exact ((𝓡∂ 3).isBoundaryPoint_iff_not_isInteriorPoint p).mp hb hp


/-! ## `M₁` -/

theorem unionZC_STR :
    ((⋃ i, range (ballZeroDomainsL_STR.piece i).map) ∪
        ⋃ b, range (X135Radial.radialCuspCores.piece b).map) =
      {p | 4 / 5 ≤ uW_STR p} ∪ {p | -(1 / 4 : ℝ) ≤ X135Radial.height p} := by
  ext p
  constructor
  · rintro (hp | hp)
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hp
      have hr : p ∈ range capPiece_STI.map := hi
      rw [range_capPiece_STI] at hr
      exact Or.inl (ratioBall_le_zero_iff_STI.1 hr)
    · obtain ⟨b, hb⟩ := mem_iUnion.1 hp
      have hb' : p ∈ range X135Radial.cuspToCarrier := hb
      rw [X135Radial.cuspToCarrier_range] at hb'
      exact Or.inr hb'
  · rintro (hp | hp)
    · left
      refine mem_iUnion.2 ⟨(0 : Fin 1), ?_⟩
      change p ∈ range capPiece_STI.map
      rw [range_capPiece_STI]
      exact ratioBall_le_zero_iff_STI.2 hp
    · right
      refine mem_iUnion.2 ⟨(0 : Fin 1), ?_⟩
      change p ∈ range X135Radial.cuspToCarrier
      rw [X135Radial.cuspToCarrier_range]
      exact hp

theorem uW_lt_kap_of_height_STR {p : Wc.Carrier} (h : X135Radial.height p = -(1 / 4 : ℝ)) :
    uW_STR p < 4 / 5 := by
  have h1 := norm_second_sq_STR p
  have h2 := uW_le_norm_STR p
  have h3 := norm_nonneg (sphereSecond p.val)
  rw [h] at h1
  nlinarith

theorem height_lt_of_uW_STR {p : Wc.Carrier} (h : uW_STR p = 4 / 5) :
    X135Radial.height p < -(1 / 4 : ℝ) := by
  have h1 := norm_second_sq_STR p
  have h2 : uW_STR p ≤ ‖sphereSecond p.val‖ := uW_le_norm_STR p
  have h3 : (4 / 5 : ℝ) ≤ ‖sphereSecond p.val‖ := by rw [← h]; exact h2
  nlinarith

theorem regionM1_eq_STR :
    regionM1 ballZeroDomainsL_STR X135Radial.radialCuspCores =
      {p | uW_STR p ≤ 4 / 5 ∧ X135Radial.height p ≤ -(1 / 4 : ℝ)} := by
  unfold regionM1
  rw [unionZC_STR]
  ext p
  simp only [mem_compl_iff]
  constructor
  · intro hp
    by_contra hcon
    apply hp
    have hcon' : ¬ (uW_STR p ≤ 4 / 5 ∧ X135Radial.height p ≤ -(1 / 4 : ℝ)) := hcon
    rw [not_and_or] at hcon'
    rcases hcon' with h1 | h2
    · refine mem_interior.2 ⟨{q | 4 / 5 < uW_STR q}, ?_, isOpen_lt continuous_const
        continuous_uW_STR, not_le.mp h1⟩
      intro q hq
      exact Or.inl (le_of_lt (show 4 / 5 < uW_STR q from hq))
    · refine mem_interior.2 ⟨{q | -(1 / 4 : ℝ) < X135Radial.height q}, ?_,
        isOpen_lt continuous_const X135Radial.height_continuous, not_le.mp h2⟩
      intro q hq
      exact Or.inr (le_of_lt (show -(1 / 4 : ℝ) < X135Radial.height q from hq))
  · rintro ⟨hu, hh⟩ hint
    have hU : ({p | 4 / 5 ≤ uW_STR p} ∪ {p | -(1 / 4 : ℝ) ≤ X135Radial.height p} :
        Set Wc.Carrier) ∈ nhds p :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hint) interior_subset
    have hpU := interior_subset hint
    rcases hpU with hpU | hpU
    · have hu' : uW_STR p = 4 / 5 := le_antisymm hu hpU
      have hlt := height_lt_of_uW_STR hu'
      have hz : ratioL_STR p = 0 := by
        change lamMix_STR (sphereSecond p.val) * (kap_STR - (sphereSecond p.val).re) = 0
        have : (sphereSecond p.val).re = 4 / 5 := hu'
        rw [this]
        norm_num [kap_STR]
      have hint0 : (𝓡∂ 3).IsInteriorPoint p :=
        isInteriorPoint_of_height_STR (by linarith)
      have hf := frequently_gt_of_mfderiv_STR hint0 (ratioL_regular_STR p hz)
      have hev : ∀ᶠ y in nhds p, X135Radial.height y < -(1 / 4 : ℝ) :=
        (isOpen_lt X135Radial.height_continuous continuous_const).mem_nhds hlt
      obtain ⟨y, hy1, hy2, hy3⟩ := (hf.and_eventually (hev.and hU)).exists
      rcases hy3 with hy | hy
      · have hy1' : 0 < ratioL_STR y := by
          have := hy1
          rw [hz] at this
          exact this
        have hpos : 0 < kap_STR - uW_STR y := by
          by_contra hc
          have : ratioL_STR y ≤ 0 := by
            change lamMix_STR (sphereSecond y.val) * (kap_STR - (sphereSecond y.val).re) ≤ 0
            exact mul_nonpos_of_nonneg_of_nonpos (lamMix_pos_STR _).le (not_lt.mp hc)
          linarith
        have h45 : (4 / 5 : ℝ) ≤ uW_STR y := hy
        norm_num [kap_STR] at hpos
        linarith
      · have h14 : (-(1 / 4 : ℝ)) ≤ X135Radial.height y := hy
        linarith
    · have hh' : X135Radial.height p = -(1 / 4 : ℝ) := le_antisymm hh hpU
      have hlt := uW_lt_kap_of_height_STR hh'
      have hz : X135Radial.cuspDefiner p = 0 := by
        change -(1 / 4 : ℝ) - X135Radial.height p = 0
        rw [hh']
        norm_num
      have hint0 : (𝓡∂ 3).IsInteriorPoint p :=
        isInteriorPoint_of_height_STR (by linarith)
      have hf := frequently_gt_of_mfderiv_STR hint0 (X135Radial.cuspDefiner_regular p hz)
      have hev : ∀ᶠ y in nhds p, uW_STR y < 4 / 5 :=
        (isOpen_lt continuous_uW_STR continuous_const).mem_nhds hlt
      obtain ⟨y, hy1, hy2, hy3⟩ := (hf.and_eventually (hev.and hU)).exists
      have hy1' : X135Radial.height y < -(1 / 4 : ℝ) := by
        have : X135Radial.cuspDefiner p < X135Radial.cuspDefiner y := hy1
        change -(1 / 4 : ℝ) - X135Radial.height p < -(1 / 4 : ℝ) - X135Radial.height y at this
        linarith
      rcases hy3 with hy | hy
      · have : (4 / 5 : ℝ) ≤ uW_STR y := hy
        linarith
      · have : (-(1 / 4 : ℝ)) ≤ X135Radial.height y := hy
        linarith


/-! ## The edge piece as an explicit set -/

theorem lam1_pos_of_STR {q : ℂ} (hre : q.re < ‖q‖) (hk : kap_STR < ‖q‖) : 0 < lam1_STR q := by
  have hk0 : 0 < kap_STR := by norm_num [kap_STR]
  unfold lam1_STR
  apply div_pos
  · linarith
  · exact mul_pos (sub_pos.mpr hre) (by linarith)

theorem kap_lt_norm_of_edgeParent_STR {w : Wc.Carrier} (hw : w ∈ edgeParent_STR) :
    kap_STR < ‖sphereSecond w.val‖ :=
  kap_lt_norm_second_STR hw

/-- On the parent, `t ∈ [0, 1]` iff `u ≤ κ` (the identity `4t(1-t) = λ₁(κ - u)`). -/
theorem t_mem_iff_STR {w : Wc.Carrier} (hw : w ∈ edgeParent_STR) :
    tOf_STR (sphereSecond w.val) ∈ Icc (0 : ℝ) 1 ↔ uW_STR w ≤ kap_STR := by
  have hk := kap_lt_norm_of_edgeParent_STR hw
  have hre : (sphereSecond w.val).re < ‖sphereSecond w.val‖ := hw.2
  have hid := four_t_STR hk hre
  have hl := lam1_pos_of_STR hre hk
  set t := tOf_STR (sphereSecond w.val) with ht
  constructor
  · rintro ⟨h0, h1⟩
    have : 0 ≤ 4 * t * (1 - t) := by
      have := mul_nonneg h0 (sub_nonneg.mpr h1)
      linarith
    rw [hid] at this
    by_contra hcon
    have hlt : kap_STR < (sphereSecond w.val).re := not_le.mp hcon
    have : lam1_STR (sphereSecond w.val) * (kap_STR - (sphereSecond w.val).re) < 0 :=
      mul_neg_of_pos_of_neg hl (by linarith)
    linarith
  · intro hu
    have h0 : 0 ≤ lam1_STR (sphereSecond w.val) * (kap_STR - (sphereSecond w.val).re) :=
      mul_nonneg hl.le (by
        have hu' : (sphereSecond w.val).re ≤ kap_STR := hu
        linarith)
    rw [← hid] at h0
    constructor
    · by_contra hcon
      have : t < 0 := not_le.mp hcon
      nlinarith
    · by_contra hcon
      have : 1 < t := not_le.mp hcon
      nlinarith

theorem height_eq_of_first_STR (w : Wc.Carrier) :
    X135Radial.height w = 2 * ‖sphereFirst w.val‖ ^ 2 - 1 := by
  have := norm_sphereFirst_sq_eq w.val
  change cliffordHeight w.val = _
  linarith

theorem edgeSet_eq_STR :
    (cutChoice_STR ballZeroDomainsL_STR).edgeSet =
      {p | uW_STR p ≤ 4 / 5 ∧ X135Radial.height p ≤ -(7 / 8 : ℝ)} := by
  ext p
  constructor
  · rintro ⟨hy, hc, hh⟩
    have hc' : edgeProj_STR ⟨p, hy⟩ ∈ edgeC2_STR := hc
    have hh' : ‖sphereFirst p.val‖ ^ 2 ≤ 1 / 16 := hh
    have h0 : tOf_STR (sphereSecond p.val) ∈ Icc (0 : ℝ) 1 := by
      have := hc'
      rw [edgeProj_eq_single_STR hy] at this
      simpa [edgeC2_STR] using this
    refine ⟨?_, ?_⟩
    · have := (t_mem_iff_STR hy).1 h0
      norm_num [kap_STR] at this
      exact this
    · rw [height_eq_of_first_STR]
      linarith
  · rintro ⟨hu, hh⟩
    have hs : ‖sphereFirst p.val‖ ^ 2 ≤ 1 / 16 := by
      rw [height_eq_of_first_STR] at hh
      linarith
    have hn := norm_sphereFirst_sq_add p.val
    have hk : kap_STR < ‖sphereSecond p.val‖ := by
      have h0 := norm_nonneg (sphereSecond p.val)
      norm_num [kap_STR]
      nlinarith
    have hy : p ∈ edgeParent_STR := by
      refine ⟨by linarith, ?_⟩
      have : (sphereSecond p.val).re ≤ 4 / 5 := hu
      change (sphereSecond p.val).re < ‖sphereSecond p.val‖
      norm_num [kap_STR] at hk
      linarith
    refine ⟨hy, ?_, hs⟩
    have h1 := (t_mem_iff_STR hy).2 (by norm_num [kap_STR]; exact hu)
    change edgeProj_STR ⟨p, hy⟩ ∈ edgeC2_STR
    rw [edgeProj_eq_single_STR hy]
    simpa [edgeC2_STR] using h1


/-! ## The relative interior of the edge piece in `M₁` -/

/-- The region `M₁ = {u ≤ κ, h ≤ -1/4}`. -/
def M1set_STR : Set Wc.Carrier :=
  {p | uW_STR p ≤ 4 / 5 ∧ X135Radial.height p ≤ -(1 / 4 : ℝ)}

/-- The radial dilation `(1 + ε) ζ` of the disk coordinate of a chart point. -/
def radPath_STR (x₀ : EuclideanSpace ℝ (Fin 3)) (ε : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  ofCoords_STI ((1 + ε) * x₀ 0) ((1 + ε) * x₀ 1) (x₀ 2)

theorem rho2_radPath_STR (x₀ : EuclideanSpace ℝ (Fin 3)) (ε : ℝ) :
    rho2_STR (radPath_STR x₀ ε) = (1 + ε) ^ 2 * rho2_STR x₀ := by
  simp only [rho2_STR, radPath_STR, ofCoords_zero_STI, ofCoords_one_STI]
  ring

theorem radPath_two_STR (x₀ : EuclideanSpace ℝ (Fin 3)) (ε : ℝ) :
    radPath_STR x₀ ε 2 = x₀ 2 := by
  simp [radPath_STR]

theorem radPath_zero_STR (x₀ : EuclideanSpace ℝ (Fin 3)) : radPath_STR x₀ 0 = x₀ := by
  ext i
  fin_cases i <;> simp [radPath_STR]

theorem continuous_radPath_STR (x₀ : EuclideanSpace ℝ (Fin 3)) :
    Continuous (radPath_STR x₀) := by
  have hf : Continuous fun ε : ℝ => (((1 + ε) * x₀ 0, (1 + ε) * x₀ 1, x₀ 2) : ℝ × ℝ × ℝ) := by
    fun_prop
  exact contDiff_ofCoords_STI.continuous.comp hf

/-- Near a point of the level `h = -7/8` of `M₁ ∩ M^edge`, there are points of `M₁` above the
level (the radial dilation of the disk coordinate in the edge chart). -/
theorem frequently_above_level_STR {p : Wc.Carrier} (hpu : uW_STR p ≤ 4 / 5)
    (hh : X135Radial.height p = -(7 / 8 : ℝ)) :
    ∃ᶠ y in nhds p, y ∈ M1set_STR ∧ -(7 / 8 : ℝ) < X135Radial.height y := by
  have hs : ‖sphereFirst p.val‖ ^ 2 = 1 / 16 := by
    rw [height_eq_of_first_STR] at hh
    linarith
  have hn := norm_sphereFirst_sq_add p.val
  have hk : kap_STR < ‖sphereSecond p.val‖ := by
    have h0 := norm_nonneg (sphereSecond p.val)
    norm_num [kap_STR]
    nlinarith
  have hy : p ∈ edgeParent_STR := by
    refine ⟨by linarith, ?_⟩
    have : (sphereSecond p.val).re ≤ 4 / 5 := hpu
    norm_num [kap_STR] at hk
    linarith
  set x₀ := edgeInv_STR p.val with hx₀
  have hρ : rho2_STR x₀ = 1 := by
    rw [hx₀, rho2_edgeInv_STR, hs]
    norm_num
  have hsrc : rho2_STR x₀ < 4 := by rw [hρ]; norm_num
  have ht0 : tOf_STR (sphereSecond p.val) ∈ Icc (0 : ℝ) 1 :=
    (t_mem_iff_STR hy).2 hpu
  have hpt : edgeToW_STR x₀ = p := Subtype.ext (edgeMap_edgeInv_STR hy)
  have hcont : ContinuousAt (fun ε => edgeToW_STR (radPath_STR x₀ ε)) 0 := by
    have h1 : ContinuousAt edgeToW_STR (radPath_STR x₀ 0) := by
      rw [radPath_zero_STR]
      exact continuousOn_edgeToW_STR.continuousAt (isOpen_edgeSource_STR.mem_nhds hsrc)
    exact h1.comp (continuous_radPath_STR x₀).continuousAt
  have htend : Filter.Tendsto (fun ε => edgeToW_STR (radPath_STR x₀ ε)) (nhdsWithin 0 (Ioi 0))
      (nhds p) := by
    have h0 : edgeToW_STR (radPath_STR x₀ 0) = p := by rw [radPath_zero_STR]; exact hpt
    have := hcont.tendsto
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine htend.frequently ?_
  apply Filter.Eventually.frequently
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
  have hρε : rho2_STR (radPath_STR x₀ ε) = (1 + ε) ^ 2 := by
    rw [rho2_radPath_STR, hρ]
    ring
  have hlt : rho2_STR (radPath_STR x₀ ε) < 4 := by
    rw [hρε]
    nlinarith [hε.1, hε.2]
  have hpar := edgeToW_mem_parent_STR hlt
  have hseq := sphereFirst_sq_edgeToW_STR hlt
  rw [hρε] at hseq
  have hheight : X135Radial.height (edgeToW_STR (radPath_STR x₀ ε)) = (1 + ε) ^ 2 / 8 - 1 := by
    rw [height_eq_of_first_STR]
    simp only [edgeToW_STR] at hseq ⊢
    rw [hseq]
    ring
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h1 := (t_mem_iff_STR hpar).1 (by
      rw [tOf_edgeToW_STR hlt, radPath_two_STR]
      have : x₀ 2 = tOf_STR (sphereSecond p.val) := by rw [hx₀, edgeInv_two_STR]
      rw [this]
      exact ht0)
    exact h1
  · rw [hheight]
    nlinarith [hε.1, hε.2]
  · rw [hheight]
    nlinarith [hε.1, hε.2]


theorem relInt_edge_STR :
    relInt M1set_STR {p | uW_STR p ≤ 4 / 5 ∧ X135Radial.height p ≤ -(7 / 8 : ℝ)} =
      {p | p ∈ M1set_STR ∧ X135Radial.height p < -(7 / 8 : ℝ)} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    by_contra hlt
    have hP := interior_subset hx
    have heq : X135Radial.height x.val = -(7 / 8 : ℝ) := le_antisymm hP.2 (not_lt.mp hlt)
    have hfreq := frequently_above_level_STR hP.1 heq
    have hnh : interior ((Subtype.val : M1set_STR → Wc.Carrier) ⁻¹'
        {p | uW_STR p ≤ 4 / 5 ∧ X135Radial.height p ≤ -(7 / 8 : ℝ)}) ∈ nhds x :=
      isOpen_interior.mem_nhds hx
    obtain ⟨V, hV, hVsub⟩ := (mem_nhds_subtype M1set_STR x _).1 hnh
    obtain ⟨y, ⟨hyM, hyh⟩, hyV⟩ := (hfreq.and_eventually hV).exists
    have h1 := interior_subset (hVsub (show (⟨y, hyM⟩ : M1set_STR) ∈ _ from hyV))
    have h2 : X135Radial.height y ≤ -(7 / 8 : ℝ) := h1.2
    linarith
  · rintro ⟨hpM, hlt⟩
    refine ⟨⟨p, hpM⟩, ?_, rfl⟩
    refine mem_interior.2 ⟨{x : M1set_STR | X135Radial.height x.val < -(7 / 8 : ℝ)}, ?_, ?_, hlt⟩
    · intro x hx
      exact ⟨x.2.1, le_of_lt hx⟩
    · exact isOpen_lt (X135Radial.height_continuous.comp continuous_subtype_val) continuous_const

theorem relInt_empty_STR {X : Type*} [TopologicalSpace X] (A : Set X) : relInt A ∅ = ∅ := by
  simp [relInt]

theorem slimSet_eq_STR : (cutChoice_STR ballZeroDomainsL_STR).slimSet = ∅ :=
  eq_empty_of_forall_notMem fun x ⟨h, _⟩ =>
    (CircleRegion.false_of_bot Wc ⟨x, h⟩).elim

theorem M2_eq_STR : (cutChoice_STR ballZeroDomainsL_STR).M₂ = M1set_STR := by
  change regionM1 ballZeroDomainsL_STR X135Radial.radialCuspCores \
    relInt (regionM1 ballZeroDomainsL_STR X135Radial.radialCuspCores)
      (cutChoice_STR ballZeroDomainsL_STR).slimSet = M1set_STR
  rw [slimSet_eq_STR, relInt_empty_STR, sdiff_empty]
  exact regionM1_eq_STR

theorem M3_eq_STR : (cutChoice_STR ballZeroDomainsL_STR).M₃ =
    {p | uW_STR p ≤ 4 / 5 ∧ -(7 / 8 : ℝ) ≤ X135Radial.height p ∧
      X135Radial.height p ≤ -(1 / 4 : ℝ)} := by
  change (cutChoice_STR ballZeroDomainsL_STR).M₂ \
    relInt (cutChoice_STR ballZeroDomainsL_STR).M₂
      (cutChoice_STR ballZeroDomainsL_STR).edgeSet = _
  rw [M2_eq_STR, edgeSet_eq_STR, relInt_edge_STR]
  ext p
  constructor
  · rintro ⟨⟨hu, hh⟩, hn⟩
    refine ⟨hu, ?_, hh⟩
    by_contra hc
    exact hn ⟨⟨hu, hh⟩, not_le.mp hc⟩
  · rintro ⟨hu, h1, h2⟩
    exact ⟨⟨hu, h2⟩, fun hn => absurd hn.2 (not_lt.mpr h1)⟩

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

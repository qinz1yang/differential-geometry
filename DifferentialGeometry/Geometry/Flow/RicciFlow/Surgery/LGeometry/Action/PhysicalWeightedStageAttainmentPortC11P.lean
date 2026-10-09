import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedSemicontinuity

/-!
# S-CH11-FIX4 `PortC11P` port

Module `Surgery.LGeometry.Action.PhysicalWeightedStageAttainment`.

Source: donor file of the same relative path in the chapter-11 branch (ch11 HEAD a73e4bdbfd).
Verbatim it does not elaborate against this tree (3 errors).  `PhysicalWeightedSemicontinuity` is
now a shim over its port, so private names are mangled there.  Elaboration-level repairs:
* `open private ObservedHistory.<two names> from ..PhysicalWeightedSemicontinuityPortC11P`
  (port module; declaration names written `ObservedHistory.foo`); the two use sites write
  `ObservedHistory.foo` too.
* `dist : X → ℝ≥0∞` becomes `X → ENNReal` (`ℝ≥0∞` needs `open scoped ENNReal`).
* the same three repairs as in `PhysicalWeightedSemicontinuity` for the copied proof: `hnonneg`
  `simpa only [WithTop.map_coe] using ..` becomes `simp only [..]; exact ..`; `hKdist` names
  `hcomp` and gives `ContinuousAt.comp` `(f := ..) (x := z)`; `hy ▸ hw` becomes
  `hy.symm.trans_le hw`.
No statement, definition or proof idea is altered.  The module
`Surgery.LGeometry.Action.PhysicalWeightedStageAttainment` is a shim re-exporting this file.
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

open private ObservedHistory.lowerSemicontinuous_variable_positive_affine_map
  ObservedHistory.continuous_stage_clock_edist from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedSemicontinuityPortC11P

private theorem physicalWeightedCost_lsc_nonnegative_and_minima_on_stage
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B Bsharp r A a b : ℝ) (hr : 0 < r) (ha : 0 < a) (hab : a ≤ b)
    (hBsharp : 0 ≤ Bsharp) (hroom : (2 * Bsharp / 3) * b ^ 3 < r)
    (hupper : T ∈ H.stageDomain last)
    (hclock : ∀ w ∈ Icc a b,
      T - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T b j.val),
      ∀ y : (H.stage j.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y)
    (hsharp : ∀ j : H.StageInterval first last,
      ∀ s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T b j.val),
      ∀ y : (H.stage j.val).Carrier,
        -Bsharp ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y)
    (x : (H.stage last).Carrier) (O : (H.stage first).Carrier) :
    let M : ℝ → WithTop ℝ := fun w => sInf (Set.range
      (H.physicalWeightedCost first last hle T B r A w x O))
    LowerSemicontinuousOn M (Icc a b) ∧ (∀ w ∈ Icc a b, 0 ≤ M w) ∧
    ∀ w ∈ Icc a b, ∃ q : (H.stage first).Carrier,
      M w = H.physicalWeightedCost first last hle T B r A w x O q ∧
      ∀ y : (H.stage first).Carrier,
        H.physicalWeightedCost first last hle T B r A w x O q ≤
          H.physicalWeightedCost first last hle T B r A w x O y := by
  classical
  intro M
  let X := Icc a b × (H.stage first).Carrier
  let cost : X → WithTop ℝ := fun z => H.regularizedCost first last hle T B 0 z.1.val x z.2
  let dist : X → ENNReal := fun z =>
    riemannianEDistOf (H.stageMetric first (T - z.1.val ^ 2)) O z.2
  let shift : X → ℝ := fun z => A * (1 - 2 * z.1.val ^ 2 / r ^ 2)
  let arg : X → ℝ := fun z => (dist z).toReal / r - shift z
  let phi := DifferentialGeometry.Analysis.SingularBarrier.value
  let W : X → WithTop ℝ := fun z =>
    H.physicalWeightedCost first last hle T B r A z.1.val x O z.2
  let κ : ℝ := r - (2 * Bsharp / 3) * b ^ 3
  have hκ : 0 < κ := sub_pos.mpr hroom
  have hρ : 0 < 2 * a * κ := by positivity
  have hdist : Continuous dist :=
    ObservedHistory.continuous_stage_clock_edist H first T a b hab hclock O
  have htime : Continuous (fun z : X => z.1.val) := continuous_subtype_val.comp continuous_fst
  have hshift : Continuous shift :=
    continuous_const.mul (continuous_const.sub ((continuous_const.mul (htime.pow 2)).div_const _))
  have hcost : LowerSemicontinuous cost := by
    have h := H.lowerSemicontinuousOn_regularizedCost_clock_past_endpoint first last hle
      T B a b ha hab hupper hclock hscalar x
    intro z c hc
    have hm : Tendsto (fun z : X => (z.1.val, z.2)) (𝓝 z)
        (𝓝[Icc a b ×ˢ univ] (z.1.val, z.2)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(htime.prodMk continuous_snd).continuousAt.tendsto, ?_⟩
      exact Eventually.of_forall (fun z => ⟨z.1.property, mem_univ _⟩)
    exact hm.eventually (h (z.1.val, z.2) ⟨z.1.property, mem_univ _⟩ c hc)
  have hcostfloor (z : X) : ((-(2 * Bsharp / 3) * z.1.val ^ 3 : ℝ) : WithTop ℝ) ≤ cost z := by
    have hrestrict (C : ℝ)
        (hC : ∀ j : H.StageInterval first last,
          ∀ s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T b j.val),
          ∀ y : (H.stage j.val).Carrier,
            -C ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y)
        (j : H.StageInterval first last) (s : ℝ)
        (hs : s ∈ Ioo (H.regularizedStageStart T 0 j.val)
          (H.regularizedStageEnd T z.1.val j.val)) (y : (H.stage j.val).Carrier) :
        -C ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y :=
      hC j s ⟨hs.1, hs.2.trans_le
        (H.regularizedStageEnd_monotoneOn T j.val (ha.le.trans z.1.property.1)
          (ha.le.trans hab) z.1.property.2)⟩ y
    dsimp only [cost]
    rw [H.regularizedCost_congr_scalar_lower_bound first last hle T B Bsharp 0 z.1.val
      (hrestrict B hscalar) (hrestrict Bsharp hsharp) x z.2]
    simpa only [zero_pow (by decide : 3 ≠ 0), sub_zero] using
      H.regularizedCost_ge first last hle T Bsharp 0 z.1.val x z.2
  have hshifted (z : X) (L : ℝ) (hL : cost z = (L : WithTop ℝ)) :
      2 * a * κ ≤ 2 * z.1.val * L + 2 * r * z.1.val := by
    have hl := hcostfloor z
    rw [hL] at hl
    have hl' := WithTop.coe_le_coe.mp hl
    have hcub := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (ha.le.trans z.1.property.1) z.1.property.2 3)
      (by positivity : 0 ≤ 2 * Bsharp / 3)
    have hLr : κ ≤ L + r := by dsimp only [κ]; linarith
    have hh := mul_le_mul hLr z.1.property.1 ha.le (by linarith : 0 ≤ L + r)
    nlinarith
  have hargInside (z : X) (hz : dist z < ENNReal.ofReal (r * (shift z + 1 / 10))) :
      arg z < 1 / 10 := by
    have hd := ENNReal.toReal_lt_of_lt_ofReal hz
    dsimp only [arg]
    apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ hr).mpr
    nlinarith
  have hWformula (z : X) (hz : dist z < ENNReal.ofReal (r * (shift z + 1 / 10))) :
      W z = WithTop.map (fun L : ℝ => phi (arg z) *
        (2 * z.1.val * L + 2 * r * z.1.val)) (cost z) := by
    simp only [W, physicalWeightedCost, cost, phi, arg, dist, shift, ite_eq_left hz]
  have hnonneg (z : X) : (0 : WithTop ℝ) ≤ W z := by
    by_cases hz : dist z < ENNReal.ofReal (r * (shift z + 1 / 10))
    · rw [hWformula z hz]
      cases hL : cost z using WithTop.recTopCoe with
      | top => simp only [WithTop.map_top]; exact le_top
      | coe L =>
        have hZ := hshifted z L hL
        have hp := DifferentialGeometry.Analysis.SingularBarrier.pos (hargInside z hz)
        simp only [WithTop.map_coe]
        exact WithTop.coe_le_coe.mpr (mul_nonneg hp.le (hρ.le.trans hZ))
    · simp only [W, physicalWeightedCost, dist, shift, ite_eq_right hz]
      exact le_top
  have hcompact (bound : ℝ) : IsCompact {z : X | W z ≤ (bound : WithTop ℝ)} := by
    obtain ⟨θ, hθ, hphiθ⟩ : ∃ θ : ℝ, θ < 1 / 10 ∧ bound / (2 * a * κ) < phi θ := by
      have he := (DifferentialGeometry.Analysis.SingularBarrier.tendsto_at_pole.eventually
        (eventually_gt_atTop (bound / (2 * a * κ)))).and self_mem_nhdsWithin
      obtain ⟨θ, hp, hθ⟩ := he.exists
      exact ⟨θ, hθ, hp⟩
    let Rθ : X → ℝ := fun z => r * (shift z + θ)
    let K : Set X := {z | 0 ≤ Rθ z ∧ dist z ≤ ENNReal.ofReal (Rθ z)}
    have hRθ : Continuous Rθ := continuous_const.mul (hshift.add continuous_const)
    have hKclosed : IsClosed K :=
      (isClosed_le continuous_const hRθ).inter (isClosed_le hdist (ENNReal.continuous_ofReal.comp hRθ))
    have hKcompact : IsCompact K := hKclosed.isCompact
    have hcapture (z : X) (hz : W z ≤ (bound : WithTop ℝ)) : z ∈ K := by
      have hinside : dist z < ENNReal.ofReal (r * (shift z + 1 / 10)) := by
        by_contra hnot
        have htop : W z = ⊤ := by
          simp only [W, physicalWeightedCost, dist, shift, ite_eq_right hnot]
        exact WithTop.not_top_le_coe bound (htop ▸ hz)
      have harg := hargInside z hinside
      have hfinite : cost z ≠ ⊤ := by
        intro htop
        rw [hWformula z hinside, htop, WithTop.map_top] at hz
        exact WithTop.not_top_le_coe bound hz
      obtain ⟨L, hL⟩ := WithTop.ne_top_iff_exists.mp hfinite
      have hreal : phi (arg z) * (2 * z.1.val * L + 2 * r * z.1.val) ≤ bound := by
        rw [hWformula z hinside, ← hL, WithTop.map_coe] at hz
        exact WithTop.coe_le_coe.mp hz
      have hZ := hshifted z L hL.symm
      have hargθ : arg z < θ := by
        by_contra hnot
        have hp := DifferentialGeometry.Analysis.SingularBarrier.monotoneOn hθ harg
          (le_of_not_gt hnot)
        have hp0 := DifferentialGeometry.Analysis.SingularBarrier.pos harg
        have hlow := mul_le_mul_of_nonneg_left hZ hp0.le
        have hmul := mul_le_mul_of_nonneg_right hp hρ.le
        have hstrict := (div_lt_iff₀ hρ).mp hphiθ
        nlinarith
      have hrealDist : (dist z).toReal < Rθ z := by
        have hh := (div_lt_iff₀ hr).mp ((sub_lt_iff_lt_add).mp hargθ)
        dsimp only [arg, Rθ] at hh ⊢
        nlinarith
      have hRpos : 0 < Rθ z := (ENNReal.toReal_nonneg).trans_lt hrealDist
      exact ⟨hRpos.le, (ENNReal.lt_ofReal_iff_toReal_lt
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hinside.le)).mpr hrealDist |>.le⟩
    have hKarg (z : K) : arg z.val ≤ θ := by
      have hd := ENNReal.toReal_le_of_le_ofReal z.property.1 z.property.2
      dsimp only [arg]
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hr).mpr
      dsimp only [Rθ] at hd
      nlinarith
    have hKinside (z : K) : dist z.val < ENNReal.ofReal (r * (shift z.val + 1 / 10)) := by
      have hRlt : Rθ z.val < r * (shift z.val + 1 / 10) := by
        dsimp only [Rθ]
        nlinarith
      have hRpos : 0 < r * (shift z.val + 1 / 10) := z.property.1.trans_lt hRlt
      exact z.property.2.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hRpos).mpr hRlt)
    have hKdist : Continuous (fun z : K => (dist z.val).toReal) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      have hcomp : ContinuousAt (fun z : K => dist z.val) z :=
        hdist.continuousAt.comp continuous_subtype_val.continuousAt
      exact (ENNReal.continuousAt_toReal
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top z.property.2)).comp
        (f := fun z : K => dist z.val) (x := z) hcomp
    have hKphi : Continuous (fun z : K => phi (arg z.val)) :=
      DifferentialGeometry.Analysis.SingularBarrier.contDiffOn.continuousOn.comp_continuous
        ((hKdist.div_const r).sub (hshift.comp continuous_subtype_val))
        (fun z => (hKarg z).trans_lt hθ)
    have hKtime : Continuous (fun z : K => z.val.1.val) := htime.comp continuous_subtype_val
    have hKlsc : LowerSemicontinuous (fun z : K => W z.val) := by
      have hh := ObservedHistory.lowerSemicontinuous_variable_positive_affine_map
        (fun z : K => cost z.val) (hcost.comp continuous_subtype_val)
        (fun z : K => phi (arg z.val) * (2 * z.val.1.val))
        (fun z : K => phi (arg z.val) * (2 * r * z.val.1.val))
        (hKphi.mul (continuous_const.mul hKtime))
        (hKphi.mul (continuous_const.mul hKtime))
        (fun z => mul_pos (DifferentialGeometry.Analysis.SingularBarrier.pos
          ((hKarg z).trans_lt hθ)) (mul_pos (by norm_num) (ha.trans_le z.val.1.property.1)))
      convert hh using 1
      funext z
      rw [hWformula z.val (hKinside z)]
      congr 1
      funext L
      ring
    have hclosed : IsClosed {z : K | W z.val ≤ (bound : WithTop ℝ)} :=
      lowerSemicontinuous_iff_isClosed_preimage.mp hKlsc _
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
    have himg := hclosed.isCompact.image continuous_subtype_val
    convert himg using 1
    ext z
    constructor
    · intro hz
      exact ⟨⟨z, hcapture z hz⟩, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hz
  have hWlsc : LowerSemicontinuous W := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro bound
    cases bound using WithTop.recTopCoe with
    | top => simpa only [Iic_top, preimage_univ] using isClosed_univ
    | coe bound => exact (hcompact bound).isClosed
  have hrange (w : Icc a b) : (range (fun y => W (w, y))).Nonempty :=
    ⟨_, mem_range_self O⟩
  have hbdd (w : Icc a b) : BddBelow (range (fun y => W (w, y))) :=
    ⟨0, by rintro _ ⟨y, rfl⟩; exact hnonneg (w, y)⟩
  have hmin (w : Icc a b) : ∃ y : (H.stage first).Carrier,
      M w.val = W (w, y) ∧ ∀ z, W (w, y) ≤ W (w, z) := by
    have hl := hWlsc.comp (continuous_const.prodMk continuous_id :
      Continuous (fun y : (H.stage first).Carrier => (w, y)))
    obtain ⟨y, _, hy⟩ := LowerSemicontinuousOn.exists_isMinOn
      ⟨O, mem_univ O⟩ isCompact_univ (hl.lowerSemicontinuousOn univ)
    refine ⟨y, le_antisymm (csInf_le (hbdd w) (mem_range_self y)) ?_,
      fun z => hy (mem_univ z)⟩
    apply le_csInf (hrange w)
    rintro _ ⟨z, rfl⟩
    exact hy (mem_univ z)
  have hMlsc : LowerSemicontinuous (fun w : Icc a b => M w.val) := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro bound
    cases bound using WithTop.recTopCoe with
    | top => simpa only [Iic_top, preimage_univ] using isClosed_univ
    | coe bound =>
      have hp := (hcompact bound).image (continuous_fst : Continuous (Prod.fst : X → Icc a b))
      convert hp.isClosed using 1
      ext w
      constructor
      · intro hw
        obtain ⟨y, hy, _⟩ := hmin w
        exact ⟨(w, y), hy.symm.trans_le hw, rfl⟩
      · rintro ⟨⟨w, y⟩, hy, rfl⟩
        exact (csInf_le (hbdd w) (mem_range_self y)).trans hy
  refine ⟨lowerSemicontinuous_restrict_iff.mp hMlsc, ?_, ?_⟩
  · intro w hw
    apply le_csInf (hrange ⟨w, hw⟩)
    rintro _ ⟨y, rfl⟩
    exact hnonneg (⟨w, hw⟩, y)
  · intro w hw
    exact hmin ⟨w, hw⟩

theorem physicalWeightedCost_minima_on_half_clock_of_cutoff_records
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hfixed : ∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y)
    (hscalar : ∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y)
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T r A a b : ℝ) (hr : 0 < r) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ^ 2 ≤ r ^ 2 / 2) (hT : 2 * r ^ 2 < T)
    (hupper : T ∈ H.stageDomain last)
    (hclock : ∀ w ∈ Icc a b,
      T - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (x : (H.stage last).Carrier) (O : (H.stage first).Carrier) :
    let M : ℝ → WithTop ℝ := fun w => sInf (Set.range
      (H.physicalWeightedCost first last hle T (3 / a₀) r A w x O))
    ∀ w ∈ Icc a b, ∃ q : (H.stage first).Carrier,
      M w = H.physicalWeightedCost first last hle T (3 / a₀) r A w x O q ∧
      ∀ y : (H.stage first).Carrier,
        H.physicalWeightedCost first last hle T (3 / a₀) r A w x O q ≤
          H.physicalWeightedCost first last hle T (3 / a₀) r A w x O y := by
  have hb0 : 0 < b := ha.trans_le hab
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hT0 : 0 < T := by nlinarith
  let Bsharp : ℝ := 3 / (a₀ + T / 2)
  have hden : 0 < a₀ + T / 2 := by positivity
  have hBsharp : 0 < Bsharp := by dsimp only [Bsharp]; positivity
  have hBr : Bsharp * r ^ 2 < 3 := by
    dsimp only [Bsharp]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hblt : b < r := by nlinarith
  have hroom : (2 * Bsharp / 3) * b ^ 3 < r := by
    have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * Bsharp / 3)
    have hcoef : (2 * Bsharp / 3) * b ^ 2 < 1 := by nlinarith
    have hm := mul_lt_mul_of_pos_right hcoef hb0
    nlinarith
  have hHI := (H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalar).1
  have hfloors (j : H.StageInterval first last) (s : ℝ)
      (hs : s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T b j.val))
      (y : (H.stage j.val).Carrier) :
      -(3 / a₀) ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y ∧
        -Bsharp ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y := by
    have hs0 : 0 ≤ s := (Real.sqrt_nonneg _).trans hs.1.le
    have hend : H.regularizedStageEnd T b j.val ≤ b := by
      have hh : T - max (T - b ^ 2) (H.time j.val) ≤ b ^ 2 := by
        have hm := le_max_left (T - b ^ 2) (H.time j.val)
        linarith
      exact (Real.sqrt_le_sqrt hh).trans_eq (Real.sqrt_sq hb0.le)
    have hsb : s ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hs0 (hs.2.le.trans hend) 2
    have hrecent : T / 2 ≤ T - s ^ 2 := by nlinarith
    have htime0 : 0 ≤ T - s ^ 2 := by linarith
    have htimeDen : 0 < a₀ + (T - s ^ 2) := by linarith
    have hR := (hHI j.val (T - s ^ 2) (H.mapsTo_regularizedStage_Ioo T 0 b j.val hs) y).2
    have hglobal : 3 / (a₀ + (T - s ^ 2)) ≤ 3 / a₀ := by
      apply (div_le_div_iff₀ htimeDen ha₀).mpr
      linarith
    have hnear : 3 / (a₀ + (T - s ^ 2)) ≤ Bsharp := by
      change 3 / (a₀ + (T - s ^ 2)) ≤ 3 / (a₀ + T / 2)
      apply (div_le_div_iff₀ htimeDen hden).mpr
      linarith
    constructor
    · exact (show -(3 / a₀) ≤ -3 / (a₀ + (T - s ^ 2)) by
        simpa only [neg_div] using neg_le_neg hglobal).trans hR
    · exact (show -Bsharp ≤ -3 / (a₀ + (T - s ^ 2)) by
        simpa only [neg_div] using neg_le_neg hnear).trans hR
  exact (H.physicalWeightedCost_lsc_nonnegative_and_minima_on_stage first last hle
    T (3 / a₀) Bsharp r A a b hr ha hab hBsharp.le hroom hupper hclock
    (fun j s hs y => (hfloors j s hs y).1)
    (fun j s hs y => (hfloors j s hs y).2) x O).2.2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

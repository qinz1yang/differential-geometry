import DifferentialGeometry.Topology.Order.Semicontinuity
import Mathlib.Topology.Order.LeftRight
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryActionJoin
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.Density
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology Interval BigOperators NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

private theorem continuousOn_stage_scalar_prod (j : Fin (H.eventCount + 1)) :
    ContinuousOn (fun z : ℝ × (H.stage j).Carrier => metricScalarAt (H.stageMetric j z.1) z.2)
      (H.stageDomain j ×ˢ univ) := by
  cases j using Fin.lastCases with
  | cast i =>
    have hh := (H.event i).incoming.equation.scalarCont
    simpa only [ObservedHistory.stageMetric_castSucc_apply, ObservedHistory.stageDomain,
      Fin.lastCases_castSucc, SolutionOn.scalar, SolutionFamily.scalar,
      RealTimeInterval.closedOpen] using hh
  | last =>
    by_cases h : H.time (Fin.last H.eventCount) < H.horizon
    · have hh := (H.finalSlab h).equation.scalarCont
      simpa only [ObservedHistory.stageMetric_last_of_lt (h := h), ObservedHistory.stageDomain,
        Fin.lastCases_last, SolutionOn.scalar, SolutionFamily.scalar, RealTimeInterval.closed] using hh
    · simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dif_neg h]
      exact ((metricScalar_smooth (H.initialMetric (Fin.last H.eventCount))).continuous.comp
        continuous_snd).continuousOn

private theorem stage_const_lagrangian_eq
    (j : Fin (H.eventCount + 1)) (T : ℝ) (y : (H.stage j).Carrier) (s : ℝ) :
    H.stageRegularizedLagrangian j T (fun _ => y) s =
      2 * s ^ 2 * metricScalarAt (H.stageMetric j (T - s ^ 2)) y := by
  have hv : lVelocity (I := ThreeModel) (fun _ : ℝ => y) s = 0 := by
    simp only [lVelocity, mfderiv_const]
    rfl
  simp only [stageRegularizedLagrangian, hv, map_zero, mul_zero, zero_add]

theorem exists_uniform_regularizedC1ActionValues_const_extension_le
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T u a b : ℝ)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hclock : ∀ s ∈ Icc a b, T - s ^ 2 ∈ H.stageDomain first) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ w ∈ Icc a b, ∀ v ∈ Icc a b, w ≤ v →
      ∀ (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) (A : ℝ),
      A ∈ H.regularizedC1ActionValues first last hle T u w p q →
      ∀ ε : ℝ, 0 < ε →
      ∃ A' ∈ H.regularizedC1ActionValues first last hle T u v p q,
        A' ≤ A + C * (v - w) + ε := by
  have hcont : ContinuousOn
      (fun z : ℝ × (H.stage first).Carrier =>
        2 * z.1 ^ 2 * metricScalarAt (H.stageMetric first (T - z.1 ^ 2)) z.2)
      (Icc a b ×ˢ univ) := by
    apply ContinuousOn.mul
    · fun_prop
    · apply (H.continuousOn_stage_scalar_prod first).comp
        (f := fun z : ℝ × (H.stage first).Carrier => (T - z.1 ^ 2, z.2)) (by fun_prop)
      intro z hz
      exact ⟨hclock z.1 hz.1, mem_univ _⟩
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_univ).bddAbove_image hcont
  let C := max 0 K
  refine ⟨C, le_max_left _ _, ?_⟩
  intro w hw v hv hwv p q A hA ε hε
  rcases hwv.eq_or_lt with rfl | hwv
  · exact ⟨A, hA, by simp only [sub_self, mul_zero, add_zero]; exact le_add_of_nonneg_right hε.le⟩
  have htail : ContinuousOn (H.stageRegularizedLagrangian first T (fun _ => q)) (Icc w v) := by
    have hh : ContinuousOn
        (fun s => 2 * s ^ 2 * metricScalarAt (H.stageMetric first (T - s ^ 2)) q) (Icc w v) :=
      hcont.comp (continuousOn_id.prodMk continuousOn_const)
        (fun s hs => ⟨⟨hw.1.trans hs.1, hs.2.trans hv.2⟩, mem_univ q⟩)
    rw [show H.stageRegularizedLagrangian first T (fun _ => q) =
      (fun s => 2 * s ^ 2 * metricScalarAt (H.stageMetric first (T - s ^ 2)) q) from
        funext (H.stage_const_lagrangian_eq first T q)]
    exact hh
  have hint : IntervalIntegrable (H.stageRegularizedLagrangian first T (fun _ => q)) volume w v :=
    htail.intervalIntegrable_of_Icc hwv.le
  have htailBound : H.stageRegularizedAction first T (fun _ => q) w v ≤ C * (v - w) := by
    have hh := intervalIntegral.integral_mono_on hwv.le hint (intervalIntegrable_const (c := C))
      (fun s hs => by
        rw [H.stage_const_lagrangian_eq]
        exact (hK ⟨(s, q), ⟨⟨hw.1.trans hs.1, hs.2.trans hv.2⟩, mem_univ q⟩, rfl⟩).trans
          (le_max_right _ _))
    simpa only [stageRegularizedAction, intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hh
  obtain ⟨A', hA', hbound⟩ := H.exists_regularizedC1ActionValues_join_same_stage first last hle
    hwv hε hupper (hclock v hv) p q q hA (fun _ => q) contMDiff_const rfl rfl hint
  exact ⟨A', hA', hbound.trans (by linarith)⟩

theorem exists_regularizedC1ActionValues_prefix_le
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v A : ℝ}
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hA : A ∈ H.regularizedC1ActionValues first last hle T u v p q)
    (k : H.StageInterval first last) {w : ℝ} (hw : w ∈ Icc u v)
    (hkw : T - w ^ 2 ∈ H.stageDomain k.val) :
    ∃ (y : (H.stage k.val).Carrier) (C : ℝ),
      C ∈ H.regularizedC1ActionValues k.val last k.property.2 T u w p y ∧
        C ≤ A + (2 * B / 3) * (v ^ 3 - w ^ 3) := by
  obtain ⟨hu, huv, hupper, hlower, α, hα, hint, hstart, _, hnodes, hsum⟩ := hA
  let embed : H.StageInterval k.val last → H.StageInterval first last :=
    fun j => ⟨j.val, k.property.1.trans j.property.1, j.property.2⟩
  let β := fun j : H.StageInterval k.val last => α (embed j)
  let C := ∑ j : H.StageInterval k.val last, H.stageRegularizedAction j.val T (β j)
    (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)
  refine ⟨β ⟨k.val, le_rfl, k.property.2⟩ w, C,
    ⟨hu, hw.1, hupper, hkw, β, (fun j => hα (embed j)), ?_, hstart, rfl, ?_, rfl⟩, ?_⟩
  · intro j
    apply (hint (embed j)).mono_set
    rw [uIcc_of_le (H.regularizedStage_bounds hu hw.1 hupper hkw j).2.1,
      uIcc_of_le (H.regularizedStage_bounds hu huv hupper hlower (embed j)).2.1]
    exact Icc_subset_Icc le_rfl
      (H.regularizedStageEnd_monotoneOn T j.val (hu.trans hw.1) (hu.trans huv) hw.2)
  · intro i hki hil
    exact hnodes i (k.property.1.trans hki) hil
  · exact H.sum_stageRegularizedAction_prefix_le_of_sum_le hu huv hupper hlower α hint
      (fun j t ht => hscalar j t ht (α j t)) hsum.le k hw hkw

theorem regularizedCost_ge_of_prefix_lower_bound
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (k : H.StageInterval first last) {w m : ℝ} (hw : w ∈ Icc u v)
    (hkw : T - w ^ 2 ∈ H.stageDomain k.val)
    (hlower : ∀ y : (H.stage k.val).Carrier,
      (m : WithTop ℝ) ≤ H.regularizedCost k.val last k.property.2 T B u w p y) :
    ((m - (2 * B / 3) * (v ^ 3 - w ^ 3) : ℝ) : WithTop ℝ) ≤
      H.regularizedCost first last hle T B u v p q := by
  rw [H.regularizedCost_eq_regularizedC1Cost first last hle T B u v hupper hscalar]
  by_cases hne : (H.regularizedC1ActionValues first last hle T u v p q).Nonempty
  · apply le_csInf (hne.image (fun A : ℝ => (A : WithTop ℝ)))
    rintro _ ⟨A, hA, rfl⟩
    have hu : 0 ≤ u := hA.1
    obtain ⟨y, C, hC, hCA⟩ :=
      H.exists_regularizedC1ActionValues_prefix_le first last hle hscalar p q hA k hw hkw
    have hscalar' : ∀ j : H.StageInterval k.val last,
        ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val),
        ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x := by
      intro j t ht x
      exact hscalar ⟨j.val, k.property.1.trans j.property.1, j.property.2⟩ t
        ⟨ht.1, ht.2.trans_le (H.regularizedStageEnd_monotoneOn T j.val
          (hu.trans hw.1) (hu.trans hA.2.1) hw.2)⟩ x
    have hmin := (hlower y).trans (H.regularizedCost_le_of_competitor
      k.val last k.property.2 T B u w p y
        (H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
          k.val last k.property.2 hscalar' p y hC))
    apply WithTop.coe_le_coe.mpr
    have hmC : m ≤ C := WithTop.coe_le_coe.mp hmin
    linarith only [hmC, hCA]
  · rw [H.regularizedC1Cost_eq_top_of_no_competitor first last hle T u v p q
      (Set.not_nonempty_iff_eq_empty.mp hne)]
    exact le_top

theorem exists_lipschitz_spatial_cost_minimum_on_stage
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u a b : ℝ) (hab : a ≤ b)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hclock : ∀ s ∈ Icc a b, T - s ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T b j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier)
    (hfinite : ∃ q : (H.stage first).Carrier, H.regularizedCost first last hle T B u a p q ≠ ⊤) :
    ∃ (m : ℝ → ℝ) (C : ℝ≥0), LipschitzOnWith C m (Icc a b) ∧
      ∀ v ∈ Icc a b,
        sInf (range (H.regularizedCost first last hle T B u v p)) = (m v : WithTop ℝ) ∧
        ∃ q : (H.stage first).Carrier,
          H.regularizedCost first last hle T B u v p q = (m v : WithTop ℝ) := by
  classical
  obtain ⟨q₀, hq₀⟩ := hfinite
  have hsome : ¬ ∀ A ∈ H.regularizedActionValues first last hle T B u a p q₀, A = ⊤ :=
    fun h => hq₀ ((H.regularizedCost_eq_top_iff first last hle T B u a p q₀).mpr h)
  push Not at hsome
  obtain ⟨A₀, hA₀, hA₀top⟩ := hsome
  obtain ⟨A, hA⟩ := WithTop.ne_top_iff_exists.mp hA₀top
  rw [← hA] at hA₀
  have hu : 0 ≤ u := hA₀.1
  have hua : u ≤ a := hA₀.2.1
  have ha : 0 ≤ a := hu.trans hua
  have hb : 0 ≤ b := ha.trans hab
  have hfloor (v : ℝ) (hv : v ∈ Icc a b) : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x := by
    intro j t ht x
    exact hscalar j t ⟨ht.1, ht.2.trans_le
      (H.regularizedStageEnd_monotoneOn T j.val (ha.trans hv.1) hb hv.2)⟩ x
  obtain ⟨c₀, hc₀, _⟩ := H.exists_mem_regularizedC1ActionValues_lt_of_mem_regularizedActionValues
    first last hle hupper (hfloor a ⟨le_rfl, hab⟩) p q₀ hA₀ (ε := 1) zero_lt_one
  obtain ⟨K, hK, happend⟩ := H.exists_uniform_regularizedC1ActionValues_const_extension_le
    first last hle T u a b hupper hclock
  have hfiniteV (v : ℝ) (hv : v ∈ Icc a b) :
      ∃ q : (H.stage first).Carrier, H.regularizedCost first last hle T B u v p q ≠ ⊤ := by
    obtain ⟨c, hc, _⟩ := happend a ⟨le_rfl, hab⟩ v hv hv.1 p q₀ c₀ hc₀ 1 zero_lt_one
    refine ⟨q₀, ne_top_of_le_ne_top (b := (c : WithTop ℝ)) WithTop.coe_ne_top ?_⟩
    exact H.regularizedCost_le_of_competitor first last hle T B u v p q₀
      (H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
        first last hle (hfloor v hv) p q₀ hc)
  have hminV (v : ℝ) (hv : v ∈ Icc a b) :=
    H.exists_regularizedCost_spatial_minimizer first last hle T B u v hupper (hfloor v hv) p (hfiniteV v hv)
  choose q m γ hAC hInt hstart hend hnodes haction hmember hcost hmin using hminV
  let value : ℝ → ℝ := fun v => if hv : v ∈ Icc a b then m v hv else 0
  have hvalue (v : ℝ) (hv : v ∈ Icc a b) : value v = m v hv := dif_pos hv
  have hforward {w v : ℝ} (hw : w ∈ Icc a b) (hv : v ∈ Icc a b) (hwv : w ≤ v) :
      m v hv ≤ m w hw + K * (v - w) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨c, hc, hcm⟩ := H.exists_mem_regularizedC1ActionValues_lt_of_mem_regularizedActionValues
      first last hle hupper (hfloor w hw) p (q w hw) (hmember w hw) (half_pos hε)
    obtain ⟨d, hd, hdc⟩ := happend w hw v hv hwv p (q w hw) c hc (ε / 2) (half_pos hε)
    have hm := (hmin v hv (q w hw)).trans (H.regularizedCost_le_of_competitor
      first last hle T B u v p (q w hw)
        (H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
          first last hle (hfloor v hv) p (q w hw) hd))
    have hmd : m v hv ≤ d := WithTop.coe_le_coe.mp hm
    linarith only [hmd, hdc, hcm]
  have hreverse {w v : ℝ} (hw : w ∈ Icc a b) (hv : v ∈ Icc a b) (hwv : w ≤ v) :
      m w hw ≤ m v hv + (2 * B / 3) * (v ^ 3 - w ^ 3) := by
    have hh := H.regularizedCost_ge_of_prefix_lower_bound first last hle hupper (hfloor v hv)
      p (q v hv) ⟨first, le_rfl, hle⟩ (w := w) (m := m w hw)
      ⟨hua.trans hw.1, hwv⟩ (hclock w hw) (hmin w hw)
    rw [hcost v hv] at hh
    have hh' := WithTop.coe_le_coe.mp hh
    linarith only [hh']
  let L : ℝ := max K (2 * |B| * b ^ 2)
  have hL : 0 ≤ L := hK.trans (le_max_left _ _)
  have hcubic {w v : ℝ} (hw : w ∈ Icc a b) (hv : v ∈ Icc a b) (hwv : w ≤ v) :
      (2 * B / 3) * (v ^ 3 - w ^ 3) ≤ L * (v - w) := by
    have hw0 := ha.trans hw.1
    have hv0 := ha.trans hv.1
    have hww := (sq_le_sq₀ hw0 hb).mpr hw.2
    have hvv := (sq_le_sq₀ hv0 hb).mpr hv.2
    have hwv' : w * v ≤ b ^ 2 := by nlinarith [mul_le_mul hw.2 hv.2 hv0 hb]
    have hquad : v ^ 2 + v * w + w ^ 2 ≤ 3 * b ^ 2 := by nlinarith
    have hdiff : v ^ 3 - w ^ 3 = (v - w) * (v ^ 2 + v * w + w ^ 2) := by ring
    have hdiff0 : 0 ≤ v ^ 3 - w ^ 3 := sub_nonneg.mpr (pow_le_pow_left₀ hw0 hwv 3)
    calc
      _ ≤ (2 * |B| / 3) * (v ^ 3 - w ^ 3) := by gcongr; exact le_abs_self B
      _ ≤ (2 * |B| * b ^ 2) * (v - w) := by
        rw [hdiff]
        have hh := mul_le_mul_of_nonneg_left hquad
          (mul_nonneg (by positivity : 0 ≤ 2 * |B| / 3) (sub_nonneg.mpr hwv))
        nlinarith only [hh]
      _ ≤ L * (v - w) := mul_le_mul_of_nonneg_right (le_max_right _ _) (sub_nonneg.mpr hwv)
  have hdist {w v : ℝ} (hw : w ∈ Icc a b) (hv : v ∈ Icc a b) (hwv : w ≤ v) :
      dist (value w) (value v) ≤ L * dist w v := by
    rw [hvalue w hw, hvalue v hv, Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hwv)]
    apply abs_le.mpr
    constructor
    · have hh := hforward hw hv hwv
      have hKL := mul_le_mul_of_nonneg_right (le_max_left K (2 * |B| * b ^ 2)) (sub_nonneg.mpr hwv)
      linarith only [hh, hKL]
    · have hh := hreverse hw hv hwv
      have hbound := hcubic hw hv hwv
      linarith only [hh, hbound]
  refine ⟨value, ⟨L, hL⟩, ?_, ?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro w hw v hv
    rcases le_total w v with hwv | hvw
    · exact hdist hw hv hwv
    · change dist (value w) (value v) ≤ L * dist w v
      simpa only [dist_comm] using hdist hv hw hvw
  · intro v hv
    rw [hvalue v hv]
    refine ⟨?_, q v hv, hcost v hv⟩
    apply IsLeast.csInf_eq
    exact ⟨⟨q v hv, hcost v hv⟩, by rintro z ⟨y, rfl⟩; exact hmin v hv y⟩

theorem continuousOn_sInf_regularizedCost_on_stage
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u a b : ℝ) (hab : a ≤ b)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hclock : ∀ s ∈ Icc a b, T - s ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T b j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier)
    (hfinite : ∃ q : (H.stage first).Carrier, H.regularizedCost first last hle T B u a p q ≠ ⊤) :
    ContinuousOn (fun v : ℝ => sInf (range (H.regularizedCost first last hle T B u v p))) (Icc a b) := by
  obtain ⟨m, C, hLip, hm⟩ := H.exists_lipschitz_spatial_cost_minimum_on_stage first last hle
    T B u a b hab hupper hclock hscalar p hfinite
  exact (WithTop.continuous_coe.comp_continuousOn hLip.continuousOn).congr (fun v hv => (hm v hv).1)

theorem continuousOn_sInf_regularizedCost_on_stage_of_terminal_ne_top
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u a b : ℝ) (hua : u ≤ a) (hab : a ≤ b)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hclock : ∀ s ∈ Icc a b, T - s ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T b j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier)
    (hfinite : ∃ q : (H.stage first).Carrier, H.regularizedCost first last hle T B u b p q ≠ ⊤) :
    ContinuousOn (fun v : ℝ => sInf (range (H.regularizedCost first last hle T B u v p))) (Icc a b) := by
  obtain ⟨q, hq⟩ := hfinite
  have hsome : ¬ ∀ A ∈ H.regularizedActionValues first last hle T B u b p q, A = ⊤ :=
    fun h => hq ((H.regularizedCost_eq_top_iff first last hle T B u b p q).mpr h)
  push Not at hsome
  obtain ⟨A, hA, hAtop⟩ := hsome
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hAtop
  rw [← hr] at hA
  have hu : 0 ≤ u := hA.1
  obtain ⟨c, hc, _⟩ := H.exists_mem_regularizedC1ActionValues_lt_of_mem_regularizedActionValues
    first last hle hupper hscalar p q hA (ε := 1) zero_lt_one
  obtain ⟨y, C, hC, _⟩ := H.exists_regularizedC1ActionValues_prefix_le first last hle
    hscalar p q hc ⟨first, le_rfl, hle⟩ ⟨hua, hab⟩ (hclock a ⟨le_rfl, hab⟩)
  have hfloor : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T a j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x := by
    intro j t ht x
    exact hscalar j t ⟨ht.1, ht.2.trans_le
      (H.regularizedStageEnd_monotoneOn T j.val (hu.trans hua) (hu.trans hA.2.1) hab)⟩ x
  apply H.continuousOn_sInf_regularizedCost_on_stage first last hle T B u a b hab hupper hclock hscalar p
  refine ⟨y, ne_top_of_le_ne_top (b := (C : WithTop ℝ)) WithTop.coe_ne_top ?_⟩
  exact H.regularizedCost_le_of_competitor first last hle T B u a p y
    (H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues first last hle hfloor p y hC)

theorem tendsto_sInf_regularizedCost_left
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u v : ℝ) (huv : u < v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier)
    (hfinite : ∃ q : (H.stage first).Carrier, H.regularizedCost first last hle T B u v p q ≠ ⊤) :
    Tendsto (fun w : ℝ => sInf (range (H.regularizedCost first last hle T B u w p)))
      (𝓝[<] v) (𝓝 (sInf (range (H.regularizedCost first last hle T B u v p)))) := by
  obtain ⟨q, hq⟩ := hfinite
  have hne : (H.regularizedActionValues first last hle T B u v p q).Nonempty := by
    by_contra h
    exact hq (H.regularizedCost_eq_top_of_no_competitor first last hle T B u v p q
      (Set.not_nonempty_iff_eq_empty.mp h))
  obtain ⟨_, hvalue⟩ := hne
  have hu : 0 ≤ u := hvalue.1
  have hv : 0 ≤ v := hu.trans huv.le
  have hpast : T - v ^ 2 ∈ H.stageDomain first := hvalue.2.2.2.1
  have hstrict : T - v ^ 2 < H.stageEndTime first := by
    cases first using Fin.lastCases with
    | cast i =>
      have hpast' : T - v ^ 2 ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
        simpa only [stageDomain, Fin.lastCases_castSucc] using hpast
      simpa only [stageEndTime_castSucc] using hpast'.2
    | last =>
      have hlast : last = Fin.last H.eventCount := le_antisymm (Fin.le_last _) hle
      subst last
      have hbound := H.le_stageEndTime_of_mem_stageDomain hupper
      have hsq := (sq_lt_sq₀ hu hv).mpr huv
      linarith
  have hnear : ∀ᶠ w in 𝓝 v, T - w ^ 2 < H.stageEndTime first :=
    ((continuous_const.sub (continuous_id.pow 2)).continuousAt).eventually (Iio_mem_nhds hstrict)
  have hnearLT : ∀ᶠ w in 𝓝[<] v, u < w ∧ T - w ^ 2 < H.stageEndTime first :=
    (Filter.Eventually.and (Ioi_mem_nhds huv) hnear).filter_mono nhdsWithin_le_nhds
  obtain ⟨a, hav, ha⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hnearLT
  change a < v at hav
  obtain ⟨a', haa', ha'v⟩ := exists_between hav
  have hua' : u < a' := (ha ⟨haa', ha'v⟩).1
  have hclock : ∀ r ∈ Icc a' v, T - r ^ 2 ∈ H.stageDomain first := by
    intro r hr
    rcases hr.2.eq_or_lt with rfl | hrv
    · exact hpast
    · apply H.mem_stageDomain_of_mem_Ioo
      have hsq := (sq_lt_sq₀ ((hu.trans hua'.le).trans hr.1) hv).mpr hrv
      exact ⟨by linarith [H.time_le_of_mem_stageDomain hpast],
        (ha ⟨haa'.trans_le hr.1, hrv⟩).2⟩
  have hc := H.continuousOn_sInf_regularizedCost_on_stage_of_terminal_ne_top first last hle
    T B u a' v hua'.le ha'v.le hupper hclock hscalar p ⟨q, hq⟩
  exact (hc v ⟨ha'v.le, le_rfl⟩).mono_left
    (le_inf nhdsWithin_le_nhds (le_principal_iff.mpr (Icc_mem_nhdsLT ha'v)))

theorem continuousAt_sInf_regularizedCost_of_mem_stage_interior
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u v : ℝ) (huv : u < v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hclock : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hfloor : ∀ j : Fin (H.eventCount + 1), ∀ s ∈ H.stageDomain j,
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j s) x)
    (p : (H.stage last).Carrier)
    (hfinite : ∃ q : (H.stage first).Carrier, H.regularizedCost first last hle T B u v p q ≠ ⊤) :
    ContinuousAt (fun w : ℝ => sInf (range (H.regularizedCost first last hle T B u w p))) v := by
  have hnear : ∀ᶠ r in 𝓝 v, u < r ∧ T - r ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) := by
    have hc : ContinuousAt (fun r : ℝ => T - r ^ 2) v := by fun_prop
    exact Filter.Eventually.and (Ioi_mem_nhds huv) (hc.preimage_mem_nhds (isOpen_Ioo.mem_nhds hclock))
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hnear
  let a := v - δ / 2
  let b := v + δ / 2
  have hav : a < v := by dsimp only [a]; linarith
  have hvb : v < b := by dsimp only [b]; linarith
  have hband (r : ℝ) (hr : r ∈ Icc a b) :
      u < r ∧ T - r ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) := by
    apply hδbound
    rw [Real.dist_eq, abs_lt]
    dsimp only [a, b] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hbandClock : ∀ r ∈ Icc a b, T - r ^ 2 ∈ H.stageDomain first :=
    fun r hr => H.mem_stageDomain_of_mem_Ioo (hband r hr).2
  have hscalar (w : ℝ) : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x :=
    fun j r hr x => hfloor j.val (T - r ^ 2) (H.mapsTo_regularizedStage_Ioo T u w j.val hr) x
  obtain ⟨q, hq⟩ := hfinite
  have hsome : ¬ ∀ A ∈ H.regularizedActionValues first last hle T B u v p q, A = ⊤ :=
    fun h => hq ((H.regularizedCost_eq_top_iff first last hle T B u v p q).mpr h)
  push Not at hsome
  obtain ⟨A, hA, hAtop⟩ := hsome
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hAtop
  rw [← hr] at hA
  obtain ⟨C, hC, _⟩ := H.exists_mem_regularizedC1ActionValues_lt_of_mem_regularizedActionValues
    first last hle hupper (hscalar v) p q hA (ε := 1) zero_lt_one
  obtain ⟨K, _, happend⟩ := H.exists_uniform_regularizedC1ActionValues_const_extension_le
    first last hle T u a b hupper hbandClock
  obtain ⟨C', hC', _⟩ := happend v ⟨hav.le, hvb.le⟩ b ⟨(hav.trans hvb).le, le_rfl⟩
    hvb.le p q C hC 1 zero_lt_one
  have hfiniteB : H.regularizedCost first last hle T B u b p q ≠ ⊤ :=
    ne_top_of_le_ne_top (b := (C' : WithTop ℝ)) WithTop.coe_ne_top
      (H.regularizedCost_le_of_competitor first last hle T B u b p q
        (H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
          first last hle (hscalar b) p q hC'))
  have hcont := H.continuousOn_sInf_regularizedCost_on_stage_of_terminal_ne_top first last hle
    T B u a b (hband a ⟨le_rfl, (hav.trans hvb).le⟩).1.le (hav.trans hvb).le
    hupper hbandClock (hscalar b) p ⟨q, hfiniteB⟩
  exact (hcont v ⟨hav.le, hvb.le⟩).continuousAt (Icc_mem_nhds hav hvb)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem continuousAt_regularizedSpatialCost_of_eq_sqrt
    (t : Icc (0 : ℝ) H.horizon) (B : ℝ) (p : (H.stageAt t).Carrier)
    (v : Icc (0 : ℝ) (Real.sqrt t.val))
    (hvmax : v.val = Real.sqrt t.val)
    (hfloor : ∀ (j : Fin (H.eventCount + 1)) (s : ℝ), s ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j s) x)
    (hfinite : ∃ q : (H.stage 0).Carrier,
      H.regularizedCost 0 (H.activeStage t) (Fin.zero_le _) t B 0 v.val p q ≠ ⊤) :
    ContinuousAt (H.regularizedSpatialCost t B p) v := by
  by_cases hvzero : v.val = 0
  · have heq : H.regularizedSpatialCost t B p =
        fun _ => H.regularizedSpatialCost t B p v := by
      funext w
      have hw : w = v := by
        apply Subtype.ext
        calc
          w.val = 0 := le_antisymm (w.property.2.trans_eq (hvmax.symm.trans hvzero))
            w.property.1
          _ = v.val := hvzero.symm
      rw [hw]
    rw [heq]
    exact continuousAt_const
  have hv : 0 < v.val := lt_of_le_of_ne v.property.1 (Ne.symm hvzero)
  have hclock : t.val - v.val ^ 2 = 0 := by
    rw [hvmax, Real.sq_sqrt t.property.1, sub_self]
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t
  have hscalar (j : H.StageInterval 0 (H.activeStage t))
      (r : ℝ) (hr : r ∈ Ioo (H.regularizedStageStart t 0 j.val)
        (H.regularizedStageEnd t v.val j.val)) (x : (H.stage j.val).Carrier) :
      -B ≤ metricScalarAt (H.stageMetric j.val (t.val - r ^ 2)) x :=
    hfloor j.val _ (H.mapsTo_regularizedStage_Ioo t 0 v.val j.val hr) x
  let f : ℝ → WithTop ℝ := fun w =>
    sInf (range (H.regularizedCost 0 (H.activeStage t) (Fin.zero_le _) t B 0 w p))
  have hleft : ContinuousWithinAt f (Iio v.val) v.val :=
    H.tendsto_sInf_regularizedCost_left 0 (H.activeStage t) (Fin.zero_le _) t B 0 v.val
      hv hupper hscalar p hfinite
  have hclosed : ContinuousWithinAt f (Iic v.val) v.val :=
    continuousWithinAt_Iio_iff_Iic.mp hleft
  have hcont : ContinuousAt (fun w : Icc (0 : ℝ) (Real.sqrt t.val) => f w.val) v :=
    (continuousWithinAt_iff_continuousAt_domRestrict f v.property).mp
      (hclosed.mono (by intro w hw; exact hw.2.trans_eq hvmax.symm))
  have hswitch := H.eventually_activeStage_eq_zero_of_backward_clock_eq_zero hclock
  have heq : H.regularizedSpatialCost t B p =ᶠ[𝓝 v]
      (fun w : Icc (0 : ℝ) (Real.sqrt t.val) => f w.val) := by
    filter_upwards [continuous_subtype_val.continuousAt.eventually hswitch] with w hw
    have hsq : w.val ^ 2 ≤ t.val := (Real.le_sqrt w.property.1 t.property.1).mp w.property.2
    have hrange : t.val - w.val ^ 2 ∈ Icc 0 H.horizon :=
      ⟨sub_nonneg.mpr hsq, (sub_le_self _ (sq_nonneg _)).trans t.property.2⟩
    apply H.regularizedSpatialCost_eq_of_mem_stageDomain t B p w 0 (Fin.zero_le _)
    exact (H.mem_stageDomain_iff ⟨t.val - w.val ^ 2, hrange⟩ 0).mpr (hw hrange)
  exact (continuousAt_congr heq).mpr hcont

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem regularizedSpatialCost_le_add_cubic_of_le
    (t : Icc (0 : ℝ) H.horizon) (B : ℝ) (p : (H.stageAt t).Carrier)
    (hfloor : ∀ (j : Fin (H.eventCount + 1)) (s : ℝ), s ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j s) x)
    (w v : Icc (0 : ℝ) (Real.sqrt t.val)) (hwv : w ≤ v) :
    H.regularizedSpatialCost t B p w ≤ H.regularizedSpatialCost t B p v +
      (((2 * B / 3) * (v.val ^ 3 - w.val ^ 3) : ℝ) : WithTop ℝ) := by
  by_cases hvtop : H.regularizedSpatialCost t B p v = ⊤
  · simp only [hvtop, WithTop.top_add, le_top]
  let clock (x : Icc (0 : ℝ) (Real.sqrt t.val)) : Icc (0 : ℝ) H.horizon :=
    ⟨t.val - x.val ^ 2, by
      have hsquare := (Real.le_sqrt x.property.1 t.property.1).mp x.property.2
      exact ⟨sub_nonneg.mpr hsquare, (sub_le_self _ (sq_nonneg _)).trans t.property.2⟩⟩
  have hclock (x : Icc (0 : ℝ) (Real.sqrt t.val)) : clock x ≤ t := by
    change t.val - x.val ^ 2 ≤ t.val
    exact sub_le_self _ (sq_nonneg _)
  have hclockvw : clock v ≤ clock w := by
    change t.val - v.val ^ 2 ≤ t.val - w.val ^ 2
    exact sub_le_sub_left (pow_le_pow_left₀ w.property.1 hwv 2) _
  let first := H.activeStage (clock v)
  let last := H.activeStage t
  let k : H.StageInterval first last :=
    ⟨H.activeStage (clock w), H.activeStage_mono hclockvw, H.activeStage_mono (hclock w)⟩
  have hle : first ≤ last := H.activeStage_mono (hclock v)
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain last := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t
  have hkw : t.val - w.val ^ 2 ∈ H.stageDomain k.val := H.activeStage_mem (clock w)
  have hvclock : t.val - v.val ^ 2 ∈ H.stageDomain first := H.activeStage_mem (clock v)
  have hscalar : ∀ j : H.StageInterval first last,
      ∀ s ∈ Ioo (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v.val j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) x :=
    fun j s hs x => hfloor j.val _ (H.mapsTo_regularizedStage_Ioo t 0 v.val j.val hs) x
  have hscalarw : ∀ j : H.StageInterval k.val last,
      ∀ s ∈ Ioo (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t w.val j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) x :=
    fun j s hs x => hfloor j.val _ (H.mapsTo_regularizedStage_Ioo t 0 w.val j.val hs) x
  have hvEq := H.regularizedSpatialCost_eq_of_mem_stageDomain t B p v first hle hvclock
  have hwEq := H.regularizedSpatialCost_eq_of_mem_stageDomain t B p w k.val k.property.2 hkw
  rw [hvEq] at hvtop
  rw [hvEq, hwEq]
  have hnonempty : (range (H.regularizedCost first last hle t B 0 v.val p)).Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn, WithTop.sInf_empty] at hvtop
    exact hvtop rfl
  obtain ⟨_, ⟨q, rfl⟩, hq⟩ := exists_lt_of_csInf_lt hnonempty (lt_top_iff_ne_top.mpr hvtop)
  have hsome : ¬ ∀ A ∈ H.regularizedActionValues first last hle t B 0 v.val p q, A = ⊤ :=
    fun h => (ne_top_of_lt hq) ((H.regularizedCost_eq_top_iff first last hle t B 0 v.val p q).mpr h)
  push Not at hsome
  obtain ⟨A, hA, hAtop⟩ := hsome
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hAtop
  rw [← ha] at hA
  obtain ⟨c, hc, _⟩ := H.exists_mem_regularizedC1ActionValues_lt_of_mem_regularizedActionValues
    first last hle hupper hscalar p q hA (ε := 1) zero_lt_one
  obtain ⟨y, d, hd, _⟩ := H.exists_regularizedC1ActionValues_prefix_le first last hle hscalar
    p q hc k ⟨w.property.1, hwv⟩ hkw
  have hdAC := H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
    k.val last k.property.2 hscalarw p y hd
  have hbddw : BddBelow (range (H.regularizedCost k.val last k.property.2 t B 0 w.val p)) := by
    refine ⟨(-(2 * B / 3) * (w.val ^ 3 - 0 ^ 3) : ℝ), ?_⟩
    rintro _ ⟨z, rfl⟩
    exact H.regularizedCost_ge k.val last k.property.2 t B 0 w.val p z
  have hwfinite : sInf (range (H.regularizedCost k.val last k.property.2 t B 0 w.val p)) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top ((csInf_le hbddw (mem_range_self y)).trans
      (H.regularizedCost_le_of_competitor k.val last k.property.2 t B 0 w.val p y hdAC))
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hwfinite
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hvtop
  have hbound : (((m - (2 * B / 3) * (v.val ^ 3 - w.val ^ 3) : ℝ)) : WithTop ℝ) ≤
      sInf (range (H.regularizedCost first last hle t B 0 v.val p)) := by
    apply le_csInf hnonempty
    rintro _ ⟨z, rfl⟩
    apply H.regularizedCost_ge_of_prefix_lower_bound first last hle hupper hscalar p z k
      ⟨w.property.1, hwv⟩ hkw
    intro x
    rw [hm]
    exact csInf_le hbddw (mem_range_self x)
  rw [← hn, WithTop.coe_le_coe] at hbound
  rw [← hm, ← hn, ← WithTop.coe_add, WithTop.coe_le_coe]
  linarith only [hbound]


theorem monotone_regularizedSpatialCost_add_cubic
    (t : Icc (0 : ℝ) H.horizon) (B : ℝ) (p : (H.stageAt t).Carrier)
    (hfloor : ∀ (j : Fin (H.eventCount + 1)) (s : ℝ), s ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j s) x) :
    Monotone (fun v : Icc (0 : ℝ) (Real.sqrt t.val) =>
      H.regularizedSpatialCost t B p v + (((2 * B / 3) * v.val ^ 3 : ℝ) : WithTop ℝ)) := by
  intro w v hwv
  have h := add_le_add (H.regularizedSpatialCost_le_add_cubic_of_le
    t B p hfloor w v hwv) (le_refl (((2 * B / 3) * w.val ^ 3 : ℝ) : WithTop ℝ))
  simpa only [add_assoc, ← WithTop.coe_add,
    show (2 * B / 3) * (v.val ^ 3 - w.val ^ 3) + (2 * B / 3) * w.val ^ 3 =
      (2 * B / 3) * v.val ^ 3 by ring] using h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem regularizedSpatialCost_ne_top_of_frequently_ne_top_left
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (B : ℝ)
    (p : (H.stageAt t).Carrier) (v : Icc (0 : ℝ) (Real.sqrt t.val))
    (hfloor : ∀ (j : Fin (H.eventCount + 1)) (s : ℝ), s ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j s) x)
    (hfinite : ∃ᶠ w in 𝓝[<] v, H.regularizedSpatialCost t B p w ≠ ⊤) :
    H.regularizedSpatialCost t B p v ≠ ⊤ := by
  classical
  obtain ⟨w₀, _, hw₀⟩ := (hfinite.and_eventually self_mem_nhdsWithin).exists
  have hv : 0 < v.val := w₀.property.1.trans_lt hw₀
  have hphysical : t.val - v.val ^ 2 ∈ Icc 0 H.horizon := by
    have hsq : v.val ^ 2 ≤ t.val := (Real.le_sqrt v.property.1 t.property.1).mp v.property.2
    exact ⟨sub_nonneg.mpr hsq, (sub_le_self _ (sq_nonneg _)).trans t.property.2⟩
  let s : Icc (0 : ℝ) H.horizon := ⟨t.val - v.val ^ 2, hphysical⟩
  let first := H.activeStage s
  let last := H.activeStage t
  have hle : first ≤ last := H.activeStage_mono (by
    change t.val - v.val ^ 2 ≤ t.val
    exact sub_le_self _ (sq_nonneg _))
  have hpast : t.val - v.val ^ 2 ∈ H.stageDomain first := H.activeStage_mem s
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain last := by
    simpa only [zero_pow two_ne_zero, sub_zero] using H.activeStage_mem t
  have hstrict : t.val - v.val ^ 2 < H.stageEndTime first := by
    cases hfirst : first using Fin.lastCases with
    | cast i =>
      have hpast' : t.val - v.val ^ 2 ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
        simpa only [hfirst, stageDomain, Fin.lastCases_castSucc] using hpast
      simpa only [stageEndTime_castSucc] using hpast'.2
    | last =>
      have hlast : last = Fin.last H.eventCount := le_antisymm (Fin.le_last _) (by simpa only [hfirst] using hle)
      have hbound := H.le_stageEndTime_of_mem_stageDomain hupper
      rw [hlast] at hbound
      have hsquare := sq_pos_of_pos hv
      linarith
  have hnear : ∀ᶠ w : Icc (0 : ℝ) (Real.sqrt t.val) in 𝓝 v,
      t.val - w.val ^ 2 < H.stageEndTime first := by
    exact ((continuous_const.sub (continuous_subtype_val.pow 2)).continuousAt).eventually
      (Iio_mem_nhds hstrict)
  obtain ⟨w, hwfinite, hwstrict, hwv⟩ := (hfinite.and_eventually
    ((hnear.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)).exists
  have hwv' : w.val < v.val := hwv
  have hclock : ∀ r ∈ Icc w.val v.val, t.val - r ^ 2 ∈ H.stageDomain first := by
    intro r hr
    rcases hr.2.eq_or_lt with rfl | hrv
    · exact hpast
    · apply H.mem_stageDomain_of_mem_Ioo
      have hsq := (sq_lt_sq₀ (w.property.1.trans hr.1) hv.le).mpr hrv
      have hsqw := pow_le_pow_left₀ w.property.1 hr.1 2
      exact ⟨by linarith [H.time_le_of_mem_stageDomain hpast], by linarith⟩
  have hscalar (j : H.StageInterval first last) (r : ℝ)
      (hr : r ∈ Ioo (H.regularizedStageStart t 0 j.val)
        (H.regularizedStageEnd t v.val j.val)) (x : (H.stage j.val).Carrier) :
      -B ≤ metricScalarAt (H.stageMetric j.val (t.val - r ^ 2)) x :=
    hfloor j.val _ (H.mapsTo_regularizedStage_Ioo t 0 v.val j.val hr) x
  have hwclock := hclock w.val ⟨le_rfl, hwv'.le⟩
  rw [H.regularizedSpatialCost_eq_of_mem_stageDomain t B p w first hle hwclock] at hwfinite
  have hne : (range (H.regularizedCost first last hle t B 0 w.val p)).Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn, WithTop.sInf_empty] at hwfinite
    exact hwfinite rfl
  obtain ⟨_, ⟨q, rfl⟩, hq⟩ := exists_lt_of_csInf_lt hne (lt_top_iff_ne_top.mpr hwfinite)
  obtain ⟨m, C, hLip, hm⟩ := H.exists_lipschitz_spatial_cost_minimum_on_stage
    first last hle t B 0 w.val v.val hwv'.le hupper hclock hscalar p ⟨q, ne_top_of_lt hq⟩
  rw [H.regularizedSpatialCost_eq_of_mem_stageDomain t B p v first hle hpast,
    (hm v.val ⟨hwv'.le, le_rfl⟩).1]
  exact WithTop.coe_ne_top


theorem continuousWithinAt_regularizedSpatialCost_left
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (B : ℝ)
    (p : (H.stageAt t).Carrier) (v : Icc (0 : ℝ) (Real.sqrt t.val))
    (hfloor : ∀ (j : Fin (H.eventCount + 1)) (s : ℝ), s ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j s) x) :
    ContinuousWithinAt (H.regularizedSpatialCost t B p) (Iio v) v := by
  classical
  by_cases htop : H.regularizedSpatialCost t B p v = ⊤
  · have hnot : ¬ ∃ᶠ w in 𝓝[<] v, H.regularizedSpatialCost t B p w ≠ ⊤ := by
      intro hfinite
      exact H.regularizedSpatialCost_ne_top_of_frequently_ne_top_left t B p v hfloor hfinite htop
    have hevent : ∀ᶠ w in 𝓝[<] v, H.regularizedSpatialCost t B p w = ⊤ := by
      simpa only [Filter.Frequently, not_not] using hnot
    have heq : H.regularizedSpatialCost t B p =ᶠ[𝓝[<] v] fun _ => ⊤ := by
      filter_upwards [hevent] with x hx
      exact hx
    change Tendsto (H.regularizedSpatialCost t B p) (𝓝[<] v)
      (𝓝 (H.regularizedSpatialCost t B p v))
    rw [htop]
    exact tendsto_const_nhds.congr' heq.symm
  by_cases hv : 0 < v.val
  swap
  · have hempty : Iio v = (∅ : Set (Icc (0 : ℝ) (Real.sqrt t.val))) := by
      apply eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact hv (w.property.1.trans_lt hw)
    rw [hempty]
    simp only [ContinuousWithinAt, nhdsWithin_empty, tendsto_bot]
  have hphysical : t.val - v.val ^ 2 ∈ Icc 0 H.horizon := by
    have hsq : v.val ^ 2 ≤ t.val := (Real.le_sqrt v.property.1 t.property.1).mp v.property.2
    exact ⟨sub_nonneg.mpr hsq, (sub_le_self _ (sq_nonneg _)).trans t.property.2⟩
  let s : Icc (0 : ℝ) H.horizon := ⟨t.val - v.val ^ 2, hphysical⟩
  let first := H.activeStage s
  let last := H.activeStage t
  have hle : first ≤ last := H.activeStage_mono (by
    change t.val - v.val ^ 2 ≤ t.val
    exact sub_le_self _ (sq_nonneg _))
  have hpast : t.val - v.val ^ 2 ∈ H.stageDomain first := H.activeStage_mem s
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain last := by
    simpa only [zero_pow two_ne_zero, sub_zero] using H.activeStage_mem t
  have hstrict : t.val - v.val ^ 2 < H.stageEndTime first := by
    cases hfirst : first using Fin.lastCases with
    | cast i =>
      have hpast' : t.val - v.val ^ 2 ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
        simpa only [hfirst, stageDomain, Fin.lastCases_castSucc] using hpast
      simpa only [stageEndTime_castSucc] using hpast'.2
    | last =>
      have hlast : last = Fin.last H.eventCount :=
        le_antisymm (Fin.le_last _) (by simpa only [hfirst] using hle)
      have hbound := H.le_stageEndTime_of_mem_stageDomain hupper
      rw [hlast] at hbound
      have hsquare := sq_pos_of_pos hv
      linarith
  have hnear : ∀ᶠ w : Icc (0 : ℝ) (Real.sqrt t.val) in 𝓝 v,
      t.val - w.val ^ 2 < H.stageEndTime first := by
    exact ((continuous_const.sub (continuous_subtype_val.pow 2)).continuousAt).eventually
      (Iio_mem_nhds hstrict)
  have hscalar (j : H.StageInterval first last) (r : ℝ)
      (hr : r ∈ Ioo (H.regularizedStageStart t 0 j.val)
        (H.regularizedStageEnd t v.val j.val)) (x : (H.stage j.val).Carrier) :
      -B ≤ metricScalarAt (H.stageMetric j.val (t.val - r ^ 2)) x :=
    hfloor j.val _ (H.mapsTo_regularizedStage_Ioo t 0 v.val j.val hr) x
  have hvalue := H.regularizedSpatialCost_eq_of_mem_stageDomain t B p v first hle hpast
  have hfinite := htop
  rw [hvalue] at hfinite
  have hne : (range (H.regularizedCost first last hle t B 0 v.val p)).Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn, WithTop.sInf_empty] at hfinite
    exact hfinite rfl
  obtain ⟨_, ⟨q, rfl⟩, hq⟩ := exists_lt_of_csInf_lt hne (lt_top_iff_ne_top.mpr hfinite)
  have hleft := H.tendsto_sInf_regularizedCost_left first last hle t B 0 v.val
    hv hupper hscalar p ⟨q, ne_top_of_lt hq⟩
  have hmap : Tendsto (fun w : Icc (0 : ℝ) (Real.sqrt t.val) => w.val)
      (𝓝[<] v) (𝓝[<] v.val) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hw
  have heq : H.regularizedSpatialCost t B p =ᶠ[𝓝[<] v]
      (fun w => sInf (range (H.regularizedCost first last hle t B 0 w.val p))) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwv
    apply H.regularizedSpatialCost_eq_of_mem_stageDomain t B p w first hle
    apply H.mem_stageDomain_of_mem_Ioo
    have hsq := (sq_lt_sq₀ w.property.1 hv.le).mpr (show w.val < v.val from hwv)
    exact ⟨by linarith [H.time_le_of_mem_stageDomain hpast], hw⟩
  change Tendsto (H.regularizedSpatialCost t B p) (𝓝[<] v)
    (𝓝 (H.regularizedSpatialCost t B p v))
  rw [hvalue]
  exact (hleft.comp hmap).congr' heq.symm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem lowerSemicontinuous_regularizedSpatialCost
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (B : ℝ)
    (p : (H.stageAt t).Carrier)
    (hfloor : ∀ (j : Fin (H.eventCount + 1)) (s : ℝ), s ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j s) x) :
    LowerSemicontinuous (H.regularizedSpatialCost t B p) := by
  intro v
  apply WithTop.lowerSemicontinuousAt_of_continuousWithinAt_Iic_of_monotone_add
    (H.monotone_regularizedSpatialCost_add_cubic t B p hfloor)
  · exact continuousWithinAt_Iio_iff_Iic.mp
      (H.continuousWithinAt_regularizedSpatialCost_left t B p v hfloor)
  · exact continuousAt_const.mul (continuous_subtype_val.continuousAt.pow 3)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

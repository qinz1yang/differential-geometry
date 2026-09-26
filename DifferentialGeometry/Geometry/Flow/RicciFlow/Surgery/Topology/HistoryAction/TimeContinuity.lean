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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

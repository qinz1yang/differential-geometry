import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bAssemblyV2P6HPB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ScaleSepP6SS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepNeckP6CD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CwsUniformP6SN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapWireKP6WR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10WireStayProdP6JW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NonCWPP6NC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnDefsCH2

set_option autoImplicit false

/-!
[CEILHN2：自 `P6NonCWPCHN.lean` 机械克隆]
# CHN G2b：hrecords 槽（HN ceiling）

CEIL-HN 孪生（O-CH11-CEILHN，后缀 `_CHN`）：自 `P6NonCWPP6NC.lean` 机械克隆
（生成器 `build-logs/scratch/CEILHN/gen/clone.py`），ceiling 常数换 HN 扩展。
-/

noncomputable section
open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
open Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6 p6FineEta_pos_C11GT6 epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2 BudgetCertificate_C11GT2
  SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A C1P6_C11GT6 C2P6_C11GT6
  p6X1HN_CH2 p6X2HN_CH2 p6CtimeHN_CH2 p6BadCH2_CH2 htransMBadHN_CH2)
namespace ObservedHistory
open GC.LongTime.Ch11 (p6CoarseCH2_CH2 one_le_p6CoarseCH2_CH2 p6CoarseC_le_p6CoarseCH2_CH2)

/-- **G1 `hrecords_slot_P6NC_CH2`**（PROVED，0 binder）：结论 = HP6B2 v2 `hrecords` 槽逐字（sha `af630e70…`）；
records = SCRS⁺ NOMID S14（Dcap 之后选参数），late non-CWP 由 (CWS) + (SEP′) 本族孪生证出；绕过 FOOT5 G3b。 -/
theorem hrecords_slot_P6NC_CH2 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ) :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ →
      Ctime = p6CtimeHN_CH2.{u} Γ →
      ∀ (Rrad ζ₀ B Dcap : ℝ), 0 < ζ₀ →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (T₀ : ℝ)
          (records : ∀ i' : Fin (Kh k).eventCount, T₀ ≤ (Kh k).time i'.succ →
            GeometricCutoffRecord (Kh k) i' pp),
          (∀ i' hT b, ((records i' hT).static b).hasCanonicalWindow) ∧
          Rrad ≤ pp.modelRadius ∧ 2 ≤ pp.modelOrder ∧ pp.modelAccuracy ≤ ζ₀ ∧
          T₀ ≤ (σ k : ℝ) - B / R k ∧
          ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ¬ ∃ (i' : Fin (Kh k).eventCount)
              (hT : T₀ ≤ (Kh k).time i'.succ) (hl : i'.succ ≤ (i k).castSucc)
              (Btr : BackwardPointTrace (Kh k) i'.succ (i k).castSucc hl p')
              (b : ((Kh k).event i').RetainedBoundaryIndex)
              (w : standardCapWindow pp.modelRadius),
              Btr.point i'.succ le_rfl hl = ((records i' hT).static b).window w ∧
                ‖w.val‖ < Dcap + 1 ∧
                t - (Kh k).time i'.succ ≤ 1 / 2 * (((records i' hT).static b).neck.scale)⁻¹ := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt Rrad ζ₀ B Dcap hζ₀ ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y
    R hsT has L hRdef hRpos hRr hL hsel hgood hwin hwin' hroom hradii i hi
  subst hε hC1 hC2 hCt
  obtain ⟨F₀, q₀, -, records₀, ⟨hF₀, hq₀, -⟩, -, -, ⟨-, hρanti, hδlim⟩, ⟨-, hrecent, -, -⟩,
    -, -, -, -, hNOM⟩ := id hS
  have hFF : F = F₀ := GC.LongTime.Ch11.rawSurgery_eq_of_tower_eq_C11KW (hF.trans hF₀.symm)
  subst F₀
  obtain ⟨-, hcanS, -, hTD⟩ := GC.LongTime.Ch11.outerSupply_twoLevel_C11G2 hS hfine F q₀ hF hq₀
    (GC.LongTime.Ch11.C1ceil_le_C1P6_C11GT6 p6X1HN_CH2.{u} Γ)
    (GC.LongTime.Ch11.C2ceil_le_C2P6_C11GT6 p6X2HN_CH2.{u} Γ)
    (GC.LongTime.Ch11.Ctime_le_p6CtimeHN_CH2.{u} Γ)
  -- (SEP′) 的 ceiling 侧：σ 处 `R_k ≤ c_k · ρ(c_k σ_k)⁻²`（hsel 元组 = outerSupply 元组）
  have hceil : ∀ k, R k ≤ c k * (q₀.neckRadius (c k * σ k) ^ 2)⁻¹ := fun k => by
    have h := (Kh k).ceiling_of_not_good_P6SS (nr := (q₀.rescale_P6N (c k) (hc k)).neckRadius)
      ((F.tower.history (ind k)).canonical_rescale_P6X (hc k) (hcanS (ind k)))
      ((F.tower.history (ind k)).derivative_rescale_P6X (hc k)
        (fun v z hlo hhi hR =>
          GC.LongTime.Ch11.stageDerivative_of_timeDerivativeSupply_P6X hTD (ind k) v z hlo hhi hR))
      (hsel k)
    rw [RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc k) q₀] at h
    rw [hRdef k]
    exact h
  -- (CWS) 常数：P6LL @ Θ = 1/2、C = p6Ctime Γ、D = |Dcap| + 1
  obtain ⟨cc, hcc, hLL⟩ :=
    RetainedCoreHistory.exists_scalar_lower_bound_of_cap_window_trace_late_P6LL.{u}
  obtain ⟨Cbirth, hCb, hLL2⟩ := hLL (1 / 2) (by norm_num) (by norm_num) (p6CtimeHN_CH2.{u} Γ)
  obtain ⟨Rw, -, m₀, -, ζw, δw, hζw, -, hδw, hLL3⟩ := hLL2 (|Dcap| + 1) (by positivity)
  obtain ⟨a₀, ha₀, hHI⟩ := exists_initialHI_P6WR F
  obtain ⟨εr, hεr, hεCb, hεcc, hεa⟩ := exists_eps_P6NC hCb hcc ha₀
    (q₀.neckRadius_pos 0 le_rfl)
  obtain ⟨Tδ, hTδ⟩ := Filter.eventually_atTop.mp (hδlim.eventually (ge_mem_nhds
    (lt_min hδw (div_pos one_pos (by linarith [q₀.recenterConstant_ge_four] :
      (0 : ℝ) < 2 * q₀.recenterConstant)))))
  obtain ⟨Trc, -, hrc⟩ := hrecent εr hεr
  -- records：SCRS⁺ NOMID S14 @ (max Rrad Rw, min ζ₀ ζw, max 2 m₀)，带 nominal identity
  obtain ⟨Tthr, hTthr⟩ := hNOM (max Rrad Rw) (min ζ₀ ζw) (max 2 m₀) (lt_min hζ₀ hζw)
  choose p hpδ hpρ _hpf hprc hD hacc' hord' hrec using hTthr
  choose records hlink hid using hrec
  obtain ⟨T₁, hT₁a, hT₁b⟩ : ∃ x : ℝ, Tthr ≤ x ∧ Tδ ≤ x := ⟨max Tthr Tδ, le_max_left _ _,
    le_max_right _ _⟩
  have hlate : Tendsto (fun k => c k * (σ k : ℝ)) atTop atTop :=
    tendsto_late_P6NC hc hTc hclock h1 (fun k => Subtype.coe_le_coe.mpr (has k))
  have hBR : ∀ᶠ k in atTop, B / R k ≤ 1 / 2 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * |B|)] with k hk
    rw [div_le_iff₀ (hRpos k)]
    have hR1 := hRr k
    linarith only [le_abs_self B, hR1, hk]
  filter_upwards [hlate.eventually_ge_atTop
    (max (2 * T₁) (max Trc (4 * q₀.neckRadius 0 ^ 2))), hBR] with k hk hkB
  have hσ1 : (1 : ℝ) ≤ σ k := (h1 k).trans (Subtype.coe_le_coe.mpr (has k))
  have hck := hc k
  have hk2 : 2 * T₁ ≤ c k * σ k := (le_max_left _ _).trans hk
  have hkrc : Trc ≤ c k * σ k := ((le_max_left _ _).trans (le_max_right _ _)).trans hk
  have hk4 : 4 * q₀.neckRadius 0 ^ 2 ≤ c k * σ k :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hk
  have conv : ∀ i' : Fin (Kh k).eventCount, T₁ / c k ≤ (Kh k).time i'.succ →
      Tthr ≤ (F.tower.history (ind k)).time i'.succ := fun i' hT =>
    hT₁a.trans ((div_le_div_iff_of_pos_right hck).mp hT)
  refine ⟨(p (ind k)).rescale_P6N (c k) (hc k), T₁ / c k,
    fun i' hT => (records (ind k) i' (conv i' hT)).rescale_P6M (c k) (hc k),
    fun i' hT b => ?_, (le_max_left _ _).trans (hD (ind k)),
    (le_max_left _ _).trans (hord' (ind k)), (hacc' (ind k)).trans (min_le_left _ _),
    thr_le_P6NC hck hσ1 hk2 hkB, ?_⟩
  · exact ((records (ind k) i' (conv i' hT)).static b).hasCanonicalWindow_rescale_P6M
      (GC.LongTime.Ch11.linkedCanonicalWindow_hasCanonicalWindow_C11E _
        (hlink (ind k) i' (conv i' hT) b)) (c k) (hc k)
  intro p' q' hq' hcr
  -- R(t, p′) → R_k（terminal 极限 + crossing 等距）
  have hσi : (σ k : ℝ) = (Kh k).time (i k).succ := hi k
  have hσact : (Kh k).activeStage (σ k) = (i k).succ := by
    refine le_antisymm ?_ ((Kh k).le_activeStage (σ k) (i k).succ (le_of_eq hσi.symm))
    by_contra hlt
    have h1' := (Kh k).time_strictMono (not_le.mp hlt)
    have h2' := (Kh k).activeStage_time_le (σ k)
    have h3' : ((σ k : Icc (0 : ℝ) (Kh k).horizon) : ℝ) = (σ k).1 := rfl
    linarith only [h1', h2', h3', hσi]
  have hiT : (Kh k).time (i k).succ ≤ (Tn k : ℝ) := by
    rw [← hσi]
    exact hsT k
  have h2i : (i k).succ ≤ (Kh k).activeStage (Tn k) := (Kh k).le_activeStage (Tn k) (i k).succ hiT
  have h1s : (Kh k).activeStage (aSeed k) ≤ (i k).succ := hσact ▸ (Kh k).activeStage_mono (has k)
  obtain ⟨-, hRσ, -⟩ := (Kh k).transport_at_stage_P6JW (haT k) (seedTrace k) (has k) (hsT k)
    hσact hσi (y k) q' hq' h1s h2i
  have hqR : metricScalarAt ((Kh k).event (i k)).outputMetric q' = R k := by
    rw [hRdef k, hRσ, (Kh k).stageMetric_succ_time_C11G (i k)]
  have hp : p' ∈ ((Kh k).event (i k)).incoming.terminalRegularOpen :=
    MetricCutCapEvent.RegularCrossing.mem_terminalRegularRegion _ hcr
  have hlim := ((Kh k).event (i k)).terminal.tendsto_metricScalarAt ⟨p', hp⟩
  rw [MetricCutCapEvent.RegularCrossing.scalar_eq _ (p := ⟨p', hp⟩) hcr, hqR] at hlim
  have hRk := hRpos k
  have hev1 : ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
      ((Kh k).event (i k)).incoming.flow.scalar t p' < 2 * R k :=
    hlim.eventually (gt_mem_nhds (by linarith only [hRk]))
  have hlo : max ((Kh k).time (i k).castSucc) (3 / 4 * (σ k : ℝ)) < (Kh k).time (i k).succ := by
    refine max_lt ((Kh k).time_strictMono (Fin.castSucc_lt_succ (i := i k))) ?_
    rw [← hσi]
    linarith only [hσ1]
  filter_upwards [hev1, Ioo_mem_nhdsLT hlo] with t ht2 htI
  rintro ⟨i', hT, hl, Btr, b, w, hw1, hw2, hw3⟩
  exact nonCWP_point_P6NC (hc k) hLL3 hcc hεCb hεcc hεa (records (ind k)) (records₀ (ind k))
    (hpδ (ind k)) (hpρ (ind k)) (hprc (ind k)) (hlink (ind k))
    (fun i'' hi'' => (hid (ind k) i'' hi'').1)
    ((le_max_right _ _).trans (hD (ind k))) ((le_max_right _ _).trans (hord' (ind k)))
    ((hacc' (ind k)).trans (min_le_right _ _)) hT₁a (fun s hs => hTδ s (hT₁b.trans hs)) hρanti
    (hTD.1 (ind k)) (hHI (ind k)) hσi hk4
    (fun i'' hi'' h => hrc (c k * σ k) hkrc (ind k) i'' hi'' h) (hceil k) ht2 htI i' hT hl Btr b
    w hw1 (by linarith only [le_abs_self Dcap, hw2]) hw3
end ObservedHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

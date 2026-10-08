import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HstayAnchorSlotsP6HS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HstayGuardedEnvSlotsP6HS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NonCWPP6NC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6Foot3MarginRecordsP6F5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedRecordsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SupplyRescaleP6HN

/-!
# env 形 guarded 槽 `hderivL⋆` / `hgradL⋆` 无 stay binder（HSTAY-A4 G9，后缀 `_P6HS`）

lead R14 的三情形路线在 env（SCRS⁺ 元组）上付清：
* `hsupply_of_scrs_P6HS`（PROVED）：G8 gate 定理的天花板供给 `hsupply` ⇐ SCRS⁺（同 `hrecords_slot_P6NC` 的取法）：
  `Q_k := c_k·ρ(c_k σ_k)⁻²`；先验 Dt ⇐ `outerSupply_twoLevel_C11G2` 的 TDS +
  `prefixDt_rescale_P6HN`（`t := σ_k`）；
  records = SCRS⁺ NOMID records（radius ≥ TE+11、accuracy ≤ min(ε₀, 1/2)、order ≥ 2，重标度 `rescale_P6M`）；
  `hnc` ⇐ `exists_hnc_of_records_P6SB2`；scale 分离 `max 6 (8Q) < scale`
  ⇐ recent（`η = 1/5`，nominal identity）
  + 重定心（δ → 0）+ `static_scale_ge_of_recenter_P6CD` + `R_k ≤ Q_k`（`ceiling_of_not_good_P6SS`，`hsel`）。
* `hderivLStar_slot_full_P6HS` / `hgradLStar_slot_full_P6HS`（PROVED，无 binder；选择子约束 `hCg4`）：陈述 =
  G4 `hderivLStar_slot_P6HS` / `hgradLStar_slot_P6HS` 去掉 binder `hstaySlotStar`；
  hmargin ⇐ `hmargin_slot_P6F5`，
  全事件 records ⇐ `exists_records_of_prepared_chain_CXSP`，HI ⇐ `hpin_rescaled_of_records_P6HI`。
生成：build-logs/scratch/HSTAY-A4/gen/gen8.py。
-/

set_option autoImplicit false

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
  p6X1std_C11GT6 p6X2std_C11GT6 p6Ctime_C11G7B)

namespace ObservedHistory

/-- **天花板供给 ⇐ SCRS⁺（`_P6HS`，PROVED）**：结论 = G8 gate 定理 `hderivLStar_of_anchor_threeCase_P6HS`
的 binder `hsupply` 正文（env 前缀同 `hmargin_slot_P6F5`）。 -/
theorem hsupply_of_scrs_P6HS (P : OrientedThreeStage.{u}) (g : P.Metric)
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
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
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
        ∀ᶠ k in atTop, ∃ (Q : ℝ) (pp : CutoffParameters) (T₀ : ℝ)
          (recs : ∀ e : Fin (Kh k).eventCount, T₀ ≤ (Kh k).time e.succ →
            GeometricCutoffRecord (Kh k) e pp),
          0 < Q ∧
          (∀ e : Fin (Kh k).eventCount, e.castSucc ≤ (i k).castSucc →
            ((Kh k).event e).incoming.DerivativeBoundBefore Ctime Q ((Kh k).time e.succ)) ∧
          T₀ ≤ (σ k : ℝ) - 2 / R k ∧
          (∀ e he b, ((recs e he).static b).hasCanonicalWindow) ∧
          pp.modelAccuracy ≤ 1 / 2 ∧ StandardCap.transitionEnd + 10 < pp.modelRadius ∧
          (∀ (e : Fin (Kh k).eventCount) (he : T₀ ≤ (Kh k).time e.succ)
            (w : ((Kh k).stage e.succ).Carrier),
            (∀ b, metricScalarAt ((Kh k).event e).outputMetric w <
              ((recs e he).static b).neck.scale / 2) →
            ¬ ∃ (b : ((Kh k).event e).RetainedBoundaryIndex)
              (x : standardCapWindow pp.modelRadius),
              w = ((recs e he).static b).window x ∧ ‖x.val‖ < pp.modelRadius) ∧
          (∀ (e : Fin (Kh k).eventCount) (he : T₀ ≤ (Kh k).time e.succ) b,
            (σ k : ℝ) - 2 / R k < (Kh k).time e.succ → e.succ ≤ (i k).castSucc →
            max 6 (8 * Q) < ((recs e he).static b).neck.scale) := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  subst hε hC1 hC2 hCt
  obtain ⟨F₀, q₀, -, records₀, ⟨hF₀, hq₀, -⟩, -, -, ⟨-, hρanti, hδlim⟩, ⟨-, hrecent, -, -⟩,
    -, -, -, -, hNOM⟩ := id hS
  have hFF : F = F₀ := GC.LongTime.Ch11.rawSurgery_eq_of_tower_eq_C11KW (hF.trans hF₀.symm)
  subst F₀
  obtain ⟨-, hcanS, -, hTD⟩ := GC.LongTime.Ch11.outerSupply_twoLevel_C11G2 hS hfine F q₀ hF hq₀
    (GC.LongTime.Ch11.C1ceil_le_C1P6_C11GT6 p6X1std_C11GT6.{u} Γ)
    (GC.LongTime.Ch11.C2ceil_le_C2P6_C11GT6 p6X2std_C11GT6.{u} Γ)
    (GC.LongTime.Ch11.Ctime_le_p6Ctime_C11G7B.{u} Γ)
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
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_hnc_of_records_P6SB2.{u}
  have hΛpos : 0 < q₀.recenterConstant := by linarith [q₀.recenterConstant_ge_four]
  obtain ⟨Tδ, hTδ⟩ := Filter.eventually_atTop.mp (hδlim.eventually (ge_mem_nhds
    (div_pos one_pos (by linarith : (0 : ℝ) < 2 * q₀.recenterConstant))))
  obtain ⟨Trc, -, hrc⟩ := hrecent (1 / 5) (by norm_num)
  obtain ⟨Tthr, hTthr⟩ := hNOM (StandardCap.transitionEnd + 11) (min ε₀ (1 / 2)) 2
    (lt_min hε₀ (by norm_num))
  choose p hpδ hpρ _hpf hprc hD hacc' hord' hrec using hTthr
  choose records hlink hid using hrec
  obtain ⟨T₁, hT₁a, hT₁b⟩ : ∃ x : ℝ, Tthr ≤ x ∧ Tδ ≤ x :=
    ⟨max Tthr Tδ, le_max_left _ _, le_max_right _ _⟩
  have hlate : Tendsto (fun k => c k * (σ k : ℝ)) atTop atTop :=
    tendsto_late_P6NC hc hTc hclock hone (fun k => Subtype.coe_le_coe.mpr (has k))
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRr (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  filter_upwards [hlate.eventually_ge_atTop (max (2 * T₁) Trc), hRlim.eventually_ge_atTop 4]
    with k hk hR4
  have hck := hc k
  have hRk := hRpos k
  have hσ1 : (1 : ℝ) ≤ σ k := (hone k).trans (Subtype.coe_le_coe.mpr (has k))
  have hσs : (σ k : ℝ) = (Kh k).time (i k).succ := hi k
  have hcs : (Kh k).time (i k).castSucc < (Kh k).time (i k).succ :=
    (Kh k).time_strictMono Fin.castSucc_lt_succ
  have hk2 : 2 * T₁ ≤ c k * σ k := (le_max_left _ _).trans hk
  have hkrc : Trc ≤ c k * σ k := (le_max_right _ _).trans hk
  have h2R : 2 / R k ≤ 1 / 2 := by
    rw [div_le_iff₀ hRk]
    linarith only [hR4]
  have hT₀ : T₁ / c k ≤ (σ k : ℝ) - 2 / R k := thr_le_P6NC hck hσ1 hk2 h2R
  have conv : ∀ e : Fin (Kh k).eventCount, T₁ / c k ≤ (Kh k).time e.succ →
      Tthr ≤ (F.tower.history (ind k)).time e.succ := fun e hT =>
    hT₁a.trans ((div_le_div_iff_of_pos_right hck).mp hT)
  have hρσ : 0 < q₀.neckRadius (c k * σ k) :=
    q₀.neckRadius_pos _ (mul_nonneg hck.le (by linarith only [hσ1]))
  have hQ1 : (1 : ℝ) ≤ c k * (q₀.neckRadius (c k * σ k) ^ 2)⁻¹ := by
    have e1 := hRr k
    have e2 : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith only [e1, e2, hceil k]
  obtain ⟨hES, hDB⟩ := prefixDt_rescale_P6HN hTD hρanti (ind k) hck (i k) (t := (σ k : ℝ))
    (by rw [hσs]; exact hcs) (le_of_eq hσs)
  have hcanR : ∀ (e : Fin (Kh k).eventCount) (hT : T₁ / c k ≤ (Kh k).time e.succ) b,
      (((records (ind k) e (conv e hT)).rescale_P6M (c k) hck).static b).hasCanonicalWindow :=
    fun e hT b => ((records (ind k) e (conv e hT)).static b).hasCanonicalWindow_rescale_P6M
      (GC.LongTime.Ch11.linkedCanonicalWindow_hasCanonicalWindow_C11E _
        (hlink (ind k) e (conv e hT) b)) (c k) hck
  refine ⟨c k * (q₀.neckRadius (c k * σ k) ^ 2)⁻¹, (p (ind k)).rescale_P6N (c k) hck, T₁ / c k,
    fun e hT => (records (ind k) e (conv e hT)).rescale_P6M (c k) hck, by linarith only [hQ1], ?_,
    hT₀, hcanR, (hacc' (ind k)).trans (min_le_right _ _),
    lt_of_lt_of_le (by linarith only : StandardCap.transitionEnd + 10 <
      StandardCap.transitionEnd + 11) (hD (ind k)),
    hnc0 _ ((hacc' (ind k)).trans (min_le_left _ _)) (hord' (ind k)) hcanR, ?_⟩
  · intro e he
    rcases lt_or_eq_of_le he with hlt | heq
    · exact hES e hlt
    · have hei : e = i k := Fin.castSucc_injective _ heq
      subst hei
      intro x s hs hq
      exact hDB x s ⟨hs.1, by rw [hσs]; exact hs.2⟩ hq
  · intro e he b hve he4
    have hTt := conv e he
    obtain ⟨So, hSodef⟩ : ∃ s, ((records (ind k) e hTt).static b).neck.scale = s := ⟨_, rfl⟩
    have hSS : (((records (ind k) e hTt).rescale_P6M (c k) hck).static b).neck.scale =
        c k * So := by
      rw [← hSodef]
      exact ((records (ind k) e hTt).static b).rescale_P6M_scale (c k) hck
    rw [hSS]
    have htK : (Kh k).time e.succ = (F.tower.history (ind k)).time e.succ / c k := rfl
    have hT1 : T₁ ≤ (F.tower.history (ind k)).time e.succ :=
      (div_le_div_iff_of_pos_right hck).mp he
    have hδc : (p (ind k)).recenterConstant *
        (p (ind k)).delta ((F.tower.history (ind k)).time e.succ) ≤ 1 / 2 := by
      rw [hprc, hpδ]
      have h2 := hTδ _ (hT₁b.trans hT1)
      calc q₀.recenterConstant * q₀.delta ((F.tower.history (ind k)).time e.succ)
          ≤ q₀.recenterConstant * (1 / (2 * q₀.recenterConstant)) :=
            mul_le_mul_of_nonneg_left h2 hΛpos.le
        _ = 1 / 2 := by field_simp
    have hSlo := static_scale_ge_of_recenter_P6CD (records (ind k) e hTt) hδc b
    rw [hSodef] at hSlo
    have hlo : c k * σ k / 2 ≤ (F.tower.history (ind k)).time e.succ := by
      have e1 : (σ k : ℝ) / 2 ≤ (Kh k).time e.succ := by linarith only [hve, h2R, hσ1]
      rw [htK, le_div_iff₀ hck] at e1
      linarith only [e1]
    have hhi : (F.tower.history (ind k)).time e.succ ≤ c k * σ k := by
      have e1 : (Kh k).time e.succ ≤ (Kh k).time (i k).castSucc :=
        (Kh k).time_strictMono.monotone he4
      have e2 : (Kh k).time e.succ ≤ σ k := by linarith only [e1, hcs, hσs]
      rw [htK, div_le_iff₀ hck] at e2
      linarith only [e2]
    have hnom : (records (ind k) e hTt).nominalRadius ⟨b.1.1⟩ ≤
        1 / 5 * q₀.neckRadius (c k * σ k) := by
      rw [(hid (ind k) e hTt).1]
      exact hrc (c k * σ k) hkrc (ind k) e ⟨hlo, hhi⟩ _
    have hnpos := (records (ind k) e hTt).nominal_pos ⟨b.1.1⟩
    have hkey : 9 * (q₀.neckRadius (c k * σ k) ^ 2)⁻¹ ≤ So := by
      refine le_trans ?_ hSlo
      have hq : 9 * (q₀.neckRadius (c k * σ k) ^ 2)⁻¹ =
          (q₀.neckRadius (c k * σ k) ^ 2 / 9)⁻¹ := by
        field_simp
      rw [hq]
      refine inv_anti₀ (by positivity) ?_
      nlinarith only [hnom, hnpos, hρσ]
    have hQ0 : 0 < c k * (q₀.neckRadius (c k * σ k) ^ 2)⁻¹ := by linarith only [hQ1]
    have h9 : 9 * (c k * (q₀.neckRadius (c k * σ k) ^ 2)⁻¹) ≤ c k * So := by
      nlinarith only [mul_le_mul_of_nonneg_left hkey hck.le]
    exact max_lt (by linarith only [h9, hQ1]) (by linarith only [h9, hQ0])

/-- **env 形 `hderivL⋆`，无 binder（`_P6HS`，PROVED；`hCg4`）**：陈述 = G4 `hderivLStar_slot_P6HS` 去掉
`hstaySlotStar`。 -/
theorem hderivLStar_slot_full_P6HS (P : OrientedThreeStage.{u}) (g : P.Metric)
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (Cgsel : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (hCg4 : ∀ Γ Γf, 4 ≤ Cgsel Γ Γf) :
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
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ {Cg : ℝ}, Cg = Cgsel Γ Γf →
      ∀ (T r : ℝ), 0 < T → 0 < r →
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
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            (∀ (first : Fin ((Kh k).eventCount + 1)) (hfl : first ≤ (i k).castSucc),
              ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k)),
              ∀ (B : BackwardPointTrace (Kh k) first (i k).castSucc hfl z)
                (i' : Fin (Kh k).eventCount) (hf : first ≤ i'.castSucc)
                (hij : i'.castSucc < (i k).castSucc),
              ∀ v' ∈ Ioo ((Kh k).time i'.castSucc) ((Kh k).time i'.succ), t - T / R k ≤ v' →
                Cg * R k < ((Kh k).event i').incoming.flow.scalar v'
                  (B.point i'.castSucc hf hij.le) →
                (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                  1 / (2 * max (Ctime : ℝ) 1) →
                |derivWithin (fun w' => ((Kh k).event i').incoming.flow.scalar w'
                    (B.point i'.castSucc hf hij.le)) (Iic v') v'| ≤
                  Ctime * ((Kh k).event i').incoming.flow.scalar v'
                    (B.point i'.castSucc hf hij.le) ^ 2) ∧
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                Cg * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                  1 / (2 * max (Ctime : ℝ) 1) →
                |derivWithin (fun w' => ((Kh k).event (i k)).incoming.flow.scalar w' z)
                    (Iic v') v'| ≤
                  Ctime * ((Kh k).event (i k)).incoming.flow.scalar v' z ^ 2 := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt Cg hCg
  have h4 : (4 : ℝ) ≤ Cg := hCg ▸ hCg4 Γ Γf
  have hC2' : 0 ≤ C2 := by
    rw [hC2]
    exact zero_le_one.trans (GC.LongTime.Ch11.one_le_C2P6_C11GT6 _ Γ)
  obtain ⟨params, records, -⟩ :=
    GC.LongTime.Ch11.exists_records_of_prepared_chain_CXSP T.toChain F hF q hq
  exact hderivLStar_of_anchor_threeCase_P6HS (F := F) (C1 := C1) h4 hC2' records
    (hmargin_slot_P6F5 P g εP6 hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord hε
      hC1 hC2 hCt)
    (hsupply_of_scrs_P6HS P g εP6 hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord
      hε hC1 hC2 hCt)

/-- **env 形 `hgradL⋆`，无 binder（`_P6HS`，PROVED；`hCg4`）**：陈述 = G4 `hgradLStar_slot_P6HS` 去掉
`hstaySlotStar`；`Cgrad := C2.toNNReal`。 -/
theorem hgradLStar_slot_full_P6HS (P : OrientedThreeStage.{u}) (g : P.Metric)
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (Cgsel : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (hCg4 : ∀ Γ Γf, 4 ≤ Cgsel Γ Γf) :
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
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ {Cg : ℝ}, Cg = Cgsel Γ Γf →
      ∃ Cgrad : ℝ≥0,
      ∀ (T r : ℝ), 0 < T → 0 < r →
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
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                Cg * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                  1 / (2 * max (Ctime : ℝ) 1) →
                ∀ ξ : TangentSpace ThreeModel z,
                  |scalarDifferential ((Kh k).event (i k)).incoming.flow v' z ξ| ≤
                    Cgrad * ((Kh k).event (i k)).incoming.flow.scalar v' z *
                      Real.sqrt (((Kh k).event (i k)).incoming.flow.scalar v' z) *
                      Real.sqrt
                        ((((Kh k).event (i k)).incoming.flow.base.metric v').inner z ξ ξ) := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt Cg hCg
  have h4 : (4 : ℝ) ≤ Cg := hCg ▸ hCg4 Γ Γf
  have hC2' : 0 ≤ C2 := by
    rw [hC2]
    exact zero_le_one.trans (GC.LongTime.Ch11.one_le_C2P6_C11GT6 _ Γ)
  obtain ⟨params, records, -⟩ :=
    GC.LongTime.Ch11.exists_records_of_prepared_chain_CXSP T.toChain F hF q hq
  exact ⟨C2.toNNReal, hgradLStar_of_anchor_P6HS (F := F) (C1 := C1) h4 hC2' records
    (hmargin_slot_P6F5 P g εP6 hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord hε
      hC1 hC2 hCt)⟩

/-- consumer：G9 两槽与 G4 槽同型（G4 的 `hstaySlotStar` 不再需要）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (Cgsel : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (hCg4 : ∀ Γ Γf, 4 ≤ Cgsel Γ Γf) : True := by
  have _h1 : type_of% (@hderivLStar_slot_P6HS.{u} P g εP6 Cgsel hCg4) := fun _ =>
    hderivLStar_slot_full_P6HS P g εP6 Cgsel hCg4
  have _h2 : type_of% (@hgradLStar_slot_P6HS.{u} P g εP6 Cgsel hCg4) := fun _ =>
    hgradLStar_slot_full_P6HS P g εP6 Cgsel hCg4
  trivial

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

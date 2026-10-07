import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFineTowerC11Q6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaBlockRadiusC11ND

/-!
# 块数据 + `nr(3^k) = rad(k+1)` 桥（S-CH11-DOUBLE G2 接线，后缀 `_C11ND`）

`exists_blockData_C11Q6`（FINEPACK）同证明，多交一个合取项
`∀ k, N.params.neckRadius (3^k) = rad (k+1)`（`rad m = (TW.block m).radius`，来自
`neckRadius_pow_eq_stateRadius_C11ND` ∘ `exists_surgery_with_retained_raw_caps` 的 `hpref`）。
其余 6 项与原定理逐字相同；原定理本身不改（它的 `∃ rad` 不带 nr 与 rad 的联系）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory renaming
  exists_distinct_pole_half_clock_support_with_event_local_cap_exclusion_requests_at_closed_poles
    → closedPoleSupport_C11Q6,
  exists_distinct_pole_half_clock_support_with_event_local_cap_exclusion_requests
    → ureSupport_C11Q6

namespace GC.LongTime.Ch11

universe u

/-- **块数据 + 桥**：`exists_blockData_C11Q6` 加 `N.params.neckRadius (3^k) = rad (k+1)`。 -/
theorem exists_blockData_nrBridge_C11ND (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (F : GC.Interface.RawSurgery P g)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
      (rad Df εf cap : ℕ → ℝ) (mf : ℕ → ℕ),
      (∀ m, 0 < rad m) ∧ (∀ s, 0 ≤ s → N.params.neckRadius s ≤ 1) ∧
      (∀ n (j : Fin (F.tower.history n).toHistory.eventCount), ∃ m : ℕ,
      preparedSpatialHorizon m < (F.tower.history n).toHistory.time j.succ ∧
      (F.tower.history n).toHistory.time j.succ ≤ (3 : ℝ) ^ m ∧
      N.params.delta ((F.tower.history n).toHistory.time j.succ) ≤ cap m ∧
      (∀ T ∈ Icc ((F.tower.history n).toHistory.time j.succ)
          (2 * (F.tower.history n).toHistory.time j.succ),
        rad (m + 1) ≤ N.params.neckRadius T) ∧
      (∀ A : ℝ, 0 < A → N.params.delta ((F.tower.history n).toHistory.time j.succ) <
        diagonalAccuracy_C11S N.params.delta A ((F.tower.history n).toHistory.time j.succ) →
        A < 12 * (3 : ℝ) ^ m) ∧
      ∀ b', ∃ raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap N.params.fixed
          (Df m) (mf m) (εf m) b',
        raw.hasCanonicalWindow ∧ raw.neck.scale = ((N.records n j).static b').neck.scale ∧
        ∀ z, raw.inclusion (raw.witness.cap z) =
          ((N.records n j).static b').inclusion (((N.records n j).static b').witness.cap z)) ∧
      (∀ m : ℕ,
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ Df m ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤ mf m ∧
      εf m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤
        Df (m + 1) ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤
        mf (m + 1) ∧
      εf (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1) ∧
      (∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) ∧
      (∀ m : ℕ,
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) ∧
      ∀ k : ℕ, N.params.neckRadius ((3 : ℝ) ^ k) = rad (k + 1) := by
  have hsteps := exists_blockSteps_of_astra_C11W5.{u} 1 1 one_pos one_pos 1 one_pos
  obtain ⟨Cdist, -, Γ, -, hΓ⟩ := hsteps
  have hPg := hΓ P g
  obtain ⟨pBase, prepared, hbase, hdist, hres, hstep⟩ := hPg
  have hinv := exists_inv_base_C11W Cdist 1 1 1 one_pos prepared hbase hdist hres
  obtain ⟨X₀, hX₀, hhist, hrad₀⟩ := hinv
  have hΛ : 0 < pBase.recenterConstant :=
    lt_of_lt_of_le (by norm_num) pBase.recenterConstant_ge_four
  have htower := tower_of_blockSteps_policy_C11Q6
    (fun j X ℓ req =>
      ((k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.2.1 ≤ req.Dcut ∧
        (k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.2.2 ≤ req.mcut ∧
        req.epsCut ≤ (k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.1 ∧
        req.accuracyCap ≤
          (k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).1) ∧
      ((k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime (j - 1) X.radius).2.2.1 ≤ req.Dcut ∧
        (k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime (j - 1) X.radius).2.2.2 ≤ req.mcut ∧
        req.epsCut ≤ (k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime (j - 1) X.radius).2.1 ∧
        req.accuracyCap ≤
          (k3BlockConsts_C11Q6 P g pBase.recenterConstant Γ.Ctime (j - 1) X.radius).1) ∧
      ((eventBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.1 ≤ req.Dcut ∧
        (eventBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.2.1 ≤ req.mcut ∧
        req.epsCut ≤ (eventBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).1 ∧
        req.accuracyCap ≤
          (eventBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.2.2) ∧
      ((ureBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.1 ≤ req.Dcut ∧
        (ureBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.2.1 ≤ req.mcut ∧
        req.epsCut ≤ (ureBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).1 ∧
        req.accuracyCap ≤
          (ureBlockRequest_C11Q6 P g pBase.recenterConstant Γ.Ctime j ℓ.rNext).2.2.2))
    (fun j X _ ℓ hℓ => budgetChoice_dominating_C11Q6 P g hΛ Γ.Ctime j X hℓ.rNext_pos)
    hstep X₀ hX₀ hhist hrad₀
  obtain ⟨TW, -, hQ⟩ := htower
  let W : ∀ n, PreparedSpatialStepRetention (TW.toChain.state n) (TW.toChain.state (n + 1))
      (TW.toChain.accuracy n) (1 / ((n : ℝ) + 2)) (TW.request n).epsCut (TW.request n).Dcut
      (TW.request n).mcut := fun n => Classical.choice (TW.extension n).retention
  have hraw := TW.toChain.exists_surgery_with_retained_raw_caps (fun n => (TW.inv n).distance)
    (fun n => (TW.request n).epsCut) (fun n => (TW.request n).Dcut)
    (fun n => (TW.request n).mcut) W (fun n => (TW.extension n).shift_eq)
    (fun n => (TW.extension n).offset_eq) (fun n => TW.toChain_accuracy_le_quarter n)
    (windowBarrierA₀_C11Q2 P g) (windowBarrierA₀_spec_C11Q2 P g).2.1
  obtain ⟨F, q, κ, records, hbig⟩ := hraw
  obtain ⟨⟨hW1, hdiag, -, -, hmi, -⟩, hblock⟩ := hbig
  obtain ⟨hTower, -, hStatic, -, -, hδanti, hρanti, hpref, -, hcan, hwin, -, -, hδlim, hrecent⟩ :=
    hW1
  have hP2 := timeDerivativeSupply_of_astra_C12X TW.toChain (fun n => (TW.request n).epsCut)
    (fun n => (TW.request n).Dcut) (fun n => (TW.request n).mcut) W
    (fun n => (TW.extension n).shift_eq) (fun n => (TW.extension n).offset_eq) F hTower q hρanti
    (fun v hv => (hdiag v hv).2)
  let N := nativeDataOfSupplies_C11KD F q records Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ)
    Γ.Ctime hρanti hδanti hδlim (canonicalConstantsSupply_of_closedBirthConstants_C11A Γ) hwin
    hcan hP2 hrecent
  have hrc : N.params.recenterConstant = pBase.recenterConstant := hStatic.2.2.2.2
  refine ⟨F, N, fun m => (TW.block m).radius, fun m => (W m).fineParameters.modelRadius,
    fun m => (W m).fineParameters.modelAccuracy, fun m => TW.accuracy m,
    fun m => (W m).fineParameters.modelOrder, fun m => (TW.block m).radius_pos, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro s hs
    have h0 : q.neckRadius 0 ≤ 1 := by
      calc q.neckRadius 0 = (TW.toChain.observation 0).parameters.neckRadius 0 :=
            (hpref 0 0 ⟨le_rfl, by norm_num⟩).2.1
        _ = (TW.toChain.state 1).parameters.neckRadius 0 := rfl
        _ = (TW.toChain.state 0).parameters.neckRadius 0 :=
            ((TW.toChain.successor 0).parameters_past 0
              (by norm_num [preparedSpatialHorizon])).2.1
        _ = (TW.toChain.state 0).radius :=
            (TW.toChain.state 0).radius_after 0 (by norm_num [preparedSpatialHorizon])
        _ ≤ 1 := TW.toChain.initial_radius_le
    exact (hρanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs).trans h0
  · intro n j
    have hb := hblock n j
    obtain ⟨m, -, i, -, -, -, htime, hIoc, -, hδ, -, -, -, hrawc⟩ := hb
    have htime' : (F.tower.history n).toHistory.time j.succ =
        (TW.toChain.state (m + 1)).native.time i.succ + (TW.toChain.state (m + 1)).shift := htime
    have hmi' := hmi m i
    obtain ⟨-, -, -, hnrT, hAg, -⟩ := hmi'
    refine ⟨m, hIoc.1, hIoc.2, hδ.le, ?_, ?_, ?_⟩
    · intro T hT
      rw [htime'] at hT
      exact hnrT T hT
    · intro A hA hlt
      rw [htime'] at hlt
      refine hAg A hA ?_
      rw [diagonalLargerBallAccuracy_eq_C11Q6 TW.toChain q (fun t ht => (hdiag t ht).1)]
      exact hlt
    · intro b'
      have hr := hrawc b'
      obtain ⟨b, raw, -, hcanr, -, -, -, -, -, -, -, -, -, -, -, -, hsc, hcap, -⟩ := hr
      exact ⟨raw, hcanr, hsc, hcap⟩
  · intro m
    have hrN : (TW.block (m + 1)).radius = (TW.lookahead m).rNext := (TW.extension m).radius_eq
    have hcap0 : TW.accuracy m ≤ (TW.request m).accuracyCap := (TW.extension m).accuracy_le_cap
    have hcap1 : TW.accuracy (m + 1) ≤ (TW.request (m + 1)).accuracyCap :=
      (TW.extension (m + 1)).accuracy_le_cap
    have hQm := hQ m
    have hQm1 := hQ (m + 1)
    obtain ⟨⟨a1, a2, a3, a4⟩, -, -, -⟩ := hQm
    obtain ⟨-, ⟨b1, b2, b3, b4⟩, -, -⟩ := hQm1
    beta_reduce
    rw [hrc, hrN]
    rw [hrN] at b1 b2 b3 b4
    exact ⟨a1.trans (W m).fine_radius, a2.trans (W m).fine_order, (W m).fine_accuracy.trans a3,
      hcap0.trans a4, b1.trans (W (m + 1)).fine_radius, b2.trans (W (m + 1)).fine_order,
      (W (m + 1)).fine_accuracy.trans b3, hcap1.trans b4⟩
  · intro m
    have hrN : (TW.block (m + 1)).radius = (TW.lookahead m).rNext := (TW.extension m).radius_eq
    have hcap0 : TW.accuracy m ≤ (TW.request m).accuracyCap := (TW.extension m).accuracy_le_cap
    have hQm := hQ m
    obtain ⟨-, -, ⟨a1, a2, a3, a4⟩, -⟩ := hQm
    beta_reduce
    rw [hrc, hrN]
    exact ⟨a1.trans (W m).fine_radius, a2.trans (W m).fine_order, (W m).fine_accuracy.trans a3,
      hcap0.trans a4⟩
  · intro m
    have hrN : (TW.block (m + 1)).radius = (TW.lookahead m).rNext := (TW.extension m).radius_eq
    have hcap0 : TW.accuracy m ≤ (TW.request m).accuracyCap := (TW.extension m).accuracy_le_cap
    have hQm := hQ m
    obtain ⟨-, -, -, ⟨a1, a2, a3, a4⟩⟩ := hQm
    beta_reduce
    rw [hrc, hrN]
    exact ⟨a1.trans (W m).fine_radius, a2.trans (W m).fine_order, (W m).fine_accuracy.trans a3,
      hcap0.trans a4⟩
  · intro k
    exact neckRadius_pow_eq_stateRadius_C11ND TW.toChain q (fun n t ht => (hpref n t ht).2.1) k


end GC.LongTime.Ch11

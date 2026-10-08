import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnotP5LSeqP6HN

/-!
# final 帧 (CWW) hnotK：坏点在 final slab（O-CH11-HNOT-LOCALDT / HNOT-A3 G9，后缀 `_P6HN`）

A12′ 顶层 `hgapJF` / `hgapJF8` 槽结论里的 cap-window 合取项是 final 帧形：坏点 `σ n` 在 final slab
（`time last < σ < horizon`），trace 终点 stage `Fin.last`，`HEq (y n) yG'`，年龄 `≤ (1 − 1/(n+2))/scale`，
窗口 `‖x‖ < n + 2`。本文件给它的 (CWW) producer：
* 时间半 ⇐ G1 `capWindow_trace_localDt_P6HN`（`k := Fin.last`、`Gk := (finalSlab _).restrictIncoming …`、
  `final_initial`）；Dt 前提取槽结论自带的截断形 (D1)(D2)（终点 `min … Tn`，`σ ≤ Tn`）；
* witness ⇐ G7 `capWindow_trace_spatialWitness_P6HN`（同一 `Gk`）；
* `hsel`（`¬ HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ n) (y n)`）是槽自身前提。
diagonal 参数（`Cb Rn ζ δ₀ m₀`）落在 `1/(n+1)²`、`n+1`、`1/(n+1)`、`1/(n+1)`、`n+2` 档之内（与
`P6FinalCondP6FCCws` 同形），HI 常数 `a₀ n` 逐 `n`（重标度帧 `a₀/c n`）。
常数约束：`Cs ≤ C1`、`Cs ≤ C2`、`Ctime₀ ≤ Ctime`（`Cs, Ctime₀` 只依赖 `ε`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

/-- final stage 度量 = final slab（restrictIncoming）度量（`_P6HN`）。 -/
theorem stageMetric_last_eq_P6HN (K : RetainedCoreHistory.{u})
    (hK : K.time (Fin.last K.eventCount) < K.horizon) (v : ℝ) :
    K.toHistory.stageMetric (Fin.last K.eventCount) v =
      ((K.finalSlab hK).restrictIncoming le_rfl hK le_rfl).flow.base.metric v := by
  rw [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_left hK]
  rfl

/-- final slab witness ⇒ `stageMetric m` 形（`m = Fin.last`，`HEq z zG`；`_P6HN`）。 -/
theorem spatialWitness_stage_of_final_P6HN (K : RetainedCoreHistory.{u})
    (hK : K.time (Fin.last K.eventCount) < K.horizon) {m : Fin (K.eventCount + 1)}
    (hm : Fin.last K.eventCount = m) (v : ℝ) (z : (K.stage m).Carrier)
    (zG : (K.stage (Fin.last K.eventCount)).Carrier) (hz : HEq z zG) {ε C1 C2 : ℝ}
    (h : ∃ W : SpatialCanonicalWitness
      (((K.finalSlab hK).restrictIncoming le_rfl hK le_rfl).flow.base.metric v) ε C1 C2 zG,
      W.capTubeHasNeckChart ε) :
    ∃ W : SpatialCanonicalWitness (K.toHistory.stageMetric m v) ε C1 C2 z,
      W.capTubeHasNeckChart ε := by
  subst hm
  obtain rfl := eq_of_heq hz
  rw [K.stageMetric_last_eq_P6HN hK]
  exact h

/-- final slab 点态 Dt ⇒ `stageMetric m` 形（`_P6HN`）。 -/
theorem stageDerivative_of_final_P6HN (K : RetainedCoreHistory.{u})
    (hK : K.time (Fin.last K.eventCount) < K.horizon) {m : Fin (K.eventCount + 1)}
    (hm : Fin.last K.eventCount = m) (v : ℝ) (z : (K.stage m).Carrier)
    (zG : (K.stage (Fin.last K.eventCount)).Carrier) (hz : HEq z zG) {Ct : ℝ}
    (h : |derivWithin (fun s => ((K.finalSlab hK).restrictIncoming le_rfl hK le_rfl).flow.scalar
        s zG) (Iic v) v| ≤
      Ct * ((K.finalSlab hK).restrictIncoming le_rfl hK le_rfl).flow.scalar v zG ^ 2) :
    |derivWithin (fun t => metricScalarAt (K.toHistory.stageMetric m t) z) (Iic v) v| ≤
      Ct * metricScalarAt (K.toHistory.stageMetric m v) z ^ 2 := by
  subst hm
  obtain rfl := eq_of_heq hz
  have hfun : ∀ t, metricScalarAt (K.toHistory.stageMetric (Fin.last K.eventCount) t) z =
      ((K.finalSlab hK).restrictIncoming le_rfl hK le_rfl).flow.scalar t z := fun t => by
    rw [K.stageMetric_last_eq_P6HN hK]
    rfl
  simp only [hfun]
  exact h

/-- **final 帧 (CWW) hnotK（`_P6HN`，PROVED）**：见文件头。结论 = `hgapJF` 槽 cap-window 合取项的形
（`Kh n := (K n).toHistory`，年龄 `1 − 1/(n+2)`，`‖x‖ < n+2`）。 -/
theorem hnotK_final_cww_P6HN {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (Ctime₀ : ℝ≥0) (Cs : ℝ), 0 < Ctime₀ ∧ 1 ≤ Cs ∧ ∀ C : ℝ≥0,
    ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, 0 < δ₀ n ∧ δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
    ∀ {C1 C2 : ℝ} {Ctime : ℝ≥0}, Cs ≤ C1 → Cs ≤ C2 → Ctime₀ ≤ Ctime →
    ∀ {K : ℕ → RetainedCoreHistory.{u}} {Tn : ℕ → ℝ}
      (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier),
      (∀ n, (K n).time (Fin.last (K n).eventCount) < (σ n : ℝ) ∧
        (σ n : ℝ) < (K n).horizon) → (∀ n, (σ n : ℝ) ≤ Tn n) →
    ∀ {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)},
      (∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) → ∀ {a₀ : ℕ → ℝ},
      (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ δ₀ n) →
      (∀ n, (p n).modelAccuracy ≤ ζ n) → (∀ n, Rn n ≤ (p n).modelRadius) →
      (∀ n, m₀ n ≤ (p n).modelOrder) → (∀ n, 0 < Q n) →
      (∀ n (j : Fin (K n).eventCount),
        ((K n).toHistory.event j).incoming.DerivativeBoundBefore C (Q n)
          (min ((K n).time j.succ) (Tn n))) →
      (∀ n (hK : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
        (((K n).finalSlab hK).restrictIncoming le_rfl hK le_rfl).DerivativeBoundBefore
          C (Q n) (min (K n).horizon (Tn n))) →
      (∀ n i hi b, Q n ≤ Cb n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n, ¬ (K n).toHistory.HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ n) (y n)) →
    ∀ (n : ℕ) (yG' : ((K n).stage (Fin.last (K n).eventCount)).Carrier), HEq (y n) yG' →
      ¬ (∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ Fin.last (K n).eventCount)
        (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl yG')
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹) := by
  obtain ⟨Ct₀, hCt₀, hDt⟩ := capWindow_trace_localDt_P6HN.{u}
  obtain ⟨Cs, hCs, hWit⟩ := capWindow_trace_spatialWitness_P6HN.{u} hε hε'
  refine ⟨Ct₀, Cs, hCt₀, hCs, fun C => ?_⟩
  have hθ0 : ∀ n : ℕ, 0 < 1 - 1 / ((n : ℝ) + 2) := fun n => by
    have : (1 : ℝ) / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  have hθ1 : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) < 1 := fun n => by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  choose Cw hCw hW2 using fun n : ℕ => hWit _ (hθ0 n) (hθ1 n) C
  choose Rw hRw mw _hmw ζw δw hζw hδw hW4 using fun n : ℕ => hW2 n ((n : ℝ) + 1) (by positivity)
  choose Cd hCd hD2 using fun n : ℕ => hDt C _ (hθ1 n)
  choose Rd md hRd ζd δd hζd hδd hD4 using fun n : ℕ => hD2 n ((n : ℝ) + 1) (by positivity)
  refine ⟨fun n => min (min (Cw n) (Cd n)) (1 / ((n : ℝ) + 1) ^ 2),
    fun n => max (max (Rw n) (Rd n)) ((n : ℝ) + 1),
    fun n => min (min (ζw n) (ζd n)) (1 / ((n : ℝ) + 1)),
    fun n => min (min (δw n) (δd n)) (1 / ((n : ℝ) + 1)),
    fun n => max (max (mw n) (md n)) (n + 2),
    fun n => ⟨lt_min (lt_min (hCw n) (hCd n)) (by positivity), min_le_right _ _⟩,
    fun n => ⟨lt_min (lt_min (hζw n) (hζd n)) (by positivity), min_le_right _ _⟩,
    fun n => ⟨lt_min (lt_min (hδw n) (hδd n)) (by positivity), min_le_right _ _⟩,
    fun n => le_max_right _ _, fun n => le_max_right _ _, ?_⟩
  intro C1 C2 Ctime hC1 hC2 hCt K Tn σ y hfin hσT Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF
    hacc hrad hord hQ hD1 hDF hbirth hbirthA hsel n yG' hyG ⟨i, hi, hl, A, b, x, hx, hxn, hage⟩
  have hK : (K n).time (Fin.last (K n).eventCount) < (K n).horizon :=
    (hfin n).1.trans (hfin n).2
  set G := ((K n).finalSlab hK).restrictIncoming le_rfl hK le_rfl with hGdef
  have hGi : G.flow.base.metric ((K n).time (Fin.last (K n).eventCount)) =
      (K n).initialMetric (Fin.last (K n).eventCount) := (K n).final_initial hK
  have hder : (K n).EventSlabsDerivative C (Q n) (Fin.last (K n).eventCount) := by
    intro j _
    have hjl : (K n).time j.succ ≤ (K n).time (Fin.last (K n).eventCount) :=
      (K n).time_strictMono.monotone (Fin.le_last _)
    have h := hD1 n j
    rwa [min_eq_left (hjl.trans ((hfin n).1.le.trans (hσT n)))] at h
  have hcur : G.DerivativeBoundBefore C (Q n) (σ n) :=
    G.derivativeBoundBefore_mono (le_min (hfin n).2.le (hσT n)) (hDF n hK)
  set q := ((recordsK n i hi).static b).neck.scale with hqdef
  have hq : 0 < q := ((recordsK n i hi).static b).neck.scale_pos
  have hbw : Q n ≤ Cw n * q := (hbirth n i hi b).trans (mul_le_mul_of_nonneg_right
    ((min_le_left _ _).trans (min_le_left _ _)) hq.le)
  have hbd : Q n ≤ Cd n * q := (hbirth n i hi b).trans (mul_le_mul_of_nonneg_right
    ((min_le_left _ _).trans (min_le_right _ _)) hq.le)
  have hW := hW4 n (K n) (recordsK n) (hcanK n)
    (((le_max_left _ _).trans (le_max_left _ _)).trans (hrad n))
    (((le_max_left _ _).trans (le_max_left _ _)).trans (hord n))
    ((hacc n).trans ((min_le_left _ _).trans (min_le_left _ _))) (recordsF n) _ (hδF n)
    ((min_le_left _ _).trans (min_le_left _ _)) (Q n) (a₀ n) _ (hQ n) le_rfl
    (fun x => (hHI n x).1) (fun x => (hHI n x).2) (Fin.last (K n).eventCount) (K n).horizon G
    hGi hder (σ n) (hfin n).1 (hfin n).2 hcur i hi hl yG' A b x hx hage hxn hbw
    (hbirthA n i hi b) C1 C2 hC1 hC2
  have hD := (hD4 n (K n) (recordsK n) (hcanK n)
    (((le_max_right _ _).trans (le_max_left _ _)).trans (hrad n))
    (((le_max_right _ _).trans (le_max_left _ _)).trans (hord n))
    ((hacc n).trans ((min_le_left _ _).trans (min_le_right _ _))) (recordsF n) _
    (fun i' hi' => (hδF n i' hi').trans ((min_le_left _ _).trans (min_le_right _ _))) le_rfl
    (Q n) (a₀ n) (hQ n) (fun x => (hHI n x).1) (fun x => (hHI n x).2)
    (Fin.last (K n).eventCount) (K n).horizon G hGi hder (σ n) (hfin n).1 (hfin n).2 hcur i hi
    hl yG' A b x hx hage hxn hbd (hbirthA n i hi b)).1
  have hact : (K n).toHistory.activeStage (σ n) = Fin.last (K n).eventCount :=
    le_antisymm (Fin.le_last _) ((K n).toHistory.le_activeStage (σ n) _ (hfin n).1.le)
  apply hsel n
  refine ⟨(K n).spatialWitness_stage_of_final_P6HN hK hact.symm (σ n) (y n) yG' hyG hW,
    fun _ _ => ?_⟩
  refine (K n).stageDerivative_of_final_P6HN hK hact.symm (σ n) (y n) yG' hyG
    (hD.trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hCt) (sq_nonneg _)))

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

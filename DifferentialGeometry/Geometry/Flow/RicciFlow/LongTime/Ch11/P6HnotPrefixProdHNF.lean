import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnotPrefixHNF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HcwwSeqP6HN

/-!
# HNOTF G2：J10ResE_DJ 的 `hnot` 项 ⇐ HNOT θ n 形 hnotK producer（`_HNF`）

* `hnotK_seq_a0_HNF`（PROVED 组合）：HNOT G7 `hnotK_of_capWindow_seq_P6HN` 的孪生，唯一改动
  HI 常数 `a₀ : ℕ → ℝ` 逐 `n`（DrvResE 给 `a₀K n`；底层 G1 `capWindow_trace_localDt_P6HN` 与 G7
  `capWindow_trace_spatialWitness_P6HN` 本就逐实例取 `a₀`），并以 `σ` 直接作坏点时刻。
  `Ctime₀`、`Cs` 只依赖 `ε`，在 `C, θ` 之前；`Cb Rn ζ δ₀ m₀` 只依赖 `(C, θ)`。
* **`hnot_prefix_J10_HNF`**：`θ n := 1 − 1/(n+2)`、`D n := n + 1`，前缀 Dt ⇐ 全 slab
  `EventSlabsDerivative … (Fin.last _)`，birth 两条以 **∀ᶠ** 形进入，经 T₀ 有限前段抬高
  （`raiseT0_HNF`）变 ∀，结论 = `J10ResE_DJ` 的 `hnot` 项逐字（prefix 帧、records :=
  `prefixLateRecords_P6N` ∘ `raiseRecords_HNF`）。PROVISIONAL 前提见各前提行（hsel 常数约束、
  records 对角档 `ζ Rn m₀ δ₀`、birth 因子 `Cb`）。
无新顶层 binder；不假设 `hqR`。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

/-- **G7 孪生，`a₀` 逐 `n`（`_HNF`，PROVED 组合）**：θ n 形 hnotK（K 帧，`‖x‖ < n + 2`）。 -/
theorem hnotK_seq_a0_HNF {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (Ctime₀ : ℝ≥0) (Cs : ℝ), 0 < Ctime₀ ∧ 1 ≤ Cs ∧
    ∀ (C : ℝ≥0) {θ : ℕ → ℝ}, (∀ n, θ n < 1) →
    ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n) ∧ (∀ n : ℕ, ((n : ℝ) + 1) + 1 < Rn n) ∧ (∀ n, 0 < ζ n) ∧
      (∀ n, 0 < δ₀ n) ∧
    ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, Cs ≤ C1' → Cs ≤ C2' → Ctime₀ ≤ Ctime' →
    ∀ {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount}
      (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon),
      (∀ n, (K n).time (j n).castSucc < (σ n : ℝ)) → (∀ n, (σ n : ℝ) < (K n).time (j n).succ) →
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
      (∀ n, (K n).EventSlabsDerivative C (Q n) (j n).castSucc) →
      (∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore C (Q n) (σ n)) →
      (∀ n i hi b, i.succ ≤ (j n).castSucc →
        (σ n : ℝ) - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        Q n ≤ Cb n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, i.succ ≤ (j n).castSucc →
        (σ n : ℝ) - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
    ∀ (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}, (∀ n, HEq (y n) (yG n)) →
      (∀ n, ¬ (K n).toHistory.HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
    ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  obtain ⟨Ct₀, hCt₀, hDt⟩ := capWindow_trace_localDt_P6HN.{u}
  obtain ⟨Cs, hCs, hWit⟩ := capWindow_trace_spatialWitness_P6HN.{u} hε hε'
  refine ⟨Ct₀, Cs, hCt₀, hCs, fun C θ hθ => ?_⟩
  have hΘ0 : ∀ n, 0 < max (θ n) (1 / 2) := fun n =>
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hΘ1 : ∀ n, max (θ n) (1 / 2) < 1 := fun n => max_lt (hθ n) (by norm_num)
  choose Cw hCw hW2 using fun n : ℕ => hWit _ (hΘ0 n) (hΘ1 n) C
  choose Rw hRw mw _hmw ζw δw hζw hδw hW4 using fun n : ℕ => hW2 n ((n : ℝ) + 1) (by positivity)
  choose Cd hCd hD2 using fun n : ℕ => hDt C (θ n) (hθ n)
  choose Rd md hRd ζd δd hζd hδd hD4 using fun n : ℕ => hD2 n ((n : ℝ) + 1) (by positivity)
  refine ⟨fun n => min (Cw n) (Cd n), fun n => max (Rw n) (Rd n), fun n => min (ζw n) (ζd n),
    fun n => min (δw n) (δd n), fun n => max (mw n) (md n), fun n => lt_min (hCw n) (hCd n),
    fun n => (hRw n).trans_le (le_max_left _ _), fun n => lt_min (hζw n) (hζd n),
    fun n => lt_min (hδw n) (hδd n), ?_⟩
  intro C1' C2' Ctime' hC1 hC2 hCt K j σ hjt htj Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF
    hacc hrad hord hQ hder hcur hbirth hbirthA y yG hyG hsel n ⟨i, hi, hl, A, b, x, hx, hxn, hage⟩
  have hq : 0 < ((recordsK n i hi).static b).neck.scale :=
    ((recordsK n i hi).static b).neck.scale_pos
  have hbw : Q n ≤ Cw n * ((recordsK n i hi).static b).neck.scale :=
    (hbirth n i hi b hl hage).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hq.le)
  have hbd : Q n ≤ Cd n * ((recordsK n i hi).static b).neck.scale :=
    (hbirth n i hi b hl hage).trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hq.le)
  have hW := hW4 n (K n) (recordsK n) (hcanK n) ((le_max_left _ _).trans (hrad n))
    ((le_max_left _ _).trans (hord n)) ((hacc n).trans (min_le_left _ _)) (recordsF n) _
    (hδF n) (min_le_left _ _) (Q n) (a₀ n) (θ n) (hQ n) (le_max_left _ _)
    (fun x => (hHI n x).1) (fun x => (hHI n x).2) (j n).castSucc ((K n).time (j n).succ)
    ((K n).toHistory.event (j n)).incoming ((K n).event_initial (j n)) (hder n) (σ n) (hjt n)
    (htj n) (hcur n) i hi hl (yG n) A b x hx hage hxn hbw (hbirthA n i hi b hl hage) C1' C2' hC1
    hC2
  have hD := (hD4 n (K n) (recordsK n) (hcanK n) ((le_max_right _ _).trans (hrad n))
    ((le_max_right _ _).trans (hord n)) ((hacc n).trans (min_le_right _ _)) (recordsF n) _
    (hδF n) (min_le_right _ _) (Q n) (a₀ n) (hQ n) (fun x => (hHI n x).1)
    (fun x => (hHI n x).2) (j n).castSucc ((K n).time (j n).succ)
    ((K n).toHistory.event (j n)).incoming ((K n).event_initial (j n)) (hder n) (σ n) (hjt n)
    (htj n) (hcur n) i hi hl (yG n) A b x hx hage hxn hbd (hbirthA n i hi b hl hage)).1
  have hact : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6X (j n) (σ n) (hjt n).le (htj n)
  apply hsel n
  refine ⟨(K n).spatialWitness_stage_of_incoming_P6HN (j n) hact.symm (σ n) (y n) (yG n) (hyG n)
    hW, fun _ _ => ?_⟩
  exact (K n).stageDerivative_at_of_incoming_P6HN (j n) hact.symm (σ n) (y n) (yG n) (hyG n)
    (hD.trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hCt) (sq_nonneg _)))

/-- **J10 `hnot` 项 producer（`_HNF`）**：`θcap n := 1 − 1/(n+2)`、`D n := n + 1`、records :=
`prefixLateRecords_P6N (j n).castSucc (raiseRecords_HNF N recordsK n)`、阈值 `raiseT0_HNF K T₀ N`
（与 `T₀` 尾相等）。前缀 Dt ⇐ 全 slab Dt；birth 两条 ∀ᶠ（无条件形）。结论 = `J10ResE_DJ` 的
`hnot` 项（`H n := (K n).prefixAt (j n).castSucc`、`y := yG`、`t := σ`）逐字。 -/
theorem hnot_prefix_J10_HNF {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (Ctime₀ : ℝ≥0) (Cs : ℝ), 0 < Ctime₀ ∧ 1 ≤ Cs ∧ ∀ C : ℝ≥0,
    ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n) ∧ (∀ n : ℕ, ((n : ℝ) + 1) + 1 < Rn n) ∧ (∀ n, 0 < ζ n) ∧
      (∀ n, 0 < δ₀ n) ∧
    ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, Cs ≤ C1' → Cs ≤ C2' → Ctime₀ ≤ Ctime' →
    ∀ {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount}
      (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon),
      (∀ n, (K n).time (j n).castSucc < (σ n : ℝ)) → (∀ n, (σ n : ℝ) < (K n).time (j n).succ) →
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
      (∀ n, (K n).EventSlabsDerivative C (Q n) (Fin.last (K n).eventCount)) →
      (∀ᶠ n in atTop, ∀ i hi b, Q n ≤ Cb n * ((recordsK n i hi).static b).neck.scale ∧
        1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
    ∀ (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}, (∀ n, HEq (y n) (yG n)) →
      (∀ n, ¬ (K n).toHistory.HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
    ∃ N : ℕ, ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : raiseT0_HNF K T₀ N n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = (((K n).prefixLateRecords_P6N (j n).castSucc
          (raiseRecords_HNF N recordsK n) i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        (σ n : ℝ) - ((K n).prefixAt (j n).castSucc).time i.succ ≤ (1 - 1 / ((n : ℝ) + 2)) *
          ((((K n).prefixLateRecords_P6N (j n).castSucc
            (raiseRecords_HNF N recordsK n) i hi).static b).neck.scale)⁻¹ := by
  obtain ⟨Ct₀, Cs, hCt₀, hCs, hall⟩ := hnotK_seq_a0_HNF.{u} hε hε'
  refine ⟨Ct₀, Cs, hCt₀, hCs, fun C => ?_⟩
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hRn, hζ, hδ, h⟩ :=
    hall C (θ := fun n => 1 - 1 / ((n : ℝ) + 2)) thetaCap_lt_one_HNF
  refine ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hRn, hζ, hδ, ?_⟩
  intro C1' C2' Ctime' hC1 hC2 hCt K j σ hjt htj Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF
    hacc hrad hord hQ hslab hbirth y yG hyG hsel
  obtain ⟨N, hN⟩ := forall_raise_of_eventually_HNF (K := K) (T₀ := T₀)
    (fun n i hi => ∀ b, Q n ≤ Cb n * ((recordsK n i hi).static b).neck.scale ∧
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) hbirth
  refine ⟨N, ?_⟩
  have hnotK := h (T₀ := raiseT0_HNF K T₀ N) (recordsK := raiseRecords_HNF N recordsK) hC1 hC2
    hCt σ hjt htj recordsF hHI (fun n i hi b => hcanK n i _ b)
    (fun n i hi => hδF n i ((le_raiseT0_HNF K T₀ N n).trans hi)) hacc hrad hord hQ
    (fun n => ((K n).prefixDt_of_lastDt_HNF (j n) (hslab n) le_rfl).1)
    (fun n => ((K n).prefixDt_of_lastDt_HNF (j n) (hslab n) (htj n).le).2)
    (fun n i hi b _ _ => (hN n i hi b).1) (fun n i hi b _ _ => (hN n i hi b).2) y hyG hsel
  exact hnot_prefix_of_hnotK_HNF (t := fun n => (σ n : ℝ)) (θ := fun n => 1 - 1 / ((n : ℝ) + 2))
    (D := fun n => (n : ℝ) + 1) j (raiseRecords_HNF N recordsK) yG (fun _ => le_rfl)
    (fun _ => le_rfl) hnotK

end RetainedCoreHistory

open RetainedCoreHistory

/-- consumer（`_HNF`）：`hnot_prefix_J10_HNF` 的结论按 `J10ResE_DJ`（P6DrvResJ10DJ:118–126）`hnot` 项的
`let` 形逐字（`H`、`t`、`y` 为 let；`records := prefixLateRecords_P6N ∘ raiseRecords_HNF`、
`T₀ := raiseT0_HNF`、`D n := n + 1`、`θcap n := 1 − 1/(n+2)`）重述。 -/
example {K : ℕ → RetainedCoreHistory.{0}} (j : ∀ n, Fin (K n).eventCount)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) {p : ℕ → CutoffParameters} {T₀ : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (N : ℕ)
    (h : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : raiseT0_HNF K T₀ N n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = (((K n).prefixLateRecords_P6N (j n).castSucc
          (raiseRecords_HNF N recordsK n) i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        (σ n : ℝ) - ((K n).prefixAt (j n).castSucc).time i.succ ≤ (1 - 1 / ((n : ℝ) + 2)) *
          ((((K n).prefixLateRecords_P6N (j n).castSucc
            (raiseRecords_HNF N recordsK n) i hi).static b).neck.scale)⁻¹) :
    let H : ℕ → RetainedCoreHistory.{0} := fun n => (K n).prefixAt (j n).castSucc
    let t : ℕ → ℝ := fun n => (σ n : ℝ)
    let y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier := yG
    let T₀' : ℕ → ℝ := raiseT0_HNF K T₀ N
    let D : ℕ → ℝ := fun n => (n : ℝ) + 1
    let θcap : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
    let records : ∀ n (i : Fin (H n).eventCount), T₀' n ≤ (H n).time i.succ →
        GeometricCutoffRecord (H n).toHistory i (p n) :=
      fun n => (K n).prefixLateRecords_P6N (j n).castSucc (raiseRecords_HNF N recordsK n)
    (∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) ∧ (∀ n : ℕ, (n : ℝ) + 1 ≤ D n) ∧
    ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀' n ≤ (H n).time j.succ)
        (hl : j.succ ≤ Fin.last (H n).eventCount)
        (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
        (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹ :=
  ⟨fun _ => le_rfl, fun _ => le_rfl, h⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.HsmallAssemblyLateC11V3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PinchingP6A
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues

set_option autoImplicit false

/-!
# S-CH11-SMALLVOL3 G3：晚期 Hamilton–Ivey ⇒ `|Rm| ≤ C·R`，discharge 晚期 `hcomp`（`_C11V3`，GAP-1′）

* `metricScalar_eq_two_mul_sum_ordered_C11V3`（metric 级 `R = 2 Σ k_i`，经 trace-normalized 矩阵）；
* `sqrt_normSq_le_of_HI_C11V3`（点态）：`InFixedHamiltonIveyRegion g a x`（`a > 0`）⇒
  `√(normSq0S g x 4 Rm) ≤ 2√3 · (3/2 |R| + e⁴/a)`。正交基下 `k₀ ≥ k₁ ≥ k₂`，HI 区给
  `0 ≤ 2k₂ ∨ X(log(aX) − 3) ≤ R`（`X = −2k₂`）；`aX ≥ e⁴` 时 `X ≤ R`，否则 `X < e⁴/a`，两种都有
  `k₀ ≤ 3|R|/2 + e⁴/a`、`k₂ ≥ −(…)`，再用
  `sqrt_normSq0S_le_of_abs_orderedSectionalCurvaturesAt_le`；
* `hcomp_late_of_HI_C11V3`：HI（年龄 `c + t`）+ `-3/(t + c') ≤ R` + `nr ≤ M` ⇒ 晚期
  `s⁻² ≤ 2500·R`（实得 `≤ 8R`）：`R ≤ 0` 时 `s⁻² ≤ K/2 < K = 2500/M² ≤ s⁻²` 矛盾；
* `localKappaWindow_zero_of_narrowTuple_HI_C11V3` + consumer：narrow tuple + 晚期 HI 起步，**不再有显式
  `hcomp`**，喂 `tracedKappa_of_window_P6B`。
-/

noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

/-- metric 级 `R = 2 Σ ordered sectional`（trace-normalized 矩阵 trace = scalar，特征值 = `2 •` ordered）。 -/
theorem metricScalar_eq_two_mul_sum_ordered_C11V3 {X : Type u} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X] [T2Space X]
    (g : SmoothRiemannianMetric ThreeModel X) (x : X)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace ThreeModel x))
    (horth : OrthonormalBasisAt (I := ThreeModel) g x basis) :
    metricScalarAt g x = 2 * ∑ i : Fin 3, orderedSectionalCurvaturesAt (I := ThreeModel) x basis
      (metricAlgebraicCurvatureTensorAt g x) i := by
  have h1 := traceNormalizedMetricCurvatureOperatorMatrixAt_trace_eq_metricScalarAt
    (I := ThreeModel) g x basis horth
  rw [← h1]
  let A := metricAlgebraicCurvatureTensorAt g x
  have hH := traceNormalizedCurvatureOperatorMatrixAt_isHermitian (I := ThreeModel) x basis A
  have hperm : ∑ i : Fin 3, hH.eigenvalues i = ∑ i : Fin 3, hH.eigenvalues₀ i := by
    unfold Matrix.IsHermitian.eigenvalues
    let e : Fin 3 ≃ Fin 3 := Fintype.equivOfCardEq (Fintype.card_fin 3)
    exact (e.symm.sum_comp hH.eigenvalues₀)
  have htr : (traceNormalizedMetricCurvatureOperatorMatrixAt (I := ThreeModel) g x basis).trace =
      ∑ i : Fin 3, hH.eigenvalues i :=
    hH.trace_eq_sum_eigenvalues
  rw [htr, hperm, traceNormalizedCurvatureOperatorMatrixAt_eigenvalues]
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rfl

/-- **HI ⇒ 点态 `|Rm|` 上界**：`InFixedHamiltonIveyRegion g a x`（`a > 0`）⇒
`√(normSq0S g x 4 Rm) ≤ 2√3 · (3/2 |R| + e⁴/a)`（metric 级，对应 G2 `hcan` 的 `normSq0S` 形）。 -/
theorem sqrt_normSq_le_of_HI_C11V3 {X : Type u} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X] [T2Space X]
    (g : SmoothRiemannianMetric ThreeModel X) {a : ℝ} (ha : 0 < a) (x : X)
    (hHI : InFixedHamiltonIveyRegion g a x) :
    Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤
      2 * Real.sqrt 3 * (3 / 2 * |metricScalarAt g x| + Real.exp 4 / a) := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt g x (by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp)
  let A := metricAlgebraicCurvatureTensorAt g x
  have hR := metricScalar_eq_two_mul_sum_ordered_C11V3 g x basis horth
  rw [Fin.sum_univ_three] at hR
  set k0 := orderedSectionalCurvaturesAt (I := ThreeModel) x basis A 0 with hk0
  set k1 := orderedSectionalCurvaturesAt (I := ThreeModel) x basis A 1 with hk1
  set k2 := orderedSectionalCurvaturesAt (I := ThreeModel) x basis A 2 with hk2
  have h10 : k1 ≤ k0 := orderedSectionalCurvaturesAt_one_le_zero (I := ThreeModel) x basis A
  have h21 : k2 ≤ k1 := orderedSectionalCurvaturesAt_two_le_one (I := ThreeModel) x basis A
  have hmem := (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion g a x).mp hHI
  rw [leastCurvatureOperatorEigenvalueAt_eq_sectionalMin (I := ThreeModel) g x basis horth A]
    at hmem
  change 0 ≤ 2 * k2 ∨ fixedHamiltonIveyBarrier a (-(2 * k2)) ≤ metricScalarAt g x at hmem
  set R := metricScalarAt g x with hRdef
  have he : (0 : ℝ) < Real.exp 4 / a := by positivity
  set b : ℝ := 3 / 2 * |R| + Real.exp 4 / a with hb
  have hb0 : 0 ≤ b := by positivity
  have hRabs : R ≤ |R| := le_abs_self R
  have hRabs0 : 0 ≤ |R| := abs_nonneg R
  have hk0b : k0 ≤ b ∧ -b ≤ k2 := by
    rcases hmem with h | h
    · refine ⟨by linarith, by linarith⟩
    · set Xv : ℝ := -(2 * k2) with hXv
      unfold fixedHamiltonIveyBarrier at h
      rcases le_or_gt Xv 0 with hX0 | hX0
      · refine ⟨by linarith, by linarith⟩
      · by_cases haX : Real.exp 4 ≤ a * Xv
        · have hlog : 4 ≤ Real.log (a * Xv) := by
            rw [Real.le_log_iff_exp_le (by positivity)]
            exact haX
          have hXR : Xv ≤ R := by nlinarith
          refine ⟨by linarith, by linarith⟩
        · have hXe : Xv < Real.exp 4 / a := by
            rw [lt_div_iff₀ ha]
            linarith [not_le.mp haX]
          refine ⟨by linarith, by linarith⟩
  have habs : ∀ i : Fin 3, |orderedSectionalCurvaturesAt (I := ThreeModel) x basis A i| ≤ b := by
    intro i
    have hanti := orderedSectionalCurvaturesAt_antitone (I := ThreeModel) x basis A
    have hle0 := hanti (Fin.zero_le i)
    have hle2 : orderedSectionalCurvaturesAt (I := ThreeModel) x basis A i ≥ k2 := by
      have hi : i ≤ (2 : Fin 3) := by fin_cases i <;> decide
      exact hanti hi
    rw [abs_le]
    exact ⟨by linarith [hk0b.2], by linarith [hk0b.1]⟩
  exact sqrt_normSq0S_le_of_abs_orderedSectionalCurvaturesAt_le (I := ThreeModel) g x basis
    horth A habs

/-- **晚期 `hcomp`（GAP-1′ 的来源）**：history slice 的 HI（年龄 `c + t`，`Pre841NativeData.pinching`）+
标量下界（`-3/(t + c') ≤ R`，`scalar_lower` 的 `-3/(2(t+c))` 蕴含它）+ `nr ≤ M` ⇒ 存在 `T₀`，`v' ≥ T₀` 时
`|Rm| = s⁻²`、`s < nr v'/50` ⇒ `s⁻² ≤ 2500·R`（实际得 `≤ 8R`）。晚期 `e⁴/(c+v')`、`1/(v'+c')` 与
`K = 2500/M² ≤ s⁻²` 比较：`R ≤ 0` 时 `s⁻² ≤ K/2` 矛盾，故 `R > 0`，再 `s⁻² ≤ 6R + K/4`。 -/
theorem hcomp_late_of_HI_C11V3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {nr : ℝ → ℝ} {M c c' : ℝ} (hM : 0 < M)
    (hnr : ∀ s, 0 ≤ s → nr s ≤ M) (hc : 0 < c) (hc' : 0 < c')
    (hHI : ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
        InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (c + t) x)
    (hlow : ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
        -3 / ((t : ℝ) + c') ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) x) :
    ∃ T₀ : ℝ, ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (v' : Icc (0 : ℝ) H.horizon) (w : (H.stageAt v').Carrier) (s : ℝ),
        T₀ ≤ (v' : ℝ) → 0 < s → s < nr v' / 50 →
        s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
          (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
        (s⁻¹) ^ 2 ≤ 2500 * metricScalarAt (H.stageMetric (H.activeStage v') v') w := by
  have hK : 0 < 2500 / M ^ 2 := by positivity
  set K : ℝ := 2500 / M ^ 2 with hKdef
  have he4 : 0 < Real.exp 4 := Real.exp_pos 4
  refine ⟨(16 * Real.exp 4 + 72) / K, ?_⟩
  intro n H v' w s hT0 hs hsnr hcont
  have hT0pos : 0 < (16 * Real.exp 4 + 72) / K := by positivity
  have hv0 : 0 < (v' : ℝ) := lt_of_lt_of_le hT0pos hT0
  have hsM : s < M / 50 := lt_of_lt_of_le hsnr (by linarith [hnr v' v'.2.1])
  have hu : K ≤ (s⁻¹) ^ 2 := by
    have h1 : 50 / M < s⁻¹ := by
      rw [lt_inv_comm₀ (by positivity) hs]
      rw [inv_div]
      exact hsM
    have h2 : (50 / M) ^ 2 ≤ (s⁻¹) ^ 2 := pow_le_pow_left₀ (by positivity) h1.le 2
    have h3 : (50 / M) ^ 2 = K := by rw [hKdef, div_pow]; norm_num
    linarith
  have hN : normSq0S (H.stageMetric (H.activeStage v') v') w 4
      (metricRm04At (H.stageMetric (H.activeStage v') v') w) = ((s⁻¹) ^ 2) ^ 2 := by
    have hs4 : s ^ 4 ≠ 0 := by positivity
    have : normSq0S (H.stageMetric (H.activeStage v') v') w 4
        (metricRm04At (H.stageMetric (H.activeStage v') v') w) = (s ^ 4)⁻¹ := by
      field_simp
      linarith
    rw [this]
    field_simp
  have hsqrt : Real.sqrt (normSq0S (H.stageMetric (H.activeStage v') v') w 4
      (metricRm04At (H.stageMetric (H.activeStage v') v') w)) = (s⁻¹) ^ 2 := by
    rw [hN]
    exact Real.sqrt_sq (by positivity)
  have hbound := sqrt_normSq_le_of_HI_C11V3 (H.stageMetric (H.activeStage v') v')
    (by positivity : 0 < c + (v' : ℝ)) w (hHI n v' w)
  rw [hsqrt] at hbound
  have h3 : Real.sqrt 3 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have h30 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  set R := metricScalarAt (H.stageMetric (H.activeStage v') v') w with hRdef
  have hTK : (16 * Real.exp 4 + 72) ≤ K * v' := by
    have := (div_le_iff₀ hK).mp hT0
    linarith
  have hea : Real.exp 4 / (c + v') ≤ K / 16 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hlowR := hlow n v' w
  have hRpos : 0 < R := by
    by_contra hneg
    have hR0 : R ≤ 0 := not_lt.mp hneg
    have habsR : |R| = -R := abs_of_nonpos hR0
    have h4 : -R ≤ 3 / ((v' : ℝ) + c') := by
      have := neg_le_neg hlowR
      rw [neg_div] at this
      linarith
    have h5 : 3 / ((v' : ℝ) + c') ≤ 3 / v' := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      linarith
    have h6 : 3 / (v' : ℝ) ≤ K / 24 := by
      rw [div_le_iff₀ hv0]
      nlinarith
    rw [habsR] at hbound
    nlinarith [mul_nonneg h30 (neg_nonneg.mpr hR0)]
  rw [abs_of_pos hRpos] at hbound
  nlinarith [mul_nonneg h30 hRpos.le]

/-- **端到端（narrow tuple + 晚期 HI，无显式 `hcomp`）**：`hcomp` 由 history slice 的 HI（年龄 `c + t`）与
标量下界 `-3/(2(t + c')) ≤ R`（`Pre841NativeData.pinching / scalar_lower` 的 history 形）+ `nr` 单调
给出（`M = q.neckRadius 0`）。剩余显式前提只剩 GAP-2（`q.modelAccuracy ≤ ε₀`）与 K 链（GAP-3）。 -/
theorem localKappaWindow_zero_of_narrowTuple_HI_C11V3 (D : ℝ)
    (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {q : CutoffParameters} {A c c' : ℝ}, 0 < A → 0 < c → 0 < c' →
      q.modelRadius = D → q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder →
      ∀ records : CutoffRecords_C11S F q,
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) →
      AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
          InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (c + t) x) →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
          -3 / ((t : ℝ) + c') ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) x) →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      LargerBallAccuracySupply_C11S δ α → LocalKappaWideSupply_C11Q F δ α q.neckRadius →
      ∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'' := by
  obtain ⟨ε₀, hε₀, hE⟩ := localKappaWindow_zero_of_narrowTuple_late_C11V3.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F δ α q A c c' hA hc hc' hDq hacc' hord records hwin hanti hcanon hHI hlow hdeg hacc
    hwide
  have hcomp := hcomp_late_of_HI_C11V3 (nr := q.neckRadius) (M := q.neckRadius 0)
    (q.neckRadius_pos 0 le_rfl) (fun s hs => hanti (Set.mem_Ici.mpr le_rfl) hs hs) hc hc' hHI hlow
  exact hE hA hDq hacc' hord records hwin hanti hcanon hcomp hdeg hacc hwide

/-- **端到端 consumer（K 链 + 晚期 HI ⇒ `tracedKappa_of_window_P6B`）**。 -/
example (D : ℝ) (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ)
    (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {q : CutoffParameters} {A c c' : ℝ}, 0 < A → 0 < c → 0 < c' →
      q.modelRadius = D → q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder →
      ∀ records : CutoffRecords_C11S F q,
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) →
      AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
          InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (c + t) x) →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
          -3 / ((t : ℝ) + c') ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) x) →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      LargerBallAccuracySupply_C11S δ α → LocalKappaWideSupply_C11Q F δ α q.neckRadius →
      True := by
  obtain ⟨ε₀, hε₀, hE⟩ := localKappaWindow_zero_of_narrowTuple_HI_C11V3.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F δ α q A c c' hA hc hc' hDq hacc hord records hwin hanti hcanon hHI hlow hdeg hS7
    hwide
  obtain ⟨κ'', -, hW0⟩ := hE hA hc hc' hDq hacc hord records hwin hanti hcanon hHI hlow hdeg hS7
    hwide
  have := tracedKappa_of_window_P6B hW0
  trivial

/-- **HI 与标量下界直接由 `records` 给出**（P6A L3a `exists_history_pinching_P6A`，`a₀` 一致于全部 history）：
`c = c' = a₀`（标量下界取 `-3/(t + c')` 形，比 `scalar_lower` 的 `-3/(2(t+c))` 弱，后者蕴含前者）。 -/
theorem history_HI_and_lower_of_records_C11V3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} (records : CutoffRecords_C11S F q) :
    ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
          InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (c + t) x) ∧
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
          -3 / ((t : ℝ) + c') ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) x) := by
  obtain ⟨a₀, ha₀, hP⟩ := exists_history_pinching_P6A F records
  refine ⟨a₀, a₀, ha₀, ha₀, ?_, ?_⟩
  · intro n H t x
    exact (hP n (H.activeStage t) t (H.activeStage_mem t) x).1
  · intro n H t x
    have h := (hP n (H.activeStage t) t (H.activeStage_mem t) x).2
    rw [add_comm (t : ℝ) a₀]
    exact h

/-- **端到端（narrow tuple，只吃 `records`，无 HI / `hcomp` 前提）**：HI 与标量下界由
`history_HI_and_lower_of_records_C11V3` 内部给出。 -/
theorem localKappaWindow_zero_of_narrowTuple_records_C11V3 (D : ℝ)
    (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {q : CutoffParameters} {A : ℝ}, 0 < A →
      q.modelRadius = D → q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder →
      ∀ records : CutoffRecords_C11S F q,
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) →
      AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      LargerBallAccuracySupply_C11S δ α → LocalKappaWideSupply_C11Q F δ α q.neckRadius →
      ∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'' := by
  obtain ⟨ε₀, hε₀, hE⟩ := localKappaWindow_zero_of_narrowTuple_HI_C11V3.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F δ α q A hA hDq hacc' hord records hwin hanti hcanon hdeg hacc hwide
  obtain ⟨c, c', hc, hc', hHI, hlow⟩ := history_HI_and_lower_of_records_C11V3 records
  exact hE hA hc hc' hDq hacc' hord records hwin hanti hcanon hHI hlow hdeg hacc hwide

/-- **端到端 consumer（records 形，最终入口）**：K 链 wide 供给 + narrow tuple 的 `records` /
`HistoryCanonicalSupply` / 单调 + `N` + S7 ⇒ `nr := 0` window ⇒ `tracedKappa_of_window_P6B`；
GAP-1 已闭合，剩 GAP-2（`q.modelAccuracy ≤ ε₀`）与 GAP-3（K 链）。 -/
example (D : ℝ) (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ)
    (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {q : CutoffParameters} {A : ℝ}, 0 < A →
      q.modelRadius = D → q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder →
      ∀ records : CutoffRecords_C11S F q,
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) →
      AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      LargerBallAccuracySupply_C11S δ α → LocalKappaWideSupply_C11Q F δ α q.neckRadius →
      True := by
  obtain ⟨ε₀, hε₀, hE⟩ := localKappaWindow_zero_of_narrowTuple_records_C11V3.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F δ α q A hA hDq hacc hord records hwin hanti hcanon hdeg hS7 hwide
  obtain ⟨κ'', -, hW0⟩ := hE hA hDq hacc hord records hwin hanti hcanon hdeg hS7 hwide
  have := tracedKappa_of_window_P6B hW0
  trivial

end GC.LongTime.Ch11

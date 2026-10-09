import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeResetTracedC11SP

set_option autoImplicit false

/-!
# Q 一致的 reset Shi（O-CH11-NATIVE-BORN G3a，后缀 `_C11SP`）

hBorn 的 jets 常数 `J` 要先于 `Q` 选，而 SPINE-B G7 `exists_reset_shi_commonFlow_C11SP` 的常数 `B` 依赖
`(N, T, R, K, A)`。native 下零阶界是 `K·Q²`（`normSq0S` 形）、初始 jets 是 `A k·Q^{2+k}`、深度是 `θ/Q`、
初始球半径是 `R/√Q`，都随 `Q` 变，所以 G7 不能直接给 Q 一致的界。本页先做抛物 rescale：
* `exists_initial_shi_scaled_C11SP`：对一般 `SolutionOn`，用树内 `parabolicSolution S 0 Q`
  （`Scaling/Parabolic`，`parabolicSolution_isSolutionOn`、`parabolicNablaKRmNormSq`）
  把 `[0, θ]` 拉到 `[0, Qθ]`，再调 `InitialLocalEndpointHorizon` 的
  `exists_uniform_initial_curvature_derivative_bound_on_compact_ball_of_open_regular_interval`；
  逐行照 `InitialLocalCutoffHorizon` 里 `c := max 1 K` 的 rescale 段（Gram、球、零阶、初始 jets 四处）。
  结论 `nablaKRm04NormSqIntrinsic S k t x ≤ B·Q^{2+k}`，`B` 只依赖 `(N, T, R, K, A)`。
* `exists_reset_shi_commonFlow_scaled_C11SP`：G7 的 Q 一致孪生（同 G7 证明，换成上面的 scaled 核），
  结论直接写成归一化形 `curvDerivNorm k (scaleMetric Q g(t)) pU ≤ √B`。仍要正 stage age（O2）。
-/

noncomputable section

open Set Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

/-- **G3a（PROVED）**：带初始数据的 Shi 的 Q 一致形。常数 `B` 先于空间 / 解 / `Q` 选。 -/
theorem exists_initial_shi_scaled_C11SP (N : ℕ) (T R K : ℝ) (hR : 0 < R) (A : ℕ → ℝ)
    (hA : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ A k) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
      [IsManifold ThreeModel ∞ X] [T2Space X] [SigmaCompactSpace X],
      ∀ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := X) D) (Q : ℝ),
        0 < Q → ∀ θ : ℝ, 0 < θ → Q * θ ≤ T → IsSolutionOn S →
      Icc 0 θ ⊆ D.carrier → Ioo 0 θ ⊆ D.regular →
      (∀ (x₀ : X) (i j : Fin (Module.finrank ℝ ThreeSpace)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × X => Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
          (Icc 0 θ ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet)) →
      ∀ p : X,
      IsCompact {x : X | riemannianEDistOf (S.base.metric 0) p x ≤
        ENNReal.ofReal (R / Real.sqrt Q)} →
      (∀ t ∈ Icc 0 θ, ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal (R / Real.sqrt Q) →
          nablaKRm04NormSqIntrinsic S 0 t x ≤ K * Q ^ 2) →
      (∀ k, 1 ≤ k → k ≤ N → ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal (R / Real.sqrt Q) →
          nablaKRm04NormSqIntrinsic S k 0 x ≤ A k * Q ^ (2 + k)) →
      ∀ k ≤ N, ∀ t ∈ Icc 0 θ, ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal (R / Real.sqrt Q / 2) →
          nablaKRm04NormSqIntrinsic S k t x ≤ B * Q ^ (2 + k) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_initial_curvature_derivative_bound_on_compact_ball_of_open_regular_interval
      (I := ThreeModel) N T R K hR A hA
  refine ⟨B, hB, ?_⟩
  intro X _ _ _ _ _ D S Q hQ θ hθ hθT hS hslab hreg hgram p hcompact hcurv hinit k hk t ht x hx
  have hzero : (0 : ℝ) ∈ D.carrier := hslab ⟨le_rfl, hθ.le⟩
  let P := parabolicSolution S 0 Q hQ hzero
  have hP : IsSolutionOn P := parabolicSolution_isSolutionOn S hS 0 Q hQ hzero
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hRR : Real.sqrt Q * (R / Real.sqrt Q) = R := mul_div_cancel₀ R hsQ.ne'
  have htime : ∀ s ∈ Icc 0 (Q * θ), s / Q ∈ Icc 0 θ := by
    intro s hs
    refine ⟨div_nonneg hs.1 hQ.le, (div_le_iff₀ hQ).mpr ?_⟩
    simpa only [mul_comm] using hs.2
  have hpslab : Icc 0 (Q * θ) ⊆ (parabolicInterval D 0 Q hzero).carrier := by
    intro s hs
    change parabolicTime 0 Q s ∈ D.carrier
    simpa only [parabolicTime, zero_add] using hslab (htime s hs)
  have hpreg : Ioo 0 (Q * θ) ⊆ (parabolicInterval D 0 Q hzero).regular := by
    intro s hs
    change parabolicTime 0 Q s ∈ D.regular
    have h2 : s / Q < θ := (div_lt_iff₀ hQ).mpr (by linarith [hs.2, mul_comm Q θ])
    simpa only [parabolicTime, zero_add] using hreg ⟨div_pos hs.1 hQ, h2⟩
  have hmetric0 : P.base.metric 0 = scaleMetric Q hQ (S.base.metric 0) := by
    simp only [P, parabolicSolution, parabolicFamily, parabolicTime, zero_div, zero_add]
  have hpgram : ∀ (x₀ : X) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × X => Tensor.Coordinates.chartGramMatrix (P.base.metric q.1) x₀ q.2 i j)
        (Icc 0 (Q * θ) ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet) := by
    intro x₀ i j
    have hm : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) (𝓘(ℝ, ℝ).prod ThreeModel) ∞
        (fun q : ℝ × X => (q.1 / Q, q.2)) :=
      (contMDiff_fst.div_const Q).prodMk contMDiff_snd
    have hmap : MapsTo (fun q : ℝ × X => (q.1 / Q, q.2))
        (Icc 0 (Q * θ) ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet)
        (Icc 0 θ ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet) :=
      fun q hq => ⟨htime q.1 hq.1, hq.2⟩
    have hh := (contMDiffOn_const (c := Q)).mul ((hgram x₀ i j).comp hm.contMDiffOn hmap)
    apply hh.congr
    intro q _
    simp only [Function.comp_def, P, parabolicSolution, parabolicFamily,
      parabolicTime, zero_add, Tensor.Coordinates.chartGramMatrix_apply,
      scaleMetric_inner, Pi.mul_apply]
  have hball (r : ℝ) : {y : X | riemannianEDistOf (P.base.metric 0) p y ≤
      ENNReal.ofReal (Real.sqrt Q * r)} =
    {y : X | riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal r} := by
    rw [hmetric0]
    exact closedBall_scaleMetric_eq (S.base.metric 0) Q hQ p r
  have hballR : {y : X | riemannianEDistOf (P.base.metric 0) p y ≤ ENNReal.ofReal R} =
      {y : X | riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal (R / Real.sqrt Q)} := by
    rw [← hball (R / Real.sqrt Q), hRR]
  have hpcompact : IsCompact {y : X | riemannianEDistOf (P.base.metric 0) p y ≤
      ENNReal.ofReal R} := by
    rw [hballR]
    exact hcompact
  have hpcurv : ∀ s ∈ Icc 0 (Q * θ), ∀ y : X,
      riemannianEDistOf (P.base.metric 0) p y ≤ ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic P 0 s y ≤ K := by
    intro s hs y hy
    have hy' : riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal (R / Real.sqrt Q) := by
      change y ∈ {y : X | riemannianEDistOf (S.base.metric 0) p y ≤
        ENNReal.ofReal (R / Real.sqrt Q)}
      rw [← hballR]
      exact hy
    rw [parabolicNablaKRmNormSq S 0 Q hQ hzero]
    have hraw := hcurv (s / Q) (htime s hs) y hy'
    have heq : Q⁻¹ ^ (2 + 0) * (K * Q ^ 2) = K := by
      rw [add_zero, mul_left_comm, ← mul_pow, inv_mul_cancel₀ hQ.ne', one_pow, mul_one]
    calc Q⁻¹ ^ (2 + 0) * nablaKRm04NormSqIntrinsic S 0 (parabolicTime 0 Q s) y
        ≤ Q⁻¹ ^ (2 + 0) * (K * Q ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (inv_pos.mpr hQ).le _)
          simpa only [parabolicTime, zero_add] using hraw
      _ = K := heq
  have hpinit : ∀ j, 1 ≤ j → j ≤ N → ∀ y : X,
      riemannianEDistOf (P.base.metric 0) p y ≤ ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic P j 0 y ≤ A j := by
    intro j hj hjN y hy
    have hy' : riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal (R / Real.sqrt Q) := by
      change y ∈ {y : X | riemannianEDistOf (S.base.metric 0) p y ≤
        ENNReal.ofReal (R / Real.sqrt Q)}
      rw [← hballR]
      exact hy
    rw [parabolicNablaKRmNormSq S 0 Q hQ hzero]
    have heq : Q⁻¹ ^ (2 + j) * (A j * Q ^ (2 + j)) = A j := by
      rw [mul_left_comm, ← mul_pow, inv_mul_cancel₀ hQ.ne', one_pow, mul_one]
    calc Q⁻¹ ^ (2 + j) * nablaKRm04NormSqIntrinsic S j (parabolicTime 0 Q 0) y
        ≤ Q⁻¹ ^ (2 + j) * (A j * Q ^ (2 + j)) := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (inv_pos.mpr hQ).le _)
          simpa only [parabolicTime, zero_div, zero_add] using hinit j hj hjN y hy'
      _ = A j := heq
  have hpt : Q * t ∈ Icc 0 (Q * θ) :=
    ⟨mul_nonneg hQ.le ht.1, mul_le_mul_of_nonneg_left ht.2 hQ.le⟩
  have hpx : riemannianEDistOf (P.base.metric 0) p x ≤ ENNReal.ofReal (R / 2) := by
    have hx' : x ∈ {y : X | riemannianEDistOf (P.base.metric 0) p y ≤
        ENNReal.ofReal (Real.sqrt Q * (R / Real.sqrt Q / 2))} := by
      rw [hball]
      exact hx
    have hR2 : Real.sqrt Q * (R / Real.sqrt Q / 2) = R / 2 := by
      rw [mul_div_assoc', hRR]
    rw [hR2] at hx'
    exact hx'
  have hb := hbound X _ P (Q * θ) (mul_pos hQ hθ) hθT hP hpslab hpreg hpgram p hpcompact
    hpcurv hpinit k hk (Q * t) hpt x hpx
  rw [parabolicNablaKRmNormSq S 0 Q hQ hzero] at hb
  simp only [parabolicTime, zero_add, mul_div_cancel_left₀ t hQ.ne'] at hb
  have hmul := mul_le_mul_of_nonneg_left hb (pow_pos hQ (2 + k)).le
  have heq : Q ^ (2 + k) * (Q⁻¹ ^ (2 + k) * nablaKRm04NormSqIntrinsic S k t x) =
      nablaKRm04NormSqIntrinsic S k t x := by
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hQ.ne', one_pow, one_mul]
  rw [heq] at hmul
  linarith [hmul, mul_comm (Q ^ (2 + k)) B]

/-- **G3b（PROVED）**：SPINE-B G7 `exists_reset_shi_commonFlow_C11SP` 的 Q 一致孪生。零阶 `K·Q²`、
初始 jets `A k·Q^{2+k}`、深度 `Q(t − a) ≤ T`、初始球 `R/√Q`；结论归一化 `≤ √B`，`B` 先于 history 与 `Q`。 -/
theorem exists_reset_shi_commonFlow_scaled_C11SP (N : ℕ) (T R K : ℝ) (hR : 0 < R)
    (A : ℕ → ℝ) (hA : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ A k) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
      (Q : ℝ) (hQ : 0 < Q),
      (a : ℝ) < t → Q * ((t : ℝ) - a) ≤ T → H.time (H.activeStage t) < t →
      ∀ (U : TopologicalSpace.Opens (H.stageAt t).Carrier)
        (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U →
          (H.stage j.val).Carrier)
        (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
        (S : SolutionOn (I := ThreeModel) (M := U) (RealTimeInterval.closed a.val t.val hat)),
        IsSolutionOn S →
        (∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
          ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
            S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) →
        (∀ v ∈ Icc a.val t.val, ∀ x : U,
          normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ K * Q ^ 2) →
        S.base.metric t = (H.stageMetric (H.activeStage t) t).restrictOpen U →
      ∀ (pU : U) (Rbig : ℝ≥0),
        {x | riemannianEDistOf (H.stageMetric (H.activeStage t) t) pU.val x ≤ Rbig} ⊆ U →
        ENNReal.ofReal (Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 *
          Real.sqrt (K * Q ^ 2) * |(a : ℝ) - t|)) * ENNReal.ofReal (R / Real.sqrt Q) ≤ Rbig →
        (∀ k, 1 ≤ k → k ≤ N → ∀ x : U,
          riemannianEDistOf (S.base.metric a) pU x ≤ ENNReal.ofReal (R / Real.sqrt Q) →
          curvDerivNormSq k (H.stageMetric (H.activeStage a) a)
            (f ⟨H.activeStage a, le_rfl, H.activeStage_mono hat⟩ x) ≤ A k * Q ^ (2 + k)) →
      ∀ k ≤ N, curvDerivNorm k (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) pU.val ≤
        Real.sqrt B := by
  obtain ⟨B, hB, hb⟩ := exists_initial_shi_scaled_C11SP.{u} N T R K hR A hA
  refine ⟨B, hB, ?_⟩
  intro H a t hat Q hQ hlt hT hpos U f hf S hS hmetric hRm hterm pU Rbig hball hfit hinit k hk
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have hcar : Icc a.val t.val ⊆ (RealTimeInterval.closed a.val t.val hat).carrier :=
    fun _ h => h
  have hreg : Ioo a.val t.val ⊆ (RealTimeInterval.closed a.val t.val hat).regular :=
    fun _ h => h
  have h0 : (S.timeShift a.val).base.metric 0 = S.base.metric a.val := by
    rw [SolutionOn.timeShift_base_metric, zero_add]
  have hgram : ∀ (x₀ : U) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × U => Tensor.Coordinates.chartGramMatrix
          ((S.timeShift a.val).base.metric q.1) x₀ q.2 i j)
        (Icc 0 (t.val - a.val) ×ˢ
          (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet) := by
    intro x₀ i j
    have hG := commonFlow_closedGram_C11SP H hat hlt hpos f hf S hS hmetric x₀ i j
    have hφ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) (𝓘(ℝ, ℝ).prod ThreeModel) ∞
        (fun q : ℝ × U => (q.1 + a.val, q.2)) :=
      (contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd
    refine (hG.comp hφ.contMDiffOn ?_).congr ?_
    · intro q hq
      exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hq.2⟩
    · intro q _
      rfl
  have hcomp : IsCompact
      {x | riemannianEDistOf (H.stageMetric (H.activeStage t) t) pU.val x ≤ (Rbig : ℝ≥0∞)} := by
    have h := (Geometry.Metric.isClosed_riemannianClosedBallOf
      (H.stageMetric (H.activeStage t) t) pU.val (Rbig : ℝ)).isCompact
    simpa only [riemannianClosedBallOf, ENNReal.ofReal_coe_nnreal] using h
  have hcpt : IsCompact {x : U |
      riemannianEDistOf ((S.timeShift a.val).base.metric 0) pU x ≤
        ENNReal.ofReal (R / Real.sqrt Q)} := by
    rw [h0]
    exact isCompact_intrinsic_closedBall_of_terminal_ball (H.stageMetric (H.activeStage t) t) U
      S hS hcar hreg hRm ⟨le_rfl, hat⟩ hterm pU (r := (R / Real.sqrt Q).toNNReal) (R := Rbig)
      hcomp hball hfit
  have key := hb U (RealTimeInterval.closed a.val t.val hat |>.timeShift a.val)
    (S.timeShift a.val) Q hQ (t.val - a.val) (by linarith) hT (isSolutionOn_timeShift hS a.val)
    (fun r hr => hcar ⟨by linarith [hr.1], by linarith [hr.2]⟩)
    (fun r hr => hreg ⟨by linarith [hr.1], by linarith [hr.2]⟩) hgram pU hcpt
    (fun s hs x _ => by
      rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, SolutionOn.timeShift_base_metric,
        FILL910.curvDerivNormSq_zero_eq_normSq0S_metricRm04At]
      exact hRm (s + a.val) ⟨by linarith [hs.1], by linarith [hs.2]⟩ x)
    (fun j hj1 hjN x hx => by
      rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, h0,
        hmetric ⟨H.activeStage a, le_rfl, H.activeStage_mono hat⟩ a.val ⟨le_rfl, hat⟩
          (H.activeStage_mem a), curvDerivNormSq_localPullMetric]
      exact hinit j hj1 hjN x (h0 ▸ hx))
    k hk (t.val - a.val) ⟨by linarith, le_rfl⟩ pU
    (by rw [h0, riemannianEDistOf_self]; exact bot_le)
  rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, SolutionOn.timeShift_base_metric,
    sub_add_cancel, hterm] at key
  have hQpow : Q ^ (2 + k) = (Q * Real.sqrt Q ^ k) ^ 2 := by
    have hs : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ.le
    calc Q ^ (2 + k) = Q ^ 2 * (Real.sqrt Q ^ 2) ^ k := by rw [hs, pow_add]
      _ = (Q * Real.sqrt Q ^ k) ^ 2 := by ring
  have hden : 0 < Q * Real.sqrt Q ^ k := mul_pos hQ (pow_pos (Real.sqrt_pos.mpr hQ) k)
  have hnorm : curvDerivNorm k (H.stageMetric (H.activeStage t) t) pU.val ≤
      Real.sqrt B * (Q * Real.sqrt Q ^ k) := by
    calc curvDerivNorm k (H.stageMetric (H.activeStage t) t) pU.val
        = curvDerivNorm k ((H.stageMetric (H.activeStage t) t).restrictOpen U) pU :=
          (curvDerivNorm_restrictOpen _ U k pU).symm
      _ ≤ Real.sqrt (B * Q ^ (2 + k)) := Real.sqrt_le_sqrt key
      _ = Real.sqrt B * (Q * Real.sqrt Q ^ k) := by
          rw [hQpow, Real.sqrt_mul (by linarith), Real.sqrt_sq hden.le]
  rw [curvDerivNorm_scaleMetric]
  exact (div_le_iff₀ hden).mpr hnorm

end GC.LongTime.Ch11

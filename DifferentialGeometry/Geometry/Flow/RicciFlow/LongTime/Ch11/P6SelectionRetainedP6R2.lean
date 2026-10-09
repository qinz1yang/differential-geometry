import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectionP6X

/-!
# 保留 per-n room / ball 的 selector 变体（O-CH11-P6REST2 G1，后缀 `_P6R2`）

树内 selector `exists_localized_canonical_time_control_point_selection` 一次选择给出 room
`T − r²/2 ≤ s − L²/Q`（⑥）与 ball `y ∈ B_s(O_s, (A+1) r)`（⑧）；`selection_step_P6X` 丢 ⑧，
`selection_of_bad_sequence_P6X` 再把 ⑥ 降成 eventual 版、`L` 的显式式只留在证明体里。对任意旧
`σ y L` 这些分量无法事后恢复，所以本文件在**同一次** selection 里保留它们：

* `selection_step_retained_P6R2`：直接调树内 selector（同前提，`L := √(R₀ r²)/4`），输出 =
  `selection_step_P6X` 的输出 + ball ⑧；
* `selection_of_bad_sequence_retained_P6R2`：同 `selection_of_bad_sequence_P6X` 的前提，结论 =
  P6X 原结论 ∧ `L n = √(R₀ r²)/4` ∧ per-n room ∧ per-n ball；
* consumer `example`：由本文件结论推回 `selection_of_bad_sequence_P6X` 的结论（新结论严格更强）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **单点 selection，保留 ball（`_P6R2`）**：树内 selector 取 `L := √(R₀ r²)/4`；输出 =
`selection_step_P6X` 的分量（坏、`0 < Q`、`R₀ ≤ Q`、`Q ≤ ρ(T)⁻²`、room、Good 区）+ ball
`y ∈ B_s(O_s, (A+1) r)`（selector 的第 ⑧ 分量）。 -/
theorem selection_step_retained_P6R2 (H : ObservedHistory.{u}) (q : CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcanonical : ∀ (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier),
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt (H.stageMetric (H.activeStage v) v) z →
      ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hderivative : ∀ (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier),
      H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt (H.stageMetric (H.activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt (H.stageMetric (H.activeStage v) t) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt (H.stageMetric (H.activeStage v) v) z ^ 2)
    (T : Icc (0 : ℝ) H.horizon) (p : (H.stageAt T).Carrier) (r A : ℝ) (hr : 0 < r) (hA : 0 < A)
    (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ T)
    (haSeed : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (x : (H.stageAt T).Carrier)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage T) T) p (A * r))
    (hR : 0 < metricScalarAt (H.stageMetric (H.activeStage T) T) x)
    (hbad : ¬ H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' T x) :
    ∃ (s : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ s) (hsT : s ≤ T)
      (y : (H.stageAt s).Carrier),
    (¬ H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' s y) ∧
    0 < metricScalarAt (H.stageMetric (H.activeStage s) s) y ∧
    metricScalarAt (H.stageMetric (H.activeStage T) T) x ≤
      metricScalarAt (H.stageMetric (H.activeStage s) s) y ∧
    metricScalarAt (H.stageMetric (H.activeStage s) s) y ≤ (q.neckRadius T ^ 2)⁻¹ ∧
    (T : ℝ) - r ^ 2 / 2 ≤ (s : ℝ) -
      (Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage T) T) x * r ^ 2) / 4) ^ 2 /
        metricScalarAt (H.stageMetric (H.activeStage s) s) y ∧
    y ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s)
      (seedTrace.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hsT))
      ((A + 1) * r) ∧
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ s),
      (s : ℝ) -
        (Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage T) T) x * r ^ 2) / 4) ^ 2 /
          metricScalarAt (H.stageMetric (H.activeStage s) s) y ≤ (v : ℝ) →
    ∀ z : (H.stageAt v).Carrier,
      riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
            (H.activeStage_mono (hvs.trans hsT))) z ≤
        riemannianEDistOf (H.stageMetric (H.activeStage s) s)
            (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y +
          ENNReal.ofReal
            ((Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage T) T) x * r ^ 2) / 4) /
              Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage s) s) y)) →
      4 * metricScalarAt (H.stageMetric (H.activeStage s) s) y ≤
        metricScalarAt (H.stageMetric (H.activeStage v) v) z →
      H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z := by
  have hL : 0 < Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage T) T) x * r ^ 2) / 4 :=
    div_pos (Real.sqrt_pos.mpr (by positivity)) (by norm_num)
  obtain ⟨s, has, hsT, y, hbad', hQ, hRQ, hQρ, -, hwin, -, hball, hgood⟩ :=
    H.exists_localized_canonical_time_control_point_selection q hC1 hC2 hCtime hanti
      hcanonical hderivative T p r A _ hr hA hL aSeed haT haSeed seedTrace x hx hR hbad
      (selection_htime_P6X hR) (selection_hspace_P6X hR hr)
  exact ⟨s, has, hsT, y, hbad', hQ, hRQ, hQρ, hwin, hball, hgood⟩

/-- **坏点序列 ⇒ selection 输出，保留 per-n room / ball（G1 主定理，`_P6R2`）**：前提与
`selection_of_bad_sequence_P6X` 逐字相同；结论 = P6X 原结论（逐字、同序）∧ `L n = √(R₀ r²)/4`
∧ per-n room `Tn − r²/2 ≤ σ − L²/R`（闭合主形 `hroom` 逐字）∧ per-n ball
`y ∈ B_σ(O_σ, (A+1) r)`（`hdistσ` 的来源）。 -/
theorem selection_of_bad_sequence_retained_P6R2 {Kh : ℕ → ObservedHistory.{u}}
    (q : ℕ → CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : ∀ n, AntitoneOn (q n).neckRadius (Ici 0))
    (hcanonical : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      ∃ W : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hderivative : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      (Kh n).time ((Kh n).activeStage v) < (v : ℝ) → (v : ℝ) < (Kh n).horizon →
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) t) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z ^ 2)
    (Tn : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (r : ℕ → ℝ) (A : ℝ) (hr : ∀ n, 0 < r n) (hA : 0 < A)
    (aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (haSeed : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (x : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (hx : ∀ n, x n ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n))
      (pT n) (A * r n))
    (hR : ∀ n, 0 < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (x n))
    (hbad : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (Tn n) (x n))
    (hdiv : Tendsto (fun n => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n))
      (Tn n)) (x n) * r n ^ 2) atTop atTop) :
    ∃ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
      (R : ℕ → ℝ) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n) (L : ℕ → ℝ),
      ((∀ n, R n = metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)) ∧
      (∀ n, 0 < R n) ∧
      (∀ n, metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (x n) ≤
        R n) ∧
      (∀ n, R n ≤ ((q n).neckRadius (Tn n) ^ 2)⁻¹) ∧
      Tendsto L atTop atTop ∧
      (∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (σ n) (y n)) ∧
      (∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
        ∀ z : ((Kh n).stageAt v).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
          (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z) ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - T / R n) ∧
      Tendsto (fun n => R n * ((σ n : ℝ) - ((Tn n : ℝ) - r n ^ 2 / 2))) atTop atTop ∧
      Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop) ∧
      (∀ n, L n = Real.sqrt (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n))
        (Tn n)) (x n) * r n ^ 2) / 4) ∧
      (∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - L n ^ 2 / R n) ∧
      (∀ n, y n ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) ((A + 1) * r n)) := by
  have key := fun n => selection_step_retained_P6R2 (Kh n) (q n) hC1 hC2 hCtime (hanti n)
    (hcanonical n) (hderivative n) (Tn n) (pT n) (r n) A (hr n) hA (aSeed n) (haT n) (haSeed n)
    (seedTrace n) (x n) (hx n) (hR n) (hbad n)
  choose σ has hsT y hsel hQ hRQ hQρ hwin hball hgood using key
  set R0 : ℕ → ℝ := fun n =>
    metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (x n) with hR0def
  have hL : Tendsto (fun n => Real.sqrt (R0 n * r n ^ 2) / 4) atTop atTop :=
    tendsto_sqrt_div_P6X hdiv (by norm_num)
  have hwin' : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - T /
      metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n) := by
    intro T hT
    filter_upwards [hL.eventually_ge_atTop (max 1 T)] with n hn
    exact window_of_large_L_P6X (hQ n) (hwin n) hn
  refine ⟨σ, y, fun n => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
    (y n), hsT, has, fun n => Real.sqrt (R0 n * r n ^ 2) / 4,
    ⟨fun _ => rfl, hQ, hRQ, hQρ, hL, hsel, hgood, ?_, hwin', ?_, ?_⟩, fun _ => rfl, hwin, hball⟩
  · intro T hT
    filter_upwards [hwin' T hT] with n hn
    have h2 : (0 : ℝ) ≤ r n ^ 2 := sq_nonneg _
    rw [haSeed n]
    linarith
  · refine tendsto_atTop_mono (fun n => ?_) (hL.atTop_mul_atTop₀ hL)
    exact window_room_P6X (hQ n) (hwin n)
  · have h200 : Tendsto (fun n => Real.sqrt (R0 n * r n ^ 2) / 200) atTop atTop :=
      tendsto_sqrt_div_P6X hdiv (by norm_num)
    refine tendsto_atTop_mono (fun n => ?_) h200
    have hs : Real.sqrt (R0 n) ≤ Real.sqrt
        (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)) :=
      Real.sqrt_le_sqrt (hRQ n)
    rw [sqrt_mul_sq_P6X (hR n).le (hr n)]
    have := (hr n).le
    nlinarith [Real.sqrt_nonneg (R0 n)]

/-- consumer：retained 结论的第一个合取分量逐字 = `selection_of_bad_sequence_P6X` 的结论
（新 selector 严格更强；`hroom` / ball / `L` 式是追加分量）。 -/
example : type_of% @selection_of_bad_sequence_P6X.{u} := by
  intro Kh q eps C1 C2 C1' C2' hC1 hC2 Ctime Ctime' hCtime hanti hcanonical hderivative Tn pT r A
    hr hA aSeed haT haSeed seedTrace x hx hR hbad hdiv
  obtain ⟨σ, y, R, hsT, has, L, hmain, -, -, -⟩ := selection_of_bad_sequence_retained_P6R2 q hC1
    hC2 hCtime hanti hcanonical hderivative Tn pT r A hr hA aSeed haT haSeed seedTrace x hx hR hbad
    hdiv
  exact ⟨σ, y, R, hsT, has, L, hmain⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

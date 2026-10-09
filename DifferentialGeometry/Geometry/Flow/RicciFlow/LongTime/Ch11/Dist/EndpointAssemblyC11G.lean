import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointCurvatureC11G
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.LateRecordsSupplyC11G
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.DistanceAssemblyC11D

/-!
# P6 几何输入 G4：装配（O-CH11-P6GEO，后缀 `_C11G`）

G1（端点保护）+ G2（端点 `|Rm|`）+ G3（late records）⇒ DIST G4 的全部几何前提：

* `GeometricCutoffRecord.inv_two_mul_delta_sq_lt_static_scale_C11G`：单 record 的**精细** scale 下界
  `(2 δ(τ)⁴ ρ(τ)²)⁻¹ < scale`（nominal 半径 `< δ² ρ`，比 G1 的 `(2ρ²)⁻¹` 多 `δ⁻⁴`）。
* `exists_hprot_window_C11G`：G1 主装配的**窗口**版——scale 分离只要窗口内事件
  （`s − θ/Q < time e⁺`）`2 max(3/r², B) < scale`。
* **`exists_hgeom_of_K0_pinching_C11G`**（序列层）：G2 的 (i) ∧ (iii) + 窗口 hprot（(ii)，其 slab 标量
  `B = C R_n` 取自同一个 BCAD 形 `hscal` 在 trace 点自身的值）⇒ DIST `hrate_of_endpoint_bounds_C11D`
  的**整个** `hgeom`。
* **`hwit_of_K0_pinching_P5_C11G`**（端到端）：selection 输出（`hgood`、`L_n → ∞`、(D2) `hwin`）+ K0 种子
  （`hasSmallParabolicCurvature`、`aSeed = t − r²`、`2r² < t`、`t_n → ∞`、`R_n r_n² → ∞`）+ BCAD 形 `hscal`
  + pinching（Pre841 native 形）+ P5Linked records + 窗口 scale 分离 `hsep`（`q₀` 的 `δ, ρ, Λ`）+
  `R_n ≥ 1` ⇒ DIST `hwit_of_selection_C11D` 的输出 = P6D2 `false_of_not_good_extendAt_P6D2` 的
  `hwit`（`qs n = 4 R_n`）。

"P6 反证现在只差"清单见 `build-logs/resume/state-O-CH11-P6GEO.md`（HANDOVER）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-! ## 精细 scale 下界与窗口 hprot -/

/-- **单 record 精细 scale 下界（`_C11G`）**：`Λ δ(τ) ≤ 1/2`（`τ = time e⁺`）⇒
`(2 δ(τ)⁴ ρ(τ)²)⁻¹ < static scale`（nominal 半径 `< δ(τ)² ρ(τ)`、`scale ≥ N/2`）。 -/
theorem GeometricCutoffRecord.inv_two_mul_delta_sq_lt_static_scale_C11G
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p)
    (hΛδ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    (b : (H.event i).RetainedBoundaryIndex) :
    (2 * (p.delta (H.time i.succ) ^ 4 * p.neckRadius (H.time i.succ) ^ 2))⁻¹ <
      (R.static b).neck.scale := by
  have hn := R.nominal_small ⟨b.1.1⟩
  have hnpos := R.nominal_pos ⟨b.1.1⟩
  have hNlow : ((p.delta (H.time i.succ) ^ 2 * p.neckRadius (H.time i.succ)) ^ 2)⁻¹ <
      (R.neck b.1.1).scale := by
    rw [R.scale_eq b.1.1]
    exact inv_strictAnti₀ (pow_pos hnpos 2) (pow_lt_pow_left₀ hn hnpos.le two_ne_zero)
  have hNpos : 0 < (R.neck b.1.1).scale := by
    rw [R.scale_eq b.1.1]
    exact inv_pos.mpr (pow_pos hnpos 2)
  have hΛδα : p.recenterConstant * R.delta b.1.1 ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (R.delta_le b.1.1)
      (by linarith [p.recenterConstant_ge_four])).trans hΛδ
  have hhalf : 1 / 2 ≤ (R.static b).neck.scale / (R.neck b.1.1).scale := by
    have := (abs_le.mp ((R.recenter_scale_comparison b).trans hΛδα)).1
    linarith
  have hS : (R.neck b.1.1).scale / 2 ≤ (R.static b).neck.scale := by
    rw [le_div_iff₀ hNpos] at hhalf
    linarith
  have h2 : (2 * (p.delta (H.time i.succ) ^ 4 * p.neckRadius (H.time i.succ) ^ 2))⁻¹ =
      ((p.delta (H.time i.succ) ^ 2 * p.neckRadius (H.time i.succ)) ^ 2)⁻¹ / 2 := by
    ring
  rw [h2]
  linarith

namespace ObservedHistory

/-- **窗口 hprot（`_C11G`）**：G1 `exists_hprot_of_seed_slab_scalar_C11G` 的 scale 分离只在窗口内事件
（`s − θ/Q < time e⁺`）要求 `2 max(3/r², B) < scale_b`。 -/
theorem exists_hprot_window_C11G :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (H : ObservedHistory.{u}) {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T)
        {p : (H.stageAt T).Carrier} {r : ℝ},
        GC.LongTime.hasSmallParabolicCurvature H T p r → (aSeed : ℝ) = (T : ℝ) - r ^ 2 →
        ∀ (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
          (H.activeStage_mono haT) p)
        (y : (H.stageAt s).Carrier) {Q θ Rad T₀ B : ℝ} {q : CutoffParameters}
        (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q),
        (∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
          ((records e he).static b).hasCanonicalWindow) →
        q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder →
        StandardCap.transitionEnd + 10 < q.modelRadius →
        (∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
          (s : ℝ) - θ / Q < H.time e.succ →
          2 * max (3 / r ^ 2) B < ((records e he).static b).neck.scale) →
        (∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
          ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
          ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s)
            (H.activeStage_mono hvs) x,
          ∀ (e : Fin H.eventCount) (h3 : H.activeStage v ≤ e.castSucc)
            (h4 : e.succ ≤ H.activeStage s) (t' : ℝ),
            (v : ℝ) < t' → H.time e.castSucc < t' → t' < H.time e.succ →
            metricScalarAt (H.stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤ B) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
          ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
          ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s)
            (H.activeStage_mono hvs) x,
          ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
            (h2 : e.succ ≤ H.activeStage T) (h3 : H.activeStage v ≤ e.castSucc)
            (h4 : e.succ ≤ H.activeStage s), (v : ℝ) < H.time e.succ →
          ∀ (he : T₀ ≤ H.time e.succ) b,
            seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
                ((records e he).static b).window ''
                  {z : standardCapWindow q.modelRadius |
                    ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
              tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
                ((records e he).static b).window ''
                  {z : standardCapWindow q.modelRadius |
                    ‖z.val‖ ≤ StandardCap.transitionEnd + 10} := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_hprot_of_scalar_lt_C11G.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro H T aSeed s haT p r hsmall hclock seedTrace y Q θ Rad T₀ B q records hcan hacc hm hDm
    hscale hslab
  refine h H haT seedTrace y records hcan hacc hm hDm ?_
  intro x hx v hav hvs hθv tr e h1 h2 h3 h4 hvτ he b
  have hsc := hscale e he b (lt_of_le_of_lt hθv hvτ)
  have hmax1 : 3 / r ^ 2 ≤ max (3 / r ^ 2) B := le_max_left _ _
  have hmax2 : B ≤ max (3 / r ^ 2) B := le_max_right _ _
  have hav' : (aSeed : ℝ) ≤ v := hav
  refine ⟨?_, ?_⟩
  · have hτ1 : aSeed ≤ H.stageTime e.succ := by
      change (aSeed : ℝ) ≤ H.time e.succ
      exact hav'.trans hvτ.le
    have hτ2 : H.stageTime e.succ ≤ T := by
      change H.time e.succ ≤ (T : ℝ)
      exact (H.time_strictMono.monotone h2).trans (H.activeStage_time_le T)
    have hseed := H.seed_scalar_le_of_smallParabolic_C11G haT hsmall hclock seedTrace
      (H.stageTime e.succ) hτ1 hτ2 e.succ (H.activeStage_stageTime e.succ)
      (h1.trans e.castSucc_lt_succ.le) h2
    change metricScalarAt (H.stageMetric e.succ (H.time e.succ)) _ ≤ _ at hseed
    rw [H.stageMetric_succ_time_C11G e] at hseed
    linarith
  · have hpt := H.scalar_succ_le_of_slab_C11G e (tr.crossing e h3 h4) hvτ
      (fun t' h₁ h₂ h₃ => hslab x hx v hav hvs hθv tr e h3 h4 t' h₁ h₂ h₃)
    linarith

end ObservedHistory

/-! ## 序列层：DIST `hgeom` 全体 -/

/-- **DIST `hgeom` 的生产（`_C11G`，序列层）**：存在绝对 `ε₀ > 0`；G2 的输入（K0 种子、`R_n r_n² → ∞`、
`hwin`、`hlate`、pinching、BCAD 形 `hscal`）+ late records（canonical windows、精度 `≤ ε₀`、阶 `≥ 2`、
`transitionEnd + 10 < modelRadius`）+ 窗口 scale 分离 `hsepW`（每个 `C ≥ 0`、`T > 0`）⇒ DIST
`hrate_of_endpoint_bounds_C11D` 的 `hgeom`（(i) ∧ (ii) ∧ (iii)）。 -/
theorem exists_hgeom_of_K0_pinching_C11G :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (Hs : ℕ → ObservedHistory.{u})
      (t : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (p : ∀ n, ((Hs n).stageAt (t n)).Carrier)
      (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haT : ∀ n, aSeed n ≤ t n)
      (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
        ((Hs n).activeStage (t n)) ((Hs n).activeStage_mono (haT n)) (p n))
      (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ t n) (has : ∀ n, aSeed n ≤ s n)
      (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R r : ℕ → ℝ), (∀ᶠ n in atTop, 0 < R n) →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (t n) (p n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (s n : ℝ) - T / R n) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((s n : ℝ) - T / R n)) →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
        InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀ + τ) x) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
        (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
          ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
            τ < s n →
          ∀ z : ((Hs n).stageAt (s n)).Carrier,
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
              ENNReal.ofReal (1 / Real.sqrt (R n)) →
            metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z ≤ C * R n) ∧
        (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
          ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
            (s n : ℝ) - T / R n ≤ v →
          ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
            ((Hs n).activeStage_mono hvs) x,
          ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
            (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
            (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
          ∀ z : ((Hs n).stage e.castSucc).Carrier,
            riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
                (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
              ENNReal.ofReal (1 / Real.sqrt (R n)) →
            metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ C * R n)) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (records : ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
        GeometricCutoffRecord (Hs n) e (q n)),
      (∀ n (e : Fin (Hs n).eventCount) (he : T₀ n ≤ (Hs n).time e.succ) b,
        ((records n e he).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ C : ℝ, 0 ≤ C → ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
        ∀ (e : Fin (Hs n).eventCount) (he : T₀ n ≤ (Hs n).time e.succ) b,
          (s n : ℝ) - T / R n < (Hs n).time e.succ →
          2 * max (3 / r n ^ 2) (C * R n) < ((records n e he).static b).neck.scale) →
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ ℓ K : ℝ, 0 < ℓ ∧ K * ℓ ^ 2 ≤ 1 ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
          τ < s n →
        ∀ z : ((Hs n).stageAt (s n)).Carrier,
          (riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
              ((seedTrace n).point ((Hs n).activeStage (s n))
                ((Hs n).activeStage_mono (has n)) ((Hs n).activeStage_mono (hst n))) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          Real.sqrt (normSq0S ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z 4
            (metricRm04At ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z)) ≤ K * R n) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)), (v : ℝ) < (Hs n).time e.succ →
        ∀ (he : T₀ n ≤ (Hs n).time e.succ) b,
          (seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
              ((records n e he).static b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
            tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
              ((records n e he).static b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
          (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        ∀ z : ((Hs n).stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
          (riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              ((seedTrace n).point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          ricciTensor ((Hs n).stageMetric e.castSucc t') z ξ ξ ≤
            (3 / (ℓ / Real.sqrt (R n)) ^ 2) *
              ((Hs n).stageMetric e.castSucc t').inner z ξ ξ) := by
  obtain ⟨ε₀, hε₀, hP⟩ := ObservedHistory.exists_hprot_window_C11G.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro Hs t p aSeed haT seedTrace s hst has y R r hR hsmall hclock hX hwin hlate a₀ ha₀ hpin
    hscal q T₀ records hcan hacc0 hm hDm hsepW D T hD hT
  obtain ⟨ℓ, K, hℓ, hKℓ, hev⟩ := hgeom_smooth_ric_of_K0_pinching_C11G Hs t p aSeed haT seedTrace
    s hst has y R r hR hsmall hclock hX hwin hlate ha₀ hpin hscal D T hD hT
  obtain ⟨C, hC, hevC⟩ := hscal D T hD hT
  refine ⟨ℓ, K, hℓ, hKℓ, ?_⟩
  filter_upwards [hev, hevC, hsepW C hC T hT, hR] with n hn hnC hsep hRn
  obtain ⟨hi, hiii⟩ := hn
  have hslab : ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
      (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
        ((Hs n).activeStage_mono hvs) x,
      ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
        (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
        (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        metricScalarAt ((Hs n).stageMetric e.castSucc t')
          (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤ C * R n := by
    intro x hx v hav hvs hθv tr e h3 h4 t' ht1 ht2 ht3
    refine hnC.2 x hx v hav hvs hθv tr e h3 h4 t' ht1 ht2 ht3 _ ?_
    rw [riemannianEDistOf_self]
    have := Real.sqrt_pos.2 hRn
    exact ENNReal.ofReal_pos.mpr (by positivity)
  exact ⟨hi, hP (Hs n) (haT n) (hsmall n) (hclock n) (seedTrace n) (y n) (records n) (hcan n)
    (hacc0 n) (hm n) (hDm n) hsep hslab, hiii⟩

/-! ## 端到端：selection + K0 + BCAD + late records ⇒ P6D2 `hwit` -/

/-- **端到端 `hrate`（`_C11G`）**：`Hs n = (F.tower.history (ind n)).toHistory`；K0 种子
（`hasSmallParabolicCurvature`、`aSeed = t − r²`、`2r² < t`、`t_n → ∞`、`R_n r_n² → ∞`）；`R_n ≥ 1`；
(D2) `hwin`；BCAD 形 `hscal`；
pinching `hpin`（Pre841 native 形）；P5Linked records；窗口 scale 分离 `hsep`（`q₀` 的 `Λ, δ, ρ`：
`Λ δ(τ) ≤ 1/2`、`4 max(3/r², C R) δ(τ)⁴ ρ(τ)² ≤ 1`）⇒ DIST G1 形 `hrate`（`hD1_of_stage_bounds_C11D`
与 `hwit_of_selection_C11D` 共用的唯一几何前提）。 -/
theorem hrate_of_K0_pinching_P5_C11G {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q₀ : CutoffParameters}
    (hP5 : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q₀)
    (ind : ℕ → ℕ)
    (Hs : ℕ → ObservedHistory.{u}) (hHs : Hs = fun n => (F.tower.history (ind n)).toHistory)
    (t : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (p : ∀ n, ((Hs n).stageAt (t n)).Carrier)
    (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haT : ∀ n, aSeed n ≤ t n)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (t n)) ((Hs n).activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ t n) (has : ∀ n, aSeed n ≤ s n)
    (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R r : ℕ → ℝ) (hR1 : ∀ᶠ n in atTop, 1 ≤ R n)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (t n) (p n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hlateT : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (hX : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (s n : ℝ) - T / R n)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀ + τ) x)
    (hscal : ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
          τ < s n →
        ∀ z : ((Hs n).stageAt (s n)).Carrier,
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
            ENNReal.ofReal (1 / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z ≤ C * R n) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
          (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        ∀ z : ((Hs n).stage e.castSucc).Carrier,
          riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
            ENNReal.ofReal (1 / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ C * R n))
    (hsep : ∀ C : ℝ, 0 ≤ C → ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      ∀ e : Fin (Hs n).eventCount, (s n : ℝ) - T / R n < (Hs n).time e.succ →
        q₀.recenterConstant * q₀.delta ((Hs n).time e.succ) ≤ 1 / 2 ∧
        4 * max (3 / r n ^ 2) (C * R n) *
          (q₀.delta ((Hs n).time e.succ) ^ 4 * q₀.neckRadius ((Hs n).time e.succ) ^ 2) ≤ 1) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n ≤ τ → (Hs n).time ((Hs n).activeStage (s n)) ≤ τ →
          τ ≤ s n →
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
            ((seedTrace n).point ((Hs n).activeStage (s n)) ((Hs n).activeStage_mono (has n))
              ((Hs n).activeStage_mono (hst n))) x ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
              ((seedTrace n).point ((Hs n).activeStage (s n))
                ((Hs n).activeStage_mono (has n)) ((Hs n).activeStage_mono (hst n))) x +
            ENNReal.ofReal (c * Real.sqrt (R n) * ((s n : ℝ) - τ))) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (τ : ℝ),
          (v : ℝ) ≤ τ → (Hs n).time e.castSucc ≤ τ → τ < (Hs n).time e.succ →
        riemannianEDistOf ((Hs n).stageMetric e.castSucc τ)
            ((seedTrace n).point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2))
            (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤
          riemannianEDistOf ((Hs n).stageMetric e.succ ((Hs n).time e.succ))
              ((seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2)
              (tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4) +
            ENNReal.ofReal (c * Real.sqrt (R n) * ((Hs n).time e.succ - τ))) := by
  subst hHs
  obtain ⟨ε₀, hε₀, hB⟩ := exists_hgeom_of_K0_pinching_C11G.{u}
  obtain ⟨T₀, q, records, hcan, hacc, hacc0, hm, hDm, hpar⟩ :=
    GC.LongTime.Ch11.exists_lateRecords_of_P5Linked_C11G hP5 hε₀
  have hR : ∀ᶠ n in atTop, 0 < R n := hR1.mono fun n h => by linarith
  have hs : Tendsto (fun n => (s n : ℝ)) atTop atTop :=
    GC.LongTime.Ch11.tendsto_s_of_seed_C11G t s aSeed r hlateT htime hclock has
  have hlate := GC.LongTime.Ch11.hlate_of_late_C11G s R hs hR1
  have hT₀ := GC.LongTime.Ch11.hT₀_of_late_C11G s R T₀ hs hR1
  have hsepW : ∀ C : ℝ, 0 ≤ C → ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      ∀ (e : Fin (F.tower.history (ind n)).toHistory.eventCount)
        (he : T₀ ≤ (F.tower.history (ind n)).toHistory.time e.succ) b,
        (s n : ℝ) - T / R n < (F.tower.history (ind n)).toHistory.time e.succ →
        2 * max (3 / r n ^ 2) (C * R n) < ((records (ind n) e he).static b).neck.scale := by
    intro C hC T hT
    filter_upwards [hsep C hC T hT] with n hn e he b hwe
    obtain ⟨hΛδ, hρ⟩ := hn e hwe
    obtain ⟨hδeq, hρeq, hΛeq⟩ := hpar (ind n)
    have hΛδ' : (q (ind n)).recenterConstant *
        (q (ind n)).delta ((F.tower.history (ind n)).toHistory.time e.succ) ≤ 1 / 2 := by
      rw [hδeq, hΛeq]
      exact hΛδ
    have hlow := (records (ind n) e he).inv_two_mul_delta_sq_lt_static_scale_C11G hΛδ' b
    rw [hδeq, hρeq] at hlow
    have hpos : 0 < q₀.delta ((F.tower.history (ind n)).toHistory.time e.succ) ^ 4 *
        q₀.neckRadius ((F.tower.history (ind n)).toHistory.time e.succ) ^ 2 := by
      have ht := (F.tower.history (ind n)).toHistory.time_nonneg e.succ
      have h1 := (q (ind n)).delta_pos _ ht
      have h2 := (q (ind n)).neckRadius_pos _ ht
      rw [hδeq] at h1
      rw [hρeq] at h2
      positivity
    have h2 : 2 * max (3 / r n ^ 2) (C * R n) ≤
        (2 * (q₀.delta ((F.tower.history (ind n)).toHistory.time e.succ) ^ 4 *
          q₀.neckRadius ((F.tower.history (ind n)).toHistory.time e.succ) ^ 2))⁻¹ := by
      rw [← one_div, le_div_iff₀ (by linarith [hpos])]
      linarith
    linarith
  have hgeom := hB (fun n => (F.tower.history (ind n)).toHistory) t p aSeed haT seedTrace s hst
    has y R r hR hsmall hclock hX hwin hlate ha₀ hpin hscal (fun n => q (ind n)) (fun _ => T₀)
    (fun n => records (ind n)) (fun n => hcan (ind n)) (fun n => hacc0 (ind n))
    (fun n => hm (ind n)) (fun n => hDm (ind n)) hsepW
  have hrate := hrate_of_endpoint_bounds_C11D (fun n => (F.tower.history (ind n)).toHistory) t p
    aSeed haT seedTrace s hst has y R hR (fun n => q (ind n)) (fun _ => T₀)
    (fun n => records (ind n)) (fun n e he => (records (ind n) e he).old_eq_retained)
    (fun n => hcan (ind n)) (fun n => hacc (ind n)) (fun n => hDm (ind n)) hT₀ hgeom
  exact hrate

/-- **端到端 `hwit`（`_C11G`）**：`hrate_of_K0_pinching_P5_C11G` 的输入 + selection 末项 `hgood`
（`L_n → ∞`）⇒ DIST `hwit_of_selection_C11D` 的输出（= P6D2 `false_of_not_good_extendAt_P6D2` 的
`hwit`，`qs n = 4 R_n`、`C1s = C1'`、`C2s = C2'`）。 -/
theorem hwit_of_K0_pinching_P5_C11G {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q₀ : CutoffParameters}
    (hP5 : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q₀)
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} (ind : ℕ → ℕ)
    (Hs : ℕ → ObservedHistory.{u}) (hHs : Hs = fun n => (F.tower.history (ind n)).toHistory)
    (t : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (p : ∀ n, ((Hs n).stageAt (t n)).Carrier)
    (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haT : ∀ n, aSeed n ≤ t n)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (t n)) ((Hs n).activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ t n) (has : ∀ n, aSeed n ≤ s n)
    (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R L r : ℕ → ℝ) (hR1 : ∀ᶠ n in atTop, 1 ≤ R n)
    (hL : Tendsto L atTop atTop)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (t n) (p n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hlateT : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (hX : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hgood : ∀ᶠ n in atTop, ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hav : aSeed n ≤ v)
      (hvs : v ≤ s n), (s n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Hs n).stageAt v).Carrier,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedTrace n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hst n)))) z ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
              ((seedTrace n).point ((Hs n).activeStage (s n)) ((Hs n).activeStage_mono (has n))
                ((Hs n).activeStage_mono (hst n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        4 * R n ≤ metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) z →
        (Hs n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (s n : ℝ) - T / R n)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀ + τ) x)
    (hscal : ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
          τ < s n →
        ∀ z : ((Hs n).stageAt (s n)).Carrier,
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
            ENNReal.ofReal (1 / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z ≤ C * R n) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
          (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        ∀ z : ((Hs n).stage e.castSucc).Carrier,
          riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
            ENNReal.ofReal (1 / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ C * R n))
    (hsep : ∀ C : ℝ, 0 ≤ C → ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      ∀ e : Fin (Hs n).eventCount, (s n : ℝ) - T / R n < (Hs n).time e.succ →
        q₀.recenterConstant * q₀.delta ((Hs n).time e.succ) ≤ 1 / 2 ∧
        4 * max (3 / r n ^ 2) (C * R n) *
          (q₀.delta ((Hs n).time e.succ) ^ 4 * q₀.neckRadius ((Hs n).time e.succ) ^ 2) ≤ 1) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ s n), (s n : ℝ) - T / R n ≤ v →
      (v : ℝ) < s n → (Hs n).time ((Hs n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
        ((Hs n).activeStage_mono hvt) x,
        4 * R n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
          (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
        ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) eps C1' C2'
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
          Wt.capTubeHasNeckChart eps := by
  have hR : ∀ᶠ n in atTop, 0 < R n := hR1.mono fun n h => by linarith
  exact hwit_of_selection_C11D Hs t p aSeed haT seedTrace s hst has y R L hR hL hgood hwin
    (hrate_of_K0_pinching_P5_C11G hP5 ind Hs hHs t p aSeed haT seedTrace s hst has y R r hR1
      hsmall hclock htime hlateT hX hwin ha₀ hpin hscal hsep)

/-- **consumer（G4，(D1)）**：同一组输入 + 中心界 `hcenter`（selection 第 8 项）⇒ P6B2
`hdist_fixed_of_D1_P6B2` 的 `hD1`（经 DIST `hD1_of_stage_bounds_C11D`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q₀ : CutoffParameters}
    (hP5 : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q₀)
    {A₀ : ℝ} (ind : ℕ → ℕ)
    (Hs : ℕ → ObservedHistory.{u}) (hHs : Hs = fun n => (F.tower.history (ind n)).toHistory)
    (t : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (p : ∀ n, ((Hs n).stageAt (t n)).Carrier)
    (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haT : ∀ n, aSeed n ≤ t n)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (t n)) ((Hs n).activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ t n) (has : ∀ n, aSeed n ≤ s n)
    (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R r : ℕ → ℝ) (hR1 : ∀ᶠ n in atTop, 1 ≤ R n)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (t n) (p n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hlateT : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (hX : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (s n : ℝ) - T / R n)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀ + τ) x)
    (hscal : ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
          τ < s n →
        ∀ z : ((Hs n).stageAt (s n)).Carrier,
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
            ENNReal.ofReal (1 / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z ≤ C * R n) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
          (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        ∀ z : ((Hs n).stage e.castSucc).Carrier,
          riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
            ENNReal.ofReal (1 / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric e.castSucc t') z ≤ C * R n))
    (hsep : ∀ C : ℝ, 0 ≤ C → ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      ∀ e : Fin (Hs n).eventCount, (s n : ℝ) - T / R n < (Hs n).time e.succ →
        q₀.recenterConstant * q₀.delta ((Hs n).time e.succ) ≤ 1 / 2 ∧
        4 * max (3 / r n ^ 2) (C * R n) *
          (q₀.delta ((Hs n).time e.succ) ^ 4 * q₀.neckRadius ((Hs n).time e.succ) ^ 2) ≤ 1)
    (hcenter : ∀ᶠ n in atTop, y n ∈ riemannianBallOf
      ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
      ((seedTrace n).point ((Hs n).activeStage (s n)) ((Hs n).activeStage_mono (has n))
        ((Hs n).activeStage_mono (hst n))) (A₀ * r n)) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvs : v ≤ s n), (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
        ((Hs n).activeStage_mono hvs) x,
      ∀ hav : aSeed n ≤ v,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedTrace n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hst n))))
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvs)) <
          ENNReal.ofReal (A₀ * r n + C / Real.sqrt (R n)) :=
  hD1_of_stage_bounds_C11D Hs t p r aSeed haT seedTrace s hst has y R
    (hR1.mono fun n h => by linarith) hcenter
    (hrate_of_K0_pinching_P5_C11G hP5 ind Hs hHs t p aSeed haT seedTrace s hst has y R r hR1
      hsmall hclock htime hlateT hX hwin ha₀ hpin hscal hsep)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **consumer（G4）**：pinching 由 `Pre841NativeData_C11K` 的 native `pinching`（`a₀ = pinchingShift`）
供给，喂端到端 `hwit_of_K0_pinching_P5_C11G` 的 `hpin`（类型逐字对上）。 -/
example {Hs : ℕ → ObservedHistory.{u}} (N : Pre841NativeData_C11K Hs) :
    0 ≤ N.pinchingShift ∧
      ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
        DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InFixedHamiltonIveyRegion
          ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (N.pinchingShift + τ) x :=
  ⟨N.pinchingShift_pos.le, fun n τ x => N.pinching n τ x⟩

end GC.LongTime.Ch11

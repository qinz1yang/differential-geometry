import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscalCrossEventP6E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreA1Seq_O45
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.RicciLowerMetricComparison
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.CurvatureOperator

/-!
# traced ball 前向存活的单侧（Ric 下界）版：HI pinching 去掉 `e^{9Kθ}`（J16PT G1，后缀 `_J16`）

P6CE G1 `survives_of_traced_ball_P6E` 的孪生。原件的 ball capture 用双侧 Grönwall
`metric_inner_exp_bounds_of_curvature_bound`，因子 `e^{9Kθ}`；但 capture
（`ball_subset_image_of_metric_lower_on_opens`）只要**单侧** `g(s) ≤ L² g(t')`（前向度量增长上界），
即 **Ric 下界**（`metric_inner_le_exp_mul_of_ricci_lower_bound`）。Ric 下界由 Hamilton–Ivey
pinching 给：`hpinJ`（stage 度量的 fixed HI region，参数 `aP + τ ≥ 1`）+ 允许的 pinching 函数 `Φ`
（`curvatureOperatorLowerBoundAt_of_fixedHI_O16`）+ 拉回自然性
（`curvatureOperatorLowerBoundAt_localPullMetric_iff`）+
`ricci_lower_of_curvatureOperatorLowerBound_O45`，
而 traced region 内 `R ≤ 9K`（`scalar_le_of_normSq_le_P6E`），故 `Ric_S ≥ −3Φ(9K)·g`，
`L = exp(3Φ(9K)θ)`。序列层 `K ↦ K·R n`、`θ ↦ T / R n` 时 `3Φ(9KR)T/R → 0`（`Φ(s)/s → 0`），
L 最终 ≤ 2——这就是 J16 不需要半径一致 `K` 的原因（G2）。
* `survives_of_traced_ball_HI_J16`：结论与 P6CE G1 逐字（因子换成 `L`）。
* `scalar_le_of_twoStep_survival_HI_J16`：P6CE 续 `scalar_le_of_twoStep_survival_PCE` 的同法孪生。
全部 PROVED，无 binder。
-/

set_option autoImplicit false

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **traced ball 的前向存活，单侧版（`_J16`）**：P6CE G1 逐字，`e^{9Kθ}` 换 `L = exp(3Φ(9K)θ)`，
多 HI 前提 `hpinJ`（`[s − θ, s]` 上每个 stage 度量处于参数 `aP + τ` 的 fixed HI region）、
`1 ≤ aP + (s − θ)` 与 `Φ`（`hbound`：`a ≥ 1` 的 HI region 内 `−ν ≤ Φ(R)`）。 -/
theorem survives_of_traced_ball_HI_J16 (H : ObservedHistory.{u})
    (s : Icc (0 : ℝ) H.horizon) (y : (H.stageAt s).Carrier) {ρ θ K r ℓ aP : ℝ}
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ a : ℝ, 1 ≤ a → ∀ R ν : ℝ, (R, ν) ∈ fixedHamiltonIveyRegion a → -ν ≤ Phi R)
    (hpinJ : ∀ (k : Fin (H.eventCount + 1)) (τ : ℝ), τ ∈ H.stageDomain k → (s : ℝ) - θ ≤ τ →
      τ ≤ s → ∀ q : (H.stage k).Carrier,
        InFixedHamiltonIveyRegion (H.stageMetric k τ) (aP + τ) q)
    (haP : 1 ≤ aP + ((s : ℝ) - θ))
    (htr : H.isTracedRegion s y ρ θ K) (hK : 0 ≤ K) (hℓ : 0 < ℓ)
    (hrad : r + Real.exp (3 * Phi (9 * K) * θ) * ℓ ≤ ρ)
    (x : (H.stageAt s).Carrier)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y r)
    (j : Fin (H.eventCount + 1)) (hjs : j ≤ H.activeStage s)
    (tr : BackwardPointTrace H j (H.activeStage s) hjs x)
    (t' : ℝ) (ht'a : (s : ℝ) - θ ≤ t') (ht's : t' ≤ s) (hdom : t' ∈ H.stageDomain j)
    (z : (H.stage j).Carrier)
    (hz : riemannianEDistOf (H.stageMetric j t') (tr.point j le_rfl hjs) z <
      ENNReal.ofReal ℓ) :
    ∃ x' ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y ρ,
      riemannianEDistOf (H.stageMetric (H.activeStage s) s) x x' ≤
        ENNReal.ofReal (Real.exp (3 * Phi (9 * K) * θ) * ℓ) ∧
      ∃ A : BackwardPointTrace H j (H.activeStage s) hjs x', A.point j le_rfl hjs = z ∧
        normSq0S (H.stageMetric j t') z 4 (metricRm04At (H.stageMetric j t') z) ≤ K ^ 2 := by
  classical
  obtain ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm⟩ :=
    H.exists_common_flow_of_isTracedRegion s y htr
  have hat' : (a : ℝ) ≤ t' := by rw [ha]; exact ht'a
  have haj : H.activeStage a ≤ j := H.activeStage_le_of_mem_stageDomain_P6E a hdom hat'
  set δ : ℝ := 3 * Phi (9 * K) with hδdef
  have hδ : 0 ≤ δ := by have := hPhi.pos (9 * K); rw [hδdef]; linarith
  set L : ℝ := Real.exp (δ * θ) with hLdef
  have hL : 0 < L := Real.exp_pos _
  have hLℓ : 0 < L * ℓ := mul_pos hL hℓ
  have hx' : riemannianEDistOf (H.stageMetric (H.activeStage s) s) y x < ENNReal.ofReal r := hx
  have hr : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hx')
  have hxU : x ∈ U := by
    rw [← SetLike.mem_coe, hU]
    change riemannianEDistOf _ y x < ENNReal.ofReal ρ
    exact hx'.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  let pU : U := ⟨x, hxU⟩
  have htraceU : ∀ q : U, ∃ B : BackwardPointTrace H j (H.activeStage s) hjs q.val,
      ∀ (k : Fin (H.eventCount + 1)) (hk1 : j ≤ k) (hk2 : k ≤ H.activeStage s),
        B.point k hk1 hk2 = f ⟨k, haj.trans hk1, hk2⟩ q := by
    intro q
    exact ⟨{ point := fun k hk1 hk2 => f ⟨k, haj.trans hk1, hk2⟩ q
             endpoint_eq := hlast q
             crossing := fun i hi hl => hcross i (haj.trans hi) hl q }, fun _ _ _ => rfl⟩
  let J : H.StageInterval (H.activeStage a) (H.activeStage s) := ⟨j, haj, hjs⟩
  have hfx : f J pU = tr.point j le_rfl hjs := by
    obtain ⟨B, hB⟩ := htraceU pU
    have hBtr : B = tr := Subsingleton.elim _ _
    rw [← hBtr, hB]
  let Jl : H.StageInterval (H.activeStage a) (H.activeStage s) :=
    ⟨H.activeStage s, H.activeStage_mono hat, le_rfl⟩
  have hfl : f Jl = Subtype.val := funext hlast
  have hsdom : (s : ℝ) ∈ H.stageDomain (H.activeStage s) := H.activeStage_mem s
  have hsI : (s : ℝ) ∈ Icc (a : ℝ) s := ⟨hat, le_rfl⟩
  have ht'I : t' ∈ Icc (a : ℝ) s := ⟨hat', ht's⟩
  -- Ric 下界：`Ric_S(τ) ≥ −δ·S(τ)` on `(t', s)`
  have hRic : ∀ q : U, ∀ v : TangentSpace ThreeModel q, ∀ τ ∈ Ioo t' (s : ℝ),
      -δ * (S.base.metric τ).inner q v v ≤ S.ricciAt τ q (vec2 v v) := by
    intro q v τ hτ
    have hτI : τ ∈ Icc (a : ℝ) s := ⟨hat'.trans hτ.1.le, hτ.2.le⟩
    let τI : Icc (0 : ℝ) H.horizon := ⟨τ, a.2.1.trans hτI.1, hτI.2.trans s.2.2⟩
    have haτ : a ≤ τI := hτI.1
    have hτs : τI ≤ s := hτI.2
    let Jτ : H.StageInterval (H.activeStage a) (H.activeStage s) :=
      ⟨H.activeStage τI, H.activeStage_mono haτ, H.activeStage_mono hτs⟩
    have hdτ : τ ∈ H.stageDomain (H.activeStage τI) := H.activeStage_mem τI
    have hm := hmetric Jτ τ hτI hdτ
    have hHI := hpinJ (H.activeStage τI) τ hdτ (by linarith [hτ.1]) hτ.2.le (f Jτ q)
    have hlowg := GC.LongTime.Ch12.curvatureOperatorLowerBoundAt_of_fixedHI_O16 hPhi hbound
      (H.stageMetric (H.activeStage τI) τ) (by linarith [hτ.1]) (f Jτ q) hHI
    have hlowS := (curvatureOperatorLowerBoundAt_localPullMetric_iff
      (H.stageMetric (H.activeStage τI) τ) (f Jτ) (hf Jτ) q _).mpr hlowg
    have hP0 := (hPhi.pos (metricScalarAt (H.stageMetric (H.activeStage τI) τ) (f Jτ q))).le
    have hric := GC.LongTime.Ch12.ricci_lower_of_curvatureOperatorLowerBound_O45 _ q hP0 hlowS v
    have hfin : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by simp [ThreeSpace]
    rw [hfin] at hric
    -- `R(f q) ≤ 9K`
    have h1 := hRm τ hτI q
    have hrm : S.base.rm04 τ q = metricRm04At (S.base.metric τ) q := metricRm04_apply _ _
    rw [hrm, hm, normSq0S_metricRm04At_localPullMetric] at h1
    have hsc := scalar_le_of_normSq_le_P6E (H.stageMetric (H.activeStage τI) τ) (f Jτ q) h1
    rw [abs_of_nonneg hK] at hsc
    have hPm := hPhi.mono hsc
    have hin : 0 ≤ (S.base.metric τ).inner q v v := metric_inner_self_nonneg _ _ _
    have hSr : S.ricciAt τ q (vec2 v v) = ricciTensor (S.base.metric τ) q v v :=
      metricRicciAt_apply_eq_ricciTensor _ _ _ _
    rw [hSr, hm]
    rw [hm] at hin
    have hmul := mul_le_mul_of_nonneg_right hPm hin
    nlinarith
  have hexp : ∀ τ ∈ Icc t' (s : ℝ), Real.exp (2 * δ * ((s : ℝ) - t')) ≤ L ^ 2 := by
    intro _ _
    rw [hLdef, sq, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : (s : ℝ) - t' ≤ θ := by linarith
    nlinarith
  have hcarr : Icc t' (s : ℝ) ⊆ (RealTimeInterval.closed (a : ℝ) s hat).carrier :=
    fun _ h => ⟨hat'.trans h.1, h.2⟩
  have hregl : Ioo t' (s : ℝ) ⊆ (RealTimeInterval.closed (a : ℝ) s hat).regular :=
    fun _ h => ⟨lt_of_le_of_lt hat' h.1, h.2⟩
  have hlower : ∀ q : U,
      q.val ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage s) s) pU.val (L * ℓ) →
      ∀ v : TangentSpace ThreeModel q,
        (H.stageMetric (H.activeStage s) s).inner q.val v v ≤
          L ^ 2 * (H.stageMetric j t').inner (f J q)
            (mfderiv ThreeModel ThreeModel (f J) q v)
            (mfderiv ThreeModel ThreeModel (f J) q v) := by
    intro q _ v
    have hb := metric_inner_le_exp_mul_of_ricci_lower_bound S hS ht's hcarr hregl q v
      (fun τ hτ => hRic q v τ hτ)
    rw [hmetric Jl s hsI hsdom, hmetric J t' ht'I hdom, localPullMetric_inner,
      localPullMetric_inner, hfl, mfderiv_subtype_val_apply] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (hexp s ⟨ht's, le_rfl⟩)
      (metric_inner_self_nonneg _ _ _))
  have hcompact : IsCompact
      (riemannianClosedBallOf (H.stageMetric (H.activeStage s) s) pU.val (L * ℓ)) :=
    (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _).isCompact
  have hsource : riemannianClosedBallOf (H.stageMetric (H.activeStage s) s) pU.val (L * ℓ) ⊆
      (U : Set (H.stageAt s).Carrier) := by
    intro w hw
    rw [hU]
    have hw' : riemannianEDistOf (H.stageMetric (H.activeStage s) s) x w ≤
        ENNReal.ofReal (L * ℓ) := hw
    change riemannianEDistOf _ y w < ENNReal.ofReal ρ
    calc riemannianEDistOf (H.stageMetric (H.activeStage s) s) y w
        ≤ riemannianEDistOf (H.stageMetric (H.activeStage s) s) y x +
          riemannianEDistOf (H.stageMetric (H.activeStage s) s) x w :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal r + ENNReal.ofReal (L * ℓ) :=
          ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hw') hx' hw'
      _ = ENNReal.ofReal (r + L * ℓ) := (ENNReal.ofReal_add hr.le hLℓ.le).symm
      _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal hrad
  have hcap := Geometry.Metric.ball_subset_image_of_metric_lower_on_opens
    (H.stageMetric j t') (H.stageMetric (H.activeStage s) s) U (f J) (hf J) (hinj J) pU
    hLℓ hL hcompact hsource hlower
  have hdiv : L * ℓ / L = ℓ := by field_simp
  rw [hdiv, hfx] at hcap
  obtain ⟨q, hq, hqz⟩ := hcap hz
  obtain ⟨B, hB⟩ := htraceU q
  refine ⟨q.val, ?_, hq, B, ?_, ?_⟩
  · have hqU := q.property
    rw [← SetLike.mem_coe, hU] at hqU
    exact hqU
  · rw [hB]
    exact hqz
  · have h1 := hRm t' ht'I q
    have hrm : S.base.rm04 t' q = metricRm04At (S.base.metric t') q := metricRm04_apply _ _
    rw [hrm, hmetric J t' ht'I hdom, normSq0S_metricRm04At_localPullMetric, hqz] at h1
    exact h1

/-- **两步 survival ⇒ 标量界，单侧版（`_J16`）**：`scalar_le_of_twoStep_survival_PCE` 同法，
覆盖条件 `r + L ℓ₁ + L ℓ₂ ≤ ρ`，`L = exp(3Φ(9K)θ)`；`v, τ ∈ [σ − θ, σ]` 同在 slab `j`，
`d_v(tr.point, x) < ℓ₁`、`d_τ(x, z) < ℓ₂` ⇒ `R(τ, z) ≤ 9K`。 -/
theorem scalar_le_of_twoStep_survival_HI_J16 (H : ObservedHistory.{u})
    (σ : Icc (0 : ℝ) H.horizon) (y : (H.stageAt σ).Carrier) {ρ θ K r ℓ₁ ℓ₂ aP : ℝ}
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ a : ℝ, 1 ≤ a → ∀ R ν : ℝ, (R, ν) ∈ fixedHamiltonIveyRegion a → -ν ≤ Phi R)
    (hpinJ : ∀ (k : Fin (H.eventCount + 1)) (τ : ℝ), τ ∈ H.stageDomain k → (σ : ℝ) - θ ≤ τ →
      τ ≤ σ → ∀ q : (H.stage k).Carrier,
        InFixedHamiltonIveyRegion (H.stageMetric k τ) (aP + τ) q)
    (haP : 1 ≤ aP + ((σ : ℝ) - θ))
    (htr : H.isTracedRegion σ y ρ θ K) (hK : 0 ≤ K) (hℓ₁ : 0 < ℓ₁) (hℓ₂ : 0 < ℓ₂)
    (hrad : r + Real.exp (3 * Phi (9 * K) * θ) * ℓ₁ +
      Real.exp (3 * Phi (9 * K) * θ) * ℓ₂ ≤ ρ)
    (x₁ : (H.stageAt σ).Carrier)
    (hx₁ : x₁ ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y r)
    (j : Fin H.eventCount) (hjσ : j.castSucc ≤ H.activeStage σ)
    (tr : BackwardPointTrace H j.castSucc (H.activeStage σ) hjσ x₁)
    (v : ℝ) (hvθ : (σ : ℝ) - θ ≤ v) (hvσ : v ≤ σ) (hv1 : H.time j.castSucc ≤ v)
    (hv2 : v < H.time j.succ) (x : (H.stage j.castSucc).Carrier)
    (hx : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
      (tr.point j.castSucc le_rfl hjσ) x < ENNReal.ofReal ℓ₁)
    (τ : ℝ) (hτθ : (σ : ℝ) - θ ≤ τ) (hτσ : τ ≤ σ) (hτ1 : H.time j.castSucc ≤ τ)
    (hτ2 : τ < H.time j.succ) (z : (H.stage j.castSucc).Carrier)
    (hz : riemannianEDistOf ((H.event j).incoming.flow.base.metric τ) x z < ENNReal.ofReal ℓ₂) :
    (H.event j).incoming.flow.scalar τ z ≤ 9 * K := by
  set L : ℝ := Real.exp (3 * Phi (9 * K) * θ) with hLdef
  have hL : 0 < L := Real.exp_pos _
  have hdomv : v ∈ H.stageDomain j.castSucc := by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show v ∈ Ico (H.time j.castSucc) (H.time j.succ) from ⟨hv1, hv2⟩)
  have hdomτ : τ ∈ H.stageDomain j.castSucc := by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show τ ∈ Ico (H.time j.castSucc) (H.time j.succ) from ⟨hτ1, hτ2⟩)
  have hx' : riemannianEDistOf (H.stageMetric j.castSucc v) (tr.point j.castSucc le_rfl hjσ) x <
      ENNReal.ofReal ℓ₁ := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hx
  have hrad1 : r + L * ℓ₁ ≤ ρ := by nlinarith [mul_pos hL hℓ₂]
  obtain ⟨x', -, hxx', A, hA, -⟩ := H.survives_of_traced_ball_HI_J16 σ y hPhi hbound hpinJ haP
    htr hK hℓ₁ hrad1 x₁ hx₁ j.castSucc hjσ tr v hvθ hvσ hdomv x hx'
  have hr : 0 ≤ r := by
    have h0 : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) y x₁ < ENNReal.ofReal r := hx₁
    by_contra hneg
    rw [ENNReal.ofReal_of_nonpos (by linarith)] at h0
    exact (ENNReal.not_lt_zero h0).elim
  have hx'r : x' ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (r + L * ℓ₁) := by
    change riemannianEDistOf _ y x' < ENNReal.ofReal (r + L * ℓ₁)
    have h0 : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) y x₁ < ENNReal.ofReal r := hx₁
    calc riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) y x'
        ≤ riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) y x₁ +
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) x₁ x' :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal r + ENNReal.ofReal (L * ℓ₁) :=
          ENNReal.add_lt_add_of_lt_of_le
            (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxx') h0 hxx'
      _ = ENNReal.ofReal (r + L * ℓ₁) := (ENNReal.ofReal_add hr (mul_pos hL hℓ₁).le).symm
  have hrad2 : r + L * ℓ₁ + L * ℓ₂ ≤ ρ := hrad
  have hz' : riemannianEDistOf (H.stageMetric j.castSucc τ) (A.point j.castSucc le_rfl hjσ) z <
      ENNReal.ofReal ℓ₂ := by
    rw [hA, ObservedHistory.stageMetric_castSucc_apply]
    exact hz
  obtain ⟨-, -, -, -, -, hRm⟩ := H.survives_of_traced_ball_HI_J16 σ y hPhi hbound hpinJ haP htr
    hK hℓ₂ hrad2 x' hx'r j.castSucc hjσ A τ hτθ hτσ hdomτ z hz'
  have h := scalar_le_of_normSq_le_P6E (H.stageMetric j.castSucc τ) z hRm
  rw [abs_of_nonneg hK, ObservedHistory.stageMetric_castSucc_apply] at h
  exact h

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

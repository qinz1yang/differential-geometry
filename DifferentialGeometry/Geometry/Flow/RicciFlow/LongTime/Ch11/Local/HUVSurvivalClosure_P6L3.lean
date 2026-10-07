import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HUVKappaClosure_P6L3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TracedBallSurvivalP6E

/-!
# seed closure 的 survival 生产（单 history；O-CH11-P6ANCH3 G2b，后缀 `_P6L3`）

`hclosC`（`P6HUVCondP6M3` 的剩余 binder）在**覆盖**前提下的单点生产：traced region `(ρ, θ, K)` 于 `(σ, y)`、
基点 `x₁ ∈ B_σ(y, r)`、`r + e^{9Kθ} ℓ ≤ ρ`；`x` 在 slab `j`、时刻 `v` 离 trace 点 `tr.point j` 不足 `ℓ`
⇒ P6CE `survives_of_traced_ball_P6E`：`x` 是某 `x' ∈ B_σ(y, ρ)` 的 trace 在 stage `j` 的点 ⇒ 相对 `hdist`
（radius `ρ`、窗口 `θ`，HDISTC `hdistC` 的单 history 体）在同 slab 的任一 `τ` 上给
`d_τ(O_j, x) ≤ d_σ + L/√R`（同 slab 内 trace 点 = `x`，不随 `τ` 变）。
* `exists_trace_of_eq_first_P6L3`：trace 首指标等式搬运（`HEq` 点）；
* **`seed_closure_of_survival_P6L3`**：上述单点 closure。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

universe u

/-- trace 首指标等式搬运（`_P6L3`）。 -/
theorem exists_trace_of_eq_first_P6L3 (H : ObservedHistory.{u})
    {f f' l : Fin (H.eventCount + 1)} (h : f = f') (hle : f ≤ l) (hle' : f' ≤ l)
    {x : (H.stage l).Carrier} (A : BackwardPointTrace H f l hle x) :
    ∃ A' : BackwardPointTrace H f' l hle' x,
      HEq (A'.point f' le_rfl hle') (A.point f le_rfl hle) := by
  subst h
  exact ⟨A, HEq.rfl⟩

/-- **seed closure ⇐ survival + 相对 hdist（单 history，`_P6L3`）**。 -/
theorem seed_closure_of_survival_P6L3 (H : ObservedHistory.{u})
    {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (y : (H.stageAt σ).Carrier) {R L ρ θ K r ℓ : ℝ}
    (htr : H.isTracedRegion σ y ρ θ K) (hK : 0 ≤ K) (hℓ : 0 < ℓ)
    (hrad : r + Real.exp (9 * K * θ) * ℓ ≤ ρ)
    (hdist : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y ρ,
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ), (σ : ℝ) - θ ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage σ) (H.activeStage_mono hvs) x,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT)))
            (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R))
    (x₁ : (H.stageAt σ).Carrier)
    (hx₁ : x₁ ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y r)
    (j : Fin H.eventCount) (hjσ : j.castSucc ≤ H.activeStage σ)
    (tr : BackwardPointTrace H j.castSucc (H.activeStage σ) hjσ x₁)
    (v : ℝ) (hvθ : (σ : ℝ) - θ ≤ v) (hvσ : v ≤ σ) (hv1 : H.time j.castSucc ≤ v)
    (hv2 : v < H.time j.succ) (x : (H.stage j.castSucc).Carrier)
    (hx : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
      (tr.point j.castSucc le_rfl hjσ) x < ENNReal.ofReal ℓ)
    (τ : ℝ) (hτθ : (σ : ℝ) - θ ≤ τ) (hτσ : τ ≤ σ) (hτ1 : H.time j.castSucc < τ)
    (hτ2 : τ < H.time j.succ) (haτ : (aSeed : ℝ) ≤ τ)
    (h1 : H.activeStage aSeed ≤ j.castSucc) (h2 : j.castSucc ≤ H.activeStage Tn) :
    riemannianEDistOf ((H.event j).incoming.flow.base.metric τ)
        (seedTrace.point j.castSucc h1 h2) x ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R) := by
  have hdom : v ∈ H.stageDomain j.castSucc := by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show v ∈ Ico (H.time j.castSucc) (H.time j.succ) from ⟨hv1, hv2⟩)
  have hz : riemannianEDistOf (H.stageMetric j.castSucc v) (tr.point j.castSucc le_rfl hjσ) x <
      ENNReal.ofReal ℓ := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hx
  obtain ⟨x', hx', -, A, hA, -⟩ := H.survives_of_traced_ball_P6E σ y htr hK hℓ hrad x₁ hx₁
    j.castSucc hjσ tr v hvθ hvσ hdom x hz
  have h0 : (0 : ℝ) ≤ τ := (H.time_nonneg _).trans hτ1.le
  let τI : Icc (0 : ℝ) H.horizon := ⟨τ, h0, hτσ.trans σ.2.2⟩
  have hact : H.activeStage τI = j.castSucc := H.activeStage_eq_of_slab_P6L3 j τI hτ1.le hτ2
  have hav : aSeed ≤ τI := haτ
  have hvs : τI ≤ σ := hτσ
  obtain ⟨A', hA'⟩ := exists_trace_of_eq_first_P6L3 H hact.symm hjσ (H.activeStage_mono hvs) A
  have hs := point_heq_of_eq_P6M2 seedTrace hact (H.activeStage_mono hav)
    (H.activeStage_mono (hvs.trans hsT)) h1 h2
  have hpt : HEq (A'.point (H.activeStage τI) le_rfl (H.activeStage_mono hvs)) x :=
    hA'.trans (heq_of_eq hA)
  have h := hdist x' hx' τI hav hvs hτθ A'
  rw [edist_stage_eq_P6L2 j hact τ _ _ _ x hs hpt] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

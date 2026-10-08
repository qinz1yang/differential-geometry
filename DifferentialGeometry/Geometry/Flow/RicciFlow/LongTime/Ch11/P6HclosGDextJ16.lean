import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgapJ16DextJ16
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HUVSurvivalClosure_P6L3

/-!
# hclosG ⇐ 条件形 `hdistC` + `hDext` + HI，去 `huni`（J16PT G4，后缀 `_J16`）

O-CH11-HCLOSC 缺口见证 `hclosG_of_cover_uniformK_P6HC`（P6HclosCCondP6HC）的孪生：内联假设 `huni`
（半径一致 K）换成 hPN 中心 driver 输出 `hDext`（`∀ φ ∃ ψ ∀ T, DepthExtendable`，`∀ A ∃ K(A)`）+ `hpin`
（fixed HI，参数 `aP n + s`）+ `n + 1 ≤ R n`、`1 ≤ aSeed n`。结论（NotKBody:196 `hclosG` 体）与
`hdistC` 前提逐字（生成器 `build-logs/scratch/J16PT/gen/gen_g4.py` 从源切片并 assert）。
* `seed_closure_of_survival_HI_J16`：`seed_closure_of_survival_P6L3` 孪生，survival 换 G1
  `survives_of_traced_ball_HI_J16`（覆盖因子 `exp(3Φ(9K)θ)`）。
* **`hclosG_of_depthExt_HI_J16`**：半径 `D := Dw + 2(Dd + max Rad 0) + 1`、深度 `θb := max B 0 − σ₁ + 1`
  先定，再由 `hDext` 取 `K(2D)`；`eventually_exp_le_two_J16` 给因子 ≤ 2，覆盖 `Dw + 2(Dd + max Rad 0) ≤ D`
  与 K 无关；`hdistC`（余量 `L/4`）在 `(D, θb, K)` 处给 footprint，`L ≥ 0` eventually 放宽到 `L`；
  子列 → `∀ᶠ` 由 `exists_const_eventually_of_subseq_P6AN`（常数无关的 P）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **seed closure ⇐ 单侧 survival + 相对 hdist（单 history，`_J16`）**：`seed_closure_of_survival_P6L3`
逐字，覆盖条件 `r + exp(3Φ(9K)θ) ℓ ≤ ρ`，多 HI 前提（同 G1）。 -/
theorem seed_closure_of_survival_HI_J16 (H : ObservedHistory.{u})
    {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (y : (H.stageAt σ).Carrier) {R L ρ θ K r ℓ aP : ℝ}
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ a : ℝ, 1 ≤ a → ∀ R ν : ℝ, (R, ν) ∈ fixedHamiltonIveyRegion a → -ν ≤ Phi R)
    (hpinJ : ∀ (k : Fin (H.eventCount + 1)) (τ : ℝ), τ ∈ H.stageDomain k → (σ : ℝ) - θ ≤ τ →
      τ ≤ σ → ∀ q : (H.stage k).Carrier,
        InFixedHamiltonIveyRegion (H.stageMetric k τ) (aP + τ) q)
    (haP : 1 ≤ aP + ((σ : ℝ) - θ))
    (htr : H.isTracedRegion σ y ρ θ K) (hK : 0 ≤ K) (hℓ : 0 < ℓ)
    (hrad : r + Real.exp (3 * Phi (9 * K) * θ) * ℓ ≤ ρ)
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
  obtain ⟨x', hx', -, A, hA, -⟩ := H.survives_of_traced_ball_HI_J16 σ y hPhi hbound hpinJ haP htr
    hK hℓ hrad x₁ hx₁ j.castSucc hjσ tr v hvθ hvσ hdom x hz
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

/-- **hclosG ⇐ `hdistC` + `hDext` + HI（`_J16`，PROVED 相对 `hdistC`、`hDext`、`hpin`）**：结论 =
NotKBody `hclosG` 体逐字（= `hclosG_of_cover_uniformK_P6HC` 结论）；不需要 `huni`。 -/
theorem ObservedHistory.hclosG_of_depthExt_HI_J16 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (hR : ∀ n, 0 < R n) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hRr : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n) (ha1 : ∀ n, 1 ≤ (aSeed n : ℝ))
    (aP : ℕ → ℝ) (haP : ∀ n, 0 ≤ aP n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s) (aP n + s) x)
    (hDext : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R (φ ∘ ψ) T) :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
        ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
        ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
          (Kh n).time j'.castSucc < τ →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro Rad B σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  obtain ⟨Phi, hPhi, hbound⟩ :=
    Perelman.exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion
      (a₀ := 1) one_pos
  have hM : 0 ≤ max Rad 0 := le_max_right _ _
  have hθ : 0 < max B 0 - σ₁ + 1 := by linarith [le_max_right B 0]
  set θb : ℝ := max B 0 - σ₁ + 1 with hθbdef
  set D : ℝ := Dw + 2 * (Dd + max Rad 0) + 1 with hDdef
  have hD : 0 < D := by rw [hDdef]; linarith
  obtain ⟨C₀, -, hfin⟩ := exists_const_eventually_of_subseq_P6AN (P := fun n (_ : ℝ) =>
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
          v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
          (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
        ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
          (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              ((seedTrace n).point j'.castSucc h1 h2) w ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
              (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
          ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
            (Kh n).time j'.castSucc < τ →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n))) (by
    intro φ hφ
    obtain ⟨ψ, hψ, hdx⟩ := hDext φ hφ
    obtain ⟨K, hK, htr⟩ := hdx θb hθ (2 * D) (by positivity)
    have hφψ : Tendsto (φ ∘ ψ) atTop atTop := (hφ.comp hψ).tendsto_atTop
    have htr' : ∀ᶠ n in map (φ ∘ ψ) atTop, (Kh n).isTracedRegion (σ n) (y n)
        (2 * D / Real.sqrt (R n)) (θb / R n) (K * R n) := Filter.eventually_map.mpr htr
    have hfoot := hdistC (φ ∘ ψ) (hφ.comp hψ) D θb K hD hθ hK htr'
    have hE := (ObservedHistory.eventually_exp_le_two_J16 hPhi R hRr hK hθ).filter_mono hφψ
    have hW := (hwin θb hθ).filter_mono hφψ
    have hL0 := (hL.eventually_ge_atTop 0).filter_mono hφψ
    refine ⟨ψ, hψ, 1, ?_⟩
    change ∀ᶠ m in map (φ ∘ ψ) atTop, (fun n => ∀ C : ℝ, 1 ≤ C →
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
          v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
          (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
        ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
          (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              ((seedTrace n).point j'.castSucc h1 h2) w ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
              (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
          ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
            (Kh n).time j'.castSucc < τ →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n))) m
    filter_upwards [htr', hfoot, hE, hW, hL0] with n htri hfi hEi hWi hLi
    intro _ _ j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w _hwseed hwnear hRw x hx τ hτ hτv
      hτ1
    have hRn := hR n
    have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
    have hRw0 : 0 < ((Kh n).event j').incoming.flow.scalar v w := hRn.trans_le hRw
    have hℓ : 0 < (Dd + max Rad 0) / Real.sqrt (R n) := div_pos (by linarith) hsR
    have hrad' : Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w) ≤
        max Rad 0 / Real.sqrt (R n) :=
      (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
        (div_le_div_of_nonneg_left hM hsR (Real.sqrt_le_sqrt hRw))
    have hzx : riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
        (tr.point j'.castSucc le_rfl hjσ) x <
          ENNReal.ofReal ((Dd + max Rad 0) / Real.sqrt (R n)) :=
      calc riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) x
          ≤ riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              (tr.point j'.castSucc le_rfl hjσ) w +
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v) w x :=
            riemannianEDistOf_triangle _ _ _ _
        _ < ENNReal.ofReal (Dd / Real.sqrt (R n)) +
              ENNReal.ofReal (max Rad 0 / Real.sqrt (R n)) :=
            ENNReal.add_lt_add hwnear (lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal hrad'))
        _ = ENNReal.ofReal ((Dd + max Rad 0) / Real.sqrt (R n)) := by
            rw [← ENNReal.ofReal_add (div_nonneg hDd.le hsR.le) (div_nonneg hM hsR.le),
              ← add_div]
    have hB : B / ((Kh n).event j').incoming.flow.scalar v w ≤ max B 0 / R n :=
      (div_le_div_of_nonneg_right (le_max_left _ _) hRw0.le).trans
        (div_le_div_of_nonneg_left (le_max_right _ _) hRn hRw)
    have hθR : θb / R n = max B 0 / R n - σ₁ / R n + 1 / R n := by
      rw [hθbdef]
      ring
    have h1R : 0 < 1 / R n := one_div_pos.2 hRn
    have hB0 : 0 ≤ max B 0 / R n := div_nonneg (le_max_right _ _) hRn.le
    have hvθ : (σ n : ℝ) - θb / R n ≤ v := by linarith
    have hτθ : (σ n : ℝ) - θb / R n ≤ τ := by linarith
    have hvσ : v ≤ (σ n : ℝ) := by
      have : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
      linarith
    have hpinJ : ∀ (k : Fin ((Kh n).eventCount + 1)) (t : ℝ), t ∈ (Kh n).stageDomain k →
        (σ n : ℝ) - θb / R n ≤ t → t ≤ σ n → ∀ q : ((Kh n).stage k).Carrier,
          InFixedHamiltonIveyRegion ((Kh n).stageMetric k t) (aP n + t) q := by
      intro k t hdom htθ htσ q
      have h1n := ha1 n
      let tI : Icc (0 : ℝ) (Kh n).horizon := ⟨t, by linarith, htσ.trans (σ n).2.2⟩
      have hk : (Kh n).activeStage tI = k := ((Kh n).mem_stageDomain_iff tI k).mp hdom
      subst hk
      exact hpin n tI q
    have haP' : 1 ≤ aP n + ((σ n : ℝ) - θb / R n) := by linarith [haP n, ha1 n]
    have hDM : 0 ≤ (Dd + max Rad 0) / Real.sqrt (R n) := hℓ.le
    have hrad : Dw / Real.sqrt (R n) +
        Real.exp (3 * Phi (9 * (K * R n)) * (θb / R n)) * ((Dd + max Rad 0) / Real.sqrt (R n)) ≤
        D / Real.sqrt (R n) := by
      have e1 := mul_le_mul_of_nonneg_right hEi hDM
      have e3 : Dw / Real.sqrt (R n) + 2 * ((Dd + max Rad 0) / Real.sqrt (R n)) +
          1 / Real.sqrt (R n) = D / Real.sqrt (R n) := by rw [hDdef]; ring
      have e4 : 0 ≤ 1 / Real.sqrt (R n) := div_nonneg zero_le_one hsR.le
      linarith
    have htrD : (Kh n).isTracedRegion (σ n) (y n) (D / Real.sqrt (R n)) (θb / R n) (K * R n) :=
      htri.mono_radius (div_pos hD hsR) (div_le_div_of_nonneg_right (by linarith) hsR.le)
    have hcl := seed_closure_of_survival_HI_J16 (Kh n) (haT n) (hsT n) (has n) (seedTrace n)
      (y n) hPhi hbound hpinJ haP' htrD (mul_nonneg hK hRn.le) hℓ hrad hfi x₁ hx₁ j' hjσ tr v
      hvθ hvσ hv1.le hv2 x hzx τ hτθ (hτv.trans hvσ) hτ1 (lt_of_le_of_lt hτv hv2)
      (hWi.trans hτθ) h1 h2
    refine hcl.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
    exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
  exact hfin

/-- consumer：`hclosG_of_depthExt_HI_J16` 的结论在具体参数处 eventually 成立 ⇒ 存在这样的 `n`。 -/
example (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (hR : ∀ n, 0 < R n) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hRr : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n) (ha1 : ∀ n, 1 ≤ (aSeed n : ℝ))
    (aP : ℕ → ℝ) (haP : ∀ n, 0 ≤ aP n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s) (aP n + s) x)
    (hDext : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R (φ ∘ ψ) T) :
    ∃ n : ℕ, 0 ≤ n := by
  obtain ⟨n, -⟩ := (ObservedHistory.hclosG_of_depthExt_HI_J16 Kh Tn aSeed σ haT hsT has pT seedTrace
    y R L hR hL hwin hdistC hRr ha1 aP haP hpin hDext 1 1 (-1) (-1) le_rfl (by norm_num) 1 1
    one_pos one_pos).exists
  exact ⟨n, n.zero_le⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

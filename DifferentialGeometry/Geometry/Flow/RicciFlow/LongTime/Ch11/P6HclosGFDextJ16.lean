import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HclosGDextJ16

/-!
# final 帧 hclosGF ⇐ `hdistQ` + `hDext` + HI（J16PT G5a，后缀 `_J16`）

KT2c final producer（P6GapProducersFinalLocP6KT2c）`hOpenFJ` / `hOpenF8J` 的 `hclosGF` 合取（final slab
`Fin.last` 上的 seed closure）⇐ 同一 binder 的 `hdistQ` 合取（∀ D T，余量 `L/4`）+ hPN 中心 driver 输出
`hDext` + `hpin`。证明同 G4（`hclosG_of_depthExt_HI_J16`），stage 换 `Fin.last`（stageDomain = `Icc`）。
陈述文本由生成器 `build-logs/scratch/J16PT/gen/gen_g5.py` 从源 binder 切片（括号配平 + assert）。
* `edist_stage_heq_J16`：stage 指标相等 + HEq 点 ⇒ 距离相等（通用搬运）。
* `seed_closure_final_of_survival_HI_J16`：final slab 单 history closure。
* **`hclosGF_of_depthExt_HI_J16`**：结论 = `hclosGF` 合取逐字。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- stage 指标相等 + HEq 点 ⇒ 同一时刻距离相等（`_J16`）。 -/
theorem edist_stage_heq_J16 (H : ObservedHistory.{u}) {k k' : Fin (H.eventCount + 1)} (h : k = k')
    (t : ℝ) (a b : (H.stage k).Carrier) (a' b' : (H.stage k').Carrier) (ha : HEq a a')
    (hb : HEq b b') :
    riemannianEDistOf (H.stageMetric k t) a b = riemannianEDistOf (H.stageMetric k' t) a' b' := by
  subst h
  cases ha
  cases hb
  rfl

/-- **final slab seed closure ⇐ 单侧 survival + 相对 hdist（单 history，`_J16`）**。 -/
theorem seed_closure_final_of_survival_HI_J16 (H : ObservedHistory.{u})
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
    (hjσ : Fin.last H.eventCount ≤ H.activeStage σ)
    (tr : BackwardPointTrace H (Fin.last H.eventCount) (H.activeStage σ) hjσ x₁)
    (v : ℝ) (hvθ : (σ : ℝ) - θ ≤ v) (hvσ : v ≤ σ) (hv1 : H.time (Fin.last H.eventCount) ≤ v)
    (x : (H.stage (Fin.last H.eventCount)).Carrier)
    (hx : riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) v)
      (tr.point (Fin.last H.eventCount) le_rfl hjσ) x < ENNReal.ofReal ℓ)
    (τ : ℝ) (hτθ : (σ : ℝ) - θ ≤ τ) (hτσ : τ ≤ σ) (hτ1 : H.time (Fin.last H.eventCount) < τ)
    (haτ : (aSeed : ℝ) ≤ τ)
    (h1 : H.activeStage aSeed ≤ Fin.last H.eventCount)
    (h2 : Fin.last H.eventCount ≤ H.activeStage Tn) :
    riemannianEDistOf (H.stageMetric (Fin.last H.eventCount) τ)
        (seedTrace.point (Fin.last H.eventCount) h1 h2) x ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R) := by
  have hdom : v ∈ H.stageDomain (Fin.last H.eventCount) := by
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last]
    exact ⟨hv1, hvσ.trans σ.2.2⟩
  obtain ⟨x', hx', -, A, hA, -⟩ := H.survives_of_traced_ball_HI_J16 σ y hPhi hbound hpinJ haP htr
    hK hℓ hrad x₁ hx₁ (Fin.last H.eventCount) hjσ tr v hvθ hvσ hdom x hx
  have h0 : (0 : ℝ) ≤ τ := (H.time_nonneg _).trans hτ1.le
  let τI : Icc (0 : ℝ) H.horizon := ⟨τ, h0, hτσ.trans σ.2.2⟩
  have hact : H.activeStage τI = Fin.last H.eventCount :=
    (H.mem_stageDomain_iff τI (Fin.last H.eventCount)).mp (by
      simp only [ObservedHistory.stageDomain, Fin.lastCases_last]
      exact ⟨hτ1.le, τI.2.2⟩)
  have hav : aSeed ≤ τI := haτ
  have hvs : τI ≤ σ := hτσ
  obtain ⟨A', hA'⟩ := exists_trace_of_eq_first_P6L3 H hact.symm hjσ (H.activeStage_mono hvs) A
  have hs := point_heq_of_eq_P6M2 seedTrace hact (H.activeStage_mono hav)
    (H.activeStage_mono (hvs.trans hsT)) h1 h2
  have hpt : HEq (A'.point (H.activeStage τI) le_rfl (H.activeStage_mono hvs)) x :=
    hA'.trans (heq_of_eq hA)
  have h := hdist x' hx' τI hav hvs hτθ A'
  rw [edist_stage_heq_J16 H hact τ _ _ _ x hs hpt] at h
  exact h

/-- **hclosGF ⇐ `hdistQ` + `hDext` + HI（`_J16`，PROVED 相对 `hdistQ`、`hDext`、`hpin`）**：结论 =
KT2c final `hOpenFJ` 的 `hclosGF` 合取逐字。 -/
theorem ObservedHistory.hclosGF_of_depthExt_HI_J16 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (hR : ∀ n, 0 < R n) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistQ : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
        ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
        v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (hjσ : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (σ n))
          (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
            hjσ x₁),
        ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ (Fin.last (Kh n).eventCount))
          (h2 : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage
            (Fin.last (Kh n).eventCount)).Carrier),
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
              ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
              (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt
                (R n)) →
          R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
          ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
              (Rad / Real.sqrt (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
                w)),
          ∀ τ : ℝ, v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤ τ
            → τ ≤ v →
            (Kh n).time (Fin.last (Kh n).eventCount) < τ →
            riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) τ)
                ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) x ≤
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
        ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
        v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (hjσ : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (σ n))
          (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
            hjσ x₁),
        ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ (Fin.last (Kh n).eventCount))
          (h2 : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage
            (Fin.last (Kh n).eventCount)).Carrier),
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
              ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
              (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt
                (R n)) →
          R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
          ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
              (Rad / Real.sqrt (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
                w)),
          ∀ τ : ℝ, v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤ τ
            → τ ≤ v →
            (Kh n).time (Fin.last (Kh n).eventCount) < τ →
            riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) τ)
                ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) x ≤
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
    have hfoot := (hdistQ D θb hD hθ).filter_mono hφψ
    have hE := (ObservedHistory.eventually_exp_le_two_J16 hPhi R hRr hK hθ).filter_mono hφψ
    have hW := (hwin θb hθ).filter_mono hφψ
    have hL0 := (hL.eventually_ge_atTop 0).filter_mono hφψ
    refine ⟨ψ, hψ, 1, ?_⟩
    change ∀ᶠ m in map (φ ∘ ψ) atTop, (fun n => ∀ C : ℝ, 1 ≤ C →
        ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
        v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (hjσ : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (σ n))
          (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
            hjσ x₁),
        ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ (Fin.last (Kh n).eventCount))
          (h2 : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage
            (Fin.last (Kh n).eventCount)).Carrier),
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
              ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
              (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt
                (R n)) →
          R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
          ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
              (Rad / Real.sqrt (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
                w)),
          ∀ τ : ℝ, v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤ τ
            → τ ≤ v →
            (Kh n).time (Fin.last (Kh n).eventCount) < τ →
            riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) τ)
                ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n))) m
    filter_upwards [htr', hfoot, hE, hW, hL0] with n htri hfi hEi hWi hLi
    intro _ _ v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w _hwseed hwnear hRw x hx τ hτ hτv hτ1
    have hRn := hR n
    have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
    set Rw : ℝ := metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w with hRwdef
    have hRw0 : 0 < Rw := hRn.trans_le hRw
    have hℓ : 0 < (Dd + max Rad 0) / Real.sqrt (R n) := div_pos (by linarith) hsR
    have hrad' : Rad / Real.sqrt Rw ≤ max Rad 0 / Real.sqrt (R n) :=
      (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
        (div_le_div_of_nonneg_left hM hsR (Real.sqrt_le_sqrt hRw))
    have hzx : riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
        (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) x <
          ENNReal.ofReal ((Dd + max Rad 0) / Real.sqrt (R n)) :=
      calc riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) x
          ≤ riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
              (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w +
            riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w x :=
            riemannianEDistOf_triangle _ _ _ _
        _ < ENNReal.ofReal (Dd / Real.sqrt (R n)) +
              ENNReal.ofReal (max Rad 0 / Real.sqrt (R n)) :=
            ENNReal.add_lt_add hwnear (lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal hrad'))
        _ = ENNReal.ofReal ((Dd + max Rad 0) / Real.sqrt (R n)) := by
            rw [← ENNReal.ofReal_add (div_nonneg hDd.le hsR.le) (div_nonneg hM hsR.le),
              ← add_div]
    have hB : B / Rw ≤ max B 0 / R n :=
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
    have hcl := seed_closure_final_of_survival_HI_J16 (Kh n) (haT n) (hsT n) (has n)
      (seedTrace n) (y n) hPhi hbound hpinJ haP' htrD (mul_nonneg hK hRn.le) hℓ hrad hfi x₁ hx₁
      hjσ tr v hvθ hvσ hv1.le x hzx τ hτθ (hτv.trans hvσ) hτ1 (hWi.trans hτθ) h1 h2
    refine hcl.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
    exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
  exact hfin

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

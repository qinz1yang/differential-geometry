import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.FirstExitDistanceP6M4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointCurvatureC11G

/-!
# seed closure 的单 history 首出时刻生产（O-CH11-P6ANCH4 G2，后缀 `_P6L4`）

`hclosG`（DF-1）在单 history、单 slab `j` 上的生产：seed 点 `O := seedTrace.point j⁻`、U 侧点
`x ∈ B_v(w, Rad/√Q)`（`Q := R(v, w)`）、窗 `τ ∈ [v − B/Q, v]`。
* `ricci_seed_or_scal_P6L4`：Good 时刻 `s` 的端点曲率——seed 端 K0（`seed_rmNorm_le_of_smallParabolic_C11G`，
  `B_s(O, r/50)` 上 `|Rm| ≤ r⁻²`）；U 端 `B_s(x, ℓ)` 上标量 `≤ C Q` + Hamilton–Ivey pinching
  （`sqrt_rmNormSq_le_of_HI_scalar_C11G`）⇒ 两端 `ℓ`-球 `Ric ≤ 3/ℓ²`（`K Q ℓ² ≤ 1`）。
* **`seed_closure_firstExit_P6L4`**：初始余量（slice 时刻三角：`d_v(O, x) < d_σ + (L/2 + Rad⁺)/√R`）+ 漂移
  `8√(KQ)(v − τ) ≤ 8√K B⁺/√R` + `L ≥ 2Rad⁺ + 16√K B⁺` ⇒ `firstExit_distance_P6M4`（预算
  `X = d_σ + L/√R`）⇒ `d_τ(O, x) ≤ d_σ + L/√R`。U 端标量界 `hscal` **只在已 seed-Good 的时刻**用。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **Good 时刻的端点 Ricci 界（`_P6L4`）**：slab `j` 内时刻 `s`（`aSeed ≤ s ≤ Tn`、`Q s ≥ 1`）；seed 端 K0
（`ℓ ≤ r/50`、`r⁻² ≤ K`），U 端 `B_s(x, ℓ)` 标量 `≤ C Q` + pinching（`2√3(C/2 + max C (2e⁴)) Q ≤ K`）；
`K ℓ² ≤ 1` ⇒ 两端 `ℓ`-球 `Ric ≤ (3/ℓ²) g`。 -/
theorem ObservedHistory.ricci_seed_or_scal_P6L4 (H : ObservedHistory.{u})
    {Tn aSeed : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (j : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ H.activeStage Tn) (x : (H.stage j.castSucc).Carrier)
    {Q K C ℓ s : ℝ} (hQ : 0 < Q) (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50)
    (hKr : 1 / r ^ 2 ≤ K) (hC : 0 ≤ C)
    (hKC : 2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)) * Q ≤ K)
    (hs1 : H.time j.castSucc < s) (hs2 : s < H.time j.succ) (has : (aSeed : ℝ) ≤ s)
    (hsT : s ≤ Tn) (hQs : 1 ≤ Q * s)
    (hscal : ∀ z : (H.stage j.castSucc).Carrier,
      riemannianEDistOf ((H.event j).incoming.flow.base.metric s) x z < ENNReal.ofReal ℓ →
      (H.event j).incoming.flow.scalar s z ≤ C * Q) :
    ∀ z : (H.stage j.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf ((H.event j).incoming.flow.base.metric s)
          (seedTrace.point j.castSucc h1 h2) z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf ((H.event j).incoming.flow.base.metric s) x z < ENNReal.ofReal ℓ) →
      ricciTensor ((H.event j).incoming.flow.base.metric s) z ξ ξ ≤
        (3 / ℓ ^ 2) * ((H.event j).incoming.flow.base.metric s).inner z ξ ξ := by
  intro z ξ hz
  have hs0 : 0 < s := by
    by_contra hneg
    have hle := not_lt.mp hneg
    nlinarith
  let τI : Icc (0 : ℝ) H.horizon := ⟨s, hs0.le, hsT.trans Tn.2.2⟩
  have hk : H.activeStage τI = j.castSucc := H.activeStage_eq_castSucc_C11G j τI hs1.le hs2
  have hK : Real.sqrt (normSq0S ((H.event j).incoming.flow.base.metric s) z 4
      (metricRm04At ((H.event j).incoming.flow.base.metric s) z)) ≤ K := by
    rcases hz with hz | hz
    · have hzr : riemannianEDistOf (H.stageMetric j.castSucc τI)
          (seedTrace.point j.castSucc h1 h2) z < ENNReal.ofReal (r / 50) := by
        rw [ObservedHistory.stageMetric_castSucc_apply]
        exact hz.trans_le (ENNReal.ofReal_le_ofReal hℓr)
      have h := H.seed_rmNorm_le_of_smallParabolic_C11G haT hsmall hclock seedTrace τI has hsT
        j.castSucc hk h1 h2 z hzr
      rw [ObservedHistory.stageMetric_castSucc_apply] at h
      exact h.trans hKr
    · have hfix := H.inFixedHI_stage_C11G hpin τI j.castSucc hk z
      rw [ObservedHistory.stageMetric_castSucc_apply] at hfix
      have hsc : metricScalarAt ((H.event j).incoming.flow.base.metric s) z ≤ C * Q :=
        hscal z hz
      exact (sqrt_rmNormSq_le_of_HI_scalar_C11G _ z ha₀ hs0 hQ hQs hC hfix hsc).trans hKC
  have hg : 0 ≤ ((H.event j).incoming.flow.base.metric s).inner z ξ ξ :=
    metric_inner_self_nonneg _ z ξ
  have hK' : K ≤ 1 / ℓ ^ 2 := by
    rw [le_div_iff₀ (pow_pos hℓ 2)]
    exact hKℓ
  calc ricciTensor ((H.event j).incoming.flow.base.metric s) z ξ ξ ≤
        3 * K * ((H.event j).incoming.flow.base.metric s).inner z ξ ξ :=
        ricciTensor_le_of_sqrt_rmNormSq_le_C11D _ z hK ξ
    _ ≤ (3 / ℓ ^ 2) * ((H.event j).incoming.flow.base.metric s).inner z ξ ξ := by
      apply mul_le_mul_of_nonneg_right _ hg
      calc 3 * K ≤ 3 * (1 / ℓ ^ 2) := by linarith
        _ = 3 / ℓ ^ 2 := by ring

/-- 漂移的实数界（`_P6L4`）：`ℓ = 1/√K/√Q`、`v − τ ≤ B/Q`、`R ≤ Q` ⇒ `8/ℓ (v − τ) ≤ 8√K B⁺/√R`。 -/
theorem drift_le_P6L4 {K Q R B τ v : ℝ} (hK : 0 < K) (hR : 0 < R) (hRQ : R ≤ Q)
    (hτB : v - B / Q ≤ τ) :
    8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ) ≤ 8 * Real.sqrt K * max B 0 / Real.sqrt R := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have h8 : 8 / (1 / Real.sqrt K / Real.sqrt Q) = 8 * Real.sqrt K * Real.sqrt Q := by
    field_simp
  have hvτ : v - τ ≤ max B 0 / Q := by
    have : B / Q ≤ max B 0 / Q := div_le_div_of_nonneg_right (le_max_left _ _) hQ.le
    linarith
  have key : ∀ sQ : ℝ, 0 < sQ → sQ * sQ = Q →
      8 * Real.sqrt K * sQ * (max B 0 / Q) = 8 * Real.sqrt K * max B 0 / sQ := by
    intro sQ hsQ' hsq
    rw [← hsq]
    field_simp
  rw [h8]
  calc 8 * Real.sqrt K * Real.sqrt Q * (v - τ) ≤
        8 * Real.sqrt K * Real.sqrt Q * (max B 0 / Q) :=
        mul_le_mul_of_nonneg_left hvτ (by positivity)
    _ = 8 * Real.sqrt K * max B 0 / Real.sqrt Q := key _ hsQ (Real.mul_self_sqrt hQ.le)
    _ ≤ 8 * Real.sqrt K * max B 0 / Real.sqrt R :=
        div_le_div_of_nonneg_left (by have := le_max_right B 0; positivity) hsR
          (Real.sqrt_le_sqrt hRQ)

/-- **单 history seed closure（首出时刻，`_P6L4`）**：slab `j`、`Q := R(v, w) ≥ R`、`x ∈ B_v(w, Rad/√Q)`、
`d_v(O, w) ≤ d_σ + L/(2√R)`、窗 `τ ∈ [v − B/Q, v]`（`time j⁻ < τ`）；K0 种子 + pinching + **条件** U 端标量界
`hscal`（`B_s(x, 1/√(CQ))` 上 `R ≤ CQ`，`1 ≤ C`；只在 `d_s(O, x) ≤ d_σ + L/√R` 的时刻）+
`L ≥ 2Rad⁺ + 16√K B⁺`、`2500 K ≤ R r²`
（`K := max 1 (2√3(C/2 + max C (2e⁴)))`）⇒ `d_τ(O, x) ≤ d_σ + L/√R`。 -/
theorem ObservedHistory.seed_closure_firstExit_P6L4 (H : ObservedHistory.{u})
    {Tn aSeed : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (j : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ H.activeStage Tn) (w x : (H.stage j.castSucc).Carrier)
    {dσ : ℝ≥0∞} {A R Q L C Rad B τ v : ℝ} (hdσ : dσ = ENNReal.ofReal A) (hA : 0 ≤ A)
    (hR : 0 < R) (hRQ : R ≤ Q) (hC1 : 1 ≤ C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R * r ^ 2)
    (hL : 2 * max Rad 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max B 0 ≤ L)
    (hwv : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
      (seedTrace.point j.castSucc h1 h2) w ≤ dσ + ENNReal.ofReal (L / 2 / Real.sqrt R))
    (hxw : x ∈ riemannianBallOf ((H.event j).incoming.flow.base.metric v) w
      (Rad / Real.sqrt Q))
    (hτB : v - B / Q ≤ τ) (hτv : τ ≤ v) (hτ1 : H.time j.castSucc < τ)
    (hv2 : v < H.time j.succ) (haτ : (aSeed : ℝ) ≤ τ) (hvT : v ≤ Tn) (hQτ : 1 ≤ Q * τ)
    (hscal : ∀ s : ℝ, v - B / Q ≤ s → s ≤ v → H.time j.castSucc < s →
      riemannianEDistOf ((H.event j).incoming.flow.base.metric s)
          (seedTrace.point j.castSucc h1 h2) x ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) →
      ∀ z : (H.stage j.castSucc).Carrier,
        riemannianEDistOf ((H.event j).incoming.flow.base.metric s) x z <
          ENNReal.ofReal (1 / Real.sqrt (C * Q)) →
        (H.event j).incoming.flow.scalar s z ≤ C * Q) :
    riemannianEDistOf ((H.event j).incoming.flow.base.metric τ)
        (seedTrace.point j.castSucc h1 h2) x ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) := by
  set K := max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hQ : 0 < Q := hR.trans_le hRQ
  have hC : 0 ≤ C := by linarith
  have h3 : 1 ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hCK : C ≤ K := by
    refine le_trans ?_ (le_max_right _ _)
    have hm : C ≤ max C (2 * Real.exp 4) := le_max_left _ _
    nlinarith
  have hr : 0 < r := hsmall.1
  have hQr : 2500 * K ≤ Q * r ^ 2 := hRr.trans (mul_le_mul_of_nonneg_right hRQ (sq_nonneg r))
  obtain ⟨hℓr, hKr, hKℓ, -⟩ := seq_scale_bounds_C11G hK1 hQ hr hQr
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 (by linarith)
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hℓ : 0 < 1 / Real.sqrt K / Real.sqrt Q := by positivity
  have hℓCQ : 1 / Real.sqrt K / Real.sqrt Q ≤ 1 / Real.sqrt (C * Q) := by
    have hCQ : Real.sqrt (C * Q) ≤ Real.sqrt K * Real.sqrt Q := by
      rw [← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hCK hQ.le)
    rw [div_div]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity)) hCQ
  have hKC : 2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)) * Q ≤ K * Q :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hQ.le
  have hRad0 : 0 ≤ max Rad 0 := le_max_right _ _
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hL0 : 0 ≤ L := by
    have : 0 ≤ 16 * Real.sqrt K * max B 0 := by positivity
    linarith
  -- 漂移与初始余量
  have hdrift := drift_le_P6L4 (by linarith : (0 : ℝ) < K) hR hRQ hτB
  have hdr0 : 0 ≤ 8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ) :=
    mul_nonneg (by positivity) (by linarith)
  have hrad' : Rad / Real.sqrt Q ≤ max Rad 0 / Real.sqrt R :=
    (div_le_div_of_nonneg_right (le_max_left _ _) hsQ.le).trans
      (div_le_div_of_nonneg_left hRad0 hsR (Real.sqrt_le_sqrt hRQ))
  have hwx : riemannianEDistOf ((H.event j).incoming.flow.base.metric v) w x <
      ENNReal.ofReal (max Rad 0 / Real.sqrt R) :=
    lt_of_lt_of_le hxw (ENNReal.ofReal_le_ofReal hrad')
  have hwv' : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
      (seedTrace.point j.castSucc h1 h2) w ≤ ENNReal.ofReal (A + L / 2 / Real.sqrt R) := by
    rw [ENNReal.ofReal_add hA (by positivity), ← hdσ]
    exact hwv
  have hd2 : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
        (seedTrace.point j.castSucc h1 h2) w +
      riemannianEDistOf ((H.event j).incoming.flow.base.metric v) w x <
      ENNReal.ofReal (A + L / 2 / Real.sqrt R) + ENNReal.ofReal (max Rad 0 / Real.sqrt R) :=
    ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hwv') hwv' hwx
  have hd3 : ENNReal.ofReal (A + L / 2 / Real.sqrt R) +
        ENNReal.ofReal (max Rad 0 / Real.sqrt R) +
        ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ)) ≤
      dσ + ENNReal.ofReal (L / Real.sqrt R) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) hdr0, hdσ, ← ENNReal.ofReal_add hA (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hsum : L / 2 / Real.sqrt R + max Rad 0 / Real.sqrt R +
        8 * Real.sqrt K * max B 0 / Real.sqrt R =
        (L / 2 + max Rad 0 + 8 * Real.sqrt K * max B 0) / Real.sqrt R := by ring
    have hle : (L / 2 + max Rad 0 + 8 * Real.sqrt K * max B 0) / Real.sqrt R ≤
        L / Real.sqrt R := div_le_div_of_nonneg_right (by linarith) hsR.le
    linarith
  have hmargin : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
        (seedTrace.point j.castSucc h1 h2) x +
      ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ)) <
      dσ + ENNReal.ofReal (L / Real.sqrt R) :=
    calc riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
          (seedTrace.point j.castSucc h1 h2) x +
          ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ)) ≤
        (riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
            (seedTrace.point j.castSucc h1 h2) w +
          riemannianEDistOf ((H.event j).incoming.flow.base.metric v) w x) +
          ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ)) :=
          add_le_add (riemannianEDistOf_triangle _ _ _ _) le_rfl
      _ < ENNReal.ofReal (A + L / 2 / Real.sqrt R) +
            ENNReal.ofReal (max Rad 0 / Real.sqrt R) +
          ENNReal.ofReal (8 / (1 / Real.sqrt K / Real.sqrt Q) * (v - τ)) :=
          ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hd2
      _ ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) := hd3
  -- 首出时刻
  have hfe := H.firstExit_distance_P6M4 j hℓ hτv hτ1 hv2 (seedTrace.point j.castSucc h1 h2) x
    hmargin (fun s hs hgood => H.ricci_seed_or_scal_P6L4 haT hsmall hclock seedTrace ha₀ hpin j
      h1 h2 x hQ hℓ hKℓ hℓr hKr hC hKC (hτ1.trans hs.1) (hs.2.trans hv2)
      (haτ.trans hs.1.le) (hs.2.le.trans hvT)
      (hQτ.trans (mul_le_mul_of_nonneg_left hs.1.le hQ.le))
      (fun z hz => hscal s (hτB.trans hs.1.le) hs.2.le (hτ1.trans hs.1) hgood.le z
        (hz.trans_le (ENNReal.ofReal_le_ofReal hℓCQ)))) τ ⟨le_rfl, hτv⟩
  exact (lt_of_le_of_lt hfe hmargin).le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

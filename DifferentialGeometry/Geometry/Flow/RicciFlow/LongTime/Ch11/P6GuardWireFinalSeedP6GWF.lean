import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardWireFinalEdistP6GWF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallSeedClosureLocalC11SC2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FirstExitFinalP6M6

/-!
# GUARDWIRE-FINAL G2：stopped first-exit 核 + seed closure 的 final-slab 孪生（`_P6GWF`）

GUARDWIRE G2b `hseedG` 的 repair target 第 2 项：SEEDCL2
`ObservedHistory.firstExit_distance_stopped_C11SC2` /
`ObservedHistory.seed_closure_firstExit_stopped_C11SC2`
（event `j` 的 incoming flow）→ final slab 形。替换表（文件头 GW Final 逐字）：
`j : Fin H.eventCount` → `Fin.last`（`h1 h2` 仍为显式实参，消费端 `h1 := Fin.le_last _`）、
`(H.event j).incoming` → `(K.finalSlab h).restrictIncoming le_rfl h le_rfl`、
`H.time j.castSucc` → `K.time last`、
`hv2 : v < H.time j.succ` → `hv2 : v < K.horizon`、seed 点 `seedTrace.point (Fin.last _) h1 h2`。

* `firstExit_distance_stopped_final_P6GWF`：核 = `firstExit_window_CXJD`；链 = G1
  `edist_le_add_of_final_ricci_P6GWF`；左延拓 = `edist_lt_near_left_P6L4`（对 flow 通用，直接用于 restrict
  final slab flow）。证明体逐字。
* `ricci_seed_or_scal_final_restrict_P6GWF`：P6L4 `ricci_seed_or_scal_P6L4` 的 final 孪生在树内已有
  stageMetric 形（S-CH11-HSCALU2 `ricci_seed_or_scal_final_P6M6`）；本条只做
  `stageMetric_last_restrict_P6HF` 改写到 restrict final slab 形（无新数学）。
* `seed_closure_firstExit_stopped_final_P6GWF`：SEEDCL2 stopped closure 逐字（`hscal` 只在 `[s, v]` 上已
  seed-Good 的时刻要）。

无额外前提（final slab 不需要 regular 性：`IncomingSlab` 定义域 `Ico (time last) horizon` 与 event 同形）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section StoppedFirstExitFinal

/-- **stopped first-exit 距离引理（final slab，`_P6GWF`，PROVED）**：SEEDCL2
`firstExit_distance_stopped_C11SC2` 的 final 孪生——`hRic` 只在 `[s, t]` 上 `d(p, q) < X` 已成立时要。
核 = `firstExit_window_CXJD`；链 = G1；左延拓 = `edist_lt_near_left_P6L4`。证明体逐字。 -/
theorem RetainedCoreHistory.firstExit_distance_stopped_final_P6GWF (K : RetainedCoreHistory.{u})
    (h : K.time (Fin.last K.eventCount) < K.horizon) {a t ℓ : ℝ} (hℓ : 0 < ℓ) (hat : a ≤ t)
    (ha : K.time (Fin.last K.eventCount) < a) (ht : t < K.horizon)
    (p q : (K.stage (Fin.last K.eventCount)).Carrier) {X : ℝ≥0∞}
    (hmargin : riemannianEDistOf
        (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric t) p q +
      ENNReal.ofReal ((8 / ℓ) * (t - a)) < X)
    (hRic : ∀ s ∈ Ioo a t,
      (∀ s' ∈ Icc s t, riemannianEDistOf
          (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s') p q < X) →
      ∀ z : (K.stage (Fin.last K.eventCount)).Carrier, ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s)
          p z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s)
          q z < ENNReal.ofReal ℓ) →
      ricciTensor (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s) z ξ ξ ≤
        (3 / ℓ ^ 2) *
          (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s).inner z ξ ξ) :
    ∀ s ∈ Icc a t, riemannianEDistOf
        (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s) p q ≤
      riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric t)
          p q +
        ENNReal.ofReal ((8 / ℓ) * (t - s)) :=
  firstExit_window_CXJD
    (f := fun s => riemannianEDistOf
      (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s) p q)
    hat (div_pos (by norm_num) hℓ).le hmargin
    (fun s hs hG => K.edist_le_add_of_final_ricci_P6GWF h hℓ hs.2 (ha.trans_le hs.1) ht p q
      (fun r hr z ξ hz => hRic r ⟨hs.1.trans_lt hr.1, hr.2⟩
        (fun s' hs' => hG s' ⟨hr.1.trans_le hs'.1, hs'.2⟩) z ξ hz))
    (fun s hs hG => by
      obtain ⟨s₁, has₁, hs₁, hnear⟩ := edist_lt_near_left_P6L4
        ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow
        ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).equation hs.1
        (fun r hr => ⟨ha.trans_le hr.1, lt_of_le_of_lt (hr.2.trans hs.2) ht⟩) p q
        (hG s ⟨le_rfl, hs.2⟩)
      exact ⟨s₁, ⟨has₁, hs₁⟩, hnear⟩)

/-- **Good 时刻端点 Ricci 界（final slab，restrict 形，`_P6GWF`，PROVED）**：P6M6
`ricci_seed_or_scal_final_P6M6`（stageMetric 形）经 `stageMetric_last_restrict_P6HF` 改写；U 端标量前提与结论
均为 restrict final slab flow 形（= SEEDCL2 closure 内部对 `ricci_seed_or_scal_P6L4` 的用法）。 -/
theorem RetainedCoreHistory.ricci_seed_or_scal_final_restrict_P6GWF (K : RetainedCoreHistory.{u})
    (h : K.time (Fin.last K.eventCount) < K.horizon)
    {Tn aSeed : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn)
    {pT : (K.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage t) t) (a₀ + t) x)
    (h1 : K.toHistory.activeStage aSeed ≤ Fin.last K.eventCount)
    (h2 : Fin.last K.eventCount ≤ K.toHistory.activeStage Tn)
    (x : (K.stage (Fin.last K.eventCount)).Carrier)
    {Q Kc C ℓ s : ℝ} (hQ : 0 < Q) (hℓ : 0 < ℓ) (hKℓ : Kc * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50)
    (hKr : 1 / r ^ 2 ≤ Kc) (hC : 0 ≤ C)
    (hKC : 2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)) * Q ≤ Kc)
    (hs1 : K.time (Fin.last K.eventCount) < s) (has : (aSeed : ℝ) ≤ s)
    (hsT : s ≤ Tn) (hQs : 1 ≤ Q * s)
    (hscal : ∀ z : (K.stage (Fin.last K.eventCount)).Carrier,
      riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s)
          x z < ENNReal.ofReal ℓ →
      ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar s z ≤ C * Q) :
    ∀ z : (K.stage (Fin.last K.eventCount)).Carrier, ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s)
          (seedTrace.point (Fin.last K.eventCount) h1 h2) z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s)
          x z < ENNReal.ofReal ℓ) →
      ricciTensor (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s) z ξ ξ ≤
        (3 / ℓ ^ 2) *
          (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s).inner z ξ ξ := by
  intro z ξ hz
  have hscal' : ∀ z' : (K.toHistory.stage (Fin.last K.toHistory.eventCount)).Carrier,
      riemannianEDistOf (K.toHistory.stageMetric (Fin.last K.toHistory.eventCount) s) x z' <
        ENNReal.ofReal ℓ →
      metricScalarAt (K.toHistory.stageMetric (Fin.last K.toHistory.eventCount) s) z' ≤
        C * Q := by
    intro z' hz'
    rw [K.stageMetric_last_restrict_P6HF h] at hz' ⊢
    exact hscal z' hz'
  have hz' : riemannianEDistOf (K.toHistory.stageMetric (Fin.last K.toHistory.eventCount) s)
        (seedTrace.point (Fin.last K.toHistory.eventCount) h1 h2) z < ENNReal.ofReal ℓ ∨
      riemannianEDistOf (K.toHistory.stageMetric (Fin.last K.toHistory.eventCount) s) x z <
        ENNReal.ofReal ℓ := by
    rw [K.stageMetric_last_restrict_P6HF h]
    exact hz
  have hres := K.toHistory.ricci_seed_or_scal_final_P6M6 haT hsmall hclock seedTrace ha₀ hpin
    h1 h2 x hQ hℓ hKℓ hℓr hKr hC hKC hs1 has hsT hQs hscal' z ξ hz'
  rw [K.stageMetric_last_restrict_P6HF h] at hres
  exact hres

/-- **单 history seed closure 的 stopped 版（final slab，`_P6GWF`，PROVED）**：SEEDCL2
`seed_closure_firstExit_stopped_C11SC2` 的 final 孪生。U 端标量界 `hscal` 只在 **`[s, v]` 上已 seed-Good**
（`d_{s′}(O, x) < d_σ + L/√R`，`s′ ∈ [s, v]`）的时刻 `s` 要；首出时刻用
`firstExit_distance_stopped_final_P6GWF`，端点 Ricci 用 `ricci_seed_or_scal_final_restrict_P6GWF`。
证明体逐字。 -/
theorem RetainedCoreHistory.seed_closure_firstExit_stopped_final_P6GWF
    (K : RetainedCoreHistory.{u}) (h : K.time (Fin.last K.eventCount) < K.horizon)
    {Tn aSeed : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn)
    {pT : (K.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage t) t) (a₀ + t) x)
    (h1 : K.toHistory.activeStage aSeed ≤ Fin.last K.eventCount)
    (h2 : Fin.last K.eventCount ≤ K.toHistory.activeStage Tn)
    (w x : (K.stage (Fin.last K.eventCount)).Carrier)
    {dσ : ℝ≥0∞} {A R Q L C Rad B τ v : ℝ} (hdσ : dσ = ENNReal.ofReal A) (hA : 0 ≤ A)
    (hR : 0 < R) (hRQ : R ≤ Q) (hC1 : 1 ≤ C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R * r ^ 2)
    (hL : 2 * max Rad 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max B 0 ≤ L)
    (hwv : riemannianEDistOf
      (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v)
      (seedTrace.point (Fin.last K.eventCount) h1 h2) w ≤
        dσ + ENNReal.ofReal (L / 2 / Real.sqrt R))
    (hxw : x ∈ riemannianBallOf
      (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v) w
      (Rad / Real.sqrt Q))
    (hτB : v - B / Q ≤ τ) (hτv : τ ≤ v) (hτ1 : K.time (Fin.last K.eventCount) < τ)
    (hv2 : v < K.horizon) (haτ : (aSeed : ℝ) ≤ τ) (hvT : v ≤ Tn) (hQτ : 1 ≤ Q * τ)
    (hscal : ∀ s : ℝ, v - B / Q ≤ s → s ≤ v → K.time (Fin.last K.eventCount) < s →
      (∀ s' ∈ Icc s v, riemannianEDistOf
          (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s')
          (seedTrace.point (Fin.last K.eventCount) h1 h2) x <
            dσ + ENNReal.ofReal (L / Real.sqrt R)) →
      ∀ z : (K.stage (Fin.last K.eventCount)).Carrier,
        riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric s)
            x z < ENNReal.ofReal (1 / Real.sqrt (C * Q)) →
        ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar s z ≤ C * Q) :
    riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric τ)
        (seedTrace.point (Fin.last K.eventCount) h1 h2) x ≤
      dσ + ENNReal.ofReal (L / Real.sqrt R) := by
  set Kc := max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) with hKdef
  have hK1 : 1 ≤ Kc := le_max_left _ _
  have hQ : 0 < Q := hR.trans_le hRQ
  have hC : 0 ≤ C := by linarith
  have h3 : 1 ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hCK : C ≤ Kc := by
    refine le_trans ?_ (le_max_right _ _)
    have hm : C ≤ max C (2 * Real.exp 4) := le_max_left _ _
    nlinarith
  have hr : 0 < r := hsmall.1
  have hQr : 2500 * Kc ≤ Q * r ^ 2 := hRr.trans (mul_le_mul_of_nonneg_right hRQ (sq_nonneg r))
  obtain ⟨hℓr, hKr, hKℓ, -⟩ := seq_scale_bounds_C11G hK1 hQ hr hQr
  have hsK : 0 < Real.sqrt Kc := Real.sqrt_pos.2 (by linarith)
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hℓ : 0 < 1 / Real.sqrt Kc / Real.sqrt Q := by positivity
  have hℓCQ : 1 / Real.sqrt Kc / Real.sqrt Q ≤ 1 / Real.sqrt (C * Q) := by
    have hCQ : Real.sqrt (C * Q) ≤ Real.sqrt Kc * Real.sqrt Q := by
      rw [← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hCK hQ.le)
    rw [div_div]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity)) hCQ
  have hKC : 2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)) * Q ≤ Kc * Q :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hQ.le
  have hRad0 : 0 ≤ max Rad 0 := le_max_right _ _
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hL0 : 0 ≤ L := by
    have : 0 ≤ 16 * Real.sqrt Kc * max B 0 := by positivity
    linarith
  -- 漂移与初始余量
  have hdrift := drift_le_P6L4 (by linarith : (0 : ℝ) < Kc) hR hRQ hτB
  have hdr0 : 0 ≤ 8 / (1 / Real.sqrt Kc / Real.sqrt Q) * (v - τ) :=
    mul_nonneg (by positivity) (by linarith)
  have hrad' : Rad / Real.sqrt Q ≤ max Rad 0 / Real.sqrt R :=
    (div_le_div_of_nonneg_right (le_max_left _ _) hsQ.le).trans
      (div_le_div_of_nonneg_left hRad0 hsR (Real.sqrt_le_sqrt hRQ))
  have hwx : riemannianEDistOf
      (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v) w x <
      ENNReal.ofReal (max Rad 0 / Real.sqrt R) :=
    lt_of_lt_of_le hxw (ENNReal.ofReal_le_ofReal hrad')
  have hwv' : riemannianEDistOf
      (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v)
      (seedTrace.point (Fin.last K.eventCount) h1 h2) w ≤
        ENNReal.ofReal (A + L / 2 / Real.sqrt R) := by
    rw [ENNReal.ofReal_add hA (by positivity), ← hdσ]
    exact hwv
  have hd2 : riemannianEDistOf
        (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v)
        (seedTrace.point (Fin.last K.eventCount) h1 h2) w +
      riemannianEDistOf
        (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v) w x <
      ENNReal.ofReal (A + L / 2 / Real.sqrt R) + ENNReal.ofReal (max Rad 0 / Real.sqrt R) :=
    ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hwv') hwv' hwx
  have hd3 : ENNReal.ofReal (A + L / 2 / Real.sqrt R) +
        ENNReal.ofReal (max Rad 0 / Real.sqrt R) +
        ENNReal.ofReal (8 / (1 / Real.sqrt Kc / Real.sqrt Q) * (v - τ)) ≤
      dσ + ENNReal.ofReal (L / Real.sqrt R) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) hdr0, hdσ, ← ENNReal.ofReal_add hA (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hsum : L / 2 / Real.sqrt R + max Rad 0 / Real.sqrt R +
        8 * Real.sqrt Kc * max B 0 / Real.sqrt R =
        (L / 2 + max Rad 0 + 8 * Real.sqrt Kc * max B 0) / Real.sqrt R := by ring
    have hle : (L / 2 + max Rad 0 + 8 * Real.sqrt Kc * max B 0) / Real.sqrt R ≤
        L / Real.sqrt R := div_le_div_of_nonneg_right (by linarith) hsR.le
    linarith
  have hmargin : riemannianEDistOf
        (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v)
        (seedTrace.point (Fin.last K.eventCount) h1 h2) x +
      ENNReal.ofReal (8 / (1 / Real.sqrt Kc / Real.sqrt Q) * (v - τ)) <
      dσ + ENNReal.ofReal (L / Real.sqrt R) :=
    calc riemannianEDistOf
          (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v)
          (seedTrace.point (Fin.last K.eventCount) h1 h2) x +
          ENNReal.ofReal (8 / (1 / Real.sqrt Kc / Real.sqrt Q) * (v - τ)) ≤
        (riemannianEDistOf
            (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v)
            (seedTrace.point (Fin.last K.eventCount) h1 h2) w +
          riemannianEDistOf
            (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v) w x) +
          ENNReal.ofReal (8 / (1 / Real.sqrt Kc / Real.sqrt Q) * (v - τ)) :=
          add_le_add (riemannianEDistOf_triangle _ _ _ _) le_rfl
      _ < ENNReal.ofReal (A + L / 2 / Real.sqrt R) +
            ENNReal.ofReal (max Rad 0 / Real.sqrt R) +
          ENNReal.ofReal (8 / (1 / Real.sqrt Kc / Real.sqrt Q) * (v - τ)) :=
          ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hd2
      _ ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) := hd3
  -- 首出时刻（stopped）
  have hfe := K.firstExit_distance_stopped_final_P6GWF h hℓ hτv hτ1 hv2
    (seedTrace.point (Fin.last K.eventCount) h1 h2) x hmargin
    (fun s hs hG => K.ricci_seed_or_scal_final_restrict_P6GWF h haT hsmall hclock seedTrace ha₀
      hpin h1 h2 x hQ hℓ hKℓ hℓr hKr hC hKC (hτ1.trans hs.1)
      (haτ.trans hs.1.le) (hs.2.le.trans hvT)
      (hQτ.trans (mul_le_mul_of_nonneg_left hs.1.le hQ.le))
      (fun z hz => hscal s (hτB.trans hs.1.le) hs.2.le (hτ1.trans hs.1) hG z
        (hz.trans_le (ENNReal.ofReal_le_ofReal hℓCQ)))) τ ⟨le_rfl, hτv⟩
  exact (lt_of_le_of_lt hfe hmargin).le

end StoppedFirstExitFinal

/-- consumer（G2，`_P6GWF`）：stopped closure 常量登记；真正的消费者 = G4 `windowSeed_pointAnchor_final_P6GWF`
（closure 步 + G3 `windowScal` 喂 `hscal`）。 -/
example := @RetainedCoreHistory.seed_closure_firstExit_stopped_final_P6GWF.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

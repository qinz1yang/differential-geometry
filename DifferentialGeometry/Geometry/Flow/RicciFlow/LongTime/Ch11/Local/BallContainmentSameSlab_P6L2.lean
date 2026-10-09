import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ForwardTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.NoncollapseLocalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionBackwardStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion

/-!
# (α) 球包含路线，同 slab 部分（O-CH11-P6ANCH2 G2b，后缀 `_P6L2`）

B2（设计段见 state-O-CH11-P6ANCH2）：hscal 不经 Good / 梯度，直接由 traced region 给。
* `riemannianBallOf_subset_of_inner_le_mul_on_P6L2`（**first-exit 版**球包含）：树内
  `riemannianBallOf_subset_of_inner_le_mul`（`Perelman/Noncollapsing/ForwardTransfer:22`）要求度量比较
  `h ≤ Q g` 在**源球** `B_g(p, r)` 上——那正是要控制的球（循环）。这里只要求比较在某集合 `Ω` 上、且
  `B_h(p, √Q r) ⊆ Ω`：对 `g`-长 `< r` 的路径 `γ`，取 `c = sup {u | γ([0, u]) ⊆ B_h(p, √Q r)}`，
  `γ((0, c)) ⊆ Ω` ⇒ `h`-长 `≤ √Q · g`-长 `< √Q r` ⇒ `γ c` 在球内；球开 + `γ` 连续 ⇒ `c = 1`。
* `scalar_le_on_ball_of_isTracedRegion_sameSlab_P6L2`（**hscal 第一分量**）：traced region
  `(ρ, θ, K)` 于 `(s, y)`，`x ∈ B_s(y, r)`，`τ ∈ (s − θ, s)` 与 `s` 同 slab；slab 内 trace 是恒等 ⇒
  `Ω := B_s(y, ρ)` 上 `[τ, s]` 内 `|Rm| ≤ K` ⇒ `g(s) ≤ e^{18Kθ} g(τ)`（树内
  `stageMetric_inner_le_exp_of_normSq_le`）⇒（first-exit，`r + e^{9Kθ} ℓ ≤ ρ`）`B_τ(x, ℓ) ⊆ Ω` ⇒
  `R(τ) ≤ 9K` 于 `B_τ(x, ℓ)`。
序列层（`ρ = 2D/√R`、`θ = T/R`、`K ↦ K R`、`ℓ = ℓ₀/√R`，`ℓ₀ ≤ D e^{−9KT}`）见
`P6HscalSameSlabP6M2`。
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **first-exit 版球包含**：度量比较 `h ≤ Q g` 只在 `Ω` 上，且 `B_h(p, √Q r) ⊆ Ω` ⇒
`B_g(p, r) ⊆ B_h(p, √Q r)`。 -/
theorem riemannianBallOf_subset_of_inner_le_mul_on_P6L2
    (g h : SmoothRiemannianMetric I M) (p : M) {r Q : ℝ} (hQ : 0 < Q) (hr : 0 < r) (Ω : Set M)
    (hΩ : riemannianBallOf h p (Real.sqrt Q * r) ⊆ Ω)
    (hlocal : ∀ q ∈ Ω, ∀ v : TangentSpace I q, h.inner q v v ≤ Q * g.inner q v v) :
    riemannianBallOf g p r ⊆ riemannianBallOf h p (Real.sqrt Q * r) := by
  intro z hz
  have hlen : ∀ (k : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ),
      (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨k.toRiemannianMetric⟩;
        pathELength I γ a b) =
        ∫⁻ s in Ioo a b, ENNReal.ofReal (Real.sqrt (k.inner (γ s)
          (mfderiv (modelWithCornersSelf ℝ ℝ) I γ s 1)
          (mfderiv (modelWithCornersSelf ℝ ℝ) I γ s 1))) := by
    intro k γ a b
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨k.toRiemannianMetric⟩
    rw [pathELength_eq_lintegral_mfderiv_Ioo]
    apply lintegral_congr
    intro s
    exact Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm k (γ s) _
  obtain ⟨γ, h0, h1, hγ, hγlen⟩ : ∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = z ∧
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Icc 0 1) ∧
      (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
        pathELength I γ 0 1) < ENNReal.ofReal r := by
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    change riemannianEDist I p z < ENNReal.ofReal r at hz
    exact exists_lt_of_riemannianEDist_lt hz
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  -- 关键一步：`γ((0, c)) ⊆ Ω` ⇒ `γ c ∈ B_h(p, √Q r)`
  have key : ∀ c ∈ Icc (0 : ℝ) 1, (∀ u ∈ Ioo (0 : ℝ) c, γ u ∈ Ω) →
      γ c ∈ riemannianBallOf h p (Real.sqrt Q * r) := by
    intro c hc hin
    have hcomp :
        (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨h.toRiemannianMetric⟩;
          pathELength I γ 0 c) ≤ ENNReal.ofReal (Real.sqrt Q) *
        (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
          pathELength I γ 0 c) := by
      rw [hlen h, hlen g, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_mono' measurableSet_Ioo
      intro s hs
      have hroot := Real.sqrt_le_sqrt
        (hlocal (γ s) (hin s hs) (mfderiv (modelWithCornersSelf ℝ ℝ) I γ s 1))
      rw [Real.sqrt_mul hQ.le] at hroot
      simpa only [ENNReal.ofReal_mul (Real.sqrt_nonneg Q)] using ENNReal.ofReal_le_ofReal hroot
    have hgle : (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
        pathELength I γ 0 c) ≤
        (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
          pathELength I γ 0 1) := by
      let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
      exact pathELength_mono le_rfl hc.2
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨h.toRiemannianMetric⟩
    change riemannianEDist I p (γ c) < ENNReal.ofReal (Real.sqrt Q * r)
    calc
      riemannianEDist I p (γ c) ≤ pathELength I γ 0 c :=
        riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl hc.2)) h0 rfl hc.1
      _ ≤ ENNReal.ofReal (Real.sqrt Q) *
          (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
            pathELength I γ 0 c) := hcomp
      _ ≤ ENNReal.ofReal (Real.sqrt Q) *
          (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
            pathELength I γ 0 1) := by gcongr
      _ < ENNReal.ofReal (Real.sqrt Q) * ENNReal.ofReal r :=
        ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hsQ).ne' ENNReal.ofReal_ne_top hγlen
      _ = ENNReal.ofReal (Real.sqrt Q * r) := (ENNReal.ofReal_mul (Real.sqrt_nonneg Q)).symm
  -- first exit：`c = sup A`
  let B := riemannianBallOf h p (Real.sqrt Q * r)
  let A : Set ℝ := {c | c ∈ Icc (0 : ℝ) 1 ∧ ∀ u ∈ Icc (0 : ℝ) c, γ u ∈ B}
  have hpB : p ∈ B := by
    change riemannianEDistOf h p p < ENNReal.ofReal (Real.sqrt Q * r)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (mul_pos hsQ hr)
  have hA0 : (0 : ℝ) ∈ A := ⟨⟨le_rfl, zero_le_one⟩, fun u hu => by
    obtain rfl : u = 0 := le_antisymm hu.2 hu.1
    rw [h0]
    exact hpB⟩
  have hAne : A.Nonempty := ⟨0, hA0⟩
  have hAbdd : BddAbove A := ⟨1, fun c hc => hc.1.2⟩
  have hc0 : 0 ≤ sSup A := le_csSup hAbdd hA0
  have hc1 : sSup A ≤ 1 := csSup_le hAne fun x hx => hx.1.2
  have hbelow : ∀ u ∈ Ico (0 : ℝ) (sSup A), γ u ∈ B := by
    intro u hu
    obtain ⟨a, ha, hua⟩ := exists_lt_of_lt_csSup hAne hu.2
    exact ha.2 u ⟨hu.1, hua.le⟩
  have hcB : γ (sSup A) ∈ B :=
    key _ ⟨hc0, hc1⟩ fun u hu => hΩ (hbelow u ⟨hu.1.le, hu.2⟩)
  have hcA : ∀ u ∈ Icc (0 : ℝ) (sSup A), γ u ∈ B := fun u hu =>
    (eq_or_lt_of_le hu.2).elim (fun h' => h' ▸ hcB) fun h' => hbelow u ⟨hu.1, h'⟩
  have hc_eq : sSup A = 1 := by
    by_contra hne
    have hlt : sSup A < 1 := lt_of_le_of_ne hc1 hne
    have hcont : ContinuousWithinAt γ (Icc 0 1) (sSup A) := hγ.continuousOn _ ⟨hc0, hc1⟩
    have hBopen : IsOpen B := isOpen_riemannianBallOf h p _
    have hev : γ ⁻¹' B ∈ 𝓝[Icc 0 1] (sSup A) := hcont (hBopen.mem_nhds hcB)
    obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhdsWithin_iff.mp hev
    have hc'A : min 1 (sSup A + δ / 2) ∈ A := by
      refine ⟨⟨le_min zero_le_one (by linarith), min_le_left _ _⟩, fun u hu => ?_⟩
      rcases le_or_gt u (sSup A) with huc | huc
      · exact hcA u ⟨hu.1, huc⟩
      · refine hδB ⟨?_, hu.1, hu.2.trans (min_le_left _ _)⟩
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor
        · linarith
        · linarith [hu.2.trans (min_le_right _ _)]
    have h1' : min 1 (sSup A + δ / 2) ≤ sSup A := le_csSup hAbdd hc'A
    have h2' : sSup A < min 1 (sSup A + δ / 2) := lt_min hlt (by linarith)
    linarith
  rw [← h1, ← hc_eq]
  exact hcB

end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- endpoint 处的 `|Rm|²` 界在 stage 指标 `m = last` 间搬运（`subst` + `endpoint_eq`）。 -/
private theorem normSq_endpoint_of_stage_eq_P6L2 {H : ObservedHistory.{u}}
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {x : (H.stage last).Carrier}
    (A : BackwardPointTrace H first last hle x) {m : Fin (H.eventCount + 1)} (hm : m = last)
    (h1 : first ≤ m) (h2 : m ≤ last) (v C : ℝ)
    (h : normSq0S (H.stageMetric m v) (A.point m h1 h2) 4
      (metricRm04At (H.stageMetric m v) (A.point m h1 h2)) ≤ C) :
    normSq0S (H.stageMetric last v) x 4 (metricRm04At (H.stageMetric last v) x) ≤ C := by
  subst hm
  rwa [A.endpoint_eq] at h

/-- 照抄 G2c `P6CenterScalarP6M` 的 private `scalar_le_of_normSq_le_P6M`。 -/
private theorem scalar_le_of_normSq_le_P6L2 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (x : M) {C : ℝ}
    (h : normSq0S g x 4 (metricRm04At g x) ≤ C ^ 2) : metricScalarAt g x ≤ 9 * |C| := by
  have hfin : Module.finrank ℝ (TangentSpace ThreeModel x) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp
  have h1 := scalar_abs_le_rm g x
  rw [hfin] at h1
  have h2 : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ |C| := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  have h3 := le_abs_self (metricScalarAt g x)
  push_cast at h1
  nlinarith

/-- **hscal 第一分量（同 slab，`_P6L2`）**：traced region `(ρ, θ, K)` 于 `(s, y)`、`x ∈ B_s(y, r)`、
`τ ∈ (s − θ, s)` 与 `s` 同 slab、`r + e^{9Kθ} ℓ ≤ ρ` ⇒ `B_τ(x, ℓ)` 上 `R(τ) ≤ 9K`。 -/
theorem scalar_le_on_ball_of_isTracedRegion_sameSlab_P6L2 (H : ObservedHistory.{u})
    (s : Icc (0 : ℝ) H.horizon) (y : (H.stageAt s).Carrier) {ρ θ K r ℓ : ℝ}
    (htr : H.isTracedRegion s y ρ θ K) (hK : 0 ≤ K) (hℓ : 0 < ℓ)
    (hrad : r + Real.exp (9 * K * θ) * ℓ ≤ ρ)
    (x : (H.stageAt s).Carrier)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y r)
    (τ : ℝ) (hτ1 : (s : ℝ) - θ < τ) (hτ2 : H.time (H.activeStage s) < τ) (hτ3 : τ < s)
    (z : (H.stageAt s).Carrier)
    (hz : riemannianEDistOf (H.stageMetric (H.activeStage s) τ) x z < ENNReal.ofReal ℓ) :
    metricScalarAt (H.stageMetric (H.activeStage s) τ) z ≤ 9 * K := by
  obtain ⟨-, -, a, hat, ha, htrace⟩ := htr
  -- traced region：`Ω = B_s(y, ρ)` 上、`[τ, s]` 内 `|Rm|² ≤ K²`（slab 内 trace 点 = 自身）
  have hbound : ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y ρ,
      ∀ r' ∈ Icc τ (s : ℝ), normSq0S (H.stageMetric (H.activeStage s) r') q 4
        (metricRm04At (H.stageMetric (H.activeStage s) r') q) ≤ K ^ 2 := by
    intro q hq r' hr'
    obtain ⟨A, hA⟩ := htrace q hq
    let r'' : Icc (0 : ℝ) H.horizon :=
      ⟨r', (H.time_nonneg _).trans (hτ2.le.trans hr'.1), hr'.2.trans s.2.2⟩
    have har : a ≤ r'' := show (a : ℝ) ≤ r' by rw [ha]; linarith [hr'.1]
    have hrs : r'' ≤ s := hr'.2
    have hact : H.activeStage r'' = H.activeStage s :=
      le_antisymm (H.activeStage_mono hrs) (H.le_activeStage r'' _ (hτ2.le.trans hr'.1))
    exact normSq_endpoint_of_stage_eq_P6L2 A hact _ _ r' _ (hA.1 r'' har hrs)
  -- 同 slab：`s` 之前没有 event
  have hnext : ∀ i : Fin H.eventCount, H.activeStage s = i.castSucc → (s : ℝ) < H.time i.succ := by
    intro e he
    have hlt : (H.activeStage s : ℕ) < H.eventCount := by
      rw [he]
      exact e.isLt
    have h := H.activeStage_before_next s hlt
    have heq : (⟨(H.activeStage s : ℕ) + 1, by omega⟩ : Fin (H.eventCount + 1)) = e.succ := by
      apply Fin.ext
      simp only [he, Fin.val_castSucc, Fin.val_succ]
    rwa [heq] at h
  have hexp : Real.exp (9 * K * θ) ^ 2 = Real.exp (18 * K * θ) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  -- 度量比较：`g(s) ≤ e^{18Kθ} g(τ)` 于 `Ω`
  have hQ : ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y ρ,
      ∀ ξ : TangentSpace ThreeModel q,
        (H.stageMetric (H.activeStage s) s).inner q ξ ξ ≤
          Real.exp (9 * K * θ) ^ 2 * (H.stageMetric (H.activeStage s) τ).inner q ξ ξ := by
    intro q hq ξ
    have h := H.stageMetric_inner_le_exp_of_normSq_le (H.activeStage s) q hτ2.le hnext s.2.2
      (C := K ^ 2) (fun r' hr' => hbound q hq r' hr') ⟨hτ3.le, le_rfl⟩ ⟨le_rfl, hτ3.le⟩ ξ
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (metric_inner_self_nonneg _ _ _))
    rw [hexp, Real.sqrt_sq hK, abs_of_nonneg (by linarith)]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hr0 : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt (zero_le (α := ENNReal)) hx)
  have hsq : Real.sqrt (Real.exp (9 * K * θ) ^ 2) = Real.exp (9 * K * θ) :=
    Real.sqrt_sq (Real.exp_pos _).le
  have hΩ : riemannianBallOf (H.stageMetric (H.activeStage s) s) x
      (Real.sqrt (Real.exp (9 * K * θ) ^ 2) * ℓ) ⊆
      riemannianBallOf (H.stageMetric (H.activeStage s) s) y ρ := by
    intro w hw
    rw [hsq] at hw
    have hw' : riemannianEDistOf (H.stageMetric (H.activeStage s) s) x w <
        ENNReal.ofReal (Real.exp (9 * K * θ) * ℓ) := hw
    have hx' : riemannianEDistOf (H.stageMetric (H.activeStage s) s) y x <
        ENNReal.ofReal r := hx
    change riemannianEDistOf (H.stageMetric (H.activeStage s) s) y w < ENNReal.ofReal ρ
    calc riemannianEDistOf (H.stageMetric (H.activeStage s) s) y w
        ≤ riemannianEDistOf (H.stageMetric (H.activeStage s) s) y x +
          riemannianEDistOf (H.stageMetric (H.activeStage s) s) x w :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal r + ENNReal.ofReal (Real.exp (9 * K * θ) * ℓ) :=
          ENNReal.add_lt_add hx' hw'
      _ = ENNReal.ofReal (r + Real.exp (9 * K * θ) * ℓ) :=
          (ENNReal.ofReal_add hr0.le (by positivity)).symm
      _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal hrad
  have hzΩ := hΩ (DifferentialGeometry.riemannianBallOf_subset_of_inner_le_mul_on_P6L2
    (H.stageMetric (H.activeStage s) τ) (H.stageMetric (H.activeStage s) s) x (by positivity) hℓ
    _ hΩ hQ hz)
  have h := scalar_le_of_normSq_le_P6L2 (H.stageMetric (H.activeStage s) τ) z
    (hbound z hzΩ τ ⟨le_rfl, hτ3.le⟩)
  rwa [abs_of_nonneg hK] at h

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

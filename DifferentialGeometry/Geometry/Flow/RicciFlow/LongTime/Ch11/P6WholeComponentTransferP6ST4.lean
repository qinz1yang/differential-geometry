import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SecLowerCompP6ST4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WholeComponentP6ST3

/-!
# S-c OPEN-C：positive 型 whole-component witness 的 transfer（O-CH11-STAB4 G3，后缀 `_P6ST4`）

`positive` alternative 的 domain 是**整个** `connectedComponent x`，`HasMargins` 定义上排除它，故不走
margin 层而直接 transfer（R-C11-8 D-10 (3)：OPEN-C 必须覆盖 positive / round）：
* (C3) **不需要外径 margin**：whole component 上 `B(F x, r') ⊆ comp(F x)` 对任意 `r'` 自动成立
  （ball path-connected，`riemannianBallOf_subset_connectedComponent_P6ST4`），外径由
  `d'(F x, F y) ≤ √(1+δ)·d(x,y)`（树内 `crossModel_edist_transfer_of_comparison`，闭球 `B̄(x, 8r)` 自动
  ⊆ `comp(x)`）吸收：取 `r' := max ((1+δ)r) (√Q')⁻¹`。
* (C1) `SecLower`：G2 `secLower_image_of_comparison_P6ST4`；`PositiveComponent`：树内
  `positiveComponent_transport_of_partialDiffeomorph`；scalar / Rm / volume：树内 comparison 引理。
* 抽象定理 **`exists_positive_wholeComponent_transport_P6ST4`**（任意 `P, N`、`F`、comparison 于
  `comp(x)`，显式 `δ` 条件只依赖 `C2, Rlow`）；event 层
  **`MetricCutCapEvent.wholeComponent_positive_transfer_P6ST4`**：crossing + comp(p) 与 cut tubes 不交 +
  `v n ↑ s` 上 eventually positive 型 fine witness ⇒ `q` 处 `(ηout, C1out, C2out)` positive 型 witness
  （`domain = comp(q)`）。0 binder。
round 型见 DELIVERIES G3 块（BLOCKED + repair target）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]
  {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N]

omit [T2Space P] [SigmaCompactSpace P] in
/-- 开球落在中心的 connected component 内（球 path-connected）。 -/
theorem riemannianBallOf_subset_connectedComponent_P6ST4 (g : SmoothRiemannianMetric I3 P)
    (x : P) (ρ : ℝ) : riemannianBallOf (I := I3) g x ρ ⊆ connectedComponent x := by
  intro y hy
  have hρ : 0 < ρ := by
    by_contra h
    change riemannianEDistOf (I := I3) g x y < ENNReal.ofReal ρ at hy
    rw [ENNReal.ofReal_eq_zero.mpr (not_lt.mp h)] at hy
    exact ENNReal.not_lt_zero hy
  have hx : x ∈ riemannianBallOf (I := I3) g x ρ := by
    change riemannianEDistOf (I := I3) g x x < ENNReal.ofReal ρ
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hρ
  exact IsPreconnected.subset_connectedComponent
    (DifferentialGeometry.isPathConnected_riemannianBallOf g x hρ).isConnected.isPreconnected hx hy

omit [T2Space P] [SigmaCompactSpace P] in
/-- 闭球落在中心的 connected component 内。 -/
theorem riemannianClosedBallOf_subset_connectedComponent_P6ST4
    (g : SmoothRiemannianMetric I3 P) (x : P) (R : ℝ) :
    riemannianClosedBallOf (I := I3) g x R ⊆ connectedComponent x := by
  intro y hy
  refine riemannianBallOf_subset_connectedComponent_P6ST4 g x (max R 0 + 1) ?_
  change riemannianEDistOf (I := I3) g x y < ENNReal.ofReal (max R 0 + 1)
  exact lt_of_le_of_lt (hy.trans (ENNReal.ofReal_le_ofReal (le_max_left R 0)))
    ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))

omit [IsManifold I3 ∞ P] [T2Space P] [SigmaCompactSpace P] [IsManifold I3 ∞ N]
  [SigmaCompactSpace N] in
/-- component 搬运（component 紧、⊆ source）：`F '' comp(x) = comp(F x)`。 -/
theorem image_connectedComponent_P6ST4 (F : PartialDiffeomorph I3 I3 P N ∞) {x : P}
    (hK : IsCompact (connectedComponent x)) (hsrc : connectedComponent x ⊆ F.source) :
    (F : P → N) '' connectedComponent x = connectedComponent (F x) := by
  have : LocallyConnectedSpace P := ChartedSpace.locallyConnectedSpace ThreeSpace P
  have hopen : IsOpen ((F : P → N) '' connectedComponent x) :=
    F.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_connectedComponent hsrc
  have hclosed : IsClosed ((F : P → N) '' connectedComponent x) :=
    (hK.image_of_continuousOn (F.contMDiffOn_toFun.continuousOn.mono hsrc)).isClosed
  have hconn : IsPreconnected ((F : P → N) '' connectedComponent x) :=
    isPreconnected_connectedComponent.image _ (F.contMDiffOn_toFun.continuousOn.mono hsrc)
  exact subset_antisymm (hconn.subset_connectedComponent ⟨x, mem_connectedComponent, rfl⟩)
    (IsClopen.connectedComponent_subset ⟨hclosed, hopen⟩ ⟨x, mem_connectedComponent, rfl⟩)

/-- scalar 界的数值传递（`θ ≤ 1/(2C2)`、`q/2 ≤ q' ≤ 2q`、`1000C2 ≤ C2'`）。 -/
theorem scalar_bounds_real_P6ST4 {a a' q q' θ C2 C2' : ℝ} (hq : 0 < q) (hC2 : 1 ≤ C2)
    (hC2' : 1000 * C2 ≤ C2') (hθ : θ ≤ 1 / (2 * C2)) (hlo : C2⁻¹ * q ≤ a)
    (hhi : a ≤ C2 * q) (hclose : |a' - a| ≤ θ * q) (hq'2 : q / 2 ≤ q') (hq'4 : q' ≤ 2 * q) :
    C2'⁻¹ * q' ≤ a' ∧ a' ≤ C2' * q' := by
  have hC2pos : 0 < C2 := by linarith
  have hk : 1 / (2 * C2) = C2⁻¹ / 2 := by field_simp
  rw [hk] at hθ
  have hinv : C2'⁻¹ ≤ C2⁻¹ / 1000 := by
    rw [div_eq_mul_inv, ← mul_inv]
    exact inv_anti₀ (by positivity) (by linarith)
  have hq'0 : 0 ≤ q' := by linarith
  have h1 : C2'⁻¹ * q' ≤ C2⁻¹ / 1000 * (2 * q) :=
    mul_le_mul hinv hq'4 hq'0 (by positivity)
  have h2 : θ * q ≤ C2⁻¹ / 2 * q := mul_le_mul_of_nonneg_right hθ hq.le
  have h3 := abs_le.mp hclose
  have hθ1 : θ ≤ C2 := by
    have : C2⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC2
    linarith
  have h4 : θ * q ≤ C2 * q := mul_le_mul_of_nonneg_right hθ1 hq.le
  have h5 : C2 * q ≤ 2 * (C2 * q') := by nlinarith
  have h6 : 4 * (C2 * q') ≤ C2' * q' := by nlinarith
  constructor <;> nlinarith

/-- volume 下界的数值传递（`δ ≤ 1/10`、`q/2 ≤ q'`、`1000C2 ≤ C2'`）。 -/
theorem volume_lower_real_P6ST4 {δ q q' C2 C2' : ℝ} (hδ : δ ≤ 1 / 10) (hq : 0 < q)
    (hq' : q / 2 ≤ q') (hC2 : 1 ≤ C2) (hC2' : 1000 * C2 ≤ C2') :
    C2'⁻¹ / (q' * Real.sqrt q') ≤ Real.sqrt ((1 - δ) ^ 3) * (C2⁻¹ / (q * Real.sqrt q)) := by
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hq'0 : 0 < q' := by linarith
  have hsq' : Real.sqrt q / 2 ≤ Real.sqrt q' := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, Real.sq_sqrt hq.le]
    linarith
  have hZ' : q * Real.sqrt q / 4 ≤ q' * Real.sqrt q' := by
    have := mul_le_mul hq' hsq' (by positivity) hq'0.le
    linarith
  have hC2pos : 0 < C2 := by linarith
  have hinv : C2'⁻¹ ≤ (1000 * C2)⁻¹ := inv_anti₀ (by positivity) hC2'
  have hL : C2'⁻¹ / (q' * Real.sqrt q') ≤ (1000 * C2)⁻¹ / (q * Real.sqrt q / 4) :=
    div_le_div₀ (by positivity) hinv (by positivity) hZ'
  have he : (1000 * C2)⁻¹ / (q * Real.sqrt q / 4) = 1 / 250 * (C2⁻¹ / (q * Real.sqrt q)) := by
    field_simp
    ring
  have hs : 1 / 2 ≤ Real.sqrt ((1 - δ) ^ 3) := by
    apply Real.le_sqrt_of_sq_le
    have h1 : (9 / 10 : ℝ) ^ 3 ≤ (1 - δ) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    nlinarith
  have hX : 0 ≤ C2⁻¹ / (q * Real.sqrt q) := by positivity
  have h2 : 1 / 2 * (C2⁻¹ / (q * Real.sqrt q)) ≤
      Real.sqrt ((1 - δ) ^ 3) * (C2⁻¹ / (q * Real.sqrt q)) := mul_le_mul_of_nonneg_right hs hX
  rw [he] at hL
  nlinarith

/-- 半径上界的数值传递：`r ≤ C1/√q`、`q' ≤ 2q`、`δ ≤ 1/10`、`2C1 ≤ C1'` ⇒
`max ((1+δ) r) (√q')⁻¹ ≤ C1'/√q'`。 -/
theorem radius_upper_real_P6ST4 {r δ q q' C1 C1' : ℝ} (hq : 0 < q) (hq' : 0 < q')
    (hq'2 : q' ≤ 2 * q) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 10) (hC1 : 1 ≤ C1) (hC1' : 2 * C1 ≤ C1')
    (hr : r ≤ C1 / Real.sqrt q) :
    max ((1 + δ) * r) (Real.sqrt q')⁻¹ ≤ C1' / Real.sqrt q' := by
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsq' : 0 < Real.sqrt q' := Real.sqrt_pos.mpr hq'
  have hroot : (1 + δ) * Real.sqrt q' ≤ 2 * Real.sqrt q := by
    have h1 : (1 + δ) * Real.sqrt q' = Real.sqrt ((1 + δ) ^ 2 * q') := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
    have h2 : 2 * Real.sqrt q = Real.sqrt (2 ^ 2 * q) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by norm_num)]
    rw [h1, h2]
    apply Real.sqrt_le_sqrt
    have h3 : (1 + δ) ^ 2 ≤ 2 := by nlinarith
    nlinarith
  apply max_le
  · have h4 : (1 + δ) * r ≤ (1 + δ) * (C1 / Real.sqrt q) :=
      mul_le_mul_of_nonneg_left hr (by linarith)
    refine h4.trans ?_
    rw [← mul_div_assoc, div_le_div_iff₀ hsq hsq']
    have h5 : (1 + δ) * C1 * Real.sqrt q' ≤ 2 * C1 * Real.sqrt q := by nlinarith
    have h6 : 2 * C1 * Real.sqrt q ≤ C1' * Real.sqrt q := mul_le_mul_of_nonneg_right hC1' hsq.le
    linarith
  · rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by linarith) hsq'.le

/-- **OPEN-C positive 型 transfer（抽象）**：`W` positive 型（domain = `comp(x)`）、`Rlow ≤ Q`，`F` 于
`comp(x)` 上的 `C^order` comparison（`2 ≤ order`）且 `δ` 满足只依赖 `C2, Rlow` 的四个显式条件 ⇒
`F x` 处 positive 型 witness `(eps', C1', C2')`，domain = `comp(F x)`。外径无需 margin。 -/
theorem exists_positive_wholeComponent_transport_P6ST4 {C1 C2 Rlow δ : ℝ} (hC1 : 1 ≤ C1)
    (hC2 : 1 ≤ C2) (hRlow : 0 < Rlow) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 10)
    (hδθ : δ * (243 * (Rlow⁻¹ + 3 * C2)) ≤ 1 / (2 * C2)) (hδK : 40 * δ ≤ C2 * Rlow)
    (hδsec : δ ≤ C2⁻¹ / (8 * (C2⁻¹ + 360 / Rlow + C2)))
    (g : SmoothRiemannianMetric I3 P) (x : P) {eps : ℝ}
    (W : SpatialCanonicalWitness g eps C1 C2 x)
    (hpos : ∃ wh d sc, W.alternative = .positive wh d sc) (hRx : Rlow ≤ metricScalarAt g x)
    (g' : SmoothRiemannianMetric I3 N) (F : PartialDiffeomorph I3 I3 P N ∞) {order : ℕ}
    (horder : 2 ≤ order) (hsrc : connectedComponent x ⊆ F.source)
    (C : MetricComparisonOn (fun _ => g) (fun _ => g') F (connectedComponent x) {0} order δ)
    {eps' C1' C2' : ℝ} (heps0 : 0 < eps') (heps1 : eps' < 1) (hC1' : 2 * C1 ≤ C1')
    (hC2' : 1000 * C2 ≤ C2')
    (hgrad : ∀ v : TangentSpace I3 (F x),
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g') (F x) v)| ≤
        C2' * metricScalarAt g' (F x) * Real.sqrt (metricScalarAt g' (F x)) *
          Real.sqrt (g'.inner (F x) v v)) :
    ∃ W' : SpatialCanonicalWitness g' eps' C1' C2' (F x), W'.capTubeHasNeckChart eps' ∧
      W'.domain.carrier = connectedComponent (F x) ∧
      ∃ wh d sc, W'.alternative = .positive wh d sc := by
  have : LocallyConnectedSpace P := ChartedSpace.locallyConnectedSpace ThreeSpace P
  obtain ⟨whole, data, sec, hA⟩ := hpos
  set Q := metricScalarAt g x with hQdef
  have hQ : 0 < Q := hRlow.trans_le hRx
  have hC2p : 0 < C2 := by linarith
  have hcK : IsCompact (connectedComponent x) := whole ▸ W.domain.compact
  let U : Opens P := ⟨connectedComponent x, isOpen_connectedComponent⟩
  have hdomF : W.domain.carrier ⊆ F.source := whole ▸ hsrc
  have hxc : x ∈ connectedComponent x := mem_connectedComponent
  have hrmW : ∀ y ∈ connectedComponent x,
      Real.sqrt (normSq0S (I := I3) g y 4 (metricRm04At g y)) ≤ C2 * Q := by
    intro y hy
    have h := W.rm_bound y (whole ▸ hy)
    rwa [metricRm04_apply] at h
  have hrmW' : ∀ y ∈ (U : Set P),
      Real.sqrt (normSq0S (I := I3) g y 4 (metricRm04 g y)) ≤ C2 * Q :=
    fun y hy => W.rm_bound y (whole ▸ hy)
  -- scalar 闭近：`|R'(F y) − R(y)| ≤ Q/(2C2)`
  have hscal : ∀ y ∈ connectedComponent x,
      |metricScalarAt g' (F y) - metricScalarAt g y| ≤ 1 / (2 * C2) * Q := by
    intro y hy
    have h := C.abs_metricScalarAt_sub_le_of_rm_bound (U := U) hsrc hδ0 (by linarith) horder hy
      (hrmW y hy)
    refine h.trans ?_
    have hQR : 1 ≤ Q * Rlow⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hRlow, one_mul]
      exact hRx
    have hb : 243 * (δ + δ * (3 * (C2 * Q))) ≤ Q * (δ * (243 * (Rlow⁻¹ + 3 * C2))) := by
      nlinarith
    have hc : Q * (δ * (243 * (Rlow⁻¹ + 3 * C2))) ≤ Q * (1 / (2 * C2)) :=
      mul_le_mul_of_nonneg_left hδθ hQ.le
    linarith
  set Q' := metricScalarAt g' (F x) with hQ'def
  have hθ2 : 1 / (2 * C2) ≤ 1 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith
  have hqq := abs_le.mp (hscal x hxc)
  have hθQ : 1 / (2 * C2) * Q ≤ 1 / 2 * Q := mul_le_mul_of_nonneg_right hθ2 hQ.le
  have hQ'2 : Q / 2 ≤ Q' := by linarith [hqq.1]
  have hQ'4 : Q' ≤ 2 * Q := by linarith [hqq.2]
  have hQ' : 0 < Q' := by linarith
  have hr0 : 0 < W.radius :=
    (inv_pos.mpr (Real.sqrt_pos.mpr W.Q_pos)).trans_le W.radius_lower
  set r' := max ((1 + δ) * W.radius) (Real.sqrt Q')⁻¹ with hr'def
  have hr'1 : (1 + δ) * W.radius ≤ r' := le_max_left _ _
  have himg : (F : P → N) '' W.domain.carrier = connectedComponent (F x) := by
    rw [whole]
    exact image_connectedComponent_P6ST4 F hcK hsrc
  -- 内球：自动
  have hin : riemannianBallOf (I := I3) g' (F x) r' ⊆ (F : P → N) '' W.domain.carrier := by
    rw [himg]
    exact riemannianBallOf_subset_connectedComponent_P6ST4 g' (F x) r'
  -- 外径：`d'(F x, F y) ≤ √(1+δ) d(x,y) < 2(1+δ)r ≤ 2r'`
  have hout : (F : P → N) '' W.domain.carrier ⊆ riemannianBallOf (I := I3) g' (F x) (2 * r') := by
    have hRb : 0 < 8 * W.radius := by positivity
    have hball : riemannianClosedBallOf (I := I3) g x (8 * W.radius) ⊆ connectedComponent x :=
      riemannianClosedBallOf_subset_connectedComponent_P6ST4 g x _
    have hcpt : IsCompact (riemannianClosedBallOf (I := I3) g x (8 * W.radius)) :=
      hcK.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf g x _) hball
    have hsp : Real.sqrt (1 + δ) ≤ 1 + δ := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have hsm : 9 / 10 ≤ Real.sqrt (1 - δ) := Real.le_sqrt_of_sq_le (by linarith)
    have hroom : Real.sqrt (1 + δ) * (3 * (2 * W.radius)) <
        Real.sqrt (1 - δ) * (8 * W.radius) := by
      have h1 : Real.sqrt (1 + δ) * (3 * (2 * W.radius)) ≤ 11 / 10 * (6 * W.radius) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      have h2 : 9 / 10 * (8 * W.radius) ≤ Real.sqrt (1 - δ) * (8 * W.radius) :=
        mul_le_mul_of_nonneg_right hsm hRb.le
      linarith
    have htr := crossModel_edist_transfer_of_comparison g g' F C x hRb hδ0 (by linarith)
      (by linarith : (0 : ℝ) ≤ 2 * W.radius) hcpt hball (hball.trans hsrc) hroom
    rintro _ ⟨y, hy, rfl⟩
    have hyb := W.inside_ball hy
    change riemannianEDistOf g x y < ENNReal.ofReal (2 * W.radius) at hyb
    have hy2 : y ∈ riemannianClosedBallOf (I := I3) g x (2 * W.radius) := hyb.le
    have hx2 : x ∈ riemannianClosedBallOf (I := I3) g x (2 * W.radius) := by
      change riemannianEDistOf (I := I3) g x x ≤ _
      rw [riemannianEDistOf_self]
      exact zero_le
    have hfin : riemannianEDistOf g x y ≠ ⊤ := ne_top_of_lt hyb
    have hlt : (riemannianEDistOf g x y).toReal < 2 * W.radius :=
      (ENNReal.lt_ofReal_iff_toReal_lt hfin).mp hyb
    have h := (htr x hx2 y hy2).2
    change riemannianEDistOf g' (F x) (F y) < ENNReal.ofReal (2 * r')
    refine lt_of_le_of_lt h ?_
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have ht0 := ENNReal.toReal_nonneg (a := riemannianEDistOf g x y)
    have h1 : Real.sqrt (1 + δ) * (riemannianEDistOf g x y).toReal ≤
        (1 + δ) * (riemannianEDistOf g x y).toReal := mul_le_mul_of_nonneg_right hsp ht0
    have h2 : (1 + δ) * (riemannianEDistOf g x y).toReal < (1 + δ) * (2 * W.radius) :=
      mul_lt_mul_of_pos_left hlt (by linarith)
    linarith
  -- scalar / Rm / volume
  have hsc : ∀ y ∈ (F : P → N) '' W.domain.carrier,
      C2'⁻¹ * Q' ≤ metricScalarAt g' y ∧ metricScalarAt g' y ≤ C2' * Q' := by
    rintro _ ⟨y, hy, rfl⟩
    exact scalar_bounds_real_P6ST4 hQ hC2 hC2' le_rfl (W.scalar_bounds y hy).1
      (W.scalar_bounds y hy).2 (hscal y (whole ▸ hy)) hQ'2 hQ'4
  have hrm : ∀ y ∈ (F : P → N) '' W.domain.carrier,
      Real.sqrt (normSq0S (I := I3) g' y 4 (metricRm04 g' y)) ≤ C2' * Q' := by
    rintro _ ⟨y, hy, rfl⟩
    have hyc : y ∈ connectedComponent x := whole ▸ hy
    have hK : 40 * δ ≤ C2 * Q := hδK.trans (mul_le_mul_of_nonneg_left hRx hC2p.le)
    have hB : normSq0S g y 4 (metricRm04At g y) ≤ (C2 * Q) ^ 2 := by
      have h0 := normSq0S_nonneg g y 4 (metricRm04At g y)
      have h1 := Real.sq_sqrt h0
      nlinarith [Real.sqrt_nonneg (normSq0S g y 4 (metricRm04At g y)), hrmW y hyc]
    have h := C.rmNormSq_image_le_of_mem_opens (U := U) hsrc hδ0 hδ1 hK horder hyc hB
    rw [metricRm04_apply]
    have h18 : Real.sqrt (normSq0S g' (F y) 4 (metricRm04At g' (F y))) ≤ 18 * (C2 * Q) := by
      calc Real.sqrt (normSq0S g' (F y) 4 (metricRm04At g' (F y)))
          ≤ Real.sqrt ((18 * (C2 * Q)) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 18 * (C2 * Q) := Real.sqrt_sq (by positivity)
    have h3 : 36 * C2 * Q' ≤ C2' * Q' := mul_le_mul_of_nonneg_right (by linarith) hQ'.le
    nlinarith
  have hvol : ENNReal.ofReal (C2'⁻¹ / (Q' * Real.sqrt Q')) ≤
      riemannianVolumeMeasure I3 N g' ((F : P → N) '' W.domain.carrier) := by
    have hvolW : ENNReal.ofReal (C2⁻¹ / (Q * Real.sqrt Q)) ≤
        riemannianVolumeMeasure I3 P g W.domain.carrier :=
      W.volume (by rw [hA]; trivial)
    have hV := MetricComparisonOn.volume_image_ge F C rfl hδ0 (by linarith) U.isOpen subset_rfl
      hsrc W.domain.compact (le_of_eq whole)
    have hdim : Module.finrank ℝ ThreeSpace = 3 := finrank_euclideanSpace_fin
    rw [hdim] at hV
    calc ENNReal.ofReal (C2'⁻¹ / (Q' * Real.sqrt Q'))
        ≤ ENNReal.ofReal (Real.sqrt ((1 - δ) ^ 3) * (C2⁻¹ / (Q * Real.sqrt Q))) :=
          ENNReal.ofReal_le_ofReal (volume_lower_real_P6ST4 hδ1 hQ hQ'2 hC2 hC2')
      _ = ENNReal.ofReal (Real.sqrt ((1 - δ) ^ 3)) * ENNReal.ofReal (C2⁻¹ / (Q * Real.sqrt Q)) :=
          ENNReal.ofReal_mul (Real.sqrt_nonneg _)
      _ ≤ ENNReal.ofReal (Real.sqrt ((1 - δ) ^ 3)) * riemannianVolumeMeasure I3 P g
            W.domain.carrier := mul_le_mul' le_rfl hvolW
      _ ≤ _ := hV
  -- alternative：positive（`PositiveComponent` 搬运 + (C1) `SecLower`）
  have hsec' : SecLower g' (C2'⁻¹ * Q') ((F : P → N) '' W.domain.carrier) := by
    rw [whole]
    exact secLower_image_of_comparison_P6ST4 C U hsrc subset_rfl horder hδ0 (by linarith) hδsec
      hC2 hC2' hRlow hRx hQ'4
      (by change SecLower g (C2⁻¹ * Q) (connectedComponent x); rw [← whole]; exact sec) hrmW'
  have hxint : F x ∈ interior (W.domain.map F hdomF).carrier := by
    rw [CompactDomain.map_carrier, ← partialDiffeomorph_image_interior_of_subset_source F hdomF]
    exact ⟨x, W.center_inside, rfl⟩
  let A' : SpatialCanonicalAlternative g' eps' C2' (F x) (W.domain.map F hdomF).carrier :=
    .positive himg (Classical.choice (positiveComponent_transport_of_partialDiffeomorph data F
      hdomF)) hsec'
  let W' : SpatialCanonicalWitness g' eps' C1' C2' (F x) :=
    { Q_pos := hQ'
      eps_pos := heps0
      eps_lt_one := heps1
      domain := W.domain.map F hdomF
      center_inside := hxint
      radius := r'
      radius_lower := le_max_right _ _
      radius_upper := radius_upper_real_P6ST4 hQ hQ' hQ'4 hδ0 hδ1 hC1 hC1' W.radius_upper
      ball_inside := hin
      inside_ball := hout
      scalar_bounds := hsc
      rm_bound := hrm
      alternative := A'
      volume := fun _ => hvol
      gradient := hgrad }
  refine ⟨W', ?_, himg, _, _, _, rfl⟩
  intro cap depth heq
  cases heq

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature
open Perelman.CanonicalNeighborhood.FiniteHorn

universe u

/-- positive 型 transfer 的 `δ`：只依赖 `C2, Rlow` 的显式选择。 -/
theorem exists_positiveDelta_P6ST4 {C2 Rlow : ℝ} (hC2 : 1 ≤ C2) (hRlow : 0 < Rlow) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 10 ∧ δ * (243 * (Rlow⁻¹ + 3 * C2)) ≤ 1 / (2 * C2) ∧
      40 * δ ≤ C2 * Rlow ∧ δ ≤ C2⁻¹ / (8 * (C2⁻¹ + 360 / Rlow + C2)) := by
  have hC2p : 0 < C2 := by linarith
  have hA : 0 < 243 * (Rlow⁻¹ + 3 * C2) := by positivity
  have hsec := secDelta_pos_P6ST4 hC2 hRlow
  refine ⟨min (1 / 10) (min (1 / (2 * C2) / (243 * (Rlow⁻¹ + 3 * C2)))
    (min (C2 * Rlow / 40) (C2⁻¹ / (8 * (C2⁻¹ + 360 / Rlow + C2))))),
    lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) hsec)),
    min_le_left _ _, ?_, ?_, ?_⟩
  · have h : min (1 / 10) (min (1 / (2 * C2) / (243 * (Rlow⁻¹ + 3 * C2)))
        (min (C2 * Rlow / 40) (C2⁻¹ / (8 * (C2⁻¹ + 360 / Rlow + C2))))) ≤
        1 / (2 * C2) / (243 * (Rlow⁻¹ + 3 * C2)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    rwa [le_div_iff₀ hA] at h
  · have h : min (1 / 10) (min (1 / (2 * C2) / (243 * (Rlow⁻¹ + 3 * C2)))
        (min (C2 * Rlow / 40) (C2⁻¹ / (8 * (C2⁻¹ + 360 / Rlow + C2))))) ≤ C2 * Rlow / 40 :=
      ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
    linarith
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

/-- **OPEN-C positive 型 transfer（event 层，0 binder）**：`RegularCrossing p q` + `comp(p)` 与 cut tubes
不交 + `v n ↑ s` 上 eventually positive 型 fine witness `(ηfine, C1, C2)`（domain = `comp(p)`）+
`R⁺(q) > 0` ⇒ `q` 处 positive 型 witness `(ηout, C1out, C2out)`，domain = `comp(q)`
（`2C1 ≤ C1out`、`1000C2 ≤ C2out`；survivor `J`、整 component comparison 由 STAB3 G4，`SecLower` 由 G2，
外径无 margin）。 -/
theorem wholeComponent_positive_transfer_P6ST4 (E : MetricCutCapEvent P Q a s) {p : P.Carrier}
    {q : Q.Carrier} (hcross : E.RegularCrossing p q)
    (htube : ∀ i, Disjoint (connectedComponent p)
      (Set.range (E.transition.trace.tubes.tube i)))
    {v : ℕ → ℝ} (hv : ∀ n, v n ∈ Ioo a s) (hvt : Tendsto v atTop (𝓝 s))
    (hQ : 0 < metricScalarAt E.outputMetric q) {ηfine C1 C2 : ℝ} (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2)
    (hfine : ∀ᶠ n in atTop, ∃ W : SpatialCanonicalWitness (E.incoming.flow.base.metric (v n))
      ηfine C1 C2 p, ∃ wh d sc, W.alternative = .positive wh d sc)
    {ηout C1out C2out : ℝ} (hη0 : 0 < ηout) (hη1 : ηout < 1) (h1 : 2 * C1 ≤ C1out)
    (h2 : 1000 * C2 ≤ C2out) :
    ∃ W : SpatialCanonicalWitness E.outputMetric ηout C1out C2out q,
      W.capTubeHasNeckChart ηout ∧ W.domain.carrier = connectedComponent q ∧
      ∃ wh d sc, W.alternative = .positive wh d sc := by
  obtain ⟨J, hJ, hsub, -, -, hcmp⟩ := E.wholeComponent_survivor_P6ST3 hcross
    (E.connectedComponent_subset_interior_old_P6ST4 hcross htube)
  obtain ⟨δ, hδ, hδ1, hδθ, hδK, hδsec⟩ := exists_positiveDelta_P6ST4 hC2 (half_pos hQ)
  have hsc := E.scalar_tendsto_of_regularCrossing_P6ST3 hcross hv hvt
  have hC : C2 ≤ C2out := by linarith
  have hgrad : ∀ w : TangentSpace I3 q,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt E.outputMetric) q w)| ≤
        C2out * metricScalarAt E.outputMetric q * Real.sqrt (metricScalarAt E.outputMetric q) *
          Real.sqrt (E.outputMetric.inner q w w) := by
    intro w
    obtain ⟨u, hu1, hu2⟩ := E.gradient_tendsto_of_regularCrossing_P6ST3 hcross hv hvt w
    have hev : ∀ᶠ n in atTop,
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ)
            (metricScalarAt (E.incoming.flow.base.metric (v n))) p u)| ≤
          C2 * metricScalarAt (E.incoming.flow.base.metric (v n)) p *
            Real.sqrt (metricScalarAt (E.incoming.flow.base.metric (v n)) p) *
            Real.sqrt ((E.incoming.flow.base.metric (v n)).inner p u u) := by
      filter_upwards [hfine] with n hn
      obtain ⟨W, -⟩ := hn
      exact W.gradient u
    have hR := ((tendsto_const_nhds (x := C2)).mul hsc).mul hsc.sqrt
    have hlim := le_of_tendsto_of_tendsto hu1.abs (hR.mul hu2.sqrt) hev
    exact hlim.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC hQ.le) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hcmpn := (tendsto_nhdsLT_of_slab_P6ST3 hv hvt).eventually (hcmp 2 δ hδ)
  have hlow : ∀ᶠ n in atTop, metricScalarAt E.outputMetric q / 2 ≤
      metricScalarAt (E.incoming.flow.base.metric (v n)) p :=
    hsc.eventually (eventually_ge_nhds (half_lt_self hQ))
  obtain ⟨n, ⟨W, hpos⟩, ⟨C⟩, hlo⟩ := (hfine.and (hcmpn.and hlow)).exists
  subst hJ
  exact exists_positive_wholeComponent_transport_P6ST4 hC1 hC2 (half_pos hQ) hδ.le hδ1 hδθ hδK
    hδsec _ p W hpos hlo E.outputMetric J le_rfl hsub C hη0 hη1 h1 h2 hgrad

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

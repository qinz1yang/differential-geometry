import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BufferedTransferP6ST2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientLimitSurvivorCanonicalWitness

/-!
# S-c P-W：restrictOpen witness conversion 的 margins 版（O-CH11-STAB4 G1，后缀 `_P6ST4`）

STAB3 G4 判定 P-W 的 repair target (a)：树内
`exists_spatialCanonicalWitness_of_canonicalWitness_restrictOpen`
（`Surgery/Topology/AncientLimitSurvivorCanonicalWitness.lean:401`）的结论不带 `HasMargins`。
本文件逐步重做该 conversion（cast metric → `pushforward` along `Subtype.val` → `scaleMetric R⁻¹` → cast），
证明每一步都**原样**保持 `HasMargins m`（`restrictOpen` / pushforward 是等距，`scaleMetric` 是相似）：
* `hasMargins_scaleMetric_P6ST4`：`W.HasMargins m ⇒ (W.scaleMetric c hc).HasMargins m`（半径 `√c·r`，
  `R ↦ c⁻¹R`、距离 `↦ √c·d`，五个条件都是 scale-invariant）；
* `hasMargins_pushforward_P6ST4`：等距 pushforward（`2r < R`、闭球紧 ⊆ source）保持 margins
  （ball 等式 `e '' B(x,ρ) = B(e x, ρ)`，`ρ = (1+m)r, (2−m)r < R`；cap tube 深度用 `d_h ≤ d_g ∘ e`）；
* **`exists_spatialCanonicalWitness_of_canonicalWitness_restrictOpen_margins_P6ST4`**：源
  `K.toSpatial.HasMargins m` ⇒ 输出 `W.capTubeHasNeckChart ε ∧ W.HasMargins m`（同一 `m`，`0 < m ≤ 1/2`）。
consumer `BufferedTransferData_P6ST2.ofRestrictOpenMargins_P6ST4`：footprint 层 + 每个 `v n` 处的
restrictOpen κ-witness（带 `toSpatial.HasMargins m`）⇒ STAB2 完整合同（`fine` 字段由本文件生产）。
κ-solution witness producer 本身的 margins 版（`toSpatial.HasMargins m₀` 的来源）不在本文件：见 DELIVERIES G1 块
BLOCKED repair target。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PartialDiffeomorph (image_riemannianBall_eq_of_isometric_on_compact_ball)

universe u

section Margins

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {eps C1 C2 m alpha : ℝ}

/-- metric cast（`g = g'`）保持 chart 与 margins。 -/
theorem exists_hasMargins_cast_metric_P6ST4 {g g' : SmoothRiemannianMetric I3 M} (hg : g = g')
    {x : M} (W : SpatialCanonicalWitness g eps C1 C2 x) (hW : W.capTubeHasNeckChart alpha)
    (hM : W.HasMargins m) :
    ∃ W' : SpatialCanonicalWitness g' eps C1 C2 x, W'.capTubeHasNeckChart alpha ∧
      W'.HasMargins m ∧ W'.radius = W.radius := by
  subst hg
  exact ⟨W, hW, hM, rfl⟩

/-- point cast（`p = q`）保持 chart 与 margins。 -/
theorem exists_hasMargins_cast_point_P6ST4 {g : SmoothRiemannianMetric I3 M} {p q : M}
    (hpq : p = q) (W : SpatialCanonicalWitness g eps C1 C2 p) (hW : W.capTubeHasNeckChart alpha)
    (hM : W.HasMargins m) :
    ∃ W' : SpatialCanonicalWitness g eps C1 C2 q, W'.capTubeHasNeckChart alpha ∧
      W'.HasMargins m := by
  subst hpq
  exact ⟨W, hW, hM⟩

/-- **scaling**：`HasMargins` 在 `scaleMetric c` 下保持（半径 `√c·r`，scalar `c⁻¹R`，距离 `√c·d`）。 -/
theorem hasMargins_scaleMetric_P6ST4 {g : SmoothRiemannianMetric I3 M} {x : M}
    (c : ℝ) (hc : 0 < c) {W : SpatialCanonicalWitness g eps C1 C2 x} (h : W.HasMargins m) :
    (W.scaleMetric c hc).HasMargins m := by
  obtain ⟨hshape, hrad, hin, hout, hdeep⟩ := h
  have halt : (W.scaleMetric c hc).alternative = W.alternative.scaleMetric c hc := rfl
  have hQ := W.Q_pos
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsQ : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr hQ
  have hroot : Real.sqrt (metricScalarAt (DifferentialGeometry.scaleMetric c hc g) x) =
      Real.sqrt (metricScalarAt g x) / Real.sqrt c := by
    rw [metricScalarAt_scaleMetric, Real.sqrt_mul (inv_nonneg.mpr hc.le), Real.sqrt_inv,
      inv_mul_eq_div]
  have hdiv : ∀ a : ℝ, a / Real.sqrt (metricScalarAt (DifferentialGeometry.scaleMetric c hc g) x) =
      Real.sqrt c * (a / Real.sqrt (metricScalarAt g x)) := by
    intro a
    rw [hroot]
    field_simp
  have hball : ∀ ρ : ℝ, riemannianBallOf (I := I3) (DifferentialGeometry.scaleMetric c hc g) x
      (Real.sqrt c * ρ) = riemannianBallOf (I := I3) g x ρ :=
    fun ρ => DifferentialGeometry.riemannianBallOf_scaleMetric c hc g x ρ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [halt]
    rcases hshape with ⟨n, hn⟩ | ⟨cc, d, hcd⟩
    · exact Or.inl ⟨_, by rw [hn]; rfl⟩
    · exact Or.inr ⟨_, _, by rw [hcd]; rfl⟩
  · change (1 + m) / Real.sqrt (metricScalarAt (DifferentialGeometry.scaleMetric c hc g) x) ≤
      Real.sqrt c * W.radius
    rw [hdiv]
    exact mul_le_mul_of_nonneg_left hrad hsc.le
  · change riemannianBallOf (I := I3) (DifferentialGeometry.scaleMetric c hc g) x
      ((1 + m) * (Real.sqrt c * W.radius)) ⊆ W.domain.carrier
    rw [show (1 + m) * (Real.sqrt c * W.radius) = Real.sqrt c * ((1 + m) * W.radius) by ring,
      hball]
    exact hin
  · change W.domain.carrier ⊆ riemannianBallOf (I := I3)
      (DifferentialGeometry.scaleMetric c hc g) x ((2 - m) * (Real.sqrt c * W.radius))
    rw [show (2 - m) * (Real.sqrt c * W.radius) = Real.sqrt c * ((2 - m) * W.radius) by ring,
      hball]
    exact hout
  · intro cc d heq
    rw [halt] at heq
    cases hW : W.alternative with
    | neck data =>
      rw [hW] at heq
      cases heq
    | cap data deep =>
      rw [hW] at heq
      change SpatialCanonicalAlternative.cap (data.scaleMetric c hc) (deep_scaleMetric c hc deep) =
        SpatialCanonicalAlternative.cap cc d at heq
      cases heq
      intro y hy
      rw [hdiv, metricDistance_scaleMetric]
      exact mul_le_mul_of_nonneg_left (hdeep data deep hW y hy) hsc.le
    | positive whole data sec =>
      rw [hW] at heq
      cases heq
    | round whole data =>
      rw [hW] at heq
      cases heq

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
/-- witness domain 落在 `B(x, 2r)` 内，故 `2r < R` 时落在任何包含 `B̄(x,R)` 的集合内。 -/
theorem domain_subset_of_ball_subset_P6ST4 {h : SmoothRiemannianMetric I3 N} {x : N}
    (W : SpatialCanonicalWitness h eps C1 C2 x) {S : Set N} {R : ℝ} (hR : 2 * W.radius < R)
    (hsrc : riemannianClosedBallOf h x R ⊆ S) : W.domain.carrier ⊆ S := by
  have hr : 0 < W.radius :=
    (inv_pos.mpr (Real.sqrt_pos.mpr W.Q_pos)).trans_le W.radius_lower
  refine W.inside_ball.trans (fun y hy => hsrc ?_)
  exact le_of_lt (lt_trans hy ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hR))

omit [SigmaCompactSpace M] in
/-- 等距 `e`（闭球 `B̄(x,R)` 紧 ⊆ source，`2r < R`）下 domain 点的距离不缩：`d_h(x,y) ≤ d_g(e x, e y)`。 -/
theorem metricDistance_le_image_P6ST4 {g : SmoothRiemannianMetric I3 M}
    {h : SmoothRiemannianMetric I3 N} {x : N} (W : SpatialCanonicalWitness h eps C1 C2 x)
    (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {R : ℝ} (hR : 2 * W.radius < R) (hcpt : IsCompact (riemannianClosedBallOf h x R))
    (hsrc : riemannianClosedBallOf h x R ⊆ e.source) :
    ∀ y ∈ W.domain.carrier, metricDistance h x y ≤ metricDistance g (e x) (e y) := by
  have hr : 0 < W.radius :=
    (inv_pos.mpr (Real.sqrt_pos.mpr W.Q_pos)).trans_le W.radius_lower
  have hdom := domain_subset_of_ball_subset_P6ST4 W hR hsrc
  have hB2 := image_riemannianBall_eq_of_isometric_on_compact_ball h g e x
    (by linarith : 0 < 2 * W.radius) hR hcpt hsrc (fun z hz v => hiso z (hsrc hz) v v)
  intro y hy
  apply metricDistance_le_of_isometryOn e hiso hcpt hsrc (hdom hy)
  have hy2 : e y ∈ riemannianBallOf g (e x) (2 * W.radius) := by
    rw [← hB2]
    exact ⟨y, W.inside_ball hy, rfl⟩
  exact lt_trans hy2 ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hR)

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
/-- alternative 的 pushforward 保持 neck / cap 形状。 -/
theorem pushforward_shape_P6ST4 {g : SmoothRiemannianMetric I3 M}
    {h : SmoothRiemannianMetric I3 N} {C : ℝ} {x : N} {V : Set N}
    (A : SpatialCanonicalAlternative h eps C x V) (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    (hV : V ⊆ e.source) (hVc : IsCompact V)
    (hdist : ∀ y ∈ V, metricDistance h x y ≤ metricDistance g (e x) (e y))
    (hneck : ∀ n, A = .neck n → ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, n.neck.map z ∈ e.source)
    (hcap : ∀ c d, A = .cap c d →
      ∀ i, ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (c.chain.necks i).map z ∈ e.source)
    (hshape : (∃ n, A = .neck n) ∨ ∃ c d, A = .cap c d) :
    (∃ n, A.pushforward e hiso hV hVc hdist hneck hcap = .neck n) ∨
      ∃ c d, A.pushforward e hiso hV hVc hdist hneck hcap = .cap c d := by
  cases A with
  | neck data => exact Or.inl ⟨_, rfl⟩
  | cap data deep => exact Or.inr ⟨_, _, rfl⟩
  | positive whole data sec =>
    rcases hshape with ⟨_, hn⟩ | ⟨_, _, hn⟩ <;> cases hn
  | round whole data =>
    rcases hshape with ⟨_, hn⟩ | ⟨_, _, hn⟩ <;> cases hn

/-- **等距 pushforward** 保持 `HasMargins m`（`0 < m ≤ 1/2`，`2r < R`，闭球 `B̄(x,R)` 紧 ⊆ source）。 -/
theorem hasMargins_pushforward_P6ST4 {g : SmoothRiemannianMetric I3 M}
    {h : SmoothRiemannianMetric I3 N} {x : N} {W : SpatialCanonicalWitness h eps C1 C2 x}
    (hM : W.HasMargins m) (hm0 : 0 < m) (hm1 : m ≤ 1 / 2) (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {R : ℝ} (hR : 2 * W.radius < R) (hcpt : IsCompact (riemannianClosedBallOf h x R))
    (hsrc : riemannianClosedBallOf h x R ⊆ e.source)
    (hneck : ∀ n, W.alternative = .neck n →
      ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, n.neck.map z ∈ e.source)
    (hcap : ∀ c d, W.alternative = .cap c d →
      ∀ i, ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (c.chain.necks i).map z ∈ e.source) :
    (W.pushforward e hiso hR hcpt hsrc hneck hcap).HasMargins m := by
  obtain ⟨hshape, hrad, hin, hout, hdeep⟩ := hM
  have hr : 0 < W.radius :=
    (inv_pos.mpr (Real.sqrt_pos.mpr W.Q_pos)).trans_le W.radius_lower
  have hdom : W.domain.carrier ⊆ e.source := domain_subset_of_ball_subset_P6ST4 W hR hsrc
  have hdist := metricDistance_le_image_P6ST4 W e hiso hR hcpt hsrc
  have hx : x ∈ e.source := hdom (interior_subset W.center_inside)
  have hRx := metricScalarAt_eq_of_isometryOn e hiso hx
  have halt : (W.pushforward e hiso hR hcpt hsrc hneck hcap).alternative =
      W.alternative.pushforward e hiso hdom W.domain.compact hdist hneck hcap := rfl
  have hquad : ∀ z ∈ riemannianClosedBallOf h x R, ∀ v : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z v) = h.inner z v v :=
    fun z hz v => hiso z (hsrc hz) v v
  have hB : ∀ ρ : ℝ, 0 < ρ → ρ < R →
      (e : N → M) '' riemannianBallOf h x ρ = riemannianBallOf g (e x) ρ :=
    fun ρ hρ hρR => image_riemannianBall_eq_of_isometric_on_compact_ball
      h g e x hρ hρR hcpt hsrc hquad
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [halt]
    exact pushforward_shape_P6ST4 _ e hiso hdom W.domain.compact hdist hneck hcap hshape
  · change (1 + m) / Real.sqrt (metricScalarAt g (e x)) ≤ W.radius
    rw [hRx]
    exact hrad
  · change riemannianBallOf (I := I3) g (e x) ((1 + m) * W.radius) ⊆ e '' W.domain.carrier
    rw [← hB _ (by positivity) (by nlinarith)]
    exact image_mono hin
  · change e '' W.domain.carrier ⊆ riemannianBallOf (I := I3) g (e x) ((2 - m) * W.radius)
    rw [← hB _ (by nlinarith) (by nlinarith)]
    exact image_mono hout
  · intro cap depth heq
    rw [halt] at heq
    obtain ⟨data, deep, hA, htube⟩ := SpatialCanonicalAlternative.pushforward_eq_cap heq
    intro y hy
    rw [← cap.tube_eq] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [htube z, hRx]
    have hw : data.tubeMap z ∈ data.tube := data.tube_eq ▸ ⟨z, hz, rfl⟩
    have hwd : data.tubeMap z ∈ W.domain.carrier :=
      (subset_union_right.trans data.union_eq.ge) hw
    exact (hdeep data deep hA _ hw).trans (hdist _ hwd)

end Margins

section RestrictOpen

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)

omit [SigmaCompactSpace M] in
theorem scaleMetric_restrictOpen_eq_P6ST4 (g : SmoothRiemannianMetric I3 M) (W : Opens M) {c : ℝ}
    (hc : 0 < c) :
    scaleMetric c hc (g.restrictOpen W) = (scaleMetric c hc g).restrictOpen W := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rfl

/-- **P-W (a)，margins 版**：`exists_spatialCanonicalWitness_of_canonicalWitness_restrictOpen` 加
`K.toSpatial.HasMargins m` 前提与 `W.HasMargins m` 结论（同一 `m`；cast / `Subtype.val` pushforward /
`scaleMetric R⁻¹` 每步保持 margins）。 -/
theorem exists_spatialCanonicalWitness_of_canonicalWitness_restrictOpen_margins_P6ST4
    [CompactSpace M] (g : SmoothRiemannianMetric I3 M) {R : ℝ} (hR : 0 < R) (U : Opens M)
    (x : U) (hQ : metricScalarAt g x.val = R) {L : ℝ} (hL : -L ≤ 0)
    (h : ℝ → SmoothRiemannianMetric I3 U) (hh0 : h 0 = scaleMetric R hR (g.restrictOpen U))
    {ε C m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1 / 2)
    (K : CanonicalWitness ({ base.metric := h } : SolutionOn (I := I3) (M := U)
      (RealTimeInterval.closed (-L) 0 hL)) ε C C x 0)
    (hK : K.capTubeHasNeckChart ε) (hKm : K.toSpatial.HasMargins m)
    (hball : riemannianClosedBallOf (scaleMetric R hR g) x.val (2 * C + 1) ⊆ U) :
    ∃ W : SpatialCanonicalWitness g ε C C x.val, W.capTubeHasNeckChart ε ∧ W.HasMargins m := by
  set g' : SmoothRiemannianMetric I3 M := scaleMetric R hR g with hg'
  have hpull : h 0 = localPullMetric g' Subtype.val (isLocalDiffeomorph_subtype_val U) := by
    rw [hh0, scaleMetric_restrictOpen_eq_P6ST4, localPullMetric_subtype_val]
  have hscal : metricScalarAt (h 0) x = 1 := by
    rw [hh0, Geometry.Curvature.metricScalarAt_scaleMetric, metricScalarAt_restrictOpen, hQ,
      inv_mul_cancel₀ hR.ne']
  have hrad0 : K.toSpatial.radius ≤ C := by
    have h1 := K.radius_upper
    change K.radius ≤ C / Real.sqrt (metricScalarAt (h 0) x) at h1
    rw [hscal, Real.sqrt_one, div_one] at h1
    exact h1
  obtain ⟨W₀, hW₀, hM₀, hr₀⟩ := exists_hasMargins_cast_metric_P6ST4 hpull K.toSpatial
    (K.capTubeHasNeckChart_toSpatial hK) hKm
  have hrad : W₀.radius ≤ C := hr₀ ▸ hrad0
  have hR' : 2 * W₀.radius < 2 * C + 1 := by linarith
  have hcl : IsCompact (riemannianClosedBallOf g' x.val (2 * C + 1)) :=
    (Geometry.Metric.isClosed_riemannianClosedBallOf g' x.val _).isCompact
  have hpre : IsCompact {z : U | z.val ∈ riemannianClosedBallOf g' x.val (2 * C + 1)} :=
    _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hcl
      (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hball)
  have hcpt : IsCompact (riemannianClosedBallOf
      (localPullMetric g' Subtype.val (isLocalDiffeomorph_subtype_val U)) x (2 * C + 1)) := by
    refine hpre.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _) ?_
    intro z hz
    change riemannianEDistOf _ _ _ ≤ _ at hz ⊢
    rw [localPullMetric_subtype_val] at hz
    exact (riemannianEDistOf_le_restrictOpen g' U x z).trans hz
  have hloc : IsLocalDiffeomorph I3 I3 ∞ (Subtype.val : U → M) := isLocalDiffeomorph_subtype_val U
  obtain ⟨e, hes, -, hef⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (hloc.isLocalDiffeomorphOn univ) isOpen_univ
    ⟨x, trivial⟩ Subtype.val_injective.injOn
  have hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g'.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) =
        (localPullMetric g' Subtype.val (isLocalDiffeomorph_subtype_val U)).inner z v w := by
    intro z _ v w
    rw [hef, localPullMetric_inner]
  have hmem : ∀ y : U, y ∈ e.source := fun y => hes ▸ mem_univ y
  let W₁ := W₀.pushforward e hiso hR' hcpt (fun y _ => hmem y) (fun _ _ z _ => hmem _)
    (fun _ _ _ _ z _ => hmem _)
  have hW₁ : W₁.capTubeHasNeckChart ε :=
    hW₀.pushforward e hiso hR' hcpt (fun y _ => hmem y) _ _ fun _ _ _ _ _ _ z _ => hmem _
  have hM₁ : W₁.HasMargins m :=
    hasMargins_pushforward_P6ST4 hM₀ hm0 hm1 e hiso hR' hcpt (fun y _ => hmem y) _ _
  have heq : scaleMetric R⁻¹ (inv_pos.mpr hR) g' = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [hg', scaleMetric_inner, scaleMetric_inner, inv_mul_cancel_left₀ hR.ne']
  obtain ⟨W₂, hW₂, hM₂, -⟩ := exists_hasMargins_cast_metric_P6ST4 heq
    (W₁.scaleMetric R⁻¹ (inv_pos.mpr hR)) (hW₁.scaleMetric R⁻¹ (inv_pos.mpr hR))
    (hasMargins_scaleMetric_P6ST4 R⁻¹ (inv_pos.mpr hR) hM₁)
  have hex : e x = x.val := by rw [hef]
  exact exists_hasMargins_cast_point_P6ST4 hex W₂ hW₂ hM₂

end RestrictOpen

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature
open Perelman.CanonicalNeighborhood.FiniteHorn

universe u

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {p : P.Carrier} {q : Q.Carrier} {ηfine ηout C m : ℝ} {k : ℕ}

/-- **consumer（P-W → 合同 `fine`）**：footprint 层（`C1 = C2 = C`）+ fine 精度 + 每个 `v n` 处的
restrictOpen κ-witness 数据（开集 `U ∋ p`、`h 0 = R_n·g(v n)|U`、`K` 带 chart 与 `toSpatial.HasMargins m`、
`B̄_{R_n g(v n)}(p, 2C+1) ⊆ U`）eventually ⇒ STAB2 完整合同 `BufferedTransferData_P6ST2`。 -/
def BufferedTransferData_P6ST2.ofRestrictOpenMargins_P6ST4
    (D : E.BufferedFootprintData_P6ST2 p q ηout C C m k)
    (hle : ηfine ≤ neckModelTolerance (ηout / 2))
    (hrec : ∀ᶠ n in atTop, ∃ (U : Opens P.Carrier) (hp : p ∈ U)
      (hR : 0 < metricScalarAt (E.incoming.flow.base.metric (D.v n)) p) (L : ℝ) (hL : -L ≤ 0)
      (h : ℝ → SmoothRiemannianMetric I3 U)
      (_ : h 0 = scaleMetric _ hR ((E.incoming.flow.base.metric (D.v n)).restrictOpen U))
      (K : CanonicalWitness ({ base.metric := h } : SolutionOn (I := I3) (M := U)
        (RealTimeInterval.closed (-L) 0 hL)) ηfine C C ⟨p, hp⟩ 0),
      K.capTubeHasNeckChart ηfine ∧ K.toSpatial.HasMargins m ∧
        riemannianClosedBallOf (scaleMetric _ hR (E.incoming.flow.base.metric (D.v n))) p
          (2 * C + 1) ⊆ U) :
    E.BufferedTransferData_P6ST2 p q ηfine ηout C C m k :=
  BufferedTransferData_P6ST2.ofFootprint_P6ST2 D hle (hrec.mono fun _ ⟨U, hp, hR, _, hL, h, hh0,
    K, hK, hKm, hball⟩ =>
      exists_spatialCanonicalWitness_of_canonicalWitness_restrictOpen_margins_P6ST4 _ hR U
        ⟨p, hp⟩ rfl hL h hh0 D.m_pos D.m_le K hK hKm hball)

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

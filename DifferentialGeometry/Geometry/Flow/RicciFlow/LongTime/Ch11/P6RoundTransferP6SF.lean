import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WholeComponentTransferP6ST4
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PartialJetBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalAlternativeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticRescalingComparison
import DifferentialGeometry.Geometry.Metric.Construction.TensorOpenExtension
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

/-!
# S-c OPEN-C：round 型 whole-component witness 的 transfer（O-CH11-SCFIN G3，后缀 `_P6SF`）

STAB4 G3 的 round 支 BLOCKED 于"树内 `MetricComparisonOn.trans` 的 `TransportedErrorTower` 只能由**全局**
`Phi : Z ≃ₘ P` 构造"（`ofPullbackCrossOfClose`）。本文件走 repair target (i)：**partial-pullback tower**。
* `exists_tensor0SField_eq_partialPullback_P6SF`：紧集上沿 `PartialDiffeomorph` 拉回 tensor（树内
  `WindowedModelLocalPull` 私有引理的公开重证：`toOpensDiffeo` + `restrictOpen0S` + open-subtype 延拓）。
* **`partialTower_P6SF`**：`G : L ⇢ P`、`G.source = univ`、`L` 紧 ⇒ `TransportedErrorTower`（常数
  `backgroundJetConstant·(order+1)`，与全局版相同）；jet 界用树内
  `tensor02CovDerivNormWith_le_of_partial_pullback_comparison`（`PartialJetBound.lean`），不需全局 `Phi`。
* **`SpatialRoundComponent.transport_P6SF`**：round 数据 `R`（`R.map : Z ⇢ P`，target = `U`）+ `F` 于
  `U` 的 scaled comparison ⇒ `F '' U` 上的 round 数据（`map := R.map.trans F`，comparison 由 `trans` +
  partial tower）。
* `exists_round_wholeComponent_transport_P6SF`（抽象）：round 型 witness（domain = `comp(x)`）+ `F` 于
  `comp(x)` 的 `C^order'` comparison（`δ` 显式条件，只依赖 `C2, Rlow, order'` 与目标精度 `epsc`）⇒ `F x` 处
  round 型 witness，domain = `comp(F x)`（scaled comparison 由树内 `staticRescale`）。
* event 层 **`MetricCutCapEvent.wholeComponent_round_transfer_P6SF`**（0 binder；fine witness 只需
  **frequently**）；**OPEN-C 完整**：`wholeComponent_transfer_P6SF`（positive ∨ round，eventually）与
  逆否 **`frequently_not_wholeComponent_P6SF`**（目标层无 witness ⇒ frequently `(v n, p)` 无
  whole-component fine witness），positive 支用 STAB4 G3 `wholeComponent_positive_transfer_P6ST4`。
精度：`0 < ηfine < ηout ≤ 1/2`、`ηfine ≤ backgroundJetSmallness ⌈ηout⁻¹⌉₊`（数值前提，非 binder）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section PartialTower

variable {L : Type u} [TopologicalSpace L] [ChartedSpace ThreeSpace L] [IsManifold I3 ∞ L]
  [T2Space L] [SigmaCompactSpace L]
  {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]
  {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace L] [T2Space P] [SigmaCompactSpace P] in
/-- 紧集上沿 partial diffeo 拉回 2-tensor：`B y v = A (G y) (dG v)`（`K` 紧、`K ⊆ G.source`）。 -/
theorem exists_tensor0SField_eq_partialPullback_P6SF (G : PartialDiffeomorph I3 I3 L P ∞)
    {K : Set L} (hK : IsCompact K) (hKG : K ⊆ G.source)
    (A : Tensor0SField (I := I3) (M := P) (n := ∞) 2) :
    ∃ B : Tensor0SField (I := I3) (M := L) (n := ∞) 2, ∀ y ∈ K,
      ∀ v : Fin 2 → TangentSpace I3 y,
        B y v = A (G y) (fun j => mfderiv I3 I3 G y (v j)) := by
  let U : TopologicalSpace.Opens L := ⟨G.source, G.open_source⟩
  let V : TopologicalSpace.Opens P :=
    ⟨G '' (U : Set L), DifferentialGeometry.image_opens_isOpen G (U := U) subset_rfl⟩
  let psi := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo G (U := U) subset_rfl
  let C := pullbackTensor02FieldCross psi (restrictOpen0S (I := I3) 2 (V := V) A)
  obtain ⟨B, hB⟩ := DifferentialGeometry.exists_tensor0SField_eqOn_openSubtype 2 U hK hKG C
  refine ⟨B, fun y hy v => ?_⟩
  refine (hB ⟨y, hKG hy⟩ hy v).trans ?_
  refine (pullbackTensor02FieldCross_apply psi _ ⟨y, hKG hy⟩ v).trans ?_
  change A (G y) (fun j => mfderiv I3 I3 psi ⟨y, hKG hy⟩ (v j)) = _
  congr 1
  funext j
  exact DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo G subset_rfl _ (v j)

/-- **partial-pullback `TransportedErrorTower`**：`G : L ⇢ P`（`G.source = univ`，`L` 紧）、
`c₁`（`h` vs `k` 经 `G`，`alpha ≤ backgroundJetSmallness`）、`c`（`k` vs `g` 经 `F`）⇒ tower，常数同全局版。 -/
def partialTower_P6SF [CompactSpace L] {k : ℝ → SmoothRiemannianMetric I3 P}
    {g : ℝ → SmoothRiemannianMetric I3 M} {F : P → M} {V : Set P} {order' : ℕ} {eps : ℝ}
    (c : MetricComparisonOn k g F V {0} order' eps) (h : ℝ → SmoothRiemannianMetric I3 L)
    (G : PartialDiffeomorph I3 I3 L P ∞) (hsrc : G.source = univ) {order : ℕ} {alpha : ℝ}
    (c₁ : MetricComparisonOn h k G univ {0} order alpha) (hV : ∀ y, G y ∈ V)
    (horder : order ≤ order') (heps : 0 ≤ eps) (halpha : 0 < alpha)
    (halpha' : alpha ≤ backgroundJetSmallness ThreeSpace order) :
    TransportedErrorTower c h G univ {0} order
      (backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1)) := by
  have hKG : (univ : Set L) ⊆ G.source := hsrc ▸ subset_rfl
  choose B hB using fun (b : ℕ) (s : ℝ) =>
    exists_tensor0SField_eq_partialPullback_P6SF G isCompact_univ hKG (c.jet b s)
  exact
    { tower := B
      zero_eq := fun s y _ v => hB 0 s y (mem_univ y) v
      succ_eq := by
        intro b s hs y _ v
        have hfun : (fun a => B b a y v) =
            fun a => c.jet b a (G y) (fun q => mfderiv I3 I3 G y (v q)) :=
          funext fun a => hB b a y (mem_univ y) v
        rw [hB (b + 1) s y (mem_univ y) v, hfun]
        exact c.jet_succ b s hs (G y) (hV y) _
      differentiableWithinAt := fun _ _ _ _ _ _ _ => DifferentiableWithinAt.singleton
      close := by
        intro a b hab s hs y _
        have hale : a ≤ order := by omega
        have hbound := tensor02CovDerivNormWith_le_of_partial_pullback_comparison G
          ⟨univ, isOpen_univ⟩ hKG c₁ halpha halpha' hs (c.jet b s) (B b s)
          (fun z _ v => hB b s z (mem_univ z) v) hale (mem_univ y)
        refine hbound.trans ?_
        have hterm : ∀ j ∈ Finset.range (a + 1),
            tensor02CovDerivNormWith (I := I3) j (c.jet b s) (k s) (k s) (G y) ≤ eps := by
          intro j hj
          have hjle : j ≤ a := by have := Finset.mem_range.mp hj; omega
          exact c.close j b (by omega) s hs (G y) (hV y)
        have hsum : (∑ j ∈ Finset.range (a + 1),
            tensor02CovDerivNormWith (I := I3) j (c.jet b s) (k s) (k s) (G y)) ≤
              ((a : ℝ) + 1) * eps := by
          have h1 := Finset.sum_le_card_nsmul (Finset.range (a + 1)) _ eps hterm
          rw [Finset.card_range, nsmul_eq_mul] at h1
          calc _ ≤ ((a + 1 : ℕ) : ℝ) * eps := h1
            _ = ((a : ℝ) + 1) * eps := by push_cast; ring
        have hcast : ((a : ℝ) + 1) * eps ≤ ((order : ℝ) + 1) * eps := by
          have hle : (a : ℝ) ≤ (order : ℝ) := by exact_mod_cast hale
          nlinarith
        have hK := (backgroundJetConstant_pos ThreeSpace order).le
        calc _ ≤ backgroundJetConstant ThreeSpace order * (((a : ℝ) + 1) * eps) :=
              mul_le_mul_of_nonneg_left hsum hK
          _ ≤ backgroundJetConstant ThreeSpace order * (((order : ℝ) + 1) * eps) :=
              mul_le_mul_of_nonneg_left hcast hK
          _ = _ := by ring }

end PartialTower

section RoundTransport

variable {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]
  {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N]

omit [T2Space N] [SigmaCompactSpace N] in
/-- **round 数据沿 comparison 搬运（partial `R.map`）**：`R : SpatialRoundComponent g epsR x U`、`F` 于 `U` 的
scaled comparison（`order' ≥ order`，`eps`）⇒ `SpatialRoundComponent g' eps' (F x) (F '' U)`。 -/
theorem SpatialRoundComponent.transport_P6SF {g : SmoothRiemannianMetric I3 P}
    {g' : SmoothRiemannianMetric I3 N} {epsR : ℝ} {x : P} {U : Set P}
    (R : SpatialRoundComponent g epsR x U) (F : PartialDiffeomorph I3 I3 P N ∞)
    (hQ' : 0 < metricScalarAt g' (F x)) {order' : ℕ} {eps : ℝ}
    (cmp : MetricComparisonOn
      (fun _ => DifferentialGeometry.scaleMetric (metricScalarAt g x) R.Q_pos g)
      (fun _ => DifferentialGeometry.scaleMetric (metricScalarAt g' (F x)) hQ' g') F U {0}
      order' eps)
    (order : ℕ) (eps' : ℝ) (horderR : order ≤ ⌈epsR⁻¹⌉₊) (hepsR : 0 < epsR)
    (hepsR_small : epsR ≤ backgroundJetSmallness ThreeSpace order) (horder : order ≤ order')
    (heps : 0 ≤ eps)
    (hge : backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1) * eps ≤ eps' - epsR)
    (horder' : ⌈eps'⁻¹⌉₊ ≤ order) (heps'half : eps' ≤ 1 / 2) (hUF : U ⊆ F.source) :
    Nonempty (SpatialRoundComponent g' eps' (F x) ((F : P → N) '' U)) := by
  let _ : TopologicalSpace R.Z := R.topology
  let _ : ChartedSpace ThreeSpace R.Z := R.charted
  let _ : IsManifold I3 ∞ R.Z := R.smooth
  let _ : T2Space R.Z := R.t2
  let _ : CompactSpace R.Z := R.compact
  let _ : ConnectedSpace R.Z := R.connected
  have hmap_mem (y : R.Z) : R.map y ∈ R.map.target :=
    PartialEquiv.map_source R.map.toPartialEquiv (by rw [R.source_eq]; trivial)
  have hV (y : R.Z) : R.map y ∈ U := by
    have h := hmap_mem y
    rwa [R.target_eq] at h
  have hc₁ : MetricComparisonOn (fun _ => R.metric)
      (fun _ => DifferentialGeometry.scaleMetric (metricScalarAt g x) R.Q_pos g)
      (R.map : R.Z → P) univ {0} order epsR := R.comparison.mono (subset_refl _) horderR le_rfl
  have hG : ∀ y ∈ (univ : Set R.Z), MDifferentiableAt I3 I3 (R.map : R.Z → P) y :=
    fun y _ => R.map.mdifferentiableAt (by decide) (by rw [R.source_eq]; trivial)
  have hF : ∀ y ∈ (univ : Set R.Z), MDifferentiableAt I3 I3 (F : P → N) (R.map y) :=
    fun y _ => F.mdifferentiableAt (by decide) (hUF (hV y))
  have hcc := hc₁.trans cmp
    (partialTower_P6SF cmp (fun _ => R.metric) R.map R.source_eq hc₁ hV horder heps hepsR
      hepsR_small) (fun y _ => hV y) hG hF (fun _ _ _ _ _ _ _ => DifferentiableWithinAt.singleton)
  have hcc' := hcc.mono (subset_refl _) horder' (by linarith)
  have htgt : R.map.target ⊆ F.source := by
    rw [R.target_eq]
    exact hUF
  refine ⟨
    { Z := R.Z
      topology := R.topology
      charted := R.charted
      smooth := R.smooth
      t2 := R.t2
      compact := R.compact
      connected := R.connected
      metric := R.metric
      p := R.p
      scalar_one := R.scalar_one
      constant_curvature := R.constant_curvature
      map := PartialDiffeomorph.trans R.map F
      source_eq := ?_
      target_eq := ?_
      center_eq := ?_
      Q_pos := hQ'
      comparison := hcc'
      metric_bounds := ?_ }⟩
  · rw [partialDiffeomorph_trans_source, R.source_eq, univ_inter]
    exact Set.eq_univ_of_forall fun z => htgt (hmap_mem z)
  · rw [partialDiffeomorph_trans_target, Set.inter_eq_self_of_subset_right htgt, R.target_eq]
  · rw [partialDiffeomorph_trans_apply, R.center_eq]
  · intro z v
    rw [partialDiffeomorph_trans_apply]
    have hpb := hcc'.pullback_eq 0 z (Set.mem_univ z) (fun _ => v)
    have hcf := hcc'.equivalence 0 rfl z (Set.mem_univ z) v
    rw [hpb] at hcf
    rw [scaleMetric_inner] at hcf
    have hnn : 0 ≤ R.metric.inner z v v := inner_self_nonneg R.metric z v
    have h1 : (1 : ℝ) / 2 ≤ 1 - eps' := by linarith
    have h2 : 1 + eps' ≤ 2 := by linarith
    refine ⟨?_, ?_⟩
    · calc (1 / 2 : ℝ) * R.metric.inner z v v ≤ (1 - eps') * R.metric.inner z v v :=
          mul_le_mul_of_nonneg_right h1 hnn
        _ ≤ _ := hcf.1
    · calc _ ≤ (1 + eps') * R.metric.inner z v v := hcf.2
        _ ≤ 2 * R.metric.inner z v v := mul_le_mul_of_nonneg_right h2 hnn

/-- staticRescale 权重的数值界：`Rlow ≤ q`、`q' ≤ 2q`、`|q' − q| ≤ 243(δ + 3δC2q)`、`a ≤ order'` ⇒
`√(q⁻¹^(a+2))·q'·δ + |q'/q − 1|·√3 ≤ δ(2·max(1, Rlow⁻¹)^order' + 243(Rlow⁻¹ + 3C2)√3)`。 -/
theorem round_weight_real_P6SF {q q' δ C2 Rlow : ℝ} {a order' : ℕ} (hRlow : 0 < Rlow)
    (hRq : Rlow ≤ q) (hq'2 : q' ≤ 2 * q) (hδ0 : 0 ≤ δ)
    (hclose : |q' - q| ≤ 243 * (δ + δ * (3 * (C2 * q)))) (ha : a ≤ order') :
    Real.sqrt (q⁻¹ ^ (a + 2)) * q' * δ + |q' / q - 1| * Real.sqrt 3 ≤
      δ * (2 * (max 1 Rlow⁻¹) ^ order' + 243 * (Rlow⁻¹ + 3 * C2) * Real.sqrt 3) := by
  have hq : 0 < q := hRlow.trans_le hRq
  have hqi : q⁻¹ ≤ Rlow⁻¹ := inv_anti₀ hRlow hRq
  have hm1 : (1 : ℝ) ≤ max 1 Rlow⁻¹ := le_max_left _ _
  -- 第一项：`√(q⁻¹^(a+2))·q' ≤ 2·max(1,Rlow⁻¹)^order'`
  have hsq : Real.sqrt (q⁻¹ ^ (a + 2)) = q⁻¹ * Real.sqrt (q⁻¹ ^ a) := by
    rw [pow_add, mul_comm, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hpa : Real.sqrt (q⁻¹ ^ a) ≤ (max 1 Rlow⁻¹) ^ order' := by
    have h1 : q⁻¹ ^ a ≤ (max 1 Rlow⁻¹) ^ a :=
      pow_le_pow_left₀ (by positivity) (hqi.trans (le_max_right _ _)) a
    have h2 : (max 1 Rlow⁻¹) ^ a ≤ (max 1 Rlow⁻¹) ^ order' := pow_le_pow_right₀ hm1 ha
    have h3 : (1 : ℝ) ≤ (max 1 Rlow⁻¹) ^ order' := one_le_pow₀ hm1
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hT1 : Real.sqrt (q⁻¹ ^ (a + 2)) * q' ≤ 2 * (max 1 Rlow⁻¹) ^ order' := by
    rw [hsq]
    have h1 : q⁻¹ * Real.sqrt (q⁻¹ ^ a) * q' ≤ q⁻¹ * Real.sqrt (q⁻¹ ^ a) * (2 * q) :=
      mul_le_mul_of_nonneg_left hq'2 (by positivity)
    have h2 : q⁻¹ * Real.sqrt (q⁻¹ ^ a) * (2 * q) = 2 * Real.sqrt (q⁻¹ ^ a) := by
      field_simp
    linarith
  -- 第二项：`|q'/q − 1| ≤ 243δ(Rlow⁻¹ + 3C2)`
  have hT2 : |q' / q - 1| ≤ δ * (243 * (Rlow⁻¹ + 3 * C2)) := by
    rw [div_sub_one hq.ne', abs_div, abs_of_pos hq, div_le_iff₀ hq]
    have h1 : δ * (243 * (q⁻¹ + 3 * C2)) * q = 243 * (δ + δ * (3 * (C2 * q))) := by
      field_simp
    have h2 : δ * (243 * (q⁻¹ + 3 * C2)) ≤ δ * (243 * (Rlow⁻¹ + 3 * C2)) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ0
    nlinarith
  have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have e1 : Real.sqrt (q⁻¹ ^ (a + 2)) * q' * δ ≤ 2 * (max 1 Rlow⁻¹) ^ order' * δ :=
    mul_le_mul_of_nonneg_right hT1 hδ0
  have e2 : |q' / q - 1| * Real.sqrt 3 ≤ δ * (243 * (Rlow⁻¹ + 3 * C2)) * Real.sqrt 3 :=
    mul_le_mul_of_nonneg_right hT2 hs3
  nlinarith

/-- **OPEN-C round 型 transfer（抽象）**：`W` round 型（domain = `comp(x)`）、`Rlow ≤ Q`，`F` 于 `comp(x)` 上的
`C^order'` comparison（`2 ≤ order'`）、`δ` 显式条件 ⇒ `F x` 处 round 型 witness `(eps', C1', C2')`，
domain = `comp(F x)`。 -/
theorem exists_round_wholeComponent_transport_P6SF {C1 C2 Rlow δ : ℝ} (hC1 : 1 ≤ C1)
    (hC2 : 1 ≤ C2) (hRlow : 0 < Rlow) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 10)
    (hδθ : δ * (243 * (Rlow⁻¹ + 3 * C2)) ≤ 1 / (2 * C2)) (hδK : 40 * δ ≤ C2 * Rlow)
    {order' : ℕ} {epsc : ℝ}
    (hδc : δ * (2 * (max 1 Rlow⁻¹) ^ order' + 243 * (Rlow⁻¹ + 3 * C2) * Real.sqrt 3) ≤ epsc)
    (g : SmoothRiemannianMetric I3 P) (x : P) {eps : ℝ}
    (W : SpatialCanonicalWitness g eps C1 C2 x)
    (hround : ∃ wh R, W.alternative = .round wh R) (hRx : Rlow ≤ metricScalarAt g x)
    (g' : SmoothRiemannianMetric I3 N) (F : PartialDiffeomorph I3 I3 P N ∞)
    (horder2 : 2 ≤ order') (hsrc : connectedComponent x ⊆ F.source)
    (C : MetricComparisonOn (fun _ => g) (fun _ => g') F (connectedComponent x) {0} order' δ)
    (order : ℕ) {eps' C1' C2' : ℝ} (horderR : order ≤ ⌈eps⁻¹⌉₊) (heps0 : 0 < eps)
    (hsmall : eps ≤ backgroundJetSmallness ThreeSpace order) (horder : order ≤ order')
    (hge : backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1) * epsc ≤ eps' - eps)
    (horder' : ⌈eps'⁻¹⌉₊ ≤ order) (heps'half : eps' ≤ 1 / 2) (hC1' : 2 * C1 ≤ C1')
    (hC2' : 1000 * C2 ≤ C2')
    (hgrad : ∀ v : TangentSpace I3 (F x),
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g') (F x) v)| ≤
        C2' * metricScalarAt g' (F x) * Real.sqrt (metricScalarAt g' (F x)) *
          Real.sqrt (g'.inner (F x) v v)) :
    ∃ W' : SpatialCanonicalWitness g' eps' C1' C2' (F x), W'.capTubeHasNeckChart eps' ∧
      W'.domain.carrier = connectedComponent (F x) ∧
      ∃ wh R, W'.alternative = .round wh R := by
  have : LocallyConnectedSpace P := ChartedSpace.locallyConnectedSpace ThreeSpace P
  obtain ⟨whole, R, -⟩ := hround
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
  have hscal0 : ∀ y ∈ connectedComponent x,
      |metricScalarAt g' (F y) - metricScalarAt g y| ≤ 243 * (δ + δ * (3 * (C2 * Q))) :=
    fun y hy => C.abs_metricScalarAt_sub_le_of_rm_bound (U := U) hsrc hδ0 (by linarith) horder2
      hy (hrmW y hy)
  have hscal : ∀ y ∈ connectedComponent x,
      |metricScalarAt g' (F y) - metricScalarAt g y| ≤ 1 / (2 * C2) * Q := by
    intro y hy
    refine (hscal0 y hy).trans ?_
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
    have h3 : (1 + δ) * W.radius ≤ r' := le_max_left _ _
    linarith
  -- scalar / Rm
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
    have h := C.rmNormSq_image_le_of_mem_opens (U := U) hsrc hδ0 hδ1 hK horder2 hyc hB
    rw [metricRm04_apply]
    have h18 : Real.sqrt (normSq0S g' (F y) 4 (metricRm04At g' (F y))) ≤ 18 * (C2 * Q) := by
      calc Real.sqrt (normSq0S g' (F y) 4 (metricRm04At g' (F y)))
          ≤ Real.sqrt ((18 * (C2 * Q)) ^ 2) := Real.sqrt_le_sqrt (by linarith)
        _ = 18 * (C2 * Q) := Real.sqrt_sq (by positivity)
    have h3 : 36 * C2 * Q' ≤ C2' * Q' := mul_le_mul_of_nonneg_right (by linarith) hQ'.le
    have h4 : C2 * Q ≤ C2 * (2 * Q') := mul_le_mul_of_nonneg_left (by linarith) hC2p.le
    linarith
  -- alternative：round（scaled comparison = `staticRescale`，搬运 = partial tower）
  have hepsc : 0 ≤ epsc := le_trans (by positivity) hδc
  have hdim : Real.sqrt (Module.finrank ℝ ThreeSpace : ℝ) = Real.sqrt 3 := by
    rw [show Module.finrank ℝ ThreeSpace = 3 from finrank_euclideanSpace_fin]
    norm_num
  have cmp := (C.staticRescale (mem_singleton 0) Q Q' hQ hQ' hepsc (fun a ha => by
    rw [hdim]
    exact (round_weight_real_P6SF hRlow hRx hQ'4 hδ0 (hscal0 x hxc) ha).trans hδc)).mono
      (le_of_eq whole) le_rfl le_rfl
  obtain ⟨R'⟩ := R.transport_P6SF F hQ' cmp order eps' horderR heps0 hsmall horder hepsc hge
    horder' heps'half hdomF
  have heps'0 : 0 < eps' := by
    have : 0 ≤ backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1) * epsc :=
      mul_nonneg (mul_nonneg (backgroundJetConstant_pos ThreeSpace order).le (by positivity))
        hepsc
    linarith
  have hxint : F x ∈ interior (W.domain.map F hdomF).carrier := by
    rw [CompactDomain.map_carrier, ← partialDiffeomorph_image_interior_of_subset_source F hdomF]
    exact ⟨x, W.center_inside, rfl⟩
  let A' : SpatialCanonicalAlternative g' eps' C2' (F x) (W.domain.map F hdomF).carrier :=
    .round himg R'
  let W' : SpatialCanonicalWitness g' eps' C1' C2' (F x) :=
    { Q_pos := hQ'
      eps_pos := heps'0
      eps_lt_one := by linarith
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
      volume := fun h => False.elim h
      gradient := hgrad }
  refine ⟨W', ?_, himg, _, _, rfl⟩
  intro cap depth heq
  cases heq

end RoundTransport

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature
open Perelman.CanonicalNeighborhood.FiniteHorn

universe u

/-- round 型 transfer 的 `δ`：只依赖 `C2, Rlow, order', epsc` 的显式选择。 -/
theorem exists_roundDelta_P6SF {C2 Rlow epsc : ℝ} (order' : ℕ) (hC2 : 1 ≤ C2) (hRlow : 0 < Rlow)
    (hepsc : 0 < epsc) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 10 ∧ δ * (243 * (Rlow⁻¹ + 3 * C2)) ≤ 1 / (2 * C2) ∧
      40 * δ ≤ C2 * Rlow ∧
      δ * (2 * (max 1 Rlow⁻¹) ^ order' + 243 * (Rlow⁻¹ + 3 * C2) * Real.sqrt 3) ≤ epsc := by
  have hC2p : 0 < C2 := by linarith
  have hA : 0 < 243 * (Rlow⁻¹ + 3 * C2) := by positivity
  have hB : 0 < 2 * (max 1 Rlow⁻¹) ^ order' + 243 * (Rlow⁻¹ + 3 * C2) * Real.sqrt 3 := by
    have : 0 < (max 1 Rlow⁻¹) ^ order' := pow_pos (lt_max_of_lt_left one_pos) _
    positivity
  set A := 243 * (Rlow⁻¹ + 3 * C2) with hAdef
  set B := 2 * (max 1 Rlow⁻¹) ^ order' + 243 * (Rlow⁻¹ + 3 * C2) * Real.sqrt 3 with hBdef
  refine ⟨min (1 / 10) (min (1 / (2 * C2) / A) (min (C2 * Rlow / 40) (epsc / B))),
    lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity))),
    min_le_left _ _, ?_, ?_, ?_⟩
  · have h : min (1 / 10) (min (1 / (2 * C2) / A) (min (C2 * Rlow / 40) (epsc / B))) ≤
        1 / (2 * C2) / A := (min_le_right _ _).trans (min_le_left _ _)
    rwa [le_div_iff₀ hA] at h
  · have h : min (1 / 10) (min (1 / (2 * C2) / A) (min (C2 * Rlow / 40) (epsc / B))) ≤
        C2 * Rlow / 40 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
    linarith
  · have h : min (1 / 10) (min (1 / (2 * C2) / A) (min (C2 * Rlow / 40) (epsc / B))) ≤
        epsc / B := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
    rwa [le_div_iff₀ hB] at h

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

/-- 目标层梯度界（frequently 版）：frequently fine witness 的梯度界 + crossing 的梯度 / 度量收敛 ⇒
`q` 处 `C2out` 梯度界。 -/
theorem gradient_bound_of_frequently_P6SF (E : MetricCutCapEvent P Q a s) {p : P.Carrier}
    {q : Q.Carrier} (hcross : E.RegularCrossing p q) {v : ℕ → ℝ} (hv : ∀ n, v n ∈ Ioo a s)
    (hvt : Tendsto v atTop (𝓝 s)) (hQ : 0 < metricScalarAt E.outputMetric q) {C2 C2out : ℝ}
    (hC : C2 ≤ C2out)
    (hfine : ∃ᶠ n in atTop, ∀ u : TangentSpace I3 p,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt (E.incoming.flow.base.metric (v n))) p u)| ≤
        C2 * metricScalarAt (E.incoming.flow.base.metric (v n)) p *
          Real.sqrt (metricScalarAt (E.incoming.flow.base.metric (v n)) p) *
          Real.sqrt ((E.incoming.flow.base.metric (v n)).inner p u u)) :
    ∀ w : TangentSpace I3 q,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt E.outputMetric) q w)| ≤
        C2out * metricScalarAt E.outputMetric q * Real.sqrt (metricScalarAt E.outputMetric q) *
          Real.sqrt (E.outputMetric.inner q w w) := by
  intro w
  obtain ⟨u, hu1, hu2⟩ := E.gradient_tendsto_of_regularCrossing_P6ST3 hcross hv hvt w
  have hsc := E.scalar_tendsto_of_regularCrossing_P6ST3 hcross hv hvt
  have hR := ((tendsto_const_nhds (x := C2)).mul hsc).mul hsc.sqrt
  have hpair := (hu1.abs).prodMk_nhds (hR.mul hu2.sqrt)
  have hmem := (isClosed_le continuous_fst continuous_snd).mem_of_frequently_of_tendsto
    (hfine.mono fun n hn => hn u) hpair
  refine hmem.trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC hQ.le) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- **OPEN-C round 型 transfer（event 层，0 binder）**：`RegularCrossing p q` + `comp(p)` 与 cut tubes
不交 + `v n ↑ s` 上 **frequently** round 型 fine witness `(ηfine, C1, C2)` + `R⁺(q) > 0` ⇒ `q` 处
round 型 witness `(ηout, C1out, C2out)`，domain = `comp(q)`（`0 < ηfine < ηout ≤ 1/2`、
`ηfine ≤ backgroundJetSmallness ⌈ηout⁻¹⌉₊`、`2C1 ≤ C1out`、`1000C2 ≤ C2out`）。 -/
theorem wholeComponent_round_transfer_P6SF (E : MetricCutCapEvent P Q a s) {p : P.Carrier}
    {q : Q.Carrier} (hcross : E.RegularCrossing p q)
    (htube : ∀ i, Disjoint (connectedComponent p)
      (Set.range (E.transition.trace.tubes.tube i)))
    {v : ℕ → ℝ} (hv : ∀ n, v n ∈ Ioo a s) (hvt : Tendsto v atTop (𝓝 s))
    (hQ : 0 < metricScalarAt E.outputMetric q) {ηfine C1 C2 : ℝ} (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2)
    (hfine : ∃ᶠ n in atTop, ∃ W : SpatialCanonicalWitness (E.incoming.flow.base.metric (v n))
      ηfine C1 C2 p, ∃ wh R, W.alternative = .round wh R)
    {ηout C1out C2out : ℝ} (hη0 : 0 < ηfine) (hηlt : ηfine < ηout) (hηhalf : ηout ≤ 1 / 2)
    (hsmall : ηfine ≤ backgroundJetSmallness ThreeSpace ⌈ηout⁻¹⌉₊) (h1 : 2 * C1 ≤ C1out)
    (h2 : 1000 * C2 ≤ C2out) :
    ∃ W : SpatialCanonicalWitness E.outputMetric ηout C1out C2out q,
      W.capTubeHasNeckChart ηout ∧ W.domain.carrier = connectedComponent q ∧
      ∃ wh R, W.alternative = .round wh R := by
  obtain ⟨J, hJ, hsub, -, -, hcmp⟩ := E.wholeComponent_survivor_P6ST3 hcross
    (E.connectedComponent_subset_interior_old_P6ST4 hcross htube)
  set order := ⌈ηout⁻¹⌉₊ with horderdef
  set K := backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1) with hKdef
  have hK : 0 < K := mul_pos (backgroundJetConstant_pos ThreeSpace order) (by positivity)
  set epsc := (ηout - ηfine) / K with hepscdef
  have hepsc : 0 < epsc := div_pos (by linarith) hK
  have hge : K * epsc ≤ ηout - ηfine := by
    rw [hepscdef, mul_div_cancel₀ _ hK.ne']
  obtain ⟨δ, hδ, hδ1, hδθ, hδK, hδc⟩ :=
    exists_roundDelta_P6SF (max 2 order) hC2 (half_pos hQ) hepsc
  have hgrad := E.gradient_bound_of_frequently_P6SF hcross hv hvt hQ (by linarith : C2 ≤ C2out)
    (hfine.mono fun n ⟨W, _⟩ => W.gradient)
  have hcmpn := (tendsto_nhdsLT_of_slab_P6ST3 hv hvt).eventually (hcmp (max 2 order) δ hδ)
  have hsc := E.scalar_tendsto_of_regularCrossing_P6ST3 hcross hv hvt
  have hlow : ∀ᶠ n in atTop, metricScalarAt E.outputMetric q / 2 ≤
      metricScalarAt (E.incoming.flow.base.metric (v n)) p :=
    hsc.eventually (eventually_ge_nhds (half_lt_self hQ))
  obtain ⟨n, ⟨W, hround⟩, ⟨C⟩, hlo⟩ := (hfine.and_eventually (hcmpn.and hlow)).exists
  have horderR : order ≤ ⌈ηfine⁻¹⌉₊ := Nat.ceil_mono (inv_anti₀ hη0 hηlt.le)
  subst hJ
  exact exists_round_wholeComponent_transport_P6SF hC1 hC2 (half_pos hQ) hδ.le hδ1 hδθ hδK hδc
    _ p W hround hlo E.outputMetric J (le_max_left _ _) hsub C order horderR hη0 hsmall
    (le_max_right _ _) hge le_rfl hηhalf h1 h2 hgrad

/-- **OPEN-C 完整（whole-component = positive ∨ round）**：eventually whole-component 型 fine witness ⇒
`q` 处 `(ηout, C1out, C2out)` witness（chart，domain = `comp(q)`）。round 支 frequently 即可，否则 eventually
positive，用 STAB4 G3 positive transfer。 -/
theorem wholeComponent_transfer_P6SF (E : MetricCutCapEvent P Q a s) {p : P.Carrier}
    {q : Q.Carrier} (hcross : E.RegularCrossing p q)
    (htube : ∀ i, Disjoint (connectedComponent p)
      (Set.range (E.transition.trace.tubes.tube i)))
    {v : ℕ → ℝ} (hv : ∀ n, v n ∈ Ioo a s) (hvt : Tendsto v atTop (𝓝 s))
    (hQ : 0 < metricScalarAt E.outputMetric q) {ηfine C1 C2 : ℝ} (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2)
    (hfine : ∀ᶠ n in atTop, ∃ W : SpatialCanonicalWitness (E.incoming.flow.base.metric (v n))
      ηfine C1 C2 p, (∃ wh d sc, W.alternative = .positive wh d sc) ∨
        ∃ wh R, W.alternative = .round wh R)
    {ηout C1out C2out : ℝ} (hη0 : 0 < ηfine) (hηlt : ηfine < ηout) (hηhalf : ηout ≤ 1 / 2)
    (hsmall : ηfine ≤ backgroundJetSmallness ThreeSpace ⌈ηout⁻¹⌉₊) (h1 : 2 * C1 ≤ C1out)
    (h2 : 1000 * C2 ≤ C2out) :
    ∃ W : SpatialCanonicalWitness E.outputMetric ηout C1out C2out q,
      W.capTubeHasNeckChart ηout ∧ W.domain.carrier = connectedComponent q := by
  by_cases hR : ∃ᶠ n in atTop, ∃ W : SpatialCanonicalWitness (E.incoming.flow.base.metric (v n))
      ηfine C1 C2 p, ∃ wh R, W.alternative = .round wh R
  · obtain ⟨W, hW, hdom, -⟩ := E.wholeComponent_round_transfer_P6SF hcross htube hv hvt hQ hC1
      hC2 hR hη0 hηlt hηhalf hsmall h1 h2
    exact ⟨W, hW, hdom⟩
  · rw [not_frequently] at hR
    have hP : ∀ᶠ n in atTop, ∃ W : SpatialCanonicalWitness
        (E.incoming.flow.base.metric (v n)) ηfine C1 C2 p,
        ∃ wh d sc, W.alternative = .positive wh d sc := by
      filter_upwards [hfine, hR] with n hn hnR
      obtain ⟨W, hW⟩ := hn
      rcases hW with hpos | hrd
      · exact ⟨W, hpos⟩
      · exact absurd ⟨W, hrd⟩ hnR
    obtain ⟨W, hW, hdom, -⟩ := E.wholeComponent_positive_transfer_P6ST4 hcross htube hv hvt hQ
      hC1 hC2 hP (hη0.trans hηlt) (by linarith) h1 h2
    exact ⟨W, hW, hdom⟩

/-- **OPEN-C 逆否（htrans whole-component 支的形）**：目标层 `q` 无 `(ηout, C1out, C2out)` witness ⇒
frequently `(v n, p)` 无 whole-component（positive ∨ round）型 `(ηfine, C1, C2)` fine witness。 -/
theorem frequently_not_wholeComponent_P6SF (E : MetricCutCapEvent P Q a s) {p : P.Carrier}
    {q : Q.Carrier} (hcross : E.RegularCrossing p q)
    (htube : ∀ i, Disjoint (connectedComponent p)
      (Set.range (E.transition.trace.tubes.tube i)))
    {v : ℕ → ℝ} (hv : ∀ n, v n ∈ Ioo a s) (hvt : Tendsto v atTop (𝓝 s))
    (hQ : 0 < metricScalarAt E.outputMetric q) {ηfine C1 C2 : ℝ} (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2)
    {ηout C1out C2out : ℝ} (hη0 : 0 < ηfine) (hηlt : ηfine < ηout) (hηhalf : ηout ≤ 1 / 2)
    (hsmall : ηfine ≤ backgroundJetSmallness ThreeSpace ⌈ηout⁻¹⌉₊) (h1 : 2 * C1 ≤ C1out)
    (h2 : 1000 * C2 ≤ C2out)
    (hnot : ¬ ∃ W : SpatialCanonicalWitness E.outputMetric ηout C1out C2out q,
      W.capTubeHasNeckChart ηout) :
    ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness (E.incoming.flow.base.metric (v n))
      ηfine C1 C2 p, (∃ wh d sc, W.alternative = .positive wh d sc) ∨
        ∃ wh R, W.alternative = .round wh R := by
  intro hev
  obtain ⟨W, hW, -⟩ := E.wholeComponent_transfer_P6SF hcross htube hv hvt hQ hC1 hC2
    (hev.mono fun _ hn => not_not.mp hn) hη0 hηlt hηhalf hsmall h1 h2
  exact hnot ⟨W, hW⟩

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

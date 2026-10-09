import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BufferedTransferP6ST2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonSectionalCurvature

/-!
# S-c OPEN-C (C1) + (C4)：`SecLower` 的 `C²` 扰动与 component 存活（O-CH11-STAB4 G2，后缀 `_P6ST4`）

* **(C1)** `secLower_image_of_comparison_P6ST4`：树内 `MetricComparisonOn.secLower_image`
  （ComparisonSectionalCurvature.lean:42，`SecLower c ⇒ SecLower (c − 4δ(c + 360 + K))`，`K` = Rm 界）的
  canonical 归一化版：源 `SecLower g (C2⁻¹Q) U` + `|Rm| ≤ C2·Q` 于 `U` + `Rlow ≤ Q` +
  `δ ≤ δsec(C2, Rlow) := C2⁻¹ / (8(C2⁻¹ + 360/Rlow + C2))` + `Q' ≤ 2Q` + `1000·C2 ≤ C2'` ⇒
  `SecLower g' (C2'⁻¹Q') (F '' U)`。`δsec` 只依赖 `C2, Rlow`（在选 `n` 之前）。
  （STAB3 G4 记 (C1) 为 "树内只有等距版"；实际树内已有 `C²` 扰动版，本文件只做归一化接线。）
* **(C4)** `connectedComponent_subset_interior_old_P6ST4`：`RegularCrossing p q` + `comp(p)` 与每条
  cut tube 的像不交 ⇒ `connectedComponent p ⊆ interior (val '' old)`（`comp(p) ⊆ core`；
  retained 是 core 中 clopen 集，`comp(p)` 在 core 中 preconnected 且含 `p`（`p` 来自
  `old ⊆ retained`）；再用 `old_contains_outside`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]
  {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N]

/-- `δsec(C2, Rlow) := C2⁻¹ / (8(C2⁻¹ + 360/Rlow + C2))`，正。 -/
theorem secDelta_pos_P6ST4 {C2 Rlow : ℝ} (hC2 : 1 ≤ C2) (hRlow : 0 < Rlow) :
    0 < C2⁻¹ / (8 * (C2⁻¹ + 360 / Rlow + C2)) := by
  have : 0 < C2 := by linarith
  positivity

/-- 数值部分：`c' := C2⁻¹Q − 4δ(C2⁻¹Q + 360 + C2·Q) ≥ C2'⁻¹Q'`。 -/
theorem secLower_constant_real_P6ST4 {C2 C2' Rlow Q Q' δ : ℝ} (hC2 : 1 ≤ C2)
    (hC2' : 1000 * C2 ≤ C2') (hRlow : 0 < Rlow) (hQ : Rlow ≤ Q) (hQ' : Q' ≤ 2 * Q)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ C2⁻¹ / (8 * (C2⁻¹ + 360 / Rlow + C2))) :
    C2'⁻¹ * Q' ≤ C2⁻¹ * Q - 4 * δ * (C2⁻¹ * Q + 360 + C2 * Q) := by
  have hC2p : 0 < C2 := by linarith
  have hQp : 0 < Q := by linarith
  have hA : 0 < C2⁻¹ + 360 / Rlow + C2 := by positivity
  have h360 : 360 ≤ 360 / Rlow * Q := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hRlow]
    nlinarith
  have hsum : C2⁻¹ * Q + 360 + C2 * Q ≤ (C2⁻¹ + 360 / Rlow + C2) * Q := by nlinarith
  have hδA : 4 * δ * (C2⁻¹ + 360 / Rlow + C2) ≤ C2⁻¹ / 2 := by
    have h1 : δ * (8 * (C2⁻¹ + 360 / Rlow + C2)) ≤ C2⁻¹ := by
      rwa [le_div_iff₀ (by positivity)] at hδ
    nlinarith
  have hloss : 4 * δ * (C2⁻¹ * Q + 360 + C2 * Q) ≤ C2⁻¹ * Q / 2 := by
    have h2 : 4 * δ * (C2⁻¹ * Q + 360 + C2 * Q) ≤ 4 * δ * ((C2⁻¹ + 360 / Rlow + C2) * Q) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have h3 : 4 * δ * ((C2⁻¹ + 360 / Rlow + C2) * Q) ≤ C2⁻¹ / 2 * Q := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hδA hQp.le
    linarith
  have hinv : C2'⁻¹ ≤ C2⁻¹ / 1000 := by
    rw [div_eq_mul_inv, ← mul_inv]
    exact inv_anti₀ (by positivity) (by linarith)
  have hQ'0 : 0 ≤ Q' ∨ Q' < 0 := le_or_gt 0 Q'
  have hC2'0 : 0 < C2' := by linarith
  have hlhs : C2'⁻¹ * Q' ≤ C2⁻¹ / 1000 * (2 * Q) := by
    rcases hQ'0 with h0 | h0
    · exact mul_le_mul hinv hQ' h0 (by positivity)
    · have : C2'⁻¹ * Q' < 0 := mul_neg_of_pos_of_neg (inv_pos.mpr hC2'0) h0
      have : 0 ≤ C2⁻¹ / 1000 * (2 * Q) := by positivity
      linarith
  have hC2inv : 0 < C2⁻¹ := inv_pos.mpr hC2p
  nlinarith

omit [SigmaCompactSpace N] in
/-- **(C1) `SecLower` 的 `C²` 扰动（canonical 归一化）**：`MetricComparisonOn g g' F A {0} order δ`
（`2 ≤ order`），开集 `U ⊆ A ∩ F.source`，`SecLower g (C2⁻¹Q) U`、`|Rm_g| ≤ C2·Q` 于 `U`，`Rlow ≤ Q`，
`δ ≤ min (1/2) δsec`，`Q' ≤ 2Q`，`1000·C2 ≤ C2'` ⇒ `SecLower g' (C2'⁻¹Q') (F '' U)`。 -/
theorem secLower_image_of_comparison_P6ST4 {g : SmoothRiemannianMetric I3 P}
    {g' : SmoothRiemannianMetric I3 N} {F : PartialDiffeomorph I3 I3 P N ∞} {A : Set P}
    {order : ℕ} {δ C2 C2' Rlow Q Q' : ℝ}
    (C : MetricComparisonOn (fun _ => g) (fun _ => g') F A {0} order δ)
    (U : Opens P) (hU : (U : Set P) ⊆ F.source) (hUA : (U : Set P) ⊆ A) (horder : 2 ≤ order)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hδ : δ ≤ C2⁻¹ / (8 * (C2⁻¹ + 360 / Rlow + C2)))
    (hC2 : 1 ≤ C2) (hC2' : 1000 * C2 ≤ C2') (hRlow : 0 < Rlow) (hQ : Rlow ≤ Q)
    (hQ' : Q' ≤ 2 * Q) (hsec : SecLower g (C2⁻¹ * Q) U)
    (hrm : ∀ y ∈ (U : Set P), Real.sqrt (normSq0S (I := I3) g y 4 (metricRm04 g y)) ≤ C2 * Q) :
    SecLower g' (C2'⁻¹ * Q') (F '' (U : Set P)) := by
  have hQp : 0 < Q := hRlow.trans_le hQ
  have hK : 0 ≤ C2 * Q := by positivity
  have hrm' : ∀ y ∈ (U : Set P), normSq0S g y 4 (metricRm04At g y) ≤ (C2 * Q) ^ 2 := by
    intro y hy
    have h := hrm y hy
    rw [metricRm04_apply] at h
    have h0 := normSq0S_nonneg g y 4 (metricRm04At g y)
    have h1 := Real.sq_sqrt h0
    nlinarith [Real.sqrt_nonneg (normSq0S g y 4 (metricRm04At g y))]
  have hs := C.secLower_image U hU hUA (s := 0) rfl hδ1 horder (by positivity) hK hsec hrm'
  exact hs.mono (secLower_constant_real_P6ST4 hC2 hC2' hRlow hQ hQ' hδ0 hδ)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

/-- **(C4) component 存活**：`RegularCrossing p q` + `comp(p)` 与每条 cut tube 的像不交 ⇒
`connectedComponent p ⊆ interior (val '' old)`。 -/
theorem connectedComponent_subset_interior_old_P6ST4 (E : MetricCutCapEvent P Q a s)
    {p : P.Carrier} {q : Q.Carrier} (hcross : E.RegularCrossing p q)
    (htube : ∀ i, Disjoint (connectedComponent p)
      (Set.range (E.transition.trace.tubes.tube i))) :
    connectedComponent p ⊆ interior (Subtype.val '' E.old) := by
  have : LocallyConnectedSpace P.Carrier := ChartedSpace.locallyConnectedSpace ThreeSpace P.Carrier
  set T := E.transition.trace.tubes with hT
  have hcore : connectedComponent p ⊆ T.core := by
    intro y hy hband
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hband
    obtain ⟨z, -, hz⟩ := hi
    exact Set.disjoint_left.mp (htube i) hy ⟨z, hz⟩
  let S : Set T.core := Subtype.val ⁻¹' connectedComponent p
  have hS : IsPreconnected S := by
    have himg : (Subtype.val : T.core → P.Carrier) '' S = connectedComponent p := by
      change Subtype.val '' (Subtype.val ⁻¹' connectedComponent p) = _
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hcore]
    exact _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      (himg ▸ isPreconnected_connectedComponent)
  obtain ⟨x, -, hxp, -⟩ := hcross
  have hpS : x.1 ∈ S := by
    change x.1.1 ∈ connectedComponent p
    rw [hxp]
    exact mem_connectedComponent
  have hret : S ⊆ E.transition.trace.retainedCore :=
    hS.subset_isClopen E.transition.trace.isClopen_retainedCore ⟨x.1, hpS, E.old_retained x.2⟩
  have hsub : connectedComponent p ⊆ Subtype.val '' E.old := by
    intro y hy
    refine ⟨⟨y, hcore hy⟩, E.old_contains_outside _ (hret hy) fun i hi => ?_, rfl⟩
    obtain ⟨z, -, hz⟩ := hi
    exact Set.disjoint_left.mp (htube i) hy ⟨z, hz⟩
  exact interior_maximal hsub isOpen_connectedComponent

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

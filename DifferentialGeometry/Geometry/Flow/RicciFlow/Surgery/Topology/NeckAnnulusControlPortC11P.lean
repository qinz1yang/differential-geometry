import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckBoundaryChord
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapAnnulusCoordinates
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz
import DifferentialGeometry.Topology.Manifold.OpenFunctionExtension
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# S-CH11-FIX5 port of astra `NeckAnnulusControl`（`PortC11P`）

来源：donor `NeckAnnulusControl.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树有 16 个 elaboration error（`CapAnnulusCoordinates` 落地后才暴露），源头在
下面几处，其余是级联；本 port 只做 elaboration 层面修补
（no statement / definition / proof idea altered）：
* `capSeamOpen_subset_annulus` 与 `capRadialCoordinates_mem_closedTest`：`abs_lt.mp hx` /
  `abs_lt.mp x.property` 的参数先 `show |‖·‖ - standardCapL| < 2 * capSeamWidth from …`
  （`x ∈ ↑capSeamOpen` 不会被自动展开成绝对值不等式）。
* `private theorem capRadialCoordinates_mem_closedTest` 前加 `include N in`：证明体里用
  `N.delta_pos` / `N.delta_lt_one`，而 theorem 的 `variable (N)` 只在陈述里出现才被带入；
  不 include 时 `N` 不在作用域，`N.annulusLift` 等后续 field notation 全部级联失败。
* `omit [T2Space M] [SigmaCompactSpace M] in` 加在上面的 `include N in` 之前（否则 `include N`
  把这两个实例连带拉进 `annulusLift`，使 `annulusLift_smooth` 上 donor 自己的 `omit` 报
  "cannot omit referenced section variable"）。
* `annulusPoint_boundary` / `annulusPoint_retained`：`simpa only [sub_self] using …` /
  `simpa only [add_sub_cancel_left] using …` 改为 `have h := …; simp only […] at h; exact h`
  （目标是 `↑(N.annulusLift ⟨_, hx⟩) = _`，与 `capRadialCoordinates _ = _` 只差 `annulusLift`
  的 delta，`simpa` 收尾只做 reducible 匹配，`exact` 用默认透明度）。
* `annulusPoint_mfderiv`：局部 `hrestrict` 的左端 `N.annulusPoint ∘ Subtype.val` 改为
  `fun y : capSeamOpen => N.annulusPoint y.val`（`mfderiv_restrict_open` 的 pattern 是 lambda
  形，`Function.comp` 形 `rw` 找不到）。
* `annulusPoint_speed_le` 的 `hconstant`：`dsimp only [annulusDerivativeConstant]` 改为
  `change N.scale * ((√2 * c / √N.scale) * ‖v‖) ^ 2 = 2 * (c * ‖v‖) ^ 2`
  （`dsimp` 留下 `↑⟨…, _⟩`，后面 `rw [div_pow]` 匹配不到）。

原路径 `NeckAnnulusControl` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- This constant is chosen once from the fixed round-cylinder model. -/
def capRadialDerivativeConstant : ℝ≥0 := Classical.choose exists_capRadialCoordinates_bound

theorem capRadialDerivativeConstant_bound (x : ThreeSpace) (hx : x ∈ capSeamAnnulus)
    (v : ThreeSpace) :
    Real.sqrt (roundCylinderMetric.inner (capRadialCoordinates x)
      (mfderiv ThreeModel NeckCylinderModel capRadialCoordinates x v)
      (mfderiv ThreeModel NeckCylinderModel capRadialCoordinates x v)) ≤
        capRadialDerivativeConstant * ‖v‖ :=
  (Classical.choose_spec exists_capRadialCoordinates_bound).2 x hx v

def capSeamOpen : TopologicalSpace.Opens ThreeSpace :=
  ⟨{x | |‖x‖ - standardCapL| < 2 * capSeamWidth},
    isOpen_lt ((continuous_norm.sub continuous_const).abs) continuous_const⟩

theorem capSeamOpen_subset_annulus : (capSeamOpen : Set ThreeSpace) ⊆ capSeamAnnulus := by
  intro x hx
  obtain ⟨hlo, hhi⟩ := abs_lt.mp
    (show |‖x‖ - standardCapL| < 2 * capSeamWidth from hx)
  constructor <;> linarith

theorem capSeamBall_subset {x₀ : ThreeSpace} (hx₀ : ‖x₀‖ = standardCapL) :
    Metric.ball x₀ capSeamWidth ⊆ (capSeamOpen : Set ThreeSpace) := by
  intro x hx
  change |‖x‖ - standardCapL| < 2 * capSeamWidth
  rw [← hx₀]
  have h := (abs_norm_sub_norm_le x x₀).trans_lt
    (by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hx))
  linarith [capSeamWidth_pos]

namespace NormalizedNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}
  (N : NormalizedNeck g δ k)

omit [T2Space M] [SigmaCompactSpace M] in
include N in
private theorem capRadialCoordinates_mem_closedTest (x : capSeamOpen) :
    -δ⁻¹ ≤ (capRadialCoordinates x.val).2 ∧
      (capRadialCoordinates x.val).2 ≤ δ⁻¹ := by
  have hinv : 1 < δ⁻¹ := (one_lt_inv₀ N.delta_pos).mpr N.delta_lt_one
  have hx := abs_lt.mp
    (show |‖x.val‖ - standardCapL| < 2 * capSeamWidth from x.property)
  have ha := capSeamWidth_le_one
  change -δ⁻¹ ≤ ‖x.val‖ - standardCapL ∧ ‖x.val‖ - standardCapL ≤ δ⁻¹
  constructor <;> linarith

def annulusLift (x : capSeamOpen) : neckBuffer δ :=
  ⟨capRadialCoordinates x.val, by
    have h := N.capRadialCoordinates_mem_closedTest x
    constructor <;> linarith [h.1, h.2]⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem annulusLift_smooth : ContMDiff ThreeModel NeckCylinderModel ∞ N.annulusLift := by
  apply (ContMDiff.subtypeVal_comp_iff (neckBuffer δ) N.annulusLift).mp
  intro x
  have hx := capSeamAnnulus_ne_zero (capSeamOpen_subset_annulus x.property)
  exact ((capRadialCoordinates_smooth x.val hx).contMDiffAt
    (isOpen_compl_singleton.mem_nhds hx)).comp x contMDiff_subtype_val.contMDiffAt

/-- The original terminal neck chart, extended only to make a total source function. -/
def annulusPoint : ThreeSpace → M :=
  Function.extend (Subtype.val : capSeamOpen → ThreeSpace)
    (N.chart ∘ N.annulusLift) (fun _ => N.center)

theorem annulusPoint_apply (x : capSeamOpen) :
    N.annulusPoint x.val = N.chart (N.annulusLift x) :=
  Subtype.val_injective.extend_apply _ _ x

theorem annulusPoint_boundary (y : Sphere 2) :
    N.annulusPoint (standardCapL • (y : ThreeSpace)) = N.boundaryPoint y := by
  have hL : 0 < standardCapL := by
    rw [standardCapL_eq_transitionEnd]
    exact StandardCap.transitionEnd_pos
  have hx : standardCapL • (y : ThreeSpace) ∈ capSeamOpen := by
    change |‖standardCapL • (y : ThreeSpace)‖ - standardCapL| < 2 * capSeamWidth
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL, norm_eq_of_mem_sphere y,
      mul_one, sub_self, abs_zero]
    exact mul_pos (by norm_num) capSeamWidth_pos
  rw [N.annulusPoint_apply ⟨_, hx⟩]
  apply congrArg N.chart
  apply Subtype.ext
  have h := capRadialCoordinates_pos_smul y hL
  simp only [sub_self] at h
  exact h

theorem annulusPoint_retained (x : neckRetainedCollar δ)
    (hx : (standardCapL + x.val.2) • (x.val.1 : ThreeSpace) ∈ capSeamOpen)
    (hbuffer : x.val ∈ neckBuffer δ) :
    N.annulusPoint ((standardCapL + x.val.2) • (x.val.1 : ThreeSpace)) =
      N.chart ⟨x.val, hbuffer⟩ := by
  have hL : 0 < standardCapL := by
    rw [standardCapL_eq_transitionEnd]
    exact StandardCap.transitionEnd_pos
  rw [N.annulusPoint_apply ⟨_, hx⟩]
  apply congrArg N.chart
  apply Subtype.ext
  have h := capRadialCoordinates_pos_smul x.val.1
    (add_pos_of_pos_of_nonneg hL x.property.1)
  simp only [add_sub_cancel_left] at h
  exact h

omit [T2Space M] [SigmaCompactSpace M] in
theorem annulusPoint_smooth :
    ContMDiffOn ThreeModel ThreeModel ∞ N.annulusPoint capSeamOpen := by
  have h := contMDiffOn_extend_from_open capSeamOpen (N.chart ∘ N.annulusLift)
    (fun _ => N.center) isOpen_univ
    (N.chart_smooth.contMDiff.comp N.annulusLift_smooth).contMDiffOn
  apply h.mono
  intro x hx
  exact ⟨⟨x, hx⟩, mem_univ _, rfl⟩

private theorem annulusLift_mfderiv (x : capSeamOpen) (v : ThreeSpace) :
    (mfderiv ThreeModel NeckCylinderModel N.annulusLift x v :
      EuclideanSpace ℝ (Fin 2) × ℝ) =
        mfderiv ThreeModel NeckCylinderModel capRadialCoordinates x.val v := by
  have hsub := mfderiv_comp_apply x
    ((contMDiff_subtype_val (I := NeckCylinderModel) (U := neckBuffer δ)
      (n := ∞)).mdifferentiableAt (x := N.annulusLift x) (by decide))
    (N.annulusLift_smooth.mdifferentiableAt (x := x) (by decide)) v
  rw [mfderiv_subtype_val_apply] at hsub
  have hrestrict := congrArg (fun D : ThreeSpace →L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ) => D v)
    (mfderiv_restrict_open (I := ThreeModel) (J := NeckCylinderModel)
      capRadialCoordinates capSeamOpen x)
  have heq := hsub.symm.trans hrestrict
  simpa only using! heq

private theorem annulusPoint_mfderiv (x : capSeamOpen) (v : ThreeSpace) :
    mfderiv ThreeModel ThreeModel N.annulusPoint x.val v =
      mfderiv NeckCylinderModel ThreeModel N.chart (N.annulusLift x)
        (mfderiv ThreeModel NeckCylinderModel N.annulusLift x v) := by
  have hrestrict : (fun y : capSeamOpen => N.annulusPoint y.val) =
      N.chart ∘ N.annulusLift := funext N.annulusPoint_apply
  have h := mfderiv_comp_apply x
    (N.chart_smooth.contMDiff.mdifferentiableAt (x := N.annulusLift x) (by decide))
    (N.annulusLift_smooth.mdifferentiableAt (x := x) (by decide)) v
  rw [← hrestrict, mfderiv_restrict_open] at h
  simpa only using! h

def annulusDerivativeConstant : ℝ≥0 :=
  ⟨Real.sqrt 2 * capRadialDerivativeConstant / Real.sqrt N.scale,
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) capRadialDerivativeConstant.coe_nonneg)
      (Real.sqrt_nonneg _)⟩

/-- Uniform transfer from the fixed model to this actual normalized terminal neck. -/
theorem annulusPoint_speed_le (x : capSeamOpen) (v : ThreeSpace) :
    Real.sqrt (g.inner (N.annulusPoint x.val)
      (mfderiv ThreeModel ThreeModel N.annulusPoint x.val v)
      (mfderiv ThreeModel ThreeModel N.annulusPoint x.val v)) ≤
        N.annulusDerivativeConstant * ‖v‖ := by
  let V := mfderiv ThreeModel NeckCylinderModel N.annulusLift x v
  have hcore : N.annulusLift x ∈ neckClosedTest δ :=
    N.capRadialCoordinates_mem_closedTest x
  have herr := metricDerivNorm_lt_of_sup_lt (isCompact_neckClosedTest δ)
    (Nat.zero_le k) N.normalizedMetric
    (roundCylinderMetric.restrictOpen (neckBuffer δ))
    (roundCylinderMetric.restrictOpen (neckBuffer δ)) N.closeness hcore
  have hb := (Geometry.Metric.inner_bounds_of_metricDerivNorm_le
    (roundCylinderMetric.restrictOpen (neckBuffer δ)) N.normalizedMetric
    (N.annulusLift x) herr.le V).2
  have href : (roundCylinderMetric.restrictOpen (neckBuffer δ)).inner
      (N.annulusLift x) V V = roundCylinderMetric.inner (capRadialCoordinates x.val)
        (mfderiv ThreeModel NeckCylinderModel capRadialCoordinates x.val v)
        (mfderiv ThreeModel NeckCylinderModel capRadialCoordinates x.val v) := by
    dsimp only [V]
    change roundCylinderMetric.inner (capRadialCoordinates x.val)
      (mfderiv ThreeModel NeckCylinderModel N.annulusLift x v)
      (mfderiv ThreeModel NeckCylinderModel N.annulusLift x v) = _
    erw [N.annulusLift_mfderiv x v]
  rw [href, N.normalized_inner] at hb
  dsimp only [V] at hb
  erw [← N.annulusPoint_mfderiv x v, ← N.annulusPoint_apply x] at hb
  have hρ := capRadialDerivativeConstant_bound x.val
    (capSeamOpen_subset_annulus x.property) v
  have hρnn := metric_inner_self_nonneg roundCylinderMetric (capRadialCoordinates x.val)
    (mfderiv ThreeModel NeckCylinderModel capRadialCoordinates x.val v)
  have hρsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg
    capRadialDerivativeConstant.coe_nonneg (norm_nonneg v))).mpr hρ
  rw [Real.sq_sqrt hρnn] at hρsq
  have hconstant : N.scale * (N.annulusDerivativeConstant * ‖v‖) ^ 2 =
      2 * (capRadialDerivativeConstant * ‖v‖) ^ 2 := by
    change N.scale * ((Real.sqrt 2 * (capRadialDerivativeConstant : ℝ) /
      Real.sqrt N.scale) * ‖v‖) ^ 2 = 2 * ((capRadialDerivativeConstant : ℝ) * ‖v‖) ^ 2
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt N.scale_pos.le]
    field_simp [N.scale_pos.ne'] <;> ring
  have hupper : g.inner (N.annulusPoint x.val)
      (mfderiv ThreeModel ThreeModel N.annulusPoint x.val v)
      (mfderiv ThreeModel ThreeModel N.annulusPoint x.val v) ≤
        (N.annulusDerivativeConstant * ‖v‖) ^ 2 := by
    apply (mul_le_mul_iff_right₀ N.scale_pos).mp
    rw [hconstant]
    nlinarith [mul_nonneg (sub_nonneg.mpr N.delta_lt_one.le) hρnn]
  exact (Real.sqrt_le_sqrt hupper).trans_eq
    (Real.sqrt_sq (mul_nonneg N.annulusDerivativeConstant.coe_nonneg (norm_nonneg v)))

theorem annulusPoint_edist_le {x₀ : ThreeSpace} (hx₀ : ‖x₀‖ = standardCapL)
    {x y : ThreeSpace} (hx : x ∈ Metric.ball x₀ capSeamWidth)
    (hy : y ∈ Metric.ball x₀ capSeamWidth) :
    riemannianEDistOf g (N.annulusPoint x) (N.annulusPoint y) ≤
      (N.annulusDerivativeConstant : ℝ≥0∞) * edist x y := by
  apply riemannian_edist_le_on_convex_source g capSeamOpen.isOpen
    (N.annulusPoint_smooth.of_le (by decide)) (capSeamBall_subset hx₀)
    (convex_ball x₀ capSeamWidth) _ hx hy
  intro p hp v
  exact N.annulusPoint_speed_le ⟨p, capSeamBall_subset hx₀ hp⟩ v

end NormalizedNeck
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

import DifferentialGeometry.Geometry.Neck.SpatialNormalization
import DifferentialGeometry.Geometry.Curvature.RiemannPerturbation
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Restriction
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA3Algebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelWitnesses

/-!
# CX-CAPCORE G1：neck 上的 Rm 上界（后缀 `_CXCC`）

core-collar 延伸把 witness domain 沿 neck 轴向外延；新 domain 点的 `rm_bound` 需要一个**显式**的
neck 曲率上界：`ε`-neck `nk`（中心 `x`、`Q = R(x)`）的 window 内每点
`√|Rm_g|² ≤ 1200 · Q`（`SpatialNeck.sqrt_rmNormSq_map_le_CXCC`）。
证明 = neckBuffer pullback 的 `C²` 接近（`exists_neckBuffer_pullback_bound`）+ 树内 Riemann 扰动
`sqrt_normSq_metricRm04At_le_of_metricDerivNorm_le` + round cylinder 的 `|Rm|² = 1`
（product 化为 `S²(√2)`，二维 `|Rm|² = R²`）+ scale / pullback / open restriction 的不变性。
-/

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section Restrict

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- open restriction 不改 `|Rm|²`（不需 inner product model；`rmNormSq_restrictOpen` 的一般版）。 -/
theorem rmNormSq_restrictOpen_CXCC (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) [T2Space U] [IsManifold I 1 U] (y : U) :
    normSq0S (I := I) (M := U) (g.restrictOpen (I := I) U) y 4
        (metricRm04At (I := I) (M := U) (g.restrictOpen (I := I) U) y) =
      normSq0S (I := I) (M := M) g (y : M) 4 (metricRm04At (I := I) (M := M) g (y : M)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hRm : metricRm04At (I := I) (M := U) (g.restrictOpen (I := I) U) y =
      metricRm04At (I := I) (M := M) g (y : M) := by
    ext w
    have hw : w = vec4 (I := I) (w 0) (w 1) (w 2) (w 3) := by
      funext i
      fin_cases i <;> rfl
    rw [hw]
    have h := metricRm04StandardAt_restrictOpen (I := I) g U y (w 0) (w 1) (w 2) (w 3)
    simp only [mfderiv_subtype_val_apply] at h
    exact h
  rw [normSq0S_restrictOpen_apply (I := I) g U 4 y
    (metricRm04At (I := I) (M := U) (g.restrictOpen (I := I) U) y), hRm]

/-- scale：`|Rm_{c g}|² = c⁻² |Rm_g|²`。 -/
theorem rmNormSq_scaleMetric_CXCC (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x : M) :
    normSq0S (I := I) (scaleMetric (I := I) c hc g) x 4
        (metricRm04At (I := I) (scaleMetric (I := I) c hc g) x) =
      (c⁻¹) ^ 2 * normSq0S (I := I) g x 4 (metricRm04At (I := I) g x) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  rw [← metricRm04_apply, ← metricRm04_apply, metricRm_scale, normSq0S_smul, normSq0S_scale]
  field_simp

end Restrict

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

/-- round cylinder `S²(√2) × ℝ`：`|Rm|² = 1`。 -/
theorem rmNormSq_roundCylinder_CXCC (y : NeckCylinder) :
    normSq0S roundCylinderMetric y 4 (metricRm04At roundCylinderMetric y) = 1 := by
  have hprod : (roundCylinderMetric : SmoothRiemannianMetric NeckCylinderModel NeckCylinder) =
      (scaleMetric 2 (by norm_num) (Geometry.roundMetric (E := ThreeSpace) (n := 2))).prod
        (euclideanMetric (E := ℝ)) := by
    rw [roundCylinderMetric_eq_geometry]
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [Geometry.Metric.roundCylinderMetric_inner, SmoothRiemannianMetric.prod_inner]
    erw [scaleMetric_inner, Geometry.roundMetric_inner]
    congr 1
    exact mul_comm _ _
  rw [hprod, normSq0S_metricRm04At_productReal,
    GC.Geometry.normSq0S_metricRm04At_eq_sq_of_finrank_two (by simp), metricScalarAt_scaleMetric,
    metricScalarAt_roundMetric_eq (by norm_num)]
  norm_num

/-- **neck 上的显式 Rm 上界**：`ε`-neck `nk`（中心 `x`）的 window 内，`√|Rm_g|² ≤ 1200 · R(x)`。 -/
theorem SpatialNeck.sqrt_rmNormSq_map_le_CXCC {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M}
    (nk : SpatialNeck g eps x) {y : Cylinder} (hy : y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) :
    Real.sqrt (normSq0S g (nk.map y) 4 (metricRm04At g (nk.map y))) ≤
      1200 * metricScalarAt g x := by
  have heps := nk.eps_pos
  have hsmall := nk.eps_small
  have hinv : 11 < eps⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) heps]
    linarith
  set δ : ℝ := (eps⁻¹ - 1)⁻¹ with hδ
  have hδinv : δ⁻¹ = eps⁻¹ - 1 := by rw [hδ, inv_inv]
  have hfit : δ⁻¹ + 1 ≤ eps⁻¹ := by rw [hδinv]; linarith
  obtain ⟨V, Φ, hΦ, hjet⟩ := nk.exists_neckBuffer_pullback_bound hfit
  have hyB : y ∈ (neckBuffer δ : Set NeckCylinder) := by
    change -δ⁻¹ - 1 < y.2 ∧ y.2 < δ⁻¹ + 1
    rw [hδinv]
    constructor <;> linarith [hy.2.1, hy.2.2]
  let z : neckBuffer δ := ⟨y, hyB⟩
  let _ : SigmaCompactSpace (neckBuffer δ) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen NeckCylinderModel
      (neckBuffer δ).isOpen)
  have hceil : (2 : ℕ) ≤ ⌈eps⁻¹⌉₊ := by
    have h := Nat.le_ceil eps⁻¹
    have h2 : (2 : ℝ) ≤ (⌈eps⁻¹⌉₊ : ℝ) := by linarith
    exact_mod_cast h2
  have hpert := sqrt_normSq_metricRm04At_le_of_metricDerivNorm_le
    (roundCylinderMetric.restrictOpen (neckBuffer δ))
    (DifferentialGeometry.scaleMetric (metricScalarAt g x) nk.Q_pos
      (Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ))
    z (delta := eps) (by linarith) (fun a ha => hjet a (ha.trans hceil) z)
  rw [rmNormSq_restrictOpen_CXCC, rmNormSq_roundCylinder_CXCC, Real.sqrt_one,
    rmNormSq_scaleMetric_CXCC, riemannNormSq_cross, rmNormSq_restrictOpen_CXCC, hΦ] at hpert
  have hdim : ((Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) : ℕ) : ℝ) = 3 := by simp
  rw [hdim] at hpert
  have hQ := nk.Q_pos
  set N := normSq0S g (nk.map y) 4 (metricRm04At g (nk.map y))
  have hsq : Real.sqrt ((metricScalarAt g x)⁻¹ ^ 2 * N) =
      (metricScalarAt g x)⁻¹ * Real.sqrt N := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr hQ.le)]
  rw [hsq] at hpert
  have hb : (metricScalarAt g x)⁻¹ * Real.sqrt N ≤ 1200 := by
    have : 4 * (1 + (3 : ℝ) ^ 2 * eps * (1 + 360)) ≤ 1200 := by nlinarith
    linarith
  rw [inv_mul_le_iff₀ hQ] at hb
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

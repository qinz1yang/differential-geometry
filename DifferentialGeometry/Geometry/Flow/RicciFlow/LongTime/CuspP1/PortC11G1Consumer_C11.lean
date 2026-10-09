import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.TwoMapGermClosure
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.ForwardPhaseScalarContinuationConsumer
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.EqualAreaFoldArc
import DifferentialGeometry.Geometry.MinimalSurface.Boundary.ConormalGraphSide
import DifferentialGeometry.Geometry.MinimalSurface.Boundary.ConormalGraphCauchy
import DifferentialGeometry.Analysis.Elliptic.Planar.BoundaryCauchyUniqueness
import DifferentialGeometry.Analysis.Calculus.Inverse.TwoMapCommonProjection
import DifferentialGeometry.Geometry.HarmonicMap.TwoMapGraphContact

/-!
# S-MY-C11 G1 consumer：C11 F2 链（IMS03 tip `66cbb8d61`）整包搬入后的使用面

G1 = 17 个 verbatim 文件（`Embeddedness/TwoMapGermClosure` 闭包 + `Restriction/
ForwardPhaseScalarContinuationConsumer` 闭包；两个根的并集；搬入后归我们所有）。

* 十个 `example := @…`：对 C11 的公共定理做逐字型检查（陈述与 IMS03 完全一致），含两个根
  `actual_morrey_forward_phase_scalar_continuation` 与
  `IsMorreyDisk.image_germs_eq_of_regular_interior_limit`。
* `forward_phase_image_germ_pair_C11`：把 scalar continuation 的巨大结论压成 R5 链条下一步真正
  要的形状——原盘 `q` 的 trimmed 子盘 `affineSubdisk q 0 r` 与 alternate 盘 `aOrig` 在某一对内部点
  `(a, b)` 处取值相同且 image germ 相等（open coincidence patch 的 `yStar` 见证）。
  假设逐字取自 IMS03 定理，不加任何新前提。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Function Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry DifferentialGeometry.Analysis
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology ContDiff Manifold NNReal ENNReal ComplexConjugate

namespace GC.LongTime.CuspP1

/-- 逐字型检查（根 1）：actual forward-phase seam 上的 scalar continuation，给出 open coincidence patch
与 image germ。 -/
example :=
  @IMS03ConsumerAudit.actual_morrey_forward_phase_scalar_continuation

/-- 逐字型检查（根 2）：两个 Morrey 盘的 image germ 相等在 regular interior 极限点处保持。 -/
example :=
  @IsMorreyDisk.image_germs_eq_of_regular_interior_limit

/-- 逐字型检查：forward-phase seam 的 graph Cauchy data。 -/
example :=
  @IMS03ConsumerAudit.actual_morrey_forward_phase_graph_cauchy_data

/-- 逐字型检查：forward-phase seam 的 conormal cancellation。 -/
example :=
  @IMS03ConsumerAudit.actual_morrey_forward_phase_conormal_cancellation

/-- 逐字型检查：等面积两叶在 regular arc 上 conormal sum 为零（fold arc）。 -/
example :=
  @IsMorreyDisk.equal_area_two_sheet_conormal_sum_eq_zero_on_arc

/-- 逐字型检查：conormal cancellation ⇒ graph side reversal。 -/
example :=
  @exists_graph_side_reversal_of_trace_conormal_cancellation

/-- 逐字型检查：conormal cancellation ⇒ 固定 graph 的 frontier Cauchy data。 -/
example :=
  @exists_fixed_graph_frontier_cauchy_data_of_conormal_cancellation

/-- 逐字型检查：同一 isothermal 坐标下 regular side 的 boundary Cauchy 零 germ。 -/
example :=
  @planar_boundary_cauchy_zero_germ_on_regular_side_in_same_isothermal_coordinates

/-- 逐字型检查：两张映射的 common-projection inverse germs。 -/
example :=
  @exists_two_map_common_projection_inverse_germs

/-- 逐字型检查：同 tangent range 时 chart height 的 value / fderiv 相等。 -/
example :=
  @chart_height_value_fderiv_eq_of_tangent_range_le

/-- 原盘 `q` 的 trimmed 子盘 `affineSubdisk q 0 r` 与 alternate 盘 `aOrig` 在某一对内部点
`(a, b)` 处取值相同、image germ 相等：scalar continuation 的 `yStar` 见证。 -/
theorem forward_phase_image_germ_pair_C11
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : freeLoop M} {q : C(closedDisk, M)} (hq : IsMorreyDisk G γ q)
    (aOrig : C(closedDisk, M)) {r b : ℝ}
    (hr : 0 < r) (hrb : r < b) (hb : b < 1)
    (hd3 : Module.finrank ℝ E = 3)
    (haOrig : IsMorreyDisk G (diskTrace (affineSubdisk q 0 r)) aOrig)
    (QOriginal A : ℂ → M)
    (hQOriginal : SmoothDiskExtension (E := E) q QOriginal)
    (hA : SmoothDiskExtension (E := E) aOrig A)
    (ψ : ℝ → ℝ) (aForward : C(closedDisk, M)) (φ : ℝ ≃ₜ ℝ)
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ t))
    (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1)
    (D : ℂ → ℂ)
    (hbranch : (D = id ∧ aForward = aOrig ∧ ∀ t : ℝ, φ t = ψ t) ∨
      (D = conj ∧ aForward = aOrig.comp ⟨diskReflection, diskReflection.continuous⟩ ∧
        ∀ t : ℝ, φ t = ψ (-t)))
    (F : C(closedDisk, M)) {L : ℝ≥0}
    (hFLip : ∀ z w, riemannianEDistOf G (F z) (F w) ≤ (L : ℝ≥0∞) * edist z w)
    (hFtrace : diskTrace F = diskTrace q)
    (hFarea : riemannianDiskArea G F = riemannianDiskArea G q)
    (t₀ α : ℝ) (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hseam :
      t₀ ∈ Ioo (0 : ℝ) 1 ∧ 0 < deriv φ t₀ ∧ 0 < α ∧
      (∀ z : ℂ, χ z = r • Complex.diskBoundaryChart
        (diskBoundary (t₀ : loopCircle) : ℂ) (by simp [diskBoundary]) (α • z)) ∧
      Metric.closedBall (0 : ℂ) 1 ⊆ χ.source ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, r / 2 < ‖χ z‖ ∧ ‖χ z‖ < b) ∧
      χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 ∧
      let H := ForwardPhaseAnnulus.map r b hφ hp
      let ψAlt : ℂ → ℂ := fun z => (r⁻¹ : ℝ) • χ z
      let ψOuter : ℂ → ℂ := H ∘ χ ∘ conj
      let UAlt : ℂ → M := A ∘ (D ∘ ψAlt)
      let UOuter : ℂ → M := QOriginal ∘ ψOuter
      χ 0 = r • (diskBoundary (t₀ : loopCircle) : ℂ) ∧
      ψAlt 0 = (diskBoundary (t₀ : loopCircle) : ℂ) ∧
      ψOuter 0 = r • (diskBoundary (φ t₀ : loopCircle) : ℂ) ∧
      ContDiffOn ℝ ∞ ψAlt (Metric.ball (0 : ℂ) 1) ∧
      ContDiffOn ℝ ∞ ψOuter (Metric.ball (0 : ℂ) 1) ∧
      (∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), Bijective (fderiv ℝ ψAlt z)) ∧
      (∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), Bijective (fderiv ℝ ψOuter z)) ∧
      MapsTo ψAlt (closedHalfDisk 0 (1 / 4)) (Metric.closedBall (0 : ℂ) 1) ∧
      MapsTo ψAlt (openHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1) ∧
      MapsTo ψOuter (closedHalfDisk 0 (1 / 4)) (Metric.ball (0 : ℂ) 1) ∧
      (∀ z ∈ (openHalfDisk 0 (1 / 4) : Set ℂ), r < ‖ψOuter z‖ ∧ ‖ψOuter z‖ < b) ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UAlt (Metric.ball (0 : ℂ) 1) ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ UOuter (Metric.ball (0 : ℂ) 1) ∧
      (∀ z ∈ closedHalfDisk 0 (1 / 4), Injective
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UAlt (closedHalfDisk 0 (1 / 4)) z)) ∧
      (∀ z ∈ closedHalfDisk 0 (1 / 4), Injective
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) UOuter (closedHalfDisk 0 (1 / 4)) z)) ∧
      EqOn (diskExtension F ∘ χ) UAlt (closedHalfDisk 0 (1 / 4)) ∧
      EqOn (diskExtension F ∘ χ ∘ conj) UOuter (closedHalfDisk 0 (1 / 4)) ∧
      (∀ s ∈ Icc (-(1 / 4) : ℝ) (1 / 4), UAlt (s : ℂ) = UOuter (s : ℂ))) :
    ∃ a b : ℂ, a ∈ Metric.ball (0 : ℂ) 1 ∧ b ∈ Metric.ball (0 : ℂ) 1 ∧
      diskExtension (affineSubdisk q 0 r) a = diskExtension aOrig b ∧
      Filter.map (diskExtension (affineSubdisk q 0 r)) (𝓝 a) =
        Filter.map (diskExtension aOrig) (𝓝 b) := by
  obtain ⟨_, -, -, -, _, _, _, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ :=
    IMS03ConsumerAudit.actual_morrey_forward_phase_scalar_continuation
      G hq aOrig hr hrb hb hd3 haOrig QOriginal A hQOriginal hA ψ aForward φ hφ hp D hbranch F
      hFLip hFtrace hFarea t₀ α χ hseam
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfin⟩ := hrest
  obtain ⟨_, _, _, -, -, -, -, -, _, _, -, -, -, -, -, -, -, -, -, -, _, -, -, -, -,
    _, -, -, -, -, -, -, -, _, -, -, h2, h3, h4, h5⟩ := hfin
  exact ⟨_, _, h2, h3, h4, h5⟩

end GC.LongTime.CuspP1

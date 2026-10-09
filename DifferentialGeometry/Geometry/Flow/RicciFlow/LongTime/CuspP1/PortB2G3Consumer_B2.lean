import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BranchExclusion
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ImmersionSmoothInterior
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ReplacementFoldArc
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.CriticalValues
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.SeamProjection
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.ProfileAlternateConfinement
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.RegularValueSourceConnected
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.ForwardPhaseSeamChartConsumer

/-!
# S-MY-PORT-B2 G3 consumer：MY 支撑包的「其余根」（含 B1 依赖的一半）

G3 = `BranchExclusion`、`ImmersionSmoothInterior`、`ReplacementFoldArc`
（后两个分别依赖 B1 搬入的 `Measure/Area/ImmersionPullback`、`Plateau/ReplacementFold`）、
`Restriction/{CriticalValues, SeamProjection, ProfileAlternateConfinement,
RegularValueSourceConnected, ForwardPhaseSeamChartConsumer}`（IMS03 tip `66cbb8d61` 的逐字节拷贝）。

* 八个 `example := @…`：对八个根定理做逐字型检查（陈述与 IMS03 完全一致）。
* `restriction_pair_critical_values_locally_finite_B2`：affine 限制盘与 alternate 盘的 interior
  critical values 在 trace 之外局部有限（`CriticalValues` 的使用形式）。
* `pullback_area_iff_B2`：immersion 下 smooth-interior 盘的 pullback-metric 面积相等 ⇔
  推前盘的原 metric 面积相等（`riemannianDiskArea_pullback_immersion_of_smoothInterior` 用两次）。
不加任何新前提，所有假设逐字取自 IMS03 定理。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold MeasureTheory Metric DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry
open scoped Topology ContDiff Manifold

namespace GC.LongTime.CuspP1

/-- 逐字型检查：leading-projection contact germs 的 continuous factor（BranchExclusion）。 -/
example :=
  @DifferentialGeometry.Geometry.exists_continuous_factor_of_leading_projection_contact_germs

/-- 逐字型检查：immersion 下 smooth-interior 盘的 pullback 面积。 -/
example := @DifferentialGeometry.Geometry.riemannianDiskArea_pullback_immersion_of_smoothInterior

/-- 逐字型检查：replacement 弧上的 conormal sum 为零。 -/
example :=
  @DifferentialGeometry.Geometry.IsMorreyDisk.sourceChart_replacement_conormal_sum_eq_zero_on_arc

/-- 逐字型检查：proper restriction 的 critical values 在 trace 外局部有限。 -/
example :=
  @IMS03Embeddedness.ConsumerAudit.actual_proper_restriction_pair_critical_values_away_trace

/-- 逐字型检查：actual Morrey 盘的 seam projection 与 split。 -/
example := @IMS03Embeddedness.actual_morrey_seam_projection_and_split

/-- 逐字型检查：profile alternate 的 negative margin 与 compact 原像。 -/
example :=
  @DifferentialGeometry.Geometry.profile_alternate_negative_margin_and_compact_original_preimage

/-- 逐字型检查：删去 critical values 后的 source preimage 连通。 -/
example :=
  @IMS03Embeddedness.ConsumerAudit.actual_proper_restriction_regular_value_source_connected

/-- 逐字型检查：actual Morrey 盘的 regular forward-phase seam chart。 -/
example :=
  @DifferentialGeometry.Geometry.IMS03ConsumerAudit.actual_morrey_regular_forward_phase_seam_chart

/-- affine 限制盘 `qRest` 与 alternate 盘 `qAlt` 的 interior critical values 在 trace 之外局部有限。 -/
theorem restriction_pair_critical_values_locally_finite_B2
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (QOriginal : ℂ → M) (hQOriginal : SmoothDiskExtension (E := E) u QOriginal)
    (a : ℂ) (r : ℝ) (hr : 0 < r) (hinside : ‖a‖ + r < 1)
    (hloop : IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk u a r)))
    (qAlt : C(closedDisk, M))
    (hqAlt : IsMorreyDisk g (diskTrace (affineSubdisk u a r)) qAlt)
    {y : M} (hy : y ∉ Set.range (diskTrace (affineSubdisk u a r))) :
    ∃ V : Set M, IsOpen V ∧ y ∈ V ∧ V ⊆ (Set.range (diskTrace (affineSubdisk u a r)))ᶜ ∧
      ((diskInteriorCriticalValues (E := E) (affineSubdisk u a r) ∪
        diskInteriorCriticalValues (E := E) qAlt) ∩ V).Finite :=
  (IMS03Embeddedness.ConsumerAudit.actual_proper_restriction_pair_critical_values_away_trace
    hu QOriginal hQOriginal a r hr hinside hloop qAlt hqAlt).2 y hy

/-- 两个 smooth-interior 盘在 pullback metric 下面积相等，当且仅当它们在 immersion 下的像盘
在原 metric 下面积相等。 -/
theorem pullback_area_iff_B2
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    {g : SmoothRiemannianMetric 𝓘(ℝ, F) N} {p : M → N}
    (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p x))
    {u v : C(closedDisk, M)} (hu : DiskSmoothInterior (E := E) u)
    (hv : DiskSmoothInterior (E := E) v) :
    riemannianDiskArea (g.pullback p hp himm) u = riemannianDiskArea (g.pullback p hp himm) v ↔
      riemannianDiskArea g (p ∘ u) = riemannianDiskArea g (p ∘ v) := by
  rw [riemannianDiskArea_pullback_immersion_of_smoothInterior g p hp himm u hu,
    riemannianDiskArea_pullback_immersion_of_smoothInterior g p hp himm v hv]

end GC.LongTime.CuspP1

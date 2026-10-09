import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TraceRestrictionBack_CX2

set_option autoImplicit false

/-!
# CX-SPINE G23：完整 small seed 的双向 restriction

准确识别空间r、深度r²、曲率阈值((√3*r)²)⁻¹的traced region。
复用已证明 ordinary+terminal bounded trace 的restriction iff，允许cut等于顶时刻。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

/-- small seed 与独立空间/时间/控制尺度的 traced region 准确等价。 -/
theorem smallParabolicCurvature_iff_traced_CXSP
    {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {r : ℝ} :
    hasSmallParabolicCurvature H t p r ↔
      H.isTracedRegion t p r (r ^ 2) ((Real.sqrt 3 * r) ^ 2)⁻¹ := by
  constructor
  · rintro ⟨hr, a, hat, ha, htrace⟩
    refine ⟨hr, sq_pos_of_pos hr, a, hat, ha, ?_⟩
    intro x hx
    obtain ⟨A, hA⟩ := htrace x hx
    exact ⟨A, (A.isRmControlled_iff_isRmBoundedBy (by positivity)).mp hA⟩
  · rintro ⟨hr, -, a, hat, ha, htrace⟩
    refine ⟨hr, a, hat, ha, ?_⟩
    intro x hx
    obtain ⟨A, hA⟩ := htrace x hx
    exact ⟨A, (A.isRmControlled_iff_isRmBoundedBy (by positivity)).mpr hA⟩

/-- 限制顶时刻之后的 history 不改变整个 seed；ordinary 与terminal控制均双向保留。 -/
theorem smallParabolicCurvature_restrict_iff_CXSP
    {H : ObservedHistory.{u}} {cut : Icc (0 : ℝ) H.horizon}
    {t : Icc (0 : ℝ) (H.restrict cut).horizon} {p : ((H.restrict cut).stageAt t).Carrier}
    {r : ℝ} :
    hasSmallParabolicCurvature (H.restrict cut) t p r ↔
      hasSmallParabolicCurvature H (Ch12.restrictTime_CX2 H cut t)
        (Ch12.restrictPoint_CX2 H cut t p) r := by
  rw [smallParabolicCurvature_iff_traced_CXSP, smallParabolicCurvature_iff_traced_CXSP]
  exact Ch12.isTracedRegion_restrict_iff_CX2 H cut t p r (r ^ 2) ((Real.sqrt 3 * r) ^ 2)⁻¹

end GC.LongTime.Ch11

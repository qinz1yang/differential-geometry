import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.OrientedForwardPhaseDiskConsumer
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TracePhaseAnnulus.Relative

/-!
# S-MY-PORT-B2 G1 consumer：MY-2（C10）三个根定理的型检查与实际使用

G1 = C10（IMS03 tip `66cbb8d61` 的逐字节拷贝）：
`exists_forwardPhase_pastedDisk`（`Measure/Area/ForwardPhaseDisk`）、
`exists_relative_phase_correction`（`TracePhaseAnnulus/Relative`）、
`IMS03Embeddedness.ConsumerAudit.actual_morrey_oriented_forward_phase_splice`
（`Restriction/OrientedForwardPhaseDiskConsumer`）。

* 三个 `example := @…`：逐字的型检查（陈述与 IMS03 完全一致）。
* `forwardPhase_pastedDisk_trace_area_B2`：pasted disk 的 trace 不变，面积 = 原面积减去内圆盘
  面积再加 alternate filling 的面积。
* `relative_phase_correction_trace_area_B2`：相位校正后 trace 变成 `γ`，面积不变（zero area cost）。
* `morrey_oriented_splice_competitor_B2`：对 actual Morrey disk 做 oriented splice 得到的 `F`
  与 `q` 同 trace、同面积、range 落在 `W`、trace 仍是 weak Jordan —— MY-2 要的 competitor。
  不加任何新前提，所有假设逐字取自 IMS03 的 splice 定理。
-/

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace GC.LongTime.CuspP1

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- 逐字型检查：forward-phase paste。 -/
example := @DifferentialGeometry.Geometry.exists_forwardPhase_pastedDisk

/-- 逐字型检查：relative phase correction。 -/
example := @DifferentialGeometry.Geometry.exists_relative_phase_correction

/-- 逐字型检查：actual Morrey disk 的 oriented forward-phase splice。 -/
example := @IMS03Embeddedness.ConsumerAudit.actual_morrey_oriented_forward_phase_splice

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Forward-phase paste 的面积账：trace 不变，`F` 的面积 = `q` 的面积 − 内圆盘面积 + `a` 的面积。 -/
theorem forwardPhase_pastedDisk_trace_area_B2
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q a : C(closedDisk, M))
    {Lq La : ℝ≥0}
    (hqLip : ∀ z w : closedDisk, riemannianEDistOf G (q z) (q w) ≤
      (Lq : ℝ≥0∞) * edist z w)
    (haLip : ∀ z w : closedDisk, riemannianEDistOf G (a z) (a w) ≤
      (La : ℝ≥0∞) * edist z w)
    (hqSmooth : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension q)
      (Metric.ball (0 : ℂ) 1))
    {r b : ℝ} (hr : 0 < r) (hrb : r < b) (hb : b < 1)
    (φ : ℝ ≃ₜ ℝ) (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ t))
    (hm : StrictMono φ) (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1)
    (htrace : ∀ t : ℝ, diskTrace a (t : loopCircle) =
      diskExtension q (r • (AddCircle.toCircle (φ t : loopCircle) : ℂ))) :
    ∃ F : C(closedDisk, M), diskTrace F = diskTrace q ∧
      riemannianDiskArea G F = riemannianDiskArea G q -
        riemannianArea G (diskExtension q) (Metric.closedBall (0 : ℂ) r) +
        riemannianDiskArea G a := by
  obtain ⟨F, _, -, -, -, -, -, htr, -, -, harea⟩ :=
    exists_forwardPhase_pastedDisk G q a hqLip haLip hqSmooth hr hrb hb φ hφ hm hp htrace
  exact ⟨F, htr, harea⟩

/-- Relative phase correction 的 zero-area-cost 版本：trace 变成 `γ`，面积不变。 -/
theorem relative_phase_correction_trace_area_B2
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {v : C(closedDisk, M)} {γ : freeLoop M} {Ku : ℝ≥0}
    (hu : ∀ z w : closedDisk, riemannianEDistOf g (v z) (v w) ≤ (Ku : ℝ≥0∞) * edist z w)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hm : Monotone ρ)
    (hp : ∀ t, ρ (t + 1) = ρ t + 1)
    (htrace : ∀ t : ℝ, diskTrace v (t : loopCircle) = γ (ρ t : loopCircle))
    {s ε : ℝ} (hε : 0 < ε) (hlocal : ∀ t : ℝ, |t - s| < ε → ρ t = t) :
    ∃ dFill : C(closedDisk, M), diskTrace dFill = γ ∧
      riemannianDiskArea g dFill = riemannianDiskArea g v := by
  obtain ⟨dFill, _, _, _, _, htr, harea, -, -, -⟩ :=
    exists_relative_phase_correction g hu hγ hρ hm hp htrace hε hlocal
  exact ⟨dFill, htr, harea⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- MY-2 competitor：actual Morrey disk `q` 做 oriented forward-phase splice 得到 `F`，
`F` 与 `q` 同 trace、同面积，range 落在 `W` 内，trace 仍是 weak Jordan。 -/
theorem morrey_oriented_splice_competitor_B2
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : freeLoop M} {q : C(closedDisk, M)} (hq : IsMorreyDisk G γ q)
    (aOrig : C(closedDisk, M)) {Lq La : ℝ≥0}
    (hqLip : ∀ z w : closedDisk, riemannianEDistOf G (q z) (q w) ≤
      (Lq : ℝ≥0∞) * edist z w)
    (haOrigLip : ∀ z w : closedDisk, riemannianEDistOf G (aOrig z) (aOrig w) ≤
      (La : ℝ≥0∞) * edist z w)
    {r2 b : ℝ} (hr2 : 0 < r2) (hr2b : r2 < b) (hb : b < 1)
    (haOrig : IsMorreyDisk G (diskTrace (affineSubdisk q 0 r2)) aOrig)
    (hΓ : IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk q 0 r2)))
    {A : ℂ → M} (hA : SmoothDiskExtension (E := E) aOrig A)
    {W : Set M} (hqW : Set.range q ⊆ W) (haOrigW : Set.range aOrig ⊆ W) :
    ∃ F : C(closedDisk, M), diskTrace F = diskTrace q ∧
      riemannianDiskArea G F = riemannianDiskArea G q ∧
      Set.range F ⊆ W ∧ DiskWeakJordanTrace γ F := by
  obtain ⟨-, -, -, -, -, -, aForward, φ, hφ, hp, -, -, -, -, -, -, F, KF, hF⟩ :=
    IMS03Embeddedness.ConsumerAudit.actual_morrey_oriented_forward_phase_splice
      G hq aOrig hqLip haOrigLip hr2 hr2b hb haOrig hΓ hA hqW haOrigW
  obtain ⟨-, -, -, -, -, htr, -, -, -, hW, hJ, -, -, -, harea⟩ := hF
  exact ⟨F, htr, harea, hW, hJ⟩

end GC.LongTime.CuspP1

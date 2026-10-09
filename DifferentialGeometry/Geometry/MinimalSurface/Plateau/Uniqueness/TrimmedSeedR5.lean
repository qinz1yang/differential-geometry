import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Uniqueness.DegreeOneR5
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.ForwardPhaseScalarContinuationConsumer
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.ForwardPhaseSeamChartConsumer
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.OrientedForwardPhaseDiskConsumer
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.BoundaryArcADP
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SecondTrimR8
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TrimCollarMR1

/-!
# O-MY-R5 G4（上）：R5 的输入胶水与 seed（S0–S3）

R5 合同（scratch `MYD3/R03R05.lean:90`）的输入：`q` Morrey（trace `γ`）、`SmoothDiskExtension q Q`、闭盘 rank、
collar `hcol`（`ρ₀ < ‖z‖ ⇒ q z = q w ⇒ z = w`）、`0 < ρ₀ < r₂ < 1`、`u` 是
`Γ₂ := diskTrace (affineSubdisk q 0 r₂)`
的 Morrey 盘。本文件生产 G3 / G2 所需的全部输入：
* S0：`q` 的 R3b 前提（边界单射、内部不碰边界——均由 `hcol`）、`coincidentGermPairs q = ∅`、开盘 rank、
  fiber 有限、`diskExtension q` 全局 Lipschitz；`Γ₂` smooth embedded（`isSmoothEmbeddedLoop_trim_R8`）；
  `q⁻¹(Γ₂) ⊆ r₂S¹`；`diskTrace q₂` 单射；
* S1：`A(U, D°) ≤ A(V, D_{r₂})`（splice 给出的 `A(u) = A(V, closedBall 0 r₂)`，球与闭球差零测）；
* S2–S3：splice → seam chart → scalar continuation ⇒ seed germ pair（`exists_trimmed_seed_R5`）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Function Metric Manifold DifferentialGeometry MeasureTheory ComplexConjugate
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

/-- 闭盘内 `affineSubdisk q 0 r` 的延拓是 `diskExtension q` 的缩放。 -/
theorem diskExtension_affineSubdisk_R5 {Y : Type*} [TopologicalSpace Y] (q : C(closedDisk, Y))
    (r : ℝ) {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1) :
    diskExtension (affineSubdisk q 0 r) w = diskExtension q ((r : ℂ) * w) := by
  have h := diskExtension_coe (affineSubdisk q 0 r : closedDisk → Y) ⟨w, hw⟩
  change diskExtension (affineSubdisk q 0 r) w = _ at h
  rw [h]
  change diskExtension q (0 + r • w) = _
  rw [zero_add, Complex.real_smul]

/-- 闭盘上的 Lipschitz ⇒ `diskExtension` 全局 Lipschitz。 -/
theorem diskExtension_lipschitz_R5 {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {q : C(closedDisk, M)} {L : ℝ≥0}
    (hL : ∀ z w : closedDisk, riemannianEDistOf g (q z) (q w) ≤ (L : ℝ≥0∞) * edist z w) :
    ∀ x y : ℂ, riemannianEDistOf g (diskExtension q x) (diskExtension q y) ≤
      (L : ℝ≥0∞) * edist x y := by
  intro x y
  calc riemannianEDistOf g (diskExtension q x) (diskExtension q y)
      ≤ (L : ℝ≥0∞) * edist (diskRetraction x) (diskRetraction y) := hL _ _
    _ ≤ (L : ℝ≥0∞) * edist x y := by
      gcongr
      simpa using diskRetraction_lipschitz.edist_le_mul x y

/-- 开球与闭球上的面积相同（球面零测）。 -/
theorem riemannianArea_ball_eq_closedBall_R5 {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (r : ℝ) :
    riemannianArea g U (ball 0 r) = riemannianArea g U (closedBall 0 r) := by
  unfold riemannianArea
  apply setIntegral_congr_set
  refine ae_eq_set.mpr ⟨?_, ?_⟩
  · rw [sdiff_eq_empty.mpr ball_subset_closedBall]
    exact measure_empty
  · rw [closedBall_sdiff_ball]
    exact Measure.addHaar_sphere volume 0 r

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- 闭盘 rank ⇒ 开盘内 `diskExtension q` rank 2。 -/
theorem diskExtension_rank_of_closed_rank_R5 {q : C(closedDisk, M)} {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ closedBall (0 : ℂ) 1, Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) :
    ∀ W ∈ ball (0 : ℂ) 1, Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) W) := by
  intro W hW
  have heq : diskExtension q =ᶠ[𝓝 W] Q := by
    filter_upwards [isOpen_ball.mem_nhds hW] with z hz
    have h := diskExtension_coe (q : closedDisk → M) ⟨z, ball_subset_closedBall hz⟩
    change diskExtension q z = q ⟨z, ball_subset_closedBall hz⟩ at h
    rw [h, ← hQ.1 ⟨z, ball_subset_closedBall hz⟩]
  rw [heq.mfderiv_eq]
  exact hrank W (ball_subset_closedBall hW)

/-- collar 的推论：`q` 边界单射、内部像不碰边界像、`Γ₂` 的 fiber 在 `r₂S¹` 上、`diskTrace q₂` 单射。 -/
theorem collar_consequences_R5 {q : C(closedDisk, M)} {ρ₀ r₂ : ℝ}
    (hcol : ∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w) (hr : ρ₀ < r₂)
    (hr1 : r₂ < 1) (hr0 : 0 < r₂) :
    (∀ θ θ' : loopCircle, q (diskBoundary θ) = q (diskBoundary θ') → θ = θ') ∧
    (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, q z ≠ q (diskBoundary θ)) ∧
    (∀ w ∈ closedBall (0 : ℂ) 1,
      diskExtension q w ∈ range (diskTrace (affineSubdisk q 0 r₂)) → ‖w‖ = r₂) ∧
    Injective (diskTrace (affineSubdisk q 0 r₂)) := by
  have hρ1 : ρ₀ < 1 := hr.trans hr1
  have hbn : ∀ θ : loopCircle, ‖((diskBoundary θ : closedDisk) : ℂ)‖ = 1 := norm_diskBoundary_R5
  -- `Γ₂ θ = q ⟨r₂ ∂θ⟩`
  have hmemr : ∀ θ : loopCircle, (r₂ : ℂ) * (diskBoundary θ : ℂ) ∈ closedBall (0 : ℂ) 1 := by
    intro θ
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, hbn, mul_one]
    exact hr1.le
  have hnr : ∀ θ : loopCircle, ‖(r₂ : ℂ) * (diskBoundary θ : ℂ)‖ = r₂ := by
    intro θ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hbn, mul_one]
  have hΓ : ∀ θ : loopCircle, diskTrace (affineSubdisk q 0 r₂) θ =
      q ⟨(r₂ : ℂ) * (diskBoundary θ : ℂ), hmemr θ⟩ := by
    intro θ
    change affineSubdisk q 0 r₂ (diskBoundary θ) = _
    have h := diskExtension_affineSubdisk_R5 q r₂ (diskBoundary θ).property
    rw [diskExtension_coe] at h
    rw [h]
    exact diskExtension_coe (q : closedDisk → M) ⟨_, hmemr θ⟩
  refine ⟨fun θ θ' h => ?_, fun z hz θ h => ?_, fun w hw hmem => ?_, fun θ θ' h => ?_⟩
  · have := hcol _ _ (by rw [hbn]; exact hρ1) h
    exact diskBoundary_coe_injective_R5 (congrArg Subtype.val this)
  · have := hcol _ _ (by rw [hbn]; exact hρ1) h.symm
    rw [← this, hbn] at hz
    exact lt_irrefl _ hz
  · obtain ⟨θ, hθ⟩ := hmem
    rw [hΓ θ] at hθ
    have h2 : diskExtension q w = q ⟨w, hw⟩ := diskExtension_coe (q : closedDisk → M) ⟨w, hw⟩
    rw [h2] at hθ
    have := hcol _ _ (by change ρ₀ < ‖(r₂ : ℂ) * (diskBoundary θ : ℂ)‖; rw [hnr]; exact hr) hθ
    have hv := congrArg Subtype.val this
    change (r₂ : ℂ) * (diskBoundary θ : ℂ) = w at hv
    rw [← hv, hnr]
  · rw [hΓ, hΓ] at h
    have := hcol _ _ (by change ρ₀ < ‖(r₂ : ℂ) * (diskBoundary θ : ℂ)‖; rw [hnr]; exact hr) h
    have hv := congrArg Subtype.val this
    change (r₂ : ℂ) * (diskBoundary θ : ℂ) = (r₂ : ℂ) * (diskBoundary θ' : ℂ) at hv
    have hr0' : (r₂ : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    exact diskBoundary_coe_injective_R5 (mul_left_cancel₀ hr0' hv)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- trimmed trace 的 rank：`w ↦ diskExtension q (r₂ • w)` 在单位圆上 rank 2。 -/
theorem trimmed_trace_rank_R5 {q : C(closedDisk, M)} {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ closedBall (0 : ℂ) 1, Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    {r₂ : ℝ} (hr0 : 0 < r₂) (hr1 : r₂ < 1) :
    ∀ z : ℂ, ‖z‖ = 1 → Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w : ℂ => diskExtension q (r₂ • w)) z) := by
  intro z hz
  have hsc : Continuous fun w : ℂ => r₂ • w := by fun_prop
  have hzB : r₂ • z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hz, mul_one]
    exact hr1
  have heq : (fun w : ℂ => diskExtension q (r₂ • w)) =ᶠ[𝓝 z] Q ∘ fun w : ℂ => r₂ • w := by
    filter_upwards [hsc.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hzB)] with w hw
    have hwK : r₂ • w ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hw
    have h := diskExtension_coe (q : closedDisk → M) ⟨r₂ • w, hwK⟩
    change diskExtension q (r₂ • w) = q ⟨r₂ • w, hwK⟩ at h
    change diskExtension q (r₂ • w) = Q (r₂ • w)
    rw [h, ← hQ.1 ⟨r₂ • w, hwK⟩]
  obtain ⟨-, N, hN, hDN, hQN⟩ := hQ
  have hQd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q (r₂ • z) :=
    (hQN.contMDiffAt (hN.mem_nhds (hDN (ball_subset_closedBall hzB)))).mdifferentiableAt
      (by simp)
  have hsd : HasFDerivAt (fun w : ℂ => r₂ • w) (r₂ • ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).const_smul r₂
  have hsm : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : ℂ => r₂ • w) z :=
    hsd.differentiableAt.mdifferentiableAt
  rw [heq.mfderiv_eq, mfderiv_comp z hQd hsm, mfderiv_eq_fderiv, hsd.fderiv]
  intro v w hvw
  have h1 : (r₂ • ContinuousLinearMap.id ℝ ℂ) v = (r₂ • ContinuousLinearMap.id ℝ ℂ) w :=
    hrank (r₂ • z) (ball_subset_closedBall hzB) hvw
  have h2 : r₂ • v = r₂ • w := h1
  have hr0' : r₂ ≠ 0 := hr0.ne'
  exact smul_right_injective ℂ hr0' h2

/-- `Γ₂ := diskTrace (affineSubdisk q 0 r₂)` 是 smooth embedded loop
（`isSmoothEmbeddedLoop_trim_R8`）。 -/
theorem trimmed_trace_embedded_R5 [T2Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q) {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ closedBall (0 : ℂ) 1, Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    {ρ₀ r₂ : ℝ} (hcol : ∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w)
    (hr : ρ₀ < r₂) (hr0 : 0 < r₂) (hr1 : r₂ < 1) :
    IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk q 0 r₂)) := by
  refine isSmoothEmbeddedLoop_trim_R8 hq hr0 hr1 (trimmed_trace_rank_R5 hQ hrank hr0 hr1) ?_
  intro z w hz hzw
  have hmem : ∀ x : closedDisk, (r₂ : ℂ) * (x : ℂ) ∈ closedBall (0 : ℂ) 1 := by
    intro x
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    calc r₂ * ‖(x : ℂ)‖ ≤ 1 * 1 := by
          apply mul_le_mul hr1.le (mem_closedBall_zero_iff.mp x.property) (norm_nonneg _)
            zero_le_one
      _ = 1 := by norm_num
  have hval : ∀ x : closedDisk, affineSubdisk q 0 r₂ x = q ⟨(r₂ : ℂ) * (x : ℂ), hmem x⟩ := by
    intro x
    have h := diskExtension_affineSubdisk_R5 q r₂ x.property
    rw [diskExtension_coe] at h
    rw [h]
    exact diskExtension_coe (q : closedDisk → M) ⟨_, hmem x⟩
  rw [hval, hval] at hzw
  have hnz : ρ₀ < ‖((⟨(r₂ : ℂ) * (z : ℂ), hmem z⟩ : closedDisk) : ℂ)‖ := by
    change ρ₀ < ‖(r₂ : ℂ) * (z : ℂ)‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hz, mul_one]
    exact hr
  have h := congrArg Subtype.val (hcol _ _ hnz hzw)
  change (r₂ : ℂ) * (z : ℂ) = (r₂ : ℂ) * (w : ℂ) at h
  have hr0' : (r₂ : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  exact Subtype.ext (mul_left_cancel₀ hr0' h)

/-- **seed（S1–S3）**：splice → seam chart → scalar continuation。给出 R2 等面积
`A(u) = A(V, closedBall 0 r₂)` 与 `q₂`、`u` 的一对 image germ 相等的内点。 -/
theorem exists_trimmed_seed_R5 [T3Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hd3 : Module.finrank ℝ E = 3) {γ : freeLoop M} {q : C(closedDisk, M)}
    (hq : IsMorreyDisk g γ q) {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    {r₂ : ℝ} (hr0 : 0 < r₂) (hr1 : r₂ < 1)
    (hΓ₂ : IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk q 0 r₂)))
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g (diskTrace (affineSubdisk q 0 r₂)) u) :
    riemannianDiskArea g u = riemannianArea g (diskExtension q) (closedBall (0 : ℂ) r₂) ∧
      ∃ a b : ℂ, a ∈ ball (0 : ℂ) 1 ∧ b ∈ ball (0 : ℂ) 1 ∧
        diskExtension (affineSubdisk q 0 r₂) a = diskExtension u b ∧
        Filter.map (diskExtension (affineSubdisk q 0 r₂)) (𝓝 a) =
          Filter.map (diskExtension u) (𝓝 b) := by
  obtain ⟨Lq, hqLip⟩ := hQ.lipschitz g
  obtain ⟨A, hA, La, hLa⟩ := morrey_disk_closed_extension_lipschitz_ADP g hΓ₂ hu
  have hrb : r₂ < (r₂ + 1) / 2 := by linarith
  have hb : (r₂ + 1) / 2 < 1 := by linarith
  obtain ⟨σ, ψ, -, -, -, -, aForward, φ, hφ, hp, hbranch, -, htrace, -, -, -, F, KF, -, hFLip,
      hFinner, hFmiddle, -, hFtrace, -, -, -, -, -, -, -, hAarea, hFarea⟩ :=
    IMS03Embeddedness.ConsumerAudit.actual_morrey_oriented_forward_phase_splice g hq u hqLip hLa
      hr0 hrb hb hu hΓ₂ hA (W := univ) (subset_univ _) (subset_univ _)
  obtain ⟨D, hbranchD, -, -, t₀, α, χ, hseam⟩ :=
    IMS03ConsumerAudit.actual_morrey_regular_forward_phase_seam_chart g hq u hr0 hrb hb hu hΓ₂
      Q A hQ hA ψ aForward φ hφ hp hbranch htrace F hFinner hFmiddle
  refine ⟨hAarea, ?_⟩
  obtain ⟨_, -, -, -, _, _, _, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ :=
    IMS03ConsumerAudit.actual_morrey_forward_phase_scalar_continuation
      g hq u hr0 hrb hb hd3 hu Q A hQ hA ψ aForward φ hφ hp D hbranchD F
      hFLip hFtrace hFarea t₀ α χ hseam
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfin⟩ := hrest
  obtain ⟨_, _, _, -, -, -, -, -, _, _, -, -, -, -, -, -, -, -, -, -, _, -, -, -, -,
    _, -, -, -, -, -, -, -, _, -, -, h2, h3, h4, h5⟩ := hfin
  exact ⟨_, _, h2, h3, h4, h5⟩

end DifferentialGeometry.Geometry

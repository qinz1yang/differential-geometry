import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PairedReplacementFoldLocalRank

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology Manifold ContDiff NNReal ENNReal ComplexConjugate

-- S-MY-PORT-B1 G3 consumer：C8（`PairedSubdiskReplacement` / `PairedReplacementFold` /
-- `PairedReplacementFoldLocalRank`，verbatim IMS03）的型检查（MY-11/12 smooth engine）。

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

-- `PairedReplacementFold.lean:764`：Morrey minimizer 上的 paired source disks 在 matched circle
-- 点不能 transverse；若 `coprod` 满射则 `False`。
example
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) {Uext : ℂ → M} (hUext : SmoothDiskExtension (E := E) u Uext)
    (e₁ e₂ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hsrc₁ : Metric.closedBall (0 : ℂ) 1 ⊆ e₁.source)
    (hsrc₂ : Metric.closedBall (0 : ℂ) 1 ⊆ e₂.source)
    (hinside₁ : e₁ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hinside₂ : e₂ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      diskExtension u (e₁ z) = diskExtension u (e₂ z))
    (hiU : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z))
    (hdim : Module.finrank ℝ E = 3)
    {W : Set M} (huW : Set.range u ⊆ W) (p : ℂ) (hp : ‖p‖ = 1)
    (hpW : diskExtension u (e₁ p) ∈ interior W)
    (htrans : Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (e₁ p)).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (e₂ p))))) :
    False :=
  hu.not_transverse_of_paired_source_disks hUext e₁ e₂ hsrc₁ hsrc₂ hinside₁ hinside₂ hboundary
    hiU hdim huW p hp hpW htrans

-- `PairedReplacementFoldLocalRank.lean:155`：只在两个 matched 点要求 `mfderiv` 单射
-- （MY-11/12 的 local-rank 形），C¹ charts 仅在 `p` 附近要求光滑。
example
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) {Uext : ℂ → M} (hUext : SmoothDiskExtension (E := E) u Uext)
    (e₁ e₂ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ 1)
    (hsrc₁ : Metric.closedBall (0 : ℂ) 1 ⊆ e₁.source)
    (hsrc₂ : Metric.closedBall (0 : ℂ) 1 ⊆ e₂.source)
    (hinside₁ : e₁ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hinside₂ : e₂ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      diskExtension u (e₁ z) = diskExtension u (e₂ z))
    (hdim : Module.finrank ℝ E = 3)
    {W : Set M} (huW : Set.range u ⊆ W) (p : ℂ) (hp : ‖p‖ = 1)
    (hiU₁ : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (e₁ p)))
    (hiU₂ : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (e₂ p)))
    (V₁ V₂ : Set ℂ) (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂)
    (hpV₁ : p ∈ V₁) (hpV₂ : p ∈ V₂)
    (he₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e₁ V₁)
    (he₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e₂ V₂)
    (hpW : diskExtension u (e₁ p) ∈ interior W)
    (htrans : Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (e₁ p)).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (e₂ p))))) :
    False :=
  hu.not_transverse_of_paired_source_disks_smooth_near_of_injective_at hUext e₁ e₂
    hsrc₁ hsrc₂ hinside₁ hinside₂ hboundary hdim huW p hp hiU₁ hiU₂ V₁ V₂ hV₁ hV₂ hpV₁ hpV₂
    he₁ he₂ hpW htrans

end

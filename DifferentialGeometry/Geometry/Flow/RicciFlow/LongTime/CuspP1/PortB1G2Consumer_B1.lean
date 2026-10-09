import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.DistinctFillingNoFold
import DifferentialGeometry.Analysis.Calculus.MapConvergence.ManifoldTransverseIntersection
import DifferentialGeometry.Topology.Embedding.TransverseIntersectionLimit
import DifferentialGeometry.Geometry.Measure.Area.RadialConeMetric

set_option autoImplicit false
noncomputable section

-- S-MY-PORT-B1 G2 consumer：C4（MY-13）、C5（fold）、C6（cone）三件 verbatim IMS03 文件的型检查。
-- 每段 `section` 自己 `open`；MY-13 两个同名定理
-- `not_surjective_coprod_mfderiv_of_injective_c1_limit`（`DifferentialGeometry.Analysis` 与
-- `DifferentialGeometry.Topology.Manifold`）都用全限定名，两个 namespace 都不 `open`。

section MY13Analysis

open Set Filter Manifold
open scoped Topology ContDiff Manifold

-- `ℂ` 上开集 `V` 的 chartwise C¹ limit of injective maps 没有 transverse double point：
-- 若 `(mfderiv u₀ a).coprod (-(mfderiv u₀ b))` 满射则矛盾。
example {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {V : Set ℂ} (hV : IsOpen V) {u : ℕ → ℂ → M} {u₀ : ℂ → M}
    {a b : ℂ} (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) (heq : u₀ a = u₀ b)
    (hu : ∀ᶠ n in atTop, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (u n) V)
    (hu₀ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 u₀ V)
    (hinj : ∀ᶠ n in atTop, Set.InjOn (u n) V)
    (hchart₀ : MapsTo u₀ V (extChartAt 𝓘(ℝ, E) (u₀ a)).source)
    (hchart : ∀ᶠ n in atTop,
      MapsTo (u n) V (extChartAt 𝓘(ℝ, E) (u₀ a)).source)
    (hval : ∀ z ∈ V, Tendsto
      (fun n => extChartAt 𝓘(ℝ, E) (u₀ a) (u n z)) atTop
      (𝓝 (extChartAt 𝓘(ℝ, E) (u₀ a) (u₀ z))))
    (hder : ∀ K : Set ℂ, IsCompact K → K ⊆ V →
      TendstoUniformlyOn
        (fun n z => fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) (u₀ a) (u n w)) z)
        (fun z => fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) (u₀ a) (u₀ w)) z)
        atTop K)
    (hsurj : Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u₀ a).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u₀ b)))) :
    False :=
  DifferentialGeometry.Analysis.not_surjective_coprod_mfderiv_of_injective_c1_limit
    hV ha hb hab heq hu hu₀ hinj hchart₀ hchart hval hder hsurj

end MY13Analysis

section MY13Manifold

open Set Filter Function Manifold Topology
open scoped ContDiff Manifold

-- 一般 `E` 上开集 `S` 的版本（hval / hchart / hder 对所有 target chart `p`）。
example {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
    {S : Set E} (hS : IsOpen S) {f : ℕ → E → M} {f₀ : E → M}
    (hf : ∀ᶠ n in atTop, MDifferentiableOn 𝓘(ℝ, E) 𝓘(ℝ, F) (f n) S)
    (hf₀ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) 1 f₀ S)
    (hinj : ∀ᶠ n in atTop, InjOn (f n) S)
    (hval : ∀ p : M, ∀ x ∈ S,
      f₀ x ∈ (extChartAt 𝓘(ℝ, F) p).source →
      Tendsto (fun n => extChartAt 𝓘(ℝ, F) p (f n x)) atTop
        (𝓝 (extChartAt 𝓘(ℝ, F) p (f₀ x))))
    (hchart : ∀ p : M, ∀ K : Set E, IsCompact K →
      K ⊆ S ∩ f₀ ⁻¹' (extChartAt 𝓘(ℝ, F) p).source →
      ∀ᶠ n in atTop, MapsTo (f n) K (extChartAt 𝓘(ℝ, F) p).source)
    (hder : ∀ p : M, ∀ K : Set E, IsCompact K →
      K ⊆ S ∩ f₀ ⁻¹' (extChartAt 𝓘(ℝ, F) p).source →
      TendstoUniformlyOn
        (fun n x => fderiv ℝ (fun z => extChartAt 𝓘(ℝ, F) p (f n z)) x)
        (fun x => fderiv ℝ (fun z => extChartAt 𝓘(ℝ, F) p (f₀ z)) x) atTop K)
    {a b : E} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (heq : f₀ a = f₀ b)
    (hsurj : Function.Surjective
      ((show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f₀ a).coprod
        (-(show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f₀ b)))) :
    False :=
  DifferentialGeometry.Topology.Manifold.not_surjective_coprod_mfderiv_of_injective_c1_limit
    hS hf hf₀ hinj hval hchart hder ha hb hab heq hsurj

end MY13Manifold

section Fold

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology Manifold ContDiff NNReal ENNReal ComplexConjugate

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

-- fold：两个 actual Morrey disk 的 distinct filling 在 seam 上 conormal 和为零（无 regular fold），
-- 且 filling 面积 = 原盘在 `e '' closedBall` 上的 patch 面积。
example
    (U : TopologicalSpace.Opens M)
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) U} {γ : freeLoop U} {u : C(closedDisk, U)}
    (hu : IsMorreyDisk g γ u) (d qAlt : C(closedDisk, U)) {L C CAlt : ℝ≥0}
    (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (hdLip : ∀ z w, riemannianEDistOf g (d z) (d w) ≤ (C : ℝ≥0∞) * edist z w)
    (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ 1)
    (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source)
    (hinside : e '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      diskExtension d z = diskExtension u (e z))
    (hqAlt : IsMorreyDisk g (diskTrace (diskThroughSourceChart u e hsrc)) qAlt)
    (hqAltLip : ∀ z w, riemannianEDistOf g (qAlt z) (qAlt w) ≤ (CAlt : ℝ≥0∞) * edist z w)
    (hSubSmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
      (fun t : ℝ => diskTrace (diskThroughSourceChart u e hsrc) (t : loopCircle)))
    (hSubImmersed : ∀ t : ℝ, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun s : ℝ => diskTrace (diskThroughSourceChart u e hsrc) (s : loopCircle)) t 1 ≠ 0)
    (hfillArea : riemannianDiskArea g d = riemannianDiskArea g qAlt)
    {W : Set U} (huW : Set.range u ⊆ W) (hdW : Set.range d ⊆ W)
    (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hχsrc : Metric.closedBall (0 : ℂ) 1 ⊆ χ.source)
    (hχinside : χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    {R : ℝ} (hR : 0 < R) (hRunit : R < 1)
    (hinner : MapsTo χ (closedHalfDisk 0 R) (e '' Metric.closedBall (0 : ℂ) 1))
    (houter : ∀ z ∈ closedHalfDisk 0 R,
      χ (conj z) ∉ interior (e '' Metric.closedBall (0 : ℂ) 1))
    (hFinner : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1
      (diskExtension d ∘ e.symm ∘ χ) (closedHalfDisk 0 R))
    (hiInner : ∀ z ∈ closedHalfDisk 0 R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ e.symm ∘ χ)
        (closedHalfDisk 0 R) z))
    (hiOuter : ∀ z ∈ closedHalfDisk 0 R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ χ ∘ conj)
        (closedHalfDisk 0 R) z))
    (ψAlt : ℂ → ℂ)
    (hψAlt : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψAlt (openHalfDisk 0 R))
    (hmapsAlt : MapsTo ψAlt (openHalfDisk 0 R) (Metric.ball (0 : ℂ) 1))
    (hbijAlt : ∀ z ∈ (openHalfDisk 0 R : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψAlt z))
    (heqAlt : EqOn (diskExtension d ∘ e.symm ∘ χ)
      (diskExtension qAlt ∘ ψAlt) (openHalfDisk 0 R))
    (hpW : diskExtension d (e.symm (χ 0)) ∈ interior W) :
    riemannianDiskArea g d =
      riemannianArea g (diskExtension u) (e '' Metric.closedBall (0 : ℂ) 1) ∧
    inwardConormalWithin g (diskExtension d ∘ e.symm ∘ χ) (closedHalfDisk 0 R) 0 +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension u ∘ χ ∘ conj) 0)
        ((diskExtension d ∘ e.symm ∘ χ) 0)
        (inwardConormalWithin g (diskExtension u ∘ χ ∘ conj) (closedHalfDisk 0 R) 0) = 0 :=
  IMS03Embeddedness.ConsumerAudit.actual_distinct_morrey_filling_has_no_regular_fold
    U hu d qAlt huLip hdLip e hsrc hinside hboundary hqAlt hqAltLip hSubSmooth hSubImmersed
    hfillArea huW hdW χ hχsrc hχinside hR hRunit hinner houter hFinner hiInner hiOuter ψAlt
    hψAlt hmapsAlt hbijAlt heqAlt hpW

end Fold

section Cone

open Set Metric MeasureTheory Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry
open scoped NNReal ENNReal Topology ContDiff Manifold Bundle

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] [T3Space M]

-- cone：periodic loop cone 的 pulled-back metric 面积 ≤ (A / (2 √m)) · R · length（原 coordinate 曲线长）。
example
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (φ : F → M) {U : Set F}
    (hU : IsOpen U) (hφ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 φ U)
    (p c : F) {a : ℝ → F} {K : ℝ≥0}
    (ha : Function.Periodic a 1) (hLip : LipschitzWith K a)
    {R ρ m A : ℝ} (hBU : closedBall c ρ ⊆ U)
    (hp : p ∈ closedBall c ρ) (haBall : ∀ t, a t ∈ closedBall c ρ)
    (hR : ∀ t, ‖a t - p‖ ≤ R) (hm : 0 < m) (hmA : m ≤ A)
    (hmetric : ∀ x ∈ closedBall c ρ, ∀ v : F,
      m * ‖v‖ ^ 2 ≤ g.inner (φ x)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) φ x v) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) φ x v) ∧
      g.inner (φ x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) φ x v)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) φ x v) ≤ A * ‖v‖ ^ 2) :
    riemannianDiskArea g (fun z : closedDisk => φ (periodicLoopCone p ha z)) ≤
      (A / (2 * Real.sqrt m)) * R * riemannianCurveLength g (φ ∘ a) 0 1 :=
  riemannianDiskArea_periodicLoopCone_le_radius_mul_length g φ hU hφ p c ha hLip hBU hp
    haBall hR hm hmA hmetric

end Cone

end

import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TransverseHalfDisk
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.GraphAreaStationarity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ReplacementSeamChart
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.LocalAreaMinimality
import DifferentialGeometry.Topology.Maps.TwoMapLocalCoincidentGerms
import DifferentialGeometry.Topology.Manifold.OpenPartialHomeomorph.InverseRegularity

/-!
# S-MY-PORT-B2 G2 consumer：MY 支撑包的「其余根」（无 B1 依赖的一半）

G2 = `TransverseHalfDisk`、`GraphAreaStationarity`、`ReplacementSeamChart`、`LocalAreaMinimality`、
`TwoMapLocalCoincidentGerms`、`InverseRegularity`（IMS03 tip `66cbb8d61` 的逐字节拷贝）。

* 六个 `example := @…`：对六个根定理做逐字型检查（陈述与 IMS03 完全一致）。
* `transverse_pair_segment_B2`：Morrey 盘上横截的两点 `a ≠ b`（`heq`，两处 immersion、
  `coprod` surjective）⇒ 两个 half-disk chart `ψ₁ ψ₂`，targets 不交、都在开单位盘内，
  且沿共同线段 `diskExtension u (ψ₁ t) = diskExtension u (ψ₂ t)`（MY-11/12 的 smooth engine 入口）。
* `morrey_area_not_lt_of_eqOn_sphere_B2`：Lipschitz Morrey 盘在内部球上不被同 sphere trace 的
  Lipschitz competitor 严格压低面积。
* `isOpen_coincident_domain_B2`：两个 locally injective 连续映射的 coincident-germ 定义域是开集
  （`isOpen_fst_image_twoMapCoincidentGerms` 的集合形式）。
不加任何新前提，所有假设逐字取自 IMS03 定理。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold MeasureTheory Metric DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace GC.LongTime.CuspP1

/-- 逐字型检查：transverse paired half-disk charts（MY 的 collision-arc 入口）。 -/
example := @DifferentialGeometry.Geometry.morrey_transverse_paired_halfdisk_flux

/-- 逐字型检查：closed factor 的 graph 面积弱 stationarity。 -/
example := @DifferentialGeometry.Geometry.IsMorreyDisk.closed_factor_graph_weak_stationarity

/-- 逐字型检查：replacement seam 的 regular half-disk chart。 -/
example := @DifferentialGeometry.Geometry.exists_regular_replacement_seam_chart

/-- 逐字型检查：球上 Lipschitz 面积 minimality。 -/
example := @DifferentialGeometry.Geometry.IsMorreyDisk.area_closedBall_le_of_eqOn_sphere

/-- 逐字型检查：两映射 coincident germs 的第一投影是开集。 -/
example := @DifferentialGeometry.Topology.isOpen_fst_image_twoMapCoincidentGerms

/-- 逐字型检查：invertible `mfderiv` 的 open partial homeomorphism 逆映射正则性。 -/
example :=
  @DifferentialGeometry.Topology.OpenPartialHomeomorph.contMDiffOn_symm_of_isInvertible_mfderiv

/-- Morrey 盘上两个横截的 immersed 点给出两个不交 half-disk chart，沿共同线段像点重合。 -/
theorem transverse_pair_segment_B2
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (hdim : Module.finrank ℝ E = 3) {a b : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) (hb : b ∈ Metric.ball (0 : ℂ) 1)
    (hab : a ≠ b) (heq : diskExtension u a = diskExtension u b)
    (hia : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) a))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) b))
    (htrans : Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) a).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) b)))) :
    ∃ (r : ℝ) (ψ₁ ψ₂ : OpenPartialHomeomorph ℂ ℂ),
      0 < r ∧ ψ₁ 0 = a ∧ ψ₂ 0 = b ∧ Disjoint ψ₁.target ψ₂.target ∧
      ∀ t ∈ Icc (-2 * r) (2 * r),
        diskExtension u (ψ₁ (t : ℂ)) = diskExtension u (ψ₂ (t : ℂ)) := by
  obtain ⟨r, ψ₁, ψ₂, hr, h1, h2, -, -, -, hdisj, hseg, -⟩ :=
    morrey_transverse_paired_halfdisk_flux hu hdim ha hb hab heq hia hib htrans
  exact ⟨r, ψ₁, ψ₂, hr, h1, h2, hdisj, hseg⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Lipschitz Morrey 盘在内部球上不会被同 sphere trace 的 Lipschitz competitor 严格压低面积。 -/
theorem morrey_area_not_lt_of_eqOn_sphere_B2
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u) {K : ℝ≥0}
    (huLip : ∀ z z', riemannianEDistOf g (u z) (u z') ≤
      (K : ℝ≥0∞) * edist z z')
    {v : ℂ → M} {L : ℝ≥0}
    {b : ℂ} {r : ℝ} (hbr : ‖b‖ + r < 1)
    (hv : ∀ z ∈ closedBall b r, ∀ z' ∈ closedBall b r,
      riemannianEDistOf g (v z) (v z') ≤ (L : ℝ≥0∞) * edist z z')
    (heq : ∀ z ∈ sphere b r, v z = diskExtension u z) :
    ¬ riemannianArea g v (closedBall b r) < riemannianArea g (diskExtension u) (closedBall b r) :=
  not_lt_of_ge (hu.area_closedBall_le_of_eqOn_sphere huLip hbr hv heq)

/-- 两个 locally injective 连续映射的 coincident-germ 定义域是开集。 -/
theorem isOpen_coincident_domain_B2
    {X Y Z : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [LocallyCompactSpace Y]
    [TopologicalSpace Z] [T2Space Z]
    {f : X → Z} {g : Y → Z} (hf : Continuous f) (hg : Continuous g)
    (hlocf : IsLocallyInjective f) (hlocg : IsLocallyInjective g) :
    IsOpen {x : X | ∃ y : Y, f x = g y ∧ Filter.map f (𝓝 x) = Filter.map g (𝓝 y)} := by
  have h := isOpen_fst_image_twoMapCoincidentGerms hf hg hlocf hlocg
  convert h using 1
  ext x
  constructor
  · rintro ⟨y, hxy, hmap⟩
    exact ⟨(x, y), ⟨hxy, hmap⟩, rfl⟩
  · rintro ⟨⟨x', y⟩, ⟨hxy, hmap⟩, rfl⟩
    exact ⟨y, hxy, hmap⟩

end GC.LongTime.CuspP1

import DifferentialGeometry.Geometry.MinimalSurface.MorreyLeastAreaSmoothAT
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskCriterion
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricLocality_GB

/-!
# O-MY-R7E G1：minimality transport（completion metric `Ĝ` → 原度量 `G`）

R7-E（D-R-MY2-11，R-MY3 定稿）：`u` 对 completion metric `Ĝ` 是 Morrey 盘、像落在 `Ĝ = G` 的 core `C₀`；
若每个 `G`-Lipschitz、trace 类 `Γ` 的 competitor `v` 都有一个 `Ĝ`-Lipschitz、同 trace 类、像在 `C₀`、
`A_G(w) ≤ A_G(v)` 的替身 `w`（G3 的 collar level projection 给 `w = r_c ∘ v`），则

`A_G(u) = A_Ĝ(u) ≤ A_Ĝ(w) = A_G(w) ≤ A_G(v)`。

两个等号用 `riemannianDiskArea_congr_inner_AT`（面积只依赖度量在 range 上的取值）。

* `minimality_transport_of_completion_R7E`：上面的链（scratch `MYD3/R06R07.lean:127` 的 [PF] 合同，
  把 `r ∘ v` 推广成存在量词 `w`，见 R-MY3 对 G3 的 generic level 偏差）。
* `minimality_transport_of_retraction_R7E`：scratch 原形（单个 `r : C(M, M)`）作推论。
* `isMorreyDisk_of_completion_R7E`：R-MY3 (3) jets——`Ĝ = G` 在每个 `u z` 的**邻域**上（germ），
  加上上面的 transport 假设 ⇒ `u` 是**原** `G` 的 Morrey 盘（smoothInterior / conformal / harmonic /
  finiteEnergy / trace 逐项搬运，minimality 用 transport 链）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **G1**（R7-E-3，[PF]）：minimality transport。`u` 是 `Ĝ`-Morrey 盘、像在 `C₀`、`Ĝ = G` on `C₀`，
每个 `G`-Lipschitz 同 trace 类 competitor `v` 有像在 `C₀` 的 `Ĝ`-Lipschitz 同 trace 类替身 `w`，
`A_G(w) ≤ A_G(v)` ⇒ `A_G(u) ≤ A_G(v)`。 -/
theorem minimality_transport_of_completion_R7E (G Ghat : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {C₀ : Set M} (hagree : ∀ x ∈ C₀, Ghat.inner x = G.inner x) {Γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk Ghat Γ u) (huC : Set.range u ⊆ C₀)
    (hcomp : ∀ v : C(closedDisk, M), DiskWeakJordanTrace Γ v →
      (∃ L : ℝ≥0, ∀ z w, riemannianEDistOf G (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) →
      ∃ w : C(closedDisk, M), Set.range w ⊆ C₀ ∧ DiskWeakJordanTrace Γ w ∧
        (∃ L : ℝ≥0, ∀ z z', riemannianEDistOf Ghat (w z) (w z') ≤ (L : ℝ≥0∞) * edist z z') ∧
        riemannianDiskArea G w ≤ riemannianDiskArea G v)
    (v : C(closedDisk, M)) (hv : DiskWeakJordanTrace Γ v)
    (hvL : ∃ L : ℝ≥0, ∀ z w, riemannianEDistOf G (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) :
    riemannianDiskArea G u ≤ riemannianDiskArea G v := by
  obtain ⟨w, hwC, hwt, hwL, hwA⟩ := hcomp v hv hvL
  have h1 : riemannianDiskArea G u = riemannianDiskArea Ghat u :=
    riemannianDiskArea_congr_inner_AT fun z => (hagree _ (huC ⟨z, rfl⟩)).symm
  have h2 : riemannianDiskArea Ghat w = riemannianDiskArea G w :=
    riemannianDiskArea_congr_inner_AT fun z => hagree _ (hwC ⟨z, rfl⟩)
  calc riemannianDiskArea G u = riemannianDiskArea Ghat u := h1
    _ ≤ riemannianDiskArea Ghat w := hu.minimizesLipschitz _ hwt hwL
    _ = riemannianDiskArea G w := h2
    _ ≤ riemannianDiskArea G v := hwA

/-- scratch 原形（`MYD3/R06R07.lean:127`）：单个 retraction `r` 的版本，作为 G1 的推论。 -/
theorem minimality_transport_of_retraction_R7E (G Ghat : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {C₀ : Set M} (hagree : ∀ x ∈ C₀, Ghat.inner x = G.inner x) {Γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk Ghat Γ u) (huC : Set.range u ⊆ C₀)
    (r : C(M, M))
    (hr : ∀ v : C(closedDisk, M), DiskWeakJordanTrace Γ v →
        (∃ L : ℝ≥0, ∀ z w, riemannianEDistOf G (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) →
        Set.range (r.comp v) ⊆ C₀ ∧ DiskWeakJordanTrace Γ (r.comp v) ∧
        (∃ L : ℝ≥0, ∀ z w,
          riemannianEDistOf Ghat (r.comp v z) (r.comp v w) ≤ (L : ℝ≥0∞) * edist z w) ∧
        riemannianDiskArea G (r.comp v) ≤ riemannianDiskArea G v) :
    ∀ v : C(closedDisk, M), DiskWeakJordanTrace Γ v →
      (∃ L : ℝ≥0, ∀ z w, riemannianEDistOf G (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) →
      riemannianDiskArea G u ≤ riemannianDiskArea G v :=
  minimality_transport_of_completion_R7E G Ghat hagree hu huC
    (fun v hv hvL => ⟨r.comp v, hr v hv hvL⟩)

/-- **G1 + jets**（R-MY3 (3)）：`Ĝ = G` 在每个 `u z` 的邻域上（germ）+ transport 假设 ⇒ `u` 是原 `G`
的 Morrey 盘。conformal / energy 只用 `u z` 处的度量，harmonic 用 `u z` 邻域上的度量
（`diskMapTension_congr_of_metric_eventuallyEq_GB`）。 -/
theorem isMorreyDisk_of_completion_R7E (G Ghat : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {C₀ : Set M} (hagree : ∀ x ∈ C₀, Ghat.inner x = G.inner x) {Γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk Ghat Γ u) (huC : Set.range u ⊆ C₀)
    (hgerm : ∀ z : closedDisk, ∀ᶠ y in 𝓝 (u z), Ghat.inner y = G.inner y)
    (hcomp : ∀ v : C(closedDisk, M), DiskWeakJordanTrace Γ v →
      (∃ L : ℝ≥0, ∀ z w, riemannianEDistOf G (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) →
      ∃ w : C(closedDisk, M), Set.range w ⊆ C₀ ∧ DiskWeakJordanTrace Γ w ∧
        (∃ L : ℝ≥0, ∀ z z', riemannianEDistOf Ghat (w z) (w z') ≤ (L : ℝ≥0∞) * edist z z') ∧
        riemannianDiskArea G w ≤ riemannianDiskArea G v) :
    IsMorreyDisk G Γ u := by
  have hpt : ∀ z : ℂ, ∀ v w : TangentSpace 𝓘(ℝ, E) (diskExtension u z),
      Ghat.inner (diskExtension u z) v w = G.inner (diskExtension u z) v w := by
    intro z v w
    have h := (hgerm (diskRetraction z)).self_of_nhds
    change Ghat.inner (u (diskRetraction z)) v w = G.inner (u (diskRetraction z)) v w
    rw [h]
  have hnhds : ∀ z : ℂ, ∀ᶠ y in 𝓝 (diskExtension u z), ∀ v w : TangentSpace 𝓘(ℝ, E) y,
      Ghat.inner y v w = G.inner y v w := by
    intro z
    filter_upwards [hgerm (diskRetraction z)] with y hy v w
    rw [hy]
  have henergy : diskMapEnergyDensity Ghat (diskExtension u) =
      diskMapEnergyDensity G (diskExtension u) := by
    funext z
    unfold diskMapEnergyDensity
    rw [hpt z, hpt z]
  refine isMorreyDisk_of_minimizesLipschitz G hu.smoothInterior ?_ ?_ ?_ hu.trace ?_
  · intro z hz
    exact (diskMapConformalAt_congr_of_metric_GB Ghat G (hpt z)).mp (hu.conformal z hz)
  · intro z hz
    rw [← diskMapTension_congr_of_metric_eventuallyEq_GB Ghat G (hnhds z)]
    exact hu.harmonic z hz
  · rw [← henergy]
    exact hu.finiteEnergy
  · exact minimality_transport_of_completion_R7E G Ghat hagree hu huC hcomp

end DifferentialGeometry.Geometry

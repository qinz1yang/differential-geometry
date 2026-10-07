import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# 开集上等维 smooth embedding ⇒ `PartialDiffeomorph`（S-HG-ADAPT G2，后缀 `_HGA`）

`partialDiffeomorph_of_open_smooth_embedding_HGA`：设 `I` 无边界、`E` 有限维，`U ⊆ M` 开，
`f : M → N` 在 `U` 上 `C^∞`，且限制 `fun x : U => f x` 是 `C^∞` smooth embedding（立即 = 单射 immersion）。
则存在 `C^∞` partial diffeomorphism `Φ`：`Φ.source = U`、`Φ.target = f '' U`、`⇑Φ = f`。

证明走已有的三块：
* `IsImmersionAt.mfderiv_injective` + `mfderiv_restrict_open` ⇒ `mfderiv I I f y` 单射；
  `E` 有限维 ⇒ 双射 ⇒ `fderiv (writtenInExtChartAt …)` 可逆；
* `contMDiffOn_isLocalDiffeomorphOn_infty` ⇒ `IsLocalDiffeomorphOn I I ∞ f U`；
* `exists_partialDiffeomorph_of_injOn`（`U` 上单射由 embedding 的单射性给出）。

这就是 ch12 的 `hHG06` 里 "`IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x)`" 到 donor
`isMetricApproximationOnBall`（要 `PartialDiffeomorph`）之间的 G2 缺口；没有新增任何前提。
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-- 单射的 `E →L[ℝ] E`（`E` 有限维）可逆。 -/
private theorem isInvertible_of_injective_HGA {T : E →L[ℝ] E}
    (hT : Function.Injective T) : T.IsInvertible := by
  have hs : Function.Surjective T := LinearMap.injective_iff_surjective.mp hT
  exact ⟨ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.mpr hT)
    (LinearMap.range_eq_top.mpr hs), rfl⟩

/-- **开集上等维 smooth embedding ⇒ `PartialDiffeomorph`（G2）。** -/
theorem partialDiffeomorph_of_open_smooth_embedding_HGA [Nonempty M]
    (U : Opens M) (f : M → N) (hf : ContMDiffOn I I ∞ f U)
    (hemb : _root_.Manifold.IsSmoothEmbedding I I ∞ (fun x : U => f x)) :
    ∃ Φ : PartialDiffeomorph I I M N ∞,
      Φ.source = (U : Set M) ∧ Φ.target = f '' (U : Set M) ∧ (Φ : M → N) = f := by
  have hinj : InjOn f (U : Set M) := fun x hx y hy hxy =>
    congrArg Subtype.val (hemb.isEmbedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hinv : ∀ y ∈ (U : Set M),
      (fderiv ℝ (writtenInExtChartAt I I y f) (extChartAt I y y)).IsInvertible := by
    intro y hy
    have hmd : MDifferentiableAt I I f y :=
      (hf.contMDiffAt (U.isOpen.mem_nhds hy)).mdifferentiableAt (by decide)
    have hinjm : Function.Injective (mfderiv I I f y) := by
      have h1 := (hemb.isImmersion.isImmersionAt ⟨y, hy⟩).mfderiv_injective (by decide)
      rwa [DifferentialGeometry.mfderiv_restrict_open] at h1
    have hder : fderiv ℝ (writtenInExtChartAt I I y f) (extChartAt I y y) = mfderiv I I f y := by
      rw [hmd.mfderiv_abuse, I.range_eq_univ, fderivWithin_univ]
    rw [hder]
    exact isInvertible_of_injective_HGA hinjm
  exact exists_partialDiffeomorph_of_injOn U.isOpen
    (DifferentialGeometry.Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty U.isOpen hf hinv)
    hinj

end DifferentialGeometry.Topology.Manifold

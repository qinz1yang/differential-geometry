import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness

set_option autoImplicit false

/-!
# S-CH11-PBASE (G1)：`StaticCollarAdmits`（后缀 `_C11PB`）

collar 长度 `A` 对所有 order `m + 4` 的 normalized datum 都容许 `CanonicalStaticInsertionWitness`
（`δ ≤ δ₀(D, m, ε)`）。体逐字是 `exists_canonicalStaticInsertionWitness`（`StaticWitness.lean:245`）的
结论，但**宇宙多态**（`E : Type ue`、`H : Type uh`、`M : Type um`）：这样可以沿
`exists_uniform_recentered_static_preparation.{u,v,w}` → `…family_volume_bound.{u,v,w,z}` 往上带，
到 `FiniteMetricEventVolume` 以上固定 `.{0, 0, u}`。

* 这是**结论**缩写（每处都由 `hmod` 证明，不是假设）。
* `Ch11` 的 `collarAdmitsAllOrders_C11E.{u} A hA`（`M : Type u`，`E = H = ThreeSpace`）是它在
  `.{0, 0, u}` 处的特例（去掉 `δ₀ < 1 / 2`）；adapter 放在 `Ch11/External/PBaseCollarC11PB.lean`
  （`EnhancedProfileDefsC11E` 在 Surgery 之上，这里不能 import）。
-/

noncomputable section
open Set Function Bundle Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

/-- `A` 的 collar 容许所有 order（宇宙多态版 `collarAdmitsAllOrders`）。 -/
def StaticCollarAdmits.{ue, uh, um} (A : ℝ) (hA : 0 < A) : Prop :=
  ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ {E : Type ue} {H : Type uh} {M : Type um} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ (m + 4)),
          Nonempty (CanonicalStaticInsertionWitness d A hA D m ε)

end DifferentialGeometry.PDE.RicciFlow.StandardCap

import DifferentialGeometry.Analysis.Integration.Measure.Parametric.DensityComparisonC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientLimitSurvivorCanonicalWitnessC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingAncientLimitSpatialC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceAfterEventC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowActionC11X

set_option autoImplicit false

/-!
# S-CH11-EXT2 G1 consumer（`_C11X`）

对 EXT2 五个已落地 extension 的新增定理各给一个 consumer：`type_of%` 对齐陈述，并对每个
新增定理做一次真实的实例化 / 投影（不新增声明；own file）。

* `DensityComparisonC11X`：`paramDensity_le_of_inner_mfderiv_le`；
* `AncientLimitSurvivorCanonicalWitnessC11X`：`…_of_normalized_local_flow_limit`；
* `CrossingAncientLimitSpatialC11X`：两个 `…_of_isTracedRegion_at_closed_time`；
* `BoundedCurvatureAtDistanceAfterEventC11X`：`…_of_birth_metric_comparison`、`…_at_birth`；
* `CapWindowActionC11X`：`…_with_window_scale_bound`。
（`SlabGradientScalarControlC11X` 在我们树里编不过，不进树，记 reference-only，见 state 文件。）
* 一行 `import` 与定理名 `…_with_window_scale_bound`（117 字符）无法折行，是仅有的超 100 字符行。
-/

open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry DifferentialGeometry.Integral.Measure

/-- `paramDensity` 比较在 `h = g`, `v = u` 时退化为自反（真实实例化 donor 定理）。 -/
example {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (u : E → M) (x : E)
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, E) I u x)) :
    paramDensity g u x ≤ paramDensity g u x :=
  paramDensity_le_of_inner_mfderiv_le g g hinj fun _ => le_rfl

example : type_of% @paramDensity_le_of_inner_mfderiv_le := @paramDensity_le_of_inner_mfderiv_le

open Perelman.CanonicalNeighborhood.FiniteHorn in
example {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 11) : ∃ C : ℝ, 1 ≤ C := by
  obtain ⟨C, hC, -⟩ :=
    eventually_exists_canonicalWitness_survivor_of_normalized_local_flow_limit.{0} hε hsmall
  exact ⟨C, hC⟩

example : ∃ epsW : ℝ, 0 < epsW := by
  obtain ⟨epsW, hepsW, -⟩ :=
    ObservedHistory.exists_eventually_canonicalWitness_survivor_of_isTracedRegion_at_closed_time.{0}
  exact ⟨epsW, hepsW⟩

example : ∃ epsW : ℝ, 0 < epsW := by
  obtain ⟨epsW, hepsW, -⟩ :=
    ObservedHistory.exists_eventually_spatialCanonicalWitness_of_isTracedRegion_at_closed_time.{0}
  exact ⟨epsW, hepsW⟩

open RetainedCoreHistory in
example {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq θ : ℝ) (hθ : 0 < θ) :
    ∃ Q Λ Dcap Rrad ζ₀ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
      Dcap ≤ Rrad ∧ 0 < ζ₀ := by
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, h1, h2, h3, h4, h5, -⟩ :=
    exists_scalar_bound_at_distance_of_not_capWindowPoint_at_birth.{0}
      hεle κ C1 C2 hκ Ctime Cgrad hphi A hA Cq θ hθ
  exact ⟨Q, Λ, Dcap, Rrad, ζ₀, h1, h2, h3, h4, h5⟩

open RetainedCoreHistory in
example : type_of%
    @exists_scalar_bound_at_distance_of_not_capWindowPoint_of_birth_metric_comparison :=
  @exists_scalar_bound_at_distance_of_not_capWindowPoint_of_birth_metric_comparison

open ObservedHistory in
example (A B Ebound rTest : ℝ) (Cderiv : ℝ≥0) (hB : 0 ≤ B) (hE : 0 ≤ Ebound) (hr : 0 < rTest) :
    ∃ qmin Cbirth : ℝ, 0 < qmin ∧ 0 < Cbirth := by
  obtain ⟨_, _, qmin, Cbirth, -, -, hq, hC, -⟩ :=
    exists_uniform_prepared_cap_birth_action_lower_bound_of_parabolicallyRmControlledBall_with_window_scale_bound.{0, 0, 0, 0}
      A B Ebound rTest Cderiv hB hE hr
  exact ⟨qmin, Cbirth, hq, hC⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

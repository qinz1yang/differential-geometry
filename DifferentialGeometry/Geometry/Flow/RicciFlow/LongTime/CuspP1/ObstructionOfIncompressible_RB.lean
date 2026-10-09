import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateDecomposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTopAssemblyV6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.WR.A09OfEnhancedC11M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.WR.A13OfEnhancedC11M

/-!
# S-A11-ROUTEB G3′（Route W 的 obstruction plumbing）

`hasAttainedExteriorAreaObstructionAfter F D`（`LateDecomposition.lean:53`）的右边 ∃ 在
`not_nonnegative_area_upper_barriers_pi_shift` 下蕴含 `False`，所以整个 Prop 等价于
`∀ i x, Injective (π₁ torusInPrime)`（`Incompressible`）。下游
`incompressible_of_shifted_area_barriers`（`CuspIncompressibility.lean:13`）只消费 `A ≥ 0`、
`ContinuousOn A`、barriers，embeddedness / 导数单射 / positivity 都没有用到。

这里把这条链拆成四个小定理，使 Route W 可以用 **Morrey（parametrized）disk class** 的面积 `A′`
证 incompressibility，再以 `absurd` 供给 obstruction Prop：

* (a) `hasAttainedExteriorAreaObstructionAfter_of_injective_RB`：`Injective` ⇒ obstruction Prop
  （`absurd`）。
* (b) `injective_of_morrey_obstruction_RB`：`¬Injective → ∃ T c A, …` ⇒ `Injective`
  （对任意连续映射 `φ : C(X, Y)` 的 `π₁`，不限于 torus）。
* (c) `hasAttainedExteriorAreaObstructionAfter_of_morrey_chain_RB`：对 `L j C`，把 (b) 的
  ∃-假设作为显式 ∀-参数，结论 `hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C)`。
* (d) `…_of_morrey_chain_top_RB`：用 `exists_primitive_meridian_top_CPA3` 产出 Top 对象 `M₀`，
  ∃-假设以 `M₀ : PrescribedCuspMeridianTop_CPQ L.cores` 为输入
  （接 `exists_eventual_confined_morrey_disk_HC`）。

consumer：`hasLateSequenceTests_of_thick_thin_and_morrey_chain_RB` 是
`hasLateSequenceTests_of_thick_thin_and_obstruction` 证明体的拷贝，只把
`hasExteriorAreaObstructionAfter_of_producers` 一行换成 (d)。
本文件只 import 已跟踪模块，无 sorry、无 `P2AdapterImported*` 依赖，可登记。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Analysis
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.Endpoint GC.Topology GC.LongTime Set
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1

universe u

/-- (a) 所有 torus 的 `π₁` 单射 ⇒ `hasAttainedExteriorAreaObstructionAfter`
（前提 `¬Injective` 矛盾，`absurd`）。 -/
theorem hasAttainedExteriorAreaObstructionAfter_of_injective_RB
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    {M : ConnectedClosedOrientedManifold.{u} 3} (D : TorusDecomposition M)
    (hinj : ∀ i : Fin D.boundary.count, ∀ x : GC.Endpoint.Torus,
      Function.Injective
        (FundamentalGroup.map (D.reconstructionAtlas.torusInPrime D.reconstruction i) x)) :
    hasAttainedExteriorAreaObstructionAfter F D :=
  fun i x hn => absurd (hinj i x) hn

/-- (b) Morrey 面积的 shifted upper barrier 排除非单射：`¬Injective → ∃ T c A, 0 ≤ T ∧ 0 < c ∧
ContinuousOn A ∧ 0 ≤ A ∧ barriers` ⇒ `Injective`。`A` 可以是任意非负连续函数（Route W 取
Morrey least area `A′`），不要求最小盘嵌入。 -/
theorem injective_of_morrey_obstruction_RB {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : C(X, Y)) (x : X)
    (harea : ¬ Function.Injective (FundamentalGroup.map φ x) →
      ∃ (T c : ℝ) (A : ℝ → ℝ), 0 ≤ T ∧ 0 < c ∧
        ContinuousOn A (Ici T) ∧ (∀ t ∈ Ici T, 0 ≤ A t) ∧
        (∀ t ∈ Ici T, hasLocalSmoothUpperBarrier A (Ici T) t
          (3 * A t / (4 * (t + c)) - Real.pi))) :
    Function.Injective (FundamentalGroup.map φ x) := by
  by_contra h
  obtain ⟨T, c, A, hT, hc, hcont, hn, hb⟩ := harea h
  exact not_nonnegative_area_upper_barriers_pi_shift A T c (by linarith) hcont hn hb

/-- (c) 对 `L j C`：若每个非单射的 `(s, x)` 都有 Morrey 面积 barrier 数据，则
`hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C)`。这是 Route W 里将来替换
`hasExteriorAreaObstructionAfter_of_producers` 的目标形状。 -/
theorem hasAttainedExteriorAreaObstructionAfter_of_morrey_chain_RB
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices) (j : ℕ)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (hmorrey : ∀ (s : Fin (L.decomposition j C).boundary.count) (x : GC.Endpoint.Torus),
      ¬ Function.Injective (FundamentalGroup.map
        ((L.decomposition j C).reconstructionAtlas.torusInPrime
          (L.decomposition j C).reconstruction s) x) →
      ∃ (T c : ℝ) (A : ℝ → ℝ), 0 ≤ T ∧ 0 < c ∧
        ContinuousOn A (Ici T) ∧ (∀ t ∈ Ici T, 0 ≤ A t) ∧
        (∀ t ∈ Ici T, hasLocalSmoothUpperBarrier A (Ici T) t
          (3 * A t / (4 * (t + c)) - Real.pi))) :
    hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C) :=
  hasAttainedExteriorAreaObstructionAfter_of_injective_RB F (L.decomposition j C)
    fun s x => injective_of_morrey_obstruction_RB _ x (hmorrey s x)

/-- (d) Top 版本：非单射 ⇒ Top meridian `M₀`（`exists_primitive_meridian_top_CPA3`），
Morrey 面积数据的假设以 Top 对象 `M₀ : PrescribedCuspMeridianTop_CPQ L.cores` 为输入（供 `_HC` 接入）。 -/
theorem hasAttainedExteriorAreaObstructionAfter_of_morrey_chain_top_RB
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (hmorrey : PrescribedCuspMeridianTop_CPQ L.cores →
      ∃ (T c : ℝ) (A : ℝ → ℝ), 0 ≤ T ∧ 0 < c ∧
        ContinuousOn A (Ici T) ∧ (∀ t ∈ Ici T, 0 ≤ A t) ∧
        (∀ t ∈ Ici T, hasLocalSmoothUpperBarrier A (Ici T) t
          (3 * A t / (4 * (t + c)) - Real.pi))) :
    hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C) :=
  hasAttainedExteriorAreaObstructionAfter_of_morrey_chain_RB L j C fun s x hcomp => by
    obtain ⟨M₀⟩ := exists_primitive_meridian_top_CPA3 K hK δ hadm hdec L j hj C s x hcomp
    exact hmorrey M₀

/-- consumer：`hasLateSequenceTests_of_thick_thin_and_obstruction` 的证明体，只把
`hasExteriorAreaObstructionAfter_of_producers` 一行换成 (d)（Route W 的 re-point 目标）。 -/
theorem hasLateSequenceTests_of_thick_thin_and_morrey_chain_RB
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (henh : Ch11.hasEnhancedAdmissibilityFull_C11F F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hmorrey : ∀ {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices),
      PrescribedCuspMeridianTop_CPQ L.cores →
      ∃ (T c : ℝ) (A : ℝ → ℝ), 0 ≤ T ∧ 0 < c ∧
        ContinuousOn A (Ici T) ∧ (∀ t ∈ Ici T, 0 ≤ A t) ∧
        (∀ t ∈ Ici T, hasLocalSmoothUpperBarrier A (Ici T) t
          (3 * A t / (4 * (t + c)) - Real.pi))) :
    hasLateSequenceTests F K := by
  have hadm : hasAnalyticAdmissibility F δ := Ch11.hasAnalyticAdmissibility_of_full_C11F henh
  intro slices htimes hnonempty
  obtain ⟨L⟩ := Ch11.exists_late_cut_family_of_enhanced_C11M F K hK δ henh hdec slices htimes
    hnonempty
  obtain ⟨A, hA, htests⟩ := L.exists_late_tests_of_derivative_bounds
    (Ch11.late_derivative_tests_of_flow_of_enhanced_C11M F K hK δ henh hdec slices htimes
      hnonempty L)
  refine ⟨A, hA, ?_⟩
  intro w hw hc
  obtain ⟨N, hn⟩ := htests w hw hc
  refine ⟨max N L.first, ?_⟩
  intro j hj C
  exact ⟨L.decomposition j C, hn j ((le_max_left _ _).trans hj) C,
    hasAttainedExteriorAreaObstructionAfter_of_morrey_chain_top_RB K hK δ hadm hdec L j
      ((le_max_right _ _).trans hj) C (hmorrey L)⟩

end GC.LongTime.CuspP1

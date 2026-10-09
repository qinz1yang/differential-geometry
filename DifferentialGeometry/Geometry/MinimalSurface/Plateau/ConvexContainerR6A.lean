import DifferentialGeometry.Geometry.Operator.Hessian.Positivity
import DifferentialGeometry.Topology.Ehresmann.SideBoundaryInterval

/-!
# S-MY-R6A：外审 Lemma R6 的光滑半边 R6a（`strictly_convex_container`；无 analytic）

一般 smooth manifold `M`（model `𝓘(ℝ, E)`，`E` 有限维，`M` T2）、光滑 `ρ : M → ℝ`、`a > 0`、
`IsCompact (closure {ρ < a})`、`hcvx`（`_HC2` 形：`{0 ≤ ρ < a}` 上 `dρ ≠ 0` 且**全** Hessian 正定）。

* `isOpen_convexGood_R6A`：「`dρ ≠ 0 ∧ Hess ρ > 0`」是开条件（`x ↦ mfderiv ρ x` 的满射性开 +
  `isOpen_hessFun_gt_mul_inner`）。**不**搬 ims03 `StrictLevelBarrier`：全 Hessian 正定直接是开条件。
* `exists_convex_collar_R6A`：`{ρ = 0}` 紧（⊆ `closure {ρ < a}`）+ 开条件 ⇒ `∃ ε₀ > 0`，
  「good」延伸到 `{−ε₀ < ρ < a}`。
* `exists_convex_container_R6A`（G1 一般版）：紧 `S ⊆ {ρ < 0}` ⇒ `∃ b δ > 0`，`S ⊆ {ρ < −b−δ}`，
  good 在 `{−b−δ ≤ ρ < a}` 上，`K := {ρ ≤ −b}` 紧、`K ⊆ {ρ < a}`、`frontier K ⊆ {ρ = −b}`。
* `strictly_convex_container_R6A`：design 合同 `strictly_convex_container_MYD2`
  （scratch `build-logs/scratch/O-MY-DESIGN/contracts/MYD2/R06to08.lean:59`）的**逐字**形：
  `S` 再取预连通，`K` 取 `{ρ ≤ −b}` 含 `S` 的连通分量，`S ⊆ interior K`、`IsCompact K`、
  `frontier K ⊆ {ρ = −b}`，整段水平层 `[−b−δ, −b]` 严格凸。

不要求 `ρ`、`∂K` analytic（D-R-MY1-9）。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

/-! ## Part A：拓扑零件 -/

section Topological

/-- 紧集上取负值的连续函数有统一负上界。 -/
theorem exists_neg_bound_of_isCompact_R6A {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) {S : Set X} (hS : IsCompact S) (hneg : ∀ x ∈ S, f x < 0) :
    ∃ c : ℝ, c < 0 ∧ ∀ x ∈ S, f x ≤ c := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨-1, by norm_num, fun x hx => absurd hx (notMem_empty x)⟩
  · obtain ⟨x₀, hx₀, hmax⟩ := hS.exists_isMaxOn hne hf.continuousOn
    exact ⟨f x₀, hneg x₀ hx₀, fun x hx => isMaxOn_iff.mp hmax x hx⟩

variable {X : Type*} [TopologicalSpace X]

/-- 闭集 `F` 里 `x₀` 的连通分量 `connectedComponentIn F x₀` 仍是闭集
（闭包预连通且仍在 `F` 里）。 -/
theorem isClosed_connectedComponentIn_R6A {F : Set X} (hF : IsClosed F) (x₀ : X) :
    IsClosed (connectedComponentIn F x₀) := by
  by_cases hx : x₀ ∈ F
  · refine closure_subset_iff_isClosed.mp ?_
    have hpre : IsPreconnected (closure (connectedComponentIn F x₀)) :=
      (isPreconnected_connectedComponentIn (x := x₀) (F := F)).closure
    have hsub : closure (connectedComponentIn F x₀) ⊆ F :=
      closure_minimal (connectedComponentIn_subset F x₀) hF
    exact hpre.subset_connectedComponentIn (subset_closure (mem_connectedComponentIn hx)) hsub
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-- 局部连通空间：`F ⊇ W`（`W` 开）里 `x₀` 的连通分量 `D` 与 `W` 的交落在 `interior D` 里
（`y ∈ D ∩ W` 的 `W`-连通分量是开集，且含于 `y` 的 `F`-连通分量 `= D`）。 -/
theorem inter_subset_interior_connectedComponentIn_R6A [LocallyConnectedSpace X] {F W : Set X}
    (hW : IsOpen W) (hWF : W ⊆ F) (x₀ : X) :
    connectedComponentIn F x₀ ∩ W ⊆ interior (connectedComponentIn F x₀) := by
  rintro y ⟨hyD, hyW⟩
  have hopen : IsOpen (connectedComponentIn W y) := hW.connectedComponentIn
  have hsub : connectedComponentIn W y ⊆ connectedComponentIn F x₀ := by
    rw [connectedComponentIn_eq hyD]
    exact connectedComponentIn_mono y hWF
  exact interior_maximal hsub hopen (mem_connectedComponentIn hyW)

/-- 到 `ℝ` 的连续线性泛函满射 ⇔ 非零。 -/
theorem surjective_iff_ne_zero_clm_R6A {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {L : V →L[ℝ] ℝ} : Function.Surjective L ↔ L ≠ 0 := by
  constructor
  · intro hs h0
    obtain ⟨v, hv⟩ := hs 1
    rw [h0] at hv
    exact zero_ne_one hv
  · intro hL y
    have hex : ∃ v, L v ≠ 0 := by
      by_contra h
      push Not at h
      exact hL (ContinuousLinearMap.ext h)
    obtain ⟨v, hv⟩ := hex
    refine ⟨(y / L v) • v, ?_⟩
    rw [map_smul]
    exact (smul_eq_mul _ _).trans (div_mul_cancel₀ y hv)

end Topological

/-! ## Part B：「good」是开条件 + 向内延伸 -/

section Convex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- 「`dρ ≠ 0` 且全 Hessian 正定」是开条件。`dρ ≠ 0` 即 `mfderiv ρ x` 满射
（`DifferentialGeometry.Topology.Ehresmann.isOpen_setOf_surjective_mfderiv`）；Hessian 部分是
`isOpen_hessFun_gt_mul_inner`（`c = 0`）。 -/
theorem isOpen_convexGood_R6A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {ρ : M → ℝ}
    (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) :
    IsOpen {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun g ρ x v v} := by
  have h1 : IsOpen {x : M | Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x)} :=
    DifferentialGeometry.Topology.Ehresmann.isOpen_setOf_surjective_mfderiv hρ
  have h2 : IsOpen {x : M | ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 →
      0 * g.inner x v v < hessFun g ρ x v v} := isOpen_hessFun_gt_mul_inner g hρ 0
  have hsurj : ∀ x : M, Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x) ↔
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 := by
    intro x
    exact surjective_iff_ne_zero_clm_R6A
  convert h1.inter h2 using 1
  ext x
  simp only [Set.mem_ofPred_eq, mem_inter_iff, zero_mul, hsurj x]

/-- 「good」向负侧延伸一小段：`N := {ρ ≤ 0} ∖ good` 闭且 `⊆ {ρ < a} ⊆ closure {ρ < a}`，故紧；
`hcvx` 给 `N ⊆ {ρ < 0}`（`{ρ = 0}` 上 good），紧集上 `ρ ≤ c < 0`，取 `ε₀ := −c`：
`∃ ε₀ > 0`，`{−ε₀ < ρ < a}` 上 `dρ ≠ 0` 且全 Hessian 正定。 -/
theorem exists_convex_collar_R6A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {ρ : M → ℝ}
    (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {a : ℝ} (ha : 0 < a)
    (hcpt : IsCompact (closure {x | ρ x < a}))
    (hcvx : ∀ x, 0 ≤ ρ x → ρ x < a → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun g ρ x v v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ x, -ε₀ < ρ x → ρ x < a →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
        ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun g ρ x v v := by
  have hG := isOpen_convexGood_R6A g hρ
  let N : Set M := {x | ρ x ≤ 0} ∩
    {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun g ρ x v v}ᶜ
  have hNclosed : IsClosed N :=
    (isClosed_le hρ.continuous continuous_const).inter hG.isClosed_compl
  have hNsub : N ⊆ closure {x | ρ x < a} := fun x hx => subset_closure (lt_of_le_of_lt hx.1 ha)
  have hNcpt : IsCompact N := hcpt.of_isClosed_subset hNclosed hNsub
  have hNneg : ∀ x ∈ N, ρ x < 0 := by
    intro x hx
    have hx1 : ρ x ≤ 0 := hx.1
    rcases lt_or_eq_of_le hx1 with h | h
    · exact h
    · exact absurd (hcvx x h.ge (h ▸ ha)) hx.2
  obtain ⟨c, hc, hcN⟩ := exists_neg_bound_of_isCompact_R6A hρ.continuous hNcpt hNneg
  refine ⟨-c, neg_pos.mpr hc, fun x hx1 hxa => ?_⟩
  by_cases h0 : 0 ≤ ρ x
  · exact hcvx x h0 hxa
  · by_contra hbad
    have hxN : x ∈ N := ⟨(not_le.mp h0).le, hbad⟩
    have := hcN x hxN
    linarith

/-- **G1（R6a 一般版）**：紧 `S ⊆ {ρ < 0}` ⇒ `∃ b δ > 0`：`S ⊆ {ρ < −b−δ}`；「good」
（`dρ ≠ 0` 且全 Hessian 正定）在 `{−b−δ ≤ ρ < a}` 上；`K := {ρ ≤ −b}` 紧、`K ⊆ {ρ < a}`、
`frontier K ⊆ {ρ = −b}`（且 `{ρ = −b}` 是正则水平集，由 good 给出）。 -/
theorem exists_convex_container_R6A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {ρ : M → ℝ}
    (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {a : ℝ} (ha : 0 < a)
    (hcpt : IsCompact (closure {x | ρ x < a}))
    (hcvx : ∀ x, 0 ≤ ρ x → ρ x < a → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun g ρ x v v)
    {S : Set M} (hS : IsCompact S) (hneg : ∀ x ∈ S, ρ x < 0) :
    ∃ b δ : ℝ, 0 < b ∧ 0 < δ ∧ (∀ x ∈ S, ρ x < -b - δ) ∧
      (∀ x, -b - δ ≤ ρ x → ρ x < a → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
        ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun g ρ x v v) ∧
      IsCompact {x | ρ x ≤ -b} ∧ {x | ρ x ≤ -b} ⊆ {x | ρ x < a} ∧
      frontier {x | ρ x ≤ -b} ⊆ {x | ρ x = -b} := by
  obtain ⟨ε₀, hε₀, hcol⟩ := exists_convex_collar_R6A g hρ ha hcpt hcvx
  obtain ⟨c, hc, hcS⟩ := exists_neg_bound_of_isCompact_R6A hρ.continuous hS hneg
  set η : ℝ := min ε₀ (-c) with hη
  have hηpos : 0 < η := lt_min hε₀ (neg_pos.mpr hc)
  have hη1 : η ≤ ε₀ := min_le_left _ _
  have hη2 : η ≤ -c := min_le_right _ _
  have hba : -(η / 4) < a := by linarith
  have hclosed : IsClosed {x | ρ x ≤ -(η / 4)} := isClosed_le hρ.continuous continuous_const
  have hsub : {x | ρ x ≤ -(η / 4)} ⊆ {x | ρ x < a} := fun x hx => lt_of_le_of_lt hx hba
  refine ⟨η / 4, η / 4, by positivity, by positivity, fun x hx => ?_, fun x hx1 hxa => ?_,
    hcpt.of_isClosed_subset hclosed (hsub.trans subset_closure), hsub, ?_⟩
  · have := hcS x hx
    linarith
  · exact hcol x (by linarith) hxa
  · intro x hx
    have hxcl : x ∈ closure {x | ρ x ≤ -(η / 4)} := hx.1
    rw [hclosed.closure_eq] at hxcl
    have hnotint : x ∉ interior {x | ρ x ≤ -(η / 4)} := hx.2
    refine le_antisymm hxcl (not_lt.mp fun hlt => hnotint ?_)
    exact interior_maximal (fun y hy => le_of_lt hy)
      (isOpen_lt hρ.continuous continuous_const) hlt

/-- **R6a（design 合同形）**：与 `strictly_convex_container_MYD2`（`R06to08.lean:59`）的结论
逐字相同；`S` 取预连通紧集，`K` 取 `{ρ ≤ −b}` 里含 `S` 的连通分量
`connectedComponentIn {ρ ≤ −b} x₀`（`x₀ ∈ S`）。 -/
theorem strictly_convex_container_R6A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {ρ : M → ℝ}
    (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {a : ℝ} (ha : 0 < a)
    (hcpt : IsCompact (closure {x | ρ x < a}))
    (hcvx : ∀ x, 0 ≤ ρ x → ρ x < a → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun g ρ x v v)
    {S : Set M} (hS : IsCompact S) (hSconn : IsPreconnected S) (hneg : ∀ x ∈ S, ρ x < 0) :
    ∃ b δ : ℝ, 0 < b ∧ 0 < δ ∧ (∀ x ∈ S, ρ x < -b - δ) ∧
      (∀ x, -b - δ ≤ ρ x → ρ x ≤ -b → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
        ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun g ρ x v v) ∧
      ∀ x₀ ∈ S, IsCompact (connectedComponentIn {x | ρ x ≤ -b} x₀) ∧
        S ⊆ interior (connectedComponentIn {x | ρ x ≤ -b} x₀) ∧
        frontier (connectedComponentIn {x | ρ x ≤ -b} x₀) ⊆ {x | ρ x = -b} := by
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E M
  obtain ⟨b, δ, hb, hδ, hSb, hgood, hKcpt, hKa, -⟩ :=
    exists_convex_container_R6A g hρ ha hcpt hcvx hS hneg
  have hba : ∀ x, ρ x ≤ -b → ρ x < a := fun x h => by linarith
  refine ⟨b, δ, hb, hδ, hSb, fun x h1 h2 => hgood x h1 (hba x h2), ?_⟩
  intro x₀ hx₀
  have hF : IsClosed {x | ρ x ≤ -b} := isClosed_le hρ.continuous continuous_const
  have hW : IsOpen {x | ρ x < -b} := isOpen_lt hρ.continuous continuous_const
  have hWF : {x | ρ x < -b} ⊆ {x | ρ x ≤ -b} := fun x (hx : ρ x < -b) => hx.le
  have hDclosed := isClosed_connectedComponentIn_R6A hF x₀
  have hDsub := connectedComponentIn_subset {x | ρ x ≤ -b} x₀
  have hSlt : ∀ x ∈ S, ρ x < -b := fun x hx => by have := hSb x hx; linarith
  have hSF : S ⊆ {x | ρ x ≤ -b} := fun x hx => (hSlt x hx).le
  have hSD : S ⊆ connectedComponentIn {x | ρ x ≤ -b} x₀ :=
    hSconn.subset_connectedComponentIn hx₀ hSF
  have hint := inter_subset_interior_connectedComponentIn_R6A hW hWF x₀
  refine ⟨hKcpt.of_isClosed_subset hDclosed hDsub, fun x hx => hint ⟨hSD hx, hSlt x hx⟩, ?_⟩
  intro x hx
  have hxD : x ∈ connectedComponentIn {x | ρ x ≤ -b} x₀ := by
    have h1 : x ∈ closure (connectedComponentIn {x | ρ x ≤ -b} x₀) := hx.1
    rwa [hDclosed.closure_eq] at h1
  exact le_antisymm (hDsub hxD) (not_lt.mp fun hlt => hx.2 (hint ⟨hxD, hlt⟩))

end Convex

end DifferentialGeometry.Geometry

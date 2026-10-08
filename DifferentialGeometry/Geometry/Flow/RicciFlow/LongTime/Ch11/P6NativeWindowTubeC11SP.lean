import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowSurvivalStep

/-!
# P6 native window tube：局部 Dt 合同 X 的基础层（O-CH11-NATIVE-NR，后缀 `_C11SP`）

`WindowPersistence:1029` 的 Dt 前提（`hderiv` / `hfinal`，形如 `∀ x : stage, ∀ t, q₀ < R → |∂ₜR| ≤ C R²`）
在证明里只在 cap window 的 **tube** 上被用到：`Jbig(window)` 的 backward traces 经过的点，以及这些点在
所在 slab 里的一个开邻域（terminal-regularity 的 Lipschitz(`1/max(q,R)`) 论证要开集，见
`IncomingReciprocal:40`）。本文件把这条调用树的 Dt-消费叶子改写成 **开 tube 形局部 Dt**：

* tube 数据 `W : ∀ j, Set (H.stage j).Carrier`，`hW : ∀ j, IsOpen (W j)`；
* 覆盖 `htube`：任一从 `first` 出发、起点在 `range J` 里的 `BackwardPointTrace` 的端点落在 `W j`；
* Dt 只要求在 `x ∈ W j` 上（guard `q₀ < R` 不变）。

孪生的声明一律后缀 `_tube_C11SP`，证明逐字照原文件（`HistorySurvivorFirstLossIncoming`、
`HistorySurvivorFirstLossFlow`、`CapWindowSurvival`、`WindowSurvivalStep`），只在 Dt 叶子处补 tube 成员证明；
`IncomingReciprocal` 的全局签名一步改成开集 `V` 版（`U ∩ V`）。不改任何原文件。
-/

set_option autoImplicit false

noncomputable section

section
open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

/-- `lipschitzOnWith_inv_max_scalar` 的逐点版：Dt 只要在点 `x` 上。 -/
theorem lipschitzOnWith_inv_max_scalar_pt_C11SP
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q) (x : P.Carrier)
    (hbound : ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) :
    LipschitzOnWith C (fun t => (max q (G.flow.scalar t x))⁻¹) (Ioo a s) := by
  apply DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound
    (r' := fun t => derivWithin (fun v => G.flow.scalar v x) (Iic t) t) hq ordConnected_Ioo
  · intro t ht
    exact (G.equation.scalarTime (K := Ioo a s) ht Ioo_subset_Ico_self x).continuousWithinAt
  · intro t ht _
    exact DifferentialGeometry.Analysis.hasDerivWithinAt_left_of_mem_nhdsLE
      (G.equation.scalarTime (K := Ioo a s) ht Ioo_subset_Ico_self x)
      (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ht.1 ht.2))
  · exact hbound

/-- `mem_terminalRegularRegion_of_inv_max_scalar_gt` 的开集版：Dt 只要在开集 `V ∋ x` 上
（原证明的 `U` 换成 `V ∩ U`）。 -/
theorem mem_terminalRegularRegion_of_inv_max_scalar_gt_tube_C11SP
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q) {V : Set P.Carrier} (hV : IsOpen V)
    (hbound : ∀ x : P.Carrier, x ∈ V → ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi)
    {x : P.Carrier} (hxV : x ∈ V) {t : ℝ} (ht : t ∈ Ioo a s)
    (hsmall : 4 * C * (s - t) < (max q (G.flow.scalar t x))⁻¹) :
    x ∈ G.terminalRegularRegion := by
  let B := max q (G.flow.scalar t x)
  have hB : 0 < B := hq.trans_le (le_max_left _ _)
  let U : Set P.Carrier := V ∩ {y | (2 * B)⁻¹ < (max q (G.flow.scalar t y))⁻¹}
  have hcont : Continuous (fun y : P.Carrier => (max q (G.flow.scalar t y))⁻¹) := by
    apply (continuous_const.max (scalarSmoothOfSolution G.flow t).continuous).inv₀
    intro y
    exact ne_of_gt (hq.trans_le (le_max_left _ _))
  have hU : IsOpen U := hV.inter (isOpen_lt continuous_const hcont)
  have hxU : x ∈ U := by
    refine ⟨hxV, ?_⟩
    exact (inv_lt_inv₀ (by positivity : 0 < 2 * B) hB).mpr (by linarith)
  have hsmall' : C * (s - t) < (4 * B)⁻¹ := by
    change 4 * C * (s - t) < B⁻¹ at hsmall
    have hb := inv_pos.mpr hB
    rw [mul_inv]
    nlinarith
  have hscalar : ∀ y ∈ U, ∀ v ∈ Ico t s, G.flow.scalar v y ≤ 4 * B := by
    intro y hy v hv
    have hvl : v ∈ Ioo a s := ⟨ht.1.trans_le hv.1, hv.2⟩
    have h := (G.lipschitzOnWith_inv_max_scalar_pt_C11SP hq y (hbound y hy.1)).dist_le_mul
      v hvl t ht
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hv.1)] at h
    have htime : C * (v - t) ≤ C * (s - t) :=
      mul_le_mul_of_nonneg_left (by linarith [hv.2]) C.coe_nonneg
    have hpos : (4 * B)⁻¹ < (max q (G.flow.scalar v y))⁻¹ := by
      have heq : (2 * B)⁻¹ = 2 * (4 * B)⁻¹ := by
        field_simp
        ring
      have hy2 : (2 * B)⁻¹ < (max q (G.flow.scalar t y))⁻¹ := hy.2
      rw [heq] at hy2
      have hh := neg_le_abs ((max q (G.flow.scalar v y))⁻¹ - (max q (G.flow.scalar t y))⁻¹)
      linarith
    have hmax : max q (G.flow.scalar v y) < 4 * B :=
      (inv_lt_inv₀ (by positivity) (hq.trans_le (le_max_left _ _))).mp hpos
    exact (le_max_right _ _).trans hmax.le
  obtain ⟨C3, hC3, hbridge⟩ := exists_rmNormLeOfCurvatureOperatorBounds.{u} ThreeModel
  have hnorm := hbridge P.Carrier G.flow
  refine ⟨U, hU, hxU, t, ⟨ht.1.le, ht.2⟩,
    2 * C3 * (B + Phi (4 * B) + Phi 0), by
      have := hPhi.pos (4 * B)
      have := hPhi.pos 0
      positivity, ?_⟩
  intro y hy v hv
  exact sqrt_rmNormSq_le_of_scalar_le hC3 hnorm hPhi hpinch (by simp [ThreeSpace])
    ⟨ht.1.le.trans hv.1, hv.2⟩ y hB (hscalar y hy v hv)

theorem inv_max_scalar_le_of_not_mem_terminalRegularRegion_tube_C11SP
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q) {V : Set P.Carrier} (hV : IsOpen V)
    (hbound : ∀ x : P.Carrier, x ∈ V → ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi)
    {x : P.Carrier} (hxV : x ∈ V) (hx : x ∉ G.terminalRegularRegion) {t : ℝ} (ht : t ∈ Ioo a s) :
    (max q (G.flow.scalar t x))⁻¹ ≤ 4 * C * (s - t) := by
  apply le_of_not_gt
  exact fun h => hx (G.mem_terminalRegularRegion_of_inv_max_scalar_gt_tube_C11SP hq hV hbound
    hPhi hpinch hxV ht h)

theorem tendsto_scalar_atTop_of_not_mem_terminalRegularRegion_tube_C11SP
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q) {V : Set P.Carrier} (hV : IsOpen V)
    (hbound : ∀ x : P.Carrier, x ∈ V → ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    {x : P.Carrier} (hxV : x ∈ V) (hx : x ∉ G.terminalRegularRegion) :
    Tendsto (fun t => G.flow.scalar t x) (𝓝[<] s) atTop := by
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  apply tendsto_atTop.mpr
  intro A
  let B := max q A
  have hB : 0 < B := hq.trans_le (le_max_left _ _)
  have hlim : Tendsto (fun t : ℝ => 4 * C * (s - t)) (𝓝[<] s) (𝓝 0) := by
    have hi : Tendsto (fun t : ℝ => t) (𝓝[<] s) (𝓝 s) := tendsto_id'.mpr nhdsWithin_le_nhds
    simpa using ((tendsto_const_nhds (x := s)).sub hi).const_mul (4 * (C : ℝ))
  have hsmall : ∀ᶠ t in 𝓝[<] s, 4 * C * (s - t) < B⁻¹ :=
    hlim.eventually (Iio_mem_nhds (inv_pos.mpr hB))
  filter_upwards [hsmall, Ioo_mem_nhdsLT G.lt] with t hts ht
  have hrec := G.inv_max_scalar_le_of_not_mem_terminalRegularRegion_tube_C11SP hq hV hbound
    hPhi hpinch hxV hx ht
  have hmax : B < max q (G.flow.scalar t x) :=
    (inv_lt_inv₀ (hq.trans_le (le_max_left _ _)) hB).mp (hrec.trans_lt hts)
  rcases lt_max_iff.mp hmax with h | h
  · exact (not_lt_of_ge (le_max_left q A) h).elim
  · exact ((le_max_right q A).trans_lt h).le

/-- `mem_terminalRegularRegion_of_frequently_scalar_le` 的开集版（`IncomingReciprocal:192`
签名全局、数学局部的那一步）。 -/
theorem mem_terminalRegularRegion_of_frequently_scalar_le_tube_C11SP
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q) {V : Set P.Carrier} (hV : IsOpen V)
    (hbound : ∀ x : P.Carrier, x ∈ V → ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    {x : P.Carrier} (hxV : x ∈ V) {B : ℝ}
    (hscalar : ∃ᶠ t in 𝓝[<] s, G.flow.scalar t x ≤ B) :
    x ∈ G.terminalRegularRegion := by
  by_contra hx
  have hh := (G.tendsto_scalar_atTop_of_not_mem_terminalRegularRegion_tube_C11SP hq hV hbound
    hxV hx).eventually_gt_atTop B
  exact hscalar (hh.mono fun _ h => not_le.mpr h)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
end

section
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- tube 覆盖 ⇒ trace 上每个中间点都在 tube 里（`restrictLast`）。 -/
theorem tube_trace_point_C11SP {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)}
    {Z : Set (H.stage first).Carrier}
    {W : ∀ j : Fin (H.eventCount + 1), Set (H.stage j).Carrier}
    (htube : ∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j), j ≤ last →
      ∀ (x : (H.stage j).Carrier) (A : BackwardPointTrace H first j hf x),
        A.point first le_rfl hf ∈ Z → x ∈ W j)
    {k : Fin (H.eventCount + 1)} {hk : first ≤ k} (hkl : k ≤ last) {y : (H.stage k).Carrier}
    (A : BackwardPointTrace H first k hk y) (hA : A.point first le_rfl hk ∈ Z)
    (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hjk : j ≤ k) :
    A.point j hf hjk ∈ W j :=
  htube j hf (hjk.trans hkl) _ (A.restrictLast hf hjk) hA

/-- tube 覆盖 ⇒ backward survivor 的中间像在 tube 里。 -/
theorem tube_survivor_C11SP {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)}
    {Z : Set (H.stage first).Carrier}
    {W : ∀ j : Fin (H.eventCount + 1), Set (H.stage j).Carrier}
    (htube : ∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j), j ≤ last →
      ∀ (x : (H.stage j).Carrier) (A : BackwardPointTrace H first j hf x),
        A.point first le_rfl hf ∈ Z → x ∈ W j)
    {k : Fin (H.eventCount + 1)} {hk : first ≤ k} (hkl : k ≤ last)
    (z : H.backwardSurvivorDomain first k hk)
    (hz : H.backwardSurvivorMap first k hk first le_rfl hk z ∈ Z)
    (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hjk : j ≤ k) :
    H.backwardSurvivorMap first k hk j hf hjk z ∈ W j :=
  tube_trace_point_C11SP htube hkl (Classical.choice z.property) hz j hf hjk

/-- tube 覆盖 ⇒ backward survivor 点本身在 tube 里。 -/
theorem tube_survivor_last_C11SP {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)}
    {Z : Set (H.stage first).Carrier}
    {W : ∀ j : Fin (H.eventCount + 1), Set (H.stage j).Carrier}
    (htube : ∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j), j ≤ last →
      ∀ (x : (H.stage j).Carrier) (A : BackwardPointTrace H first j hf x),
        A.point first le_rfl hf ∈ Z → x ∈ W j)
    {k : Fin (H.eventCount + 1)} {hk : first ≤ k} (hkl : k ≤ last)
    (z : H.backwardSurvivorDomain first k hk)
    (hz : H.backwardSurvivorMap first k hk first le_rfl hk z ∈ Z) :
    z.val ∈ W k :=
  htube k hk hkl z.val (Classical.choice z.property) hz

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u v
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Y : Type*} [TopologicalSpace Y] {I : ModelWithCorners ℝ E Y} [I.Boundaryless]
  {X : Type v} [TopologicalSpace X] [ChartedSpace Y X] [IsManifold I ∞ X]

theorem exists_first_event_incoming_chart_of_frequently_scalar_le_after_survival_tube_C11SP
    (J : X → (H.stage first).Carrier) (hJ : IsSmoothEmbedding I ThreeModel ∞ J)
    (next : Fin (H.eventCount + 1)) (hnext : first ≤ next)
    (hsurvived : range J ⊆ range (H.backwardSurvivorMap first next hnext first le_rfl hnext))
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (W : ∀ j : Fin (H.eventCount + 1), Set (H.stage j).Carrier) (hW : ∀ j, IsOpen (W j))
    (htube : ∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j), j ≤ last →
      ∀ (x : (H.stage j).Carrier) (A : BackwardPointTrace H first j hf x),
        A.point first le_rfl hf ∈ range J → x ∈ W j)
    (hderiv : ∀ j : Fin H.eventCount, next ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, x ∈ W j.castSucc →
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    (hscalar : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc), next ≤ j.castSucc → j.succ ≤
        last →
      ∀ (x : (H.stage j.castSucc).Carrier) (A : BackwardPointTrace H first j.castSucc hf x),
        A.point first le_rfl hf ∈ range J →
        ∃ B : ℝ, ∃ᶠ t in 𝓝[<] H.time j.succ, (H.event j).incoming.flow.scalar t x ≤ B)
    (hnot : ¬ range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle)) :
    ∃ (i : Fin H.eventCount) (hf : first ≤ i.castSucc), next ≤ i.castSucc ∧ i.succ ≤ last ∧
      (∀ (k : Fin (H.eventCount + 1)) (hk : first ≤ k), k ≤ i.castSucc →
        range J ⊆ range (H.backwardSurvivorMap first k hk first le_rfl hk)) ∧
      ∃ Ξ : X → H.backwardSurvivorTerminalFace first i hf,
        IsSmoothEmbedding I ThreeModel ∞ Ξ ∧
        (∀ x, H.backwardSurvivorMap first i.castSucc hf first le_rfl hf (Ξ x).val = J x) ∧
        ∃ x : X, ∀ y : (H.stage i.succ).Carrier,
          ¬ (H.event i).RegularCrossing
            (H.backwardSurvivorTerminalFaceMap first i hf (Ξ x)).val y := by
  obtain ⟨i, hf, hl, hpast, Φ, hΦ, hbirth, x, hx⟩ :=
    H.exists_first_event_without_regularCrossing first last hle J hJ hnot
  have hnexti : next ≤ i.castSucc := by
    by_contra hnotnext
    have hinext : i.succ ≤ next := by
      have hlt : i.castSucc < next := lt_of_not_ge hnotnext
      exact hlt
    obtain ⟨z, hz⟩ := hsurvived (mem_range_self x)
    let A : BackwardPointTrace H first next hnext z.val := Classical.choice z.property
    let B : BackwardPointTrace H first i.castSucc hf (Φ x).val := Classical.choice (Φ x).property
    have hA := H.backwardSurvivorMap_eq_point first next hnext first le_rfl hnext z A
    have hB := H.backwardSurvivorMap_eq_point first i.castSucc hf first le_rfl hf (Φ x) B
    have hpoint : A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hinext) = (Φ x).val :=
      (A.restrictLast hf (i.castSucc_lt_succ.le.trans hinext)).endpoint_eq_of_point_first_eq B
        (hA.symm.trans (hz.trans ((hbirth x).symm.trans hB)))
    have hcross := A.crossing i hf hinext
    rw [hpoint] at hcross
    exact hx _ hcross
  have hterminal (z : X) : (Φ z).val ∈ (H.event i).incoming.terminalRegularRegion := by
    let A : BackwardPointTrace H first i.castSucc hf (Φ z).val := Classical.choice (Φ z).property
    have hA : A.point first le_rfl hf ∈ range J := by
      rw [← H.backwardSurvivorMap_eq_point first i.castSucc hf first le_rfl hf (Φ z) A,
        hbirth]
      exact mem_range_self z
    obtain ⟨B, hB⟩ := hscalar i hf hnexti hl (Φ z).val A hA
    exact (H.event i).incoming.mem_terminalRegularRegion_of_frequently_scalar_le_tube_C11SP
      hq (hW _) (hderiv i hnexti hl) (htube _ hf (i.castSucc_lt_succ.le.trans hl) _ A hA) hB
  let Ξ : X → H.backwardSurvivorTerminalFace first i hf := fun z => ⟨Φ z, hterminal z⟩
  have hΞ : IsSmoothEmbedding I ThreeModel ∞ Ξ :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen I ThreeModel
      (H.backwardSurvivorTerminalFace first i hf) Ξ hΦ
  exact ⟨i, hf, hnexti, hl, hpast, Ξ, hΞ, hbirth, x, hx⟩

theorem exists_first_event_incoming_chart_of_frequently_scalar_le_tube_C11SP
    (J : X → (H.stage first).Carrier) (hJ : IsSmoothEmbedding I ThreeModel ∞ J)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (W : ∀ j : Fin (H.eventCount + 1), Set (H.stage j).Carrier) (hW : ∀ j, IsOpen (W j))
    (htube : ∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j), j ≤ last →
      ∀ (x : (H.stage j).Carrier) (A : BackwardPointTrace H first j hf x),
        A.point first le_rfl hf ∈ range J → x ∈ W j)
    (hderiv : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, x ∈ W j.castSucc →
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    (hscalar : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc), j.succ ≤ last →
      ∀ (x : (H.stage j.castSucc).Carrier) (A : BackwardPointTrace H first j.castSucc hf x),
        A.point first le_rfl hf ∈ range J →
        ∃ B : ℝ, ∃ᶠ t in 𝓝[<] H.time j.succ, (H.event j).incoming.flow.scalar t x ≤ B)
    (hnot : ¬ range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle)) :
    ∃ (i : Fin H.eventCount) (hf : first ≤ i.castSucc), i.succ ≤ last ∧
      (∀ (k : Fin (H.eventCount + 1)) (hk : first ≤ k), k ≤ i.castSucc →
        range J ⊆ range (H.backwardSurvivorMap first k hk first le_rfl hk)) ∧
      ∃ Ξ : X → H.backwardSurvivorTerminalFace first i hf,
        IsSmoothEmbedding I ThreeModel ∞ Ξ ∧
        (∀ x, H.backwardSurvivorMap first i.castSucc hf first le_rfl hf (Ξ x).val = J x) ∧
        ∃ x : X, ∀ y : (H.stage i.succ).Carrier,
          ¬ (H.event i).RegularCrossing
            (H.backwardSurvivorTerminalFaceMap first i hf (Ξ x)).val y := by
  have hself : range J ⊆ range (H.backwardSurvivorMap first first le_rfl first le_rfl le_rfl) := by
    rintro _ ⟨x, rfl⟩
    let z : H.backwardSurvivorDomain first first le_rfl :=
      ⟨J x, ⟨BackwardPointTrace.singleton H first (J x)⟩⟩
    exact ⟨z, H.backwardSurvivorMap_last first first le_rfl z⟩
  obtain ⟨i, hf, _, hl, hrest⟩ :=
    H.exists_first_event_incoming_chart_of_frequently_scalar_le_after_survival_tube_C11SP
      first last hle J hJ first le_rfl hself hq W hW htube hderiv (fun j hf _ hl => hscalar j hf
          hl) hnot
  exact ⟨i, hf, hl, hrest⟩

theorem exists_first_event_incoming_chart_of_scalar_bound_at_later_time_tube_C11SP
    (J : X → (H.stage first).Carrier) (hJ : IsSmoothEmbedding I ThreeModel ∞ J)
    (next : Fin H.eventCount) (hnext : first ≤ next.castSucc)
    (hsurvived : range J ⊆ range
      (H.backwardSurvivorMap first next.castSucc hnext first le_rfl hnext))
    {q Q τ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hτ : τ ∈ Ico (H.time next.castSucc) (H.time next.succ))
    (hscalar : ∀ (x : (H.stage next.castSucc).Carrier)
      (A : BackwardPointTrace H first next.castSucc hnext x),
      A.point first le_rfl hnext ∈ range J → (H.event next).incoming.flow.scalar τ x ≤ Q)
    (W : ∀ j : Fin (H.eventCount + 1), Set (H.stage j).Carrier) (hW : ∀ j, IsOpen (W j))
    (htube : ∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j), j ≤ last →
      ∀ (x : (H.stage j).Carrier) (A : BackwardPointTrace H first j hf x),
        A.point first le_rfl hf ∈ range J → x ∈ W j)
    (hderiv : ∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, x ∈ W j.castSucc →
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    (htime : 2 * C * (H.time last - τ) * Q ≤ 1)
    (hnot : ¬ range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle)) :
    ∃ (i : Fin H.eventCount) (hf : first ≤ i.castSucc), next.castSucc ≤ i.castSucc ∧ i.succ ≤ last ∧
      (∀ (k : Fin (H.eventCount + 1)) (hk : first ≤ k), k ≤ i.castSucc →
        range J ⊆ range (H.backwardSurvivorMap first k hk first le_rfl hk)) ∧
      ∃ Ξ : X → H.backwardSurvivorTerminalFace first i hf,
        IsSmoothEmbedding I ThreeModel ∞ Ξ ∧
        (∀ x, H.backwardSurvivorMap first i.castSucc hf first le_rfl hf (Ξ x).val = J x) ∧
        ∃ x : X, ∀ y : (H.stage i.succ).Carrier,
          ¬ (H.event i).RegularCrossing
            (H.backwardSurvivorTerminalFaceMap first i hf (Ξ x)).val y := by
  apply H.exists_first_event_incoming_chart_of_frequently_scalar_le_after_survival_tube_C11SP
    first last hle J hJ next.castSucc hnext hsurvived hq W hW htube hderiv ?_ hnot
  intro j hf hnj hl x A hx
  have hj : next ≤ j := Fin.castSucc_le_castSucc_iff.mp hnj
  have htauj : τ < H.time j.succ := hτ.2.trans_le
    (H.time_strictMono.monotone (Fin.succ_le_succ_iff.mpr hj))
  have hAτ : (H.event next).incoming.flow.scalar τ (A.point next.castSucc hnext hnj) ≤ Q :=
    hscalar _ (A.restrictLast hnext hnj) hx
  refine ⟨2 * Q, Filter.Eventually.frequently ?_⟩
  filter_upwards [Ioo_mem_nhdsLT htauj, Ioo_mem_nhdsLT (H.event j).incoming.lt] with t htτ ht
  have hb := A.scalar_le_two_mul_of_earlier_scalar_le_at_time hq next j hnext hj le_rfl
    (fun k hk hkj => hderiv k hk
      ((Fin.succ_le_succ_iff.mpr (Fin.castSucc_le_castSucc_iff.mp hkj)).trans hl) _
      (tube_trace_point_C11SP htube (j.castSucc_lt_succ.le.trans hl) A hx _ _ _))
    hτ ⟨ht.1.le, ht.2⟩ htτ.1.le hqQ hAτ ?_
  · simpa only [A.endpoint_eq] using hb
  have hQ : 0 < Q := hq.trans_le hqQ
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (ht.2.le.trans (H.time_strictMono.monotone hl)) τ)
      (by positivity : 0 ≤ 2 * (C : ℝ))) hQ.le).trans htime

theorem exists_first_event_incoming_chart_of_initial_scalar_bound_tube_C11SP
    (J : X → (H.stage first).Carrier) (hJ : IsSmoothEmbedding I ThreeModel ∞ J)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hscalar : ∀ x, metricScalarAt (H.initialMetric first) (J x) ≤ Q)
    (W : ∀ j : Fin (H.eventCount + 1), Set (H.stage j).Carrier) (hW : ∀ j, IsOpen (W j))
    (htube : ∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j), j ≤ last →
      ∀ (x : (H.stage j).Carrier) (A : BackwardPointTrace H first j hf x),
        A.point first le_rfl hf ∈ range J → x ∈ W j)
    (hderiv : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, x ∈ W j.castSucc →
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    (htime : 8 * C * (H.time last - H.time first) * Q ≤ 1)
    (hnot : ¬ range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle)) :
    ∃ (i : Fin H.eventCount) (hf : first ≤ i.castSucc), i.succ ≤ last ∧
      (∀ (k : Fin (H.eventCount + 1)) (hk : first ≤ k), k ≤ i.castSucc →
        range J ⊆ range (H.backwardSurvivorMap first k hk first le_rfl hk)) ∧
      ∃ Ξ : X → H.backwardSurvivorTerminalFace first i hf,
        IsSmoothEmbedding I ThreeModel ∞ Ξ ∧
        (∀ x, H.backwardSurvivorMap first i.castSucc hf first le_rfl hf (Ξ x).val = J x) ∧
        ∃ x : X, ∀ y : (H.stage i.succ).Carrier,
          ¬ (H.event i).RegularCrossing
            (H.backwardSurvivorTerminalFaceMap first i hf (Ξ x)).val y := by
  apply H.exists_first_event_incoming_chart_of_frequently_scalar_le_tube_C11SP
    first last hle J hJ hq W hW htube hderiv ?_ hnot
  intro j hf hl x A hx
  have hxl : j.castSucc ≤ last := j.castSucc_lt_succ.le.trans hl
  have hxW : x ∈ W j.castSucc := htube _ hf hxl x A hx
  have hAW := tube_trace_point_C11SP htube hxl A hx
  obtain ⟨z, hz⟩ := hx
  refine ⟨2 * Q, ?_⟩
  apply Filter.Eventually.frequently
  filter_upwards [Ioo_mem_nhdsLT (H.event j).incoming.lt] with t ht
  apply A.scalar_incoming_le_two_mul_initial_of_time_sub_le
    (H.event j).incoming (H.event_initial j) x hq hqQ
    (fun k hk hkj => hderiv k hk (hkj.trans (j.castSucc_lt_succ.le.trans hl)) _ (hAW _ _ _))
    (hderiv j hf hl x hxW) ?_ ⟨ht.1.le,ht.2⟩ ?_
  · rw [← hz]
    exact hscalar z
  · have hQ : 0 < Q := hq.trans_le hqQ
    have hdt : t - H.time first ≤ H.time last - H.time first :=
      sub_le_sub_right (ht.2.le.trans (H.time_strictMono.monotone hl)) _
    have hnonneg : 0 ≤ (C : ℝ) * Q := mul_nonneg C.coe_nonneg hQ.le
    have ht0 : 0 ≤ H.time last - H.time first := sub_nonneg.mpr (H.time_strictMono.monotone hle)
    nlinarith [mul_le_mul_of_nonneg_right hdt hnonneg, mul_nonneg hnonneg ht0]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem exists_first_event_normalized_chart_solution_of_scalar_bound_at_later_time_tube_C11SP
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (next : Fin H.eventCount) (hnext : first ≤ next.castSucc)
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (J : X → (H.stage first).Carrier) (hJ : IsSmoothEmbedding ThreeModel ThreeModel ∞ J)
    {τ : ℝ} (G : (H.stage next.castSucc).IncomingSlab (H.time next.castSucc) τ)
    (L : G.TerminalLimitMetric)
    (hsource : ∀ t, G.flow.base.metric t = (H.event next).incoming.flow.base.metric t)
    (hterminal : L.metric =
      ((H.event next).incoming.flow.base.metric τ).restrictOpen G.terminalRegularOpen)
    (hτ : τ ∈ Ico (H.time next.castSucc) (H.time next.succ))
    (Ψ : X → H.backwardSurvivorIncomingDomain first next.castSucc hnext G)
    (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ)
    (hΨbirth : ∀ x, H.backwardSurvivorMap first next.castSucc hnext first le_rfl hnext
      (Ψ x).val = J x)
    (gflow₀ : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first next.castSucc hnext G))
    (hslabs₀ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ next.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow₀ t = (H.backwardSurvivorSlabMetric first next.castSucc hnext j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first next.castSucc hnext G))
    (hlast₀ : ∀ t ∈ Icc (H.time next.castSucc) τ,
      gflow₀ t = H.backwardSurvivorIncomingMetric first next.castSucc hnext G L t)
    {r q C₀ a₀ Kpast : ℝ} {C : ℝ≥0}
    (hC₀ : 0 < C₀) (hq : 0 < q) (hrQ : r ≤ C₀ * q) (haq : 1 ≤ a₀ * q)
    (g₀ : SmoothRiemannianMetric ThreeModel X)
    (hzero : ∀ x (v w : TangentSpace ThreeModel x),
      g₀.inner x v w = q * (H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x w))
    {D₀ : RealTimeInterval} (S₀ : SolutionOn (I := ThreeModel) (M := X) D₀)
    (hmetric₀ : ∀ t ∈ Icc 0 (q * (τ - H.time first)), S₀.base.metric t =
      localPullMetric (scaleMetric q hq (gflow₀ (H.time first + t / q))) Ψ hΨ)
    (hpast : ∀ t ∈ Icc 0 (q * (τ - H.time first)), ∀ x : X,
      normSq0S (S₀.base.metric t) x 4 (S₀.base.rm04 t x) ≤ Kpast)
    (hscalar : ∀ x, (H.event next).incoming.flow.scalar τ (Ψ x).val.val ≤ C₀ * q)
    (W : ∀ j : Fin (H.eventCount + 1), Set (H.stage j).Carrier) (hW : ∀ j, IsOpen (W j))
    (htube : ∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j), j ≤ last →
      ∀ (x : (H.stage j).Carrier) (A : BackwardPointTrace H first j hf x),
        A.point first le_rfl hf ∈ range J → x ∈ W j)
    (hderiv : ∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, x ∈ W j.castSucc →
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        r < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last →
      ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ), τ ≤ t →
        ∀ x : (H.stage j.castSucc).Carrier,
          InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) a₀ x)
    (htime : 2 * C * C₀ * (q * (H.time last - τ)) ≤ 1)
    (hnot : ¬ range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle)) :
    ∃ (i : Fin H.eventCount) (hf : first ≤ i.castSucc),
      next.castSucc ≤ i.castSucc ∧ i.succ ≤ last ∧
      (∀ (k : Fin (H.eventCount + 1)) (hk : first ≤ k), k ≤ i.castSucc →
        range J ⊆ range (H.backwardSurvivorMap first k hk first le_rfl hk)) ∧
      ∃ Ξ : X → H.backwardSurvivorTerminalFace first i hf,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
        (∀ x, H.backwardSurvivorMap first i.castSucc hf first le_rfl hf (Ξ x).val = J x) ∧
        (∃ x : X, ∀ y : (H.stage i.succ).Carrier,
          ¬ (H.event i).RegularCrossing
            (H.backwardSurvivorTerminalFaceMap first i hf (Ξ x)).val y) ∧
        ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
          (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorTerminalFace first i
              hf)),
          (∀ (j : Fin H.eventCount) (hj : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
            ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
              gflow t = (H.backwardSurvivorSlabMetric first i.castSucc hf j hj hl t).restrictOpen
                (H.backwardSurvivorTerminalFace first i hf)) ∧
          (∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
            gflow t = H.backwardSurvivorTerminalFaceMetric first i hf t) ∧
          ∃ S : SolutionOn (I := ThreeModel) (M := X)
              (RealTimeInterval.closed 0 (q * (H.time i.succ - H.time first))
                (by have ht := H.time_strictMono (hf.trans_lt i.castSucc_lt_succ); positivity)),
            IsSolutionOn S ∧ S.base.metric 0 = g₀ ∧
            (∀ t, S.base.metric t =
              localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) ∧
            (∀ (x : X) (k l : Fin (Module.finrank ℝ ThreeSpace)),
              ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
                (fun z : ℝ × X => chartGramMatrix (S.base.metric z.1) x z.2 k l)
                (Icc 0 (q * (H.time i.succ - H.time first)) ×ˢ
                  (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).baseSet)) ∧
            (∀ t ∈ Icc 0 (q * (τ - H.time first)), S.base.metric t = S₀.base.metric t) ∧
            ∀ t ∈ Icc 0 (q * (H.time i.succ - H.time first)), ∀ x : X,
              normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤
                max Kpast ((2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2) := by
  have hsurvived : range J ⊆ range
      (H.backwardSurvivorMap first next.castSucc hnext first le_rfl hnext) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(Ψ x).val, hΨbirth x⟩
  have hscalarTrace (x : (H.stage next.castSucc).Carrier)
      (A : BackwardPointTrace H first next.castSucc hnext x)
      (hx : A.point first le_rfl hnext ∈ range J) :
      (H.event next).incoming.flow.scalar τ x ≤ C₀ * q := by
    obtain ⟨y, hy⟩ := hx
    let B : BackwardPointTrace H first next.castSucc hnext (Ψ y).val.val :=
      Classical.choice (Ψ y).val.property
    have he := H.backwardSurvivorMap_eq_point first next.castSucc hnext first le_rfl hnext
      (Ψ y).val B
    have hpoint := B.endpoint_eq_of_point_first_eq A
      (he.symm.trans ((hΨbirth y).trans hy))
    rw [← hpoint]
    exact hscalar y
  have htime' : 2 * C * (H.time last - τ) * (C₀ * q) ≤ 1 := by
    nlinarith [htime]
  obtain ⟨i, hf, hni, hil, hsurvives, Ξ, hΞs, hbirth, hfailed⟩ :=
    H.exists_first_event_incoming_chart_of_scalar_bound_at_later_time_tube_C11SP
      first last hle J hJ next hnext hsurvived (mul_pos hC₀ hq) le_rfl hτ hscalarTrace W hW htube
      (fun j hj hl x hx t ht hs => hderiv j hj hl x hx t ht (hrQ.trans_lt hs)) htime' hnot
  have hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ := fun x =>
    Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq rfl
      (hΞs.isImmersion.isImmersionAt x)
  obtain ⟨gflow, hslabs, hlast, S, hS, hSzero, hmetric, hgram⟩ :=
    H.exists_normalized_backwardSurvivor_chart_solution first i hf Ξ hΞ J hbirth q hq g₀ hzero
  have hoverlap : ∀ t ∈ Icc 0 (q * (τ - H.time first)),
      S.base.metric t = S₀.base.metric t := by
    intro t ht
    have htphys : H.time first + t / q ∈ Icc (H.time first) τ := by
      constructor
      · exact le_add_of_nonneg_right (div_nonneg ht.1 hq.le)
      · have hh := (div_le_iff₀ hq).mpr
          (show t ≤ (τ - H.time first) * q by nlinarith [ht.2])
        linarith
    rw [hmetric t, hmetric₀ t ht, DifferentialGeometry.localPullMetric_scaleMetric,
        DifferentialGeometry.localPullMetric_scaleMetric]
    congr 1
    exact (H.localPullMetric_backwardSurvivorIncoming_eq_terminalFace_of_initial_eq
      first next i hnext hf hni hτ G L hsource hterminal gflow₀ gflow
      hslabs₀ hslabs hlast₀ hlast Ψ Ξ hΨ hΞ
      (fun x => (hΨbirth x).trans (hbirth x).symm) htphys).symm
  have htimei : 2 * C * C₀ * (q * (H.time i.succ - τ)) ≤ 1 := by
    calc
      2 * C * C₀ * (q * (H.time i.succ - τ)) =
          (2 * C * C₀ * q) * (H.time i.succ - τ) := by ring
      _ ≤ (2 * C * C₀ * q) * (H.time last - τ) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right (H.time_strictMono.monotone hil) τ)
          (by positivity)
      _ = 2 * C * C₀ * (q * (H.time last - τ)) := by ring
      _ ≤ 1 := htime
  have hlate := curvature_bound_normalized_backwardSurvivor_chart_of_scalar_bound_at_time
    gflow hslabs hlast Ξ hΞ next hnext hni (mul_pos hC₀ hq) hq le_rfl haq
    (fun x j hj hji t ht hs => hderiv j hj
      ((Fin.succ_le_succ_iff.mpr (Fin.castSucc_le_castSucc_iff.mp hji)).trans hil) _
      (tube_survivor_C11SP htube (i.castSucc_lt_succ.le.trans hil) (Ξ x).val
        ⟨x, (hbirth x).symm⟩ _ _ _) t ht
      (hrQ.trans_lt hs))
    hτ (fun x => by
      have he := H.backwardSurvivorMap_eq_of_initial_eq first next.castSucc i.castSucc
        hnext hf (Ψ x).val (Ξ x).val ((hΨbirth x).trans (hbirth x).symm)
        next.castSucc hnext le_rfl hni
      have hp : (Ψ x).val.val =
          H.backwardSurvivorMap first i.castSucc hf next.castSucc hnext hni (Ξ x).val := by
        simpa only [H.backwardSurvivorMap_last] using he
      rw [← hp]
      exact hscalar x)
    (fun x j hj hji t ht hτt => hpinch j hj
      ((Fin.succ_le_succ_iff.mpr (Fin.castSucc_le_castSucc_iff.mp hji)).trans hil) t ht hτt _)
    htimei S (fun t _ => hmetric t)
  refine ⟨i, hf, hni, hil, hsurvives, Ξ, hΞs, hbirth, hfailed, hΞ, gflow,
    hslabs, hlast, S, hS, hSzero, hmetric, hgram, hoverlap, ?_⟩
  intro t ht x
  by_cases hp : t ≤ q * (τ - H.time first)
  · change normSq0S (S.base.metric t) x 4 (metricRm04At (S.base.metric t) x) ≤ _
    rw [hoverlap t ⟨ht.1, hp⟩]
    exact (hpast t ⟨ht.1, hp⟩ x).trans (le_max_left _ _)
  · exact (hlate t ⟨(lt_of_not_ge hp).le, ht.2⟩ x).trans (le_max_right _ _)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open private terminal_chart_metric from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowSurvival

universe u

private local instance (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

theorem exists_uniform_cap_window_survival_time_of_radius_lower_bound_tube_C11SP
    (C₀ : ℝ) (C : ℝ≥0) (hC₀ : 0 < C₀) :
    ∃ η ε₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ D : ℝ, 65 ≤ D → ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ),
      4 ≤ m → ζ ≤ ε₀ →
      (∀ x : standardCapWindow D, ∀ v : TangentSpace ThreeModel x,
        w.windowMetric.inner x v v ≤ (3/2 : ℝ) * StandardCap.metric.inner x.val v v) →
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (J : standardCapWindow D → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
      ∀ (q q₀ a₀ : ℝ), 0 < q → 0 < q₀ → q₀ ≤ C₀ * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (J x) (mfderiv ThreeModel ThreeModel J x v)
          (mfderiv ThreeModel ThreeModel J x z)) →
      (∀ x, metricScalarAt (H.initialMetric first) (J x) ≤ C₀ * q) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H
          j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ δ₀) →
      ∀ (W : ∀ j : Fin (H.eventCount + 1), Set (H.stage j).Carrier), (∀ j, IsOpen (W j)) →
      (∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j), j ≤ last →
        ∀ (x : (H.stage j).Carrier) (A : BackwardPointTrace H first j hf x),
          A.point first le_rfl hf ∈ range J → x ∈ W j) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, x ∈ W j.castSucc →
        ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      q * (H.time last - H.time first) ≤ η →
      ∀ (z : standardCapWindow D) (endpoint : (H.stage last).Carrier)
        (A : BackwardPointTrace H first last hle endpoint), A.point first le_rfl hle = J z →
      ∃ Ψ : standardCapWindow D → H.backwardSurvivorDomain first last hle,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ψ ∧
        ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ψ x) = J x := by
  let K := (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2
  let Cs := 9 * Real.sqrt K + 1
  have hCs : 0 < Cs := by dsimp [Cs]; positivity
  obtain ⟨ηtip, ε₀, hηtip, hηtip1, hε₀, hεhalf, htip⟩ :=
    StandardCap.exists_uniform_initial_tip_ricci_lower_bound_of_local_curvature 1 K (by norm_num)
  obtain ⟨ηdist, hηdist, hdist⟩ :=
    StandardCap.exists_uniform_window_flow_edist_bound_of_initial_metric_upper K
  let η := min ηtip (min ηdist (8 * C * C₀ + 1)⁻¹)
  have hη : 0 < η := lt_min hηtip (lt_min hηdist (by positivity))
  refine ⟨η, ε₀, hη, hε₀, hεhalf, ?_⟩
  intro D hD65
  have hD : 0 < D := by linarith
  obtain ⟨δ₀, hδ₀, hprotect⟩ := exists_cutoff_protection_tolerance_of_ricci_lower_bound
    hCs (by positivity : 0 ≤ 4 * (D + 1)) (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ hupper
    H first last hle J hJ q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records
    hfixed hlower hδ W hW htube hderiv htime z endpoint Atrace hanchor
  have htime8 : 8 * C * (H.time last - H.time first) * (C₀ * q) ≤ 1 := by
    have hh := htime.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hden : 0 < 8 * (C : ℝ) * C₀ + 1 := by positivity
    have hm := (le_div_iff₀ hden).mp (show q * (H.time last - H.time first) ≤
      1 / (8 * (C : ℝ) * C₀ + 1) from by simpa only [one_div] using hh)
    have ht0 := H.time_strictMono.monotone hle
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr ht0)]
  have hsurvive : range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle) := by
    by_contra hnot
    obtain ⟨i, hf, hl, _, Ξ, hΞs, hbirth, xbad, hbad⟩ :=
      H.exists_first_event_incoming_chart_of_initial_scalar_bound_tube_C11SP
        first last hle J hJ hq₀ hq₀Q hscalar W hW htube hderiv htime8 hnot
    have hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ := fun x =>
      Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq rfl
        (hΞs.isImmersion.isImmersionAt x)
    let θ := q * (H.time i.succ - H.time first)
    have hθ : 0 < θ := mul_pos hq (sub_pos.mpr (H.time_strictMono (hf.trans_lt i.castSucc_lt_succ)))
    have hθη : θ ≤ η :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_right (H.time_strictMono.monotone hl) _) hq.le).trans
          htime
    have hθcap : θ ≤ ηtip := hθη.trans (min_le_left _ _)
    have hθdist : θ ≤ ηdist := hθη.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hθ1 : θ ≤ 1 := hθcap.trans hηtip1
    have htime2 : 2 * C * C₀ * θ ≤ 1 := by
      have ht0 := H.time_strictMono.monotone hl
      dsimp only [θ]
      nlinarith [mul_nonneg hq.le (sub_nonneg.mpr (H.time_strictMono.monotone hle)),
        mul_nonneg C.coe_nonneg hC₀.le]
    obtain ⟨G, hslabs, hlast, L, hL, hLzero, hmetric, hgram, hRm⟩ :=
      exists_normalized_backwardSurvivor_chart_solution_curvature_bound Ξ hΞ J hbirth
        hq₀ hq hq₀Q w.windowMetric hzero haq
        (fun x j hj hji => hderiv j hj (by
          exact (Fin.succ_le_succ_iff.mpr (show j ≤ i from hji)).trans hl) _
          (tube_survivor_C11SP htube (i.castSucc_lt_succ.le.trans hl) (Ξ x).val
            ⟨x, (hbirth x).symm⟩ _ _ _))
        hscalar records hfixed hlower htime2
    have hcurv : ∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D,
        nablaKRm04NormSqIntrinsic L 0 t x ≤ K := by
      simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hRm
    let Φ := H.backwardSurvivorTerminalFaceMap first i hf ∘ Ξ
    have hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ :=
      isLocalDiffeomorph_comp (H.backwardSurvivorTerminalFaceMap_isLocalDiffeomorph first i hf) hΞ
    have hΦinj : Injective Φ :=
      (H.backwardSurvivorTerminalFaceMap_injective first i hf).comp hΞs.isEmbedding.injective
    let h := scaleMetric q hq (H.event i).terminal.metric
    have hmet := terminal_chart_metric H first i hf hq Ξ hΞ G hlast L hmetric
    let tip : standardCapWindow D := ⟨0,
        by change ‖(0 : ThreeSpace)‖ < D + 1; simpa using (by linarith : (0 : ℝ) < D + 1)⟩
    have htipRic := htip w hD65 hm hζ _ θ hθ hθ1 (fun _ ht => ht) (fun _ ht => ht)
      L hL hLzero hgram (fun t ht x _ => hcurv t ht x) θ
      ⟨hθ.le, le_min hθcap le_rfl⟩ tip rfl
    have hpull : L.base.metric θ = localPullMetric h Φ hΦ := by
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      exact (hmet x v w).trans (localPullMetric_inner h Φ hΦ x v w).symm
    have hRic : ∀ v : TangentSpace ThreeModel (Φ tip),
        (1 / 2 : ℝ) * q * (H.event i).terminal.metric.inner (Φ tip) v v ≤
          ricciTensor (H.event i).terminal.metric (Φ tip) v v := by
      intro v
      obtain ⟨w, hw⟩ := (hΦ.mfderivToContinuousLinearEquiv (by simp) tip).surjective v
      have hd : mfderiv ThreeModel ThreeModel Φ tip w = v := hw
      have hh := htipRic w
      rw [hpull, localPullMetric_inner, ricciTensor_localPull] at hh
      change (1 / 2 : ℝ) * (scaleMetric q hq (H.event i).terminal.metric).inner (Φ tip)
        (mfderiv ThreeModel ThreeModel Φ tip w) (mfderiv ThreeModel ThreeModel Φ tip w) ≤
        ricciTensor (scaleMetric q hq (H.event i).terminal.metric) (Φ tip)
          (mfderiv ThreeModel ThreeModel Φ tip w) (mfderiv ThreeModel ThreeModel Φ tip w) at hh
      rw [hd, ricciTensor_scaleMetric, scaleMetric_inner] at hh
      simpa only [mul_assoc] using hh
    have hconnected : IsPreconnected (range Φ) := by
      let : PreconnectedSpace (standardCapWindow D) := by
        apply isPreconnected_iff_preconnectedSpace.mp
        change IsPreconnected {x : ThreeSpace | ‖x‖ < D+1}
        simpa only [Metric.ball, dist_zero_right] using
          (convex_ball (0 : ThreeSpace) (D+1)).isPreconnected
      exact isPreconnected_range hΦ.contMDiff.continuous
    have hscalarouter : ∀ y ∈ range Φ, metricScalarAt h y ≤ Cs := by
      rintro _ ⟨x, rfl⟩
      have hscal := scalar_abs_le_rm (L.base.metric θ) x
      have hdim : Module.finrank ℝ (TangentSpace ThreeModel x) = 3 := by
        change Module.finrank ℝ ThreeSpace = 3
        simp [ThreeSpace]
      rw [hdim] at hscal
      have hnorm : Real.sqrt (normSq0S (L.base.metric θ) x 4 (metricRm04At (L.base.metric θ) x)) ≤
          Real.sqrt K := Real.sqrt_le_sqrt (hRm θ ⟨hθ.le, le_rfl⟩ x)
      have heq := (curvature_of_injective_local_isometry (L.base.metric θ) h Φ hΦ hΦinj hmet x).1
      rw [← heq]
      dsimp only [Cs]
      norm_num only [Nat.cast_ofNat, show (3 : ℝ)^2=9 by norm_num] at hscal
      nlinarith [le_abs_self (metricScalarAt (L.base.metric θ) x)]
    have hdiam : ∀ x ∈ range Φ, ∀ y ∈ range Φ,
        riemannianEDistOf h x y ≤ ENNReal.ofReal (4 * (D+1)) := by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      have hmapdist := edistOf_le_of_quad_of_localDiffeomorph (L.base.metric θ) h Φ hΦ
        (by norm_num : (0 : ℝ) < 1) (fun a v => by rw [← hmet]; simp only [one_mul]; rfl) x y
      have hlocaldist := hdist D _ θ hθdist (fun _ ht => ht) (fun _ ht => ht) L hL
        (fun x v => by rw [hLzero]; exact hupper x v) hcurv θ ⟨hθ.le, le_rfl⟩ x y
      have hx : ‖x.val‖ < D+1 := x.property
      have hy : ‖y.val‖ < D+1 := y.property
      simp only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hmapdist
      exact hmapdist.trans (hlocaldist.trans (ENNReal.ofReal_le_ofReal (by linarith)))
    have hcross := H.exists_regularCrossing_of_backwardSurvivor_initial_eq first last hle J i hf hl
      Ξ hbirth z endpoint Atrace hanchor
    have hscalarraw : ∀ y ∈ range Φ, metricScalarAt (H.event i).terminal.metric y ≤ Cs * q := by
      intro y hy
      have hh := hscalarouter y hy
      rw [metricScalarAt_scaleMetric, ← div_eq_inv_mul] at hh
      exact (div_le_iff₀ hq).mp hh
    have hKold := hprotect H i parameters (records i) (records i).old_eq_retained (hδ i hf hl)
      (range Φ) hconnected q hq hscalarraw hdiam (Φ tip) (mem_range_self tip) hRic
      (Φ z) (mem_range_self z) _ hcross
    obtain ⟨old, _, _, hcrossbad⟩ := (H.event i).exists_oldTerminal_eq_of_mem_interior_old
      (Φ xbad) (hKold (Φ xbad) (mem_range_self xbad))
    exact hbad ((H.event i).oldOutput old) hcrossbad
  have hF := H.backwardSurvivorMap_isSmoothEmbedding first last hle first le_rfl hle
  exact ⟨hF.lift J hsurvive, hF.isSmoothEmbedding_lift hJ (by simp) hsurvive,
    hF.comp_lift hsurvive⟩

theorem exists_uniform_incoming_cap_window_survival_time_of_radius_lower_bound_tube_C11SP
    (C₀ : ℝ) (C : ℝ≥0) (hC₀ : 0 < C₀) :
    ∃ η ε₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ D : ℝ, 65 ≤ D → ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ),
      4 ≤ m → ζ ≤ ε₀ →
      (∀ x : standardCapWindow D, ∀ v : TangentSpace ThreeModel x,
        w.windowMetric.inner x v v ≤ (3/2 : ℝ) * StandardCap.metric.inner x.val v v) →
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (J : standardCapWindow D → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
      ∀ (q q₀ a₀ : ℝ), 0 < q → 0 < q₀ → q₀ ≤ C₀ * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (J x) (mfderiv ThreeModel ThreeModel J x v)
          (mfderiv ThreeModel ThreeModel J x z)) →
      (∀ x, metricScalarAt (H.initialMetric first) (J x) ≤ C₀ * q) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H
          j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ δ₀) →
      ∀ (W : ∀ j : Fin (H.eventCount + 1), Set (H.stage j).Carrier), (∀ j, IsOpen (W j)) →
      (∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j), j ≤ last →
        ∀ (x : (H.stage j).Carrier) (A : BackwardPointTrace H first j hf x),
          A.point first le_rfl hf ∈ range J → x ∈ W j) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, x ∈ W j.castSucc →
        ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      (∀ x : (H.stage last).Carrier, x ∈ W last → ∀ t ∈ Ioo (H.time last) s,
        q₀ < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
      q * (s - H.time first) ≤ η →
      ∀ (z : standardCapWindow D) (endpoint : (H.stage last).Carrier)
        (A : BackwardPointTrace H first last hle endpoint), A.point first le_rfl hle = J z →
      ∃ Ψ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ψ ∧
        ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ψ x).val = J x := by
  obtain ⟨η₀, ε₀, hη₀, hε₀, hεhalf, hsurvive⟩ :=
    exists_uniform_cap_window_survival_time_of_radius_lower_bound_tube_C11SP C₀ C hC₀
  let η := min η₀ (8 * C * C₀ + 1)⁻¹
  have hη : 0 < η := lt_min hη₀ (by positivity)
  refine ⟨η, ε₀, hη, hε₀, hεhalf, ?_⟩
  intro D hD
  obtain ⟨δ₀, hδ₀, hsurvive⟩ := hsurvive D hD
  refine ⟨δ₀, hδ₀, ?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ hupper
    H first last hle s G hinit J hJ q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records
    hfixed hlower hδ W hW htube hderiv hfinal htime z endpoint Atrace hanchor
  have hprior : q * (H.time last - H.time first) ≤ η₀ :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_right G.lt.le _) hq.le).trans
      (htime.trans (min_le_left _ _))
  obtain ⟨Ψ, hΨ, hbirth⟩ := hsurvive w hm hζ hupper H first last hle J hJ
    q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records hfixed hlower hδ
    W hW htube hderiv
    hprior z endpoint Atrace hanchor
  have htime8 : 8 * C * (s - H.time first) * (C₀ * q) ≤ 1 := by
    have hh := htime.trans (min_le_right _ _)
    have hden : 0 < 8 * (C : ℝ) * C₀ + 1 := by positivity
    have hm := (le_div_iff₀ hden).mp (show q * (s - H.time first) ≤
      1 / (8 * (C : ℝ) * C₀ + 1) from by simpa only [one_div] using hh)
    have ht0 := (H.time_strictMono.monotone hle).trans G.lt.le
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr ht0)]
  have hregular (x : standardCapWindow D) : (Ψ x).val ∈ G.terminalRegularRegion := by
    let B : BackwardPointTrace H first last hle (Ψ x).val := Classical.choice (Ψ x).property
    have hB : B.point first le_rfl hle ∈ range J := by
      rw [← H.backwardSurvivorMap_eq_point first last hle first le_rfl hle (Ψ x) B, hbirth]
      exact mem_range_self x
    apply B.mem_incoming_terminalRegularRegion_of_initial_scalar_bound G hinit (Ψ x).val hq₀ hq₀Q
      (fun j hf hl => hderiv j hf hl _ (tube_trace_point_C11SP htube le_rfl B hB _ _ _))
      (hW last) (htube last hle le_rfl _ B hB)
      (fun y hy => hfinal y hy) ?_ htime8
    rw [← H.backwardSurvivorMap_eq_point first last hle first le_rfl hle (Ψ x) B, hbirth]
    exact hscalar x
  let Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G :=
    fun x => ⟨Ψ x, hregular x⟩
  exact ⟨Ξ, DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen ThreeModel ThreeModel
    (H.backwardSurvivorIncomingDomain first last hle G) Ξ hΨ, hbirth⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

section
open Set Function Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private local instance (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

theorem exists_uniform_cap_window_survival_step_of_standard_tip_metric_close_tube_C11SP
    (Θ Kpast C₀ : ℝ) (C : ℝ≥0) (hΘ : 0 ≤ Θ) (hΘ1 : Θ < 1) (hC₀ : 0 < C₀) :
    ∃ ε δstep : ℝ, 0 < ε ∧ 0 < δstep ∧ ∀ D : ℝ, 32 < D →
      ∃ η : ℝ, 0 < η ∧
      ∀ {E H₀ M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H₀ M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ),
      4 ≤ m → ζ ≤ 1 / 2 →
      (∀ x : standardCapWindow D, ∀ v : TangentSpace ThreeModel x,
        w.windowMetric.inner x v v ≤ (3 / 2 : ℝ) * StandardCap.metric.inner x.val v v) →
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (next : Fin H.eventCount) (hnext : first ≤ next.castSucc)
    (J : standardCapWindow D → (H.stage first).Carrier) (_ : IsSmoothEmbedding ThreeModel
        ThreeModel ∞ J)
    {τ : ℝ} (G : (H.stage next.castSucc).IncomingSlab (H.time next.castSucc) τ)
    (L : G.TerminalLimitMetric)
    (_ : ∀ t, G.flow.base.metric t = (H.event next).incoming.flow.base.metric t)
    (_ : L.metric =
      ((H.event next).incoming.flow.base.metric τ).restrictOpen G.terminalRegularOpen)
    (_ : τ ∈ Ico (H.time next.castSucc) (H.time next.succ))
    (Ψ : standardCapWindow D → H.backwardSurvivorIncomingDomain first next.castSucc hnext G)
    (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ)
    (_ : ∀ x, H.backwardSurvivorMap first next.castSucc hnext first le_rfl hnext
      (Ψ x).val = J x)
    (gflow₀ : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first next.castSucc hnext G))
    (_ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ next.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow₀ t = (H.backwardSurvivorSlabMetric first next.castSucc hnext j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first next.castSucc hnext G))
    (_ : ∀ t ∈ Icc (H.time next.castSucc) τ,
      gflow₀ t = H.backwardSurvivorIncomingMetric first next.castSucc hnext G L t)
    {r q a₀ : ℝ}
    (hq : 0 < q) (_ : r ≤ C₀ * q) (_ : 1 ≤ a₀ * q)
    (_ : ∀ x (v z : TangentSpace ThreeModel x),
      w.windowMetric.inner x v z = q * (H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x z))
    {D₀ : RealTimeInterval} (S₀ : SolutionOn (I := ThreeModel) (M := standardCapWindow D) D₀)
    (_ : ∀ t ∈ Icc 0 (q * (τ - H.time first)), S₀.base.metric t =
      localPullMetric (scaleMetric q hq (gflow₀ (H.time first + t / q))) Ψ hΨ)
    (_ : ∀ t ∈ Icc 0 (q * (τ - H.time first)), ∀ x : standardCapWindow D,
      normSq0S (S₀.base.metric t) x 4 (S₀.base.rm04 t x) ≤ Kpast)
    (_ : ∀ x, (H.event next).incoming.flow.scalar τ (Ψ x).val.val ≤ C₀ * q)
    (W : ∀ j : Fin (H.eventCount + 1), Set (H.stage j).Carrier) (_ : ∀ j, IsOpen (W j))
    (_ : ∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j), j ≤ last →
      ∀ (x : (H.stage j).Carrier) (A : BackwardPointTrace H first j hf x),
        A.point first le_rfl hf ∈ range J → x ∈ W j)
    (_ : ∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, x ∈ W j.castSucc →
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        r < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    (_ : ∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last →
      ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ), τ ≤ t →
        ∀ x : (H.stage j.castSucc).Carrier,
          InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) a₀ x),
      q * (H.time last - H.time first) ≤ Θ → q * (H.time last - τ) ≤ δstep →
      ∀ (Q : StandardSolution) (s₀ : ℝ), s₀ ∈ Icc 0 Θ →
      ∀ (tip : standardCapWindow D), tip.val = 0 →
      (∀ j ≤ 2, metricDerivNorm j (S₀.base.metric (q * (τ - H.time first)))
        ((Q.val.metric s₀).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) tip ≤ ε) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H
          j parameters),
      (∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta
          b ≤ η) →
      ∀ (z : standardCapWindow D) (endpoint : (H.stage last).Carrier)
        (Atrace : BackwardPointTrace H first last hle endpoint), Atrace.point first le_rfl hle = J
            z →
      ∃ Υ : standardCapWindow D → H.backwardSurvivorDomain first last hle,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Υ ∧
        ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Υ x) = J x := by
  let K := max Kpast ((2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2)
  obtain ⟨ε, σ, c, hε, hσ, hc, htip⟩ :=
    StandardCap.exists_uniform_window_tip_ricci_lower_bound_of_standard_metric_close Θ Θ K hΘ hΘ1
  let δstep := min σ (2 * ((C : ℝ) + 1) * C₀)⁻¹
  have hδstep : 0 < δstep := lt_min hσ (by positivity)
  have hprotect :=
    exists_cutoff_cap_survivor_partialDiffeomorph_of_window_flow_tip_ricci_lower_bound Θ K c hc
  refine ⟨ε, δstep, hε, hδstep, ?_⟩
  intro D hD
  obtain ⟨η, hη, hprotect⟩ := hprotect D (by linarith)
  refine ⟨η, hη, ?_⟩
  intro E H₀ M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ hupper
    H first last hle next hnext J hJ τ G L hsource hterminal hτ Ψ hΨ hΨbirth
    gflow₀ hslabs₀ hlast₀ r q a₀ hq hrQ haq hzero D₀ S₀ hmetric₀ hpast hscalar
    W hW htube hderiv hpinch hfulltime hremaining Q s₀ hs₀ tip htipzero hclose parameters records
    hdelta
    z endpoint Atrace hanchor
  have hbudget : 2 * C * C₀ * (q * (H.time last - τ)) ≤ 1 := by
    have hd := hremaining.trans (min_le_right _ _)
    have hp : 0 < 2 * ((C : ℝ) + 1) * C₀ := by positivity
    have hh := (le_div_iff₀ hp).mp (show q * (H.time last - τ) ≤ 1 / (2 * ((C : ℝ) + 1) * C₀) from
        by simpa only [one_div] using hd)
    by_cases ht : 0 ≤ q * (H.time last - τ)
    · nlinarith [mul_nonneg (show 0 ≤ 2 * C₀ by positivity) ht]
    · have htneg : q * (H.time last - τ) ≤ 0 := (lt_of_not_ge ht).le
      exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) htneg).trans (by norm_num)
  have hsurvive : range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle) := by
    by_contra hnot
    obtain ⟨i, hf, hni, hil, hpastStages, Ξ, hΞs, hbirth, hfailed, hΞ, gflow,
      hslabs, hlast, S, hS, hSzero, hmetric, hgram, hoverlap, hRm⟩ :=
      H.exists_first_event_normalized_chart_solution_of_scalar_bound_at_later_time_tube_C11SP
        first last hle next hnext J hJ G L hsource hterminal hτ Ψ hΨ hΨbirth
        gflow₀ hslabs₀ hlast₀ hC₀ hq hrQ haq w.windowMetric hzero S₀ hmetric₀ hpast
        hscalar W hW htube hderiv hpinch hbudget hnot
    let θ := q * (H.time i.succ - H.time first)
    let uτ := q * (τ - H.time first)
    have hθ : 0 < θ := mul_pos hq (sub_pos.mpr (H.time_strictMono (hf.trans_lt i.castSucc_lt_succ)))
    have hθΘ : θ ≤ Θ := (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (H.time_strictMono.monotone hil) _) hq.le).trans hfulltime
    have hτphys : τ < H.time i.succ := hτ.2.trans_le
      (H.time_strictMono.monotone (Fin.succ_le_succ_iff.mpr (Fin.castSucc_le_castSucc_iff.mp hni)))
    have huτ : uτ ∈ Icc 0 θ := by
      constructor
      · dsimp only [uτ]
        exact mul_nonneg hq.le (sub_nonneg.mpr ((H.time_strictMono.monotone hnext).trans hτ.1))
      · dsimp only [uτ, θ]
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right hτphys.le _) hq.le
    have hθstep : θ ≤ uτ + σ := by
      have hh := (mul_le_mul_of_nonneg_left (sub_le_sub_right (H.time_strictMono.monotone hil) τ)
          hq.le).trans hremaining
      have hh' := hh.trans (min_le_left _ _)
      dsimp only [θ, uτ]
      linarith
    have hcurv : ∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D,
        nablaKRm04NormSqIntrinsic S 0 t x ≤ K := by
      simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hRm
    have htipclose : ∀ j ≤ 2, metricDerivNorm j (S.base.metric uτ)
        ((Q.val.metric s₀).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) tip ≤ ε := by
      intro j hj
      rw [hoverlap uτ ⟨huτ.1, le_rfl⟩]
      exact hclose j hj
    have hRic := htip w hD hm hζ _ θ hθ hθΘ (fun _ h => h) (fun _ h => h)
      S hS hSzero hgram (fun t ht x _ => hcurv t ht x) uτ huτ Q s₀ hs₀ tip htipzero htipclose
      θ ⟨huτ.2, le_min hθstep le_rfl⟩
    let Φ := H.backwardSurvivorTerminalFaceMap first i hf ∘ Ξ
    have hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ :=
      isLocalDiffeomorph_comp (H.backwardSurvivorTerminalFaceMap_isLocalDiffeomorph first i hf) hΞ
    have hmet : S.base.metric θ = localPullMetric (scaleMetric q hq (H.event i).terminal.metric) Φ
        hΦ := by
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      rw [hmetric, show H.time first + θ / q = H.time i.succ by dsimp only [θ]; field_simp; ring,
        hlast _ ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩,
        H.backwardSurvivorTerminalFaceMetric_terminal]
      rw [localPullMetric_inner, scaleMetric_inner, localPullMetric_inner, localPullMetric_inner,
          scaleMetric_inner]
      rw [mfderiv_comp x
        ((H.backwardSurvivorTerminalFaceMap_isLocalDiffeomorph first i
            hf).contMDiff.mdifferentiableAt (by simp))
        (hΞ.contMDiff.mdifferentiableAt (by simp))]
      rfl
    have hcross := H.exists_regularCrossing_of_backwardSurvivor_initial_eq first last hle J i hf hil
      Ξ hbirth z endpoint Atrace hanchor
    obtain ⟨F, hFsource, hFcross, _, _, _⟩ := hprotect _ θ hθΘ (fun _ h => h) (fun _ h => h)
      S hS (by intro x v; rw [hSzero]; exact hupper x v) hcurv θ ⟨hθ.le, le_rfl⟩
      H i parameters (records i) (records i).old_eq_retained (hdelta i hni hil)
      Φ hΦ q hq hmet tip hRic z _ hcross
    obtain ⟨xbad, hbad⟩ := hfailed
    exact hbad (F (Φ xbad)) (hFcross (Φ xbad) (hFsource (mem_range_self xbad)))
  have hF := H.backwardSurvivorMap_isSmoothEmbedding first last hle first le_rfl hle
  exact ⟨hF.lift J hsurvive, hF.isSmoothEmbedding_lift hJ (by simp) hsurvive,
    hF.comp_lift hsurvive⟩

/-- 树内长标识符（105 字符）的局部别名，只为行宽 ≤ 100；展开即
`HistorySurvivorInitialCurvature:1323` 的原名（`…_chart_…_of_earlier_scalar_bound_at_time`）。 -/
local macro "earlierScalarChart%" : term =>
  `($(Lean.mkIdent (Lean.Name.mkSimple
    ("exists_normalized_backwardSurvivorIncoming_chart_solution_curvature_bound_" ++
      "of_earlier_scalar_bound_at_time"))))

theorem exists_uniform_incoming_cap_window_step_of_standard_tip_metric_close_tube_C11SP
    (Θ Kpast C₀ : ℝ) (C : ℝ≥0) (hΘ : 0 ≤ Θ) (hΘ1 : Θ < 1) (hC₀ : 0 < C₀) :
    ∃ ε δstep : ℝ, 0 < ε ∧ 0 < δstep ∧ ∀ D : ℝ, 32 < D →
      ∃ η : ℝ, 0 < η ∧
      ∀ {E H₀ M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H₀ M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ),
      4 ≤ m → ζ ≤ 1 / 2 →
      (∀ x : standardCapWindow D, ∀ v : TangentSpace ThreeModel x,
        w.windowMetric.inner x v v ≤ (3 / 2 : ℝ) * StandardCap.metric.inner x.val v v) →
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (next : Fin H.eventCount) (hnext : first ≤ next.castSucc) (hnextlast : next.succ ≤ last)
    (J : standardCapWindow D → (H.stage first).Carrier) (_ : IsSmoothEmbedding ThreeModel
        ThreeModel ∞ J)
    {τ : ℝ} (G : (H.stage next.castSucc).IncomingSlab (H.time next.castSucc) τ)
    (L : G.TerminalLimitMetric)
    (_ : ∀ t, G.flow.base.metric t = (H.event next).incoming.flow.base.metric t)
    (_ : L.metric =
      ((H.event next).incoming.flow.base.metric τ).restrictOpen G.terminalRegularOpen)
    (_ : τ ∈ Ico (H.time next.castSucc) (H.time next.succ))
    (Ψ : standardCapWindow D → H.backwardSurvivorIncomingDomain first next.castSucc hnext G)
    (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ)
    (_ : ∀ x, H.backwardSurvivorMap first next.castSucc hnext first le_rfl hnext
      (Ψ x).val = J x)
    (gflow₀ : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first next.castSucc hnext G))
    (_ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ next.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow₀ t = (H.backwardSurvivorSlabMetric first next.castSucc hnext j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first next.castSucc hnext G))
    (_ : ∀ t ∈ Icc (H.time next.castSucc) τ,
      gflow₀ t = H.backwardSurvivorIncomingMetric first next.castSucc hnext G L t)
    {r q a₀ : ℝ}
    (hq : 0 < q) (_ : r ≤ C₀ * q) (_ : 1 ≤ a₀ * q)
    (_ : ∀ x (v z : TangentSpace ThreeModel x),
      w.windowMetric.inner x v z = q * (H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x z))
    {D₀ : RealTimeInterval} (S₀ : SolutionOn (I := ThreeModel) (M := standardCapWindow D) D₀)
    (_ : ∀ t ∈ Icc 0 (q * (τ - H.time first)), S₀.base.metric t =
      localPullMetric (scaleMetric q hq (gflow₀ (H.time first + t / q))) Ψ hΨ)
    (_ : ∀ t ∈ Icc 0 (q * (τ - H.time first)), ∀ x : standardCapWindow D,
      normSq0S (S₀.base.metric t) x 4 (S₀.base.rm04 t x) ≤ Kpast)
    (_ : ∀ x, (H.event next).incoming.flow.scalar τ (Ψ x).val.val ≤ C₀ * q)
    (W : ∀ j : Fin (H.eventCount + 1), Set (H.stage j).Carrier) (_ : ∀ j, IsOpen (W j))
    (_ : ∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j), j ≤ last →
      ∀ (x : (H.stage j).Carrier) (A : BackwardPointTrace H first j hf x),
        A.point first le_rfl hf ∈ range J → x ∈ W j)
    (_ : ∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, x ∈ W j.castSucc →
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        r < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    {s : ℝ} (Gfinal : (H.stage last).IncomingSlab (H.time last) s)
    (Lfinal : Gfinal.TerminalLimitMetric)
    (_ : Gfinal.flow.base.metric (H.time last) = H.initialMetric last)
    (_ : ∀ x : (H.stage last).Carrier, x ∈ W last → ∀ t ∈ Ioo (H.time last) s,
      r < Gfinal.flow.scalar t x →
      |derivWithin (fun v => Gfinal.flow.scalar v x) (Iic t) t| ≤ C * Gfinal.flow.scalar t x ^ 2),
      q * (s - H.time first) ≤ Θ → q * (s - τ) ≤ δstep →
      ∀ (Q : StandardSolution) (s₀ : ℝ), s₀ ∈ Icc 0 Θ →
      ∀ (tip : standardCapWindow D), tip.val = 0 →
      (∀ j ≤ 2, metricDerivNorm j (S₀.base.metric (q * (τ - H.time first)))
        ((Q.val.metric s₀).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) tip ≤ ε) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H
          j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta
          b ≤ η) →
      ∀ (z : standardCapWindow D) (endpoint : Gfinal.terminalRegularOpen)
        (Atrace : BackwardPointTrace H first last hle endpoint.val), Atrace.point first le_rfl hle
            = J z →
      ∃ (Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle Gfinal),
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
        (∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ x).val = J x) ∧
        H.backwardSurvivorIncomingMap first last hle Gfinal (Ξ z) = endpoint ∧
        ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
          (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first
              last hle Gfinal)),
          (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
            ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
              gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
                (H.backwardSurvivorIncomingDomain first last hle Gfinal)) ∧
          (∀ t ∈ Icc (H.time last) s,
            gflow t = H.backwardSurvivorIncomingMetric first last hle Gfinal Lfinal t) ∧
          ∃ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
              (RealTimeInterval.closed 0 (q * (s - H.time first))
                (by have ht := (H.time_strictMono.monotone hle).trans_lt Gfinal.lt; positivity)),
            IsSolutionOn S ∧ S.base.metric 0 = w.windowMetric ∧
            (∀ t, S.base.metric t =
              localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) ∧
            (∀ (x : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
              ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
                (fun z : ℝ × standardCapWindow D => chartGramMatrix (S.base.metric z.1) x z.2 i j)
                (Icc 0 (q * (s - H.time first)) ×ˢ
                  (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).baseSet)) ∧
            (∀ t ∈ Icc 0 (q * (τ - H.time first)), S.base.metric t = S₀.base.metric t) ∧
            ∀ t ∈ Icc 0 (q * (s - H.time first)), ∀ x : standardCapWindow D,
              normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤
                max Kpast ((2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2) := by
  obtain ⟨ε, δsurvive, hε, hδsurvive, hsurvive⟩ :=
    exists_uniform_cap_window_survival_step_of_standard_tip_metric_close_tube_C11SP
    Θ Kpast C₀ C hΘ hΘ1 hC₀
  let δstep := min δsurvive (2 * ((C : ℝ) + 1) * C₀)⁻¹
  have hδstep : 0 < δstep := lt_min hδsurvive (by positivity)
  refine ⟨ε, δstep, hε, hδstep, ?_⟩
  intro D hD
  obtain ⟨η, hη, hsurvive⟩ := hsurvive D hD
  refine ⟨η, hη, ?_⟩
  intro E H₀ M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ hupper
    H first last hle next hnext hnextlast J hJ τ G L hsource hterminal hτ Ψ hΨ hΨbirth
    gflow₀ hslabs₀ hlast₀ r q a₀ hq hrQ haq hzero D₀ S₀ hmetric₀ hpast hscalar W hW htube hderiv
    s Gfinal Lfinal hinit hfinal hfulltime hremaining Q s₀ hs₀ tip htipzero hclose
    parameters records hfixed hlower hdelta z endpoint Atrace hanchor
  have hbudget : 2 * C * C₀ * (q * (s - τ)) ≤ 1 := by
    have hd := hremaining.trans (min_le_right _ _)
    have hp : 0 < 2 * ((C : ℝ) + 1) * C₀ := by positivity
    have hh := (le_div_iff₀ hp).mp
      (show q * (s - τ) ≤ 1 / (2 * ((C : ℝ) + 1) * C₀) from by
        simpa only [one_div] using hd)
    have hτs : τ < s := hτ.2.trans_le (H.time_strictMono.monotone hnextlast) |>.trans Gfinal.lt
    have ht : 0 ≤ q * (s - τ) := mul_nonneg hq.le (sub_nonneg.mpr hτs.le)
    nlinarith [mul_nonneg (show 0 ≤ 2 * C₀ by positivity) ht]
  have ha₀ : 0 < a₀ := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h hq.le
    linarith
  have hp := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hlower
  have hpinch (j : Fin H.eventCount) (_ : next.castSucc ≤ j.castSucc) (_ : j.succ ≤ last)
      (t : ℝ) (ht : t ∈ Ico (H.time j.castSucc) (H.time j.succ)) (_ : τ ≤ t)
      (x : (H.stage j.castSucc).Carrier) :
      InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) a₀ x := by
    have ht0 : 0 ≤ t := (H.time_nonneg j.castSucc).trans ht.1
    have hstage : t ∈ H.stageDomain j.castSucc := by
      simpa only [stageDomain, Fin.lastCases_castSucc] using ht
    have hregion : InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) (a₀ + t)
        x := by
      simpa only [stageMetric, Fin.lastCases_castSucc] using (hp.1 j.castSucc t hstage x).1
    apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ a₀ x).mpr
    exact fixedHamiltonIveyRegion_antitoneOn ha₀ (by linarith : 0 < a₀ + t) (by linarith)
      ((inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion _ (a₀ + t) x).mp hregion)
  have hfull : q * (H.time last - H.time first) ≤ Θ :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_right Gfinal.lt.le _) hq.le).trans hfulltime
  have hremain : q * (H.time last - τ) ≤ δsurvive :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_right Gfinal.lt.le _) hq.le).trans
      (hremaining.trans (min_le_left _ _))
  obtain ⟨Υ, hΥs, hΥbirth⟩ := hsurvive w hm hζ hupper H first last hle next hnext J hJ
    G L hsource hterminal hτ Ψ hΨ hΨbirth gflow₀ hslabs₀ hlast₀ hq hrQ haq hzero
    S₀ hmetric₀ hpast hscalar W hW htube hderiv hpinch hfull hremain Q s₀ hs₀ tip htipzero hclose
    parameters records hdelta z endpoint.val Atrace hanchor
  have hΥ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Υ := fun x =>
    Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq rfl
      (hΥs.isImmersion.isImmersionAt x)
  have hscalarΥ (x : standardCapWindow D) :
      (H.event next).incoming.flow.scalar τ
        (H.backwardSurvivorMap first last hle next.castSucc hnext
          (next.castSucc_lt_succ.le.trans hnextlast) (Υ x)) ≤ C₀ * q := by
    have he := H.backwardSurvivorMap_eq_of_initial_eq first next.castSucc last hnext hle
      (Ψ x).val (Υ x) ((hΨbirth x).trans (hΥbirth x).symm) next.castSucc hnext le_rfl
      (next.castSucc_lt_succ.le.trans hnextlast)
    have hp : (Ψ x).val.val = H.backwardSurvivorMap first last hle next.castSucc hnext
        (next.castSucc_lt_succ.le.trans hnextlast) (Υ x) := by
      simpa only [H.backwardSurvivorMap_last] using he
    rw [← hp]
    exact hscalar x
  obtain ⟨Ξ, hΞ, hprojection, hbirth, gflow, hslabs, hlast, S, hS, hSzero,
    hmetric, hgram, hoverlap, hRm⟩ :=
    (earlierScalarChart%)
      Gfinal Lfinal hinit Υ hΥ next hnext hnextlast hC₀ hq hrQ haq hτ
      (fun x j hj hl => hderiv j hj hl _
        (tube_survivor_C11SP htube le_rfl (Υ x) ⟨x, (hΥbirth x).symm⟩ _ _ _))
      (fun x => hfinal (Υ x).val (tube_survivor_last_C11SP htube le_rfl (Υ x) ⟨x, (hΥbirth
          x).symm⟩))
      hscalarΥ hbudget
      J hΥbirth w.windowMetric hzero records hfixed hlower G L hsource hterminal
      Ψ hΨ hΨbirth gflow₀ hslabs₀ hlast₀ S₀ hmetric₀ hpast
  have hΞs : IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen ThreeModel ThreeModel
      (H.backwardSurvivorIncomingDomain first last hle Gfinal) Ξ
      (by
        have he : Subtype.val ∘ Ξ = Υ := funext hprojection
        rw [he]
        exact hΥs)
  have hpoint : H.backwardSurvivorIncomingMap first last hle Gfinal (Ξ z) = endpoint :=
    H.backwardSurvivorIncomingMap_eq_of_initial_point_eq first last hle Gfinal J Ξ hbirth
      endpoint Atrace z hanchor.symm
  exact ⟨Ξ, hΞs, hbirth, hpoint, hΞ, gflow, hslabs, hlast, S, hS, hSzero,
    hmetric, hgram, hoverlap, hRm⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

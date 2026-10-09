import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceNecks

/-!
# L6-A 第 1 层：`ClosedSlab.nonempty_scaled_spatialNeck_of_minimizing_segment` 的局部化（`_P6L`）

局部化合同 `docs/geometrization/chapter8/design-C11-P6-localization-contract-20261006.md` §1–§2：
原定理 `ST/BoundedCurvatureAtDistanceNecks.lean:109` 的前提 `hW : ∀ y, q < R_b(y) → ∃ W …`（slice 上全局）
在证明里只于 `y = (γ t).val` 求值一次（原 l.145）。这里把它换成该点的单个 witness `hWt`（`q`、`hq` 一并去掉），
证明体照抄。这是最一般的局部化：区域形 (W) `∀ y ∈ U, q < R → …` 在 `(γ t).val ∈ U` 时直接给 `hWt`。
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Manifold ContDiff ENNReal Topology NNReal

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {P : OrientedThreeStage.{u}} {a b : ℝ}

private local instance (A : P.ClosedSlab a b) :
    SigmaCompactSpace (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen.isOpen)

/-- **`_P6L`**：原 `ClosedSlab.nonempty_scaled_spatialNeck_of_minimizing_segment`（`Necks:109`），
全局 `hW` 换成 `(γ t).val` 处的单个 witness `hWt`；其余前提与结论逐字。 -/
theorem ClosedSlab.nonempty_scaled_spatialNeck_of_minimizing_segment_P6L (A : P.ClosedSlab a b)
    {eps C1 C2 alpha Q : ℝ} (hQ : 0 < Q) (halpha : alpha < 1 / 11)
    (heps : 13000 * (13000 * eps) ≤ alpha)
    {γ : ℝ → (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen} {l t r : ℝ}
    (hlt : l < t) (htr : t < r)
    (hmin : ∀ s ∈ Icc l r, ∀ v ∈ Icc l r, riemannianEDistOf
      (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) (γ s) (γ v) =
        ENNReal.ofReal |s - v|)
    (hWt : ∃ W : SpatialCanonicalWitness (A.flow.base.metric b) eps C1 C2 (γ t).val,
      W.capTubeHasNeckChart eps)
    (hleft : C2 * A.flow.scalar b (γ l).val < A.flow.scalar b (γ t).val)
    (hright : C2 * A.flow.scalar b (γ t).val < A.flow.scalar b (γ r).val) :
    Nonempty (SpatialNeck (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric)
      alpha (γ t)) := by
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  let γc : ℝ → P.Carrier := fun v => (γ (Real.sqrt Q * v)).val
  have hmem (v : ℝ) (hv : v ∈ Icc (l / Real.sqrt Q) (r / Real.sqrt Q)) :
      Real.sqrt Q * v ∈ Icc l r := by
    constructor
    · have := (div_le_iff₀ hs).mp hv.1
      linarith
    · have := (le_div_iff₀ hs).mp hv.2
      linarith
  have hmin' : ∀ s ∈ Icc (l / Real.sqrt Q) (r / Real.sqrt Q),
      ∀ v ∈ Icc (l / Real.sqrt Q) (r / Real.sqrt Q),
        riemannianEDistOf (A.flow.base.metric b) (γc s) (γc v) = ENNReal.ofReal |s - v| := by
    intro s hsI v hvI
    have h := hmin _ (hmem s hsI) _ (hmem v hvI)
    rw [DifferentialGeometry.edistOf_scale, A.riemannianEDistOf_endpointTerminalLimitMetric,
      ← mul_sub, abs_mul, abs_of_pos hs, ENNReal.ofReal_mul hs.le] at h
    exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top).mp h
  have hts : Real.sqrt Q * (t / Real.sqrt Q) = t := mul_div_cancel₀ t hs.ne'
  have hls : Real.sqrt Q * (l / Real.sqrt Q) = l := mul_div_cancel₀ l hs.ne'
  have hrs : Real.sqrt Q * (r / Real.sqrt Q) = r := mul_div_cancel₀ r hs.ne'
  obtain ⟨W, hWn⟩ := hWt
  obtain ⟨nk⟩ := W.nonempty_spatialNeck_of_minimizing_segment hWn halpha heps
    (a := l / Real.sqrt Q) (t := t / Real.sqrt Q) (b := r / Real.sqrt Q) (γ := γc)
    (div_lt_div_of_pos_right hlt hs) (div_lt_div_of_pos_right htr hs) hmin'
    (by simp only [γc, hts]) (by simp only [γc, hls]; exact hleft)
    (by simp only [γc, hrs]; exact hright)
  have hU : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion = univ :=
    A.terminalRegularRegion_eq_univ P
  exact ⟨(nk.restrictOpen (U := (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen)
    (x := γ t) (fun y _ => by
      change y ∈ (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion
      rw [hU]
      trivial)).scaleMetric Q hQ⟩


/-- consumer：原定理（全局 `hW` 形）由 `_P6L` 版推出——局部化只是推广。 -/
example (A : P.ClosedSlab a b) {eps C1 C2 alpha q Q : ℝ} (hQ : 0 < Q) (halpha : alpha < 1 / 11)
    (heps : 13000 * (13000 * eps) ≤ alpha)
    (hW : ∀ y, q < A.flow.scalar b y →
      ∃ W : SpatialCanonicalWitness (A.flow.base.metric b) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    {γ : ℝ → (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen} {l t r : ℝ}
    (hlt : l < t) (htr : t < r)
    (hmin : ∀ s ∈ Icc l r, ∀ v ∈ Icc l r, riemannianEDistOf
      (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) (γ s) (γ v) =
        ENNReal.ofReal |s - v|)
    (hq : q < A.flow.scalar b (γ t).val)
    (hleft : C2 * A.flow.scalar b (γ l).val < A.flow.scalar b (γ t).val)
    (hright : C2 * A.flow.scalar b (γ t).val < A.flow.scalar b (γ r).val) :
    Nonempty (SpatialNeck (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric)
      alpha (γ t)) :=
  A.nonempty_scaled_spatialNeck_of_minimizing_segment_P6L hQ halpha heps hlt htr hmin
    (hW _ hq) hleft hright

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

import DifferentialGeometry.Geometry.Metric.Construction.SmoothMetricFromCoefficients

/-!
# F4-a（`_F4A`）模块 1：模型空间 `E` 上由局部度量系数做 cutoff 得到的全局光滑度量

F4-a 需要把 atlas chart `e ∈ 𝒜` 下的 Morrey 盘 `e ∘ F` 看成"模型空间 `E` 里的调和映射"（`chartAt = refl`），
以便复用树里只对 `chartAt E p` 成立的 tangent-graph 机器。这需要一个**全局**光滑度量 `g'`，在
目标点附近等于 chart `e` 下的度量系数。

* `exists_modelMetric_F4A`：`C^∞` 的对称正定双线性型族 ⇒ `SmoothRiemannianMetric 𝓘(ℝ, E) E`
  （`smoothMetric_of_localCoeff`）。
* `stdForm_F4A`：固定的正定对称型 `∑ coord_i ⊗ coord_i`。
* `exists_cutoff_form_F4A`：只在开集 `W ⊇ closedBall c r'` 上光滑正定的型族，用 `ContDiffBump` 延拓成全局光滑正定
  对称型族，在 `closedBall c r` 上与原族相等。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold Bundle Metric
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- 模型空间 `E` 上的全局光滑度量：由 `C^∞` 的对称正定双线性型族 `b` 给出。 -/
theorem exists_modelMetric_F4A (b : E → E →L[ℝ] E →L[ℝ] ℝ) (hb : ContDiff ℝ ∞ b)
    (hsymm : ∀ y v w, b y v w = b y w v) (hpos : ∀ y v, v ≠ 0 → 0 < b y v v) :
    ∃ g : SmoothRiemannianMetric 𝓘(ℝ, E) E, ∀ y v w, g.inner y v w = b y v w := by
  refine smoothMetric_of_localCoeff (I := 𝓘(ℝ, E)) (M := E) b hsymm hpos ?_
  intro x₀ i j
  have hframe : ∀ (x : E) (i : Fin (Module.finrank ℝ E)),
      frameVec (I := 𝓘(ℝ, E)) (M := E) x₀ i x = Module.finBasis ℝ E i := by
    intro x i
    unfold frameVec
    simp
    rfl
  have hc : ContDiff ℝ ∞ (fun x : E => b x (Module.finBasis ℝ E i) (Module.finBasis ℝ E j)) :=
    ((hb.clm_apply contDiff_const).clm_apply contDiff_const)
  refine (hc.contMDiff.contMDiffOn
    (s := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet)).congr (fun x _ => ?_)
  simp only [hframe]
  rfl

/-- 固定的正定对称双线性型 `δ v w = ∑ coord_i v * coord_i w`。 -/
def stdForm_F4A (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)).smulRight
    (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i))

theorem stdForm_F4A_apply (v w : E) :
    stdForm_F4A E v w = ∑ i, (Module.finBasis ℝ E).coord i v * (Module.finBasis ℝ E).coord i w := by
  simp [stdForm_F4A]

theorem stdForm_F4A_symm (v w : E) : stdForm_F4A E v w = stdForm_F4A E w v := by
  rw [stdForm_F4A_apply, stdForm_F4A_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem stdForm_F4A_pos {v : E} (hv : v ≠ 0) : 0 < stdForm_F4A E v v := by
  rw [stdForm_F4A_apply]
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
      0 ≤ (Module.finBasis ℝ E).coord i v * (Module.finBasis ℝ E).coord i v :=
    fun i _ => mul_self_nonneg _
  obtain ⟨i, hi⟩ : ∃ i, (Module.finBasis ℝ E).coord i v ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    have := (Module.finBasis ℝ E).sum_repr v
    rw [← this]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := h i
    simp only [Module.Basis.coord_apply] at this
    simp [this]
  exact lt_of_lt_of_le (mul_self_pos.mpr hi)
    (Finset.single_le_sum hnn (Finset.mem_univ i))

/-- 用光滑 bump 把只在开集 `W ⊇ closedBall c r'` 上光滑正定的双线性型族 `b₀` 延拓成全局的
光滑正定对称型族，在 `closedBall c r` 上与 `b₀` 相等。 -/
theorem exists_cutoff_form_F4A {W : Set E} (hW : IsOpen W) {c : E} {r r' : ℝ} (hr : 0 < r)
    (hrr' : r < r') (hsub : closedBall c r' ⊆ W) {b₀ : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hb₀ : ContDiffOn ℝ ∞ b₀ W) (hsymm : ∀ y ∈ W, ∀ v w, b₀ y v w = b₀ y w v)
    (hpos : ∀ y ∈ W, ∀ v, v ≠ 0 → 0 < b₀ y v v) :
    ∃ b : E → E →L[ℝ] E →L[ℝ] ℝ, ContDiff ℝ ∞ b ∧ (∀ y v w, b y v w = b y w v) ∧
      (∀ y v, v ≠ 0 → 0 < b y v v) ∧ ∀ y ∈ closedBall c r, b y = b₀ y := by
  let ψ : ContDiffBump c := ⟨r, r', hr, hrr'⟩
  refine ⟨fun y => ψ y • b₀ y + (1 - ψ y) • stdForm_F4A E, ?_, ?_, ?_, ?_⟩
  · refine ContDiff.add ?_ ((contDiff_const.sub ψ.contDiff).smul contDiff_const)
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ closedBall c r'
    · exact ψ.contDiff.contDiffAt.smul ((hb₀.contDiffAt (hW.mem_nhds (hsub hy))))
    · have hy' : y ∈ (closedBall c r')ᶜ := hy
      have hnhds : (closedBall c r')ᶜ ∈ 𝓝 y := isClosed_closedBall.isOpen_compl.mem_nhds hy'
      refine (contDiffAt_const (c := (0 : E →L[ℝ] E →L[ℝ] ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with z hz
      have hz' : r' ≤ dist z c := by
        rw [mem_compl_iff, mem_closedBall, not_le] at hz
        exact hz.le
      simp [ψ.zero_of_le_dist hz']
  · intro y v w
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [stdForm_F4A_symm v w]
    by_cases hy : y ∈ W
    · rw [hsymm y hy v w]
    · have : ψ y = 0 := ψ.zero_of_le_dist (by
        have : y ∉ closedBall c r' := fun h => hy (hsub h)
        rw [mem_closedBall, not_le] at this
        exact this.le)
      simp [this]
  · intro y v hv
    simp only [add_apply, smul_apply, smul_eq_mul]
    have h1 : 0 ≤ ψ y := ψ.nonneg
    have h2 : 0 ≤ 1 - ψ y := sub_nonneg.mpr ψ.le_one
    have hδ := stdForm_F4A_pos hv
    by_cases hy : y ∈ W
    · have hb := hpos y hy v hv
      by_cases hψ : ψ y = 0
      · rw [hψ]; simpa using hδ
      · have : 0 < ψ y := lt_of_le_of_ne h1 (Ne.symm hψ)
        exact add_pos_of_pos_of_nonneg (mul_pos this hb) (mul_nonneg h2 hδ.le)
    · have : ψ y = 0 := ψ.zero_of_le_dist (by
        have : y ∉ closedBall c r' := fun h => hy (hsub h)
        rw [mem_closedBall, not_le] at this
        exact this.le)
      rw [this]; simpa using hδ
  · intro y hy
    have : ψ y = 1 := ψ.one_of_mem_closedBall hy
    simp [this]

end DifferentialGeometry.Geometry

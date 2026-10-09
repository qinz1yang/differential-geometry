import DifferentialGeometry.Geometry.Analytic.ChartIndependenceF3A

/-!
# F3-a：analytic metric 的 Christoffel 系数 analytic（O-MY-F3A G2b，后缀 `_F3A`）

R8-AR 的 analytic `Γ` 来源链（ANDIG §D(5)(ii) 的核对）：
`IsAnalyticMetricOn_F3A`（chart 系数 analytic）
→ Gram 矩阵 `metricGram_F3A` 的 entries analytic、`det ≠ 0`（`G` 正定 + `D(e.symm)` 单射）
→ 逆矩阵 entries analytic（`Matrix.inv_def` = `Ring.inverse det • adjugate`；`det`/`adjugate` 是
  entries 的多项式）
→ `AnalyticOnNhd.fderiv` 给系数的偏导 analytic
→ `christoffel_F3A G e b i j k` 在 `e '' (P ∩ e.source)` 上 `AnalyticOnNhd`。
与树里 `chartChristoffel`（`extChartAt` 版）的对齐见 `ChristoffelBridgeF3A.lean`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Analytic

section Matrix

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι]

/-- entries 解析 ⇒ `det` 解析（`Matrix.det_apply'`：entries 的多项式）。 -/
theorem analyticAt_det_F3A {A : E → Matrix ι ι ℝ} {y : E}
    (h : ∀ i j, AnalyticAt ℝ (fun z => A z i j) y) : AnalyticAt ℝ (fun z => (A z).det) y := by
  simp_rw [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h (σ i) i)

/-- entries 解析、`det ≠ 0` ⇒ 逆矩阵 entries 解析（`A⁻¹ = Ring.inverse det • adjugate`）。 -/
theorem analyticAt_inv_apply_F3A {A : E → Matrix ι ι ℝ} {y : E}
    (h : ∀ i j, AnalyticAt ℝ (fun z => A z i j) y) (hdet : (A y).det ≠ 0) (k l : ι) :
    AnalyticAt ℝ (fun z => (A z)⁻¹ k l) y := by
  have hadj : AnalyticAt ℝ (fun z => (A z).adjugate k l) y := by
    simp_rw [Matrix.adjugate_apply]
    refine analyticAt_det_F3A fun i j => ?_
    simp_rw [Matrix.updateRow_apply]
    split_ifs
    · exact analyticAt_const
    · exact h i j
  have hinv : AnalyticAt ℝ (fun z => Ring.inverse (A z).det) y := by
    simp_rw [Ring.inverse_eq_inv']
    exact (analyticAt_det_F3A h).inv hdet
  have heq : (fun z => (A z)⁻¹ k l) = fun z => Ring.inverse (A z).det * (A z).adjugate k l := by
    funext z
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  rw [heq]
  exact hinv.mul hadj

end Matrix

section Christoffel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- chart `e` 中、相对 basis `b` 的 Gram 矩阵 `g_{ij}(y) = metricCoeff_F3A G e (b i) (b j) y`。 -/
def metricGram_F3A {ι : Type*} (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : OpenPartialHomeomorph M E) (b : Module.Basis ι ℝ E) (y : E) : Matrix ι ι ℝ :=
  Matrix.of fun i j => metricCoeff_F3A G e (b i) (b j) y

/-- chart `e` 中、相对 basis `b` 的第二类 Christoffel 系数
`Γ^k_{ij} = ½ ∑_l g^{kl} (∂_i g_{lj} + ∂_j g_{li} − ∂_l g_{ij})`（`∂_i = fderiv · · (b i)`；
与树里 `chartChristoffel` 同一公式）。 -/
def christoffel_F3A {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (e : OpenPartialHomeomorph M E)
    (b : Module.Basis ι ℝ E) (i j k : ι) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, (metricGram_F3A G e b y)⁻¹ k l *
    (fderiv ℝ (metricCoeff_F3A G e (b l) (b j)) y (b i) +
      fderiv ℝ (metricCoeff_F3A G e (b l) (b i)) y (b j) -
      fderiv ℝ (metricCoeff_F3A G e (b i) (b j)) y (b l))

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- maximal `C^∞` atlas 的 chart：`D(e.symm)_y` 在 `y ∈ e.target` 单射。 -/
theorem mfderiv_symm_injective_F3A {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E} (hy : y ∈ e.target) :
    Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y) := by
  have he1 := IsManifold.maximalAtlas_subset_of_le (ENat.LEInfty.out : (1 : ℕ∞ω) ≤ ∞) he
  have hmd : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨fun x hx => (mdifferentiableAt_of_mem_maximalAtlas he1 hx).mdifferentiableWithinAt,
      fun z hz => (mdifferentiableAt_symm_of_mem_maximalAtlas he1 hz).mdifferentiableWithinAt⟩
  exact hmd.symm.mfderiv_injective hy

/-- Gram 矩阵在 `e.target` 上可逆（`G` 正定、`D(e.symm)` 单射）。 -/
theorem metricGram_F3A_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (b : Module.Basis ι ℝ E) {y : E}
    (hy : y ∈ e.target) : (metricGram_F3A G e b y).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set w : E := ∑ i, v i • b i with hw
  have hrepr : b.repr w = v := by
    ext i
    rw [hw, b.repr_sum_self]
  have hw0 : w ≠ 0 := by
    intro h0
    apply hv
    rw [← hrepr, h0, map_zero]
    rfl
  have hquad : metricCoeff_F3A G e w w y = dotProduct v ((metricGram_F3A G e b y).mulVec v) := by
    rw [metricCoeff_F3A_eq_sum_basis G e b, hrepr]
    simp only [dotProduct, Matrix.mulVec, metricGram_F3A, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hpos : 0 < metricCoeff_F3A G e w w y :=
    G.pos _ _ fun h0 => hw0 (mfderiv_symm_injective_F3A he hy (h0.trans (map_zero _).symm))
  rw [hquad, hMv, dotProduct_zero] at hpos
  exact lt_irrefl 0 hpos

/-- **analytic Γ**：`G` 在 `P`（开）上对 compatible atlas `𝒜` 解析 ⇒ 每个 chart `e ∈ 𝒜` 中
Christoffel 系数在 `e '' (P ∩ e.source)` 上 `AnalyticOnNhd`。 -/
theorem IsAnalyticMetricOn_F3A.analyticOnNhd_christoffel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {𝒜 : Set (OpenPartialHomeomorph M E)} {P : Set M} {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : IsAnalyticMetricOn_F3A 𝒜 P G) (hP : IsOpen P)
    (h𝒜 : ∀ e ∈ 𝒜, e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {e : OpenPartialHomeomorph M E}
    (he : e ∈ 𝒜) (b : Module.Basis ι ℝ E) (i j k : ι) :
    AnalyticOnNhd ℝ (christoffel_F3A G e b i j k) (e '' (P ∩ e.source)) := by
  have hopen : IsOpen (e '' (P ∩ e.source)) :=
    e.isOpen_image_of_subset_source (hP.inter e.open_source) inter_subset_right
  have hG' : ∀ ξ η : E, AnalyticOnNhd ℝ (metricCoeff_F3A G e ξ η) (e '' (P ∩ e.source)) :=
    fun ξ η => hopen.analyticOn_iff_analyticOnNhd.mp (hG e he ξ η)
  have hD : ∀ (ξ η v : E), AnalyticOnNhd ℝ (fun z => fderiv ℝ (metricCoeff_F3A G e ξ η) z v)
      (e '' (P ∩ e.source)) := fun ξ η v z hz =>
    ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt _).comp ((hG' ξ η).fderiv z hz)
  intro y hy
  have hyt : y ∈ e.target := by
    obtain ⟨x, ⟨-, hxe⟩, rfl⟩ := hy
    exact e.map_source hxe
  have hinv : ∀ l, AnalyticAt ℝ (fun z => (metricGram_F3A G e b z)⁻¹ k l) y := fun l =>
    analyticAt_inv_apply_F3A (fun i' j' => hG' (b i') (b j') y hy)
      (metricGram_F3A_det_ne_zero G (h𝒜 e he) b hyt) k l
  refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun l _ => (hinv l).mul ?_)
  exact ((hD _ _ _ y hy).add (hD _ _ _ y hy)).sub (hD _ _ _ y hy)

/-- compatible atlas 版（`h𝒜` 取自 `IsAnalyticCompatibleAtlas_F3A.mem_maximalAtlas`）。 -/
theorem IsAnalyticCompatibleAtlas_F3A.analyticOnNhd_christoffel {ι : Type*} [Fintype ι]
    [DecidableEq ι] {𝒜 : Set (OpenPartialHomeomorph M E)} {P : Set M}
    (h : IsAnalyticCompatibleAtlas_F3A P 𝒜) (hP : IsOpen P)
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} (hG : IsAnalyticMetricOn_F3A 𝒜 P G)
    {e : OpenPartialHomeomorph M E} (he : e ∈ 𝒜) (b : Module.Basis ι ℝ E) (i j k : ι) :
    AnalyticOnNhd ℝ (christoffel_F3A G e b i j k) (e '' (P ∩ e.source)) :=
  hG.analyticOnNhd_christoffel hP h.mem_maximalAtlas he b i j k

end Christoffel

end DifferentialGeometry.Geometry.Analytic

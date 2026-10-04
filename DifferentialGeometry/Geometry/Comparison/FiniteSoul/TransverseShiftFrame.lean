import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteJacobiChart
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Curvature
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Orthonormal frames and the Jacobi operator of a finite metric (lane CMS3-SHIFT, group G3)

* `exists_orthonormal_of_pos`, `eq_sum_of_orthonormal`, `apply_eq_sum_of_orthonormal`: a positive
  symmetric bilinear form on a finite-dimensional space has an orthonormal basis of `finrank` vectors;
  every vector expands in an orthonormal family of `finrank` vectors (Parseval).
* `coefficientRm04_sum_left`, `coefficientRm04_sum_right`: linearity of the coefficient curvature in its
  first and last slots (`C²` coefficients).
* `finiteRm04`: the curvature `Rm(X, Y, Z, W)` of a finite metric at a point, read in the chart at the
  point; `finiteRm04_eq_chart`: it is the coefficient curvature in ANY chart containing the point
  (`Analysis.coefficientRm04_transition`).
* `finiteRm04_jacobi_symm`, `finiteRm04_nonneg_of_sectional`, `finiteRm04_le_of_sectional`: the Jacobi
  form `Rm(X, u, u, Y)` is symmetric, `≥ 0` when `sec ≥ 0` and `≤ Λ |X|² |u|²` when `sec ≤ Λ`.
* `isSelfAdjoint_toEuclideanCLM_of_symm`, `inner_toEuclideanCLM_self_eq_sum`,
  `norm_le_of_inner_self_le`: the frame matrix as an operator on `EuclideanSpace`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.MetricKoszul (raisedKoszulOp)
open DifferentialGeometry.Analysis (coefficientRm04)

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A positive symmetric bilinear form has an orthonormal basis. -/
theorem exists_orthonormal_of_pos (B : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, B u v = B v u)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) :
    ∃ f : Fin (Module.finrank ℝ E) → E, ∀ i j, B (f i) (f j) = if i = j then 1 else 0 := by
  let B' : LinearMap.BilinForm ℝ E := LinearMap.mk₂ ℝ (fun u v => B u v)
    (fun u₁ u₂ v => by simp only [map_add, add_apply])
    (fun c u v => by simp only [map_smul, smul_apply, smul_eq_mul])
    (fun u v₁ v₂ => by simp only [map_add])
    (fun c u v => by simp only [map_smul, smul_eq_mul])
  have hB'symm : LinearMap.IsSymm B' :=
    LinearMap.BilinForm.isSymm_iff.mp ⟨fun u v => hsymm u v⟩
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB'symm
  have hvpos : ∀ i, 0 < B (v i) (v i) := fun i => hpos _ (v.ne_zero i)
  refine ⟨fun i => (Real.sqrt (B (v i) (v i)))⁻¹ • v i, fun i j => ?_⟩
  simp only [map_smul, smul_apply, smul_eq_mul]
  split_ifs with hij
  · subst hij
    have hs := Real.sq_sqrt (hvpos i).le
    have hs0 := Real.sqrt_pos.mpr (hvpos i)
    field_simp
    linarith [hs]
  · have h0 : B (v i) (v j) = 0 := hv hij
    rw [h0, mul_zero, mul_zero]

/-- **Expansion in an orthonormal family of `finrank` vectors.** -/
theorem eq_sum_of_orthonormal (B : E →L[ℝ] E →L[ℝ] ℝ) {n : ℕ} (hn : n = Module.finrank ℝ E)
    (f : Fin n → E) (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) (X : E) :
    X = ∑ i, B X (f i) • f i := by
  have hli : LinearIndependent ℝ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h := congrArg (fun z => B z (f k)) hc
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
      smul_apply, smul_eq_mul, map_zero, zero_apply,
      hf] at h
    simpa using h
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [hn])
  have hX : X ∈ Submodule.span ℝ (range f) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hX
  have hck : ∀ k, B X (f k) = c k := by
    intro k
    rw [← hc]
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
      smul_apply, smul_eq_mul, hf]
    simp
  rw [← hc]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hc] at hck
  rw [hck k]

/-- **Parseval** for an orthonormal family of `finrank` vectors. -/
theorem apply_eq_sum_of_orthonormal (B : E →L[ℝ] E →L[ℝ] ℝ) {n : ℕ}
    (hn : n = Module.finrank ℝ E) (f : Fin n → E) (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0)
    (X Y : E) : B X Y = ∑ i, B X (f i) * B Y (f i) := by
  have hY := eq_sum_of_orthonormal B hn f hf Y
  conv_lhs => rw [hY]
  simp only [map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

local instance continuousDualEquiv_CMS3SHIFTf : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroup_CMS3SHIFTf : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpace_CMS3SHIFTf : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The coefficient curvature in its first and last slots is a bilinear map. -/
theorem exists_clm_coefficientRm04 {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hb : ContDiffAt ℝ 2 b x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u) (hco : IsCoercive (b x)) (Y Z : E) :
    ∃ Q : E →L[ℝ] E →L[ℝ] ℝ, ∀ X W : E, coefficientRm04 b x X Y Z W = Q X W := by
  refine ⟨(b x).comp ((ContinuousLinearMap.apply ℝ E Z).comp
    ((ContinuousLinearMap.apply ℝ (E →L[ℝ] E) Y).comp (Geometry.Connection.connectionFormCurvatureCLM
      (fun y => (raisedKoszulOp (b y) (fderiv ℝ b y) : E →L[ℝ] E →L[ℝ] E)) x))), fun X W => ?_⟩
  rw [DifferentialGeometry.Analysis.coefficientRm04_eq_connectionFormCurvature hb hsymm hco]
  rfl

theorem coefficientRm04_sum_left {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hb : ContDiffAt ℝ 2 b x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u) (hco : IsCoercive (b x)) {n : ℕ}
    (c : Fin n → ℝ) (X : Fin n → E) (Y Z W : E) :
    coefficientRm04 b x (∑ k, c k • X k) Y Z W = ∑ k, c k * coefficientRm04 b x (X k) Y Z W := by
  obtain ⟨Q, hQ⟩ := exists_clm_coefficientRm04 hb hsymm hco Y Z
  simp only [hQ, map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    smul_apply, smul_eq_mul]

theorem coefficientRm04_sum_right {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hb : ContDiffAt ℝ 2 b x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u) (hco : IsCoercive (b x)) {n : ℕ}
    (c : Fin n → ℝ) (W : Fin n → E) (X Y Z : E) :
    coefficientRm04 b x X Y Z (∑ k, c k • W k) = ∑ k, c k * coefficientRm04 b x X Y Z (W k) := by
  obtain ⟨Q, hQ⟩ := exists_clm_coefficientRm04 hb hsymm hco Y Z
  simp only [hQ, map_sum, map_smul, smul_eq_mul]

end Algebra

section Operator

variable {n : ℕ}

/-- A symmetric matrix gives a self-adjoint operator of `EuclideanSpace`. -/
theorem isSelfAdjoint_toEuclideanCLM_of_symm {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i k, A i k = A k i) : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A x, y⟫_ℝ = ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A y⟫_ℝ
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [hA i k]
  ring

/-- The quadratic form of the matrix operator. -/
theorem inner_toEuclideanCLM_self_eq_sum (A : Matrix (Fin n) (Fin n) ℝ)
    (a : EuclideanSpace ℝ (Fin n)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A a, a⟫_ℝ = ∑ i, ∑ k, A i k * a k * a i := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Operator norm from the quadratic form** for a positive semidefinite self-adjoint operator. -/
theorem norm_le_of_inner_self_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] {T : F →L[ℝ] F} {Λ : ℝ} (hΛ : 0 ≤ Λ) (hT : IsSelfAdjoint T)
    (hpos : ∀ a : F, 0 ≤ ⟪T a, a⟫_ℝ) (hle : ∀ a : F, ⟪T a, a⟫_ℝ ≤ Λ * ‖a‖ ^ 2) : ‖T‖ ≤ Λ := by
  refine ContinuousLinearMap.opNorm_le_bound _ hΛ fun a => ?_
  have hsym : ∀ x y : F, ⟪T x, y⟫_ℝ = ⟪T y, x⟫_ℝ := fun x y => by
    have h1 : ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ := hT.isSymmetric x y
    rw [h1, real_inner_comm]
  -- Cauchy–Schwarz for the positive form `⟪T ·, ·⟫`
  have hcs : ⟪T a, T a⟫_ℝ ^ 2 ≤ ⟪T a, a⟫_ℝ * ⟪T (T a), T a⟫_ℝ := by
    have h := DifferentialGeometry.Analysis.bilin_gram_nonneg (B := (innerSL ℝ).comp T)
      (fun u v => hsym u v) (fun w => hpos w) a (T a)
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at h
    linarith
  have h1 : ⟪T a, a⟫_ℝ ≤ Λ * ‖a‖ ^ 2 := hle a
  have h2 : ⟪T (T a), T a⟫_ℝ ≤ Λ * ‖T a‖ ^ 2 := hle (T a)
  have hTa : ⟪T a, T a⟫_ℝ = ‖T a‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [hTa] at hcs
  have hn0 : 0 ≤ ‖T a‖ := norm_nonneg _
  have ha0 : 0 ≤ ‖a‖ := norm_nonneg _
  have h3 : ‖T a‖ ^ 4 ≤ (Λ * ‖a‖ ^ 2) * (Λ * ‖T a‖ ^ 2) := by
    have := mul_le_mul h1 h2 (hpos (T a)) (by positivity)
    nlinarith [hpos a]
  by_cases hz : ‖T a‖ = 0
  · rw [hz]; positivity
  · have hpos' : 0 < ‖T a‖ := lt_of_le_of_ne hn0 (Ne.symm hz)
    have h4 : ‖T a‖ ^ 2 ≤ (Λ * ‖a‖) ^ 2 := by
      have h5 : ‖T a‖ ^ 2 * ‖T a‖ ^ 2 ≤ (Λ * ‖a‖) ^ 2 * ‖T a‖ ^ 2 := by nlinarith
      exact le_of_mul_le_mul_right h5 (by positivity)
    exact (pow_le_pow_iff_left₀ hn0 (by positivity) two_ne_zero).mp h4

end Operator

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {r : ℕ∞}

local instance continuousDualEquiv_CMS3SHIFTm : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

theorem two_le_coe_add_one {r : ℕ∞} (hr : 1 ≤ r) : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := by
  have h1 : (1 : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
  calc (2 : ℕ∞ω) = 1 + 1 := one_add_one_eq_two.symm
    _ ≤ (r : ℕ∞ω) + 1 := add_le_add_left h1 1

/-- The curvature `Rm(X, Y, Z, W)` of a finite metric at `y`, read in the chart at `y`. -/
def finiteRm04 {n : ℕ∞ω} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (y : M) (X Y Z W : E) : ℝ :=
  coefficientRm04 (chartCoeffFinite g y) (extChartAt I y y)
    (mfderiv I 𝓘(ℝ, E) (extChartAt I y) y X) (mfderiv I 𝓘(ℝ, E) (extChartAt I y) y Y)
    (mfderiv I 𝓘(ℝ, E) (extChartAt I y) y Z) (mfderiv I 𝓘(ℝ, E) (extChartAt I y) y W)

/-- Chart data: the coefficients are `C²` near the chart image, symmetric and coercive. -/
theorem chartCoeffFinite_data (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)) (q : M)
    {y : E} (hy : y ∈ (extChartAt I q).target) :
    ContDiffAt ℝ 2 (chartCoeffFinite g q) y ∧
      (∀ᶠ z in 𝓝 y, ∀ u v : E, chartCoeffFinite g q z u v = chartCoeffFinite g q z v u) ∧
      IsCoercive (chartCoeffFinite g q y) := by
  have h2 : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := two_le_coe_add_one hr
  refine ⟨((contDiffOn_chartCoeffFinite g h2 (WithTop.coe_le_coe.mpr le_top) q).contDiffAt
    ((isOpen_extChartAt_target q).mem_nhds hy)), Eventually.of_forall fun z u v =>
      chartCoeffFinite_symm g q z u v, isCoercive_chartCoeffFinite g hy⟩

/-- **Chart invariance** of `finiteRm04`: it is the coefficient curvature in any chart at `q ∋ y`. -/
theorem finiteRm04_eq_chart (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)) {q y : M}
    (hy : y ∈ (chartAt H q).source) (X Y Z W : E) :
    finiteRm04 g y X Y Z W =
      coefficientRm04 (chartCoeffFinite g q) (extChartAt I q y)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I q) y X) (mfderiv I 𝓘(ℝ, E) (extChartAt I q) y Y)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I q) y Z) (mfderiv I 𝓘(ℝ, E) (extChartAt I q) y W) := by
  have hyy : y ∈ (chartAt H y).source := mem_chart_source H y
  have hmem := mem_transition_source (I := I) hyy hy
  have h2 : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := two_le_coe_add_one hr
  have hmaps : MapsTo (extChartAt I q ∘ (extChartAt I y).symm)
      ((extChartAt I y).symm ≫ extChartAt I q).source (extChartAt I q).target := by
    intro z hz
    rw [PartialEquiv.trans_source] at hz
    exact (extChartAt I q).map_source hz.2
  have h := DifferentialGeometry.Analysis.coefficientRm04_transition (isOpen_transition_source y q)
    (isOpen_extChartAt_target q) ((contDiffOn_chartCoeffFinite g h2 (WithTop.coe_le_coe.mpr le_top) q))
    (fun z _ u v => chartCoeffFinite_symm g q z u v) (fun z hz => isCoercive_chartCoeffFinite g hz)
    (contDiffOn_transition y q) hmaps (fun z hz => isInvertible_fderiv_transition hz)
    (fun z hz u v => chartCoeffFinite_transition g hz u v) hmem
    (mfderiv I 𝓘(ℝ, E) (extChartAt I y) y X) (mfderiv I 𝓘(ℝ, E) (extChartAt I y) y Y)
    (mfderiv I 𝓘(ℝ, E) (extChartAt I y) y Z) (mfderiv I 𝓘(ℝ, E) (extChartAt I y) y W)
  have hΦ : (extChartAt I q ∘ (extChartAt I y).symm) (extChartAt I y y) = extChartAt I q y := by
    simp only [Function.comp_apply]
    rw [(extChartAt I y).left_inv (mem_extChartAt_source y)]
  rw [hΦ, ← mfderiv_extChartAt_eq_fderiv_transition hyy hy, ← mfderiv_extChartAt_eq_fderiv_transition hyy hy,
    ← mfderiv_extChartAt_eq_fderiv_transition hyy hy, ← mfderiv_extChartAt_eq_fderiv_transition hyy hy] at h
  exact h

/-- The Jacobi form of a finite metric is symmetric. -/
theorem finiteRm04_jacobi_symm (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)) (y : M)
    (X u Y : E) : finiteRm04 g y X u u Y = finiteRm04 g y Y u u X := by
  obtain ⟨hb, hsymm, hco⟩ := chartCoeffFinite_data hr g y
    ((extChartAt I y).map_source (mem_extChartAt_source y))
  exact coefficientRm04_jacobi_symm hb hsymm hco _ _ _

/-- `Rm(X, u, u, X) ≥ 0` where `sec ≥ 0`. -/
theorem finiteRm04_nonneg_of_sectional (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)) (y : M)
    (hsec : ∀ v w : TangentSpace I y, 0 ≤ g.sectionalCurvature y v w) (X u : E) :
    0 ≤ finiteRm04 g y X u u X := by
  have h2 : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := two_le_coe_add_one hr
  exact DifferentialGeometry.Geometry.MetricSmoothing.coefficientRm04_chart_nonneg_of_sectional g h2 y
    (mem_extChartAt_source y) hsec _ _

/-- `Rm(X, u, u, X) ≤ Λ g(X, X) g(u, u)` where `sec ≤ Λ`, `Λ ≥ 0`. -/
theorem finiteRm04_le_of_sectional (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)) (y : M)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hsec : ∀ v w : TangentSpace I y, g.sectionalCurvature y v w ≤ Λ) (X u : E) :
    finiteRm04 g y X u u X ≤ Λ * (g.inner y X X * g.inner y u u) := by
  have h2 : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := two_le_coe_add_one hr
  set D : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I y) y with hD
  set b := chartCoeffFinite g y with hbdef
  set x := extChartAt I y y with hx
  obtain ⟨hb, hsymm, hco⟩ := chartCoeffFinite_data hr g y
    ((extChartAt I y).map_source (mem_extChartAt_source y))
  have hyy : y ∈ (chartAt H y).source := mem_chart_source H y
  have hXX : g.inner y X X = b x (D X) (D X) := inner_eq_chartCoeffFinite g hyy X X
  have huu : g.inner y u u = b x (D u) (D u) := inner_eq_chartCoeffFinite g hyy u u
  have hgram := DifferentialGeometry.Analysis.bilin_gram_nonneg (B := b x)
    (fun p q => chartCoeffFinite_symm g y x p q)
    (fun w => by
      obtain ⟨C, hC, hCw⟩ := hco
      exact (by positivity : (0 : ℝ) ≤ C * ‖w‖ * ‖w‖).trans (hCw w)) (D X) (D u)
  have hbound : finiteRm04 g y X u u X ≤ Λ * (b x (D X) (D X) * b x (D u) (D u) - (b x (D X) (D u)) ^ 2) := by
    change coefficientRm04 b x (D X) (D u) (D u) (D X) ≤ _
    by_cases hind : LinearIndependent ℝ ![D X, D u]
    · have hsurj : ∀ U : E, D ((mfderiv 𝓘(ℝ, E) I (extChartAt I y).symm x : E →L[ℝ] E) U) = U := by
        intro U
        have h := mfderiv_extChartAt_apply_mfderiv_symm (I := I) (q := y)
          ((extChartAt I y).map_source (mem_extChartAt_source y)) U
        rwa [(extChartAt I y).left_inv (mem_extChartAt_source y)] at h
      have e : g.sectionalCurvature y X u =
          DifferentialGeometry.Analysis.coefficientSectional b x (D X) (D u) :=
        DifferentialGeometry.Geometry.MetricSmoothing.sectionalCurvature_eq_chart g h2 y
          (mem_extChartAt_source y) X u
      have hK := e ▸ hsec X u
      have hden := DifferentialGeometry.Analysis.bilin_gram_pos_of_linearIndependent
        (fun p q => chartCoeffFinite_symm g y x p q) hco hind
      rw [DifferentialGeometry.Analysis.coefficientSectional_def] at hK
      have h := mul_le_mul_of_nonneg_right hK hden.le
      rwa [div_mul_cancel₀ _ hden.ne'] at h
    · rw [DifferentialGeometry.Geometry.MetricSmoothing.coefficientRm04_eq_zero_of_not_linearIndependent
        hb hsymm hco hind]
      exact mul_nonneg hΛ hgram
  rw [hXX, huu]
  have hsq := sq_nonneg (b x (D X) (D u))
  nlinarith [hbound, hsq, hΛ]

/-- Linearity of `finiteRm04` in the first slot. -/
theorem finiteRm04_sum_left (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)) (y : M)
    {n : ℕ} (c : Fin n → ℝ) (X : Fin n → E) (Y Z W : E) :
    finiteRm04 g y (∑ k, c k • X k) Y Z W = ∑ k, c k * finiteRm04 g y (X k) Y Z W := by
  obtain ⟨hb, hsymm, hco⟩ := chartCoeffFinite_data hr g y
    ((extChartAt I y).map_source (mem_extChartAt_source y))
  set D : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I y) y with hD
  change coefficientRm04 (chartCoeffFinite g y) (extChartAt I y y) (D (∑ k, c k • X k)) (D Y) (D Z)
      (D W) = ∑ k, c k * coefficientRm04 (chartCoeffFinite g y) (extChartAt I y y) (D (X k)) (D Y)
        (D Z) (D W)
  rw [map_sum]
  simp only [map_smul]
  exact coefficientRm04_sum_left hb hsymm hco c _ _ _ _

/-- Linearity of `finiteRm04` in the last slot. -/
theorem finiteRm04_sum_right (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)) (y : M)
    {n : ℕ} (c : Fin n → ℝ) (W : Fin n → E) (X Y Z : E) :
    finiteRm04 g y X Y Z (∑ k, c k • W k) = ∑ k, c k * finiteRm04 g y X Y Z (W k) := by
  obtain ⟨hb, hsymm, hco⟩ := chartCoeffFinite_data hr g y
    ((extChartAt I y).map_source (mem_extChartAt_source y))
  set D : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I y) y with hD
  change coefficientRm04 (chartCoeffFinite g y) (extChartAt I y y) (D X) (D Y) (D Z)
      (D (∑ k, c k • W k)) = ∑ k, c k * coefficientRm04 (chartCoeffFinite g y) (extChartAt I y y)
        (D X) (D Y) (D Z) (D (W k))
  rw [map_sum]
  simp only [map_smul]
  exact coefficientRm04_sum_right hb hsymm hco c _ _ _ _

end Manifold

end DifferentialGeometry.Geometry.FiniteSoul

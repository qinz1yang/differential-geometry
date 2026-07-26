import DifferentialGeometry.Geometry.Operator.RoughLaplacian

set_option autoImplicit false

/-!
# Splitting a metric trace along a line

This file gives the pointwise linear-algebra decomposition of the metric trace
of a covariant two-tensor into one distinguished line and its perpendicular
complement.  The tensor need not be symmetric.
-/

namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {Hm : Type*} [TopologicalSpace Hm]
variable {I : ModelWithCorners Real E Hm}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Hm M] [IsManifold I ∞ M]

/-- The metric trace of a covariant two-tensor splits into its contribution
along a nonzero line and the inverse-Gram trace on a maximal perpendicular
family.  No symmetry of the tensor is required. -/
theorem trace_eq_line_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (Z : TangentSpace I x)
    (V : ι → TangentSpace I x)
    (H :
      Tensor0SSpace
        (𝕜 := Real) (E := E) (H := Hm)
        (I := I) (M := M) 2 x)
    (hZ : 0 < g.inner x Z Z)
    (hperp : ∀ i, g.inner x Z (V i) = 0)
    (hLI : LinearIndependent Real V)
    (hcard :
      Fintype.card ι = Module.finrank Real E - 1) :
    let G : Matrix ι ι Real :=
      Matrix.of fun i j => g.inner x (V i) (V j)
    let A : Matrix ι ι Real :=
      Matrix.of fun i j =>
        H (vec2 (I := I) (V i) (V j))
    metricTracePair0SAt (I := I) g H
      =
        (g.inner x Z Z)⁻¹ *
          H (vec2 (I := I) Z Z)
        + Matrix.trace (G⁻¹ * A) := by
  classical
  dsimp only
  let G : Matrix ι ι Real :=
    Matrix.of fun i j => g.inner x (V i) (V j)
  let A : Matrix ι ι Real :=
    Matrix.of fun i j => H (vec2 (I := I) (V i) (V j))
  let W : Option ι → TangentSpace I x :=
    fun o => Option.casesOn' o Z V
  let φ : TangentSpace I x →ₗ[Real] Real := (g.inner x Z).toLinearMap
  have hVker : Set.range V ⊆ LinearMap.ker φ := by
    rintro y ⟨i, rfl⟩
    change g.inner x Z (V i) = 0
    exact hperp i
  have hZspan : Z ∉ Submodule.span Real (Set.range V) := by
    intro hmem
    have hker : Z ∈ LinearMap.ker φ :=
      (Submodule.span_le.2 hVker) hmem
    have hzero : g.inner x Z Z = 0 := hker
    exact hZ.ne' hzero
  have hWLI : LinearIndependent Real W := by
    simpa only [W] using hLI.option hZspan
  have hZne : Z ≠ 0 := by
    intro h
    subst Z
    simp at hZ
  have hdim : 0 < Module.finrank Real E := by
    exact Module.finrank_pos_iff.mpr ⟨Z, 0, hZne⟩
  have hcardW :
      Fintype.card (Option ι) =
        Module.finrank Real (TangentSpace I x) := by
    rw [Fintype.card_option, hcard]
    exact Nat.succ_pred_eq_of_pos hdim
  let b : Module.Basis (Option ι) Real (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hWLI hcardW
  have hb (o : Option ι) : b o = W o := by
    exact congrFun
      (coe_basisOfLinearIndependentOfCardEqFinrank hWLI hcardW) o
  have hb0 : b none = Z := by
    simpa only [W] using hb none
  have hbs (i : ι) : b (some i) = V i := by
    simpa only [W] using hb (some i)
  let q : Option ι → Option ι → Real :=
    basisInvMetric (I := I) g x b
  have hq :
      MetricInverseInBasis_gen (I := I) g x b q := by
    simpa only [q] using basisInvMetric_real (I := I) g x b
  have hqsymm (i j : Option ι) : q i j = q j i := by
    simpa only [q] using basisInvMetric_symm (I := I) g x b i j
  have hperp' (i : ι) : g.inner x (V i) Z = 0 := by
    rw [g.symm x (V i) Z]
    exact hperp i
  have hq00mul :
      q none none * g.inner x Z Z = 1 := by
    have h := (hq none none).1
    simpa only [Fintype.sum_option, hb0, hbs, hperp', mul_zero,
      Finset.sum_const_zero, add_zero, if_pos] using h
  have hq00 :
      q none none = (g.inner x Z Z)⁻¹ :=
    eq_inv_of_mul_eq_one_left hq00mul
  have hq0s (j : ι) : q none (some j) = 0 := by
    have h := (hq none (some j)).2
    have hne : (none : Option ι) ≠ some j := by simp
    have hmul : g.inner x Z Z * q none (some j) = 0 := by
      simpa only [Fintype.sum_option, hb0, hbs, hperp, zero_mul,
        Finset.sum_const_zero, add_zero, if_neg hne] using h
    exact (mul_eq_zero.mp hmul).resolve_left hZ.ne'
  have hqs0 (i : ι) : q (some i) none = 0 := by
    rw [hqsymm (some i) none, hq0s]
  let Q : Matrix ι ι Real := fun i j => q (some i) (some j)
  have hQG : Q * G = 1 := by
    ext i j
    have h := (hq (some i) (some j)).1
    simpa only [Matrix.mul_apply, Q, G, Matrix.of_apply,
      Fintype.sum_option, hb0, hbs, hperp, mul_zero, zero_add,
      Matrix.one_apply, Option.some.injEq] using h
  have hGinv : G⁻¹ = Q :=
    Matrix.inv_eq_left_inv hQG
  have hqss (i j : ι) : q (some i) (some j) = G⁻¹ i j := by
    rw [hGinv]
  have hGsymm (i j : ι) : G⁻¹ i j = G⁻¹ j i := by
    rw [hGinv]
    exact hqsymm (some i) (some j)
  have hsum :
      (∑ i : ι, ∑ j : ι,
          G⁻¹ i j * H (vec2 (I := I) (V i) (V j))) =
        Matrix.trace (G⁻¹ * A) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, A, Matrix.of_apply]
    calc
      (∑ i : ι, ∑ j : ι,
          G⁻¹ i j * H (vec2 (I := I) (V i) (V j))) =
          ∑ i : ι, ∑ j : ι,
            G⁻¹ j i * H (vec2 (I := I) (V i) (V j)) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              rw [hGsymm i j]
      _ = ∑ j : ι, ∑ i : ι,
            G⁻¹ j i * H (vec2 (I := I) (V i) (V j)) := by
              rw [Finset.sum_comm]
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g b q hq H]
  rw [Fintype.sum_option]
  simp only [Fintype.sum_option, hb0, hbs, hq00, hq0s, hqs0, hqss,
    zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  simpa only [G, A] using congrArg
    (fun r => (g.inner x Z Z)⁻¹ * H (vec2 (I := I) Z Z) + r) hsum

end

end DifferentialGeometry.Integral.Connection

import DifferentialGeometry.Geometry.Connection.LeviCivita.DifferenceNorm
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Analysis.Laplacian
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem connectionDifferenceSq_le_of_bilinear_bound
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    {C L : ℝ} (hC : 1 ≤ C) (hL : 0 ≤ L)
    (heq : ∀ v : TangentSpace I x,
      C⁻¹ * g₀.inner x v v ≤ g₁.inner x v v ∧ g₁.inner x v v ≤ C * g₀.inner x v v)
    (hbound : ∀ v w : TangentSpace I x,
      Real.sqrt (g₀.inner x
        (CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x v w)
        (CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x v w)) ≤
        L * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) :
    connectionDifferenceSq (I := I) g₁ g₂ x ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * C ^ 3 * L ^ 2 := by
  classical
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  obtain ⟨b, hON⟩ := exists_orthonormal_basis (I := I) g₁ x
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g₁ b hON
  have hunit (i : Fin (Module.finrank ℝ (TangentSpace I x))) :
      g₁.inner x (b i) (b i) = 1 := by simpa using hON i i
  have hbase (i : Fin (Module.finrank ℝ (TangentSpace I x))) :
      g₀.inner x (b i) (b i) ≤ C := by
    have h := (metric_equiv_symm (I := I) g₀ g₁ x hC heq (b i)).2
    simpa only [hunit, mul_one] using h
  have hnorm (i : Fin (Module.finrank ℝ (TangentSpace I x))) :
      Real.sqrt (g₀.inner x (b i) (b i)) ≤ Real.sqrt C := Real.sqrt_le_sqrt (hbase i)
  have hcomp (slots : Fin 3 → Fin (Module.finrank ℝ (TangentSpace I x))) :
      component0S (I := I) b (connectionDifferenceLowAt (I := I) g₁ g₂ x) slots ^ 2 ≤
        C ^ 3 * L ^ 2 := by
    let V := CovariantDerivative.difference (metricCov (I := I) g₁)
      (metricCov (I := I) g₂) x (b (slots 1)) (b (slots 0))
    have hb : Real.sqrt (g₀.inner x V V) ≤ L * C := by
      refine (hbound (b (slots 1)) (b (slots 0))).trans ?_
      calc
        L * Real.sqrt (g₀.inner x (b (slots 1)) (b (slots 1))) *
            Real.sqrt (g₀.inner x (b (slots 0)) (b (slots 0))) ≤
            L * Real.sqrt C * Real.sqrt C :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hnorm (slots 1)) hL)
            (hnorm (slots 0)) (Real.sqrt_nonneg _) (by positivity)
        _ = L * C := by rw [mul_assoc, ← sq, Real.sq_sqrt hC0]
    have hsq : g₀.inner x V V ≤ (L * C) ^ 2 := (Real.sqrt_le_iff).mp hb |>.2
    have hCS := metric_inner_cauchy_schwarz_sq (I := I) g₁ x V (b (slots 2))
    rw [hunit, mul_one] at hCS
    have hpoint : (g₁.inner x V (b (slots 2))) ^ 2 ≤ C ^ 3 * L ^ 2 :=
      (hCS.trans (heq V).2).trans
        ((mul_le_mul_of_nonneg_left hsq hC0).trans_eq (by ring))
    rw [component0S_apply]
    change (Tensor0SSpace.eval (connectionDifferenceLowAt (I := I) g₁ g₂ x)
      (fun i => b (slots i))) ^ 2 ≤ _
    rw [connectionDifferenceLowAt_apply]
    exact hpoint
  rw [connectionDifferenceSq_def, normSq0S_identity_eq_sum_sq (I := I) g₁ x 3 b hinv]
  calc
    _ ≤ ∑ _ : Fin 3 → Fin (Module.finrank ℝ (TangentSpace I x)), C ^ 3 * L ^ 2 :=
      Finset.sum_le_sum fun slots _ => hcomp slots
    _ = _ := by
      rw [show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E by rfl]
      simp [nsmul_eq_mul]
      ring

variable [T2Space M]

private theorem connection_difference_sub
    (cov₀ cov₁ cov₂ : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (v w : TangentSpace I x) :
    CovariantDerivative.difference cov₁ cov₂ x v w =
      CovariantDerivative.difference cov₁ cov₀ x v w -
        CovariantDerivative.difference cov₂ cov₀ x v w := by
  obtain ⟨σ, hσ⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v
  rw [← hσ]
  change (cov₁.isCovariantDerivativeOnUniv.difference cov₂.isCovariantDerivativeOnUniv x (σ x)) w =
    (cov₁.isCovariantDerivativeOnUniv.difference cov₀.isCovariantDerivativeOnUniv x (σ x)) w -
    (cov₂.isCovariantDerivativeOnUniv.difference cov₀.isCovariantDerivativeOnUniv x (σ x)) w
  rw [IsCovariantDerivativeOn.difference_apply _ _ (mem_univ x) σ.mdifferentiableAt,
    IsCovariantDerivativeOn.difference_apply _ _ (mem_univ x) σ.mdifferentiableAt,
    IsCovariantDerivativeOn.difference_apply _ _ (mem_univ x) σ.mdifferentiableAt]
  simp only [sub_apply]
  abel

theorem connectionDifferenceSq_le_of_common_connection_bounds
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M)
    (cov₀ : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    {C L₁ L₂ : ℝ} (hC : 1 ≤ C) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (heq : ∀ v : TangentSpace I x,
      C⁻¹ * g₀.inner x v v ≤ g₁.inner x v v ∧ g₁.inner x v v ≤ C * g₀.inner x v v)
    (hbound₁ : ∀ v w : TangentSpace I x,
      Real.sqrt (g₀.inner x
        (CovariantDerivative.difference (metricCov (I := I) g₁) cov₀ x v w)
        (CovariantDerivative.difference (metricCov (I := I) g₁) cov₀ x v w)) ≤
        L₁ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w))
    (hbound₂ : ∀ v w : TangentSpace I x,
      Real.sqrt (g₀.inner x
        (CovariantDerivative.difference (metricCov (I := I) g₂) cov₀ x v w)
        (CovariantDerivative.difference (metricCov (I := I) g₂) cov₀ x v w)) ≤
        L₂ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) :
    connectionDifferenceSq (I := I) g₁ g₂ x ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * C ^ 3 * (L₁ + L₂) ^ 2 := by
  apply connectionDifferenceSq_le_of_bilinear_bound g₀ g₁ g₂ x hC (add_nonneg hL₁ hL₂) heq
  intro v w
  let V₁ := CovariantDerivative.difference (metricCov (I := I) g₁) cov₀ x v w
  let V₂ := CovariantDerivative.difference (metricCov (I := I) g₂) cov₀ x v w
  rw [connection_difference_sub cov₀]
  have h := gNorm_add_le (I := I) g₀ x V₁ (-V₂)
  simp only [map_neg, neg_apply, neg_neg] at h
  rw [sub_eq_add_neg]
  have h₁ := hbound₁ v w
  have h₂ := hbound₂ v w
  exact h.trans (by dsimp [V₁, V₂] at *; nlinarith only [h₁, h₂])

end DifferentialGeometry.PDE.RicciFlow

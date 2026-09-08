import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.Control
import DifferentialGeometry.Geometry.Metric.Coordinates.QuadraticBounds
import DifferentialGeometry.Geometry.Operator.Gradient.Basic

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Matrix

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_abs_chartInvGramMatrix_le_of_lower_bound
    (gRef : SmoothRiemannianMetric I M) (alpha : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (trivializationAt E (TangentSpace I) alpha).baseSet)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ g : SmoothRiemannianMetric I M,
      (∀ v : TangentSpace I y, lam * gRef.inner y v v ≤ g.inner y v v) →
        ∀ i j : Fin (Module.finrank ℝ E),
          |Geometry.Operator.chartInvGramMatrix g alpha y i j| ≤ C := by
  classical
  obtain ⟨c, hc, hbound⟩ := exists_pos_mul_dotProduct_le_chartGramMatrix gRef alpha hK hKchart
  refine ⟨Real.sqrt (Module.finrank ℝ E) / (lam * c),
    div_nonneg (Real.sqrt_nonneg _) (mul_pos hlam hc).le, fun y hy g hlow i j => ?_⟩
  let e := trivializationAt E (TangentSpace I) alpha
  have hframe (k : Fin (Module.finrank ℝ E)) :
      e.localFrame (chartModelBasis E) k y = chartBasisVecFiber alpha k y := by
    rw [e.localFrame_apply_of_mem_baseSet (chartModelBasis E) (hKchart hy)]
    change (e.linearEquivAt ℝ y (hKchart hy)).symm ((chartModelBasis E) k) =
      e.symmL ℝ y ((chartModelBasis E) k)
    rw [e.linearEquivAt_symm_apply, e.symmL_apply (hKchart hy)]
  have hgram : PDE.RicciFlow.gramE e g (chartModelBasis E) y = chartGramMatrix g alpha y := by
    ext k l
    simp only [PDE.RicciFlow.gramE, Matrix.of_apply, hframe, chartGramMatrix_apply]
  have hquad (v : Fin (Module.finrank ℝ E) → ℝ) :
      lam * c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (PDE.RicciFlow.gramE e g (chartModelBasis E) y) *ᵥ v := by
    rw [hgram]
    calc
      lam * c * (v ⬝ᵥ v) = lam * (c * (v ⬝ᵥ v)) := mul_assoc _ _ _
      _ ≤ lam * (v ⬝ᵥ chartGramMatrix gRef alpha y *ᵥ v) :=
        mul_le_mul_of_nonneg_left (hbound y hy v) hlam.le
      _ ≤ v ⬝ᵥ chartGramMatrix g alpha y *ᵥ v := by
        have hg := chartGramMatrix_dotProduct_mulVec g alpha y v
        have hR := chartGramMatrix_dotProduct_mulVec gRef alpha y v
        simp only [star_trivial] at hg hR
        rw [hg, hR]
        exact hlow _
  have hnorm := PDE.RicciFlow.ginv_compL2_le e g (chartModelBasis E) (lam * c)
    (mul_pos hlam hc) hquad
  calc
    |Geometry.Operator.chartInvGramMatrix g alpha y i j| =
        |PDE.RicciFlow.ginvCompField e g (chartModelBasis E) y ![i, j]| := by
      simp only [PDE.RicciFlow.ginvCompField, Matrix.cons_val_zero, Matrix.cons_val_one,
        hgram, Geometry.Operator.chartInvGramMatrix]
    _ ≤ PDE.RicciFlow.compL2 (PDE.RicciFlow.ginvCompField e g (chartModelBasis E) y) := by
      apply Real.abs_le_sqrt
      exact Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ ![i, j])
    _ ≤ Real.sqrt (Module.finrank ℝ E) / (lam * c) := by
      simpa only [Fintype.card_fin] using hnorm

end DifferentialGeometry.Tensor.Coordinates

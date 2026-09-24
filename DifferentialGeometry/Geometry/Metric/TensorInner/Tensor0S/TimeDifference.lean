import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem sqrt_sum_sq_sub_le_of_hasDerivWithinAt {ι : Type*} [Fintype ι]
    {a b L : ℝ} (c c' : ι → ℝ → ℝ)
    (hc : ∀ i t, t ∈ Icc a b → HasDerivWithinAt (c i) (c' i t) (Icc a b) t)
    (hbound : ∀ t ∈ Icc a b, Real.sqrt (∑ i, (c' i t) ^ 2) ≤ L)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    Real.sqrt (∑ i, (c i s - c i t) ^ 2) ≤ L * |s - t| := by
  classical
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)
  let f : ℝ → EuclideanSpace ℝ ι := fun r => e.symm (fun i => c i r)
  let f' : ℝ → EuclideanSpace ℝ ι := fun r => e.symm (fun i => c' i r)
  have hn (d : ι → ℝ) : ‖(e.symm d : EuclideanSpace ℝ ι)‖ = Real.sqrt (∑ i, (d i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [PiLp.continuousLinearEquiv_symm_apply, Real.norm_eq_abs, sq_abs]
  have hd (r : ℝ) (hr : r ∈ Icc a b) : HasDerivWithinAt f (f' r) (Icc a b) r := by
    have hh : HasDerivWithinAt (fun r : ℝ => (fun i => c i r : ι → ℝ))
        (fun i => c' i r) (Icc a b) r := by
      rw [hasDerivWithinAt_pi]
      exact fun i => hc i r hr
    exact e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt r hh
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun r hr => (hn _).trans_le (hbound r hr)) (convex_Icc a b) ht hs
  have hsub : f s - f t = e.symm (fun i => c i s - c i t) := by
    simp only [f, ← map_sub]
    rfl
  rw [hsub, hn, Real.norm_eq_abs] at hm
  exact hm

theorem sqrt_normSq0S_sub_le_of_hasDerivWithinAt
    (g : SmoothRiemannianMetric I M) (x : M) (q : ℕ)
    (A B : ℝ → Tensor0SSpace q I x) {a b L : ℝ}
    (hderiv : ∀ t ∈ Icc a b, ∀ v : Fin q → TangentSpace I x,
      HasDerivWithinAt (fun r => A r v) (B t v) (Icc a b) t)
    (hbound : ∀ t ∈ Icc a b, Real.sqrt (normSq0S g x q (B t)) ≤ L)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    Real.sqrt (normSq0S g x q (A s - A t)) ≤ L * |s - t| := by
  classical
  obtain ⟨basis, horth⟩ := exists_orthonormal_basis g x
  have hinv := metricInverseInBasis_of_orthonormal g basis horth
  let c := fun slots r => component0S basis (A r) slots
  let c' := fun slots r => component0S basis (B r) slots
  have hc (slots) (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivWithinAt (c slots) (c' slots r) (Icc a b) r :=
    hderiv r hr (fun i => basis (slots i))
  have hb (r : ℝ) (hr : r ∈ Icc a b) : Real.sqrt (∑ slots, (c' slots r) ^ 2) ≤ L := by
    rw [← normSq0S_identity_eq_sum_sq g x q basis hinv]
    exact hbound r hr
  have h := sqrt_sum_sq_sub_le_of_hasDerivWithinAt c c' hc hb hs ht
  rw [normSq0S_identity_eq_sum_sq g x q basis hinv]
  exact h

end DifferentialGeometry.Tensor0SBundle

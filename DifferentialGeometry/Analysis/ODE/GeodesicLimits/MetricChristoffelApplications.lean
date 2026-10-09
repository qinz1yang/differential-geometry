import DifferentialGeometry.Analysis.ODE.GeodesicLimits.MetricChristoffel
import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.CoerciveBilinearInverse

/-!
# Consumer of CM4.a/CM4.c: geodesics of metrics `C¹`-close to Euclidean converge to straight lines

On a finite-dimensional real inner product space `F`, let chart metrics `b i` converge in `C¹` on
compact sets to the Euclidean metric `innerSL ℝ`. Then

* `tendstoUniformlyOn_line_of_metric_tendsto_euclidean` (CM4.c): every sequence of `b i`-geodesics with
  initial data `(x i, v i) → (x, v)` converges uniformly on `[0,T]`, with velocities, to the straight
  line `t ↦ x + t • v`;
* `exists_C1_subseq_line_limit_of_metric_tendsto_euclidean` (CM4.a): geodesics staying in a compact set
  with bounded speed have a subsequence converging in `C¹` to a curve with zero acceleration.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology Metric
open DifferentialGeometry.MetricKoszul DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem isCoercive_innerSL : IsCoercive (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) :=
  ⟨1, one_pos, fun u => by rw [one_mul, innerSL_apply_apply, real_inner_self_eq_norm_mul_norm]⟩

/-- The Christoffel operator of the Euclidean metric vanishes. -/
theorem raisedKoszulOp_innerSL_fderiv_const (x : F) :
    raisedKoszulOp (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)
      (fderiv ℝ (fun _ : F => (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)) x) = 0 := by
  ext u v
  rw [fderiv_const_apply, raisedKoszulOp_eq isCoercive_innerSL]
  apply isCoercive_innerSL.bilin_injective
  rw [apply_koszul_vec]
  ext w
  simp [koszulCov]

/-- **Straight lines as limits (CM4.c).** -/
theorem tendstoUniformlyOn_line_of_metric_tendsto_euclidean
    (b : ℕ → F → F →L[ℝ] F →L[ℝ] ℝ) (hb : ∀ i, ContDiff ℝ 1 (b i))
    (hconv : ∀ C : Set F, IsCompact C → MapCPConvergenceOn C 1 b (fun _ => innerSL ℝ))
    {T : ℝ} (x v : F) (γ γ' : ℕ → ℝ → F)
    (hvel : ∀ i, ∀ t ∈ Icc 0 T, HasDerivWithinAt (γ i) (γ' i t) (Icc 0 T) t)
    (hacc : ∀ i, ∀ t ∈ Icc 0 T, HasDerivWithinAt (γ' i)
      (-(raisedKoszulOp (b i (γ i t)) (fderiv ℝ (b i) (γ i t)) (γ' i t) (γ' i t))) (Icc 0 T) t)
    (h0 : Tendsto (fun i => γ i 0) atTop (𝓝 x)) (h0' : Tendsto (fun i => γ' i 0) atTop (𝓝 v)) :
    TendstoUniformlyOn γ (fun t => x + t • v) atTop (Icc 0 T) ∧
      TendstoUniformlyOn γ' (fun _ => v) atTop (Icc 0 T) := by
  have hc : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun t : ℝ => x + t • v) v (Icc 0 T) t :=
    fun t _ => by simpa using ((hasDerivWithinAt_id t (Icc 0 T)).smul_const v).const_add x
  have hc' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun _ : ℝ => v)
      (-(raisedKoszulOp ((fun _ : F => (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)) (x + t • v))
        (fderiv ℝ (fun _ : F => (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)) (x + t • v)) v v))
      (Icc 0 T) t := fun t _ => by
    rw [raisedKoszulOp_innerSL_fderiv_const]
    simpa using hasDerivWithinAt_const t (Icc (0 : ℝ) T) v
  exact tendstoUniformlyOn_of_metric_tendsto isOpen_univ b (fun _ => innerSL ℝ)
    (fun i => (hb i).contDiffOn) contDiffOn_const (fun _ _ => isCoercive_innerSL)
    (fun C hC _ => hconv C hC) (fun t => x + t • v) (fun _ => v) (fun _ _ => mem_univ _)
    hc hc' γ γ' hvel hacc (by simpa using h0) h0'

/-- **Zero-acceleration limits (CM4.a).** -/
theorem exists_C1_subseq_line_limit_of_metric_tendsto_euclidean
    (b : ℕ → F → F →L[ℝ] F →L[ℝ] ℝ) (hb : ∀ i, ContDiff ℝ 1 (b i))
    {K : Set F} (hK : IsCompact K) (hconv : MapCPConvergenceOn K 1 b (fun _ => innerSL ℝ))
    {T L : ℝ} (γ γ' : ℕ → ℝ → F) (hmaps : ∀ i, ∀ t ∈ Icc 0 T, γ i t ∈ K)
    (hvel : ∀ i, ∀ t ∈ Icc 0 T, HasDerivWithinAt (γ i) (γ' i t) (Icc 0 T) t)
    (hacc : ∀ i, ∀ t ∈ Icc 0 T, HasDerivWithinAt (γ' i)
      (-(raisedKoszulOp (b i (γ i t)) (fderiv ℝ (b i) (γ i t)) (γ' i t) (γ' i t))) (Icc 0 T) t)
    (hbound : ∀ i, ∀ t ∈ Icc 0 T, ‖γ' i t‖ ≤ L) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c c' : ℝ → F,
      TendstoUniformlyOn (fun i => γ (φ i)) c atTop (Icc 0 T) ∧
      TendstoUniformlyOn (fun i => γ' (φ i)) c' atTop (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, c t ∈ K ∧ HasDerivWithinAt c (c' t) (Icc 0 T) t ∧
        HasDerivWithinAt c' 0 (Icc 0 T) t := by
  obtain ⟨φ, hφ, c, c', h1, h2, h3⟩ := exists_C1_subseq_limit_of_metric_tendsto isOpen_univ hK
    (subset_univ K) b (fun _ => innerSL ℝ) (fun i => (hb i).contDiffOn) contDiffOn_const
    (fun _ _ => isCoercive_innerSL) hconv γ γ' hmaps hvel hacc hbound
  refine ⟨φ, hφ, c, c', h1, h2, fun t ht => ⟨(h3 t ht).1, (h3 t ht).2.1, ?_⟩⟩
  have h := (h3 t ht).2.2
  rw [raisedKoszulOp_innerSL_fderiv_const] at h
  simpa using h

end DifferentialGeometry.Analysis.ODE.GeodesicLimits

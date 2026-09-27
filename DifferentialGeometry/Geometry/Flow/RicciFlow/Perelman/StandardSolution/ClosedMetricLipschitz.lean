import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointMetricRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CovariantTimeRegularity
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz
import Mathlib.Topology.Instances.ENNReal.Lemmas
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators Topology
namespace DifferentialGeometry.PDE.RicciFlow
private theorem sqrt_sum_sq_sub_le_closed {ι : Type*} [Fintype ι] {β ψ L : ℝ}
    (c c' : ι → ℝ → ℝ) (hL : 0 ≤ L)
    (hc : ∀ i, ContinuousOn (c i) (Icc β ψ))
    (hd : ∀ i, ∀ r ∈ Ioo β ψ, HasDerivAt (c i) (c' i r) r)
    (hb : ∀ r ∈ Ioo β ψ, Real.sqrt (∑ i, (c' i r) ^ 2) ≤ L)
    {s t : ℝ} (hs : s ∈ Icc β ψ) (ht : t ∈ Icc β ψ) :
    Real.sqrt (∑ i, (c i s - c i t) ^ 2) ≤ L * |s - t| := by
  classical
  by_cases hβψ : β < ψ
  · let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)
    let f : ℝ → EuclideanSpace ℝ ι := fun r => e.symm (fun i => c i r)
    let f' : ℝ → EuclideanSpace ℝ ι := fun r => e.symm (fun i => c' i r)
    have hn (d : ι → ℝ) : ‖(e.symm d : EuclideanSpace ℝ ι)‖ =
        Real.sqrt (∑ i, (d i) ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [show e.symm d i = d i from rfl, Real.norm_eq_abs, sq_abs]
    have hfc : ContinuousOn f (Icc β ψ) :=
      e.symm.continuous.comp_continuousOn (continuousOn_pi.mpr hc)
    have hfd (r : ℝ) (hr : r ∈ Ioo β ψ) : HasDerivAt f (f' r) r := by
      have hh : HasDerivAt (fun ρ : ℝ => (fun i => c i ρ : ι → ℝ)) (fun i => c' i r) r :=
        hasDerivAt_pi.mpr (fun i => hd i r hr)
      exact e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r hh
    have hfl : LipschitzOnWith ⟨L, hL⟩ f (Ioo β ψ) := by
      apply (convex_Ioo β ψ).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (fun r hr => (hfd r hr).hasDerivWithinAt)
      intro r hr
      change ‖f' r‖ ≤ L
      rw [show f' r = e.symm (fun i => c' i r) from rfl, hn]
      exact hb r hr
    have hcl : ContinuousOn f (closure (Ioo β ψ)) := by rwa [closure_Ioo hβψ.ne]
    have hfull := LipschitzOnWith.closure hcl hfl
    rw [closure_Ioo hβψ.ne] at hfull
    have hm := hfull.dist_le_mul s hs t ht
    rw [dist_eq_norm] at hm
    have he : f s - f t = e.symm (fun i => c i s - c i t) := by
      simp only [f, ← map_sub]
      rfl
    rw [he, hn] at hm
    simp only [Real.dist_eq] at hm
    exact hm
  · have he : s = t := by linarith [hs.1, hs.2, ht.1, ht.2]
    subst t
    simp

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem metricCovDeriv_contDiffOn_time
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (gRef : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    ContDiffOn ℝ ∞ (fun t => metricCovDeriv (g t) gRef a x) J := by
  have hx := chartLeviCivitaGoodSet_mem_baseSet (self_mem_chartLeviCivitaGoodSet (I := I) x)
  apply tensor0S_contDiffOn_of_components (coordinateFrameAtBasis (I := I) x hx)
  intro slots
  have hh := referenceCovariantMetricComponents_contMDiffOn g J hgram gRef x a
    (fun q => slots (acEquiv a q))
  have ht := hh.comp (contMDiffOn_id.prodMk contMDiffOn_const)
    (fun t ht => ⟨ht, self_mem_chartLeviCivitaGoodSet (I := I) x⟩)
  apply ht.contDiffOn.congr
  intro t _
  rw [component0S_apply, metricCovDeriv_eq_covDerivOfField, covDerivOfField_eq_iterCov,
    Tensor0SField.domDomCongr_apply]
  change iterCov gRef 2 (metricTensorField (g t)) a x
    (fun q => coordinateFrameAtBasis (I := I) x hx (slots (acEquiv a q))) = _
  congr 1
  funext q
  exact coordinateFrameAt_basis_apply (I := I) x hx (slots (acEquiv a q))

theorem metricDerivNorm_le_of_closed_evolution
    (g : ℝ → SmoothRiemannianMetric I M) (β ψ : ℝ)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (Icc β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (gRef : SmoothRiemannianMetric I M) (a : ℕ)
    (Ev : ℝ → (x : M) → Tensor0SSpace (a + 2) I x) (K : Set M)
    (L : ℝ) (hL : 0 ≤ L)
    (hev : ∀ x ∈ K, ∀ s ∈ Ioo β ψ, ∀ v : Fin (a + 2) → TangentSpace I x,
      HasDerivAt (fun r => metricCovDeriv (g r) gRef a x v) (Ev s x v) s)
    (hb : ∀ x ∈ K, ∀ s ∈ Ioo β ψ, Real.sqrt (normSq0S gRef x (a + 2) (Ev s x)) ≤ L) :
    ∀ s ∈ Icc β ψ, ∀ t ∈ Icc β ψ, ∀ x ∈ K,
      metricDerivNorm a (g s) (g t) gRef x ≤ L * |s - t| := by
  classical
  intro s hs t ht x hx
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis gRef x
  have hinv : MetricInverseInBasis gRef x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have hh := metricInverseInBasis_of_orthonormal gRef basis hON
    intro i j
    simpa only [identityInvMetric, diagonalInvMetric] using hh i j
  let c := fun slots r => component0S basis (metricCovDeriv (g r) gRef a x) slots
  let c' := fun slots r => component0S basis (Ev r x) slots
  have hc (slots : Fin (a + 2) → Fin (Module.finrank ℝ (TangentSpace I x))) :
      ContinuousOn (c slots) (Icc β ψ) := by
    have hh := (tensor0SEvalCLM (I := I) (fun q => basis (slots q))).continuous.comp_continuousOn
      (metricCovDeriv_contDiffOn_time g (Icc β ψ) hgram gRef a x).continuousOn
    exact hh
  have hd : ∀ slots, ∀ r ∈ Ioo β ψ, HasDerivAt (c slots) (c' slots r) r := by
    intro slots r hr
    exact hev x hx r hr (fun q => basis (slots q))
  have hbound : ∀ r ∈ Ioo β ψ, Real.sqrt (∑ slots, (c' slots r) ^ 2) ≤ L := by
    intro r hr
    rw [← normSq0S_identity_eq_sum_sq gRef x (a + 2) basis hinv (Ev r x)]
    exact hb x hx r hr
  have hh := sqrt_sum_sq_sub_le_closed c c' hL hc hd hbound hs ht
  have he : metricDerivNorm a (g s) (g t) gRef x =
      Real.sqrt (∑ slots, (c slots s - c slots t) ^ 2) := by
    rw [metricDerivNorm, metricDiffCovDerivAt,
      normSq0S_identity_eq_sum_sq gRef x (a + 2) basis hinv]
    congr 1
  rwa [he]
end DifferentialGeometry.PDE.RicciFlow

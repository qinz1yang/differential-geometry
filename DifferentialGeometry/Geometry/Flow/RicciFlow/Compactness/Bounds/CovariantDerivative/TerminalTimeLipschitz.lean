import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.CovariantContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.TimeLipschitz

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_metric_time_lipschitz_constant_of_local_solution
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    (gRef : SmoothRiemannianMetric I M) {B : ℝ} (hB : 1 ≤ B)
    (N : ℕ) (C : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K) :
    ∀ q ≤ N, ∃ L : ℝ, 0 ≤ L ∧
      ∀ (g : ℝ → SmoothRiemannianMetric I M)
        (D : RealTimeInterval) (S : SolutionOn (I := I) (M := U) D),
      IsSolutionOn S →
      (∀ t, S.family.metric t = (g t).restrictOpen U) →
      ∀ {a b : ℝ}, a < b → (Icc a b ⊆ D.carrier) → (Ico a b ⊆ D.regular) →
      (∀ t ∈ Ico a b, MetricUniformEquivalentOn U gRef (g t) B) →
      (∀ r, 1 ≤ r → r ≤ N → ∀ t ∈ Ico a b, ∀ x ∈ U,
        metricCovDerivNorm r (g t) gRef x ≤ C r) →
      (∀ ψ ∈ Ico a b, MovingShiBoundOn U a ψ (fun _ t => g t) N K) →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x ∈ U,
        metricDerivNorm q (g s) (g t) gRef x ≤ L * |s - t| := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  intro q hq
  obtain ⟨L, hL, hbound⟩ := exists_metric_time_lipschitz_constant_of_local_evolution
    U.isOpen gRef hB N C hK q hq
  refine ⟨L, hL, ?_⟩
  intro g D S hS hmet a b hab hslab hreg hequiv hcov hShi
  have hinter := hbound g hequiv hcov hShi
    (fun t ht x hx v =>
      Perelman.KappaSolutions.metricCovDeriv_hasDerivAt_of_local_solution
        g gRef U S hS hmet q (hreg ht) ⟨x, hx⟩ v)
  have hterminal (s : ℝ) (x : M) (hx : x ∈ U) :
      ContinuousWithinAt (fun t => metricDerivNorm q (g s) (g t) gRef x) (Iic b) b := by
    classical
    let R := gRef.restrictOpen U
    let y : U := ⟨x, hx⟩
    obtain ⟨basis, horth⟩ := exists_orthonormal_basis R y
    have hinv := metricInverseInBasis_of_orthonormal R basis horth
    have hnorm (h : SmoothRiemannianMetric I U) :
        metricDerivNorm q ((g s).restrictOpen U) h R y = Real.sqrt
          (∑ slots : Fin (q + 2) → Fin (Module.finrank ℝ (TangentSpace I y)),
            (component0S basis (metricCovDeriv ((g s).restrictOpen U) R q y) slots -
              component0S basis (metricCovDeriv h R q y) slots) ^ 2) := by
      rw [metricDerivNorm, metricDiffCovDerivAt,
        normSq0S_identity_eq_sum_sq R y (q + 2) basis hinv]
      congr 1
    have hc : ContinuousWithinAt
        (fun t => metricDerivNorm q ((g s).restrictOpen U) (S.base.metric t) R y)
        (Iic b) b := by
      simp only [hnorm]
      apply ContinuousWithinAt.sqrt
      apply tendsto_finsetSum
      intro slots _
      exact (continuousWithinAt_const.sub
        (solution_metricCovDeriv_component_continuousWithinAt_terminal S hS hab hslab
          (Ioo_subset_Ico_self.trans hreg) R q y basis slots)).pow 2
    have heq : (fun t => metricDerivNorm q ((g s).restrictOpen U) (S.base.metric t) R y) =
        (fun t => metricDerivNorm q (g s) (g t) gRef x) := by
      funext t
      change metricDerivNorm q ((g s).restrictOpen U) (S.family.metric t) R y = _
      rw [hmet t]
      exact metricDerivNorm_restrictOpen (g s) (g t) gRef U q y
    rwa [heq] at hc
  have hright (s : ℝ) (hs : s ∈ Ico a b) (x : M) (hx : x ∈ U) :
      metricDerivNorm q (g s) (g b) gRef x ≤ L * |s - b| := by
    have hleft := (hterminal s x hx).mono Iio_subset_Iic_self
    have hright : Tendsto (fun t : ℝ => L * |s - t|) (𝓝[<] b) (𝓝 (L * |s - b|)) :=
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_id).abs).tendsto.mono_left
        nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [Ico_mem_nhdsLT hab] with t ht
    exact hinter s hs t ht x hx
  intro s hs t ht x hx
  rcases hs.2.lt_or_eq with hsb | hsb
  · rcases ht.2.lt_or_eq with htb | htb
    · exact hinter s ⟨hs.1, hsb⟩ t ⟨ht.1, htb⟩ x hx
    · subst t
      exact hright s ⟨hs.1, hsb⟩ x hx
  · subst s
    rcases ht.2.lt_or_eq with htb | htb
    · rw [metricDerivNorm_symm, abs_sub_comm]
      exact hright t ⟨ht.1, htb⟩ x hx
    · subst t
      rw [metricDerivNorm_self, sub_self, abs_zero, mul_zero]

end DifferentialGeometry.PDE.RicciFlow

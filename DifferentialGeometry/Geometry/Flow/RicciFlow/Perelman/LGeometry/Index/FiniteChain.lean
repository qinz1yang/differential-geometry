import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.AdaptedCutoffTrace
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem sum_lRegularizedIndex_trace_smul_function_of_local_isometries
    {n : ℕ} (M : Fin (n + 1) → Type*)
    [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
    [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    (D : Fin (n + 1) → RealTimeInterval)
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (t : Fin (n + 2) → ℝ) (ht : Monotone t) (ht0 : 0 < t 0)
    (α : (i : Fin (n + 1)) → ℝ → M i)
    (P : (i : Fin (n + 1)) → Fin (Module.finrank ℝ E) → ∀ r, TangentSpace I (α i r))
    (chi dchi : ℝ → ℝ)
    (hchi : ∀ i : Fin (n + 1), ∀ r ∈ Icc (t i.castSucc) (t i.succ), HasDerivAt chi (dchi r) r)
    (hclock : ∀ i, ∀ r ∈ Icc (t i.castSucc) (t i.succ), T - r ^ 2 ∈ (D i).regular)
    (hα : ∀ i, ∀ r ∈ Icc (t i.castSucc) (t i.succ), MDifferentiableAt 𝓘(ℝ, ℝ) I (α i) r)
    (hP : ∀ i k r, r ∈ Icc (t i.castSucc) (t i.succ) →
      DifferentiableAt ℝ (chartRepAt (I := I) (α i) (P i k) r) r)
    (hDP : ∀ i k, IsLAdapted (S i) T (α i) (P i k) (Icc (t i.castSucc) (t i.succ)))
    (hON : ∀ i k l, ((S i).base.metric (T - (t i.succ) ^ 2)).inner
      (α i (t i.succ)) (P i k (t i.succ)) (P i l (t i.succ)) = if k = l then 1 else 0)
    (hIint : ∀ i k, IntervalIntegrable
      (lRegularizedIndexIntegrand (S i) T (α i) (fun r => chi r • P i k r)
        (fun r => chi r • P i k r)) volume (t i.castSucc) (t i.succ))
    (henergy : ∀ i : Fin (n + 1), IntervalIntegrable (fun r => (dchi r) ^ 2) volume (t i.castSucc) (t i.succ))
    (hHam : ∀ i, IntervalIntegrable (fun r => (chi r / r) ^ 2 * lHamSq (S i) T (α i) r)
      volume (t i.castSucc) (t i.succ))
    (X : Fin n → Type*) [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
    [∀ i, IsManifold I ∞ (X i)] [∀ i, T2Space (X i)]
    (g : (i : Fin n) → SmoothRiemannianMetric I (X i))
    (x : (i : Fin n) → X i)
    (leftMap : (i : Fin n) → X i → M i.castSucc)
    (rightMap : (i : Fin n) → X i → M i.succ)
    (hleft : ∀ i, IsLocalDiffeomorph I I ∞ (leftMap i))
    (hright : ∀ i, IsLocalDiffeomorph I I ∞ (rightMap i))
    (hmetricLeft : ∀ i : Fin n, g i = localPullMetric
      ((S i.castSucc).base.metric (T - (t i.castSucc.succ) ^ 2)) (leftMap i) (hleft i))
    (hmetricRight : ∀ i : Fin n, g i = localPullMetric
      ((S i.succ).base.metric (T - (t i.castSucc.succ) ^ 2)) (rightMap i) (hright i))
    (hpointLeft : ∀ i : Fin n, α i.castSucc (t i.castSucc.succ) = leftMap i (x i))
    (hpointRight : ∀ i : Fin n, α i.succ (t i.castSucc.succ) = rightMap i (x i)) :
    (∑ i : Fin (n + 1), ∑ k : Fin (Module.finrank ℝ E),
      lRegularizedIndex (S i) T (α i) (fun r => chi r • P i k r)
        (fun r => chi r • P i k r) (t i.castSucc) (t i.succ)) =
      (Module.finrank ℝ E : ℝ) / 2 *
          (∑ i : Fin (n + 1), ∫ r in t i.castSucc..t i.succ, (dchi r) ^ 2) -
        (t (Fin.last (n + 1)) * (chi (t (Fin.last (n + 1)))) ^ 2 *
            (S (Fin.last n)).scalar (T - (t (Fin.last (n + 1))) ^ 2)
              (α (Fin.last n) (t (Fin.last (n + 1)))) -
          t 0 * (chi (t 0)) ^ 2 * (S 0).scalar (T - (t 0) ^ 2) (α 0 (t 0))) -
        ∑ i : Fin (n + 1), ∫ r in t i.castSucc..t i.succ,
          (chi r / r) ^ 2 * lHamSq (S i) T (α i) r := by
  let boundary (i : Fin (n + 1)) (r : ℝ) := r * (chi r) ^ 2 * (S i).scalar (T - r ^ 2) (α i r)
  have hmatch (i : Fin n) : boundary i.castSucc (t i.castSucc.succ) =
      boundary i.succ (t i.succ.castSucc) := by
    have htime : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
    rw [htime]
    dsimp only [boundary]
    congr 1
    have hleftScalar := metricScalarAt_localPull
      ((S i.castSucc).base.metric (T - (t i.castSucc.succ) ^ 2)) (leftMap i) (hleft i) (x i)
    have hrightScalar := metricScalarAt_localPull
      ((S i.succ).base.metric (T - (t i.castSucc.succ) ^ 2)) (rightMap i) (hright i) (x i)
    rw [← hmetricLeft i] at hleftScalar
    rw [← hmetricRight i] at hrightScalar
    change metricScalarAt ((S i.castSucc).base.metric (T - (t i.castSucc.succ) ^ 2))
        (α i.castSucc (t i.castSucc.succ)) =
      metricScalarAt ((S i.succ).base.metric (T - (t i.castSucc.succ) ^ 2))
        (α i.succ (t i.castSucc.succ))
    rw [hpointLeft i, hpointRight i]
    exact hleftScalar.symm.trans hrightScalar
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ =>
    lRegularizedIndex_trace_smul_function (S i) (hS i) T (α i) (P i) chi dchi
      (t i.castSucc) (t i.succ) (ht0.trans_le (ht (Fin.zero_le _)))
      (ht i.castSucc_le_succ) (hchi i) (hclock i) (hα i) (hP i) (hDP i) (hON i)
      (hIint i) (henergy i) (hHam i))
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hboundary : (∑ i : Fin (n + 1),
      (boundary i (t i.succ) - boundary i (t i.castSucc))) =
      boundary (Fin.last n) (t (Fin.last (n + 1))) - boundary 0 (t 0) := by
    rw [Finset.sum_sub_distrib,
      Fin.sum_univ_castSucc (fun i => boundary i (t i.succ)),
      Fin.sum_univ_succ (fun i => boundary i (t i.castSucc))]
    have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hmatch i)
    rw [hs]
    change (∑ i : Fin n, boundary i.succ (t i.succ.castSucc)) +
      boundary (Fin.last n) (t (Fin.last (n + 1))) -
      (boundary 0 (t 0) + ∑ i : Fin n, boundary i.succ (t i.succ.castSucc)) = _
    ring
  change _ = (Module.finrank ℝ E : ℝ) / 2 * _ -
    (∑ i : Fin (n + 1), (boundary i (t i.succ) - boundary i (t i.castSucc))) - _ at hsum
  rw [hboundary] at hsum
  exact hsum

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

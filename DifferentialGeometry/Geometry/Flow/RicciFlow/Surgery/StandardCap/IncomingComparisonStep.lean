import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorChartFlow
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

set_option autoImplicit false
noncomputable section
open Set Manifold TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_incoming_chart_extension_step_of_standard_metric_close
    (theta : ℝ) (htheta : 0 ≤ theta) (htheta1 : theta < 1) (C : ℝ≥0) :
    ∃ epsilon A delta : ℝ, 0 < epsilon ∧ 0 < A ∧ 0 < delta ∧
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s)
        (U : Opens E3) (Psi : U → H.backwardSurvivorDomain first last hle)
        (q : ℝ) (hq : 0 < q) (tau : ℝ),
      ∀ hPsi : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Psi,
      tau ∈ Ico (H.time last) s →
      let f := fun x : U => (Psi x).val
      let hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
        isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hPsi
      ∀ S : StandardSolution, q * (tau - H.time first) ∈ Icc 0 theta →
      (∀ x : U, ∀ j ≤ 2,
        metricDerivNorm j (localPullMetric (scaleMetric q hq (G.flow.base.metric tau)) f hf)
          ((S.val.metric (q * (tau - H.time first))).restrictOpen U)
          (StandardCap.metric.restrictOpen U) x ≤ epsilon) →
      (∀ x : U, ∀ t ∈ Ioo tau s, A * q < G.flow.scalar t (f x) →
        |derivWithin (fun v => G.flow.scalar v (f x)) (Iic t) t| ≤ C * G.flow.scalar t (f x) ^ 2) →
      q * (s - tau) ≤ delta →
      ∃ Xi : U → H.backwardSurvivorIncomingDomain first last hle G,
        IsLocalDiffeomorph ThreeModel ThreeModel ∞ Xi ∧
        (∀ x, (Xi x).val = Psi x) ∧
        ∀ x : U, G.flow.scalar tau (f x) ≤ A * q := by
  obtain ⟨epsilon, A, hepsilon, hA, hscalar⟩ :=
    StandardCap.exists_uniform_scalar_bound_of_standard_metric_close_on_opens theta htheta htheta1
  let delta := (2 * ((C : ℝ) + 1) * A)⁻¹
  have hdelta : 0 < delta := inv_pos.mpr (by positivity)
  refine ⟨epsilon, A, delta, hepsilon, hA, hdelta, ?_⟩
  intro H first last hle s G U Psi q hq tau hPsi htau f hf S htime hclose hbound hstep
  have hanchor (x : U) : G.flow.scalar tau (f x) ≤ A * q := by
    have hh := hscalar U (localPullMetric (scaleMetric q hq (G.flow.base.metric tau)) f hf)
      S (q * (tau - H.time first)) htime x (hclose x)
    rw [metricScalarAt_localPull, metricScalarAt_scaleMetric] at hh
    change |q⁻¹ * G.flow.scalar tau (f x)| ≤ A at hh
    have hlo := (le_abs_self _).trans hh
    rw [← div_eq_inv_mul, div_le_iff₀ hq] at hlo
    exact hlo
  have hbudget : 2 * (C : ℝ) * (A * q) * (s - tau) ≤ 1 := by
    have hfac : 0 ≤ 2 * (C : ℝ) * A := by positivity
    have hh := mul_le_mul_of_nonneg_left hstep hfac
    have heq : (2 * ((C : ℝ) + 1) * A) * delta = 1 := mul_inv_cancel₀ (by positivity)
    have hc : 2 * (C : ℝ) * A * delta ≤ 1 := by nlinarith [hdelta]
    nlinarith only [hh, hc]
  obtain ⟨Xi, hXi, hproj⟩ := H.exists_backwardSurvivorIncoming_chart_of_scalar_bound_at_time
    first last hle G Psi hPsi (mul_pos hA hq) le_rfl htau hbound hanchor hbudget
  exact ⟨Xi, hXi, hproj, hanchor⟩

theorem exists_uniform_normalized_incoming_chart_step_of_standard_metric_close
    (theta : ℝ) (htheta : 0 ≤ theta) (htheta1 : theta < 1) (C : ℝ≥0) :
    ∃ epsilon A delta : ℝ, 0 < epsilon ∧ 0 < A ∧ 0 < delta ∧
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (U : Opens E3) (Psi : U → H.backwardSurvivorDomain first last hle)
        (q : ℝ) (hq : 0 < q) (tau : ℝ)
        (hPsi : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Psi), tau ∈ Ico (H.time last) s →
      let f := fun x : U => (Psi x).val
      let hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
        isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hPsi
      ∀ S : StandardSolution, q * (tau - H.time first) ∈ Icc 0 theta →
      (∀ x : U, ∀ j ≤ 2,
        metricDerivNorm j (localPullMetric (scaleMetric q hq (G.flow.base.metric tau)) f hf)
          ((S.val.metric (q * (tau - H.time first))).restrictOpen U)
          (StandardCap.metric.restrictOpen U) x ≤ epsilon) →
      (∀ x : U, ∀ t ∈ Ioo tau s, A * q < G.flow.scalar t (f x) →
        |derivWithin (fun v => G.flow.scalar v (f x)) (Iic t) t| ≤ C * G.flow.scalar t (f x) ^ 2) →
      q * (s - tau) ≤ delta →
      ∀ (J : U → (H.stage first).Carrier),
        (∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Psi x) = J x) →
      ∀ g0 : SmoothRiemannianMetric ThreeModel U,
        (∀ x (v w : TangentSpace ThreeModel x),
          g0.inner x v w = q * (H.initialMetric first).inner (J x)
            (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x w)) →
      ∃ (Xi : U → H.backwardSurvivorIncomingDomain first last hle G)
        (hXi : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Xi),
        (∀ x, (Xi x).val = Psi x) ∧
        (∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Xi x).val = J x) ∧
      ∃ gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G),
        (∀ (j : Fin H.eventCount) (hj : first ≤ j.castSucc) (hjl : j.succ ≤ last),
          ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
            gflow t = (H.backwardSurvivorSlabMetric first last hle j hj hjl t).restrictOpen
              (H.backwardSurvivorIncomingDomain first last hle G)) ∧
        (∀ t ∈ Icc (H.time last) s, gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) ∧
        ∃ Q : SolutionOn (I := ThreeModel) (M := U)
            (RealTimeInterval.closed 0 (q * (s - H.time first))
              (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity)),
          IsSolutionOn Q ∧ Q.base.metric 0 = g0 ∧
          (∀ t, Q.base.metric t =
            localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Xi hXi) ∧
          ∀ (x : U) (i j : Fin (Module.finrank ℝ ThreeSpace)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
              (fun z : ℝ × U => chartGramMatrix (Q.base.metric z.1) x z.2 i j)
              (Icc 0 (q * (s - H.time first)) ×ˢ
                (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).baseSet) := by
  obtain ⟨epsilon, A, delta, hepsilon, hA, hdelta, hstep⟩ :=
    exists_uniform_incoming_chart_extension_step_of_standard_metric_close theta htheta htheta1 C
  refine ⟨epsilon, A, delta, hepsilon, hA, hdelta, ?_⟩
  intro H first last hle s G L hinit U Psi q hq tau hPsi htau f hf S htime hclose hbound hremaining J hbirth g0 hzero
  obtain ⟨Xi, hXi, hproj, _hanchor⟩ := hstep H first last hle s G U Psi q hq tau hPsi htau
    S htime hclose hbound hremaining
  have hbirth' : ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Xi x).val = J x := by
    intro x
    rw [hproj x]
    exact hbirth x
  exact ⟨Xi, hXi, hproj, hbirth',
    H.exists_normalized_backwardSurvivorIncoming_chart_solution first last hle G L hinit
      Xi hXi J hbirth' q hq g0 hzero⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

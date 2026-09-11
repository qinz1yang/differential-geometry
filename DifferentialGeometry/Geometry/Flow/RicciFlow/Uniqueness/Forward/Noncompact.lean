import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.Vanishing
import DifferentialGeometry.Analysis.ODE.Gronwall.ClosedEdge
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [SigmaCompactSpace M]

theorem metric_eq_of_energy_zero_noncompact
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {t : ℝ}
    (hdcont : Continuous (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x))
    (hidens : Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hE : forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t = 0) :
    g₁ t = g₂ t := by
  have hE' : ∫ x, forwardUniqueDensity (I := I) g₁ g₂ t x
      ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t) = 0 := hE
  have hae : (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      =ᵐ[riemannianMeasureFamily (I := I) (M := M) g₁ t] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun x => density_nonneg (I := I) g₁ g₂ t x) hidens).mp hE'
  have hμpos : (riemannianMeasureFamily (I := I) (M := M) g₁ t).IsOpenPosMeasure := by
    rw [riemannianMeasureFamily_def]
    exact riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) (g₁ t)
  have heq : (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x) = 0 :=
    (Continuous.ae_eq_iff_eq (riemannianMeasureFamily (I := I) (M := M) g₁ t)
      hdcont continuous_const).mp hae
  have hmetric_ext : ∀ {g g' : SmoothRiemannianMetric I M},
      (∀ (x : M) (v w : TangentSpace I x), g.inner x v w = g'.inner x v w) → g = g' := by
    intro g g' h
    obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
    obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g'
    have hi : i₁ = i₂ :=
      funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
    subst hi
    rfl
  apply hmetric_ext
  intro x X Y
  have hx : forwardUniqueDensity (I := I) g₁ g₂ t x = 0 := congrFun heq x
  have hmnn : (0 : ℝ) ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [metricDiffSq_def]
    exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
  have hmle := metricDiffSq_le_dens (I := I) g₁ g₂ t x
  have hm : normSq0S (I := I) (g₁ t) x 2
      (metricDiffAt (I := I) (g₁ t) (g₂ t) x) = 0 := by
    rw [← metricDiffSq_def]
    linarith
  have h0 : metricDiffAt (I := I) (g₁ t) (g₂ t) x = 0 :=
    ((tensor0SMetricData (I := I) (g₁ t) x 2).inner_self_eq_zero_iff _).mp hm
  have hval := congrArg (fun A : Tensor0SSpace 2 I x =>
    A (fun i : Fin 2 => if i = 0 then X else Y)) h0
  simp only [metricDiffAt_apply, Tensor0SSpace.zero_apply] at hval
  norm_num at hval
  linarith [hval]

theorem metric_eq_on_of_energy_deriv_bound
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (K : ℝ)
    (hcont : ContinuousOn
      (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Set.Icc a b))
    (henergy' : ℝ → ℝ)
    (hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (forwardUniqueEnergy (I := I) (M := M) g₁ g₂)
        (henergy' t) t)
    (hbound : ∀ t ∈ Set.Ioo a b,
      henergy' t ≤ K * forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t)
    (hinitial : g₁ a = g₂ a)
    (hdcont : ∀ t ∈ Set.Icc a b,
      Continuous (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x))
    (hden : ∀ t ∈ Set.Icc a b,
      Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
        (riemannianMeasureFamily (I := I) (M := M) g₁ t)) :
    ∀ t ∈ Set.Icc a b, g₁ t = g₂ t := by
  have hzero : ∀ t ∈ Set.Icc a b,
      forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t = 0 := by
    apply DifferentialGeometry.Analysis.ODE.gronwall_zero_on hab
      (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) henergy' hcont
      (by
        simp only [forwardUniqueEnergy,
          density_eq_zero_of_eq (I := I) g₁ g₂ hinitial, integral_zero])
      (fun t _ => integral_nonneg fun x =>
        density_nonneg (I := I) g₁ g₂ t x)
      hderiv hbound
  intro t ht
  exact metric_eq_of_energy_zero_noncompact (I := I) g₁ g₂
    (hdcont t ht) (hden t ht) (hzero t ht)

structure NoncompactForwardUniquenessCriterion
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (a b K : ℝ) (energy' : ℝ → ℝ) : Prop where
  interval : a < b
  energyCont : ContinuousOn
    (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Set.Icc a b)
  energyDerivative : ∀ t ∈ Set.Ioo a b,
    HasDerivAt (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (energy' t) t
  energyBound : ∀ t ∈ Set.Ioo a b,
    energy' t ≤ K * forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t
  initial : g₁ a = g₂ a
  densityCont : ∀ t ∈ Set.Icc a b,
    Continuous (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
  densityIntegrable : ∀ t ∈ Set.Icc a b,
    Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t)

theorem forward_unique_of_noncompact_criterion
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b K : ℝ} {energy' : ℝ → ℝ}
    (h : NoncompactForwardUniquenessCriterion (I := I) g₁ g₂ a b K energy') :
    ∀ t ∈ Set.Icc a b, g₁ t = g₂ t := by
  exact metric_eq_on_of_energy_deriv_bound (I := I) g₁ g₂ h.interval K h.energyCont
    energy' h.energyDerivative h.energyBound h.initial h.densityCont h.densityIntegrable

end DifferentialGeometry.PDE.RicciFlow

end

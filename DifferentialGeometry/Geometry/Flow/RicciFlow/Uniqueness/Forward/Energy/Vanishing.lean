import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.Inequality
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Analysis.ODE.Gronwall.ClosedEdge

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M]
variable [CompactSpace M] [I.Boundaryless]

section EdgeValue

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem normSq0S_zero (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) :
    normSq0S (I := I) g x s 0 = 0 :=
  ((tensor0SMetricData (I := I) g x s).inner_self_eq_zero_iff 0).2 rfl

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem eq_zero_of_normSq0S (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {A : Tensor0SSpace s I x} (h : normSq0S (I := I) g x s A = 0) : A = 0 :=
  ((tensor0SMetricData (I := I) g x s).inner_self_eq_zero_iff A).1 h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem energy_nonneg (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ) :
    0 ≤ forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t :=
  integral_nonneg fun x => density_nonneg (I := I) g₁ g₂ t x

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem density_eq_zero_of_eq (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {t : ℝ}
    (h : g₁ t = g₂ t) (x : M) :
    forwardUniqueDensity (I := I) g₁ g₂ t x = 0 := by
  rw [forwardUniqueDensity, metricDiffSq_def, connectionDifferenceSq_def, rmDiffSq_def, h]
  rw [metricDiffAt_self, connectionDifferenceLowAt_self, rmDiffLowAt_self,
    normSq0S_zero, normSq0S_zero, normSq0S_zero]
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem energy_eq_zero_of_eq (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {t : ℝ}
    (h : g₁ t = g₂ t) :
    forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t = 0 := by
  simp only [forwardUniqueEnergy, density_eq_zero_of_eq (I := I) g₁ g₂ h, integral_zero]

end EdgeValue

section EnergyZero

theorem energy_zero_on
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (Adot : ℝ → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : ℝ → (x : M) → Tensor0SSpace 4 I x)
    (Sfield : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Uflux : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (rem : ℝ → (x : M) → Tensor0SSpace 4 I x)
    {a c ε δ C_A C_R C_Ric C_V C_U C_rem : ℝ}
    (hac : a < c)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ioo a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdens : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (Ioo a c ×ˢ (Set.univ : Set M)))
    (hPDE₁ : ∀ t ∈ Ioo a c, ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : ℝ => (g₁ r).inner x X Y)
        ((-2 : ℝ) * metricRicciAt (I := I) (g₁ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t)
    (hPDE₂ : ∀ t ∈ Ioo a c, ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : ℝ => (g₂ r).inner x X Y)
        ((-2 : ℝ) * metricRicciAt (I := I) (g₂ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t)
    (hA : ∀ t ∈ Ioo a c, ∀ (x : M) (v : Fin 3 → TangentSpace I x),
      HasDerivAt (fun r : ℝ => connectionDifferenceLowAt (I := I) (g₁ r) (g₂ r) x v) (Adot t x v) t)
    (hS : ∀ t ∈ Ioo a c, ∀ (x : M) (v : Fin 4 → TangentSpace I x),
      HasDerivAt (fun r : ℝ => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x v) (Sdot t x v) t)
    (hε : 0 < ε) (hδ : 0 < δ) (habs : δ * C_A + ε ≤ 1)
    (hcar : ∀ t ∈ Ioo a c, ∀ x, Sfield t x = rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)
    (hSdec : ∀ t ∈ Ioo a c, ∀ x, Sdot t x =
      roughLap0SField (I := I) (g₁ t) (Sfield t) x +
        covDiv0SField (I := I) (g₁ t) (Uflux t) x + rem t x)
    (hUb : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 5 (Uflux t x) ≤
      C_U * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hrem : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 4 (rem t x) ≤
      C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hreact : ∀ t ∈ Ioo a c, ∀ x,
      movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
          (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hRic : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 2
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) ≤
      C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hAdot : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
      C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
        normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) (Sfield t) x)))
    (hvol : ∀ t ∈ Ioo a c, ∀ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V)
    (hirest : ∀ t ∈ Ioo a c, Integrable (fun x => rateRest (I := I) g₁ g₂ Adot t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hipair : ∀ t ∈ Ioo a c, Integrable
      (fun x => 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hilap : ∀ t ∈ Ioo a c, Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (roughLap0SField (I := I) (g₁ t) (Sfield t) x) (Sfield t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidiv : ∀ t ∈ Ioo a c, Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (covDiv0SField (I := I) (g₁ t) (Uflux t) x) (Sfield t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hirem : ∀ t ∈ Ioo a c, Integrable
      (fun x => inner0S (I := I) (g₁ t) x 4 (rem t x) (Sfield t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hinab : ∀ t ∈ Ioo a c, Integrable (fun x => inner0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (Sfield t) x) (Uflux t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidis : ∀ t ∈ Ioo a c, Integrable (fun x => normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (Sfield t) x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidens : ∀ t ∈ Ioo a c, Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hinit : g₁ a = g₂ a)
    (hcont : ContinuousOn (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Icc a c)) :
    ∀ t ∈ Icc a c, forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t = 0 := by
  refine DifferentialGeometry.Analysis.ODE.gronwall_zero_on
    (K := C_R + 4 * C_Ric + 2 + δ * C_A + δ⁻¹ + C_V + ε⁻¹ * C_U + C_rem) hac
    (forwardUniqueEnergy (I := I) (M := M) g₁ g₂)
    (forwardUniqueRate (I := I) (M := M) g₁ g₂ Adot Sdot)
    hcont (energy_eq_zero_of_eq (I := I) g₁ g₂ hinit)
    (fun t _ => energy_nonneg (I := I) g₁ g₂ t)
    (fun t ht => forwardUniqueEnergy_hasDerivAt (I := I) g₁ g₂ Adot Sdot isOpen_Ioo ht
      hgram hdens (hPDE₁ t ht) (hPDE₂ t ht) (hA t ht) (hS t ht))
    (fun t ht => ?_)
  have hle := forwardUniqueRate_le (I := I) g₁ g₂ Adot Sdot (Sfield t) (Uflux t) (rem t)
    hε hδ habs (hcar t ht) (hSdec t ht) (hUb t ht) (hrem t ht) (hreact t ht) (hRic t ht)
    (hAdot t ht) (hvol t ht) (hirest t ht) (hipair t ht) (hilap t ht) (hidiv t ht)
    (hirem t ht) (hinab t ht) (hidis t ht) (hidens t ht)
  have hD := dissipation_nonneg (I := I) (M := M) g₁ (Sfield t) t
  linarith

end EnergyZero

section IntegralZero

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem metricExtInner {g g' : SmoothRiemannianMetric I M}
    (h : ∀ (x : M) (v w : TangentSpace I x), g.inner x v w = g'.inner x v w) : g = g' := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g'
  have hi : i₁ = i₂ :=
    funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
  subst hi
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem metric_eq_of_energy_zero (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {t : ℝ}
    (hdcont : Continuous (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x))
    (hidens : Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hE : forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t = 0) :
    g₁ t = g₂ t := by
  rw [forwardUniqueEnergy] at hE
  have hae : (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      =ᵐ[riemannianMeasureFamily (I := I) (M := M) g₁ t] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun x => density_nonneg (I := I) g₁ g₂ t x) hidens).mp hE
  have : (riemannianMeasureFamily (I := I) (M := M) g₁ t).IsOpenPosMeasure := by
    rw [riemannianMeasureFamily_def]
    exact riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) (g₁ t)
  have heq : (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x) = 0 :=
    (Continuous.ae_eq_iff_eq (riemannianMeasureFamily (I := I) (M := M) g₁ t)
      hdcont continuous_const).mp hae
  refine metricExtInner (I := I) fun x X Y => ?_
  have hx : forwardUniqueDensity (I := I) g₁ g₂ t x = 0 := congrFun heq x
  have hmnn : (0 : ℝ) ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [metricDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
  have hmle := metricDiffSq_le_dens (I := I) g₁ g₂ t x
  have hm : normSq0S (I := I) (g₁ t) x 2 (metricDiffAt (I := I) (g₁ t) (g₂ t) x) = 0 := by
    rw [← metricDiffSq_def]; linarith
  have h0 : metricDiffAt (I := I) (g₁ t) (g₂ t) x = 0 :=
    eq_zero_of_normSq0S (I := I) (g₁ t) x 2 hm
  have hval := congrArg (fun A : Tensor0SSpace 2 I x =>
    A (fun i : Fin 2 => if i = 0 then X else Y)) h0
  simp only [metricDiffAt_apply, Tensor0SSpace.zero_apply] at hval
  norm_num at hval
  linarith [hval]

end IntegralZero

section Capstone

theorem metrics_eq_on
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (Adot : ℝ → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : ℝ → (x : M) → Tensor0SSpace 4 I x)
    (Sfield : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Uflux : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (rem : ℝ → (x : M) → Tensor0SSpace 4 I x)
    {a c ε δ C_A C_R C_Ric C_V C_U C_rem : ℝ}
    (hac : a < c)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ioo a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdens : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (Ioo a c ×ˢ (Set.univ : Set M)))
    (hPDE₁ : ∀ t ∈ Ioo a c, ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : ℝ => (g₁ r).inner x X Y)
        ((-2 : ℝ) * metricRicciAt (I := I) (g₁ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t)
    (hPDE₂ : ∀ t ∈ Ioo a c, ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : ℝ => (g₂ r).inner x X Y)
        ((-2 : ℝ) * metricRicciAt (I := I) (g₂ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t)
    (hA : ∀ t ∈ Ioo a c, ∀ (x : M) (v : Fin 3 → TangentSpace I x),
      HasDerivAt (fun r : ℝ => connectionDifferenceLowAt (I := I) (g₁ r) (g₂ r) x v) (Adot t x v) t)
    (hS : ∀ t ∈ Ioo a c, ∀ (x : M) (v : Fin 4 → TangentSpace I x),
      HasDerivAt (fun r : ℝ => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x v) (Sdot t x v) t)
    (hε : 0 < ε) (hδ : 0 < δ) (habs : δ * C_A + ε ≤ 1)
    (hcar : ∀ t ∈ Ioo a c, ∀ x, Sfield t x = rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)
    (hSdec : ∀ t ∈ Ioo a c, ∀ x, Sdot t x =
      roughLap0SField (I := I) (g₁ t) (Sfield t) x +
        covDiv0SField (I := I) (g₁ t) (Uflux t) x + rem t x)
    (hUb : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 5 (Uflux t x) ≤
      C_U * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hrem : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 4 (rem t x) ≤
      C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hreact : ∀ t ∈ Ioo a c, ∀ x,
      movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
          (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hRic : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 2
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) ≤
      C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hAdot : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
      C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
        normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) (Sfield t) x)))
    (hvol : ∀ t ∈ Ioo a c, ∀ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V)
    (hirest : ∀ t ∈ Ioo a c, Integrable (fun x => rateRest (I := I) g₁ g₂ Adot t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hipair : ∀ t ∈ Ioo a c, Integrable
      (fun x => 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hilap : ∀ t ∈ Ioo a c, Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (roughLap0SField (I := I) (g₁ t) (Sfield t) x) (Sfield t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidiv : ∀ t ∈ Ioo a c, Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (covDiv0SField (I := I) (g₁ t) (Uflux t) x) (Sfield t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hirem : ∀ t ∈ Ioo a c, Integrable
      (fun x => inner0S (I := I) (g₁ t) x 4 (rem t x) (Sfield t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hinab : ∀ t ∈ Ioo a c, Integrable (fun x => inner0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (Sfield t) x) (Uflux t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidis : ∀ t ∈ Ioo a c, Integrable (fun x => normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (Sfield t) x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidens : ∀ t ∈ Icc a c, Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hdcont : ∀ t ∈ Icc a c, Continuous (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x))
    (hinit : g₁ a = g₂ a)
    (hcont : ContinuousOn (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Icc a c)) :
    ∀ t ∈ Icc a c, g₁ t = g₂ t := by
  have hzero := energy_zero_on (I := I) g₁ g₂ Adot Sdot Sfield Uflux rem hac hgram hdens
    hPDE₁ hPDE₂ hA hS hε hδ habs hcar hSdec hUb hrem hreact hRic hAdot hvol hirest hipair
    hilap hidiv hirem hinab hidis (fun t ht => hidens t (Ioo_subset_Icc_self ht)) hinit hcont
  exact fun t ht => metric_eq_of_energy_zero (I := I) g₁ g₂ (hdcont t ht) (hidens t ht)
    (hzero t ht)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem metrics_eq_ico (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b : ℝ}
    (h : ∀ c ∈ Ioo a b, ∀ t ∈ Icc a c, g₁ t = g₂ t) :
    ∀ t ∈ Ico a b, g₁ t = g₂ t := by
  intro t ht
  have htb : t < b := ht.2
  have hat : a ≤ t := ht.1
  refine h ((t + b) / 2) ⟨by linarith, by linarith⟩ t ⟨hat, by linarith⟩

end Capstone

end DifferentialGeometry.PDE.RicciFlow

end

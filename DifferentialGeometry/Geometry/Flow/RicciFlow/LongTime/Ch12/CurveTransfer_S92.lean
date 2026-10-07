import DifferentialGeometry.Geometry.Connection.OpenTarget
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong

set_option autoImplicit false

/-!
# CH12-S92 / G2a: germ-congruence of the geodesic equation / `covDerivAlong` and transfer to open subsets
-/

noncomputable section
open Bundle Manifold DifferentialGeometry Set Filter
open DifferentialGeometry.Geometry.Riemannian
open AlongCurve CovariantDerivativeAlong Geodesic
open scoped Bundle Manifold ContDiff Topology

namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hasGeodesicEquationAt_congr_S92 {g : SmoothRiemannianMetric I M} {γ γ' : ℝ → M} {t : ℝ}
    (h : γ' =ᶠ[𝓝 t] γ) (hg : HasGeodesicEquationAt (I := I) g γ t) :
    HasGeodesicEquationAt (I := I) g γ' t := by
  obtain ⟨v, a, h1, h2, h3, h4⟩ := hg
  have hγt : γ' t = γ t := h.self_of_nhds
  have hc : chartLocalCurve (I := I) γ' t =ᶠ[𝓝 t] chartLocalCurve (I := I) γ t :=
    h.mono fun s hs => by simp [chartLocalCurve, hs, hγt]
  have hcc : ∀ᶠ s in 𝓝 t, chartLocalCurve (I := I) γ' t =ᶠ[𝓝 s] chartLocalCurve (I := I) γ t :=
    eventually_eventually_nhds.mpr hc
  refine ⟨v, a, h1.congr_of_eventuallyEq hc, ?_, ?_, ?_⟩
  · filter_upwards [h2, hcc] with s hs hs'
    have := hs.congr_of_eventuallyEq hs'
    rwa [hs'.deriv_eq]
  · have hd : (fun s => deriv (chartLocalCurve (I := I) γ' t) s) =ᶠ[𝓝 t]
        (fun s => deriv (chartLocalCurve (I := I) γ t) s) :=
      hcc.mono fun s hs => hs.deriv_eq
    exact h3.congr_of_eventuallyEq hd
  · rw [hγt]; exact h4

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartRepAt_congr_S92 {γ γ' : ℝ → M} {V : ∀ s, TangentSpace I (γ s)}
    {V' : ∀ s, TangentSpace I (γ' s)} {t : ℝ}
    (hγ : γ' =ᶠ[𝓝 t] γ) (hV : ∀ᶠ s in 𝓝 t, (V' s : E) = (V s : E)) :
    chartRepAt (I := I) γ' V' t =ᶠ[𝓝 t] chartRepAt (I := I) γ V t := by
  have hγt : γ' t = γ t := hγ.self_of_nhds
  have gen : ∀ (a b : M) (e : a = b) (W : TangentSpace I a) (W' : TangentSpace I b),
      (W : E) = (W' : E) →
      (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt ℝ a W =
        (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt ℝ b W' := by
    intro a b e; subst e; intro W W' h; rw [show W = W' from h]
  filter_upwards [hγ, hV] with s hs hVs
  simp only [chartRepAt_apply]
  rw [hγt]
  exact gen _ _ hs _ _ hVs

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem covDerivAlong_congr_S92 {g : SmoothRiemannianMetric I M} {γ γ' : ℝ → M}
    {V : ∀ s, TangentSpace I (γ s)} {V' : ∀ s, TangentSpace I (γ' s)} {t : ℝ}
    (hγ : γ' =ᶠ[𝓝 t] γ) (hV : ∀ᶠ s in 𝓝 t, (V' s : E) = (V s : E)) :
    (covDerivAlong (I := I) g γ' V' t : E) = (covDerivAlong (I := I) g γ V t : E) := by
  have hγt : γ' t = γ t := hγ.self_of_nhds
  have hrep := chartRepAt_congr_S92 (I := I) hγ hV
  have hcurve : chartCurve (I := I) (γ t) γ' =ᶠ[𝓝 t] chartCurve (I := I) (γ t) γ :=
    hγ.mono fun s hs => by simp [chartCurve, hs]
  have key : ∀ (a b : M) (e : a = b) (X : E),
      (trivializationAt E (TangentSpace I) a).symmL ℝ a X =
        (trivializationAt E (TangentSpace I) b).symmL ℝ b X := by
    intro a b e X; subst e; rfl
  have hrep' : chartRepAt (I := I) γ' V' t =ᶠ[𝓝 t] chartRepAt (I := I) γ V t := hrep
  unfold covDerivAlong
  refine (key _ _ hγt _).trans ?_
  congr 1
  rw [hγt]
  simp only [chartCovDerivAlong_def]
  rw [hrep'.deriv_eq, hrep'.eq_of_nhds, hcurve.deriv_eq, hcurve.eq_of_nhds]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tangent_trivialization_open_S92
    (U : TopologicalSpace.Opens M) (a x : U)
    (hx : (x : M) ∈ (chartAt H (a : M)).source) :
    (trivializationAt E (TangentSpace I (M := U)) a).continuousLinearMapAt ℝ x =
      (trivializationAt E (TangentSpace I (M := M)) (a : M)).continuousLinearMapAt
        ℝ (x : M) := by
  have hxU : x ∈ (chartAt H a).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact hx
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hxU,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx,
    tangentCoordChange_opens x a x (mem_chart_source H (x : M))]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartRepAt_open_S92 (U : TopologicalSpace.Opens M) (γ : ℝ → U)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) (hγ : ContinuousAt γ t) :
    chartRepAt (I := I) γ V t =ᶠ[𝓝 t]
      chartRepAt (I := I) (Subtype.val ∘ γ) (fun s => V s) t := by
  have hn : ∀ᶠ s in 𝓝 t, (γ s : M) ∈ (chartAt H (γ t : M)).source :=
    (continuous_subtype_val.continuousAt.comp hγ).eventually
      ((chartAt H (γ t : M)).open_source.mem_nhds (mem_chart_source H (γ t : M)))
  filter_upwards [hn] with s hs
  exact congrArg (fun L => L (V s)) (tangent_trivialization_open_S92 U (γ t) (γ s) hs)

end GC.LongTime.Ch12

import DifferentialGeometry.Geometry.Metric.Approximation.ChartLimits.Overlap
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Atlas.FiniteLimits
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteLimitIdentities
import DifferentialGeometry.Geometry.Metric.Approximation.ChartLimits.Transition
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option autoImplicit false
noncomputable section
open Set Filter Topology Manifold Metric
open scoped ContDiff NNReal
open DifferentialGeometry.Geometry (pullbackMetricCoefficients)
open DifferentialGeometry.CheegerGromovCompactness (MapCPConvergenceOn
  tendstoUniformlyOn_of_cPConvergence)
namespace GC.MetricGeometry

private theorem contDiffOn_partialDiffeomorph_transition
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (a b : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) :
    ContDiffOn ℝ ∞ (fun u => b.symm (a u)) (a.trans b.symm).source :=
  (a.trans b.symm).contMDiffOn_toFun.contDiffOn

theorem openPartialHomeomorph_limit_laws_of_radial_chart
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace X]
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    (p : X) (o : ∀ i, Y i) {R ε : ℕ → ℝ}
    (F : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (Φ : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) ∞) (z : ∀ i, Y i) {r ρ : ℝ}
    (hΦs : ∀ i, (Φ i).source = ball 0 r) (hΦ0 : ∀ i, Φ i 0 = z i)
    (hrad : ∀ i, ∀ w ∈ ball (0 : E) r, dist (Φ i w) (z i) = ‖w‖)
    (himage : ∀ i, ∀ t ≤ r, (Φ i : E → Y i) '' ball 0 t = ball (z i) t)
    (ψ : OpenPartialHomeomorph E X) (hρr : ρ ≤ r) (hψs : ψ.source = ball 0 ρ)
    (hdom : ∀ᶠ i in atTop, ∀ u ∈ ball (0 : E) ρ, Φ i u ∈ closedBall (o i) (R i))
    (hlim : TendstoUniformlyOn (fun i u => (F i).extendToWholeSpace (Φ i u))
      ψ atTop (ball 0 ρ)) :
    (∀ᶠ i in atTop, ψ.source ⊆ (Φ i).toOpenPartialHomeomorph.source) ∧
    (∀ᶠ i in atTop, ∀ v, v ∈ (Φ i).toOpenPartialHomeomorph.source →
      dist ((Φ i).toOpenPartialHomeomorph v) ((Φ i).toOpenPartialHomeomorph 0) = ‖v‖) ∧
    (∀ᶠ i in atTop, ball ((Φ i).toOpenPartialHomeomorph 0) ρ ⊆
      (Φ i).toOpenPartialHomeomorph.target) ∧
    (∀ᶠ i in atTop, ∀ u ∈ ψ.source,
      (Φ i).toOpenPartialHomeomorph u ∈ closedBall (o i) (R i)) ∧
    TendstoUniformlyOn (fun i u => (F i).extendToWholeSpace ((Φ i).toOpenPartialHomeomorph u))
      ψ atTop ψ.source := by
  have hsub (i : ℕ) : ∀ x ∈ ball (0 : E) r, x ∈ (Φ i).source := by
    intro x hx
    rw [hΦs i]
    exact hx
  refine ⟨Eventually.of_forall fun i x hx => ?_, Eventually.of_forall fun i v hv => ?_,
    Eventually.of_forall fun i y hy => ?_, ?_, ?_⟩
  · rw [hψs] at hx
    exact hsub i x (ball_subset_ball hρr hx)
  · have hv' : v ∈ (Φ i).source := hv
    rw [hΦs i] at hv'
    have h1 := hrad i v hv'
    rw [← hΦ0 i] at h1
    exact h1
  · have hy' : y ∈ ball (z i) ρ := by
      have h : y ∈ ball (Φ i 0) ρ := hy
      rw [hΦ0 i] at h
      exact h
    rw [← himage i ρ hρr] at hy'
    obtain ⟨w, hw, rfl⟩ := hy'
    exact (Φ i).toOpenPartialHomeomorph.map_source (hsub i w (ball_subset_ball hρr hw))
  · rw [hψs]
    exact hdom
  · rw [hψs]
    exact hlim

theorem exists_countable_buffered_transition_cover
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace X] {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    (p : X) (o : ∀ i, Y i) {R ε : ℕ → ℝ}
    (F : ∀ i, PointedBallApprox (o i) p (R i) (ε i)) (hε : Tendsto ε atTop (𝓝 0))
    (Φa Φd : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) ∞)
    (ψa ψd : OpenPartialHomeomorph E X) (qd : X) {ρ : ℝ} (hρ : 0 < ρ)
    (hψs : ψd.source = ball 0 ρ) (hψt : ψd.target = ball qd ρ) (hψ0 : ψd 0 = qd)
    (has : ∀ᶠ i in atTop, ψa.source ⊆ (Φa i).toOpenPartialHomeomorph.source)
    (hbrad : ∀ᶠ i in atTop, ∀ v, v ∈ (Φd i).toOpenPartialHomeomorph.source →
      dist ((Φd i).toOpenPartialHomeomorph v) ((Φd i).toOpenPartialHomeomorph 0) = ‖v‖)
    (hbcover : ∀ᶠ i in atTop, ball ((Φd i).toOpenPartialHomeomorph 0) ρ ⊆
      (Φd i).toOpenPartialHomeomorph.target)
    (hdom : ∀ᶠ i in atTop,
      (∀ u ∈ ψa.source, (Φa i).toOpenPartialHomeomorph u ∈ closedBall (o i) (R i)) ∧
      (∀ v ∈ ψd.source, (Φd i).toOpenPartialHomeomorph v ∈ closedBall (o i) (R i)))
    (ha : TendstoUniformlyOn
      (fun i u => (F i).extendToWholeSpace ((Φa i).toOpenPartialHomeomorph u)) ψa atTop ψa.source)
    (hb : TendstoUniformlyOn
      (fun i v => (F i).extendToWholeSpace ((Φd i).toOpenPartialHomeomorph v)) ψd atTop ψd.source)
    {C : ℝ≥0} (hanti : AntilipschitzWith C (fun v : ψd.source => ψd v)) :
    ∃ S : Set (Set E), S.Countable ∧
      (∀ U ∈ S, IsOpen U ∧ U ⊆ (ψa.trans ψd.symm).source ∧
        ∃ s : ℝ, 0 < s ∧ s < ρ ∧ closedBall (0 : E) s ⊆ ψd.source ∧
          (∀ᶠ i in atTop, closure U ⊆ ((Φa i).trans (Φd i).symm).source ∧
            MapsTo (fun u => (Φd i).symm (Φa i u)) (closure U) (closedBall 0 s)) ∧
          TendstoUniformlyOn (fun i u => (Φd i).symm (Φa i u))
            (ψa.trans ψd.symm) atTop (closure U)) ∧
      ⋃₀ S = (ψa.trans ψd.symm).source := by
  apply exists_countable_open_cover_with_property
  intro x hx
  obtain ⟨U, s, hU, hxU, _, hUO, hs, hsρ, _, hst, hbuf, hconv⟩ :=
    exists_buffered_chart_transition_limit p o F hε
      (fun i => (Φa i).toOpenPartialHomeomorph) (fun i => (Φd i).toOpenPartialHomeomorph)
      ψa ψd qd hρ hψs hψt hψ0 has hbrad hbcover hdom ha hb hanti
      {x} isCompact_singleton (singleton_subset_iff.mpr hx)
  exact ⟨U, hU, hxU (mem_singleton x), subset_closure.trans hUO, s, hs, hsρ, hst, hbuf,
    hconv⟩

theorem exists_transition_buffer_of_subseq
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace X] {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    (p : X) (o : ∀ i, Y i) {R ε : ℕ → ℝ}
    (F : ∀ i, PointedBallApprox (o i) p (R i) (ε i)) (hε : Tendsto ε atTop (𝓝 0))
    (Φa Φd : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) ∞)
    (ψa ψd : OpenPartialHomeomorph E X) (qd : X) {ρ : ℝ} (hρ : 0 < ρ)
    (hψs : ψd.source = ball 0 ρ) (hψt : ψd.target = ball qd ρ) (hψ0 : ψd 0 = qd)
    (has : ∀ᶠ i in atTop, ψa.source ⊆ (Φa i).toOpenPartialHomeomorph.source)
    (hbrad : ∀ᶠ i in atTop, ∀ v, v ∈ (Φd i).toOpenPartialHomeomorph.source →
      dist ((Φd i).toOpenPartialHomeomorph v) ((Φd i).toOpenPartialHomeomorph 0) = ‖v‖)
    (hbcover : ∀ᶠ i in atTop, ball ((Φd i).toOpenPartialHomeomorph 0) ρ ⊆
      (Φd i).toOpenPartialHomeomorph.target)
    (hdom : ∀ᶠ i in atTop,
      (∀ u ∈ ψa.source, (Φa i).toOpenPartialHomeomorph u ∈ closedBall (o i) (R i)) ∧
      (∀ v ∈ ψd.source, (Φd i).toOpenPartialHomeomorph v ∈ closedBall (o i) (R i)))
    (ha : TendstoUniformlyOn
      (fun i u => (F i).extendToWholeSpace ((Φa i).toOpenPartialHomeomorph u)) ψa atTop ψa.source)
    (hb : TendstoUniformlyOn
      (fun i v => (F i).extendToWholeSpace ((Φd i).toOpenPartialHomeomorph v)) ψd atTop ψd.source)
    {C : ℝ≥0} (hanti : AntilipschitzWith C (fun v : ψd.source => ψd v))
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (Q : Set E) (hQ : IsCompact Q) (hQO : Q ⊆ (ψa.trans ψd.symm).source) :
    ∃ s : ℝ, 0 < s ∧ s < ρ ∧ ∀ᶠ i in atTop,
      Q ⊆ ((Φa (σ i)).trans (Φd (σ i)).symm).source ∧
      MapsTo (fun u => (Φd (σ i)).symm (Φa (σ i) u)) Q (closedBall 0 s) := by
  obtain ⟨s, hs, hsρ, hbuf, -⟩ := exists_chart_transition_limit_on_compact p o F hε
    (fun i => (Φa i).toOpenPartialHomeomorph) (fun i => (Φd i).toOpenPartialHomeomorph)
    ψa ψd qd hρ hψs hψt hψ0 has hbrad hbcover hdom ha hb hanti Q hQ hQO
  have hbuf' : ∀ᶠ i in atTop, Q ⊆ ((Φa i).trans (Φd i).symm).source ∧
      MapsTo (fun u => (Φd i).symm (Φa i u)) Q (closedBall 0 s) := hbuf
  exact ⟨s, hs, hsρ, hσ.tendsto_atTop.eventually hbuf'⟩

theorem eventually_transition_regular_of_buffered_limit
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace X] {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)]
    (K : ℕ) (g : ∀ i, DifferentialGeometry.SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    (Φa Φd : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) ∞)
    (ψa ψd : OpenPartialHomeomorph E X) {Vd : Set E} (hψV : ψd.source ⊆ Vd)
    {U : Set E} {ρ : ℝ}
    (hU : ∃ s : ℝ, 0 < s ∧ s < ρ ∧ closedBall (0 : E) s ⊆ ψd.source ∧
      (∀ᶠ i in atTop, closure U ⊆ ((Φa i).trans (Φd i).symm).source ∧
        MapsTo (fun u => (Φd i).symm (Φa i u)) (closure U) (closedBall 0 s)) ∧
      TendstoUniformlyOn (fun i u => (Φd i).symm (Φa i u))
        (ψa.trans ψd.symm) atTop (closure U)) :
    (∀ᶠ i in atTop, ContDiffOn ℝ (K + 1 : ℕ) (fun u => (Φd i).symm (Φa i u)) U) ∧
    (∃ Q : Set E, IsCompact Q ∧ Q ⊆ Vd ∧
      ∀ᶠ i in atTop, MapsTo (fun u => (Φd i).symm (Φa i u)) U Q) ∧
    (∀ᶠ i in atTop, ∀ u ∈ U,
      pullbackMetricCoefficients (g i) (Φa i) u =
        (pullbackMetricCoefficients (g i) (Φd i) ((Φd i).symm (Φa i u))).bilinearComp
          (fderiv ℝ (fun v => (Φd i).symm (Φa i v)) u)
          (fderiv ℝ (fun v => (Φd i).symm (Φa i v)) u)) ∧
    ∀ u ∈ U, Tendsto (fun i => (Φd i).symm (Φa i u)) atTop (𝓝 ((ψa.trans ψd.symm) u)) := by
  obtain ⟨s, _, _, hst, hbuf, hconv⟩ := hU
  refine ⟨?_, ⟨closedBall 0 s, isCompact_closedBall 0 s, hst.trans hψV, ?_⟩, ?_, ?_⟩
  · filter_upwards [hbuf] with i hi
    exact ((contDiffOn_partialDiffeomorph_transition (Φa i) (Φd i)).mono
      (subset_closure.trans hi.1)).of_le (by exact_mod_cast le_top)
  · filter_upwards [hbuf] with i hi
    exact fun x hx => hi.2 (subset_closure hx)
  · filter_upwards [hbuf] with i hi
    intro u hu
    exact pullbackMetricCoefficients_eq_bilinearComp_transition (g i) (Φa i) (Φd i)
      (hi.1 (subset_closure hu))
  · intro u hu
    exact hconv.tendsto_at (subset_closure hu)

private theorem limit_coefficient_symm_and_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Set E} {p : ℕ} {B : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {b : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hconv : ∀ D : Set E, IsCompact D → D ⊆ V → MapCPConvergenceOn D p B b)
    (hsymm : ∀ i u (v w : E), B i u v w = B i u w v)
    (hell : ∀ᶠ i in atTop, ∀ u ∈ V, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B i u v v ∧ B i u v v ≤ 2 * ‖v‖ ^ 2) :
    (∀ u ∈ V, ∀ v w : E, b u v w = b u w v) ∧
      (∀ u ∈ V, ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ b u v v ∧ b u v v ≤ 2 * ‖v‖ ^ 2) := by
  have hpt (u : E) (hu : u ∈ V) : Tendsto (fun i => B i u) atTop (𝓝 (b u)) :=
    (tendstoUniformlyOn_of_cPConvergence
      ((hconv {u} isCompact_singleton (singleton_subset_iff.mpr hu)).mono_order
        (Nat.zero_le _))).tendsto_at rfl
  refine ⟨fun u hu v w => ?_, fun u hu v => ?_⟩
  · have he (v' w' : E) : Continuous (fun C : E →L[ℝ] E →L[ℝ] ℝ => C v' w') := by
      fun_prop
    apply tendsto_nhds_unique (((he v w).tendsto _).comp (hpt u hu))
    have hs := ((he w v).tendsto _).comp (hpt u hu)
    exact hs.congr (fun i => hsymm i u w v)
  · have he : Continuous (fun C : E →L[ℝ] E →L[ℝ] ℝ => C v v) := by
      fun_prop
    have hlimv := (he.tendsto _).comp (hpt u hu)
    constructor
    · exact ge_of_tendsto hlimv (hell.mono fun i hi => (hi u hu v).1)
    · exact le_of_tendsto hlimv (hell.mono fun i hi => (hi u hu v).2)

theorem eventually_contDiffOn_pullbackMetricCoefficients
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)]
    (K : ℕ) (g : ∀ i, DifferentialGeometry.SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    (Φ : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) ∞) {r : ℝ}
    (hΦs : ∀ i, (Φ i).source = ball 0 r) {V : Set E} (hV : IsOpen V) (hVr : V ⊆ ball 0 r) :
    ∀ᶠ i in atTop, ContDiffOn ℝ K (pullbackMetricCoefficients (g i) (Φ i)) V := by
  refine Eventually.of_forall fun i => ?_
  have hsub : V ⊆ (Φ i).source := by
    rw [hΦs i]
    exact hVr
  exact (DifferentialGeometry.Geometry.contDiffOn_pullback_metric_coefficients (g i) hV
    ((Φ i).contMDiffOn_toFun.mono hsub)).of_le (by exact_mod_cast le_top)

theorem exists_coefficient_and_transition_limits_of_countable_pieces
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace X] [Countable ι] [Countable κ]
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)]
    (K : ℕ) (hK : 1 ≤ K)
    (g : ∀ i, DifferentialGeometry.SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    (Φ : ι → ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) ∞)
    (ψ : ι → OpenPartialHomeomorph E X)
    (src tgt : κ → ι) (V : ι → Set E) (W : κ → Set E)
    (hV : ∀ a, IsOpen (V a)) (hW : ∀ j, IsOpen (W j)) (hWV : ∀ j, W j ⊆ V (src j))
    (A : ι → ℝ)
    (hB : ∀ a, ∀ᶠ i in atTop, ContDiffOn ℝ K (pullbackMetricCoefficients (g i) (Φ a i)) (V a))
    (hell : ∀ a, ∀ᶠ i in atTop, ∀ u ∈ V a, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients (g i) (Φ a i) u v v ∧
        pullbackMetricCoefficients (g i) (Φ a i) u v v ≤ 2 * ‖v‖ ^ 2)
    (hjets : ∀ a, ∀ᶠ i in atTop, ∀ k : ℕ, k ≤ K → ∀ u ∈ V a,
      ‖iteratedFDeriv ℝ k (pullbackMetricCoefficients (g i) (Φ a i)) u‖ ≤ A a)
    (hΘ : ∀ j, ∀ᶠ i in atTop,
      ContDiffOn ℝ (K + 1 : ℕ) (fun u => (Φ (tgt j) i).symm (Φ (src j) i u)) (W j))
    (hbuffer : ∀ j, ∃ Q : Set E, IsCompact Q ∧ Q ⊆ V (tgt j) ∧
      ∀ᶠ i in atTop, MapsTo (fun u => (Φ (tgt j) i).symm (Φ (src j) i u)) (W j) Q)
    (hpull : ∀ j, ∀ᶠ i in atTop, ∀ u ∈ W j,
      pullbackMetricCoefficients (g i) (Φ (src j) i) u =
        (pullbackMetricCoefficients (g i) (Φ (tgt j) i)
          ((Φ (tgt j) i).symm (Φ (src j) i u))).bilinearComp
          (fderiv ℝ (fun v => (Φ (tgt j) i).symm (Φ (src j) i v)) u)
          (fderiv ℝ (fun v => (Φ (tgt j) i).symm (Φ (src j) i v)) u))
    (hT : ∀ j u, u ∈ W j → Tendsto (fun i => (Φ (tgt j) i).symm (Φ (src j) i u)) atTop
      (𝓝 (((ψ (src j)).trans (ψ (tgt j)).symm) u))) :
    ∃ (σ : ℕ → ℕ) (b : ι → E → E →L[ℝ] E →L[ℝ] ℝ), StrictMono σ ∧
      (∀ a, ContDiffOn ℝ (K - 1 : ℕ) (b a) (V a) ∧
        (∀ u ∈ V a, ∀ v w : E, b a u v w = b a u w v) ∧
        (∀ u ∈ V a, ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ b a u v v ∧ b a u v v ≤ 2 * ‖v‖ ^ 2) ∧
        ∀ D : Set E, IsCompact D → D ⊆ V a →
          MapCPConvergenceOn D (K - 1)
            (fun i => pullbackMetricCoefficients (g (σ i)) (Φ a (σ i))) (b a)) ∧
      (∀ j, ContDiffOn ℝ K ((ψ (src j)).trans (ψ (tgt j)).symm) (W j) ∧
        ∀ D : Set E, IsCompact D → D ⊆ W j →
          MapCPConvergenceOn D K (fun i u => (Φ (tgt j) (σ i)).symm (Φ (src j) (σ i) u))
            ((ψ (src j)).trans (ψ (tgt j)).symm)) := by
  have hsymm (a : ι) : ∀ᶠ i in atTop, ∀ u ∈ V a, ∀ v w : E,
      pullbackMetricCoefficients (g i) (Φ a i) u v w =
        pullbackMetricCoefficients (g i) (Φ a i) u w v :=
    Eventually.of_forall fun i u _ _ _ => (g i).symm (Φ a i u) _ _
  obtain ⟨σ, b, hσ, hb, ht⟩ :=
    DifferentialGeometry.CheegerGromovCompactness.exists_normalized_atlas_finite_subsequence
      K hK src tgt hV hW hWV (fun a i => pullbackMetricCoefficients (g i) (Φ a i))
      (fun j i u => (Φ (tgt j) i).symm (Φ (src j) i u))
      (fun j => ((ψ (src j)).trans (ψ (tgt j)).symm : E → E)) A
      hB hsymm hell hjets hΘ hbuffer hpull hT
  have hfin (a : ι) := limit_coefficient_symm_and_bounds (hb a).2
    (fun i u _ _ => (g (σ i)).symm (Φ a (σ i) u) _ _) (hσ.tendsto_atTop.eventually (hell a))
  exact ⟨σ, b, hσ, fun a => ⟨(hb a).1, (hfin a).1, (hfin a).2, (hb a).2⟩, ht⟩

private theorem bilinearComp_identity_of_eventual_pullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {B C : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {b c : E → E →L[ℝ] E →L[ℝ] ℝ}
    {Θ : ℕ → E → E} {T : E → E}
    (hB : ∀ D : Set E, IsCompact D → D ⊆ U → MapCPConvergenceOn D 0 B b)
    (hC : ∀ D : Set E, IsCompact D → D ⊆ V → MapCPConvergenceOn D 0 C c)
    (hΘ : ∀ D : Set E, IsCompact D → D ⊆ U → MapCPConvergenceOn D 1 Θ T)
    (hΘdiff : ∀ᶠ k in atTop, ContDiffOn ℝ 1 (Θ k) U) (hT : ContDiffOn ℝ 1 T U)
    (hc : ContinuousOn c V)
    (hpull : ∀ᶠ k in atTop, ∀ u ∈ U,
      B k u = (C k (Θ k u)).bilinearComp (fderiv ℝ (Θ k) u) (fderiv ℝ (Θ k) u))
    {u : E} (hu : u ∈ U) (hTu : T u ∈ V) :
    b u = (c (T u)).bilinearComp (fderiv ℝ T u) (fderiv ℝ T u) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hΘdiff.and hpull)
  have hshift : StrictMono (fun k : ℕ => k + N) := fun _ _ h => Nat.add_lt_add_right h N
  have hmetric : ∀ᶠ k in atTop, ∀ z ∈ U, Θ (k + N) z ∈ V → ∀ v w : E,
      B (k + N) z v w =
        C (k + N) (Θ (k + N) z) (fderiv ℝ (Θ (k + N)) z v) (fderiv ℝ (Θ (k + N)) z w) :=
    Eventually.of_forall fun k z hz _ v w =>
      (congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L v w)
        ((hN (k + N) (Nat.le_add_left N k)).2 z hz)).trans
        (ContinuousLinearMap.bilinearComp_apply (C (k + N) (Θ (k + N) z))
          (fderiv ℝ (Θ (k + N)) z) (fderiv ℝ (Θ (k + N)) z) v w)
  have hident :=
    DifferentialGeometry.CheegerGromovCompactness.bilinear_pullback_identity_of_mapCP_convergence
      (U := U) (V := V) (B := fun k => B (k + N)) (Binf := b)
      (C := fun k => C (k + N)) (Cinf := c) (Φ := fun k => Θ (k + N)) (Φinf := T) hU hV
      (fun D hD hDU => (hB D hD hDU).comp_subseq hshift)
      (fun D hD hDV => (hC D hD hDV).comp_subseq hshift)
      (fun D hD hDU => (hΘ D hD hDU).comp_subseq hshift)
      (fun k => (hN (k + N) (Nat.le_add_left N k)).1) hT hc hmetric hu hTu
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact (hident v w).trans (ContinuousLinearMap.bilinearComp_apply (c (T u))
    (fderiv ℝ T u) (fderiv ℝ T u) v w).symm

theorem bilinearComp_identity_of_isOpen_sUnion_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set E} {S : Set (Set E)} (hSo : ∀ U ∈ S, IsOpen U) (hS : ⋃₀ S = O)
    {V : Set E} (hV : IsOpen V)
    {B C : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {b c : E → E →L[ℝ] E →L[ℝ] ℝ}
    {Θ : ℕ → E → E} {T : E → E}
    (hB : ∀ D : Set E, IsCompact D → D ⊆ O → MapCPConvergenceOn D 0 B b)
    (hC : ∀ D : Set E, IsCompact D → D ⊆ V → MapCPConvergenceOn D 0 C c)
    (hΘ : ∀ U ∈ S, ∀ D : Set E, IsCompact D → D ⊆ U → MapCPConvergenceOn D 1 Θ T)
    (hΘdiff : ∀ U ∈ S, ∀ᶠ k in atTop, ContDiffOn ℝ 1 (Θ k) U)
    (hT : ∀ U ∈ S, ContDiffOn ℝ 1 T U) (hc : ContinuousOn c V)
    (hpull : ∀ U ∈ S, ∀ᶠ k in atTop, ∀ u ∈ U,
      B k u = (C k (Θ k u)).bilinearComp (fderiv ℝ (Θ k) u) (fderiv ℝ (Θ k) u))
    {u : E} (hu : u ∈ O) (hTu : T u ∈ V) :
    b u = (c (T u)).bilinearComp (fderiv ℝ T u) (fderiv ℝ T u) := by
  rw [← hS] at hu
  obtain ⟨U, hUS, huU⟩ := hu
  have hUO : U ⊆ O := by
    rw [← hS]
    exact subset_sUnion_of_mem hUS
  exact bilinearComp_identity_of_eventual_pullback (hSo U hUS) hV
    (fun D hD hDU => hB D hD (hDU.trans hUO)) hC (hΘ U hUS) (hΘdiff U hUS) (hT U hUS) hc
    (hpull U hUS) huU hTu

theorem contDiffOn_of_isOpen_sUnion_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} {f : E → E} {O : Set E} {S : Set (Set E)} (hSo : ∀ U ∈ S, IsOpen U)
    (hS : ⋃₀ S = O) (h : ∀ U ∈ S, ContDiffOn ℝ n f U) : ContDiffOn ℝ n f O := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  rw [← hS] at hx
  obtain ⟨U, hUS, hxU⟩ := hx
  exact ⟨U, hSo U hUS, hxU, (h U hUS).mono inter_subset_right⟩

theorem mapCPConvergenceOn_of_isOpen_sUnion_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {O : Set E} {S : Set (Set E)} (hSo : ∀ U ∈ S, IsOpen U) (hS : ⋃₀ S = O)
    {p : ℕ} {Φ : ℕ → E → F} {Φinf : E → F}
    (hloc : ∀ U ∈ S, ∀ D : Set E, IsCompact D → D ⊆ U → MapCPConvergenceOn D p Φ Φinf)
    {Q : Set E} (hQ : IsCompact Q) (hQO : Q ⊆ O) :
    MapCPConvergenceOn Q p Φ Φinf := by
  have hQS : Q ⊆ ⋃₀ S := by
    rw [hS]
    exact hQO
  exact mapCPConvergenceOn_of_isCompact_subset_sUnion hSo hloc hQ hQS

end GC.MetricGeometry

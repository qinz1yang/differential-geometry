import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PreparedCapWindowGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceForwardScalar

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u uE uH uM

theorem exists_uniform_recent_prepared_cap_product_exclusion_of_scalar_upper_bound
    (D r eps a₀ B : ℝ) (C : ℝ≥0) (ha₀ : 0 < a₀) (hB : 0 < B)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ θ ε₀ δ₀ : ℝ, 0 < θ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ c : ℝ, 0 < c → ∃ Qmin R εprod : ℝ,
        0 < Qmin ∧ 0 < R ∧ 0 < εprod ∧ εprod ≤ 1 / 4 ∧
      ∀ {E : Type uE} {H : Type uH} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {Dbig : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ)
        (hmargin : D + 1 ≤ Dbig),
      ⌈eps⁻¹⌉₊ + 2 ≤ m → ζ ≤ ε₀ →
      let inc : standardCapWindow D → standardCapWindow Dbig := TopologicalSpace.Opens.inclusion
        (show standardCapWindow D ≤ standardCapWindow Dbig from by
          intro x hx
          change ‖x‖ < Dbig + 1
          change ‖x‖ < D + 1 at hx
          linarith only [hx, hmargin]);
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (Jbig : standardCapWindow Dbig → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig →
      let J := Jbig ∘ inc;
      ∀ (q q₀ : ℝ), 0 < q → 0 < q₀ →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
          (mfderiv ThreeModel ThreeModel Jbig x z)) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      (∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s,
        q₀ < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
      ∀ (z : standardCapWindow D) (x : G.terminalRegularOpen)
        (A : BackwardPointTrace H first last hle x.val), ‖z.val‖ < r →
        A.point first le_rfl hle = J z →
      ∀ (Q : ℝ) (hQ : 0 < Q), c * Q ≤ metricScalarAt L.metric x →
      metricScalarAt L.metric x ≤ B * Q →
      2 * q₀ < metricScalarAt L.metric x → Qmin ≤ Q → q ≤ 4 * B * Q →
      Q * (s - H.time first) ≤ θ →
      ∀ {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        [TopologicalSpace H'] {Jp : ModelWithCorners ℝ F H'} [Jp.Boundaryless]
        {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold Jp ∞ N]
        [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]
        (hprod : SmoothRiemannianMetric Jp N), Module.finrank ℝ F = 2 →
      ∀ (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens G.terminalRegularOpen)
        (Φ : O ≃ₘ⟮Jp.prod 𝓘(ℝ), ThreeModel⟯ V),
      riemannianBallOf (scaleMetric Q hQ L.metric) x R ⊆ V →
      (∀ y : V, ∀ n : ℕ, n ≤ 2 →
        metricDerivNorm n (Diffeomorph.pullbackMetricCross ((scaleMetric Q hQ L.metric).restrictOpen V) Φ)
          ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O)
          ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm y) ≤ εprod) → False := by
  obtain ⟨C₀, hC₀, hscalar, η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, hexclude⟩ :=
    exists_uniform_prepared_incoming_cap_product_exclusion.{u,uE,uH,uM}
      D r eps C heps hepssmall hr hfit
  let θ := min (η / (4 * B)) ((C : ℝ) * B + 1)⁻¹
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  refine ⟨θ,ε₀,δ₀,hθ,hε₀,hεhalf,hδ₀,?_⟩
  intro c hc
  let Qmin := 2 * C₀ / (c * a₀)
  let R := 4 * Real.sqrt (2 * C₀ / c) * r
  let εprod := min (1 / 8) (((7 / 8 : ℝ) / (2 * C₀ / c)) / 23040)
  have hr0 : 0 < r := by linarith only [hr, StandardCap.transitionEnd_pos, inv_pos.mpr heps]
  have hQmin : 0 < Qmin := by dsimp [Qmin]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hεprod : 0 < εprod := lt_min (by norm_num) (by positivity)
  have hεquarter : εprod ≤ 1 / 4 := (min_le_left _ _).trans (by norm_num)
  have hεsmall : 720 * εprod < ((7 / 8 : ℝ) / (2 * C₀ / c)) / 16 := by
    have hsmall : εprod ≤ ((7 / 8 : ℝ) / (2 * C₀ / c)) / 23040 := min_le_right _ _
    have hb : 0 < (7 / 8 : ℝ) / (2 * C₀ / c) := by positivity
    linarith only [hsmall, hb]
  refine ⟨Qmin,R,εprod,hQmin,hR,hεprod,hεquarter,?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hmargin hm hζ
    inc H first last hle s G L hinit Jbig hJbig J q q₀ hq hq₀ hzero parameters records
    hfixed hlower hδ hderiv hfinal z x Atrace hz hanchor Q hQ hscalarLower hscalarUpper hthreshold hQlower
    hqQ hage F H' _ _ _ _ Jp _ N _ _ _ _ _ _ hprod hdim O V Φ hcapture hproduct
  have hbirthscalar :
      metricScalarAt (H.initialMetric first) (Atrace.point first le_rfl hle) ≤ C₀ * q := by
    rw [hanchor]
    exact (le_abs_self _).trans (hscalar (E := E) (H := H0) (M := M)
      (N := (H.stage first).Carrier) (I := I) (g := g) (x₀ := x₀) (δ := δ) (k := k)
      (d := d) (A := A) (hA := hA) (D := Dbig) (m := m) (ε := ζ)
      w (hζ.trans hεhalf) (by omega) (H.initialMetric first) Jbig hJbig q hq hzero
      (inc z) (z.property.trans_le hmargin))
  have hCθ : (C : ℝ) * B * θ ≤ 1 := by
    have hh : θ ≤ ((C : ℝ) * B + 1)⁻¹ := min_le_right _ _
    have hb := (le_div_iff₀ (by positivity : 0 < (C : ℝ) * B + 1)).mp
      (show θ ≤ 1 / ((C : ℝ) * B + 1) by simpa only [one_div] using hh)
    nlinarith only [hb, hθ.le]
  have hdt0 : 0 ≤ s - H.time first :=
    sub_nonneg.mpr ((H.time_strictMono.monotone hle).trans G.lt.le)
  have htime : C * (s - H.time first) * metricScalarAt L.metric x ≤ 1 := by
    have h₁ := mul_le_mul_of_nonneg_left hscalarUpper
      (mul_nonneg C.coe_nonneg hdt0)
    have h₂ := mul_le_mul_of_nonneg_left hage (mul_nonneg C.coe_nonneg hB.le)
    nlinarith only [h₁,h₂,hCθ]
  obtain ⟨hlowerScale, hthresholdScale⟩ := Atrace.terminal_scalar_div_le_birth_scale_of_time_sub_le
    G L hinit x hq₀
    (fun j hf hl => hderiv j hf hl (Atrace.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)))
    (hfinal x.val) hC₀ hbirthscalar hthreshold htime
  have hscaledBirth : c * Q ≤ 2 * C₀ * q := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * C₀)).mp hlowerScale
    nlinarith only [hscalarLower,hh]
  have hratio : Q / q ≤ 2 * C₀ / c := by
    apply (div_le_div_iff₀ hq hc).mpr
    nlinarith only [hscaledBirth]
  have haq : 1 ≤ a₀ * q := by
    have hh := (div_le_iff₀ (mul_pos hc ha₀)).mp hQlower
    have ht := mul_le_mul_of_nonneg_left hscaledBirth ha₀.le
    nlinarith only [hh,ht,hC₀]
  have hdt : 0 ≤ s - H.time first :=
    sub_nonneg.mpr ((H.time_strictMono.monotone hle).trans G.lt.le)
  have htimecap : q * (s - H.time first) ≤ η := by
    calc
      q * (s - H.time first) ≤ (4 * B * Q) * (s - H.time first) :=
        mul_le_mul_of_nonneg_right hqQ hdt
      _ = (4 * B) * (Q * (s - H.time first)) := by ring
      _ ≤ (4 * B) * θ := mul_le_mul_of_nonneg_left hage (by positivity)
      _ ≤ η := by
        have hh := (le_div_iff₀ (by positivity : 0 < 4 * B)).mp
          (show θ ≤ η / (4 * B) from min_le_left _ _)
        nlinarith only [hh]
  exact hexclude (E := E) (H := H0) (M := M) (I := I) (g := g) (x₀ := x₀)
    (δ := δ) (k := k) (d := d) (A := A) (hA := hA) (Dbig := Dbig) (m := m) (ζ := ζ)
    w hmargin hm hζ H first last hle s G L hinit Jbig hJbig q q₀ a₀ hq hq₀
    hthresholdScale.le haq hzero parameters records hfixed hlower hδ hderiv hfinal htimecap
    z x Atrace hz hanchor Q (2 * C₀ / c) hQ hratio hprod hdim O V Φ hcapture
    εprod hεquarter hεsmall hproduct


theorem exists_uniform_recent_prepared_cap_product_exclusion_of_scalar_bounds
    (D r eps a₀ c B : ℝ) (C : ℝ≥0) (ha₀ : 0 < a₀) (hc : 0 < c) (hB : 0 < B)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ θ Qmin R εprod ε₀ δ₀ : ℝ,
      0 < θ ∧ 0 < Qmin ∧ 0 < R ∧ 0 < εprod ∧ εprod ≤ 1 / 4 ∧
      0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {E : Type uE} {H : Type uH} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {Dbig : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ)
        (hmargin : D + 1 ≤ Dbig),
      ⌈eps⁻¹⌉₊ + 2 ≤ m → ζ ≤ ε₀ →
      let inc : standardCapWindow D → standardCapWindow Dbig := TopologicalSpace.Opens.inclusion
        (show standardCapWindow D ≤ standardCapWindow Dbig from by
          intro x hx
          change ‖x‖ < Dbig + 1
          change ‖x‖ < D + 1 at hx
          linarith only [hx, hmargin]);
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (Jbig : standardCapWindow Dbig → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig →
      let J := Jbig ∘ inc;
      ∀ (q q₀ : ℝ), 0 < q → 0 < q₀ →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
          (mfderiv ThreeModel ThreeModel Jbig x z)) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      (∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s,
        q₀ < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
      ∀ (z : standardCapWindow D) (x : G.terminalRegularOpen)
        (A : BackwardPointTrace H first last hle x.val), ‖z.val‖ < r →
        A.point first le_rfl hle = J z →
      ∀ (Q : ℝ) (hQ : 0 < Q), c * Q ≤ metricScalarAt L.metric x →
      metricScalarAt L.metric x ≤ B * Q →
      2 * q₀ < metricScalarAt L.metric x → Qmin ≤ Q → q ≤ 4 * B * Q →
      Q * (s - H.time first) ≤ θ →
      ∀ {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        [TopologicalSpace H'] {Jp : ModelWithCorners ℝ F H'} [Jp.Boundaryless]
        {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold Jp ∞ N]
        [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]
        (hprod : SmoothRiemannianMetric Jp N), Module.finrank ℝ F = 2 →
      ∀ (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens G.terminalRegularOpen)
        (Φ : O ≃ₘ⟮Jp.prod 𝓘(ℝ), ThreeModel⟯ V),
      riemannianBallOf (scaleMetric Q hQ L.metric) x R ⊆ V →
      (∀ y : V, ∀ n : ℕ, n ≤ 2 →
        metricDerivNorm n (Diffeomorph.pullbackMetricCross ((scaleMetric Q hQ L.metric).restrictOpen V) Φ)
          ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O)
          ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm y) ≤ εprod) → False := by
  obtain ⟨θ,ε₀,δ₀,hθ,hε₀,hεhalf,hδ₀,hall⟩ :=
    exists_uniform_recent_prepared_cap_product_exclusion_of_scalar_upper_bound.{u,uE,uH,uM}
      D r eps a₀ B C ha₀ hB heps hepssmall hr hfit
  obtain ⟨Qmin,R,εprod,hQmin,hR,hεprod,hεquarter,hcase⟩ := hall c hc
  exact ⟨θ,Qmin,R,εprod,ε₀,δ₀,hθ,hQmin,hR,hεprod,hεquarter,hε₀,hεhalf,hδ₀,hcase⟩


theorem exists_uniform_recent_prepared_cap_product_exclusion
    (D r eps a₀ : ℝ) (C : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ θ Qmin R εprod ε₀ δ₀ : ℝ,
      0 < θ ∧ 0 < Qmin ∧ 0 < R ∧ 0 < εprod ∧ εprod ≤ 1 / 4 ∧
      0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {E : Type uE} {H : Type uH} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {Dbig : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ)
        (hmargin : D + 1 ≤ Dbig),
      ⌈eps⁻¹⌉₊ + 2 ≤ m → ζ ≤ ε₀ →
      let inc : standardCapWindow D → standardCapWindow Dbig := TopologicalSpace.Opens.inclusion
        (show standardCapWindow D ≤ standardCapWindow Dbig from by
          intro x hx
          change ‖x‖ < Dbig + 1
          change ‖x‖ < D + 1 at hx
          linarith only [hx, hmargin]);
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (Jbig : standardCapWindow Dbig → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig →
      let J := Jbig ∘ inc;
      ∀ (q q₀ : ℝ), 0 < q → 0 < q₀ →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
          (mfderiv ThreeModel ThreeModel Jbig x z)) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      (∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s,
        q₀ < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
      ∀ (z : standardCapWindow D) (x : G.terminalRegularOpen)
        (A : BackwardPointTrace H first last hle x.val), ‖z.val‖ < r →
        A.point first le_rfl hle = J z →
      ∀ (Q : ℝ) (hQ : 0 < Q), Q = metricScalarAt L.metric x →
      2 * q₀ < Q → Qmin ≤ Q → q ≤ 4 * Q → Q * (s - H.time first) ≤ θ →
      ∀ {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        [TopologicalSpace H'] {Jp : ModelWithCorners ℝ F H'} [Jp.Boundaryless]
        {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold Jp ∞ N]
        [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]
        (hprod : SmoothRiemannianMetric Jp N), Module.finrank ℝ F = 2 →
      ∀ (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens G.terminalRegularOpen)
        (Φ : O ≃ₘ⟮Jp.prod 𝓘(ℝ), ThreeModel⟯ V),
      riemannianBallOf (scaleMetric Q hQ L.metric) x R ⊆ V →
      (∀ y : V, ∀ n : ℕ, n ≤ 2 →
        metricDerivNorm n (Diffeomorph.pullbackMetricCross ((scaleMetric Q hQ L.metric).restrictOpen V) Φ)
          ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O)
          ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm y) ≤ εprod) → False := by
  obtain ⟨θ,Qmin,R,εprod,ε₀,δ₀,hθ,hQmin,hR,hεprod,hεquarter,hε₀,hεhalf,hδ₀,hexclude⟩ :=
    exists_uniform_recent_prepared_cap_product_exclusion_of_scalar_bounds.{u,uE,uH,uM}
      D r eps a₀ 1 1 C ha₀ (by norm_num) (by norm_num) heps hepssmall hr hfit
  refine ⟨θ,Qmin,R,εprod,ε₀,δ₀,hθ,hQmin,hR,hεprod,hεquarter,hε₀,hεhalf,hδ₀,?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hmargin hm hζ
    inc H first last hle s G L hinit Jbig hJbig J q q₀ hq hq₀ hzero parameters records
    hfixed hlower hδ hderiv hfinal z x Atrace hz hanchor Q hQ hQeq hthreshold hQlower
    hqQ hage F H' _ _ _ _ Jp _ N _ _ _ _ _ _ hprod hdim O V Φ hcapture hproduct
  exact hexclude w hmargin hm hζ H first last hle s G L hinit Jbig hJbig q q₀ hq hq₀
    hzero parameters records hfixed hlower hδ hderiv hfinal z x Atrace hz hanchor Q hQ
    (by simpa only [one_mul] using hQeq.le) (by simpa only [one_mul] using hQeq.ge)
    (by simpa only [hQeq] using hthreshold) hQlower (by simpa only [mul_one] using hqQ)
    hage hprod hdim O V Φ hcapture hproduct

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

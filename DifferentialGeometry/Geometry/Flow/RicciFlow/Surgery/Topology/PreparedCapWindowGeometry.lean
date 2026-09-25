import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWindowRestriction
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u uE uH uM
private theorem window_inclusion_isSmoothEmbedding {D D' : ℝ} (hDD : D ≤ D') :
    IsSmoothEmbedding ThreeModel ThreeModel ∞
      (TopologicalSpace.Opens.inclusion
        (show standardCapWindow D ≤ standardCapWindow D' from
          by
          intro x hx
          change ‖x‖ < D' + 1
          change ‖x‖ < D + 1 at hx
          linarith only [hx, hDD])) := by
  let inc := TopologicalSpace.Opens.inclusion
    (show standardCapWindow D ≤ standardCapWindow D' from
      by
          intro x hx
          change ‖x‖ < D' + 1
          change ‖x‖ < D + 1 at hx
          linarith only [hx, hDD])
  have hc : ContMDiff ThreeModel ThreeModel ∞ inc := contMDiff_inclusion _
  have hl := DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
    inc hc (fun x => by rw [mfderiv_opens_incl]; exact fun v w h => h) rfl
  apply Perelman.KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective hl
  intro x y h
  exact Subtype.ext (congrArg (fun z : standardCapWindow D' => z.val) h)

private theorem prepared_window_restriction_bounds
    {D Dbig : ℝ} (hD : 0 < D) (hmargin : D + 1 ≤ Dbig)
    {E : Type uE} {H : Type uH} {M : Type uM} {N : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
    {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
    (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ) (hζ : ζ ≤ 1 / 2)
    (h : SmoothRiemannianMetric ThreeModel N)
    (Jbig : standardCapWindow Dbig → N) (hJbig : IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig)
    {q C₀ : ℝ}
    (hzero : ∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
      q * h.inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
        (mfderiv ThreeModel ThreeModel Jbig x z))
    (hscalarbig : ∀ x : standardCapWindow Dbig, ‖x.val‖ < Dbig → metricScalarAt h (Jbig x) ≤ C₀*q) :
    let hDD : D ≤ Dbig := by linarith only [hmargin];
    let inc := TopologicalSpace.Opens.inclusion
      (show standardCapWindow D ≤ standardCapWindow Dbig from by
        intro x hx
        change ‖x‖ < Dbig+1
        change ‖x‖ < D+1 at hx
        linarith only [hx,hmargin]);
    let ws := w.restrictWindow hD hDD;
    let J := Jbig ∘ inc;
    IsSmoothEmbedding ThreeModel ThreeModel ∞ J ∧
    (∀ x : standardCapWindow D, ∀ v : TangentSpace ThreeModel x,
      ws.windowMetric.inner x v v ≤ (3/2:ℝ)*StandardCap.metric.inner x.val v v) ∧
    (∀ x (v z : TangentSpace ThreeModel x), ws.windowMetric.inner x v z =
      q*h.inner (J x) (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x z)) ∧
    ∀ x : standardCapWindow D, metricScalarAt h (J x) ≤ C₀*q := by
  intro hDD inc ws J
  have hJ := hJbig.comp (window_inclusion_isSmoothEmbedding hDD) (by simp)
  have hpoint (x : standardCapWindow D) : ‖(inc x).val‖ < Dbig := x.property.trans_le hmargin
  refine ⟨hJ,?_,?_,fun x => hscalarbig (inc x) (hpoint x)⟩
  · intro x v
    rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
    change w.windowMetric.inner (inc x) v v ≤ _
    have hb := (w.window_inner_bounds hζ (hpoint x) v).2
    rw [standardCapMetric_eq_metric] at hb
    change w.windowMetric.inner (inc x) v v ≤ (3/2:ℝ)*StandardCap.metric.inner x.val v v at hb
    exact hb
  · intro x v z
    rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
    change w.windowMetric.inner (inc x) v z = _
    have hz := hzero (inc x) (show TangentSpace ThreeModel (inc x) from v)
      (show TangentSpace ThreeModel (inc x) from z)
    let hs : standardCapWindow D ≤ standardCapWindow Dbig := by
      intro y hy
      change ‖y‖ < Dbig + 1
      change ‖y‖ < D + 1 at hy
      linarith only [hy,hmargin]
    have hd := mfderiv_comp x (hJbig.contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_inclusion (I := ThreeModel) (n := ∞) hs).mdifferentiableAt (by simp))
    simp only [mfderiv_opens_incl] at hd
    dsimp only [TangentSpace] at hd hz ⊢
    rw [hd]
    exact hz

private theorem prepared_incoming_cap_geometry_of_scalar_bound
    (D r eps : ℝ) (C : ℝ≥0)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D)
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hscalar_bound :
      ∀ {E : Type uE} {H : Type uH} {M : Type uM} {N : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
        [T2Space N]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ε : ℝ} (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ε),
        ε ≤ 1 / 2 → 2 ≤ m →
        ∀ (h : SmoothRiemannianMetric ThreeModel N) (J : standardCapWindow D → N),
        IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
        ∀ q : ℝ, 0 < q →
        (∀ x v z, w.windowMetric.inner x v z =
          q * h.inner (J x) (mfderiv ThreeModel ThreeModel J x v)
            (mfderiv ThreeModel ThreeModel J x z)) →
        ∀ x : standardCapWindow D, ‖x.val‖ < D →
          |metricScalarAt h (J x)| ≤ C₀ * q) :
    ∃ η ε₀ δ₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
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
      ∀ (q q₀ a₀ : ℝ) (hq : 0 < q), 0 < q₀ → q₀ ≤ C₀ * q → 1 ≤ a₀ * q →
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
      q * (s - H.time first) ≤ η →
      ∀ (z : standardCapWindow D) (x : G.terminalRegularOpen)
        (A : BackwardPointTrace H first last hle x.val), ‖z.val‖ < r →
        A.point first le_rfl hle = J z →
      ∃ (Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G),
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
        (∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ y).val = J y) ∧
        ∃ (p tip : standardCapWindow D), p.val = r • (spherePoint : ThreeSpace) ∧ tip.val = 0 ∧
          ∃ (nk : SpatialNeck (scaleMetric q hq L.metric) eps
              (H.backwardSurvivorIncomingMap first last hle G (Ξ p)))
            (K : CompactDomain G.terminalRegularOpen),
            x ∈ interior K.carrier ∧ Nonempty (CapCore K.carrier) ∧
            K.carrier = (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) ''
              {y : standardCapWindow D | ‖y.val‖ ≤ r} ∧
            frontier K.carrier = range (fun y : Sphere 2 => nk.map (y, 0)) ∧
            |metricScalarAt (scaleMetric q hq L.metric)
              (H.backwardSurvivorIncomingMap first last hle G (Ξ p)) - 1| < 1/8 ∧
            K.carrier ⊆ riemannianBallOf (scaleMetric q hq L.metric)
              (H.backwardSurvivorIncomingMap first last hle G (Ξ tip)) (2*r) := by
  obtain ⟨η,ε₀,δ₀,hη,hε₀,hεhalf,hδ₀,hgeometry⟩ :=
    exists_uniform_incoming_cap_geometry D r eps C₀ C hC₀ heps hepssmall hr hfit
  refine ⟨η,ε₀,δ₀,hη,hε₀,hεhalf,hδ₀,?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hmargin hm hζ
    inc H first last hle s G L hinit Jbig hJbig J q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hδ hderiv hfinal htime z x Atrace hz hanchor
  have hD : 0 < D := by
    have hi := inv_pos.mpr heps
    have ht := StandardCap.transitionEnd_pos
    linarith
  have hDD : D ≤ Dbig := by linarith only [hmargin]
  obtain ⟨wsmall,hwsmall⟩ : ∃ ws : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ,
      ws = w.restrictWindow hD hDD := ⟨_,rfl⟩
  obtain ⟨hJ,hupperRaw,hmetricRaw,hscalar⟩ := prepared_window_restriction_bounds
    (E := E) (H := H0) (M := M) (N := (H.stage first).Carrier) (I := I)
    (g := g) (x₀ := x₀) (δ := δ) (k := k) (d := d) (A := A) (hA := hA) (m := m) (ζ := ζ)
    hD hmargin w
    (hζ.trans hεhalf) (H.initialMetric first) Jbig hJbig hzero
    (fun x hx => (le_abs_self _).trans (hscalar_bound (E := E) (H := H0) (M := M) (N := (H.stage first).Carrier) (I := I)
      (g := g) (x₀ := x₀) (δ := δ) (k := k) (d := d) (A := A) (hA := hA) (D := Dbig)
      (m := m) (ε := ζ) w (hζ.trans hεhalf) (by omega)
      (H.initialMetric first) Jbig hJbig q hq hzero x hx))
  have hupper : ∀ x : standardCapWindow D, ∀ v : TangentSpace ThreeModel x,
      wsmall.windowMetric.inner x v v ≤ (3/2:ℝ)*StandardCap.metric.inner x.val v v := by
    rw [hwsmall]
    exact hupperRaw
  have hmetric : ∀ x (v t : TangentSpace ThreeModel x), wsmall.windowMetric.inner x v t =
      q*(H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x t) := by
    rw [hwsmall]
    exact hmetricRaw
  exact hgeometry (E := E) (H := H0) (M := M) (I := I)
    (g := g) (x₀ := x₀) (δ := δ) (k := k) (d := d) (A := A) (hA := hA)
    (m := m) (ζ := ζ) wsmall hm hζ hupper H first last hle s G L hinit J hJ
    q q₀ a₀ hq hq₀ hq₀Q haq hmetric hscalar parameters records hfixed hlower hδ hderiv hfinal
    htime z x Atrace hz hanchor


theorem exists_uniform_prepared_incoming_cap_geometry
    (D r eps : ℝ) (C : ℝ≥0)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ (
      ∀ {E : Type uE} {H : Type uH} {M : Type uM} {N : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
        [T2Space N]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ε : ℝ} (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ε),
        ε ≤ 1 / 2 → 2 ≤ m →
        ∀ (h : SmoothRiemannianMetric ThreeModel N) (J : standardCapWindow D → N),
        IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
        ∀ q : ℝ, 0 < q →
        (∀ x v z, w.windowMetric.inner x v z =
          q * h.inner (J x) (mfderiv ThreeModel ThreeModel J x v)
            (mfderiv ThreeModel ThreeModel J x z)) →
        ∀ x : standardCapWindow D, ‖x.val‖ < D →
          |metricScalarAt h (J x)| ≤ C₀ * q) ∧
    ∃ η ε₀ δ₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
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
      ∀ (q q₀ a₀ : ℝ) (hq : 0 < q), 0 < q₀ → q₀ ≤ C₀ * q → 1 ≤ a₀ * q →
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
      q * (s - H.time first) ≤ η →
      ∀ (z : standardCapWindow D) (x : G.terminalRegularOpen)
        (A : BackwardPointTrace H first last hle x.val), ‖z.val‖ < r →
        A.point first le_rfl hle = J z →
      ∃ (Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G),
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
        (∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ y).val = J y) ∧
        ∃ (p tip : standardCapWindow D), p.val = r • (spherePoint : ThreeSpace) ∧ tip.val = 0 ∧
          ∃ (nk : SpatialNeck (scaleMetric q hq L.metric) eps
              (H.backwardSurvivorIncomingMap first last hle G (Ξ p)))
            (K : CompactDomain G.terminalRegularOpen),
            x ∈ interior K.carrier ∧ Nonempty (CapCore K.carrier) ∧
            K.carrier = (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) ''
              {y : standardCapWindow D | ‖y.val‖ ≤ r} ∧
            frontier K.carrier = range (fun y : Sphere 2 => nk.map (y, 0)) ∧
            |metricScalarAt (scaleMetric q hq L.metric)
              (H.backwardSurvivorIncomingMap first last hle G (Ξ p)) - 1| < 1/8 ∧
            K.carrier ⊆ riemannianBallOf (scaleMetric q hq L.metric)
              (H.backwardSurvivorIncomingMap first last hle G (Ξ tip)) (2*r) := by
  obtain ⟨C₀,hC₀,hbound⟩ :=
    StandardCap.exists_uniform_window_image_scalar_bound_of_scaled_pullback
  exact ⟨C₀,hC₀,hbound,prepared_incoming_cap_geometry_of_scalar_bound D r eps C heps hepssmall hr hfit C₀ hC₀ hbound⟩

private theorem prepared_incoming_cap_product_exclusion_of_scalar_bound
    (D r eps : ℝ) (C : ℝ≥0)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D)
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hscalar_bound :
      ∀ {E : Type uE} {H : Type uH} {M : Type uM} {N : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
        [T2Space N]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ε : ℝ} (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ε),
        ε ≤ 1 / 2 → 2 ≤ m →
        ∀ (h : SmoothRiemannianMetric ThreeModel N) (J : standardCapWindow D → N),
        IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
        ∀ q : ℝ, 0 < q →
        (∀ x v z, w.windowMetric.inner x v z =
          q * h.inner (J x) (mfderiv ThreeModel ThreeModel J x v)
            (mfderiv ThreeModel ThreeModel J x z)) →
        ∀ x : standardCapWindow D, ‖x.val‖ < D →
          |metricScalarAt h (J x)| ≤ C₀ * q) :
    ∃ η ε₀ δ₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
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
      ∀ (q q₀ a₀ : ℝ), 0 < q → 0 < q₀ → q₀ ≤ C₀ * q → 1 ≤ a₀ * q →
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
      q * (s - H.time first) ≤ η →
      ∀ (z : standardCapWindow D) (x : G.terminalRegularOpen)
        (A : BackwardPointTrace H first last hle x.val), ‖z.val‖ < r →
        A.point first le_rfl hle = J z →
      ∀ (Q A : ℝ) (hQ : 0 < Q), Q / q ≤ A →
      ∀ {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        [TopologicalSpace H'] {Jp : ModelWithCorners ℝ F H'} [Jp.Boundaryless]
        {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold Jp ∞ N]
        [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]
        (hprod : SmoothRiemannianMetric Jp N), Module.finrank ℝ F = 2 →
      ∀ (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens G.terminalRegularOpen)
        (Φ : O ≃ₘ⟮Jp.prod 𝓘(ℝ), I3⟯ V),
      riemannianBallOf (scaleMetric Q hQ L.metric) x (4 * Real.sqrt A * r) ⊆ V →
      ∀ δprod : ℝ, δprod ≤ 1/4 → 720 * δprod < ((7/8 : ℝ) / A) / 16 →
      (∀ y : V, ∀ n : ℕ, n ≤ 2 →
        metricDerivNorm n (Diffeomorph.pullbackMetricCross ((scaleMetric Q hQ L.metric).restrictOpen V) Φ)
          ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O)
          ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm y) ≤ δprod) → False := by
  obtain ⟨η,ε₀,δ₀,hη,hε₀,hεhalf,hδ₀,hexclude⟩ :=
    exists_uniform_incoming_cap_product_exclusion D r eps C₀ C hC₀ heps hepssmall hr hfit
  refine ⟨η,ε₀,δ₀,hη,hε₀,hεhalf,hδ₀,?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hmargin hm hζ
    inc H first last hle s G L hinit Jbig hJbig J q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hδ hderiv hfinal htime z x Atrace hz hanchor
  have hD : 0 < D := by
    have hi := inv_pos.mpr heps
    have ht := StandardCap.transitionEnd_pos
    linarith
  have hDD : D ≤ Dbig := by linarith only [hmargin]
  obtain ⟨wsmall,hwsmall⟩ : ∃ ws : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ,
      ws = w.restrictWindow hD hDD := ⟨_,rfl⟩
  obtain ⟨hJ,hupperRaw,hmetricRaw,hscalar⟩ := prepared_window_restriction_bounds
    (E := E) (H := H0) (M := M) (N := (H.stage first).Carrier) (I := I)
    (g := g) (x₀ := x₀) (δ := δ) (k := k) (d := d) (A := A) (hA := hA) (m := m) (ζ := ζ)
    hD hmargin w
    (hζ.trans hεhalf) (H.initialMetric first) Jbig hJbig hzero
    (fun x hx => (le_abs_self _).trans (hscalar_bound (E := E) (H := H0) (M := M) (N := (H.stage first).Carrier) (I := I)
      (g := g) (x₀ := x₀) (δ := δ) (k := k) (d := d) (A := A) (hA := hA) (D := Dbig)
      (m := m) (ε := ζ) w (hζ.trans hεhalf) (by omega)
      (H.initialMetric first) Jbig hJbig q hq hzero x hx))
  have hupper : ∀ x : standardCapWindow D, ∀ v : TangentSpace ThreeModel x,
      wsmall.windowMetric.inner x v v ≤ (3/2:ℝ)*StandardCap.metric.inner x.val v v := by
    rw [hwsmall]
    exact hupperRaw
  have hmetric : ∀ x (v t : TangentSpace ThreeModel x), wsmall.windowMetric.inner x v t =
      q*(H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x t) := by
    rw [hwsmall]
    exact hmetricRaw
  exact hexclude (E := E) (H := H0) (M := M) (I := I)
    (g := g) (x₀ := x₀) (δ := δ) (k := k) (d := d) (A := A) (hA := hA)
    (m := m) (ζ := ζ) wsmall hm hζ hupper H first last hle s G L hinit J hJ
    q q₀ a₀ hq hq₀ hq₀Q haq hmetric hscalar parameters records hfixed hlower hδ hderiv hfinal
    htime z x Atrace hz hanchor

theorem exists_uniform_prepared_incoming_cap_product_exclusion
    (D r eps : ℝ) (C : ℝ≥0)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ (
      ∀ {E : Type uE} {H : Type uH} {M : Type uM} {N : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
        [T2Space N]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ε : ℝ} (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ε),
        ε ≤ 1 / 2 → 2 ≤ m →
        ∀ (h : SmoothRiemannianMetric ThreeModel N) (J : standardCapWindow D → N),
        IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
        ∀ q : ℝ, 0 < q →
        (∀ x v z, w.windowMetric.inner x v z =
          q * h.inner (J x) (mfderiv ThreeModel ThreeModel J x v)
            (mfderiv ThreeModel ThreeModel J x z)) →
        ∀ x : standardCapWindow D, ‖x.val‖ < D →
          |metricScalarAt h (J x)| ≤ C₀ * q) ∧
    ∃ η ε₀ δ₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
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
      ∀ (q q₀ a₀ : ℝ), 0 < q → 0 < q₀ → q₀ ≤ C₀ * q → 1 ≤ a₀ * q →
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
      q * (s - H.time first) ≤ η →
      ∀ (z : standardCapWindow D) (x : G.terminalRegularOpen)
        (A : BackwardPointTrace H first last hle x.val), ‖z.val‖ < r →
        A.point first le_rfl hle = J z →
      ∀ (Q A : ℝ) (hQ : 0 < Q), Q / q ≤ A →
      ∀ {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        [TopologicalSpace H'] {Jp : ModelWithCorners ℝ F H'} [Jp.Boundaryless]
        {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold Jp ∞ N]
        [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]
        (hprod : SmoothRiemannianMetric Jp N), Module.finrank ℝ F = 2 →
      ∀ (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens G.terminalRegularOpen)
        (Φ : O ≃ₘ⟮Jp.prod 𝓘(ℝ), I3⟯ V),
      riemannianBallOf (scaleMetric Q hQ L.metric) x (4 * Real.sqrt A * r) ⊆ V →
      ∀ δprod : ℝ, δprod ≤ 1/4 → 720 * δprod < ((7/8 : ℝ) / A) / 16 →
      (∀ y : V, ∀ n : ℕ, n ≤ 2 →
        metricDerivNorm n (Diffeomorph.pullbackMetricCross ((scaleMetric Q hQ L.metric).restrictOpen V) Φ)
          ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O)
          ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm y) ≤ δprod) → False := by
  obtain ⟨C₀,hC₀,hbound⟩ :=
    StandardCap.exists_uniform_window_image_scalar_bound_of_scaled_pullback
  exact ⟨C₀,hC₀,hbound,prepared_incoming_cap_product_exclusion_of_scalar_bound D r eps C heps hepssmall hr hfit C₀ hC₀ hbound⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

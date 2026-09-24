import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowSurvival
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWindowRestriction
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩
private local instance (V : TopologicalSpace.Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

private theorem window_scalar_eq_of_scaled_inner
    {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] [T2Space N]
    {D : ℝ} (gW : SmoothRiemannianMetric ThreeModel (standardCapWindow D))
    (h : SmoothRiemannianMetric ThreeModel N)
    (J : standardCapWindow D → N) (hJ : IsSmoothEmbedding ThreeModel ThreeModel ∞ J)
    {q : ℝ} (hq : 0 < q)
    (hinner : ∀ x v z, gW.inner x v z =
      q * h.inner (J x) (mfderiv ThreeModel ThreeModel J x v)
        (mfderiv ThreeModel ThreeModel J x z))
    (x : standardCapWindow D) :
    metricScalarAt gW x = metricScalarAt h (J x) / q := by
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ J := by
    obtain ⟨Q, hQng, hQns, hQimm⟩ := hJ.isImmersion
    apply isLocalDiffeomorph_of_injective_mfderiv J hJ.contMDiff _ rfl
    intro y
    exact injective_mfderiv_of_isImmersionAt ThreeModel ThreeModel J y
      ⟨Q, hQng, hQns, hQimm y⟩
  have heq : gW = pullbackMetricOfInjectiveLocalDiffeomorph
      (scaleMetric q hq h) J hlocal hJ.isEmbedding.injective := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v z
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner]
    exact hinner y v z
  rw [heq]
  exact metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale
    h J hlocal hJ.isEmbedding.injective q hq x

private theorem exists_uniform_prepared_window_image_scalar_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
        [T2Space N]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ε : ℝ} (w : CanonicalStaticInsertionWitness d A hA D m ε),
        ε ≤ 1 / 2 → 2 ≤ m →
        ∀ (h : SmoothRiemannianMetric ThreeModel N) (J : standardCapWindow D → N),
        IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
        ∀ q : ℝ, 0 < q →
        (∀ x v z, w.windowMetric.inner x v z =
          q * h.inner (J x) (mfderiv ThreeModel ThreeModel J x v)
            (mfderiv ThreeModel ThreeModel J x z)) →
        ∀ x : standardCapWindow D, ‖x.val‖ < D →
          |metricScalarAt h (J x)| ≤ C * q := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_window_scalar_bound
  refine ⟨C, hC, ?_⟩
  intro E H M N _ _ _ _ _ I _ _ _ _ _ _ _ _ _ g x₀ δ k d A hA D m ε w hε hm
    h J hJ q hq hinner x hx
  have hb := hbound w hε hm x hx
  rw [window_scalar_eq_of_scaled_inner w.windowMetric h J hJ hq hinner x,
    abs_div, abs_of_pos hq] at hb
  exact (div_le_iff₀ hq).mp hb

end DifferentialGeometry.PDE.RicciFlow.StandardCap

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

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

theorem exists_uniform_prepared_cap_window_survival_time
    (D r eps : ℝ) (C : ℝ≥0)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ C₀ η ε₀ δ₀ : ℝ, 0 < C₀ ∧ 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {Dbig : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ)
        (hmargin : D + 1 ≤ Dbig),
      ⌈eps⁻¹⌉₊ + 2 ≤ m → ζ ≤ ε₀ →
      let inc : standardCapWindow D → standardCapWindow Dbig := TopologicalSpace.Opens.inclusion
        (show standardCapWindow D ≤ standardCapWindow Dbig from
          by
          intro x hx
          change ‖x‖ < Dbig + 1
          change ‖x‖ < D + 1 at hx
          linarith only [hx, hmargin]);
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (Jbig : standardCapWindow Dbig → (H.stage first).Carrier),
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
      q * (H.time last - H.time first) ≤ η →
      ∀ (z : standardCapWindow D) (endpoint : (H.stage last).Carrier)
        (A : BackwardPointTrace H first last hle endpoint), A.point first le_rfl hle = J z →
      ∃ Ψ : standardCapWindow D → H.backwardSurvivorDomain first last hle,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ψ ∧
        ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ψ x) = J x := by
  obtain ⟨C₀,hC₀,hscalar_bound⟩ := StandardCap.exists_uniform_prepared_window_image_scalar_bound
  obtain ⟨η,ε₀,δ₀,hη,hε₀,hεhalf,hδ₀,hsurvive⟩ :=
    exists_uniform_cap_window_survival_time D r eps C₀ C hC₀ heps hepssmall hr hfit
  refine ⟨C₀,η,ε₀,δ₀,hC₀,hη,hε₀,hεhalf,hδ₀,?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hmargin hm hζ
    inc H first last hle Jbig hJbig J q q₀ a₀ hq hq₀ hq₀Q haq hzero parameters records hfixed hlower hδ hderiv htime
    z endpoint Atrace hanchor
  have hD : 0 < D := by
    have hi := inv_pos.mpr heps
    have ht := StandardCap.transitionEnd_pos
    linarith
  have hDD : D ≤ Dbig := by linarith
  let hs : standardCapWindow D ≤ standardCapWindow Dbig := by
    intro x hx
    change ‖x‖ < Dbig + 1
    change ‖x‖ < D + 1 at hx
    linarith only [hx, hDD]
  let wsmall := w.restrictWindow hD hDD
  have hJ : IsSmoothEmbedding ThreeModel ThreeModel ∞ J :=
    hJbig.comp (window_inclusion_isSmoothEmbedding hDD) (by simp)
  have hpoint (x : standardCapWindow D) : ‖(inc x).val‖ < Dbig :=
    x.property.trans_le hmargin
  have hupper (x : standardCapWindow D) (v : TangentSpace ThreeModel x) :
      wsmall.windowMetric.inner x v v ≤ (3/2 : ℝ) * StandardCap.metric.inner x.val v v := by
    rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
    change w.windowMetric.inner (inc x) v v ≤ _
    have hb := (w.window_inner_bounds (hζ.trans hεhalf) (hpoint x) v).2
    rw [standardCapMetric_eq_metric] at hb
    change w.windowMetric.inner (inc x) v v ≤ (3/2 : ℝ) * StandardCap.metric.inner x.val v v at hb
    exact hb
  have hmetric (x : standardCapWindow D) (v z : TangentSpace ThreeModel x) :
      wsmall.windowMetric.inner x v z = q * (H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x z) := by
    rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
    change w.windowMetric.inner (inc x) v z = _
    have hz := hzero (inc x) (show TangentSpace ThreeModel (inc x) from v)
      (show TangentSpace ThreeModel (inc x) from z)
    have hd := mfderiv_comp x (hJbig.contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_inclusion (I := ThreeModel) (n := ∞) hs).mdifferentiableAt (by simp))
    simp only [mfderiv_opens_incl] at hd
    dsimp only [TangentSpace] at hd hz ⊢
    rw [hd]
    exact hz
  have hscalar (x : standardCapWindow D) : metricScalarAt (H.initialMetric first) (J x) ≤ C₀*q := by
    exact le_abs_self _ |>.trans (hscalar_bound w (hζ.trans hεhalf) (by omega)
      (H.initialMetric first) Jbig hJbig q hq hzero (inc x) (hpoint x))
  exact hsurvive wsmall hm hζ hupper H first last hle J hJ q q₀ a₀ hq hq₀ hq₀Q haq
    hmetric hscalar parameters records hfixed hlower hδ hderiv htime z endpoint Atrace hanchor
theorem exists_uniform_prepared_incoming_cap_window_survival_time
    (D r eps : ℝ) (C : ℝ≥0)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ C₀ η ε₀ δ₀ : ℝ, 0 < C₀ ∧ 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {Dbig : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ)
        (hmargin : D + 1 ≤ Dbig),
      ⌈eps⁻¹⌉₊ + 2 ≤ m → ζ ≤ ε₀ →
      let inc : standardCapWindow D → standardCapWindow Dbig := TopologicalSpace.Opens.inclusion
        (show standardCapWindow D ≤ standardCapWindow Dbig from
          by
          intro x hx
          change ‖x‖ < Dbig + 1
          change ‖x‖ < D + 1 at hx
          linarith only [hx, hmargin]);
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s),
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
      ∀ (z : standardCapWindow D) (endpoint : (H.stage last).Carrier)
        (A : BackwardPointTrace H first last hle endpoint), A.point first le_rfl hle = J z →
      ∃ Ψ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ψ ∧
        ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ψ x).val = J x := by
  obtain ⟨C₀,hC₀,hscalar_bound⟩ := StandardCap.exists_uniform_prepared_window_image_scalar_bound
  obtain ⟨η,ε₀,δ₀,hη,hε₀,hεhalf,hδ₀,hsurvive⟩ :=
    exists_uniform_incoming_cap_window_survival_time D r eps C₀ C hC₀ heps hepssmall hr hfit
  refine ⟨C₀,η,ε₀,δ₀,hC₀,hη,hε₀,hεhalf,hδ₀,?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hmargin hm hζ
    inc H first last hle s G hinit Jbig hJbig J q q₀ a₀ hq hq₀ hq₀Q haq hzero parameters records hfixed hlower hδ hderiv hfinal htime
    z endpoint Atrace hanchor
  have hD : 0 < D := by
    have hi := inv_pos.mpr heps
    have ht := StandardCap.transitionEnd_pos
    linarith
  have hDD : D ≤ Dbig := by linarith
  let hs : standardCapWindow D ≤ standardCapWindow Dbig := by
    intro x hx
    change ‖x‖ < Dbig + 1
    change ‖x‖ < D + 1 at hx
    linarith only [hx, hDD]
  let wsmall := w.restrictWindow hD hDD
  have hJ : IsSmoothEmbedding ThreeModel ThreeModel ∞ J :=
    hJbig.comp (window_inclusion_isSmoothEmbedding hDD) (by simp)
  have hpoint (x : standardCapWindow D) : ‖(inc x).val‖ < Dbig :=
    x.property.trans_le hmargin
  have hupper (x : standardCapWindow D) (v : TangentSpace ThreeModel x) :
      wsmall.windowMetric.inner x v v ≤ (3/2 : ℝ) * StandardCap.metric.inner x.val v v := by
    rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
    change w.windowMetric.inner (inc x) v v ≤ _
    have hb := (w.window_inner_bounds (hζ.trans hεhalf) (hpoint x) v).2
    rw [standardCapMetric_eq_metric] at hb
    change w.windowMetric.inner (inc x) v v ≤ (3/2 : ℝ) * StandardCap.metric.inner x.val v v at hb
    exact hb
  have hmetric (x : standardCapWindow D) (v z : TangentSpace ThreeModel x) :
      wsmall.windowMetric.inner x v z = q * (H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x z) := by
    rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
    change w.windowMetric.inner (inc x) v z = _
    have hz := hzero (inc x) (show TangentSpace ThreeModel (inc x) from v)
      (show TangentSpace ThreeModel (inc x) from z)
    have hd := mfderiv_comp x (hJbig.contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_inclusion (I := ThreeModel) (n := ∞) hs).mdifferentiableAt (by simp))
    simp only [mfderiv_opens_incl] at hd
    dsimp only [TangentSpace] at hd hz ⊢
    rw [hd]
    exact hz
  have hscalar (x : standardCapWindow D) : metricScalarAt (H.initialMetric first) (J x) ≤ C₀*q := by
    exact le_abs_self _ |>.trans (hscalar_bound w (hζ.trans hεhalf) (by omega)
      (H.initialMetric first) Jbig hJbig q hq hzero (inc x) (hpoint x))
  exact hsurvive wsmall hm hζ hupper H first last hle s G hinit J hJ q q₀ a₀ hq hq₀ hq₀Q haq
    hmetric hscalar parameters records hfixed hlower hδ hderiv hfinal htime z endpoint Atrace hanchor

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

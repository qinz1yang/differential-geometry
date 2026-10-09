import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedInterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventSurvivorMap
import DifferentialGeometry.Geometry.Metric.Comparison.IsometricBalls
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Topology.SigmaCompactOpen

noncomputable section

open Set Manifold MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem exists_survivor_ambient_ball_images
    (W : TopologicalSpace.Opens E.incoming.terminalRegularOpen)
    (hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' E.old))
    (p : E.incoming.terminalRegularOpen) {R : ℝ}
    (hcpt : IsCompact (riemannianClosedBallOf E.terminal.metric p R))
    (hball : riemannianClosedBallOf E.terminal.metric p R ⊆ W) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel
        E.incoming.terminalRegularOpen Q.Carrier ∞,
      F.source = W ∧
      (∀ x ∈ W, E.RegularCrossing x.val (F x)) ∧
      (∀ z : E.old, E.oldTerminal z ∈ W → F (E.oldTerminal z) = E.oldOutput z) ∧
      (∀ z : E.old, E.oldTerminal z ∈ W →
        E.transition.trace.presentation (E.transition.trace.capping.coreInclusion z.val) =
          Sum.inl (F (E.oldTerminal z))) ∧
      (∀ x ∈ W, ∀ v w : TangentSpace ThreeModel x,
        E.outputMetric.inner (F x) (mfderiv ThreeModel ThreeModel (F : _ → _) x v)
          (mfderiv ThreeModel ThreeModel (F : _ → _) x w) =
          E.terminal.metric.inner x v w) ∧
      (∀ r : ℝ, 0 ≤ r → r < R →
        (F : E.incoming.terminalRegularOpen → Q.Carrier) ''
            riemannianClosedBallOf E.terminal.metric p r =
          riemannianClosedBallOf E.outputMetric (F p) r) ∧
      (∀ r : ℝ, 0 < r → r < R →
        (F : E.incoming.terminalRegularOpen → Q.Carrier) ''
            riemannianBallOf E.terminal.metric p r =
          riemannianBallOf E.outputMetric (F p) r) ∧
      ∀ r : ℝ, 0 ≤ r → r < R →
        IsCompact (riemannianClosedBallOf E.outputMetric (F p) r) := by
  have hp : p ∈ W := hball (by
    change riemannianEDistOf E.terminal.metric p p ≤ ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact bot_le)
  obtain ⟨F, hsource, hcross, hold, hmetric⟩ :=
    E.exists_survivor_partialDiffeomorph W ⟨p, hp⟩ hW
  have hsourceball : riemannianClosedBallOf E.terminal.metric p R ⊆ F.source := by
    rw [hsource]
    exact hball
  have hmetricball (x) (hx : x ∈ riemannianClosedBallOf E.terminal.metric p R)
      (v : TangentSpace ThreeModel x) := hmetric x (hball hx) v v
  have hclosed (r : ℝ) (hr : 0 ≤ r) (hrR : r < R) :=
    DifferentialGeometry.PartialDiffeomorph.image_riemannianClosedBall_eq_of_isometric_on_compact_ball
      E.terminal.metric E.outputMetric F p hr hrR hcpt hsourceball hmetricball
  refine ⟨F, hsource, hcross, hold, ?_, hmetric, hclosed, ?_, ?_⟩
  · intro z hz
    rw [hold z hz]
    exact E.oldOutput_eq z
  · intro r hr hrR
    exact DifferentialGeometry.PartialDiffeomorph.image_riemannianBall_eq_of_isometric_on_compact_ball
      E.terminal.metric E.outputMetric F p hr hrR hcpt hsourceball hmetricball
  · intro r hr hrR
    rw [← hclosed r hr hrR]
    have hsub := riemannianClosedBallOf_mono E.terminal.metric p hrR.le
    have hclosedball : IsClosed (riemannianClosedBallOf E.terminal.metric p r) :=
      isClosed_le (continuous_riemannianEDist E.terminal.metric p) continuous_const
    exact (hcpt.of_isClosed_subset hclosedball hsub).image_of_continuousOn
      (F.contMDiffOn_toFun.continuousOn.mono (hsub.trans hsourceball))

private local instance : MeasurableSpace E.incoming.terminalRegularOpen :=
  borel E.incoming.terminalRegularOpen
private local instance : BorelSpace E.incoming.terminalRegularOpen := ⟨rfl⟩
private local instance : SigmaCompactSpace E.incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel E.incoming.terminalRegularOpen.isOpen)

theorem exists_survivor_ambient_ball_volume_eq
    (W : TopologicalSpace.Opens E.incoming.terminalRegularOpen)
    (hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' E.old))
    (p : E.incoming.terminalRegularOpen) {R : ℝ}
    (hcpt : IsCompact (riemannianClosedBallOf E.terminal.metric p R))
    (hball : riemannianClosedBallOf E.terminal.metric p R ⊆ W) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel
        E.incoming.terminalRegularOpen Q.Carrier ∞,
      F.source = W ∧
      (∀ x ∈ W, E.RegularCrossing x.val (F x)) ∧
      (∀ z : E.old, E.oldTerminal z ∈ W → F (E.oldTerminal z) = E.oldOutput z) ∧
      (∀ z : E.old, E.oldTerminal z ∈ W →
        E.transition.trace.presentation (E.transition.trace.capping.coreInclusion z.val) =
          Sum.inl (F (E.oldTerminal z))) ∧
      (∀ x ∈ W, ∀ v w : TangentSpace ThreeModel x,
        E.outputMetric.inner (F x) (mfderiv ThreeModel ThreeModel (F : _ → _) x v)
          (mfderiv ThreeModel ThreeModel (F : _ → _) x w) =
          E.terminal.metric.inner x v w) ∧
      (∀ r : ℝ, 0 ≤ r → r < R →
        (F : E.incoming.terminalRegularOpen → Q.Carrier) ''
            riemannianClosedBallOf E.terminal.metric p r =
          riemannianClosedBallOf E.outputMetric (F p) r) ∧
      (∀ r : ℝ, 0 < r → r < R →
        (F : E.incoming.terminalRegularOpen → Q.Carrier) ''
            riemannianBallOf E.terminal.metric p r =
          riemannianBallOf E.outputMetric (F p) r) ∧
      (∀ r : ℝ, 0 ≤ r → r < R →
        IsCompact (riemannianClosedBallOf E.outputMetric (F p) r)) ∧
      ∀ r : ℝ, 0 < r → r < R →
        riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
          (riemannianBallOf E.outputMetric (F p) r) =
        riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric
          (riemannianBallOf E.terminal.metric p r) := by
  obtain ⟨F, hsource, hcross, hold, hpresentation, hmetric, hclosed, hopen, hcompact⟩ :=
    E.exists_survivor_ambient_ball_images W hW p hcpt hball
  refine ⟨F, hsource, hcross, hold, hpresentation, hmetric, hclosed, hopen, hcompact, ?_⟩
  intro r hr hrR
  rw [← hopen r hr hrR]
  symm
  let F₁ : PartialDiffeomorph ThreeModel ThreeModel E.incoming.terminalRegularOpen Q.Carrier 1 :=
    { F.toPartialEquiv with
      open_source := F.open_source
      open_target := F.open_target
      contMDiffOn_toFun := F.contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun := F.contMDiffOn_invFun.of_le (by norm_num) }
  apply riemannianVolumeMeasure_image_of_partialIsometry E.terminal.metric E.outputMetric F₁
  · intro x hx v w
    change x ∈ F.source at hx
    have hxW : x ∈ W := by
      change x ∈ (W : Set E.incoming.terminalRegularOpen)
      rw [← hsource]
      exact hx
    exact (hmetric x hxW v w).symm
  · exact (isOpen_lt (continuous_riemannianEDist E.terminal.metric p) continuous_const).measurableSet
  · change riemannianBallOf E.terminal.metric p r ⊆ F.source
    rw [hsource]
    intro x hx
    exact hball (hx.le.trans (ENNReal.ofReal_le_ofReal hrR.le))

theorem riemannianVolumeMeasure_ball_eq_of_regularCrossing
    (p : E.incoming.terminalRegularOpen) (q : Q.Carrier)
    (hcross : E.RegularCrossing p.val q) {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hcpt : IsCompact (riemannianClosedBallOf E.terminal.metric p R))
    (hprotected : ∀ x ∈ riemannianClosedBallOf E.terminal.metric p R,
      x.val ∈ interior (Subtype.val '' E.old)) :
    riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
      (riemannianBallOf E.outputMetric q r) =
    riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric
      (riemannianBallOf E.terminal.metric p r) := by
  let W : TopologicalSpace.Opens E.incoming.terminalRegularOpen :=
    ⟨Subtype.val ⁻¹' interior (Subtype.val '' E.old), isOpen_interior.preimage continuous_subtype_val⟩
  have hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' E.old) := fun _ hx => hx
  obtain ⟨F, _, hFcross, _, _, _, _, _, _, hvolume⟩ :=
    E.exists_survivor_ambient_ball_volume_eq W hW p hcpt hprotected
  have hp : p ∈ W := hprotected p (by
    change riemannianEDistOf E.terminal.metric p p ≤ ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact bot_le)
  have heq : F p = q := E.regularCrossing_right_unique (hFcross p hp) hcross
  simpa only [heq] using hvolume r hr hrR

theorem volume_ball_lower_bound_of_regularCrossing
    (p : E.incoming.terminalRegularOpen) (q : Q.Carrier)
    (hcross : E.RegularCrossing p.val q) {R r κ : ℝ} (hr : 0 < r) (hrR : r < R)
    (hcpt : IsCompact (riemannianClosedBallOf E.terminal.metric p R))
    (hprotected : ∀ x ∈ riemannianClosedBallOf E.terminal.metric p R,
      x.val ∈ interior (Subtype.val '' E.old))
    (hvolume : ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric
        (riemannianBallOf E.terminal.metric p r)) :
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
        (riemannianBallOf E.outputMetric q r) := by
  rw [E.riemannianVolumeMeasure_ball_eq_of_regularCrossing p q hcross hr hrR hcpt hprotected]
  exact hvolume

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section

open Set Manifold MeasureTheory Filter
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

private theorem inner_symm_of_partialDiffeomorph_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph I J M N ∞)
    (hinner : ∀ x ∈ Φ.source, ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    {y : N} (hy : y ∈ Φ.target) (v w : TangentSpace J y) :
    h.inner y v w = g.inner (Φ.symm y)
      (mfderiv J I Φ.symm y v) (mfderiv J I Φ.symm y w) := by
  have hright : Φ (Φ.symm y) = y := Φ.right_inv' hy
  have heq : (Φ : M → N) ∘ (Φ.symm : N → M) =ᶠ[𝓝 y] id := by
    filter_upwards [Φ.open_target.mem_nhds hy] with z hz
    exact Φ.right_inv' hz
  have hd (u : TangentSpace J y) :
      (mfderiv I J Φ (Φ.symm y) : E →L[ℝ] F) (mfderiv J I Φ.symm y u) = u := by
    have hc := mfderiv_comp_apply y (Φ.mdifferentiableAt (by simp) (Φ.symm.map_source' hy))
      (Φ.symm.mdifferentiableAt (by simp) hy) u
    rw [heq.mfderiv_eq, mfderiv_id] at hc
    exact hc.symm
  have hh := hinner (Φ.symm y) (Φ.symm.map_source' hy)
    (mfderiv J I Φ.symm y v) (mfderiv J I Φ.symm y w)
  rw [hd v, hd w] at hh
  exact (congrArg (fun z : N => h.inner z v w) hright).symm.trans hh.symm


end DifferentialGeometry.PartialDiffeomorph

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

private local instance : MeasurableSpace Q.Carrier := borel Q.Carrier
private local instance : BorelSpace Q.Carrier := ⟨rfl⟩

private local instance : MeasurableSpace E.incoming.terminalRegularOpen :=
  borel E.incoming.terminalRegularOpen
private local instance : BorelSpace E.incoming.terminalRegularOpen := ⟨rfl⟩
private local instance : SigmaCompactSpace E.incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel E.incoming.terminalRegularOpen.isOpen)

private theorem output_regularCrossing_ball_subset_target
    (q : Q.Carrier)
    (F : PartialDiffeomorph ThreeModel ThreeModel
      E.incoming.terminalRegularOpen Q.Carrier ∞)
    (hsource : F.source = {x | x.val ∈ interior (Subtype.val '' E.old)})
    (hFcross : ∀ x ∈ F.source, E.RegularCrossing x.val (F x))
    {R : ℝ}
    (hprotected : ∀ y ∈ riemannianClosedBallOf E.outputMetric q R,
      ∃ x : E.incoming.terminalRegularOpen, E.RegularCrossing x.val y) :
    riemannianClosedBallOf E.outputMetric q R ⊆ F.target := by
  intro y hy
  obtain ⟨x, hx⟩ := hprotected y hy
  have hxs : x ∈ F.source := by
    rw [hsource]
    obtain ⟨G, hGsource, hxG, _, _, _, _⟩ := hx.exists_survivor_partialDiffeomorph E
    rw [hGsource] at hxG
    exact hxG
  have heq : F x = y := E.regularCrossing_right_unique (hFcross x hxs) hx
  exact heq ▸ F.map_source hxs


private theorem volume_ball_eq_of_output_regularCrossing_buffer
    (p : E.incoming.terminalRegularOpen) (q : Q.Carrier)
    (hcross : E.RegularCrossing p.val q) {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hprotected : ∀ y ∈ riemannianClosedBallOf E.outputMetric q R,
      ∃ x : E.incoming.terminalRegularOpen, E.RegularCrossing x.val y) :
    riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
      (riemannianBallOf E.outputMetric q r) =
    riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric
      (riemannianBallOf E.terminal.metric p r) := by
  obtain ⟨F, hsource, hp, hpq, hq, hFcross, hmetric⟩ :=
    hcross.exists_survivor_partialDiffeomorph E
  have htarget := output_regularCrossing_ball_subset_target E q F hsource hFcross hprotected
  have hcpt : IsCompact (riemannianClosedBallOf E.outputMetric q R) :=
    (isClosed_le (continuous_riemannianEDist E.outputMetric q) continuous_const).isCompact
  have hinverse (y : Q.Carrier) (hy : y ∈ F.target) (v w : TangentSpace ThreeModel y) :
      E.outputMetric.inner y v w = E.terminal.metric.inner (F.symm y)
        (mfderiv ThreeModel ThreeModel F.symm y v) (mfderiv ThreeModel ThreeModel F.symm y w) :=
    DifferentialGeometry.PartialDiffeomorph.inner_symm_of_partialDiffeomorph_inner
      E.terminal.metric E.outputMetric F (fun x hx v w => (hmetric x hx v w).symm) hy v w
  have hcenter : F.symm q = p := by
    rw [← hpq]
    exact F.left_inv' hp
  have hopen : (F.symm : Q.Carrier → E.incoming.terminalRegularOpen) ''
      riemannianBallOf E.outputMetric q r = riemannianBallOf E.terminal.metric p r := by
    rw [← hcenter]
    exact DifferentialGeometry.PartialDiffeomorph.image_riemannianBall_eq_of_isometric_on_compact_ball
      E.outputMetric E.terminal.metric F.symm q hr hrR hcpt htarget
      (fun y hy v => (hinverse y (htarget hy) v v).symm)
  rw [← hopen]
  let F₁ : PartialDiffeomorph ThreeModel ThreeModel Q.Carrier E.incoming.terminalRegularOpen 1 :=
    { F.symm.toPartialEquiv with
      open_source := F.open_target
      open_target := F.open_source
      contMDiffOn_toFun := F.symm.contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun := F.symm.contMDiffOn_invFun.of_le (by norm_num) }
  apply riemannianVolumeMeasure_image_of_partialIsometry E.outputMetric E.terminal.metric F₁
  · exact hinverse
  · exact (isOpen_lt (continuous_riemannianEDist E.outputMetric q) continuous_const).measurableSet
  · intro y hy
    exact htarget (hy.le.trans (ENNReal.ofReal_le_ofReal hrR.le))


theorem riemannianVolumeMeasure_ball_eq_of_regularCrossing_of_output_buffer
    (p : E.incoming.terminalRegularOpen) (q : Q.Carrier)
    (hcross : E.RegularCrossing p.val q) {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hprotected : riemannianClosedBallOf E.outputMetric q R ⊆ interior (range E.oldOutput)) :
    riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
      (riemannianBallOf E.outputMetric q r) =
    riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric
      (riemannianBallOf E.terminal.metric p r) :=
  volume_ball_eq_of_output_regularCrossing_buffer E p q hcross hr hrR
    (fun y hy => E.exists_terminal_regularCrossing_of_mem_interior_oldOutput y (hprotected hy))

theorem volume_ball_lower_bound_of_regularCrossing_of_output_buffer
    (p : E.incoming.terminalRegularOpen) (q : Q.Carrier)
    (hcross : E.RegularCrossing p.val q) {R r κ : ℝ} (hr : 0 < r) (hrR : r < R)
    (hprotected : riemannianClosedBallOf E.outputMetric q R ⊆ interior (range E.oldOutput))
    (hvolume : ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric
        (riemannianBallOf E.terminal.metric p r)) :
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
        (riemannianBallOf E.outputMetric q r) := by
  rw [E.riemannianVolumeMeasure_ball_eq_of_regularCrossing_of_output_buffer p q hcross hr hrR hprotected]
  exact hvolume


theorem exists_terminal_ball_volume_eq_of_output_buffer
    (q : Q.Carrier) {R : ℝ}
    (hprotected : riemannianClosedBallOf E.outputMetric q R ⊆ interior (range E.oldOutput)) :
    ∃ p : E.incoming.terminalRegularOpen, E.RegularCrossing p.val q ∧
      ∀ r : ℝ, 0 < r → r < R →
        riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
          (riemannianBallOf E.outputMetric q r) =
        riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric
          (riemannianBallOf E.terminal.metric p r) := by
  have hq : q ∈ riemannianClosedBallOf E.outputMetric q R := by
    change riemannianEDistOf E.outputMetric q q ≤ ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact bot_le
  obtain ⟨p, hp⟩ := E.exists_terminal_regularCrossing_of_mem_interior_oldOutput q (hprotected hq)
  refine ⟨p, hp, ?_⟩
  intro r hr hrR
  exact E.riemannianVolumeMeasure_ball_eq_of_regularCrossing_of_output_buffer p q hp hr hrR hprotected



theorem isCompact_terminal_closedBall_of_regularCrossing_of_output_buffer
    (p : E.incoming.terminalRegularOpen) (q : Q.Carrier)
    (hcross : E.RegularCrossing p.val q) {R r : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hprotected : riemannianClosedBallOf E.outputMetric q R ⊆ interior (range E.oldOutput)) :
    IsCompact (riemannianClosedBallOf E.terminal.metric p r) := by
  obtain ⟨F, hsource, hp, hpq, hq, hFcross, hmetric⟩ :=
    hcross.exists_survivor_partialDiffeomorph E
  have htarget := output_regularCrossing_ball_subset_target E q F hsource hFcross
    (fun y hy => E.exists_terminal_regularCrossing_of_mem_interior_oldOutput y (hprotected hy))
  have hcpt : IsCompact (riemannianClosedBallOf E.outputMetric q R) :=
    (isClosed_le (continuous_riemannianEDist E.outputMetric q) continuous_const).isCompact
  have hinverse (y : Q.Carrier) (hy : y ∈ F.target) (v w : TangentSpace ThreeModel y) :
      E.outputMetric.inner y v w = E.terminal.metric.inner (F.symm y)
        (mfderiv ThreeModel ThreeModel F.symm y v) (mfderiv ThreeModel ThreeModel F.symm y w) :=
    DifferentialGeometry.PartialDiffeomorph.inner_symm_of_partialDiffeomorph_inner
      E.terminal.metric E.outputMetric F (fun x hx v w => (hmetric x hx v w).symm) hy v w
  have hcenter : F.symm q = p := by
    rw [← hpq]
    exact F.left_inv' hp
  have hclosed : (F.symm : Q.Carrier → E.incoming.terminalRegularOpen) ''
      riemannianClosedBallOf E.outputMetric q r = riemannianClosedBallOf E.terminal.metric p r := by
    rw [← hcenter]
    exact DifferentialGeometry.PartialDiffeomorph.image_riemannianClosedBall_eq_of_isometric_on_compact_ball
      E.outputMetric E.terminal.metric F.symm q hr hrR hcpt htarget
      (fun y hy v => (hinverse y (htarget hy) v v).symm)
  rw [← hclosed]
  have hsmall : IsCompact (riemannianClosedBallOf E.outputMetric q r) :=
    (isClosed_le (continuous_riemannianEDist E.outputMetric q) continuous_const).isCompact
  apply hsmall.image_of_continuousOn
  apply F.symm.contMDiffOn_toFun.continuousOn.mono
  exact (riemannianClosedBallOf_mono E.outputMetric q hrR.le).trans htarget

theorem exists_terminal_ball_compact_volume_eq_of_output_buffer
    (q : Q.Carrier) {R : ℝ}
    (hprotected : riemannianClosedBallOf E.outputMetric q R ⊆ interior (range E.oldOutput)) :
    ∃ p : E.incoming.terminalRegularOpen, E.RegularCrossing p.val q ∧
      (∀ r : ℝ, 0 ≤ r → r < R → IsCompact (riemannianClosedBallOf E.terminal.metric p r)) ∧
      ∀ r : ℝ, 0 < r → r < R →
        riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
          (riemannianBallOf E.outputMetric q r) =
        riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric
          (riemannianBallOf E.terminal.metric p r) := by
  obtain ⟨p, hp, hvolume⟩ := E.exists_terminal_ball_volume_eq_of_output_buffer q hprotected
  exact ⟨p, hp, (fun r hr hrR =>
    E.isCompact_terminal_closedBall_of_regularCrossing_of_output_buffer p q hp hr hrR hprotected), hvolume⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

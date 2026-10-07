import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862Reg_O77
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorDomain

/-!
# CH12-O77 G2: the incoming/outgoing event adapter for `Reg (R⁺)` (R6 D-R6-4)

The outgoing inclusion `B_out(q, r) ⊆ interior (range oldOutput)` (the O70 / S130 barrier form) is
**not** KL p.161 (3) verbatim.  `regEvent_of_outgoing_O77` proves the adapter: given the regular
crossing `p ↦ q` of the centre, the survivor chart `F` of the event (a local isometry with source the
retained open set `interior (val '' old)`) has `F.target ⊇ B_out(q, r)`; for every `ρ' < r` the
closed outgoing `(ρ'+r)/2`-ball is compact (properness) and inside `F.target`, so the isometry image
lemma (first exit along paths, `image_riemannianBall_eq_of_isometric_on_compact_ball`) gives
`F.symm '' B_out(q, ρ') = B_term(p', ρ')`.  Exhausting `B(·, ρ)` by the balls `B(·, ρ')`, `ρ' < ρ`,
yields the radius-preserving bijective correspondence for every `0 < ρ ≤ r` (no buffer `R > r` is
required), and `isCompact_terminal_closedBall_of_regularCrossing_of_output_buffer` gives compact
containment of the strictly interior incoming balls.  Ambient distances on the two sides are never
identified directly.

* `reg_of_outgoing_O77`: sectional clause + finite scalar bound + outgoing inclusions at the events
  of `(a, u]` along the centre trace ⟹ `Reg_O77` (for the U-R producer, O79).
* `reg_outgoing_O77`: `Reg_O77` ⟹ outgoing inclusions of every radius `ρ ≤ r` (barrier form, O79 G2).
* `regInput_of_reg_O77`: `Reg_O77` ⟹ the three inline binders of `[FROZEN] CH12-O78 Reg-input`
  ((Reg-ev ρ) in `initialMetric i.succ` / `backwardSurvivorDomain`, (Reg-fin K), (Reg-sec)).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

section helper

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

/-- Local copy of the private `inner_symm_of_partialDiffeomorph_inner` of `EventProtectedBalls`. -/
private theorem inner_symm_O77
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

/-- A point of an open metric ball lies in a strictly smaller concentric ball of positive radius. -/
theorem exists_smaller_ball_O77 (g : SmoothRiemannianMetric I M) (c z : M) {ρ : ℝ}
    (hz : z ∈ riemannianBallOf g c ρ) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' < ρ ∧ z ∈ riemannianBallOf g c ρ' := by
  obtain ⟨ρ', hρ'0, hzρ', hρ'ρ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hz
  have hpos : 0 < ENNReal.ofReal ρ' := lt_of_le_of_lt zero_le hzρ'
  have hρ'pos : 0 < ρ' := ENNReal.ofReal_pos.mp hpos
  have hρpos : 0 < ρ := ENNReal.ofReal_pos.mp (hpos.trans hρ'ρ)
  exact ⟨ρ', hρ'pos, (ENNReal.ofReal_lt_ofReal_iff hρpos).mp hρ'ρ, hzρ'⟩

/-- Closed balls of radius `R < r` lie in the open ball of radius `r`. -/
theorem closedBall_subset_ball_O77 (g : SmoothRiemannianMetric I M) (c : M) {R r : ℝ}
    (hRr : R < r) (hr : 0 < r) :
    riemannianClosedBallOf g c R ⊆ riemannianBallOf g c r := fun _ hy =>
  lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hRr)

end helper

/-- **G2 adapter** (`[FROZEN] CH12-O77`, `frozen_regEvent_of_outgoing_O77`): the outgoing inclusion
of the `r`-ball about the crossing image `q` of `p` gives the full incoming/outgoing event clause. -/
theorem regEvent_of_outgoing_O77 {P Q : OrientedThreeStage.{u}} {s₀ s₁ : ℝ}
    (E : MetricCutCapEvent P Q s₀ s₁) {p : P.Carrier} {q : Q.Carrier}
    (hcross : E.RegularCrossing p q) {r : ℝ}
    (hball : riemannianBallOf E.outputMetric q r ⊆ interior (range E.oldOutput)) :
    RegEvent_O77 E p q r := by
  have hcross0 := hcross
  obtain ⟨z, -, hzp, -⟩ := hcross0
  set p' : E.incoming.terminalRegularOpen := E.oldTerminal z
  have hp'val : p'.val = p := (E.oldTerminal_eq z).trans hzp
  have hc' : E.RegularCrossing p'.val q := hp'val ▸ hcross
  obtain ⟨F, hsource, hp, hpq, -, hFcross, hmetric⟩ := hc'.exists_survivor_partialDiffeomorph E
  have htarget : riemannianBallOf E.outputMetric q r ⊆ F.target := by
    intro y hy
    obtain ⟨x, hx⟩ := E.exists_terminal_regularCrossing_of_mem_interior_oldOutput y (hball hy)
    have hxs : x ∈ F.source := by
      rw [hsource]
      obtain ⟨G, hGsource, hxG, _, _, _, _⟩ := hx.exists_survivor_partialDiffeomorph E
      rw [hGsource] at hxG
      exact hxG
    have heq : F x = y := E.regularCrossing_right_unique (hFcross x hxs) hx
    exact heq ▸ F.map_source hxs
  have hinverse (y : Q.Carrier) (hy : y ∈ F.target) (v w : TangentSpace ThreeModel y) :
      E.outputMetric.inner y v w = E.terminal.metric.inner (F.symm y)
        (mfderiv ThreeModel ThreeModel F.symm y v) (mfderiv ThreeModel ThreeModel F.symm y w) :=
    inner_symm_O77 E.terminal.metric E.outputMetric F (fun x hx v w => (hmetric x hx v w).symm)
      hy v w
  have hcenter : F.symm q = p' := by
    rw [← hpq]
    exact F.left_inv' hp
  -- isometric image of every strictly smaller ball (compact closed buffer ball inside `F.target`)
  have himage : ∀ ρ : ℝ, 0 < ρ → ρ < r →
      (F.symm : Q.Carrier → E.incoming.terminalRegularOpen) '' riemannianBallOf E.outputMetric q ρ =
        riemannianBallOf E.terminal.metric p' ρ := by
    intro ρ hρ hρr
    have hr : 0 < r := hρ.trans hρr
    have hρR : ρ < (ρ + r) / 2 := by linarith
    have hRr : (ρ + r) / 2 < r := by linarith
    have hcpt : IsCompact (riemannianClosedBallOf E.outputMetric q ((ρ + r) / 2)) :=
      (isClosed_le (continuous_riemannianEDist E.outputMetric q) continuous_const).isCompact
    have hsub : riemannianClosedBallOf E.outputMetric q ((ρ + r) / 2) ⊆ F.target :=
      (closedBall_subset_ball_O77 E.outputMetric q hRr hr).trans htarget
    rw [← hcenter]
    exact DifferentialGeometry.PartialDiffeomorph.image_riemannianBall_eq_of_isometric_on_compact_ball
      E.outputMetric E.terminal.metric F.symm q hρ hρR hcpt hsub
      (fun y hy v => (hinverse y (hsub hy) v v).symm)
  -- a target point and its preimage cross regularly
  have hcrossF : ∀ y ∈ F.target, E.RegularCrossing (F.symm y).val y := by
    intro y hy
    have hc := hFcross (F.symm y) (F.map_target hy)
    have h2 : F (F.symm y) = y := F.right_inv' hy
    exact (congrArg (fun w => E.RegularCrossing (F.symm y).val w) h2).mp hc
  refine ⟨p', hp'val, hball, fun ρ hρ hρr => ⟨fun w hw => ?_, fun y hy => ?_⟩, fun ρ hρ0 hρr => ?_⟩
  · obtain ⟨ρ', hρ'0, hρ'ρ, hwρ'⟩ := exists_smaller_ball_O77 E.terminal.metric p' w hw
    rw [← himage ρ' hρ'0 (hρ'ρ.trans_le hρr)] at hwρ'
    obtain ⟨y, hy, rfl⟩ := hwρ'
    have hyt : y ∈ F.target :=
      htarget (riemannianBallOf_mono E.outputMetric q (hρ'ρ.trans_le hρr).le hy)
    have hws : F.symm y ∈ F.source := F.map_target hyt
    rw [hsource] at hws
    exact ⟨hws, y, riemannianBallOf_mono E.outputMetric q hρ'ρ.le hy, hcrossF y hyt⟩
  · obtain ⟨ρ', hρ'0, hρ'ρ, hyρ'⟩ := exists_smaller_ball_O77 E.outputMetric q y hy
    have hyt : y ∈ F.target :=
      htarget (riemannianBallOf_mono E.outputMetric q (hρ'ρ.trans_le hρr).le hyρ')
    have hmem : F.symm y ∈ riemannianBallOf E.terminal.metric p' ρ' := by
      rw [← himage ρ' hρ'0 (hρ'ρ.trans_le hρr)]
      exact ⟨y, hyρ', rfl⟩
    exact ⟨F.symm y, riemannianBallOf_mono E.terminal.metric p' hρ'ρ.le hmem, hcrossF y hyt⟩
  · have hr : 0 < r := lt_of_le_of_lt hρ0 hρr
    have hρR : ρ < (ρ + r) / 2 := by linarith
    have hRr : (ρ + r) / 2 < r := by linarith
    exact E.isCompact_terminal_closedBall_of_regularCrossing_of_output_buffer p' q hc' hρ0 hρR
      ((closedBall_subset_ball_O77 E.outputMetric q hRr hr).trans hball)

/-- History level (`frozen_reg_of_outgoing_O77`): sectional clause, finite scalar bound and outgoing
inclusions at every event time of `(a, u]` along the centre trace give `Reg_O77`. -/
theorem reg_of_outgoing_O77 (N : ObservedHistory.{u}) {a u : Icc (0 : ℝ) N.horizon} (hau : a ≤ u)
    {x : (N.stageAt u).Carrier}
    (X : BackwardPointTrace N (N.activeStage a) (N.activeStage u) (N.activeStage_mono hau) x)
    {r : ℝ}
    (hsec : ∀ (v : Icc (0 : ℝ) N.horizon) (hav : a ≤ v) (hvu : v ≤ u),
      ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
          (X.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hvu)) r,
        SectionalBoundedBelowAt (N.stageMetric (N.activeStage v) v) q (-(r ^ 2)⁻¹))
    (hfin : ∃ K : ℝ, ∀ (v : Icc (0 : ℝ) N.horizon) (hav : a ≤ v) (hvu : v ≤ u),
      ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
          (X.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hvu)) r,
        metricScalarAt (N.stageMetric (N.activeStage v) v) q ≤ K)
    (hout : ∀ (i : Fin N.eventCount) (hf : N.activeStage a ≤ i.castSucc)
        (hl : i.succ ≤ N.activeStage u),
      riemannianBallOf (N.event i).outputMetric
          (X.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) r ⊆
        interior (range (N.event i).oldOutput)) :
    Reg_O77 N hau X r :=
  ⟨hsec, hfin, fun i hf hl =>
    regEvent_of_outgoing_O77 (N.event i) (X.crossing i hf hl) (hout i hf hl)⟩

/-- `Reg_O77` gives the outgoing (barrier-form) inclusion of every radius `ρ ≤ r`. -/
theorem reg_outgoing_O77 {N : ObservedHistory.{u}} {a u : Icc (0 : ℝ) N.horizon} {hau : a ≤ u}
    {x : (N.stageAt u).Carrier}
    {X : BackwardPointTrace N (N.activeStage a) (N.activeStage u) (N.activeStage_mono hau) x}
    {r : ℝ} (h : Reg_O77 N hau X r) {ρ : ℝ} (hρ : ρ ≤ r) :
    ∀ (i : Fin N.eventCount) (hf : N.activeStage a ≤ i.castSucc) (hl : i.succ ≤ N.activeStage u),
      riemannianBallOf (N.event i).outputMetric
          (X.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) ρ ⊆
        interior (range (N.event i).oldOutput) := fun i hf hl =>
  (riemannianBallOf_mono _ _ hρ).trans (h.2.2 i hf hl).choose_spec.2.1

/-- Alignment with `[FROZEN] CH12-O78 Reg-input` (`frozen_regInput_of_reg_O77`). -/
theorem regInput_of_reg_O77 (H : ObservedHistory.{u}) {a top : Icc (0 : ℝ) H.horizon}
    (hat : a ≤ top) {x0 : (H.stageAt top).Carrier}
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top) (H.activeStage_mono hat) x0)
    {r0 : ℝ} (h : Reg_O77 H hat X r0) :
    (∀ ρ : ℝ, ρ ≤ r0 → ∀ (i : Fin H.eventCount) (hai : H.activeStage a ≤ i.castSucc)
        (hit : i.succ ≤ H.activeStage top),
      riemannianBallOf (H.initialMetric i.succ)
          (X.point i.succ (hai.trans i.castSucc_lt_succ.le) hit) ρ ⊆
        H.backwardSurvivorDomain i.castSucc i.succ i.castSucc_lt_succ.le) ∧
    (∃ K : ℝ, ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
        metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤ K) ∧
    (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
        SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r0 ^ 2)⁻¹)) := by
  refine ⟨fun ρ hρ i hai hit y hy => ?_, h.2.1, h.1⟩
  rw [← H.event_output i] at hy
  obtain ⟨z, hz⟩ := (H.event i).exists_terminal_regularCrossing_of_mem_interior_oldOutput y
    (reg_outgoing_O77 h hρ i hai hit hy)
  exact ⟨(BackwardPointTrace.singleton H i.succ y).prepend z.val hz⟩

end GC.LongTime.Ch12

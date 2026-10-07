import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventProtectedBalls
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData

/-!
# CH12-S140, group 1a: forward survival of a TERMINAL ball through one event

`terminal_ball_survives_S140`: if the closed output ball `B̄_out(q,R)` lies in `interior (range oldOutput)` and
`p` is a regular crossing of `q`, then every point of the closed TERMINAL ball `B̄_term(p,r)`, `r < R`, is a regular
crossing whose image lies in `B̄_out(q,r)` (the survivor chart `F.symm` is an isometry of the balls).  This is the
forward direction needed for `hsurv` (B): no clopen argument is required, only `EventProtectedBalls`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Riemannian
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
private theorem inner_symm_S140
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

end helper

theorem terminal_ball_survives_S140 {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) {p : E.incoming.terminalRegularOpen} {q : Q.Carrier} {R r : ℝ}
    (hcross : E.RegularCrossing p.val q) (hr : 0 ≤ r) (hrR : r < R)
    (hprot : riemannianClosedBallOf E.outputMetric q R ⊆ interior (range E.oldOutput)) :
    ∀ x ∈ riemannianClosedBallOf E.terminal.metric p r,
      ∃ y ∈ riemannianClosedBallOf E.outputMetric q r, E.RegularCrossing x.val y := by
  obtain ⟨F, hsource, hp, hpq, hq, hFcross, hmetric⟩ := hcross.exists_survivor_partialDiffeomorph E
  have htarget : riemannianClosedBallOf E.outputMetric q R ⊆ F.target := by
    intro y hy
    obtain ⟨x, hx⟩ := E.exists_terminal_regularCrossing_of_mem_interior_oldOutput y (hprot hy)
    have hxs : x ∈ F.source := by
      rw [hsource]
      obtain ⟨G, hGsource, hxG, _, _, _, _⟩ := hx.exists_survivor_partialDiffeomorph E
      rw [hGsource] at hxG
      exact hxG
    have heq : F x = y := E.regularCrossing_right_unique (hFcross x hxs) hx
    exact heq ▸ F.map_source hxs
  have hcpt : IsCompact (riemannianClosedBallOf E.outputMetric q R) :=
    (isClosed_le (continuous_riemannianEDist E.outputMetric q) continuous_const).isCompact
  have hinverse (y : Q.Carrier) (hy : y ∈ F.target) (v w : TangentSpace ThreeModel y) :
      E.outputMetric.inner y v w = E.terminal.metric.inner (F.symm y)
        (mfderiv ThreeModel ThreeModel F.symm y v) (mfderiv ThreeModel ThreeModel F.symm y w) :=
    inner_symm_S140
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
  intro x hx
  rw [← hclosed] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyt : y ∈ F.target := htarget (riemannianClosedBallOf_mono E.outputMetric q hrR.le hy)
  refine ⟨y, hy, ?_⟩
  have hc := hFcross (F.symm y) (F.map_target hyt)
  have h2 : F (F.symm y) = y := F.right_inv' hyt
  exact (congrArg (fun z => E.RegularCrossing (F.symm y).val z) h2).mp hc

end GC.LongTime.Ch12

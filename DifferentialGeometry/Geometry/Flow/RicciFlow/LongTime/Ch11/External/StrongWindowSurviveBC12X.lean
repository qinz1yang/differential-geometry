import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSurviveMetricC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryNeckSG
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows

/-!
# `hwin` Survive: the far window point in the pulled-in tube (C12X, S16I G3)

Main theorem of design §4 G3 (lane C), route β:
`RetainedCoreHistory.exists_spliceSurvivor_C12X`.  A window datum `d` of `(y, t)` whose standard
window coordinate lies beyond the transition radius, `transitionEnd < ‖d.x‖` (in particular every
far-early datum `D₀ + 1 ≤ ‖d.x‖` once `transitionEnd < D₀ + 1`), together with a deep backward neck
`D` of its tube `α = d.b.1.1`, yields

* a survivor pull-in `Sv : SpliceSurvivor_C12X D k d.hl` (`StrongWindowSurviveC12X`) and a survivor
  package with start `Sv.first ≤ d.j.castSucc` (`time first ≤ time j.succ − θ r²`);
* a buffer point `u ∈ Sv.U` with `Ψ u = y`, whose output-stage survivor image is the window point
  `static.window d.x`;
* its static collar coordinate `ys` (`0 < z < δ_s⁻¹`): `witness.window d.x = witness.retained ys`
  and `u` is the recentred `ys` (`recenter_chart`).

Combined with `metric_pre` / `metric_surgery` / `metric_post` (`StrongWindowSurviveMetricC12X`,
with `hscale := (records d.j).scale_eq α`) this is the Survive input of the Splice lane.

Window point ⇒ retained collar point: the window is injective and, by `hasCanonicalWindow`, covers
every cap point with coordinates of norm `≤ transitionEnd`; the static witness covers its output by
`retained ∪ cap` and glues the collar boundary `z = 0` to the cap (`boundary_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section Window

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}

/-- A window point beyond the transition radius is not a cap point. -/
private theorem s16i_window_ne_cap (S : E.PresentedStaticCap fixed D m ε b)
    (hcan : S.hasCanonicalWindow) {x : standardCapWindow D}
    (hx : StandardCap.transitionEnd < ‖x.val‖) (z : ThreeBall) :
    S.witness.window x ≠ S.witness.cap z := by
  intro hz
  obtain ⟨-, -, -, -, -, -, -, hcap⟩ := hcan
  obtain ⟨x', hx', hw⟩ := hcap z
  have h1 : S.window x' = S.window x := by
    rw [hw]
    change S.inclusion (S.witness.cap z) = S.inclusion (S.witness.window x)
    rw [hz]
  have h2 := S.window_smooth.isEmbedding.injective h1
  rw [h2] at hx'
  linarith

/-- A window point beyond the transition radius is a retained point of the open collar. -/
private theorem s16i_exists_collar (S : E.PresentedStaticCap fixed D m ε b)
    (hcan : S.hasCanonicalWindow) {x : standardCapWindow D}
    (hx : StandardCap.transitionEnd < ‖x.val‖) :
    ∃ (ys : neckBuffer S.delta) (hys : ys ∈ collarOpen_SG S.delta),
      S.witness.window x = S.witness.retained ⟨ys.1, hys.1.le, hys.2⟩ := by
  have hδ : 0 < S.delta⁻¹ := inv_pos.mpr S.neck.delta_pos
  have hcov : S.witness.window x ∈ range S.witness.retained ∪ range S.witness.cap :=
    S.witness.cover ▸ mem_univ _
  rcases hcov with ⟨c, hc⟩ | ⟨z, hz⟩
  · have hpos : 0 < c.1.2 := by
      rcases c.2.1.lt_or_eq with h | h
      · exact h
      · exfalso
        have hb := S.witness.boundary_eq (S.witness.attaching.symm c.1.1)
        rw [Diffeomorph.apply_symm_apply] at hb
        have he : (⟨(c.1.1, 0), le_rfl, inv_pos.mpr S.neck.delta_pos⟩ :
            neckRetainedCollar S.delta) = c := Subtype.ext (Prod.ext rfl h)
        rw [he, hc] at hb
        exact s16i_window_ne_cap S hcan hx _ hb.symm
    have hmem : c.1 ∈ neckBuffer S.delta :=
      ⟨by linarith [c.2.2], by linarith [c.2.2]⟩
    exact ⟨⟨c.1, hmem⟩, ⟨hpos, c.2.2⟩, hc.symm⟩
  · exact absurd hz.symm (s16i_window_ne_cap S hcan hx z)

end Window

namespace RetainedCoreHistory

/-- **Survive (hwin G3).** A window datum beyond the transition radius and a deep backward neck of
its tube give a survivor pull-in `Sv`, a survivor package from `Sv.first ≤ j.castSucc`, and a
buffer point `u` with `Ψ u = y`, whose output-stage survivor image is the window point and which is
the recentred static collar coordinate `ys` of `d.x`. -/
theorem exists_spliceSurvivor_C12X {H : RetainedCoreHistory.{u}} {p₀ p : CutoffParameters}
    {δbound ρbound : ℝ} {records : ∀ i, GeometricCutoffRecord H.toHistory i p}
    (hfam : H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records)
    {k : Fin (H.eventCount + 1)} {s : ℝ} (Gk : (H.stage k).IncomingSlab (H.time k) s)
    (hinit : Gk.flow.base.metric (H.time k) = H.initialMetric k)
    {y : (H.stage k).Carrier} {t Dw θw : ℝ} (d : H.WindowDatum_C12X records k y t Dw θw)
    (hfar : StandardCap.transitionEnd < ‖d.x.val‖) {θ : ℝ}
    (D : IncomingBackwardNeckDeep_C12X H.toHistory d.j ((records d.j).neck d.b.1.1)
      ((records d.j).nominalRadius ⟨d.b.1.1⟩) θ) :
    ∃ (Sv : H.toHistory.SpliceSurvivor_C12X D k d.hl)
      (_ : H.toHistory.SurvivorNeckPackage_C12X k Gk Sv.first Sv.hle) (u : Sv.U)
      (ys : neckBuffer ((records d.j).static d.b).delta)
      (hys : ys ∈ collarOpen_SG ((records d.j).static d.b).delta),
      (Sv.Ψ u).val = y ∧
      H.toHistory.backwardSurvivorMap Sv.first k Sv.hle d.j.succ
          (Sv.first_le.trans d.j.castSucc_lt_succ.le) d.hl (Sv.Ψ u) =
        ((records d.j).static d.b).window d.x ∧
      ((records d.j).static d.b).witness.window d.x =
        ((records d.j).static d.b).witness.retained ⟨ys.1, hys.1.le, hys.2⟩ ∧
      u.1 = ⟨(ys.1.1, (if d.b.1.2 then 1 else -1) * (1 + ys.1.2)),
        (records d.j).recenter_in_buffer d.b ys⟩ := by
  obtain ⟨Sv⟩ := ObservedHistory.nonempty_spliceSurvivor_C12X D k d.hl
  obtain ⟨P⟩ := H.toHistory.nonempty_survivorNeckPackage_C12X Gk Sv.first Sv.hle hinit
  obtain ⟨-, -, -, -, -, hcan, -, -⟩ := hfam
  obtain ⟨ys, hys, hwin⟩ := s16i_exists_collar _ (hcan d.j d.b) hfar
  let uy : neckBuffer ((records d.j).delta d.b.1.1) :=
    ⟨(ys.1.1, (if d.b.1.2 then 1 else -1) * (1 + ys.1.2)), (records d.j).recenter_in_buffer d.b ys⟩
  have hchart : ((records d.j).neck d.b.1.1).chart uy = ((records d.j).static d.b).neck.chart ys :=
    ((records d.j).recenter_chart d.b ys _).symm
  have hwx : ((records d.j).static d.b).inclusion
      (((records d.j).static d.b).witness.retained ⟨ys.1, hys.1.le, hys.2⟩) =
        ((records d.j).static d.b).window d.x :=
    (congrArg ((records d.j).static d.b).inclusion hwin).symm
  have hcross1 : (H.toHistory.event d.j).RegularCrossing
      (((records d.j).neck d.b.1.1).chart uy).1 (((records d.j).static d.b).window d.x) := by
    rw [hchart, ← hwx]
    exact collar_regularCrossing_SG (records d.j) d.b ys hys
  have hyD : y ∈ H.toHistory.backwardSurvivorDomain d.j.succ k d.hl := ⟨d.A⟩
  have hcross : (H.toHistory.event d.j).RegularCrossing (((records d.j).neck d.b.1.1).chart uy).1
      (H.toHistory.backwardSurvivorMap d.j.succ k d.hl d.j.succ le_rfl d.hl ⟨y, hyD⟩) := by
    rw [H.toHistory.backwardSurvivorMap_eq_point d.j.succ k d.hl d.j.succ le_rfl d.hl ⟨y, hyD⟩ d.A,
      d.hx]
    exact hcross1
  obtain ⟨hu, hΨ⟩ := Sv.maximal uy ⟨y, hyD⟩ hcross
  refine ⟨Sv, P, ⟨uy, hu⟩, ys, hys, hΨ, ?_, hwin, rfl⟩
  exact (H.toHistory.event d.j).regularCrossing_right_unique (Sv.crossing ⟨uy, hu⟩) hcross1

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

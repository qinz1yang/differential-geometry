import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CollarLength_S108
import DifferentialGeometry.Geometry.Metric.DistancePullback

/-!
# CH12-S108, group 1 (part 2): `hdist_S108` and `rfcB_S108`

`hdist_of_static_S108`: every retained collar point `(y, z')` with `z' ≤ 1` is within `3/(2√q)` of the
image of a cap point (the cap point whose boundary image is `(y, 0)`).  Proof: the clamped vertical
curve in the central domain, `collapse_length` (Output length ≤ h-length), the h-length bound
`collar_length_le_S108` (`≤ √(2/q) z'`, `√2 < 3/2`), and the 1-Lipschitz transfer along the
metric-preserving smooth embedding `S.inclusion`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

private local instance sigmaCompactTerminal_S108 {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) : SigmaCompactSpace E.incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      E.incoming.terminalRegularOpen.isOpen)

theorem hdist_of_static_S108 {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b) :
    ∀ c : neckRetainedCollar S.delta, c.1.2 ≤ 1 →
      ∃ z : ThreeBall, riemannianEDistOf E.outputMetric (S.inclusion (S.witness.cap z))
        (S.inclusion (S.witness.retained c)) <
          ENNReal.ofReal (3 / (2 * Real.sqrt S.neck.scale)) := by
  rintro ⟨⟨y, z'⟩, hz0, hzδ⟩ hc
  have hz0' : 0 ≤ z' := hz0
  have hzδ' : z' < S.delta⁻¹ := hzδ
  have hz1 : z' ≤ 1 := hc
  have hq := S.neck.scale_pos
  have hδ := S.neck.delta_pos
  have hδ0 : 0 < S.delta⁻¹ := inv_pos.mpr hδ
  refine ⟨sphereToThreeBall (S.witness.attaching.symm y), ?_⟩
  -- the cap point maps to the collar point `(y, 0)`
  have hbd := S.witness.boundary_eq (S.witness.attaching.symm y)
  rw [S.witness.attaching.apply_symm_apply] at hbd
  rw [hbd]
  -- the curve
  set γ := collarCurve_S108 S.delta hδ y z' hzδ' with hγ
  have hret : ∀ t (ht : t ∈ Icc 0 z'), S.witness.collapse (γ t) =
      S.witness.retained ⟨(y, t), ht.1, lt_of_le_of_lt ht.2 hzδ'⟩ := by
    intro t ht
    have h0 : 0 ≤ ((γ t).1 : NeckCylinder).2 := by
      rw [hγ, collarCurve_val_of_mem_S108 S.delta hδ y hzδ' ht]; exact ht.1
    rw [S.witness.collapse_retained (γ t) h0]
    congr 1
    exact Subtype.ext (collarCurve_val_of_mem_S108 S.delta hδ y hzδ' ht)
  have h0mem : (0 : ℝ) ∈ Icc 0 z' := ⟨le_rfl, hz0'⟩
  have hzmem : z' ∈ Icc 0 z' := ⟨hz0', le_rfl⟩
  have hlen := collar_length_le_S108 S.neck y hz0' hzδ'
  have hfin : riemannianCurveLength E.terminal.metric (fun t => S.neck.chart (γ t).1) 0 z' ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlen
  have hcont : ContinuousOn γ (Icc 0 z') :=
    (collarCurve_continuous_S108 S.delta hδ y z' hzδ').continuousOn
  have hcl := S.witness.collapse_length γ 0 z' hz0' hcont hfin
  have hedO : riemannianEDistOf S.witness.metric (S.witness.collapse (γ 0)) (S.witness.collapse (γ z'))
      ≤ riemannianCurveLength S.witness.metric (fun t => S.witness.collapse (γ t)) 0 z' :=
    riemannianEDistOf_le_riemannianCurveLength S.witness.metric
      (fun t => S.witness.collapse (γ t)) hz0'
  rw [hret 0 h0mem, hret z' hzmem] at hedO
  -- transfer along the inclusion (local isometry)
  have hloc : IsLocalDiffeomorph ThreeModel ThreeModel ∞ S.inclusion :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv S.inclusion
      S.inclusion_smooth.contMDiff
      (fun p => (S.inclusion_smooth.isImmersion.isImmersionAt p).mfderiv_injective (by simp)) rfl
  have htr := DifferentialGeometry.Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph S.witness.metric E.outputMetric S.inclusion hloc
    (c := 1) one_pos
    (fun x v => by rw [one_mul]; exact (S.inclusion_metric x v v).ge)
    (S.witness.retained ⟨(y, 0), le_rfl, hδ0⟩) (S.witness.retained ⟨(y, z'), hz0, hzδ⟩)
  rw [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at htr
  refine htr.trans_lt ?_
  refine (hedO.trans (hcl.trans hlen)).trans_lt ?_
  -- numerics: `√(2/q) z' < 3/(2√q)`
  have hsq : 0 < Real.sqrt S.neck.scale := Real.sqrt_pos.mpr hq
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hdiv : Real.sqrt (2 / S.neck.scale) = Real.sqrt 2 / Real.sqrt S.neck.scale :=
    Real.sqrt_div (by norm_num) _
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity), hdiv]
  have h1 : Real.sqrt 2 / Real.sqrt S.neck.scale * z' ≤ Real.sqrt 2 / Real.sqrt S.neck.scale :=
    mul_le_of_le_one_right (by positivity) hz1
  have h2 : Real.sqrt 2 / Real.sqrt S.neck.scale < 3 / (2 * Real.sqrt S.neck.scale) := by
    rw [div_lt_div_iff₀ hsq (by positivity)]
    nlinarith [hs2, hsq]
  exact h1.trans_lt h2

/-- `hdist` for a geometric cutoff record: the clause consumed by `rfcB_of_collar_dist_S105`. -/
theorem hdist_S108 {H : ObservedHistory.{u}} {pp : CutoffParameters} {i : Fin H.eventCount}
    (R : GeometricCutoffRecord H i pp) (b : (H.event i).RetainedBoundaryIndex) :
    ∀ c : neckRetainedCollar (R.static b).delta, c.1.2 ≤ 1 →
      ∃ z : ThreeBall, riemannianEDistOf (H.event i).outputMetric
        ((R.static b).inclusion ((R.static b).witness.cap z))
        ((R.static b).inclusion ((R.static b).witness.retained c)) <
          ENNReal.ofReal (3 / (2 * Real.sqrt (R.static b).neck.scale)) :=
  hdist_of_static_S108 (R.static b)

/-- RFC-b (collar `z' ≤ 1` ⊆ window `‖x‖ < Dc + 1`), now without the `hdist` input. -/
theorem rfcB_S108 {H : ObservedHistory.{u}} {pp : CutoffParameters}
    {i : Fin H.eventCount} (R : GeometricCutoffRecord H i pp)
    (b : (H.event i).RetainedBoundaryIndex) {Dc : ℝ}
    (hlink : linkedCanonicalWindow_O2 (R.static b)) (hacc : pp.modelAccuracy ≤ 3 / 4)
    (hDc : StandardCap.transitionEnd + 2 ≤ Dc)
    (hD : StandardCap.transitionEnd + 3 < pp.modelRadius) :
    ∀ c : neckRetainedCollar (R.static b).delta, c.1.2 ≤ 1 →
      ∃ x : standardCapWindow pp.modelRadius, ‖x.val‖ < Dc + 1 ∧
        (R.static b).window x = (R.static b).inclusion ((R.static b).witness.retained c) :=
  rfcB_of_collar_dist_S105 R b hlink hacc hDc hD (hdist_S108 R b)

end GC.LongTime.Ch12

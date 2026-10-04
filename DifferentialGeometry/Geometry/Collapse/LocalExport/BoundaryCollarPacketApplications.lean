import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCollarPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLocalization
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarPinching

/-!
# Consumers of the LC88 collar layer

* `BoundaryCollarPacket.curvatureRadius_mem_Ico`: KL 16.4's curvature-scale clause on the collar,
  `1 ≤ R < 3` at every collar point of depth at most `96` (BDY-G's kernel fed by the packet's
  pinching field).
* `BoundaryCollarPacket.zero_ball_localization`: the corrected localisation of LC88 on the packet:
  a selected ball `B(c, r)` with `d(c, ∂W) > 10` meeting the retained depth-91 collar at a point
  where the zero packet's normalized lower bound `sec ≥ -1/(60r)²` holds has `r < 1/20`, and EVERY
  point of the ball is a collar point in the band `6 < z < 93`, in the smoothed band
  `5 < η_i < 95`, with all sectional curvatures at most `-1/8` there.
* `BoundaryCollarPacket.exists_collar_cutoffs_of_hypotheses`: FC43's boundary blocks from the
  tree's boundary collapse hypotheses: for every component a smooth cutoff with values in
  `[0, 1]`, supported in the collar between depths `19` and `91`, nonzero only where the smoothed
  depth lies in `(20, 90)`, and equal to one between depths `31` and `79`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

universe u

namespace BoundaryCollarPacket

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
  {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ} (P : BoundaryCollarPacket W g K A w₀ ε) (i : Fin P.cusp.count)

/-- KL 16.4, curvature-scale clause: on the collar below depth `96`, `1 ≤ R < 3`. -/
theorem curvatureRadius_mem_Ico {p : CuspHalfSpace} (hp : p.2.val 0 ≤ 96) :
    1 ≤ curvatureRadius g ((P.cusp.collar i).toFun p) ∧
      curvatureRadius g ((P.cusp.collar i).toFun p) < 3 :=
  (P.cusp.collar i).curvatureRadius_mem_Ico (P.threshold.trans (by norm_num))
    (fun q hq _ u w => P.pinching i q hq u w) hp

/-- **LC88 localisation on the packet.** A ball `B(c, r)` with `d(c, ∂W) > 10` that meets the
depth-91 collar of component `i` at a point where `sec ≥ -1/(60r)²` has `r < 1/20`, and every point
of the ball is a collar point of depth in `(6, 93)`, smoothed depth in `(5, 95)`, and all sectional
curvatures at most `-1/8`. -/
theorem zero_ball_localization {c : W.Carrier} {r : ℝ} (hr : 0 < r) {p : CuspHalfSpace}
    (hp : p.2.val 0 ≤ 91) (hpc : (P.cusp.collar i).toFun p ∈ riemannianBallOf g c r)
    (hlower : SectionalBoundedBelowAt g ((P.cusp.collar i).toFun p) (-(1 / (60 * r) ^ 2)))
    (hc : ENNReal.ofReal boundaryBufferDistance < distanceToBoundary W g c) :
    r < 1 / 20 ∧ ∀ y ∈ riemannianBallOf g c r, ∃ q ∈ cuspDomain,
      (P.cusp.collar i).toFun q = y ∧ 6 < q.2.val 0 ∧ q.2.val 0 < 93 ∧
      5 < P.height i y ∧ P.height i y < 95 ∧
      ∀ u w : TangentSpace W.model y, metricRm04StandardAt g y u w w u ≤
        -(1 / 8) * (g.inner y u u * g.inner y w w - g.inner y u w ^ 2) := by
  have hpd : p ∈ cuspDomain := lt_of_le_of_lt hp (by norm_num [cuspDepth])
  obtain ⟨v, w, hvw⟩ := exists_carrier_gram_pos W g ((P.cusp.collar i).toFun p)
  obtain ⟨-, h20, hball⟩ := boundary_localization W g hr v w hvw hlower
    (P.pinching i p hpd v w).2 hc
  refine ⟨h20, fun y hy => ?_⟩
  have hpc' : riemannianEDistOf g ((P.cusp.collar i).toFun p) c < ENNReal.ofReal r := by
    rw [riemannianEDistOf_comm]
    exact hpc
  have hy' : riemannianEDistOf g c y < ENNReal.ofReal r := hy
  have hlt : riemannianEDistOf g ((P.cusp.collar i).toFun p) y < 1 := by
    calc riemannianEDistOf g ((P.cusp.collar i).toFun p) y
        ≤ riemannianEDistOf g ((P.cusp.collar i).toFun p) c + riemannianEDistOf g c y :=
          riemannianEDistOf_triangle g _ _ _
      _ < ENNReal.ofReal r + ENNReal.ofReal r := ENNReal.add_lt_add hpc' hy'
      _ = ENNReal.ofReal (r + r) := (ENNReal.ofReal_add hr.le hr.le).symm
      _ ≤ 1 := ENNReal.ofReal_le_one.mpr (by linarith)
  obtain ⟨q, hq, rfl, h6, h93, hη5, hη95⟩ := P.buffer i p y hp hlt (hball _ hy)
  exact ⟨q, hq, rfl, h6, h93, hη5, hη95, fun u w => (P.pinching i q hq u w).2⟩

end BoundaryCollarPacket

/-- FC43's boundary blocks from the tree's boundary collapse hypotheses (`2 ≤ K`,
`w₀ ≤ 1/6408`): for every boundary component, a smooth cutoff with values in `[0, 1]`, supported in
the collar between depths `19` and `91`, nonzero only where the smoothed depth lies in `(20, 90)`,
and equal to one between depths `31` and `79`. -/
theorem BoundaryCollarPacket.exists_collar_cutoffs_of_hypotheses {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {w₀ : ℝ}
    (h : boundaryCollapseHypotheses W g K A w₀) (hK : 2 ≤ K) (hw : w₀ ≤ 1 / 6408) :
    ∃ P : BoundaryCollarPacket W g K A w₀ 1, ∀ i : Fin P.cusp.count,
      ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (P.cutoff i) ∧ (∀ x, P.cutoff i x ∈ Icc (0 : ℝ) 1) ∧
      tsupport (P.cutoff i) ⊆
        (P.cusp.collar i).toFun '' {p : CuspHalfSpace | 19 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 91} ∧
      (∀ x, P.cutoff i x ≠ 0 → 20 < P.height i x ∧ P.height i x < 90) ∧
      ∀ p : CuspHalfSpace, 31 ≤ p.2.val 0 → p.2.val 0 ≤ 79 →
        P.cutoff i ((P.cusp.collar i).toFun p) = 1 := by
  obtain ⟨P⟩ := nonempty_of_hypotheses h hK hw one_pos le_rfl
  refine ⟨P, fun i => ⟨P.contMDiff_cutoff i, P.cutoff_mem_Icc i, ?_, fun x hx => ?_,
    fun p h31 h79 => P.cutoff_eq_one i (by linarith) (by linarith)⟩⟩
  · refine (P.tsupport_cutoff_subset i).trans ?_
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, ⟨by linarith [hp.1], by linarith [hp.2]⟩, rfl⟩
  · refine P.height_mem_of_block_ne_zero i fun h0 => hx ?_
    change (P.block i x).2 = 0
    rw [h0]
    rfl

end DifferentialGeometry.Geometry.Collapse

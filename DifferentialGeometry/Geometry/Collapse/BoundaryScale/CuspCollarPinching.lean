import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarBalls
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspHeightOnePoint
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarLocalization
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound

/-!
# Curvature scale in a pinched cusp collar (BSA01 (ii), `1 ≤ R_p < 3` — kernels)

Blueprint 207B, BSA01 (`B:7598–7611`). The sectional pinching `-1/2 ≤ sec ≤ -1/8` on the collar
part `0 ≤ z ≤ 98` (BSA01 (i), the input produced by lane FT-C) gives the curvature-scale clause:

* `CuspEmbedding.one_le_curvatureRadius_of_pinching`: lower pinching on `z ≤ 98` and `z(p) ≤ 96`
  give `1 ≤ R_{e p}` (the unit ball stays below height `98` by G-ball, and `-1/2 ≥ -1`);
* `curvatureRadius_lt_three_of_sectional_le`: all planes at a point with `sec ≤ -1/8` give
  `R < 3` (one nondegenerate plane exists in every tangent space);
* `CuspEmbedding.curvatureRadius_lt_three_of_pinching`, `CuspEmbedding.curvatureRadius_mem_Ico`:
  `1 ≤ R_{e p} < 3` for `z(p) ≤ 96` (BSA01 (ii) with `96` in place of `95`);
* `NearlyCuspidalBoundary.one_le_curvatureRadius_of_distanceToBoundary_le_ten`: `d(p, ∂W) ≤ 10`
  gives `1 ≤ R_p` (BSA01 (iii) puts `p` at height `< 11`);
* `NearlyCuspidalBoundary.curvatureRadius_le_distanceToBoundary_add_three_of_pinching`: the upper
  pinching (used at height `1` only) gives `R_p ≤ d(p, ∂W) + 3` everywhere (BSA01.c).
-/

set_option autoImplicit false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {δ : ℝ} {X : Set W.Carrier}

/-- **BSA01 (ii), `1 ≤ R_p`.** If `sec ≥ -1/2` at every collar point of height `≤ 98` and
`δ ≤ 1/100`, every collar point of height `≤ 96` has curvature scale at least `1`. -/
theorem CuspEmbedding.one_le_curvatureRadius_of_pinching (e : CuspEmbedding W g K δ X)
    (hδ : δ ≤ 1 / 100)
    (hlow : ∀ q ∈ cuspDomain, q.2.val 0 ≤ 98 → ∀ u w : TangentSpace W.model (e.toFun q),
      -(1 / 2) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2) ≤
        metricRm04StandardAt g (e.toFun q) u w w u)
    {p : CuspHalfSpace} (hp : p.2.val 0 ≤ 96) : 1 ≤ curvatureRadius g (e.toFun p) := by
  refine one_le_curvatureRadius_of_sectional_ball g (e.toFun p) fun y hy => ?_
  obtain ⟨q, hq, rfl⟩ := e.riemannianBallOf_subset_image_height_lt hδ hp le_rfl hy
  have hqd : q ∈ cuspDomain := lt_trans (show q.2.val 0 < 98 from hq) (by norm_num [cuspDepth])
  intro v w
  have h := hlow q hqd (le_of_lt hq) v w
  have hcs := gInner_sq_le_mul g (e.toFun q) v w
  linarith

/-- All planes at a point with sectional curvature `≤ -1/8` give curvature scale `< 3`. -/
theorem curvatureRadius_lt_three_of_sectional_le (g : SmoothRiemannianMetric W.model W.Carrier)
    (x : W.Carrier)
    (hup : ∀ u w : TangentSpace W.model x, metricRm04StandardAt g x u w w u ≤
      -(1 / 8) * (g.inner x u u * g.inner x w w - g.inner x u w ^ 2)) :
    curvatureRadius g x < 3 := by
  obtain ⟨v, w, hgram⟩ := exists_carrier_gram_pos W g x
  exact curvatureRadius_lt_three_of_negative_plane g x v w hgram (hup v w)

/-- **BSA01 (ii), `R_p < 3`.** If `sec ≤ -1/8` at every collar point of height `≤ 98`, every such
point has curvature scale `< 3`. -/
theorem CuspEmbedding.curvatureRadius_lt_three_of_pinching (e : CuspEmbedding W g K δ X)
    (hup : ∀ q ∈ cuspDomain, q.2.val 0 ≤ 98 → ∀ u w : TangentSpace W.model (e.toFun q),
      metricRm04StandardAt g (e.toFun q) u w w u ≤
        -(1 / 8) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2))
    {p : CuspHalfSpace} (hpd : p ∈ cuspDomain) (hp : p.2.val 0 ≤ 98) :
    curvatureRadius g (e.toFun p) < 3 :=
  curvatureRadius_lt_three_of_sectional_le g _ (hup p hpd hp)

/-- **BSA01 (ii), curvature-scale clause.** Under the pinching `-1/2 ≤ sec ≤ -1/8` on the collar
part `z ≤ 98` and `δ ≤ 1/100`, every collar point of height `≤ 96` has `1 ≤ R < 3`. -/
theorem CuspEmbedding.curvatureRadius_mem_Ico (e : CuspEmbedding W g K δ X) (hδ : δ ≤ 1 / 100)
    (hpinch : ∀ q ∈ cuspDomain, q.2.val 0 ≤ 98 → ∀ u w : TangentSpace W.model (e.toFun q),
      -(1 / 2) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2) ≤
          metricRm04StandardAt g (e.toFun q) u w w u ∧
        metricRm04StandardAt g (e.toFun q) u w w u ≤
          -(1 / 8) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2))
    {p : CuspHalfSpace} (hp : p.2.val 0 ≤ 96) :
    1 ≤ curvatureRadius g (e.toFun p) ∧ curvatureRadius g (e.toFun p) < 3 := by
  have hpd : p ∈ cuspDomain := lt_of_le_of_lt hp (by norm_num [cuspDepth])
  exact ⟨e.one_le_curvatureRadius_of_pinching hδ (fun q hq hz u w => (hpinch q hq hz u w).1) hp,
    e.curvatureRadius_lt_three_of_pinching (fun q hq hz u w => (hpinch q hq hz u w).2) hpd
      (by linarith)⟩

/-- **BSA01 (ii)+(iii).** Under the lower pinching on every collar and `δ ≤ 1/100`, every point
within `10` of `∂W` has curvature scale at least `1`. -/
theorem NearlyCuspidalBoundary.one_le_curvatureRadius_of_distanceToBoundary_le_ten
    (B : NearlyCuspidalBoundary W g K δ) (hδ : δ ≤ 1 / 100)
    (hlow : ∀ (i : Fin B.count), ∀ q ∈ cuspDomain, q.2.val 0 ≤ 98 →
      ∀ u w : TangentSpace W.model ((B.collar i).toFun q),
        -(1 / 2) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2) ≤
          metricRm04StandardAt g ((B.collar i).toFun q) u w w u)
    {p : W.Carrier} (hp : distanceToBoundary W g p ≤ ENNReal.ofReal 10) :
    1 ≤ curvatureRadius g p := by
  obtain ⟨i, x, z, hz0, hz, rfl⟩ := B.exists_collar_height_lt_eleven hδ hp
  refine (B.collar i).one_le_curvatureRadius_of_pinching hδ (hlow i) ?_
  change (halfSpaceOneLift z).val 0 ≤ 96
  rw [halfSpaceOneLift_val_zero, max_eq_left hz0]
  linarith

/-- The height-one collar points lie in the collar part `z ≤ 98`. -/
theorem halfSpaceOneLift_one_mem_cuspDomain (x : Torus) :
    ((x, halfSpaceOneLift 1) : CuspHalfSpace) ∈ cuspDomain ∧
      ((x, halfSpaceOneLift 1) : CuspHalfSpace).2.val 0 ≤ 98 := by
  have h1 : ((x, halfSpaceOneLift 1) : CuspHalfSpace).2.val 0 = 1 := by
    change (halfSpaceOneLift 1).val 0 = 1
    rw [halfSpaceOneLift_val_zero, max_eq_left zero_le_one]
  refine ⟨?_, by rw [h1]; norm_num⟩
  change ((x, halfSpaceOneLift 1) : CuspHalfSpace).2.val 0 < cuspDepth
  rw [h1]
  norm_num [cuspDepth]

/-- **BSA01.c from the pinching.** Under the upper pinching on every collar and `δ ≤ 1/100`,
`R_p ≤ d(p, ∂W) + 3` at every point. -/
theorem NearlyCuspidalBoundary.curvatureRadius_le_distanceToBoundary_add_three_of_pinching
    (B : NearlyCuspidalBoundary W g K δ) (hδ : δ ≤ 1 / 100)
    (hup : ∀ (i : Fin B.count), ∀ q ∈ cuspDomain, q.2.val 0 ≤ 98 →
      ∀ u w : TangentSpace W.model ((B.collar i).toFun q),
        metricRm04StandardAt g ((B.collar i).toFun q) u w w u ≤
          -(1 / 8) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2))
    (p : W.Carrier) :
    curvatureRadius g p ≤ distanceToBoundary W g p + ENNReal.ofReal 3 :=
  B.curvatureRadius_le_distanceToBoundary_add_three hδ (fun i x u w =>
    hup i _ (halfSpaceOneLift_one_mem_cuspDomain x).1 (halfSpaceOneLift_one_mem_cuspDomain x).2
      u w) p

end DifferentialGeometry.Geometry.Collapse

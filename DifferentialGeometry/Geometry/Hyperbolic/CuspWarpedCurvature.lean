import DifferentialGeometry.Geometry.Hyperbolic.Cusp
import DifferentialGeometry.Geometry.Curvature.WarpedProduct.ExponentialRealBase
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.PartialDiffeomorph
import DifferentialGeometry.Geometry.Curvature.ContinuousEvaluation
import DifferentialGeometry.Geometry.Metric.WarpedProduct
import DifferentialGeometry.Geometry.Metric.Evaluation
import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.InteriorBoundary

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.Manifold
open GC.Endpoint Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Hyperbolic

local instance cuspWarpedCircleHausdorff : T2Space Circle := inferInstance

local instance cuspWarpedTorusHausdorff : T2Space Torus :=
  inferInstanceAs (T2Space (Circle × Circle))

local instance cuspWarpedHalfSpaceHausdorff : T2Space (EuclideanHalfSpace 1) :=
  inferInstanceAs (T2Space {x : EuclideanSpace ℝ (Fin 1) | 0 ≤ x 0})

local instance cuspWarpedHalfSpaceProdHausdorff : T2Space CuspHalfSpace :=
  inferInstanceAs (T2Space (Torus × EuclideanHalfSpace 1))

private abbrev realBaseCuspModel := 𝓘(ℝ, ℝ).prod torusModel

private def positiveHeightDiffeomorph :
    PartialDiffeomorph halfCollarModel realBaseCuspModel CuspHalfSpace (ℝ × Torus) ∞ where
  toFun p := (p.2.val 0, p.1)
  invFun q := (q.2, halfSpaceOneLift q.1)
  source := {p | 0 < p.2.val 0}
  target := {q | 0 < q.1}
  map_source' := fun _ hp => hp
  map_target' := fun q hq => halfSpaceOneInteriorDiffeomorph.map_source hq
  left_inv' := fun p hp =>
    Prod.ext rfl (halfSpaceOneInteriorDiffeomorph.right_inv hp)
  right_inv' := fun q hq =>
    Prod.ext (halfSpaceOneInteriorDiffeomorph.left_inv hq) rfl
  open_source := isOpen_lt continuous_const
    ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
  open_target := isOpen_lt continuous_const continuous_fst
  contMDiffOn_toFun :=
    ((contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd).prodMk
      contMDiff_fst).contMDiffOn
  contMDiffOn_invFun := contMDiffOn_snd.prodMk
    (halfSpaceOneInteriorDiffeomorph.contMDiffOn_toFun.comp contMDiffOn_fst
      (fun _ hq => hq))

set_option backward.isDefEq.respectTransparency false in
private theorem mfderiv_positiveHeightDiffeomorph (p : CuspHalfSpace)
    (v : TangentSpace halfCollarModel p) :
    mfderiv halfCollarModel realBaseCuspModel positiveHeightDiffeomorph p v =
      (v.2 0, v.1) := by
  have hc := hasMFDerivAt_halfSpaceOneCoordinate p.2
  have hheight : MDifferentiableAt halfCollarModel 𝓘(ℝ, ℝ)
      (fun q : CuspHalfSpace => q.2.val 0) p :=
    hc.mdifferentiableAt.comp p mdifferentiableAt_snd
  change mfderiv halfCollarModel realBaseCuspModel
    (fun q : CuspHalfSpace => (q.2.val 0, q.1)) p v = _
  have hcomp := mfderiv_comp p hc.mdifferentiableAt
    (mdifferentiableAt_snd (I := torusModel) (I' := 𝓡∂ 1) (x := p))
  rw [mfderiv_prodMk hheight mdifferentiableAt_fst]
  change ((mfderiv halfCollarModel 𝓘(ℝ, ℝ) ((fun t : EuclideanHalfSpace 1 => t.val 0) ∘ Prod.snd) p).prod
    (mfderiv halfCollarModel torusModel Prod.fst p)) v = _
  rw [hcomp, hc.mfderiv, mfderiv_snd, mfderiv_fst]
  rfl

private theorem exp_neg_half_sq (r : ℝ) : Real.exp (-r / 2) ^ 2 = Real.exp (-r) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem cusp_curvature_positiveHeight (H : HyperbolicCusp)
    (p : CuspHalfSpace) (hp : 0 < p.2.val 0)
    (v w : TangentSpace halfCollarModel p) :
    metricRm04StandardAt H.metric p v w w v =
      -(1 / 4 : ℝ) * (H.metric.inner p v v * H.metric.inner p w w -
        H.metric.inner p v w ^ 2) := by
  have hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun r : ℝ => Real.exp (-r / 2)) :=
    (Real.contDiff_exp.comp (contDiff_id.neg.div_const 2)).contMDiff
  let G : SmoothRiemannianMetric realBaseCuspModel (ℝ × Torus) :=
    (euclideanMetric (E := ℝ)).warpedProduct H.torusMetric
      (fun r => Real.exp (-r / 2)) hf (fun r => Real.exp_pos (-r / 2))
  have hG (q : ℝ × Torus) (a b : TangentSpace realBaseCuspModel q) :
      G.inner q a b = a.1 * b.1 + Real.exp (-q.1) * H.torusMetric.inner q.2 a.2 b.2 := by
    rw [SmoothRiemannianMetric.warpedProduct_inner, euclideanMetric_inner,
      exp_neg_half_sq]
    congr 1
    exact mul_comm _ _
  let U : TopologicalSpace.Opens CuspHalfSpace :=
    ⟨positiveHeightDiffeomorph.source, positiveHeightDiffeomorph.open_source⟩
  have hmet (q : U) (a b : TangentSpace halfCollarModel q) :
      H.metric.inner q.val a b =
        G.inner (positiveHeightDiffeomorph q.val)
          (mfderiv halfCollarModel realBaseCuspModel positiveHeightDiffeomorph q.val a)
          (mfderiv halfCollarModel realBaseCuspModel positiveHeightDiffeomorph q.val b) := by
    rw [hG, mfderiv_positiveHeightDiffeomorph, mfderiv_positiveHeightDiffeomorph]
    exact H.metric_formula q.val a b
  let q : U := ⟨p, hp⟩
  have hR := metricRm04StandardAt_eq_of_partialDiffeomorph_restriction
    positiveHeightDiffeomorph U (fun _ hy => hy) H.metric G hmet q v w w v
  rw [hR, metricRm04StandardAt_of_exponentialRealBase_inner_of_flat
    G H.torusMetric hG H.torus_flat]
  rw [← hmet q v v, ← hmet q w w, ← hmet q v w]

/-- The original cusp metric has sectional curvature `-1/4`, including at
height zero. This derives the identity from its metric formula and the flat
torus fiber, without using the inherited cusp curvature admission. -/
theorem HyperbolicCusp.metricRm04StandardAt_eq_neg_quarter_gram (H : HyperbolicCusp)
    (p : CuspHalfSpace) (v w : TangentSpace halfCollarModel p) :
    metricRm04StandardAt H.metric p v w w v =
      -(1 / 4 : ℝ) * (H.metric.inner p v v * H.metric.inner p w w -
        H.metric.inner p v w ^ 2) := by
  obtain ⟨V, hV⟩ := ContMDiffSection.exists_eq_at (I := halfCollarModel)
    (F := (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) (V := TangentSpace halfCollarModel)
    (n := (⊤ : ℕ∞)) p v
  obtain ⟨W, hW⟩ := ContMDiffSection.exists_eq_at (I := halfCollarModel)
    (F := (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) (V := TangentSpace halfCollarModel)
    (n := (⊤ : ℕ∞)) p w
  let R : CuspHalfSpace → ℝ := fun q =>
    metricRm04StandardAt H.metric q (V q) (W q) (W q) (V q)
  let Gram : CuspHalfSpace → ℝ := fun q =>
    H.metric.inner q (V q) (V q) * H.metric.inner q (W q) (W q) -
      H.metric.inner q (V q) (W q) ^ 2
  have hR : Continuous R :=
    DifferentialGeometry.Geometry.continuous_sectional_contraction H.metric id continuous_id
      V W V.contMDiff.continuous W.contMDiff.continuous
  have hGram : Continuous Gram :=
    (((contMDiff_metric_inner H.metric V V).continuous.mul
      (contMDiff_metric_inner H.metric W W).continuous).sub
        ((contMDiff_metric_inner H.metric V W).continuous.pow 2))
  have hinterior : EqOn R (fun q => -(1 / 4 : ℝ) * Gram q)
      (halfCollarModel.interior CuspHalfSpace) := by
    intro q hq
    change q ∈ (torusModel.prod (𝓡∂ 1)).interior
      (Torus × EuclideanHalfSpace 1) at hq
    rw [ModelWithCorners.interior_prod] at hq
    have ht : (𝓡∂ 1).IsInteriorPoint q.2 := hq.2
    have hpos : 0 < q.2.val 0 := by
      simpa only [ModelWithCorners.IsInteriorPoint, extChartAt_self_apply,
        interior_range_modelWithCornersEuclideanHalfSpace, mem_setOf_eq,
        modelWithCornersEuclideanHalfSpace_apply] using ht
    exact cusp_curvature_positiveHeight H q hpos (V q) (W q)
  have hlimit := hinterior.closure hR (continuous_const.mul hGram)
    ((ModelWithCorners.dense_interior halfCollarModel) p)
  simpa only [R, Gram, hV, hW] using hlimit

end DifferentialGeometry.Geometry.Hyperbolic

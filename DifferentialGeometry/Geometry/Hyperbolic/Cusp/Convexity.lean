/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Geometry.Metric.WarpedProduct
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Operator.GradientPullback
import DifferentialGeometry.Geometry.Operator.Hessian.MetricClosure
import DifferentialGeometry.Geometry.Operator.Hessian.WarpedProduct
import DifferentialGeometry.Geometry.Operator.Hessian.Collar
import DifferentialGeometry.Geometry.Operator.Pullback
import DifferentialGeometry.Topology.Manifold.HalfCollarExtension
import DifferentialGeometry.Topology.Manifold.HalfLine

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.VectorField
open scoped Manifold ContDiff



open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Topology

namespace DifferentialGeometry.Geometry.Hyperbolic.CuspConvexity


section Model
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem smooth_warp : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞
    (fun r : ℝ => Real.exp (-r / 2)) :=
  Real.contDiff_exp.contMDiff.comp (contMDiff_id.neg.div_const 2)

/-- The canonical signed model metric, constructed from the actual base metric. -/
private def signedModelMetric (h : SmoothRiemannianMetric I M) :
    SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (M × ℝ) :=
  Diffeomorph.pullbackMetricCross
    ((euclideanMetric (E := ℝ)).warpedProduct h (fun r => Real.exp (-r / 2))
      smooth_warp (fun _ => Real.exp_pos _))
    (Diffeomorph.prodComm I 𝓘(ℝ) M ℝ ∞)

private theorem signedModelMetric_inner (h : SmoothRiemannianMetric I M)
    (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ)) p) :
    (signedModelMetric h).inner p v w =
      v.2 * w.2 + Real.exp (-p.2) * h.inner p.1 v.1 w.1 := by
  have hd : (mfderiv (I.prod 𝓘(ℝ)) (𝓘(ℝ).prod I)
      (Diffeomorph.prodComm I 𝓘(ℝ) M ℝ ∞) p : E × ℝ →L[ℝ] ℝ × E) =
      (ContinuousLinearMap.snd ℝ E ℝ).prod (ContinuousLinearMap.fst ℝ E ℝ) := by
    exact (mfderiv_prodMk mdifferentiableAt_snd mdifferentiableAt_fst).trans (by
      rw [mfderiv_snd, mfderiv_fst]
      rfl)
  rw [signedModelMetric, Diffeomorph.pullbackMetricCross_inner, hd,
    SmoothRiemannianMetric.warpedProduct_inner]
  change inner ℝ v.2 w.2 + Real.exp (-p.2 / 2) ^ 2 * h.inner p.1 v.1 w.1 = _
  rw [Real.inner_apply]
  have he : Real.exp (-p.2 / 2) ^ 2 = Real.exp (-p.2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]

end Model

section ActualCollar
variable (H : FiniteVolumeHyperbolicModel) (T : HyperbolicTruncation H) (i : Fin T.count)
  (d : SmoothTwoSidedCollar torusModel (𝓡 3) (fun s => T.cuspMap i (s, halfZero)))

/-- The literal signed source strip of the actual collar. -/
private def sourceStrip : TopologicalSpace.Opens (Torus × ℝ) :=
  ⟨{p | p.2 ∈ Ioo (-d.radius) d.radius},
    isOpen_Ioo.preimage continuous_snd⟩

private def stripCoordinates :
    (sourceStrip H T i d) ≃ₘ⟮signedCollarModel, signedCollarModel⟯
      (Torus × symmetricOpenInterval d.radius) where
  toFun p := (p.val.1, ⟨p.val.2, p.property⟩)
  invFun p := ⟨(p.1, p.2.val), p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    apply (contMDiff_fst.comp contMDiff_subtype_val).prodMk
    intro p
    exact codRestr_contMDiffAt
      (V := symmetricOpenInterval d.radius)
      (f := fun q : sourceStrip H T i d => q.val.2)
      (fun q => q.property)
      ((contMDiff_snd.comp contMDiff_subtype_val).contMDiffAt)
  contMDiff_invFun := by
    intro p
    exact codRestr_contMDiffAt (V := sourceStrip H T i d)
      (f := fun q : Torus × symmetricOpenInterval d.radius => (q.1, q.2.val))
      (fun q => q.2.property)
      ((contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)).contMDiffAt)

/-- Same actual collar, expressed on the open subset of the signed cylinder. -/
private def collarCoordinates :
    (sourceStrip H T i d) ≃ₘ⟮signedCollarModel, 𝓡 3⟯ d.neighborhood :=
  (stripCoordinates H T i d).trans d.toDiffeomorph

/-- The actual ambient defining height is read from the inverse of that same collar. -/
def collarHeight (q : d.neighborhood) : ℝ := (d.toDiffeomorph.symm q).2.val

def collarRho (q : d.neighborhood) : ℝ := Real.exp (-collarHeight H T i d q) - 1

theorem collarHeight_smooth : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ (collarHeight H T i d) :=
  (contMDiff_subtype_val.comp contMDiff_snd).comp d.toDiffeomorph.symm.contMDiff

theorem collarRho_smooth : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ (collarRho H T i d) :=
  (Real.contDiff_exp.contMDiff.comp (collarHeight_smooth H T i d).neg).sub contMDiff_const

private theorem collarHeight_coordinates (p : sourceStrip H T i d) :
    collarHeight H T i d (collarCoordinates H T i d p) = p.val.2 := by
  change (d.toDiffeomorph.symm (d.toDiffeomorph (stripCoordinates H T i d p))).2.val = _
  rw [Diffeomorph.symm_apply_apply]
  rfl

private theorem collarRho_coordinates (p : sourceStrip H T i d) :
    collarRho H T i d (collarCoordinates H T i d p) = Real.exp (-p.val.2) - 1 := by
  rw [collarRho, collarHeight_coordinates]

private def positiveStrip : TopologicalSpace.Opens (sourceStrip H T i d) :=
  ⟨{p | 0 < p.val.2},
    isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)⟩

private theorem mem_closure_positiveStrip (p : sourceStrip H T i d) (hp : 0 ≤ p.val.2) :
    p ∈ closure (positiveStrip H T i d : Set (sourceStrip H T i d)) := by
  have hopen : IsOpenMap (fun q : sourceStrip H T i d => q.val.2) :=
    isOpenMap_snd.comp (sourceStrip H T i d).isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  apply hopen.preimage_closure_subset_closure_preimage (s := Ioi (0 : ℝ))
  simpa only [closure_Ioi, mem_preimage, mem_Ici] using hp


private abbrev TorusE := EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)

private theorem halfSpaceOneLift_eq_halfPoint {r : ℝ} (hr : 0 ≤ r) :
    halfSpaceOneLift r = halfPoint r hr := by
  apply Subtype.ext
  apply (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).injective
  change max r 0 = r
  exact max_eq_left hr

private theorem mfderiv_halfSpaceOneLift {r : ℝ} (hr : 0 < r) :
    (mfderiv 𝓘(ℝ) (𝓡∂ 1) halfSpaceOneLift r : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) =
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm.toContinuousLinearMap := by
  let L := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let D : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    mfderiv 𝓘(ℝ) (𝓡∂ 1) halfSpaceOneLift r
  have hsm : MDifferentiableAt 𝓘(ℝ) (𝓡∂ 1) halfSpaceOneLift r :=
    halfSpaceOneInteriorDiffeomorph.mdifferentiableAt (by simp) hr
  have heq : (fun s : ℝ => (halfSpaceOneLift s).val 0) =ᶠ[𝓝 r] id := by
    filter_upwards [eventually_gt_nhds hr] with s hs
    change max s 0 = s
    exact max_eq_left hs.le
  have hc := mfderiv_comp r
    (hasMFDerivAt_halfSpaceOneCoordinate (halfSpaceOneLift r)).mdifferentiableAt hsm
  rw [(hasMFDerivAt_halfSpaceOneCoordinate (halfSpaceOneLift r)).mfderiv] at hc
  have hD : L.toContinuousLinearMap.comp D = ContinuousLinearMap.id ℝ ℝ :=
    hc.symm.trans (heq.mfderiv_eq.trans (mfderiv_id (I := 𝓘(ℝ)) (x := r)))
  change D = L.symm.toContinuousLinearMap
  apply ContinuousLinearMap.ext
  intro a
  apply L.injective
  change L (D a) = L (L.symm a)
  rw [L.apply_symm_apply]
  exact congrArg (fun P : ℝ →L[ℝ] ℝ => P a) hD

private def actualPullbackMetric : SmoothRiemannianMetric signedCollarModel (sourceStrip H T i d) :=
  Diffeomorph.pullbackMetricCross (H.metric.restrictOpen d.neighborhood)
    (collarCoordinates H T i d)

/-- The collar's actual metric formula is derived only on the genuine positive
half-strip, from the original cusp map and the original cusp isometry. -/
private theorem actualPullbackMetric_inner_pos
    (heq : ∀ (p : Torus × symmetricOpenInterval d.radius) (hp : 0 ≤ p.2.val),
      d.toFun p = T.cuspMap i (p.1, halfPoint p.2.val hp))
    (p : sourceStrip H T i d) (hp : 0 < p.val.2)
    (v w : TangentSpace signedCollarModel p) :
    (actualPullbackMetric H T i d).inner p v w =
      v.2 * w.2 + Real.exp (-p.val.2) * (T.cusp i).torusMetric.inner p.val.1 v.1 w.1 := by
  let Φ := collarCoordinates H T i d
  let L : Torus × ℝ → CuspHalfSpace := Prod.map id halfSpaceOneLift
  let F : sourceStrip H T i d → H.Carrier := fun q => Φ q
  let A : TorusE × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv signedCollarModel (𝓡 3) F p
  let B : TorusE × EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv halfCollarModel (𝓡 3) (T.cuspMap i) (L p.val)
  let R : TorusE × ℝ →L[ℝ] TorusE × EuclideanSpace ℝ (Fin 1) :=
    (ContinuousLinearMap.id ℝ TorusE).prodMap
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm.toContinuousLinearMap
  have hL : MDifferentiableAt signedCollarModel halfCollarModel L p.val :=
    mdifferentiableAt_id.prodMap
      (halfSpaceOneInteriorDiffeomorph.mdifferentiableAt (by simp) hp)
  have hDL : (mfderiv signedCollarModel halfCollarModel L p.val :
      TorusE × ℝ →L[ℝ] TorusE × EuclideanSpace ℝ (Fin 1)) = R := by
    have hhalf : MDifferentiableAt 𝓘(ℝ) (𝓡∂ 1) halfSpaceOneLift p.val.2 :=
      halfSpaceOneInteriorDiffeomorph.mdifferentiableAt (by simp) hp
    have hh : (mfderiv signedCollarModel halfCollarModel L p.val :
        TorusE × ℝ →L[ℝ] TorusE × EuclideanSpace ℝ (Fin 1)) =
        (mfderiv torusModel torusModel id p.val.1 : TorusE →L[ℝ] TorusE).prodMap
          (mfderiv 𝓘(ℝ) (𝓡∂ 1) halfSpaceOneLift p.val.2 :
            ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) :=
      mfderiv_prodMap (p := p.val) (f := id) (g := halfSpaceOneLift)
        mdifferentiableAt_id hhalf
    exact hh.trans (congrArg₂
      (fun (P : TorusE →L[ℝ] TorusE) (Q : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) =>
        P.prodMap Q) (mfderiv_id (I := torusModel) (x := p.val.1))
      (mfderiv_halfSpaceOneLift hp))
  have hnear : F =ᶠ[𝓝 p] fun q : sourceStrip H T i d => T.cuspMap i (L q.val) := by
    filter_upwards [(positiveStrip H T i d).isOpen.mem_nhds hp] with q hq
    change d.toFun (q.val.1, ⟨q.val.2, q.property⟩) = _
    rw [heq _ hq.le]
    exact congrArg (T.cuspMap i) (Prod.ext rfl (halfSpaceOneLift_eq_halfPoint hq.le).symm)
  have hA : A = B.comp R := by
    have hh : A = mfderiv signedCollarModel (𝓡 3)
        (fun q : sourceStrip H T i d => (T.cuspMap i ∘ L) q.val) p := hnear.mfderiv_eq
    rw [DifferentialGeometry.mfderiv_restrict_open,
      mfderiv_comp p.val ((T.cuspEmbedding i).contMDiff.mdifferentiable (by simp) _) hL,
      hDL] at hh
    exact hh
  have hΦ : (mfderiv signedCollarModel (𝓡 3) Φ p :
      TorusE × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3)) = A :=
    (DifferentialGeometry.mfderiv_subtypeVal_comp (U := d.neighborhood) Φ p).symm
  have hpF : F p = T.cuspMap i (L p.val) := hnear.eq_of_nhds
  let C : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    H.metric.inner (T.cuspMap i (L p.val))
  let v₀ : TorusE × ℝ := v
  let w₀ : TorusE × ℝ := w
  have hmetric : (actualPullbackMetric H T i d).inner p v w = C (A v₀) (A w₀) := by
    rw [actualPullbackMetric, Diffeomorph.pullbackMetricCross_inner, hΦ]
    change H.metric.inner (F p) (A v₀) (A w₀) = _
    rw [hpF]
    rfl
  have hisom : C (B (R v₀)) (B (R w₀)) =
      (T.cusp i).metric.inner (L p.val) (R v₀) (R w₀) :=
    T.cuspIsometry i (L p.val) (R v₀) (R w₀)
  have hformula : (T.cusp i).metric.inner (L p.val) (R v₀) (R w₀) =
      v₀.2 * w₀.2 + Real.exp (-p.val.2) *
        (T.cusp i).torusMetric.inner p.val.1 v₀.1 w₀.1 := by
    calc
      _ = (R v₀).2 0 * (R w₀).2 0 + Real.exp (-(L p.val).2.val 0) *
          (T.cusp i).torusMetric.inner (L p.val).1 (R v₀).1 (R w₀).1 :=
        (T.cusp i).metric_formula (L p.val) (R v₀) (R w₀)
      _ = _ := by
        change v₀.2 * w₀.2 + Real.exp (-max p.val.2 0) *
          (T.cusp i).torusMetric.inner p.val.1 v₀.1 w₀.1 = _
        rw [max_eq_left hp.le]
  rw [hmetric, hA]
  exact hisom.trans hformula


private theorem actualPullback_barrier_data
    (heq : ∀ (p : Torus × symmetricOpenInterval d.radius) (hp : 0 ≤ p.2.val),
      d.toFun p = T.cuspMap i (p.1, halfPoint p.2.val hp))
    (p : sourceStrip H T i d) (hp : 0 ≤ p.val.2) :
    (∀ v w : TangentSpace signedCollarModel p,
      hessFun (actualPullbackMetric H T i d)
        (fun q : sourceStrip H T i d => Real.exp (-q.val.2) - 1) p v w =
      Real.exp (-p.val.2) / 2 * ((actualPullbackMetric H T i d).inner p v w + v.2 * w.2)) ∧
    normGradSqFun (actualPullbackMetric H T i d)
      (fun q : sourceStrip H T i d => Real.exp (-q.val.2) - 1) p =
        Real.exp (-2 * p.val.2) := by
  let U := sourceStrip H T i d
  let G := signedModelMetric (T.cusp i).torusMetric
  let g := G.restrictOpen U
  let h := actualPullbackMetric H T i d
  let F : Torus × ℝ → ℝ := fun q => Real.exp (-q.2) - 1
  let f : U → ℝ := fun q => F q.val
  have hF : ContMDiff signedCollarModel 𝓘(ℝ) ∞ F :=
    (Real.contDiff_exp.contMDiff.comp contMDiff_snd.neg).sub contMDiff_const
  have hf : ContMDiff signedCollarModel 𝓘(ℝ) ∞ f := hF.comp contMDiff_subtype_val
  have heq' (q : U) (hq : q ∈ positiveStrip H T i d)
      (v w : TangentSpace signedCollarModel q) : h.inner q v w = g.inner q v w :=
    (actualPullbackMetric_inner_pos H T i d heq q hq v w).trans
      (signedModelMetric_inner (T.cusp i).torusMetric q.val v w).symm
  have hcl := mem_closure_positiveStrip H T i d p hp
  have hzero := metricCovDeriv_eq_of_eqOn_open_closure h g g
    (positiveStrip H T i d) heq' p hcl 0
  change Tensor0SBundle.metricTensorField h p = Tensor0SBundle.metricTensorField g p at hzero
  have hpoint (v w : TangentSpace signedCollarModel p) : h.inner p v w = g.inner p v w := by
    have hvw := congrArg (fun A => A (fun j : Fin 2 => if j = 0 then v else w)) hzero
    simpa [Tensor0SBundle.metricTensorField_apply] using hvw
  constructor
  · intro v w
    have hclose := hessFun_eq_of_metric_eqOn_open_closure g h
      (positiveStrip H T i d) heq' f hf p hcl v w
    have hres := hessFun_restrictOpen G U (⟨F, hF⟩ : C^∞⟮signedCollarModel, Torus × ℝ; ℝ⟯) p v w
    rw [DifferentialGeometry.mfderiv_subtype_val_apply,
      DifferentialGeometry.mfderiv_subtype_val_apply] at hres
    have hmodel := Operator.ExponentialWarpedProduct.hess_exp_neg_height_sub_one
      (T.cusp i).torusMetric G (signedModelMetric_inner (T.cusp i).torusMetric) p.val v w
    have hh := hclose.trans (hres.trans hmodel)
    change hessFun h f p v w = Real.exp (-p.val.2) / 2 * (g.inner p v w + v.2 * w.2) at hh
    rw [← hpoint] at hh
    exact hh
  · have hgrad : gradFun h f p = gradFun g f p := by
      apply DifferentialGeometry.Geometry.Curvature.SmoothRiemannianMetric.eq_of_inner_eq_gen g
      intro v
      calc
        g.inner p (gradFun h f p) v = h.inner p (gradFun h f p) v := (hpoint _ _).symm
        _ = mvfderiv signedCollarModel f p v := inner_gradFun h f p v
        _ = g.inner p (gradFun g f p) v := (inner_gradFun g f p v).symm
    have hres := gradientFun_restrictOpen G U F p (hF.mdifferentiableAt (by simp))
    simp only [gradient_eq_gradFun, Curvature.restrictOpenTangentField_apply] at hres
    change h.inner p (gradFun h f p) (gradFun h f p) = _
    rw [hgrad, hpoint]
    change G.inner p.val (gradFun g f p) (gradFun g f p) = _
    rw [hres]
    exact Operator.ExponentialWarpedProduct.inner_grad_exp_neg_height_sub_one
      (T.cusp i).torusMetric G (signedModelMetric_inner (T.cusp i).torusMetric) p.val

/-- The exact Hessian and gradient norm of the original cusp-height profile on
the actual ambient collar, including the original boundary. The metric and
function are those of the same collar; no halfspace Boundaryless instance is used. -/
theorem actual_cusp_barrier_data
    (heq : ∀ (p : Torus × symmetricOpenInterval d.radius) (hp : 0 ≤ p.2.val),
      d.toFun p = T.cuspMap i (p.1, halfPoint p.2.val hp))
    (q : d.neighborhood) (hq : 0 ≤ collarHeight H T i d q) :
    (∀ v w : TangentSpace (𝓡 3) q,
      hessFun (H.metric.restrictOpen d.neighborhood) (collarRho H T i d) q v w =
        Real.exp (-collarHeight H T i d q) / 2 *
          ((H.metric.restrictOpen d.neighborhood).inner q v w +
            mvfderiv (𝓡 3) (collarHeight H T i d) q v *
              mvfderiv (𝓡 3) (collarHeight H T i d) q w)) ∧
    normGradSqFun (H.metric.restrictOpen d.neighborhood) (collarRho H T i d) q =
      Real.exp (-2 * collarHeight H T i d q) := by
  let Φ := collarCoordinates H T i d
  let g := H.metric.restrictOpen d.neighborhood
  let h := actualPullbackMetric H T i d
  let ρ : C^∞⟮𝓡 3, d.neighborhood; ℝ⟯ :=
    ⟨collarRho H T i d, collarRho_smooth H T i d⟩
  obtain ⟨p, rfl⟩ := Φ.surjective q
  have hp : 0 ≤ p.val.2 := by
    simpa only [Diffeomorph.coe_toEquiv, Φ, collarHeight_coordinates] using hq
  obtain ⟨hhess, hnorm⟩ := actualPullback_barrier_data H T i d heq p hp
  have hprofile : (ρ ∘ Φ) = (fun y : sourceStrip H T i d => Real.exp (-y.val.2) - 1) :=
    funext (collarRho_coordinates H T i d)
  have hheight : ((collarHeight H T i d) ∘ Φ) =
      (fun y : sourceStrip H T i d => y.val.2) :=
    funext (collarHeight_coordinates H T i d)
  have hdh (a : TangentSpace signedCollarModel p) :
      mvfderiv (𝓡 3) (collarHeight H T i d) (Φ p)
        (mfderiv signedCollarModel (𝓡 3) Φ p a) = a.2 := by
    have hc := mvfderiv_comp_apply p
      ((collarHeight_smooth H T i d).mdifferentiableAt (by simp))
      (Φ.contMDiff.mdifferentiableAt (by simp)) a
    rw [hheight] at hc
    change mfderiv signedCollarModel 𝓘(ℝ)
      (fun y : sourceStrip H T i d => y.val.2) p a =
        mvfderiv (𝓡 3) (collarHeight H T i d) (Φ p)
          (mfderiv signedCollarModel (𝓡 3) Φ p a) at hc
    rw [DifferentialGeometry.mfderiv_restrict_open, mfderiv_snd] at hc
    exact hc.symm
  constructor
  · intro v w
    let L := Φ.mfderivToContinuousLinearEquiv (by simp) p
    let a := L.symm v
    let b := L.symm w
    have ha : mfderiv signedCollarModel (𝓡 3) Φ p a = v := by
      rw [← Φ.mfderivToContinuousLinearEquiv_coe (by simp)]
      exact L.apply_symm_apply v
    have hb : mfderiv signedCollarModel (𝓡 3) Φ p b = w := by
      rw [← Φ.mfderivToContinuousLinearEquiv_coe (by simp)]
      exact L.apply_symm_apply w
    have hn := hessFun_pullbackCross g Φ ρ p a b
    change hessFun h (ρ ∘ Φ) p a b = hessFun g ρ (Φ p)
      (mfderiv signedCollarModel (𝓡 3) Φ p a)
      (mfderiv signedCollarModel (𝓡 3) Φ p b) at hn
    rw [hprofile, hhess a b, ha, hb] at hn
    have hi := Diffeomorph.pullbackMetricCross_inner g Φ p a b
    change h.inner p a b = _ at hi
    rw [ha, hb] at hi
    have hda := hdh a
    have hdb := hdh b
    rw [ha] at hda
    rw [hb] at hdb
    rw [hi, ← hda, ← hdb] at hn
    simpa only [g, ρ, ContMDiffMap.coeFn_mk, Diffeomorph.coe_toEquiv, Φ,
      collarHeight_coordinates] using hn.symm
  · have hn := normGradSqFun_eq_of_pullback_inner h g Φ p
      (Φ.contMDiff.mdifferentiableAt (by simp))
      (Diffeomorph.pullbackMetricCross_inner g Φ p)
      (by
        rw [← Φ.mfderivToContinuousLinearEquiv_coe (by simp)]
        exact (Φ.mfderivToContinuousLinearEquiv (by simp) p).surjective)
      ρ (ρ.contMDiff.mdifferentiableAt (by simp))
    rw [hprofile, hnorm] at hn
    simpa only [g, ρ, ContMDiffMap.coeFn_mk, Diffeomorph.coe_toEquiv, Φ,
      collarHeight_coordinates] using hn.symm

end ActualCollar

/-- A genuine signed collar agreeing with the original cusp map is constructed
from that map's actual smooth embedding, without any Hessian prerequisite. -/
theorem exists_actual_cusp_signed_collar
    (H : FiniteVolumeHyperbolicModel) (T : HyperbolicTruncation H) (i : Fin T.count)
    (w : ℝ) (hw : 0 < w) :
    ∃ d : SmoothTwoSidedCollar torusModel (𝓡 3) (fun s => T.cuspMap i (s, halfZero)),
      d.radius ≤ w ∧
      ∀ (p : Torus × symmetricOpenInterval d.radius) (hp : 0 ≤ p.2.val),
        d.toFun p = T.cuspMap i (p.1, halfPoint p.2.val hp) := by
  let := halfClosedIntervalChartedSpace hw
  let := halfClosedInterval_isManifold hw
  let e : Ico (0 : ℝ) w → EuclideanHalfSpace 1 := fun r => halfPoint r.val r.property.1
  let j : Torus × Ico (0 : ℝ) w → CuspHalfSpace := Prod.map id e
  let c : Torus × Ico (0 : ℝ) w → H.Carrier := T.cuspMap i ∘ j
  have hval := isSmoothEmbedding_halfClosedInterval_inclusion hw
  have he : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ e := by
    have heq : e = halfSpaceOneLift ∘ (Subtype.val : Ico (0 : ℝ) w → ℝ) :=
      funext (fun r => (halfSpaceOneLift_eq_halfPoint r.property.1).symm)
    rw [heq]
    exact contMDiffOn_halfSpaceOneLift.comp_contMDiff hval.contMDiff (fun r => r.property.1)
  have hj : ContMDiff halfCollarModel halfCollarModel ∞ j := contMDiff_id.prodMap he
  have hc : ContMDiff halfCollarModel (𝓡 3) ∞ c := (T.cuspEmbedding i).contMDiff.comp hj
  have heinj (r : Ico (0 : ℝ) w) :
      Function.Injective (mfderiv (𝓡∂ 1) (𝓡∂ 1) e r) := by
    let A : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
      mfderiv (𝓡∂ 1) (𝓡∂ 1) e r
    let B : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
      mfderiv (𝓡∂ 1) 𝓘(ℝ) (fun t : EuclideanHalfSpace 1 => t.val 0) (e r)
    let C : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
      mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Ico (0 : ℝ) w → ℝ) r
    have hC : Function.Injective C :=
      (hval.isImmersion.isImmersionAt r).mfderiv_injective (by simp)
    have hcomp : C = B.comp A :=
      mfderiv_comp r (contMDiff_halfSpaceOneCoordinate.mdifferentiableAt (by simp))
        (he.mdifferentiableAt (by simp))
    change Function.Injective A
    intro a b hab
    apply hC
    rw [hcomp]
    exact congrArg B hab
  have hcinj : Function.Injective (fun s => c (s, ⟨0, le_rfl, hw⟩)) := by
    intro s t hst
    have hpair := (T.cuspEmbedding i).isEmbedding.injective hst
    exact congrArg Prod.fst hpair
  have hcderiv (s : Torus) : Function.Bijective
      (mfderiv halfCollarModel (𝓡 3) c (s, ⟨0, le_rfl, hw⟩)) := by
    let p : Torus × Ico (0 : ℝ) w := (s, ⟨0, le_rfl, hw⟩)
    let A : TorusE × EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      mfderiv halfCollarModel (𝓡 3) c p
    have hA : Function.Injective A := by
      have hDj : Function.Injective (mfderiv halfCollarModel halfCollarModel j p) := by
        rw [mfderiv_prodMap mdifferentiableAt_id (he.mdifferentiableAt (by simp)), mfderiv_id]
        exact Function.injective_id.prodMap (heinj p.2)
      have hDc := (T.cuspEmbedding i).isImmersion.isImmersionAt (j p)
      have hcomp := mfderiv_comp p
        ((T.cuspEmbedding i).contMDiff.mdifferentiableAt (by simp))
        (hj.mdifferentiableAt (by simp))
      change A = _ at hcomp
      rw [hcomp]
      exact (hDc.mfderiv_injective (by simp)).comp hDj
    exact A.toLinearMap.linearEquivOfInjective hA (by simp [TorusE, Module.finrank_prod]) |>.bijective
  obtain ⟨d, hdwidth, hd⟩ := exists_smoothTwoSidedCollar_of_halfClosedInterval hw c hc hcinj hcderiv
  exact ⟨d, hdwidth, hd⟩


/-- Actual cusp embeddings supply an actual ambient boundary defining function
with the exact model Hessian and gradient norm on the nonnegative collar. -/
theorem exists_actual_cusp_barrier
    (H : FiniteVolumeHyperbolicModel) (T : HyperbolicTruncation H) (i : Fin T.count)
    (w : ℝ) (hw : 0 < w) :
    ∃ d : SmoothTwoSidedCollar torusModel (𝓡 3) (fun s => T.cuspMap i (s, halfZero)),
      d.radius ≤ w ∧
      (∀ (p : Torus × symmetricOpenInterval d.radius) (hp : 0 ≤ p.2.val),
        d.toFun p = T.cuspMap i (p.1, halfPoint p.2.val hp)) ∧
      ∀ q : d.neighborhood, 0 ≤ collarHeight H T i d q →
        (∀ v w : TangentSpace (𝓡 3) q,
          hessFun (H.metric.restrictOpen d.neighborhood) (collarRho H T i d) q v w =
            Real.exp (-collarHeight H T i d q) / 2 *
              ((H.metric.restrictOpen d.neighborhood).inner q v w +
                mvfderiv (𝓡 3) (collarHeight H T i d) q v *
                  mvfderiv (𝓡 3) (collarHeight H T i d) q w)) ∧
        normGradSqFun (H.metric.restrictOpen d.neighborhood) (collarRho H T i d) q =
          Real.exp (-2 * collarHeight H T i d q) := by
  obtain ⟨d, hdwidth, heq⟩ := exists_actual_cusp_signed_collar H T i w hw
  exact ⟨d, hdwidth, heq, actual_cusp_barrier_data H T i d heq⟩

end DifferentialGeometry.Geometry.Hyperbolic.CuspConvexity

namespace DifferentialGeometry.Geometry.Hyperbolic.CuspConvexity

private theorem isCompact_collar_height_band
    (H : FiniteVolumeHyperbolicModel) (T : HyperbolicTruncation H) (i : Fin T.count)
    (d : SmoothTwoSidedCollar torusModel (𝓡 3) (fun s => T.cuspMap i (s, halfZero)))
    (l u : ℝ) (hl : -d.radius < l) (hu : u < d.radius) :
    IsCompact {q : d.neighborhood | collarHeight H T i d q ∈ Icc l u} := by
  let Φ := collarCoordinates H T i d
  let C : Set (Torus × ℝ) := univ ×ˢ Icc l u
  let S : Set (sourceStrip H T i d) := Subtype.val ⁻¹' C
  have hC : IsCompact C := isCompact_univ.prod isCompact_Icc
  have hCrange : C ⊆ range (Subtype.val : sourceStrip H T i d → Torus × ℝ) := by
    intro p hp
    exact ⟨⟨p, hl.trans_le hp.2.1, hp.2.2.trans_lt hu⟩, rfl⟩
  have hS : IsCompact S :=
    _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hC hCrange
  have himage := hS.image Φ.contMDiff.continuous
  have heq : Φ '' S = {q : d.neighborhood | collarHeight H T i d q ∈ Icc l u} := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      change collarHeight H T i d (collarCoordinates H T i d p) ∈ Icc l u
      rw [collarHeight_coordinates]
      exact hp.2
    · intro hq
      obtain ⟨p, rfl⟩ := Φ.surjective q
      refine ⟨p, ⟨mem_univ _, ?_⟩, rfl⟩
      change collarHeight H T i d (collarCoordinates H T i d p) ∈ Icc l u at hq
      rw [collarHeight_coordinates] at hq
      exact hq
  rw [heq] at himage
  exact himage

/-- The original cusp metric has one compact signed band and one positive
metric-jet tolerance. Both are chosen from the same original collar before any
perturbed metric or physical time is introduced. No model formula is used at
negative heights. -/
theorem exists_compact_cusp_hessian_margin
    (H : FiniteVolumeHyperbolicModel) (T : HyperbolicTruncation H) (i : Fin T.count)
    (d : SmoothTwoSidedCollar torusModel (𝓡 3) (fun s => T.cuspMap i (s, halfZero)))
    (heq : ∀ (p : Torus × symmetricOpenInterval d.radius) (hp : 0 ≤ p.2.val),
      d.toFun p = T.cuspMap i (p.1, halfPoint p.2.val hp)) :
    ∃ δ ε : ℝ, 0 < δ ∧ δ < d.radius ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧
      let K : Set d.neighborhood := {q | |collarHeight H T i d q| ≤ δ}
      IsCompact K ∧ ∀ q ∈ K, ∀ v : TangentSpace (𝓡 3) q, v ≠ 0 →
        (1 / 4 : ℝ) * (H.metric.restrictOpen d.neighborhood).inner q v v <
          hessFun (H.metric.restrictOpen d.neighborhood) (collarRho H T i d) q v v ∧
        12 * ε * Real.sqrt (normGradSqFun (H.metric.restrictOpen d.neighborhood)
          (collarRho H T i d) q) * (H.metric.restrictOpen d.neighborhood).inner q v v ≤
            (1 / 8 : ℝ) * (H.metric.restrictOpen d.neighborhood).inner q v v := by
  let g := H.metric.restrictOpen d.neighborhood
  let ρ := collarRho H T i d
  have hρ := collarRho_smooth H T i d
  have hboundary (s : Torus) :
      let q := d.toDiffeomorph (s, ⟨0, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩)
      ∀ v : TangentSpace (𝓡 3) q, v ≠ 0 →
        (1 / 4 : ℝ) * g.inner q v v < hessFun g ρ q v v := by
    dsimp only
    intro v hv
    let q := d.toDiffeomorph (s, ⟨0, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩)
    have hq : collarHeight H T i d q = 0 := by
      unfold collarHeight q
      rw [Diffeomorph.symm_apply_apply]
    have hh := (actual_cusp_barrier_data H T i d heq q hq.ge).1 v v
    rw [hq, neg_zero, Real.exp_zero] at hh
    have hg : 0 < g.inner q v v := g.pos q v hv
    have hsq := mul_self_nonneg (mvfderiv (𝓡 3) (collarHeight H T i d) q v)
    change (1 / 4 : ℝ) * g.inner q v v < hessFun g ρ q v v
    change hessFun g ρ q v v =
      1 / 2 * (g.inner q v v + mvfderiv (𝓡 3) (collarHeight H T i d) q v *
        mvfderiv (𝓡 3) (collarHeight H T i d) q v) at hh
    nlinarith
  obtain ⟨δ, hδ, hδd, hband⟩ :=
    exists_uniform_hessian_lower_bound_on_closed_band d g hρ (1 / 4) hboundary
  let K : Set d.neighborhood := {q | |collarHeight H T i d q| ≤ δ}
  have hK : IsCompact K := by
    have hc := isCompact_collar_height_band H T i d (-δ) δ (neg_lt_neg hδd) hδd
    simpa only [K, abs_le, mem_ofPred_eq, mem_Icc] using hc
  have hgrad : Continuous (fun q => Real.sqrt (normGradSqFun g ρ q)) :=
    Real.continuous_sqrt.comp (normGradSqFun_continuous g hρ)
  obtain ⟨b, hb⟩ := hK.bddAbove_image hgrad.continuousOn
  let L : ℝ := max b 1
  have hL : 1 ≤ L := le_max_right _ _
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let ε : ℝ := 1 / (96 * L)
  have hden : 0 < (96 : ℝ) * L := mul_pos (by norm_num) hLpos
  have hεpos : 0 < ε := one_div_pos.mpr hden
  have hε : ε ≤ 1 / 2 := (div_le_iff₀ hden).mpr (by nlinarith)
  have hεL : 12 * ε * L = (1 / 8 : ℝ) := by
    dsimp only [ε]
    field_simp [ne_of_gt hLpos]
    norm_num
  refine ⟨δ, ε, hδ, hδd, hεpos, hε, hK, ?_⟩
  intro q hq v hv
  refine ⟨hband q hq v hv, ?_⟩
  have hgradL : Real.sqrt (normGradSqFun g ρ q) ≤ L :=
    (hb (mem_image_of_mem _ hq)).trans (le_max_left _ _)
  have hbound : 12 * ε * Real.sqrt (normGradSqFun g ρ q) ≤ (1 / 8 : ℝ) := by
    rw [← hεL]
    exact mul_le_mul_of_nonneg_left hgradL (mul_nonneg (by norm_num) hεpos.le)
  exact mul_le_mul_of_nonneg_right hbound (metric_inner_self_nonneg g q v)

end DifferentialGeometry.Geometry.Hyperbolic.CuspConvexity

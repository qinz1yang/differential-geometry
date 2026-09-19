import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCylinderTopology
import DifferentialGeometry.Analysis.Calculus.Periodic.CircleLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProjectedFamilies
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCoveringMap

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem continuous_deriv_y_of_smoothProductCylinder
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {a b : ℝ} (hab : a < b) {P : Type*} [TopologicalSpace P]
    (c : P → ProductCurve M)
    (hc : @Continuous P (ProductCurve M) inferInstance
      (smoothProductCylinderTopology e (Icc a b)) c)
    (hs : ∀ p, (c p).SmoothOn (I := I) (Icc a b)) :
    Continuous (fun q : (P × Icc a b) × ℝ =>
      deriv (fun x => (c q.1.1).y x q.1.2) q.2) := by
  let A : QuotientProductAtlas I M := quotientProductAtlas (I := I) (M := M)
  let := A.charts
  let := A.smoothManifold
  let eP := A.smoothLoopEmbedding e
  let L : (EuclideanSpace ℝ (Fin N) × ℂ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (N + 2)) :=
    ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N))).prodCongr
      Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv).trans
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 2)).symm
  let π : EuclideanSpace ℝ (Fin (N + 2)) →L[ℝ] ℂ :=
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin N)) ℂ).comp
      L.symm.toContinuousLinearMap
  have hcoord (p : P) (t x : ℝ) :
      π (eP.map ((c p).map.lift x t)) =
        Complex.exp ((2 * Real.pi * (c p).y x t : ℝ) * Complex.I) := by
    have heq : eP.map ((c p).map.lift x t) =
        L (productEmbeddedCoordinates e (c p) x t) := rfl
    change (L.symm (eP.map ((c p).map.lift x t))).2 = _
    rw [heq, L.symm_apply_apply]
    change ((AddCircle.homeomorphCircle _) ((c p).map (x : Surgery.Topology.Circle) t).2 : ℂ) = _
    rw [← (c p).lift_eq, AddCircle.homeomorphCircle_apply,
      AddCircle.toCircle_apply_mk, Circle.coe_exp]
    simp
  have hmap := continuous_map_of_continuous_productCurve A e
    (uniqueDiffOn_Icc hab) c hc
  have hmap_smooth (p : P) := (c p).smoothOn_map A (hs p)
  have hF : Continuous (fun q : (P × Icc a b) × ℝ =>
      eP.map ((c q.1.1).map.lift q.2 q.1.2)) := by
    simpa only [iteratedDeriv_zero] using
      continuous_embedded_spatial_jets_of_smoothCylinder eP hab hmap hmap_smooth 0
  have hDF : Continuous (fun q : (P × Icc a b) × ℝ =>
      deriv (fun x => eP.map ((c q.1.1).map.lift x q.1.2)) q.2) := by
    simpa only [iteratedDeriv_one] using
      continuous_embedded_spatial_jets_of_smoothCylinder eP hab hmap hmap_smooth 1
  have hderiv (p : P) (t : Icc a b) (x : ℝ) :
      deriv (fun z => Complex.exp ((2 * Real.pi * (c p).y z t : ℝ) * Complex.I)) x =
        π (deriv (fun z => eP.map ((c p).map.lift z t)) x) := by
    have hdiff : DifferentiableAt ℝ (fun z => eP.map ((c p).map.lift z t)) x :=
      (eP.smooth.comp ((c p).map.smooth_slice (hmap_smooth p) t.2)).contDiff
        |>.differentiable (by simp) x
    have hd := (π.hasFDerivAt).comp_hasDerivAt x hdiff.hasDerivAt
    have hfun : (π ∘ (fun z => eP.map ((c p).map.lift z t))) =
        fun z => Complex.exp ((2 * Real.pi * (c p).y z t : ℝ) * Complex.I) :=
      funext (hcoord p t)
    rw [hfun] at hd
    exact hd.deriv
  have hne (q : (P × Icc a b) × ℝ) :
      π (eP.map ((c q.1.1).map.lift q.2 q.1.2)) ≠ 0 := by
    rw [hcoord]
    exact Complex.exp_ne_zero _
  have hquot : Continuous (fun q : (P × Icc a b) × ℝ =>
      (π (deriv (fun x => eP.map ((c q.1.1).map.lift x q.1.2)) q.2) /
        π (eP.map ((c q.1.1).map.lift q.2 q.1.2)) ).im) := by
    exact (Complex.continuous_im.comp ((π.continuous.comp hDF).div (π.continuous.comp hF) hne))
  have hcont := hquot.div_const (2 * Real.pi)
  refine hcont.congr ?_
  intro q
  have hy : DifferentiableAt ℝ (fun z => (c q.1.1).y z q.1.2) q.2 := by
    have hslice : ContDiff ℝ ∞ (fun z => (c q.1.1).y z q.1.2) :=
      contDiffOn_univ.mp ((hs q.1.1).2.comp
        (contDiff_id.prodMk contDiff_const).contDiffOn
          (fun z _ => ⟨mem_univ z, q.1.2.2⟩))
    exact hslice.differentiable (by simp) q.2
  rw [DifferentialGeometry.Analysis.deriv_eq_im_div_circleExp hy, hderiv, ← hcoord]


theorem continuousOn_deriv_y_of_smoothProductCylinder
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {a b : ℝ} (hab : a < b) {P : Type*} [TopologicalSpace P]
    (c : P → ProductCurve M)
    (hc : @Continuous P (ProductCurve M) inferInstance
      (smoothProductCylinderTopology e (Icc a b)) c)
    (hs : ∀ p, (c p).SmoothOn (I := I) (Icc a b)) :
    ContinuousOn (fun q : (P × ℝ) × ℝ =>
      deriv (fun x => (c q.1.1).y x q.2) q.1.2)
      ((univ ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc a b) := by
  have h := continuous_deriv_y_of_smoothProductCylinder e hab c hc hs
  rw [continuousOn_iff_continuous_domRestrict]
  let reindex : ↥((univ ×ˢ Icc (0 : ℝ) 1 : Set (P × ℝ)) ×ˢ Icc a b) →
      (P × Icc a b) × ℝ := fun q => ((q.1.1.1, ⟨q.1.2, q.2.2⟩), q.1.1.2)
  have hindex : Continuous reindex :=
    (continuous_subtype_val.fst.fst.prodMk
      (continuous_subtype_val.snd.subtype_mk _)).prodMk continuous_subtype_val.fst.snd
  exact h.comp hindex

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

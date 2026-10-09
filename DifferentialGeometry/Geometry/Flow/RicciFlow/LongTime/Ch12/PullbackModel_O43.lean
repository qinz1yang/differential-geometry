import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCovariantJets

/-!
# CH12-O43 G2b prep: public copy of the chart model of the pullback error

Public copy (suffix `_O43`) of the private `pullbackErrorExpression` / `pullbackError_model_eq` of
`Geometry/Metric/Pullback/FiniteCovariantJets.lean`: in a chart at `p` (target chart at `q`), the
model representative of `f^*g − G` is `β(pullbackForm(g_q(f̃ y), Df̃ y) − G_p(y))`,
`f̃ = ext_q ∘ f ∘ ext_p⁻¹`.  For S80's `hmodel` take `p = q = c`, `g = G = H.metric`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.TensorLieDeriv DifferentialGeometry.Manifold
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : CompleteSpace F := FiniteDimensional.complete ℝ F
private local instance sourceC1_O43 : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
private local instance targetC1_O43 : IsManifold J 1 N := IsManifold.of_le (n := ∞) (by decide)

def bilinearTensor02_O43 (B : E →L[ℝ] E →L[ℝ] ℝ) : Tensor0SModel 2 ℝ E :=
  ((continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap.comp B).uncurryLeft

/-- `bilinearTensor02_O43` is smooth (a continuous linear map). -/
theorem bilinearTensor02_contDiff_O43 :
    ContDiff ℝ ∞ (bilinearTensor02_O43 (E := E)) := by
  let L₁ := (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap
  let L₂ := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ).symm.toContinuousLinearMap
  exact L₂.contDiff.comp ((contDiff_const (c := L₁)).clm_comp contDiff_id)

def pullbackErrorExpression_O43 (g : SmoothRiemannianMetric J N)
    (G : SmoothRiemannianMetric I M) (p : M) (q : N)
    (z : E × F × (E →L[ℝ] F)) : Tensor0SModel 2 ℝ E :=
  bilinearTensor02_O43 (pullbackForm
    (pullbackMetricCoefficients g (interiorChart J ∞ q).symm z.2.1, z.2.2) -
      pullbackMetricCoefficients G (interiorChart I ∞ p).symm z.1)


omit [FiniteDimensional ℝ F] in
/-- Public copy of `pullbackError_model_eq` (private in FiniteCovariantJets). -/
theorem pullbackError_model_eq_O43
    (g : SmoothRiemannianMetric J N) (G : SmoothRiemannianMetric I M)
    (f : M → N) (p : M) (q : N) {y : E}
    (hy : y ∈ (interiorChart I ∞ p).target)
    (hf : MDifferentiableAt I J f ((extChartAt I p).symm y))
    (hfy : f ((extChartAt I p).symm y) ∈ (interiorChart J ∞ q).source) :
    tensor0SModelInChart (I := I) (M := M) 2 p
        (fun z : M =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace I z) ℝ).symm.toContinuousLinearMap.comp
          (localPullInner g f z - G.inner z)).uncurryLeft) y =
      pullbackErrorExpression_O43 g G p q
        (y, (extChartAt J q ∘ f ∘ (extChartAt I p).symm) y,
          fderiv ℝ (extChartAt J q ∘ f ∘ (extChartAt I p).symm) y) := by
  let c := interiorChart I ∞ p
  let d := interiorChart J ∞ q
  let z := (extChartAt I p).symm y
  have hz : z ∈ (chartAt H p).source := (c.map_target' hy).1
  have hcy : extChartAt I p z = y := c.right_inv' hy
  have hRange : Set.range I ∈ 𝓝 y :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hy)
      (fun w hw => extChartAt_target_subset_range p (interior_subset hw))
  have hsource : (trivializationAt E (TangentSpace I) p).symmL ℝ z =
      mfderiv 𝓘(ℝ, E) I c.symm y := by
    rw [TangentBundle.symmL_trivializationAt hz, hcy,
      mfderivWithin_of_mem_nhds hRange]
    rfl
  have hc : MDifferentiableAt 𝓘(ℝ, E) I c.symm y :=
    (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds hy)).mdifferentiableAt
      (by simp)
  have hfc : MDifferentiableAt 𝓘(ℝ, E) J (f ∘ c.symm) y := hf.comp y hc
  let A : ∀ w : M, Tensor0SSpace 2 I w := fun w =>
    ((continuousMultilinearCurryFin1 ℝ (TangentSpace I w) ℝ).symm.toContinuousLinearMap.comp
      (localPullInner g f w - G.inner w)).uncurryLeft
  change tensor0SModelInChart (I := I) (M := M) 2 p A y = _
  ext slots
  refine (tensor0SModelInChart_apply (I := I) (M := M) 2 p A y slots).trans ?_
  change localPullInner g f z
      ((trivializationAt E (TangentSpace I) p).symmL ℝ z (slots 0))
      ((trivializationAt E (TangentSpace I) p).symmL ℝ z (slots 1)) -
      G.inner z ((trivializationAt E (TangentSpace I) p).symmL ℝ z (slots 0))
        ((trivializationAt E (TangentSpace I) p).symmL ℝ z (slots 1)) = _
  rw [hsource, localPullInner_apply]
  have htarget := pullbackMetricCoefficients_fderiv_symm g d.symm hfc hfy
    (slots 0) (slots 1)
  have hchain := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := J)
    (f := c.symm) (g := f) y hf hc
  rw [hchain] at htarget
  change _ = pullbackMetricCoefficients g d.symm
      ((d ∘ f ∘ c.symm) y)
      (fderiv ℝ (d ∘ f ∘ c.symm) y (slots 0))
      (fderiv ℝ (d ∘ f ∘ c.symm) y (slots 1)) -
        pullbackMetricCoefficients G c.symm y (slots 0) (slots 1)
  exact congrArg (fun a => a - G.inner z
    (mfderiv 𝓘(ℝ, E) I c.symm y (slots 0))
    (mfderiv 𝓘(ℝ, E) I c.symm y (slots 1))) htarget.symm


end GC.LongTime.Ch12

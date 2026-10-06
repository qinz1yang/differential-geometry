import DifferentialGeometry.Geometry.Metric.Pullback.FiniteInnerRegularity
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.CoordinateJets
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.SmoothCompatibility
import DifferentialGeometry.Topology.Manifold.InteriorChart

set_option autoImplicit false

noncomputable section

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.TensorLieDeriv DifferentialGeometry.Manifold
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : CompleteSpace F := FiniteDimensional.complete ℝ F
private local instance sourceC1 : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
private local instance targetC1 : IsManifold J 1 N := IsManifold.of_le (n := ∞) (by decide)

private def bilinearTensor02 (B : E →L[ℝ] E →L[ℝ] ℝ) : Tensor0SModel 2 ℝ E :=
  ((continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap.comp B).uncurryLeft

private theorem bilinearTensor02_contDiff :
    ContDiff ℝ ∞ (bilinearTensor02 (E := E)) := by
  let L₁ := (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap
  let L₂ := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ).symm.toContinuousLinearMap
  exact L₂.contDiff.comp ((contDiff_const (c := L₁)).clm_comp contDiff_id)

private def pullbackErrorExpression (g : SmoothRiemannianMetric J N)
    (G : SmoothRiemannianMetric I M) (p : M) (q : N)
    (z : E × F × (E →L[ℝ] F)) : Tensor0SModel 2 ℝ E :=
  bilinearTensor02 (pullbackForm
    (pullbackMetricCoefficients g (interiorChart J ∞ q).symm z.2.1, z.2.2) -
      pullbackMetricCoefficients G (interiorChart I ∞ p).symm z.1)

omit [FiniteDimensional ℝ F] [T2Space M] in
private theorem pullbackErrorExpression_contDiffAt
    (g : SmoothRiemannianMetric J N) (G : SmoothRiemannianMetric I M)
    (p : M) (q : N) (hp : I.IsInteriorPoint p) (hq : J.IsInteriorPoint q)
    (L : E →L[ℝ] F) (n : ℕ) :
    ContDiffAt ℝ n (pullbackErrorExpression g G p q)
      (extChartAt I p p, extChartAt J q q, L) := by
  let c := interiorChart I ∞ p
  let d := interiorChart J ∞ q
  have hpc : p ∈ c.source := (mem_interiorChart_source_iff I ∞ p).mpr hp
  have hqd : q ∈ d.source := (mem_interiorChart_source_iff J ∞ q).mpr hq
  have hB := (contDiffOn_pullback_metric_coefficients g (f := d.symm) d.open_target
    d.contMDiffOn_invFun).contDiffAt
      (d.open_target.mem_nhds (d.map_source' hqd))
  have hR := (contDiffOn_pullback_metric_coefficients G (f := c.symm) c.open_target
    c.contMDiffOn_invFun).contDiffAt
      (c.open_target.mem_nhds (c.map_source' hpc))
  have hB' := (hB.of_le (by simp : (n : WithTop ℕ∞) ≤ ∞)).comp
    (extChartAt I p p, extChartAt J q q, L) contDiffAt_snd.fst
  have hR' := (hR.of_le (by simp : (n : WithTop ℕ∞) ≤ ∞)).comp
    (extChartAt I p p, extChartAt J q q, L) contDiffAt_fst
  have hP := ((pullbackForm.contDiff.of_le
    (by simp : (n : WithTop ℕ∞) ≤ ∞)).contDiffAt).comp
      (extChartAt I p p, extChartAt J q q, L) (hB'.prodMk contDiffAt_snd.snd)
  exact ((bilinearTensor02_contDiff.of_le
    (by simp : (n : WithTop ℕ∞) ≤ ∞)).contDiffAt).comp
      (extChartAt I p p, extChartAt J q q, L) (hP.sub hR')

omit [FiniteDimensional ℝ F] [T2Space M] in
private theorem pullbackError_model_eq
    (g : SmoothRiemannianMetric J N) (G : SmoothRiemannianMetric I M)
    (f : M → N) (p : M) (q : N) {y : E}
    (hy : y ∈ (interiorChart I ∞ p).target)
    (hf : MDifferentiableAt I J f ((extChartAt I p).symm y))
    (hfy : f ((extChartAt I p).symm y) ∈ (interiorChart J ∞ q).source) :
    tensor0SModelInChart (I := I) (M := M) 2 p
        (fun z : M =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace I z) ℝ).symm.toContinuousLinearMap.comp
          (localPullInner g f z - G.inner z)).uncurryLeft) y =
      pullbackErrorExpression g G p q
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

omit [FiniteDimensional ℝ F] [T2Space M] in
private theorem pullbackError_model_eventuallyEq
    (g : SmoothRiemannianMetric J N) (G : SmoothRiemannianMetric I M)
    {f : M → N} {p : M} (q : N) (hp : I.IsInteriorPoint p)
    (hq : J.IsInteriorPoint q) (hfp : f p = q)
    (hf : ContMDiffAt I J 1 f p) :
    tensor0SModelInChart (I := I) (M := M) 2 p
        (fun z : M =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace I z) ℝ).symm.toContinuousLinearMap.comp
          (localPullInner g f z - G.inner z)).uncurryLeft)
      =ᶠ[𝓝 (extChartAt I p p)]
        (fun y => pullbackErrorExpression g G p q
          (y, (extChartAt J q ∘ f ∘ (extChartAt I p).symm) y,
            fderiv ℝ (extChartAt J q ∘ f ∘ (extChartAt I p).symm) y)) := by
  let c := interiorChart I ∞ p
  let d := interiorChart J ∞ q
  have hpc : p ∈ c.source := (mem_interiorChart_source_iff I ∞ p).mpr hp
  have hqd : f p ∈ d.source := by
    rw [hfp]
    exact (mem_interiorChart_source_iff J ∞ q).mpr hq
  have hnear := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp hf
  have hnear' : ∀ᶠ y in 𝓝 (extChartAt I p p),
      ContMDiffAt I J 1 f ((extChartAt I p).symm y) := by
    apply (continuousAt_extChartAt_symm (I := I) p).tendsto.eventually
    simpa only [extChartAt_to_inv] using hnear
  have htarget : ∀ᶠ y in 𝓝 (extChartAt I p p),
      f ((extChartAt I p).symm y) ∈ d.source := by
    apply (continuousAt_extChartAt_symm (I := I) p).tendsto.eventually
      (p := fun z : M => f z ∈ d.source)
    simpa only [extChartAt_to_inv] using
      hf.continuousAt.tendsto.eventually
        (p := fun z : N => z ∈ d.source) (d.open_source.mem_nhds hqd)
  filter_upwards [c.open_target.mem_nhds (c.map_source' hpc), hnear', htarget]
    with y hy hfy hdy
  exact pullbackError_model_eq g G f p q hy (hfy.mdifferentiableAt (by norm_num)) hdy

omit [FiniteDimensional ℝ F] [T2Space M] in
private theorem pullbackError_model_contDiffAt
    (g : SmoothRiemannianMetric J N) (G : SmoothRiemannianMetric I M)
    {f : M → N} {p : M} {n : ℕ} (hp : I.IsInteriorPoint p)
    (hf : ContMDiffAt I J (n + 1) f p) :
    ContDiffAt ℝ n (tensor0SModelInChart (I := I) (M := M) 2 p
      (fun z : M =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace I z) ℝ).symm.toContinuousLinearMap.comp
        (localPullInner g f z - G.inner z)).uncurryLeft)) (extChartAt I p p) :=
  ((contMDiffAt_tensor0S_iff_contDiffWithinAt_model n 2 _ p).mp
    (contMDiffAt_localPullMetricError_of_contMDiffAt g G hf)).contDiffAt
      (mem_interior_iff_mem_nhds.mp hp)

omit [FiniteDimensional ℝ F] [T2Space M] in
private theorem pullbackError_model_jets_eq
    (g : SmoothRiemannianMetric J N) (G : SmoothRiemannianMetric I M)
    {f h : M → N} {p : M} {n : ℕ}
    (hp : I.IsInteriorPoint p) (hfp : J.IsInteriorPoint (f p)) (heq : f p = h p)
    (hf : ContMDiffAt I J (n + 1) f p) (hh : ContMDiffAt I J (n + 1) h p)
    (hjets : ∀ j ≤ n + 1,
      iteratedFDeriv ℝ j (extChartAt J (f p) ∘ f ∘ (extChartAt I p).symm)
          (extChartAt I p p) =
        iteratedFDeriv ℝ j (extChartAt J (f p) ∘ h ∘ (extChartAt I p).symm)
          (extChartAt I p p)) (k : ℕ) (hk : k ≤ n) :
    iteratedFDeriv ℝ k (tensor0SModelInChart (I := I) (M := M) 2 p
        (fun z : M =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace I z) ℝ).symm.toContinuousLinearMap.comp
          (localPullInner g f z - G.inner z)).uncurryLeft)) (extChartAt I p p) =
      iteratedFDeriv ℝ k (tensor0SModelInChart (I := I) (M := M) 2 p
        (fun z : M =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace I z) ℝ).symm.toContinuousLinearMap.comp
          (localPullInner g h z - G.inner z)).uncurryLeft)) (extChartAt I p p) := by
  have hRange : Set.range I ∈ 𝓝 (extChartAt I p p) := mem_interior_iff_mem_nhds.mp hp
  have hfc : ContDiffAt ℝ (n + 1)
      (extChartAt J (f p) ∘ f ∘ (extChartAt I p).symm) (extChartAt I p p) :=
    (contMDiffAt_iff.mp hf).2.contDiffAt hRange
  have hhc : ContDiffAt ℝ (n + 1)
      (extChartAt J (f p) ∘ h ∘ (extChartAt I p).symm) (extChartAt I p p) := by
    rw [heq]
    exact (contMDiffAt_iff.mp hh).2.contDiffAt hRange
  have hΦ := pullbackErrorExpression_contDiffAt g G p (f p) hp hfp
    (fderiv ℝ (extChartAt J (f p) ∘ f ∘ (extChartAt I p).symm)
      (extChartAt I p p)) n
  have hΦ' : ContDiffAt ℝ n (pullbackErrorExpression g G p (f p))
      (extChartAt I p p,
        (extChartAt J (f p) ∘ f ∘ (extChartAt I p).symm) (extChartAt I p p),
        fderiv ℝ (extChartAt J (f p) ∘ f ∘ (extChartAt I p).symm)
          (extChartAt I p p)) := by
    simpa only [Function.comp_apply, extChartAt_to_inv] using hΦ
  have hAf := pullbackError_model_eventuallyEq g G (f p) hp hfp rfl
    (hf.of_le (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))))
  have hAh := pullbackError_model_eventuallyEq g G (f p) hp hfp heq.symm
    (hh.of_le (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))))
  exact ((hAf.iteratedFDeriv ℝ k).self_of_nhds).trans
    ((DifferentialGeometry.Analysis.iteratedFDeriv_comp_value_fderiv_eq_of_eq_jets
      hfc hhc hΦ' hjets k hk).trans (hAh.iteratedFDeriv ℝ k).self_of_nhds.symm)

omit [FiniteDimensional ℝ F] in
/-- Equal finite jets of two actual maps give equal covariant derivatives of
their raw pullback errors, with the same reference metric. The maps need only
`C^(n+1)` regularity at the specified interior point and common interior image. -/
theorem iteratedMetricCovariantDerivative_pullbackError_eq_of_map_jets
    (g : SmoothRiemannianMetric J N) (G : SmoothRiemannianMetric I M)
    {f h : M → N} {p : M} {n : ℕ}
    (hp : I.IsInteriorPoint p) (hfp : J.IsInteriorPoint (f p)) (heq : f p = h p)
    (hf : ContMDiffAt I J (n + 1) f p) (hh : ContMDiffAt I J (n + 1) h p)
    (hjets : ∀ j ≤ n + 1,
      iteratedFDeriv ℝ j (extChartAt J (f p) ∘ f ∘ (extChartAt I p).symm)
          (extChartAt I p p) =
        iteratedFDeriv ℝ j (extChartAt J (f p) ∘ h ∘ (extChartAt I p).symm)
          (extChartAt I p p)) (k : ℕ) (hk : k ≤ n) :
    iteratedMetricCovariantDerivative G 2
        (fun z : M =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace I z) ℝ).symm.toContinuousLinearMap.comp
          (localPullInner g f z - G.inner z)).uncurryLeft) k p =
      iteratedMetricCovariantDerivative G 2
        (fun z : M =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace I z) ℝ).symm.toContinuousLinearMap.comp
          (localPullInner g h z - G.inner z)).uncurryLeft) k p := by
  exact iteratedMetricCovariantDerivative_eq_of_coordinate_jets G n 2 _ _ p
    (mem_interior_iff_mem_nhds.mp hp)
    (pullbackError_model_contDiffAt g G hp hf)
    (pullbackError_model_contDiffAt g G hp hh)
    (pullbackError_model_jets_eq g G hp hfp heq hf hh hjets) k hk

omit [FiniteDimensional ℝ F] in
/-- A smooth metric realizing a finite-map pullback germ has exactly the
original raw error norms through the realized order. The original map is not
assumed infinitely smooth, and all norms use the original reference metric. -/
theorem metricDerivNorm_eq_raw_pullbackError_of_map_jets
    (g : SmoothRiemannianMetric J N) (G q : SmoothRiemannianMetric I M)
    {f h : M → N} {p : M} {n : ℕ}
    (hp : I.IsInteriorPoint p) (hfp : J.IsInteriorPoint (f p)) (heq : f p = h p)
    (hf : ContMDiffAt I J (n + 1) f p) (hh : ContMDiffAt I J (n + 1) h p)
    (hjets : ∀ j ≤ n + 1,
      iteratedFDeriv ℝ j (extChartAt J (f p) ∘ f ∘ (extChartAt I p).symm)
          (extChartAt I p p) =
        iteratedFDeriv ℝ j (extChartAt J (f p) ∘ h ∘ (extChartAt I p).symm)
          (extChartAt I p p))
    (hmetric : ∀ᶠ z in 𝓝 p, q.inner z = localPullInner g h z)
    (k : ℕ) (hk : k ≤ n) :
    metricDerivNorm k q G G p = tensor0SFiberNorm G p (2 + k)
      (iteratedMetricCovariantDerivative G 2
        (fun z : M =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace I z) ℝ).symm.toContinuousLinearMap.comp
          (localPullInner g f z - G.inner z)).uncurryLeft) k p) := by
  let A : ∀ z : M, Tensor0SSpace 2 I z := fun z =>
    ((continuousMultilinearCurryFin1 ℝ (TangentSpace I z) ℝ).symm.toContinuousLinearMap.comp
      (q.inner z - G.inner z)).uncurryLeft
  let B : ∀ z : M, Tensor0SSpace 2 I z := fun z =>
    ((continuousMultilinearCurryFin1 ℝ (TangentSpace I z) ℝ).symm.toContinuousLinearMap.comp
      (localPullInner g h z - G.inner z)).uncurryLeft
  have hgerm : tensor0SModelInChart (I := I) (M := M) 2 p A =ᶠ[𝓝 (extChartAt I p p)]
      tensor0SModelInChart (I := I) (M := M) 2 p B := by
    have hnear : ∀ᶠ y in 𝓝 (extChartAt I p p),
        q.inner ((extChartAt I p).symm y) = localPullInner g h ((extChartAt I p).symm y) := by
      apply (continuousAt_extChartAt_symm (I := I) p).tendsto.eventually
        (p := fun z : M => q.inner z = localPullInner g h z)
      simpa only [extChartAt_to_inv] using hmetric
    filter_upwards [hnear] with y hy
    let z := (extChartAt I p).symm y
    change tensor0SModelAt (I := I) (M := M) 2 p z (A z) =
      tensor0SModelAt (I := I) (M := M) 2 p z (B z)
    apply congrArg (tensor0SModelAt (I := I) (M := M) 2 p z)
    exact congrArg (fun Q : TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ =>
      (((continuousMultilinearCurryFin1 ℝ (TangentSpace I z) ℝ).symm.toContinuousLinearMap.comp
        (Q - G.inner z)).uncurryLeft : Tensor0SSpace 2 I z)) hy
  have hB := pullbackError_model_contDiffAt g G hp hh
  have hAB : iteratedMetricCovariantDerivative G 2 A k p =
      iteratedMetricCovariantDerivative G 2 B k p :=
    iteratedMetricCovariantDerivative_eq_of_coordinate_jets G n 2 A B p
      (mem_interior_iff_mem_nhds.mp hp) (hB.congr_of_eventuallyEq hgerm) hB
      (fun j _ => (hgerm.iteratedFDeriv ℝ j).self_of_nhds) k hk
  rw [metricDerivNorm_eq_iterated_inner_difference]
  change tensor0SFiberNorm G p (2 + k) (iteratedMetricCovariantDerivative G 2 A k p) = _
  rw [hAB]
  exact congrArg (tensor0SFiberNorm G p (2 + k))
    (iteratedMetricCovariantDerivative_pullbackError_eq_of_map_jets
      g G hp hfp heq hf hh hjets k hk).symm

end DifferentialGeometry.Geometry

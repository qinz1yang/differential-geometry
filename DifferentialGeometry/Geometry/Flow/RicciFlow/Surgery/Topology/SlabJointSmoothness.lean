import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabProducer

noncomputable section
open Bundle Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u
variable {P : OrientedThreeStage.{u}}

private theorem inner_chartVector_sum (g : P.Metric) (p y : P.Carrier) (v w : ThreeSpace) :
    g.inner y ((trivializationAt ThreeSpace (TangentSpace ThreeModel) p).symmL ℝ y v)
      ((trivializationAt ThreeSpace (TangentSpace ThreeModel) p).symmL ℝ y w) =
      ∑ i : Fin 3, ∑ j : Fin 3, v i * w j *
        g.inner y (P.chartVector p y i) (P.chartVector p y j) := by
  classical
  let e := trivializationAt ThreeSpace (TangentSpace ThreeModel) p
  have hv : v = ∑ i : Fin 3, v i • EuclideanSpace.single i (1 : ℝ) := by
    have h := ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.sum_repr v).symm
    convert h using 1; ext; simp
  have hw : w = ∑ i : Fin 3, w i • EuclideanSpace.single i (1 : ℝ) := by
    have h := ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.sum_repr w).symm
    convert h using 1; ext; simp
  have hev : e.symmL ℝ y v = ∑ i : Fin 3, v i • P.chartVector p y i := by
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul, chartVector, e]
  have hew : e.symmL ℝ y w = ∑ i : Fin 3, w i • P.chartVector p y i := by
    conv_lhs => rw [hw]
    simp only [map_sum, map_smul, chartVector, e]
  rw [hev, hew]
  have hL : g.inner y (∑ i : Fin 3, v i • P.chartVector p y i) =
      ∑ i : Fin 3, v i • g.inner y (P.chartVector p y i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [hL, sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_apply, smul_eq_mul, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, smul_eq_mul]
  ring

private theorem inCoordinates_metric_eq_chartVector_sum
    (g : P.Metric) (p : P.Carrier) {y : P.Carrier}
    (hy : y ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)
    (v w : ThreeSpace) :
    ContinuousLinearMap.inCoordinates ThreeSpace (TangentSpace ThreeModel)
      (ThreeSpace →L[ℝ] ℝ) (fun y : P.Carrier => TangentSpace ThreeModel y →L[ℝ] ℝ)
      p y p y (g.inner y) v w =
      ∑ i : Fin 3, ∑ j : Fin 3, v i * w j *
        g.inner y (P.chartVector p y i) (P.chartVector p y j) := by
  have hyR : y ∈ (trivializationAt ℝ (Bundle.Trivial P.Carrier ℝ) p).baseSet := mem_univ y
  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ)
    (F₁ := ThreeSpace) (F₂ := ThreeSpace) (F₃ := ℝ)
    (E₁ := TangentSpace ThreeModel) (E₂ := TangentSpace ThreeModel)
    (E₃ := Bundle.Trivial P.Carrier ℝ)
    (x₀ := p) (x := y) (ϕ := g.inner y) (v := v) (w := w) hy hy hyR]
  rw [(trivializationAt ℝ (Bundle.Trivial P.Carrier ℝ) p).coe_linearMapAt_of_mem hyR]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
  rw [← Trivialization.symmL_apply (R := ℝ) _ hy v, ← Trivialization.symmL_apply (R := ℝ) _ hy w]
  exact inner_chartVector_sum g p y v w

theorem MetricSmoothUpTo.jointContMDiffOn {g : ℝ → P.Metric} {J : Set ℝ}
    (hg : P.MetricSmoothUpTo g J) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × P.Carrier => (⟨q.2, (g q.1).inner q.2⟩ :
        TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set P.Carrier)) := by
  classical
  intro q hq
  obtain ⟨U, hU, hxU, hUb, V, hV, htV, A, hA, heq⟩ := hg q.2 q.1 hq.1
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  apply contMDiffWithinAt_clm_of_pointwise
  intro v
  apply contMDiffWithinAt_clm_of_pointwise
  intro w
  have hs : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
      (fun z : ℝ × P.Carrier => ∑ i : Fin 3, ∑ j : Fin 3, v i * w j * A z i j)
      (J ×ˢ univ) q := by
    have hlocal : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
        (fun z : ℝ × P.Carrier => ∑ i : Fin 3, ∑ j : Fin 3, v i * w j * A z i j)
        (V ×ˢ U) :=
      fun z hz => ContMDiffWithinAt.sum fun i _ =>
        ContMDiffWithinAt.sum fun j _ => contMDiffWithinAt_const.mul (hA i j z hz)
    exact (hlocal q ⟨htV, hxU⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds ((hV.prod hU).mem_nhds ⟨htV, hxU⟩))
  apply hs.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds ((hV.prod hU).mem_nhds ⟨htV, hxU⟩)] with z hz hzu
    rw [inCoordinates_metric_eq_chartVector_sum (g z.1) q.2 (hUb hzu.2)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [heq z.1 ⟨hzu.1, hz.1⟩ z.2 hzu.2 i j]
  · rw [inCoordinates_metric_eq_chartVector_sum (g q.1) q.2 (hUb hxU)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [heq q.1 ⟨htV, hq.1⟩ q.2 hxU i j]

theorem MetricSmoothUpTo.restrictOpen_jointContMDiffOn
    {g : ℝ → P.Metric} {J : Set ℝ} (hg : P.MetricSmoothUpTo g J)
    (U : TopologicalSpace.Opens P.Carrier) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × U => (⟨q.2, ((g q.1).restrictOpen U).inner q.2⟩ :
        TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set U)) := by
  let _ : IsManifold ThreeModel 1 U := IsManifold.of_le (n := ∞) (by decide)
  apply metricCLMSection_jointContMDiffOn_of_chartGram_on (I := ThreeModel)
    (fun t => (g t).restrictOpen U) J
  intro p i j
  refine chartGramMatrix_joint_contMDiffOn_of_parametric_pullback (I := ThreeModel)
    (J := ThreeModel) g J hg.jointContMDiffOn
    (fun t => (g t).restrictOpen U) (fun _ y => (y : P.Carrier))
    (contMDiff_subtype_val.comp contMDiff_snd) ?_ p i j
  intro t _ x v w
  rw [SmoothRiemannianMetric.restrictOpen_inner,
    DifferentialGeometry.mfderiv_subtype_val_apply, DifferentialGeometry.mfderiv_subtype_val_apply]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

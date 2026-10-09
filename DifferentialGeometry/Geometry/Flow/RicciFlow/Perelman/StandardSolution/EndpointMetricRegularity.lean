import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointConnection
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem nativeFrame_chart_expansion (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) (i : CoordinateIdx (𝕜 := ℝ) E) :
    coordinateFrameAt (I := I) x₀ i x = ∑ j : Fin (Module.finrank ℝ E),
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ((Module.finBasis ℝ E) i) j • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j x := by
  let e := trivializationAt E (TangentSpace I) x₀
  have he : coordinateFrameAt (I := I) x₀ i x = e.symmL ℝ x ((Module.finBasis ℝ E) i) := by
    change e.localFrame (Module.finBasis ℝ E) i x = _
    rw [e.localFrame_apply_of_mem_baseSet (b := Module.finBasis ℝ E) hx]
    unfold Bundle.Trivialization.basisAt
    rw [Module.Basis.map_apply, e.symmL_apply hx]
    rfl
  rw [he]
  conv_lhs => rw [← (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).sum_repr ((Module.finBasis ℝ E) i), map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; rfl

variable [CompleteSpace E] [T2Space M] [I.Boundaryless]
variable (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ)
  (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))

omit [CompleteSpace E] [T2Space M] [I.Boundaryless] in
include hgram in
theorem metricFrameComponents_contMDiffOn (x₀ : M)
    (idx : Fin 2 → CoordinateIdx (𝕜 := ℝ) E) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => frameComp0S (metricTensorField (g p.1))
        (coordinateFrameAt (I := I) x₀) p.2 idx)
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
  classical
  let c := fun (i : CoordinateIdx (𝕜 := ℝ) E) j =>
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ((Module.finBasis ℝ E) i) j
  have hs : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (c (idx 0) i * c (idx 1) j) * DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
    intro p hp
    exact ContMDiffWithinAt.sum fun i _ => ContMDiffWithinAt.sum fun j _ =>
      contMDiffWithinAt_const.mul (((hgram x₀ i j).mono
        (prod_mono subset_rfl (fun _ hx => chartLeviCivitaGoodSet_mem_baseSet hx))) p hp)
  apply hs.congr
  intro p hp
  change (g p.1).inner p.2 (coordinateFrameAt (I := I) x₀ (idx 0) p.2)
    (coordinateFrameAt (I := I) x₀ (idx 1) p.2) = _
  rw [nativeFrame_chart_expansion x₀ (chartLeviCivitaGoodSet_mem_baseSet hp.2),
    nativeFrame_chart_expansion x₀ (chartLeviCivitaGoodSet_mem_baseSet hp.2)]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change c (idx 1) j * (c (idx 0) i * DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j) = _
  ring

omit [CompleteSpace E] [T2Space M] [I.Boundaryless] in
private theorem constant_gram (gRef : SmoothRiemannianMetric I M)
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix gRef x₀ p.2 i j)
      ((univ : Set ℝ) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
  (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn gRef x₀ i j).comp contMDiffOn_snd (fun _ hp => hp.2)

include hgram in
theorem referenceCovariantMetricComponents_contMDiffOn (gRef : SmoothRiemannianMetric I M)
    (x₀ : M) (a : ℕ) (n : Fin (2 + a) → CoordinateIdx (𝕜 := ℝ) E) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => iterCov gRef 2 (metricTensorField (g p.1)) a p.2
        (frameTuple (coordinateFrameAt (I := I) x₀) p.2 n))
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
  have hsub : chartLeviCivitaGoodSet (I := I) x₀ ⊆ coordinateFrameSet (I := I) x₀ :=
    fun _ hx => chartLeviCivitaGoodSet_mem_baseSet hx
  have hc := iterCovComp_joint_contMDiffOn J (chartLeviCivitaGoodSet (I := I) x₀)
    (chartLeviCivitaGoodSet_isOpen (I := I) x₀) (coordinateFrameAt (I := I) x₀)
    (fun i => ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffOn i).mono hsub)
    (fun _ x => christoffelSymbolInFrame (leviCivitaConnectionOfMetric gRef)
      (coordinateFrameAt (I := I) x₀) (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x)
    (fun t => frameComp0S (metricTensorField (g t)) (coordinateFrameAt (I := I) x₀))
    (fun i j k => (connectionComponents_contMDiffOn (fun _ => gRef) univ
      (constant_gram gRef) uniqueDiffOn_univ x₀ i j k).mono (prod_mono (subset_univ J) subset_rfl))
    (metricFrameComponents_contMDiffOn g J hgram x₀) a n
  apply hc.congr
  intro p hp
  exact (iterCovComp_eq_iterCov gRef (metricTensorField (g p.1)) (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀) (coordinateFrameSet_open (I := I) x₀)
    a (hsub hp.2) n).symm

include hgram in
theorem referenceCovariantMetricNormSq_contMDiffOn (gRef : SmoothRiemannianMetric I M) (a : ℕ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => normSq0S gRef p.2 (2 + a)
        (iterCov gRef 2 (metricTensorField (g p.1)) a p.2)) (J ×ˢ (univ : Set M)) := by
  classical
  intro p hp
  let u := chartLeviCivitaGoodSet (I := I) p.2
  let frame := coordinateFrameAt (I := I) p.2
  let inv := fun q : ℝ × M => fun i j : CoordinateIdx (𝕜 := ℝ) E =>
    inverseMetricFlatModelInChartComponent gRef p.2 i j (extChartAt I p.2 q.2)
  let comp := fun q : ℝ × M => fun n : Fin (2 + a) → CoordinateIdx (𝕜 := ℝ) E =>
    iterCov gRef 2 (metricTensorField (g q.1)) a q.2 (frameTuple frame q.2 n)
  have hs : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => ∑ ns : Fin (2 + a) → CoordinateIdx (𝕜 := ℝ) E,
        ∑ ms : Fin (2 + a) → CoordinateIdx (𝕜 := ℝ) E,
          (∏ i : Fin (2 + a), inv q (ns i) (ms i)) * comp q ns * comp q ms) (J ×ˢ u) := by
    intro q hq
    refine ContMDiffWithinAt.sum fun ns _ => ContMDiffWithinAt.sum fun ms _ => ?_
    exact ((ContMDiffWithinAt.prod fun i _ =>
      ((inverseComponents_contMDiffOn (fun _ => gRef) univ (constant_gram gRef)
        p.2 (ns i) (ms i)).mono (prod_mono (subset_univ J) subset_rfl)) q hq).mul
        (referenceCovariantMetricComponents_contMDiffOn g J hgram gRef p.2 a ns q hq)).mul
        (referenceCovariantMetricComponents_contMDiffOn g J hgram gRef p.2 a ms q hq)
  have hn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => normSq0S gRef q.2 (2 + a)
        (iterCov gRef 2 (metricTensorField (g q.1)) a q.2)) (J ×ˢ u) := by
    apply hs.congr
    intro q hq
    have hx := chartLeviCivitaGoodSet_mem_baseSet hq.2
    rw [normSq0S_eq_coord gRef q.2 (2 + a) (coordinateFrameAtBasis (I := I) p.2 hx)
      (inv q) (gInvBasisAt gRef p.2 hx)]
    have hb (slots : Fin (2 + a) → CoordinateIdx (𝕜 := ℝ) E) :
        (fun j => coordinateFrameAtBasis (I := I) p.2 hx (slots j)) = frameTuple frame q.2 slots := by
      funext j
      exact coordinateFrameAt_basis_apply (I := I) p.2 hx (slots j)
    simp only [coordInner0S, tensor0SComponent_apply, hb]
    rfl
  have hx : p.2 ∈ u := self_mem_chartLeviCivitaGoodSet (I := I) p.2
  apply (hn p ⟨hp.1, hx⟩).mono_of_mem_nhdsWithin
  have hu : {q : ℝ × M | q.2 ∈ u} ∈ 𝓝 p :=
    ((chartLeviCivitaGoodSet_isOpen (I := I) p.2).preimage continuous_snd).mem_nhds hx
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hu] with q hq hqu
  exact ⟨hq.1, hqu⟩

include hgram in
theorem metricCovDerivNorm_joint_continuousOn (gRef : SmoothRiemannianMetric I M) (a : ℕ) :
    ContinuousOn (fun p : ℝ × M => metricCovDerivNorm a (g p.1) gRef p.2)
      (J ×ˢ (univ : Set M)) := by
  have hc := (referenceCovariantMetricNormSq_contMDiffOn g J hgram gRef a).continuousOn.sqrt
  apply hc.congr
  intro p _
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) gRef p.2
  have hinv : MetricInverseInBasis gRef p.2 basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I p.2)))) := by
    have hh := metricInverseInBasis_of_orthonormal gRef basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using hh i j
  exact metricCovDerivNorm_eq_iterCov (g p.1) gRef a basis hinv
end DifferentialGeometry.PDE.RicciFlow

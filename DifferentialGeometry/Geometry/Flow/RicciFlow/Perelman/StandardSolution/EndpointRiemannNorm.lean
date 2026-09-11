import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointConnection
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

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
variable (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (hJ : UniqueDiffOn ℝ J)
  (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))

include hJ hgram in
theorem riemannChartComponents_contMDiffOn (x₀ : M) (idx : Fin 4 → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => metricRm04 (g p.1) p.2
        (fun q => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (idx q) p.2))
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
  have hs : ContDiffOn ℝ ∞ (fun p : ℝ × E => ∑ l : Fin (Module.finrank ℝ E),
      chartRiemannTensor (g p.1) x₀ (idx 2) (idx 0) (idx 1) l p.2 *
        chartGramOnE (g p.1) x₀ (idx 3) l p.2)
      (J ×ˢ interior (extChartAt I x₀).target) :=
    ContDiffOn.sum fun l _ =>
      (chartRiemann_contDiffOn g J hJ hgram x₀ (idx 2) (idx 0) (idx 1) l).mul
        (chartGramOnE_set g J x₀ hgram (idx 3) l)
  apply (coordinate_model_contMDiffOn J x₀ _ hs).congr
  intro p hp
  rw [metricRm04_apply, rm04_coord_eq (g p.1) x₀ idx hp.2]
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  rw [chartGramOnE_def, (extChartAt I x₀).left_inv
    (chartLeviCivitaGoodSet_mem_extChartAt_source hp.2)]

include hJ hgram in
theorem riemannComponents_contMDiffOn (x₀ : M) (idx : Fin 4 → CoordinateIdx (𝕜 := ℝ) E) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => frameComp0S (metricRm04 (g p.1))
        (coordinateFrameAt (I := I) x₀) p.2 idx)
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
  classical
  let c := fun (i : CoordinateIdx (𝕜 := ℝ) E) j =>
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ((Module.finBasis ℝ E) i) j
  have hs : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ∑ slots : Fin 4 → Fin (Module.finrank ℝ E),
        (∏ q : Fin 4, c (idx q) (slots q)) *
          metricRm04 (g p.1) p.2 (fun q => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (slots q) p.2))
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
    intro p hp
    exact ContMDiffWithinAt.sum fun slots _ => contMDiffWithinAt_const.mul
      (riemannChartComponents_contMDiffOn g J hJ hgram x₀ slots p hp)
  apply hs.congr
  intro p hp
  let A := metricRm04 (g p.1) p.2
  change A (fun q => coordinateFrameAt (I := I) x₀ (idx q) p.2) = _
  calc
    A (fun q => coordinateFrameAt (I := I) x₀ (idx q) p.2) =
        A (fun q => ∑ j : Fin (Module.finrank ℝ E), c (idx q) j • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j p.2) := by
      congr 1
      funext q
      exact nativeFrame_chart_expansion x₀ (chartLeviCivitaGoodSet_mem_baseSet hp.2) (idx q)
    _ = ∑ slots : Fin 4 → Fin (Module.finrank ℝ E),
        A (fun q => c (idx q) (slots q) • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (slots q) p.2) :=
      A.map_sum fun q j => c (idx q) j • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j p.2
    _ = _ := by
      apply Finset.sum_congr rfl
      intro slots _
      rw [A.map_smul_univ, smul_eq_mul]

include hJ hgram in
theorem covariantRiemannComponents_contMDiffOn (x₀ : M) (a : ℕ)
    (n : Fin (4 + a) → CoordinateIdx (𝕜 := ℝ) E) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => iterCov (g p.1) 4 (metricRm04 (g p.1)) a p.2
        (frameTuple (coordinateFrameAt (I := I) x₀) p.2 n))
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
  have hsub : chartLeviCivitaGoodSet (I := I) x₀ ⊆ coordinateFrameSet (I := I) x₀ :=
    fun _ hx => chartLeviCivitaGoodSet_mem_baseSet hx
  have hc := iterCovComp_joint_contMDiffOn J (chartLeviCivitaGoodSet (I := I) x₀)
    (chartLeviCivitaGoodSet_isOpen (I := I) x₀) (coordinateFrameAt (I := I) x₀)
    (fun i => ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffOn i).mono hsub)
    (fun t x => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (g t))
      (coordinateFrameAt (I := I) x₀) (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x)
    (fun t => frameComp0S (metricRm04 (g t)) (coordinateFrameAt (I := I) x₀))
    (fun i j k => connectionComponents_contMDiffOn g J hgram hJ x₀ i j k)
    (riemannComponents_contMDiffOn g J hJ hgram x₀) a n
  apply hc.congr
  intro p hp
  exact (iterCovComp_eq_iterCov (g p.1) (metricRm04 (g p.1)) (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀) (coordinateFrameSet_open (I := I) x₀)
    a (hsub hp.2) n).symm

include hJ hgram in
theorem covariantRiemannNormSq_contMDiffOn (a : ℕ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => normSq0S (g p.1) p.2 (4 + a)
        (iterCov (g p.1) 4 (metricRm04 (g p.1)) a p.2)) (J ×ˢ (univ : Set M)) := by
  classical
  intro p hp
  let u := chartLeviCivitaGoodSet (I := I) p.2
  let frame := coordinateFrameAt (I := I) p.2
  let inv := fun q : ℝ × M => fun i j : CoordinateIdx (𝕜 := ℝ) E =>
    inverseMetricFlatModelInChartComponent (g q.1) p.2 i j (extChartAt I p.2 q.2)
  let comp := fun q : ℝ × M => fun n : Fin (4 + a) → CoordinateIdx (𝕜 := ℝ) E =>
    iterCov (g q.1) 4 (metricRm04 (g q.1)) a q.2 (frameTuple frame q.2 n)
  have hs : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => ∑ ns : Fin (4 + a) → CoordinateIdx (𝕜 := ℝ) E,
        ∑ ms : Fin (4 + a) → CoordinateIdx (𝕜 := ℝ) E,
          (∏ i : Fin (4 + a), inv q (ns i) (ms i)) * comp q ns * comp q ms) (J ×ˢ u) := by
    intro q hq
    refine ContMDiffWithinAt.sum fun ns _ => ContMDiffWithinAt.sum fun ms _ => ?_
    exact ((ContMDiffWithinAt.prod fun i _ =>
      inverseComponents_contMDiffOn g J hgram p.2 (ns i) (ms i) q hq).mul
        (covariantRiemannComponents_contMDiffOn g J hJ hgram p.2 a ns q hq)).mul
        (covariantRiemannComponents_contMDiffOn g J hJ hgram p.2 a ms q hq)
  have hn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => normSq0S (g q.1) q.2 (4 + a)
        (iterCov (g q.1) 4 (metricRm04 (g q.1)) a q.2)) (J ×ˢ u) := by
    apply hs.congr
    intro q hq
    have hx := chartLeviCivitaGoodSet_mem_baseSet hq.2
    rw [normSq0S_eq_coord (g q.1) q.2 (4 + a) (coordinateFrameAtBasis (I := I) p.2 hx)
      (inv q) (gInvBasisAt (g q.1) p.2 hx)]
    have hb (slots : Fin (4 + a) → CoordinateIdx (𝕜 := ℝ) E) :
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
end DifferentialGeometry.PDE.RicciFlow

import DifferentialGeometry.Topology.Compactness.SublevelComponents
import DifferentialGeometry.Topology.Morse.ExtremumIndex
import DifferentialGeometry.Topology.Morse.CriticalExtrema

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]

theorem exists_index_zero_mem_connectedComponentIn_lt
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : IsCompact {x | f x ≤ a})
    (hnd : ∀ p, f p < a → IsCriticalPointAt I f p → IsNondegenerateCriticalPointAt I f p)
    {x : M} (hx : f x < a) :
    ∃ p ∈ connectedComponentIn {y | f y < a} x,
      IsLocalMin f p ∧ IsCriticalPointAt I f p ∧
        sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = 0 := by
  let : LocallyConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyConnectedSpace
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  obtain ⟨p, hp, _, hmin⟩ := hf.continuous.exists_isLocalMin_mem_connectedComponentIn_lt ha hx
  have hpc := isCriticalPointAt_of_isLocalMin (I := I) hmin BoundarylessManifold.isInteriorPoint
  have hpa : f p < a := connectedComponentIn_subset {y | f y < a} x hp
  exact ⟨p, hp, hmin, hpc, minimum_morse_index_eq_zero hf (hnd p hpa hpc) hmin⟩

theorem exists_embedding_connectedComponents_lt_index_zero
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : IsCompact {x | f x ≤ a})
    (hnd : ∀ p, f p < a → IsCriticalPointAt I f p → IsNondegenerateCriticalPointAt I f p) :
    ∃ ι : ConnectedComponents {x : M // f x < a} ↪
        {p : M // f p < a ∧ IsCriticalPointAt I f p ∧
          sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = 0},
      ∀ C, ConnectedComponents.mk (⟨(ι C).val, (ι C).property.1⟩ : {x : M // f x < a}) = C := by
  let : LocallyConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyConnectedSpace
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  obtain ⟨j, hj⟩ := hf.continuous.exists_embedding_connectedComponents_lt_localMin ha
  have hlocal (p : {p : M // f p < a ∧ IsLocalMin f p}) :
      IsCriticalPointAt I f p.val ∧ sigNeg (chartHessianAt
        (fun y => f ((extChartAt I p.val).symm y)) (extChartAt I p.val p.val)) = 0 := by
    have hc := isCriticalPointAt_of_isLocalMin (I := I) p.property.2
      BoundarylessManifold.isInteriorPoint
    exact ⟨hc, minimum_morse_index_eq_zero hf (hnd p.val p.property.1 hc) p.property.2⟩
  refine ⟨⟨fun C => ⟨(j C).val, (j C).property.1, hlocal (j C)⟩, ?_⟩, hj⟩
  intro C D hCD
  apply j.injective
  apply Subtype.ext
  exact congrArg (fun p : {p : M // f p < a ∧ IsCriticalPointAt I f p ∧
    sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = 0} =>
      p.val) hCD

theorem isPreconnected_lt_of_subsingleton_index_zero
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : IsCompact {x | f x ≤ a})
    (hnd : ∀ p, f p < a → IsCriticalPointAt I f p → IsNondegenerateCriticalPointAt I f p)
    (hzero : {p | f p < a ∧ IsCriticalPointAt I f p ∧ sigNeg (chartHessianAt
      (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = 0}.Subsingleton) :
    IsPreconnected {x | f x < a} := by
  let : LocallyConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyConnectedSpace
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  apply hf.continuous.isPreconnected_lt_of_subsingleton_localMin ha
  intro p hp q hq
  have hpc := isCriticalPointAt_of_isLocalMin (I := I) hp.2 BoundarylessManifold.isInteriorPoint
  have hqc := isCriticalPointAt_of_isLocalMin (I := I) hq.2 BoundarylessManifold.isInteriorPoint
  exact hzero ⟨hp.1, hpc, minimum_morse_index_eq_zero hf (hnd p hp.1 hpc) hp.2⟩
    ⟨hq.1, hqc, minimum_morse_index_eq_zero hf (hnd q hq.1 hqc) hq.2⟩

theorem exists_index_finrank_mem_connectedComponentIn_gt
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : IsCompact {x | a ≤ f x})
    (hnd : ∀ p, a < f p → IsCriticalPointAt I f p → IsNondegenerateCriticalPointAt I f p)
    {x : M} (hx : a < f x) :
    ∃ p ∈ connectedComponentIn {y | a < f y} x,
      IsLocalMax f p ∧ IsCriticalPointAt I f p ∧
        sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) =
          Module.finrank ℝ E := by
  let : LocallyConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyConnectedSpace
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  obtain ⟨p, hp, _, hmax⟩ := hf.continuous.exists_isLocalMax_mem_connectedComponentIn_gt ha hx
  have hpc := isCriticalPointAt_of_isLocalMax (I := I) hmax BoundarylessManifold.isInteriorPoint
  have hpa : a < f p := connectedComponentIn_subset {y | a < f y} x hp
  exact ⟨p, hp, hmax, hpc, maximum_morse_index_eq_finrank hf (hnd p hpa hpc) hmax⟩

theorem isPreconnected_gt_of_subsingleton_index_finrank
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : IsCompact {x | a ≤ f x})
    (hnd : ∀ p, a < f p → IsCriticalPointAt I f p → IsNondegenerateCriticalPointAt I f p)
    (hmax : {p | a < f p ∧ IsCriticalPointAt I f p ∧ sigNeg (chartHessianAt
      (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) =
        Module.finrank ℝ E}.Subsingleton) :
    IsPreconnected {x | a < f x} := by
  let : LocallyConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyConnectedSpace
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  apply hf.continuous.isPreconnected_gt_of_subsingleton_localMax ha
  intro p hp q hq
  have hpc := isCriticalPointAt_of_isLocalMax (I := I) hp.2 BoundarylessManifold.isInteriorPoint
  have hqc := isCriticalPointAt_of_isLocalMax (I := I) hq.2 BoundarylessManifold.isInteriorPoint
  exact hmax ⟨hp.1, hpc, maximum_morse_index_eq_finrank hf (hnd p hp.1 hpc) hp.2⟩
    ⟨hq.1, hqc, maximum_morse_index_eq_finrank hf (hnd q hq.1 hqc) hq.2⟩

end DifferentialGeometry.Topology.Morse

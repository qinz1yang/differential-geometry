import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.HalfBandSeparation
import DifferentialGeometry.Geometry.Neck.HalfBandVolume
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreMaps
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Topology.Manifold.LocallyPathConnected

noncomputable section

open Set Function TopologicalSpace Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Neck

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] {ι : Type*} [Finite ι] {δ : ι → ℝ}
  (U : Opens M) (g : SmoothRiemannianMetric I U)
  (x₀ : ι → U) (order : ι → ℕ) (d : ∀ i, normalizedDatum g (x₀ i) (δ i) (order i))
  (f : ∀ i, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hOriginal : ∀ i, f i = neckAmbientMap U (d i))
  (R : Set (ConnectedComponents (cutCore f)))
  (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)

private local instance : MeasurableSpace U := borel U
private local instance : BorelSpace U := ⟨rfl⟩

include hf hdisj hOriginal in
theorem retained_core_add_negative_bands_volume_le
    (hδ : ∀ i, δ i ≤ 1 / 4)
    (hneg : ∀ i, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hdisj (i, false) ∉ R) :
    let : SecondCountableTopology H := I.secondCountableTopology
    let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    let : LocallyPathConnectedSpace M :=
      DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
    riemannianVolumeMeasure I U g (range (retainedCoreDomainMap f R U hRet)) +
      ∑' i : ι, ENNReal.ofReal (2 * Real.pi / δ i) *
        ENNReal.ofReal ((metricScalarAt g (x₀ i)) ^ (-3 / 2 : ℝ)) ≤
      riemannianVolumeMeasure I U g
        (range (retainedCoreDomainMap f R U hRet) ∪
          ⋃ i : ι, (d i).map '' {q | q.val.2 ∈ Icc (-(δ i)⁻¹) (-1 : ℝ)}) := by
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let : LocallyPathConnectedSpace M :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  dsimp only
  let C := range (retainedCoreDomainMap f R U hRet)
  let B := fun i : ι => (d i).map '' {q : bufferedCylinder (δ i) |
    q.val.2 ∈ Icc (-(δ i)⁻¹) (-1 : ℝ)}
  let μ := riemannianVolumeMeasure I U g
  have hcompact (i : ι) : IsCompact (B i) :=
    isCompact_negative_closed_half_band_image (d i).precision_pos (d i).map (d i).smooth.continuous
  have hd : Pairwise fun i j => Disjoint (B i) (B j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro x ⟨q, _, hq⟩ ⟨r, _, hr⟩
    apply disjoint_left.mp (hdisj hij) (mem_range_self q)
    refine ⟨r, ?_⟩
    rw [hOriginal i, hOriginal j]
    exact congrArg Subtype.val (hr.trans hq.symm)
  have hc (i : ι) : Disjoint C (B i) := by
    apply disjoint_left.mpr
    rintro x ⟨p, hp⟩ ⟨q, hq, heq⟩
    have hsep := negative_closed_half_band_image_disjoint_retainedCore
      (fun j => (d j).precision_pos) f hf hdisj R i (hneg i)
    apply disjoint_left.mp hsep ⟨q, hq, rfl⟩
    refine ⟨p.val, p.property, ?_⟩
    rw [hOriginal i]
    exact congrArg Subtype.val (hp.trans heq.symm)
  have hcu : Disjoint C (⋃ i, B i) := disjoint_iUnion_right.mpr hc
  have hbmeas : MeasurableSet (⋃ i, B i) := MeasurableSet.iUnion fun i => (hcompact i).measurableSet
  have hadd : μ (C ∪ ⋃ i, B i) = μ C + ∑' i, μ (B i) := by
    rw [measure_union hcu hbmeas, measure_iUnion hd (fun i => (hcompact i).measurableSet)]
  change μ C + _ ≤ μ (C ∪ ⋃ i, B i)
  rw [hadd]
  apply add_le_add_right
  apply ENNReal.tsum_le_tsum
  intro i
  exact (d i).negative_closed_band_volume_ge (hδ i)

include hf hdisj in
omit [SigmaCompactSpace M] in
theorem isCompact_retained_core_union_negative_bands [CompactSpace M] :
    let : LocallyPathConnectedSpace M :=
      DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
    IsCompact (range (retainedCoreDomainMap f R U hRet) ∪
      ⋃ i : ι, (d i).map '' {q | q.val.2 ∈ Icc (-(δ i)⁻¹) (-1 : ℝ)}) := by
  let : LocallyPathConnectedSpace M :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  let : CompactSpace (retainedCore f R) := isCompact_iff_compactSpace.mp
    (isCompact_retained_discardedCore (fun i => (d i).precision_pos) f hf hdisj R).1
  have hc : Continuous (retainedCoreDomainMap f R U hRet) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  apply (isCompact_range hc).union
  apply isCompact_iUnion
  intro i
  exact isCompact_negative_closed_half_band_image (d i).precision_pos (d i).map (d i).smooth.continuous

end DifferentialGeometry.Geometry.Neck

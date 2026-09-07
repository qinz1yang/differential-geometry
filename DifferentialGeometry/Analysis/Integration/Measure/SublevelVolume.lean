import DifferentialGeometry.Analysis.Integration.Measure.OpenSubtype
import DifferentialGeometry.Analysis.Integration.Measure.Boundary
import DifferentialGeometry.Geometry.Boundary.SublevelMetric

namespace DifferentialGeometry.Topology.Morse

open Manifold Set MeasureTheory
open Integral.Measure Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]

private def strictSublevelOpen (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    TopologicalSpace.Opens M := ⟨{x | f x < a}, isOpen_lt hf.continuous continuous_const⟩

private def strictSublevelInclusion (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) : strictSublevelOpen I f a hf → SublevelSpace f a :=
  fun x => ⟨x.1, le_of_lt (show f x.1 < a from x.2)⟩

omit [I.Boundaryless] [IsManifold I ∞ M] in
private theorem strictSublevelInclusion_isOpenEmbedding (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    _root_.Topology.IsOpenEmbedding (strictSublevelInclusion I f a hf) := by
  change _root_.Topology.IsOpenEmbedding
    (Set.inclusion (show (strictSublevelOpen I f a hf : Set M) ⊆ sublevel f a from
      fun x hx => le_of_lt (show f x < a from hx)))
  apply _root_.Topology.IsOpenEmbedding.inclusion
  exact (isOpen_lt hf.continuous continuous_const).preimage continuous_subtype_val

private theorem contMDiff_strictSublevelInclusion (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    ContMDiff I (modelWithCornersEuclideanHalfSpace (m + 1)) ∞
      (strictSublevelInclusion I f a hf) := by
  let := manifoldSublevelChartedSpace I f a hf hreg
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  have hs := contMDiff_sublevelCorestrict I f a hf hreg
    (Subtype.val : strictSublevelOpen I f a hf → M) contMDiff_subtype_val
    (fun x => le_of_lt x.2)
  exact (manifoldSublevelEuclideanDiffeomorph I f a hf hreg).contMDiff.comp hs

private def strictSublevelPartialDiffeomorph (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (hU : Nonempty (strictSublevelOpen I f a hf)) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    PartialDiffeomorph I (modelWithCornersEuclideanHalfSpace (m + 1))
      (strictSublevelOpen I f a hf) (SublevelSpace f a) 1 := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let := hU
  let e := (strictSublevelInclusion_isOpenEmbedding I f a hf).toOpenPartialHomeomorph
    (strictSublevelInclusion I f a hf)
  refine
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := ?_
      contMDiffOn_invFun := ?_ }
  · exact ((contMDiff_strictSublevelInclusion I f a hf hreg).of_le (by norm_num)).contMDiffOn
  · intro x hx
    have hs : ContMDiffAt (modelWithCornersEuclideanHalfSpace (m + 1)) I ∞ e.symm x := by
      apply (ContMDiffAt.subtypeVal_comp_iff (strictSublevelOpen I f a hf) _ x).mp
      apply (contMDiff_manifoldSublevelEuclideanInclusion I f a hf hreg x).congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds hx] with y hy
      exact congrArg Subtype.val (e.right_inv hy)
    exact hs.contMDiffWithinAt.of_le (by norm_num)

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance (f : M → ℝ) (a : ℝ) : MeasurableSpace (SublevelSpace f a) :=
  borel (SublevelSpace f a)
private local instance (f : M → ℝ) (a : ℝ) : BorelSpace (SublevelSpace f a) := ⟨rfl⟩
private local instance (U : TopologicalSpace.Opens M) : MeasurableSpace U := borel U
private local instance (U : TopologicalSpace.Opens M) : BorelSpace U := ⟨rfl⟩

theorem map_riemannianVolumeMeasure_sublevelMetric_eq_restrict_lt
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    letI : SigmaCompactSpace (SublevelSpace f a) :=
      (isClosed_le hf.continuous continuous_const).sigmaCompactSpace
    Measure.map (Subtype.val : SublevelSpace f a → M)
      (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace (m + 1))
        (M := SublevelSpace f a) (sublevelMetric I g f a hf hreg)) =
      (riemannianVolumeMeasure (I := I) (M := M) g).restrict {x | f x < a} := by
  classical
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let := manifoldSublevelEuclidean_isManifold I f a hf hreg
  let : SigmaCompactSpace (SublevelSpace f a) :=
    (isClosed_le hf.continuous continuous_const).sigmaCompactSpace
  let U := strictSublevelOpen I f a hf
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let J := modelWithCornersEuclideanHalfSpace (m + 1)
  let gs := sublevelMetric I g f a hf hreg
  let μ := riemannianVolumeMeasure (I := J) (M := SublevelSpace f a) gs
  have hb : μ (J.boundary (SublevelSpace f a)) = 0 :=
    riemannianVolumeMeasure_boundary_eq_zero gs
  have hae : ∀ᵐ x ∂μ, f x.1 < a := by
    rw [ae_iff]
    have he : {x : SublevelSpace f a | ¬ f x.1 < a} = J.boundary (SublevelSpace f a) := by
      ext x
      change (¬ f x.1 < a) ↔ J.IsBoundaryPoint x
      rw [manifoldSublevelEuclidean_isBoundaryPoint_iff I f a hf hreg]
      exact ⟨fun h => le_antisymm x.2 (le_of_not_gt h), fun h => by rw [h]; exact lt_irrefl a⟩
    rw [he]
    exact hb
  by_cases hU : Nonempty U
  · let Φ := strictSublevelPartialDiffeomorph I f a hf hreg hU
    have hs : Φ.source = Set.univ := by simp [Φ, strictSublevelPartialDiffeomorph]
    have ht : Φ.target = {x : SublevelSpace f a | f x.1 < a} := by
      dsimp only [Φ, strictSublevelPartialDiffeomorph]
      rw [_root_.Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x.1, hx⟩, rfl⟩
    have hm : ∀ x ∈ Φ.source, ∀ v w, (g.restrictOpen U).inner x v w =
        gs.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w) := by
      intro x _ v w
      have hi := (contMDiff_manifoldSublevelEuclideanInclusion I f a hf hreg (Φ x)).mdifferentiableAt
        (by simp)
      have hΦ := (contMDiff_strictSublevelInclusion I f a hf hreg x).mdifferentiableAt (by simp)
      have hc := mfderiv_comp x hi hΦ
      change mfderiv I I (Subtype.val : U → M) x =
        (mfderiv J I (Subtype.val : SublevelSpace f a → M) (Φ x)).comp (mfderiv I J Φ x) at hc
      rw [mfderiv_subtype_val] at hc
      have hv := congrArg (fun L => L v) hc
      have hw := congrArg (fun L => L w) hc
      change g.inner x.1 v w = g.inner x.1 _ _
      exact congrArg₂ (fun v w => g.inner x.1 v w) hv hw
    have hres : μ.restrict Φ.target = μ := by
      apply Measure.restrict_eq_self_of_ae_mem
      simpa only [ht, Set.mem_ofPred_eq] using hae
    have hv := riemannianVolumeMeasure_partialIsometry (g.restrictOpen U) gs Φ hm
    rw [hs, Measure.restrict_univ] at hv
    change riemannianVolumeMeasure (I := I) (M := U) (g.restrictOpen U) =
      Measure.map Φ.symm (μ.restrict Φ.target) at hv
    rw [hres] at hv
    have hi : AEMeasurable Φ.symm μ := by
      have hi' : AEMeasurable Φ.symm (μ.restrict Φ.target) :=
        Φ.contMDiffOn_invFun.continuousOn.aemeasurable Φ.open_target.measurableSet
      rwa [hres] at hi'
    have hopen := map_riemannianVolumeMeasure_restrictOpen g U
    rw [hv, AEMeasurable.map_map_of_aemeasurable
      continuous_subtype_val.measurable.aemeasurable hi] at hopen
    refine Eq.trans ?_ hopen
    apply Measure.map_congr
    filter_upwards [hae] with x hx
    exact (congrArg Subtype.val
      (Φ.toPartialEquiv.right_inv (by simpa only [ht, Set.mem_ofPred_eq] using hx))).symm
  · have hstrict : {x : M | f x < a} = ∅ := by
      ext x
      exact ⟨fun hx => hU ⟨⟨x, hx⟩⟩, fun hx => hx.elim⟩
    have hz : μ = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      have he : J.boundary (SublevelSpace f a) = Set.univ := by
        ext x
        simp only [Set.mem_univ, iff_true]
        apply (manifoldSublevelEuclidean_isBoundaryPoint_iff I f a hf hreg x).mpr
        apply le_antisymm x.2
        exact le_of_not_gt (fun hx => hU ⟨⟨x.1, hx⟩⟩)
      rwa [he] at hb
    change Measure.map (Subtype.val : SublevelSpace f a → M) μ = _
    rw [hz, Measure.map_zero]
    exact (show (riemannianVolumeMeasure (I := I) (M := M) g).restrict {x | f x < a} = 0 by
      rw [hstrict, Measure.restrict_empty]).symm

end

end DifferentialGeometry.Topology.Morse

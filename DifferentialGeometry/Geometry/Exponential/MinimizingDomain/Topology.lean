import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

private local instance tangentSpaceNormedAddCommGroup
    (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceInnerProductSpace
    (x : M) : InnerProductSpace ℝ (TangentSpace I x) :=
  Bundle.instInnerProductSpaceReal (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceNormedSpace
    (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance

variable [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem isClosed_preimage_minimizingDomain
    (g : SmoothRiemannianMetric I M) (p : M) :
    IsClosed (Subtype.val ⁻¹' minimizingDomain (I := I) g p :
      Set (show Set E from expDomain (I := I) g p)) := by
  let : T2Space M := gauss_t2Space_base I
  have hleft : Continuous (fun v : E => ENNReal.ofReal
      (Real.sqrt (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v)))) := by
    apply ENNReal.continuous_ofReal.comp
    apply Real.continuous_sqrt.comp
    with_unfolding_all exact continuous_gInner_self (I := I) g p
  have hexp : Continuous (fun v : (show Set E from expDomain (I := I) g p) =>
      expMap (I := I) g p (show TangentSpace I p from (v : E))) :=
    (contMDiffOn_expMap (I := I) g p).continuousOn.domRestrict
  have hdist : Continuous (fun q : M => riemannianEDist I p q) := by
    let : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I
    let : RegularSpace M := inferInstance
    let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    exact continuous_const.edist continuous_id
  exact isClosed_eq (hleft.comp continuous_subtype_val) (hdist.comp hexp)

theorem isCompact_minimizingDomain_inter
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKdom : K ⊆ expDomain (I := I) g p) :
    IsCompact (minimizingDomain (I := I) g p ∩ K) := by
  let f : K → (show Set E from expDomain (I := I) g p) :=
    fun v => ⟨(v : E), hKdom v.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hclosed : IsClosed {v : K | (v : E) ∈ minimizingDomain (I := I) g p} :=
    (isClosed_preimage_minimizingDomain (I := I) g p).preimage hf
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcpt := hclosed.isCompact.image continuous_subtype_val
  convert hcpt using 1
  ext v
  constructor
  · intro hv
    exact ⟨⟨v, hv.2⟩, hv.1, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw, w.property⟩

theorem isSigmaCompact_minimizingDomain
    (g : SmoothRiemannianMetric I M) (p : M) :
    IsSigmaCompact (minimizingDomain (I := I) g p) := by
  have hopen : IsOpen (show Set E from expDomain (I := I) g p) :=
    isOpen_expDomain (I := I) g p
  let : LocallyCompactSpace (show Set E from expDomain (I := I) g p) :=
    hopen.locallyCompactSpace
  have hsig : IsSigmaCompact (Subtype.val ⁻¹' minimizingDomain (I := I) g p :
      Set (show Set E from expDomain (I := I) g p)) :=
    isSigmaCompact_univ.of_isClosed_subset
      (isClosed_preimage_minimizingDomain (I := I) g p) (subset_univ _)
  have himage := hsig.image continuous_subtype_val
  convert himage using 1
  ext v
  constructor
  · intro hv
    exact ⟨⟨v, minimizingDomain_subset_expDomain (I := I) g p hv⟩, hv, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact hw

variable [MeasurableSpace E] [BorelSpace E]

theorem measurableSet_minimizingDomain
    (g : SmoothRiemannianMetric I M) (p : M) :
    MeasurableSet (minimizingDomain (I := I) g p) := by
  have hmeas := (isClosed_preimage_minimizingDomain (I := I) g p).measurableSet
  have hUopen : IsOpen (show Set E from expDomain (I := I) g p) :=
    isOpen_expDomain (I := I) g p
  have hU : MeasurableSet (show Set E from expDomain (I := I) g p) :=
    hUopen.measurableSet
  have himage : MeasurableSet (((↑) : (show Set E from expDomain (I := I) g p) → E) ''
      (Subtype.val ⁻¹' minimizingDomain (I := I) g p)) := hU.subtype_image hmeas
  convert himage using 1
  ext v
  constructor
  · intro hv
    exact ⟨⟨v, minimizingDomain_subset_expDomain (I := I) g p hv⟩, hv, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact hw

theorem measurableSet_extendibleMinimizingDomain
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    MeasurableSet (extendibleMinimizingDomain (I := I) g p) := by
  let Q : Set ℚ := {q | (1 : ℝ) < (q : ℝ)}
  let A : ℚ → Set E := fun q =>
    (fun v : E => (q : ℝ) • v) ⁻¹' minimizingDomain (I := I) g p
  have hA (q : ℚ) : MeasurableSet (A q) :=
    (measurableSet_minimizingDomain (I := I) g p).preimage
      (continuous_const_smul (q : ℝ)).measurable
  have heq : extendibleMinimizingDomain (I := I) g p = ⋃ q ∈ Q, A q := by
    ext v
    constructor
    · rintro ⟨c, hc, hcv⟩
      obtain ⟨q : ℚ, hq1, hqc⟩ := exists_rat_btwn hc
      have hqpos : 0 < (q : ℝ) := zero_lt_one.trans hq1
      refine mem_iUnion₂.mpr ⟨q, hq1, ?_⟩
      apply extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p
      refine ⟨c / (q : ℝ), (one_lt_div hqpos).mpr hqc, ?_⟩
      simpa only [smul_smul, div_mul_cancel₀ _ hqpos.ne'] using hcv
    · intro hv
      obtain ⟨q, hq, hqv⟩ := mem_iUnion₂.mp hv
      exact ⟨(q : ℝ), hq, hqv⟩
  rw [heq]
  exact MeasurableSet.biUnion (Set.to_countable Q) fun q _ => hA q

end DifferentialGeometry.Geometry.Riemannian.Exponential

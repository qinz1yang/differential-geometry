import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertionNorm
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FixedRegions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold IsManifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

def modelWindow (R : ℝ) : Opens E3 :=
  ⟨{x | ‖x‖ < R}, isOpen_lt continuous_norm continuous_const⟩

theorem modelWindow_eq_intrinsic (R : ℝ) :
    (modelWindow R : Set E3) = {x | (riemannianEDistOf metric 0 x).toReal < R} := by
  ext x
  change ‖x‖ < R ↔ (riemannianEDistOf metric 0 x).toReal < R
  rw [distance_zero]

theorem modelWindow_le_insertionBall {R B : ℝ} (hfit : R ≤ transitionEnd + B) :
    modelWindow R ≤ insertionBall B := fun _ hx => hx.trans_le hfit

def modelWindowMap {R B : ℝ} (hB : 0 < B) (hfit : R ≤ transitionEnd + B) :
    modelWindow R → InsertionQuotient hB :=
  (radialCapAttachmentDiffeomorph transitionEnd_pos hB).symm ∘
    Opens.inclusion (modelWindow_le_insertionBall hfit)

theorem modelWindowMap_realization {R B : ℝ} (hB : 0 < B) (hfit : R ≤ transitionEnd + B)
    (x : modelWindow R) :
    radialCapAttachmentDiffeomorph transitionEnd_pos hB (modelWindowMap hB hfit x) =
      Opens.inclusion (modelWindow_le_insertionBall hfit) x :=
  (radialCapAttachmentDiffeomorph transitionEnd_pos hB).apply_symm_apply _

private theorem restrictedChart_mem_maximalAtlas (U : Opens E3) (hU : Nonempty U)
    (e : OpenPartialHomeomorph E3 E3) (he : e ∈ maximalAtlas (𝓡 3) ∞ E3) :
    e.subtypeRestr hU ∈ maximalAtlas (𝓡 3) ∞ U := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e ∘ (Subtype.val : U → E3))
      (e.subtypeRestr hU).source
    exact (contMDiffOn_of_mem_maximalAtlas he).comp
      (contMDiff_subtype_val (U := U)).contMDiffOn
      (fun x hx => by simpa only [e.subtypeRestr_source hU] using hx)
  · intro z hz
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U (e.subtypeRestr hU).symm
      (e.subtypeRestr hU).target z).mp
    apply ((contMDiffOn_symm_of_mem_maximalAtlas he).mono
      (e.subtypeRestr_target_subset hU)).congr
      (fun w hw => e.subtypeRestr_symm_apply hU hw) z hz

private theorem smoothEmbedding_into_open
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (U : Opens E3) (f : M → U)
    (hf : IsSmoothEmbedding I (𝓡 3) ∞ (fun x => (f x : E3))) :
    IsSmoothEmbedding I (𝓡 3) ∞ f := by
  refine ⟨?_, (_root_.Topology.IsEmbedding.subtypeVal.of_comp_iff).mp hf.isEmbedding⟩
  obtain ⟨F, hF, hF', hfimm⟩ := hf.isImmersion
  let := hF
  let := hF'
  refine ⟨F, hF, hF', ?_⟩
  intro x
  let h := hfimm x
  have hU : Nonempty U := ⟨f x⟩
  let c := h.codChart.subtypeRestr hU
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    (show ContinuousAt f x from (continuous_induced_rng.mpr hf.contMDiff.continuous).continuousAt)
    h.equiv h.domChart c h.mem_domChart_source ?_ h.domChart_mem_maximalAtlas
    (restrictedChart_mem_maximalAtlas U hU h.codChart h.codChart_mem_maximalAtlas) ?_
  · simpa only [c, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using h.mem_codChart_source
  · exact h.writtenInCharts

private theorem smoothEmbedding_into_attachment {B : ℝ} (hB : 0 < B)
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (f : M → InsertionQuotient hB)
    (hf : IsSmoothEmbedding I (𝓡 3) ∞
      (radialCapAttachmentHomeomorph transitionEnd_pos hB ∘ f : M → insertionBall B)) :
    letI := radialCapAttachmentChartedSpace transitionEnd_pos hB
    IsSmoothEmbedding I (𝓡 3) ∞ f := by
  let := radialCapAttachmentChartedSpace transitionEnd_pos hB
  let := radialCapAttachment_isManifold transitionEnd_pos hB
  let d := radialCapAttachmentDiffeomorph transitionEnd_pos hB
  refine ⟨?_, ((radialCapAttachmentHomeomorph transitionEnd_pos hB).isEmbedding.of_comp_iff).mp hf.isEmbedding⟩
  obtain ⟨F, hF, hF', hfimm⟩ := hf.isImmersion
  let := hF
  let := hF'
  refine ⟨F, hF, hF', ?_⟩
  intro x
  let h := hfimm x
  let c := d.toHomeomorph.toOpenPartialHomeomorph.trans h.codChart
  have hc : c ∈ maximalAtlas (𝓡 3) ∞ (InsertionQuotient hB) := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        d.contMDiff.contMDiffOn (fun _ hy => hy.2)
    · change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (d.symm ∘ h.codChart.symm) c.target
      have hd : ContMDiffOn (𝓡 3) (𝓡 3) ∞ d.symm univ := d.symm.contMDiff.contMDiffOn
      exact hd.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mono
          (fun _ hy => hy.1)) (fun _ _ => mem_univ _)
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    (show ContinuousAt f x from
      ((radialCapAttachmentHomeomorph transitionEnd_pos hB).isEmbedding.continuous_iff.mpr
        hf.contMDiff.continuous).continuousAt)
    h.equiv h.domChart c h.mem_domChart_source ⟨mem_univ _, h.mem_codChart_source⟩
    h.domChart_mem_maximalAtlas hc ?_
  exact h.writtenInCharts

theorem isSmoothEmbedding_modelWindowMap {R B : ℝ} (hB : 0 < B)
    (hfit : R ≤ transitionEnd + B) :
    IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (modelWindowMap hB hfit) := by
  apply smoothEmbedding_into_attachment hB
  have he : (radialCapAttachmentHomeomorph transitionEnd_pos hB ∘ modelWindowMap hB hfit :
      modelWindow R → insertionBall B) = Opens.inclusion (modelWindow_le_insertionBall hfit) :=
    funext (modelWindowMap_realization hB hfit)
  rw [he]
  apply smoothEmbedding_into_open (insertionBall B)
  exact IsSmoothEmbedding.of_opens (modelWindow R)

theorem modelWindowMap_mfderiv_realization {R B : ℝ} (hB : 0 < B)
    (hfit : R ≤ transitionEnd + B) (x : modelWindow R) (v : TangentSpace (𝓡 3) x) :
    mfderiv (𝓡 3) (𝓡 3) (radialCapAttachmentDiffeomorph transitionEnd_pos hB)
      (modelWindowMap hB hfit x) (mfderiv (𝓡 3) (𝓡 3) (modelWindowMap hB hfit) x v) = v := by
  let e := radialCapAttachmentDiffeomorph transitionEnd_pos hB
  have hj := (isSmoothEmbedding_modelWindowMap hB hfit).contMDiff
  have he : (e ∘ modelWindowMap hB hfit : modelWindow R → insertionBall B) =
      Opens.inclusion (modelWindow_le_insertionBall hfit) :=
    funext (modelWindowMap_realization hB hfit)
  have hd := mfderiv_comp_apply x (e.contMDiff.mdifferentiableAt (by decide))
    (hj.mdifferentiableAt (by decide)) v
  erw [he, mfderiv_opens_incl] at hd
  exact hd.symm

theorem modelWindowMap_isLocalDiffeomorph {R B : ℝ} (hB : 0 < B)
    (hfit : R ≤ transitionEnd + B) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (modelWindowMap hB hfit) := by
  apply isLocalDiffeomorph_of_injective_mfderiv _ (isSmoothEmbedding_modelWindowMap hB hfit).contMDiff
  · intro x v w he
    have hv := modelWindowMap_mfderiv_realization hB hfit x v
    have hw := modelWindowMap_mfderiv_realization hB hfit x w
    rw [he] at hv
    exact hv.symm.trans hw
  · rfl

theorem modelWindowMap_agrees_cap {R B : ℝ} (hB : 0 < B) (hfit : R ≤ transitionEnd + B)
    (x : {x : E3 // ‖x‖ ≤ transitionEnd}) (hx : ‖x.val‖ < R) :
    modelWindowMap hB hfit ⟨x.val, hx⟩ =
      adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB) x := by
  apply (radialCapAttachmentDiffeomorph transitionEnd_pos hB).injective
  erw [modelWindowMap_realization]
  apply Subtype.ext
  rfl

theorem fixed_deep_mem_modelWindow (A D : ℝ) (hD : 0 < D) :
    deepRegion A ⊆ modelWindow (D + 1) := by
  intro x hx
  have hd := (fixed_radii_bounds A).2.2.1.trans_le (min_le_left _ _)
  exact hx.trans_lt (hd.trans (by linarith))

theorem modelWindowMap_restrict {R S B : ℝ} (hB : 0 < B) (hRS : R ≤ S)
    (hfit : S ≤ transitionEnd + B) (x : modelWindow R) :
    modelWindowMap hB hfit (⟨x.val, x.property.trans_le hRS⟩ : modelWindow S) =
      modelWindowMap hB (hRS.trans hfit) x := rfl

def modelWindowPullback {R B : ℝ} (hB : 0 < B) (hfit : R ≤ transitionEnd + B)
    (g : SmoothRiemannianMetric (𝓡 3) (InsertionQuotient hB)) :
    SmoothRiemannianMetric (𝓡 3) (modelWindow R) :=
  pullbackMetricOfInjectiveLocalDiffeomorph g (modelWindowMap hB hfit)
    (modelWindowMap_isLocalDiffeomorph hB hfit)
    (isSmoothEmbedding_modelWindowMap hB hfit).isEmbedding.injective

theorem modelWindowPullback_inner {R B : ℝ} (hB : 0 < B) (hfit : R ≤ transitionEnd + B)
    (g : SmoothRiemannianMetric (𝓡 3) (InsertionQuotient hB))
    (x : modelWindow R) (v w : TangentSpace (𝓡 3) x) :
    (modelWindowPullback hB hfit g).inner x v w =
      g.inner (modelWindowMap hB hfit x)
        (mfderiv (𝓡 3) (𝓡 3) (modelWindowMap hB hfit) x v)
        (mfderiv (𝓡 3) (𝓡 3) (modelWindowMap hB hfit) x w) :=
  pullbackMetricOfInjectiveLocalDiffeomorph_inner _ _ _ _ _ _ _

theorem modelWindowPullback_insertedQuotientMetric {A B η R : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (hfit : R ≤ transitionEnd + B) :
    let hB : 0 < B := (mul_pos (by norm_num : (0 : ℝ) < 2) hA).trans hAB
    modelWindowPullback hB hfit (insertedQuotientMetric hA hAB hη h) =
      (insertedMetric hA hAB hη h).restrictOpenOfSubset
        (modelWindow_le_insertionBall hfit) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [modelWindowPullback_inner]
  erw [insertedQuotientMetric_inner]
  erw [modelWindowMap_mfderiv_realization, modelWindowMap_mfderiv_realization,
    modelWindowMap_realization]
  rfl

theorem normalizedDatum_modelWindowPullback
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
    (d : DifferentialGeometry.Geometry.Neck.normalizedDatum g x₀ δ k) {A R : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹)
    (hfit : R ≤ transitionEnd + δ⁻¹) :
    modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos (d.positiveSideInsertionMetric hA hAB)) =
      (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric).restrictOpenOfSubset
        (modelWindow_le_insertionBall hfit) := by
  rw [d.positiveSideInsertionMetric_normalization]
  exact modelWindowPullback_insertedQuotientMetric hA hAB _ _ hfit

private local instance (O : Opens E3) : SigmaCompactSpace O :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) O.isOpen)

private theorem window_norm_le_ball {R B D : ℝ} (hfit : R ≤ transitionEnd + B)
    (g : SmoothRiemannianMetric (𝓡 3) (insertionBall B)) (m : ℕ) :
    metricDerivENormSupOn
      {x : modelWindow R | (riemannianEDistOf metric 0 x.val).toReal < D} m
      (g.restrictOpenOfSubset (modelWindow_le_insertionBall hfit))
      (metric.restrictOpen (modelWindow R)) (metric.restrictOpen (modelWindow R)) ≤
    metricDerivENormSupOn {x : insertionBall B | ‖x.val‖ ≤ transitionEnd + D} m
      g (metric.restrictOpen (insertionBall B)) (metric.restrictOpen (insertionBall B)) := by
  apply (metricDerivENormSupOn_le_iff _ _ _ _ _ _).mpr
  intro j hj x hx
  have hn := DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm_flat
    (modelWindow_le_insertionBall hfit) g (metric.restrictOpen (insertionBall B))
    (metric.restrictOpen (insertionBall B)) j x
  rw [SmoothRiemannianMetric.restrictOpen_flat] at hn
  rw [hn]
  apply ofReal_metricDerivNorm_le_sup _ m _ _ _ hj
  change ‖x.val‖ ≤ transitionEnd + D
  change (riemannianEDistOf metric 0 x.val).toReal < D at hx
  rw [distance_zero] at hx
  linarith [transitionEnd_pos]

theorem exists_normalizedDatum_modelWindow_error_lt
    (A : ℝ) (hA : 0 < A) (D : ℝ) (hD : 0 < D) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ (hAB : 2 * A < δ⁻¹) (hfit : D + 1 ≤ transitionEnd + δ⁻¹),
        ∀ k : ℕ, m ≤ k →
        ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : DifferentialGeometry.Geometry.Neck.normalizedDatum g x₀ δ k),
        metricDerivENormSupOn
          {x : modelWindow (D + 1) | (riemannianEDistOf metric 0 x.val).toReal < D} m
          (modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
            (scaleMetric (metricScalarAt g x₀) d.scalar_pos (d.positiveSideInsertionMetric hA hAB)))
          (metric.restrictOpen (modelWindow (D + 1))) (metric.restrictOpen (modelWindow (D + 1))) <
          ENNReal.ofReal ε := by
  obtain ⟨δ₀, hδ₀, hhalf, hmod⟩ := exists_normalizedDatum_insertedMetric_ball_error_lt
    A hA D hD.le m ε hε
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle
  obtain ⟨hAB, hDB, hb⟩ := hmod δ hδ hδle
  have hfit : D + 1 ≤ transitionEnd + δ⁻¹ := by linarith [transitionEnd_pos]
  refine ⟨hAB, hfit, ?_⟩
  intro k hmk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  rw [normalizedDatum_modelWindowPullback]
  exact (window_norm_le_ball hfit _ m).trans_lt (hb k hmk g x₀ d)

end DifferentialGeometry.PDE.RicciFlow.StandardCap

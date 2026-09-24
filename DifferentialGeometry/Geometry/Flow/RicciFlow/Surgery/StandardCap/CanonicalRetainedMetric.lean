import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckMarkSideBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Topology.Handle.Manifold
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.Handle
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev PM := ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)
private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

def neckRetainedCollarHomeomorph (δ : ℝ) :
    neckRetainedCollar δ ≃ₜ Sphere 2 × Ico (0 : ℝ) δ⁻¹ where
  toFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩)
  invFun := fun p => ⟨(p.1, p.2.1), p.2.2⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => rfl
  continuous_toFun := Continuous.prodMk
    (continuous_fst.comp continuous_subtype_val)
    (Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _)
  continuous_invFun := Continuous.subtype_mk
    (Continuous.prodMk continuous_fst (continuous_subtype_val.comp continuous_snd)) _

@[instance_reducible] def neckRetainedCollarChartedSpace {δ : ℝ} (hδ : 0 < δ) :
    ChartedSpace (EuclideanHalfSpace 3) (neckRetainedCollar δ) :=
  letI := halfClosedIntervalChartedSpace (inv_pos.mpr hδ)
  letI : ChartedSpace PM (neckRetainedCollar δ) :=
    chartedSpaceOfHomeomorph (neckRetainedCollarHomeomorph δ)
  euclideanHalfSpaceProdChartedSpace (neckRetainedCollar δ)

theorem neckRetainedCollar_isManifold {δ : ℝ} (hδ : 0 < δ) :
    letI := neckRetainedCollarChartedSpace hδ
    IsManifold (𝓡∂ 3) ∞ (neckRetainedCollar δ) := by
  let := halfClosedIntervalChartedSpace (inv_pos.mpr hδ)
  let := halfClosedInterval_isManifold (inv_pos.mpr hδ)
  let : ChartedSpace PM (neckRetainedCollar δ) :=
    chartedSpaceOfHomeomorph (neckRetainedCollarHomeomorph δ)
  let : IsManifold IR ∞ (neckRetainedCollar δ) :=
    isManifoldOfHomeomorph IR (neckRetainedCollarHomeomorph δ)
  exact euclideanHalfSpaceProd_isManifold (neckRetainedCollar δ)

def neckRetainedCollarDiffeomorph {δ : ℝ} (hδ : 0 < δ) :
    letI := halfClosedIntervalChartedSpace (inv_pos.mpr hδ)
    letI := neckRetainedCollarChartedSpace hδ
    neckRetainedCollar δ ≃ₘ⟮𝓡∂ 3, (𝓡 2).prod (𝓡∂ 1)⟯ Sphere 2 × Ico (0 : ℝ) δ⁻¹ := by
  letI := halfClosedIntervalChartedSpace (inv_pos.mpr hδ)
  letI := halfClosedInterval_isManifold (inv_pos.mpr hδ)
  letI : ChartedSpace PM (neckRetainedCollar δ) :=
    chartedSpaceOfHomeomorph (neckRetainedCollarHomeomorph δ)
  letI : IsManifold IR ∞ (neckRetainedCollar δ) :=
    isManifoldOfHomeomorph IR (neckRetainedCollarHomeomorph δ)
  letI := euclideanHalfSpaceProdChartedSpace (neckRetainedCollar δ)
  exact
    { toEquiv := (neckRetainedCollarHomeomorph δ).toEquiv
      contMDiff_toFun :=
        (contMDiff_chartedSpaceTransHomeomorph_source_iff IR (𝓡∂ 3)
          euclideanHalfSpaceProdHomeomorph euclideanHalfSpaceProdCoordinates
          euclideanHalfSpaceProdHomeomorph_model IR).mpr
          (contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
            (neckRetainedCollarHomeomorph δ) IR ∞)
      contMDiff_invFun :=
        (contMDiff_chartedSpaceTransHomeomorph_iff IR (𝓡∂ 3)
          euclideanHalfSpaceProdHomeomorph euclideanHalfSpaceProdCoordinates
          euclideanHalfSpaceProdHomeomorph_model IR).mpr
          (contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
            (neckRetainedCollarHomeomorph δ) IR ∞) }


theorem neckRetainedCollar_inclusion_isSmoothEmbedding {δ : ℝ} (hδ : 0 < δ) :
    letI := neckRetainedCollarChartedSpace hδ
    IsSmoothEmbedding (𝓡∂ 3) NeckCylinderModel ∞
      (Subtype.val : neckRetainedCollar δ → NeckCylinder) := by
  let := halfClosedIntervalChartedSpace (inv_pos.mpr hδ)
  let := halfClosedInterval_isManifold (inv_pos.mpr hδ)
  let : ChartedSpace PM (neckRetainedCollar δ) :=
    chartedSpaceOfHomeomorph (neckRetainedCollarHomeomorph δ)
  let : IsManifold IR ∞ (neckRetainedCollar δ) :=
    isManifoldOfHomeomorph IR (neckRetainedCollarHomeomorph δ)
  let Hd : neckRetainedCollar δ ≃ₘ⟮IR, IR⟯ Sphere 2 × Ico (0 : ℝ) δ⁻¹ :=
    { toEquiv := (neckRetainedCollarHomeomorph δ).toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
        (neckRetainedCollarHomeomorph δ) IR ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
        (neckRetainedCollarHomeomorph δ) IR ∞ }
  have hp : IsSmoothEmbedding IR NeckCylinderModel ∞
      (Prod.map (id : Sphere 2 → Sphere 2) (Subtype.val : Ico (0 : ℝ) δ⁻¹ → ℝ)) :=
    (IsSmoothEmbedding.id (I := 𝓡 2) (M := Sphere 2)).prodMap
      (isSmoothEmbedding_halfClosedInterval_inclusion (inv_pos.mpr hδ))
  have hh := isSmoothEmbedding_diffeomorph_precomp _ hp Hd
  exact (isSmoothEmbedding_chartedSpaceTransHomeomorph_source_iff IR (𝓡∂ 3)
    euclideanHalfSpaceProdHomeomorph euclideanHalfSpaceProdCoordinates
    euclideanHalfSpaceProdHomeomorph_model NeckCylinderModel).mpr hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}

namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d A hA D m ε)

def retainedMap : C(neckRetainedCollar δ, InsertionQuotient (inv_pos.mpr d.precision_pos)) := by
  letI := halfClosedIntervalChartedSpace (inv_pos.mpr d.precision_pos)
  exact ⟨w.data.retainedInclusion ∘ neckRetainedCollarHomeomorph δ,
    w.properties.retained_embedding.contMDiff.continuous.comp
      (neckRetainedCollarHomeomorph δ).continuous⟩


@[simp] theorem retainedMap_apply (x : neckRetainedCollar δ) :
    w.retainedMap x = w.data.retainedInclusion (x.1.1, ⟨x.1.2, x.2⟩) := rfl


theorem retainedMap_range : range w.retainedMap = range w.data.retainedInclusion :=
  (neckRetainedCollarHomeomorph δ).surjective.range_comp w.data.retainedInclusion

theorem retainedMap_contMDiff :
    letI := neckRetainedCollarChartedSpace d.precision_pos
    ContMDiff (𝓡∂ 3) (𝓡 3) ∞ w.retainedMap := by
  let := halfClosedIntervalChartedSpace (inv_pos.mpr d.precision_pos)
  let := neckRetainedCollarChartedSpace d.precision_pos
  exact w.properties.retained_embedding.contMDiff.comp
    (neckRetainedCollarDiffeomorph d.precision_pos).contMDiff

theorem retainedMap_mfderiv_injective :
    letI := neckRetainedCollarChartedSpace d.precision_pos
    ∀ x, Injective (mfderiv (𝓡∂ 3) (𝓡 3) w.retainedMap x) := by
  let := halfClosedIntervalChartedSpace (inv_pos.mpr d.precision_pos)
  let := halfClosedInterval_isManifold (inv_pos.mpr d.precision_pos)
  let := neckRetainedCollarChartedSpace d.precision_pos
  let := neckRetainedCollar_isManifold d.precision_pos
  let Hd := neckRetainedCollarDiffeomorph d.precision_pos
  intro x
  change Injective (mfderiv (𝓡∂ 3) (𝓡 3) (w.data.retainedInclusion ∘ Hd) x)
  rw [mfderiv_comp x
    (w.properties.retained_embedding.contMDiff.mdifferentiableAt (by simp))
    (Hd.contMDiff.mdifferentiableAt (by simp))]
  exact ((w.properties.retained_embedding.isImmersion.isImmersionAt (Hd x)).injective_mfderiv
    (by simp)).comp ((Hd.mfderivToContinuousLinearEquiv (by simp) x).injective)


theorem retainedMap_isSmoothEmbedding :
    letI := neckRetainedCollarChartedSpace d.precision_pos
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ w.retainedMap := by
  let := halfClosedIntervalChartedSpace (inv_pos.mpr d.precision_pos)
  let := halfClosedInterval_isManifold (inv_pos.mpr d.precision_pos)
  let : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1))
      (neckRetainedCollar δ) := chartedSpaceOfHomeomorph (neckRetainedCollarHomeomorph δ)
  let : IsManifold IR ∞ (neckRetainedCollar δ) :=
    isManifoldOfHomeomorph IR (neckRetainedCollarHomeomorph δ)
  let Hd : neckRetainedCollar δ ≃ₘ⟮IR, IR⟯ Sphere 2 × Ico (0 : ℝ) δ⁻¹ :=
    { toEquiv := (neckRetainedCollarHomeomorph δ).toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
        (neckRetainedCollarHomeomorph δ) IR ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
        (neckRetainedCollarHomeomorph δ) IR ∞ }
  have hh := isSmoothEmbedding_diffeomorph_precomp _ w.properties.retained_embedding Hd
  exact (isSmoothEmbedding_chartedSpaceTransHomeomorph_source_iff IR (𝓡∂ 3)
    euclideanHalfSpaceProdHomeomorph euclideanHalfSpaceProdCoordinates
    euclideanHalfSpaceProdHomeomorph_model (𝓡 3)).mpr hh

def retainedMetric :
    letI := neckRetainedCollarChartedSpace d.precision_pos
    letI := neckRetainedCollar_isManifold d.precision_pos
    SmoothRiemannianMetric (𝓡∂ 3) (neckRetainedCollar δ) := by
  letI := neckRetainedCollarChartedSpace d.precision_pos
  letI := neckRetainedCollar_isManifold d.precision_pos
  exact w.data.outMetric.pullback w.retainedMap w.retainedMap_contMDiff
    w.retainedMap_mfderiv_injective

theorem retained_metric_output :
    letI := neckRetainedCollarChartedSpace d.precision_pos
    letI := neckRetainedCollar_isManifold d.precision_pos
    ∀ x V W, w.retainedMetric.inner x V W =
      w.data.outMetric.inner (w.retainedMap x)
        (mfderiv (𝓡∂ 3) (𝓡 3) w.retainedMap x V)
        (mfderiv (𝓡∂ 3) (𝓡 3) w.retainedMap x W) := by
  let := neckRetainedCollarChartedSpace d.precision_pos
  let := neckRetainedCollar_isManifold d.precision_pos
  intro x V W
  rfl

theorem retained_metric_input :
    letI := neckRetainedCollarChartedSpace d.precision_pos
    letI := neckRetainedCollar_isManifold d.precision_pos
    ∀ x V W, w.retainedMetric.inner x V W =
      g.inner ((d.oriented.positiveRetainedMap ∘ neckRetainedCollarHomeomorph δ) x)
        (mfderiv (𝓡∂ 3) I (d.oriented.positiveRetainedMap ∘ neckRetainedCollarHomeomorph δ) x V)
        (mfderiv (𝓡∂ 3) I
          (d.oriented.positiveRetainedMap ∘ neckRetainedCollarHomeomorph δ) x W) := by
  let := halfClosedIntervalChartedSpace (inv_pos.mpr d.precision_pos)
  let := halfClosedInterval_isManifold (inv_pos.mpr d.precision_pos)
  let := neckRetainedCollarChartedSpace d.precision_pos
  let := neckRetainedCollar_isManifold d.precision_pos
  let Hd := neckRetainedCollarDiffeomorph d.precision_pos
  intro x V W
  rw [w.retained_metric_output]
  change w.data.outMetric.inner ((w.data.retainedInclusion ∘ Hd) x)
    (mfderiv (𝓡∂ 3) (𝓡 3) (w.data.retainedInclusion ∘ Hd) x V)
    (mfderiv (𝓡∂ 3) (𝓡 3) (w.data.retainedInclusion ∘ Hd) x W) =
      g.inner ((d.oriented.positiveRetainedMap ∘ Hd) x)
        (mfderiv (𝓡∂ 3) I (d.oriented.positiveRetainedMap ∘ Hd) x V)
        (mfderiv (𝓡∂ 3) I (d.oriented.positiveRetainedMap ∘ Hd) x W)
  rw [mfderiv_comp x (w.properties.retained_embedding.contMDiff.mdifferentiableAt (by simp))
      (Hd.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_comp x (d.oriented.positiveRetainedMap_smooth.mdifferentiableAt (by simp))
      (Hd.contMDiff.mdifferentiableAt (by simp))]
  exact w.properties.retained_metric (Hd x)
    (mfderiv (𝓡∂ 3) IR Hd x V) (mfderiv (𝓡∂ 3) IR Hd x W)

end CanonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric ThreeModel M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}

private def retainedBufferInclusion {δ : ℝ} (hδ : 0 < δ) :
    neckRetainedCollar δ → neckBuffer δ := fun y =>
  ⟨y.1, by
    have := inv_pos.mpr hδ
    constructor <;> linarith [y.2.1, y.2.2]⟩

theorem CanonicalStaticInsertionWitness.retained_metric_input_neck
    (w : CanonicalStaticInsertionWitness d A hA D m ε) :
    letI := neckRetainedCollarChartedSpace d.precision_pos
    letI := neckRetainedCollar_isManifold d.precision_pos
    ∀ x V W,
      let inclusion : neckRetainedCollar δ → neckBuffer δ := fun y =>
        ⟨y.1, by
          have := inv_pos.mpr d.precision_pos
          constructor <;> linarith [y.2.1, y.2.2]⟩
      w.retainedMetric.inner x V W =
        g.inner (d.oriented.toNormalizedNeck.chart (inclusion x))
          (mfderiv (𝓡∂ 3) ThreeModel (d.oriented.toNormalizedNeck.chart ∘ inclusion) x V)
          (mfderiv (𝓡∂ 3) ThreeModel (d.oriented.toNormalizedNeck.chart ∘ inclusion) x W) := by
  let := neckRetainedCollarChartedSpace d.precision_pos
  let := neckRetainedCollar_isManifold d.precision_pos
  have he : d.oriented.positiveRetainedMap ∘ neckRetainedCollarHomeomorph δ =
      d.oriented.toNormalizedNeck.chart ∘ retainedBufferInclusion d.precision_pos := by
    funext y
    rfl
  intro x V W
  change w.retainedMetric.inner x V W =
    g.inner ((d.oriented.toNormalizedNeck.chart ∘ retainedBufferInclusion d.precision_pos) x)
      (mfderiv (𝓡∂ 3) ThreeModel
        (d.oriented.toNormalizedNeck.chart ∘ retainedBufferInclusion d.precision_pos) x V)
      (mfderiv (𝓡∂ 3) ThreeModel
        (d.oriented.toNormalizedNeck.chart ∘ retainedBufferInclusion d.precision_pos) x W)
  rw [← he]
  exact w.retained_metric_input x V W

end DifferentialGeometry.PDE.RicciFlow.StandardCap

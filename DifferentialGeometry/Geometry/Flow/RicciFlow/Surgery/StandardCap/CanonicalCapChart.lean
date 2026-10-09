import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalRetainedMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalTransitionBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph

set_option autoImplicit false
noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.Handle DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩
private local instance : ChartedSpace (EuclideanHalfSpace 3)
    {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd} :=
  closedBallChartedSpace StandardCap.transitionEnd_pos
private local instance : IsManifold (𝓡∂ 3) ∞
    {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd} :=
  closedBall_isManifold StandardCap.transitionEnd_pos

def standardCapCoreHomeomorph :
    standardCapClosedCore ≃ₜ {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd} where
  toFun x := ⟨x.val, by
    simpa only [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right,
      show standardCapL = StandardCap.transitionEnd from rfl] using x.property⟩
  invFun x := ⟨x.val, by
    simpa only [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right,
      show standardCapL = StandardCap.transitionEnd from rfl] using x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := continuous_subtype_val.subtype_mk (fun x => by
    simpa only [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right,
      show standardCapL = StandardCap.transitionEnd from rfl] using x.property)
  continuous_invFun := continuous_subtype_val.subtype_mk (fun x => by
    simpa only [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right,
      show standardCapL = StandardCap.transitionEnd from rfl] using x.property)

@[instance_reducible] def standardCapCoreChartedSpace :
    ChartedSpace (EuclideanHalfSpace 3) standardCapClosedCore :=
  chartedSpaceOfHomeomorph standardCapCoreHomeomorph

theorem standardCapCore_isManifold :
    letI := standardCapCoreChartedSpace
    IsManifold (𝓡∂ 3) ∞ standardCapClosedCore :=
  isManifoldOfHomeomorph (𝓡∂ 3) standardCapCoreHomeomorph

def standardCapCoreDiffeomorph :
    letI := standardCapCoreChartedSpace
    standardCapClosedCore ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯
      {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd} := by
  letI := standardCapCoreChartedSpace
  exact
    { toEquiv := standardCapCoreHomeomorph.toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
        standardCapCoreHomeomorph (𝓡∂ 3) ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
        standardCapCoreHomeomorph (𝓡∂ 3) ∞ }

theorem standardCapCore_induced :
    letI := standardCapCoreChartedSpace
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (Subtype.val : standardCapClosedCore → ThreeSpace) := by
  let := standardCapCoreChartedSpace
  let := standardCapCore_isManifold
  exact isSmoothEmbedding_diffeomorph_precomp Subtype.val
    (isSmoothEmbedding_closedBall_inclusion StandardCap.transitionEnd_pos)
    standardCapCoreDiffeomorph

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : ChartedSpace (EuclideanHalfSpace 3)
    {x : E3 // ‖x‖ ≤ transitionEnd} := closedBallChartedSpace transitionEnd_pos
private local instance : IsManifold (𝓡∂ 3) ∞
    {x : E3 // ‖x‖ ≤ transitionEnd} := closedBall_isManifold transitionEnd_pos
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

def capChart : C(standardCapClosedCore, InsertionQuotient (inv_pos.mpr d.precision_pos)) :=
  ⟨w.data.capMap ∘ standardCapCoreHomeomorph,
    w.properties.capMap_embedding.contMDiff.continuous.comp standardCapCoreHomeomorph.continuous⟩

theorem capChart_smooth :
    letI := standardCapCoreChartedSpace
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ w.capChart := by
  let := standardCapCoreChartedSpace
  let := standardCapCore_isManifold
  exact isSmoothEmbedding_diffeomorph_precomp w.data.capMap w.properties.capMap_embedding
    standardCapCoreDiffeomorph

theorem capChart_range : range w.capChart = range w.data.capInclusion := by
  change range (w.data.capMap ∘ standardCapCoreHomeomorph) = range w.data.capInclusion
  rw [standardCapCoreHomeomorph.surjective.range_comp]
  exact w.properties.capMap_image

theorem capChart_boundary (y : Sphere 2)
    (hx : standardCapL • y.val ∈ standardCapClosedCore) :
    w.capChart ⟨standardCapL • y.val, hx⟩ =
      w.data.retainedInclusion (retainedBoundary (inv_pos.mpr d.precision_pos) y) := by
  exact w.properties.capMap_boundary y

theorem capChart_tip (hx : (0 : ThreeSpace) ∈ standardCapClosedCore) :
    w.capChart ⟨0, hx⟩ = w.data.tip := by
  exact w.properties.capMap_tip

theorem windowMap_eq_capChart (x : ThreeSpace) (hx : ‖x‖ < D + 1)
    (hc : x ∈ standardCapClosedCore) :
    w.data.windowMap ⟨x, hx⟩ = w.capChart ⟨x, hc⟩ := by
  rw [w.properties.windowMap_eq]
  change modelWindowMap (inv_pos.mpr d.precision_pos) w.properties.window_fit ⟨x, hx⟩ =
    w.data.capMap (standardCapCoreHomeomorph ⟨x, hc⟩)
  rw [w.properties.capMap_eq, w.properties.capInclusion_eq]
  exact modelWindowMap_agrees_cap _ _ (standardCapCoreHomeomorph ⟨x, hc⟩) hx

end CanonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩
private local instance : ChartedSpace (EuclideanHalfSpace 3)
    {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd} :=
  closedBallChartedSpace StandardCap.transitionEnd_pos
private local instance : IsManifold (𝓡∂ 3) ∞
    {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd} :=
  closedBall_isManifold StandardCap.transitionEnd_pos
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold
attribute [local instance] threeBallChartedSpace threeBall_isManifold

def standardCapBallDiffeomorph :
    ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd} :=
  threeBallDiffeomorph.symm.trans
    (closedBallUnitDiffeomorph StandardCap.transitionEnd_pos).symm

@[simp] theorem standardCapBallDiffeomorph_apply_val (x : ThreeBall) :
    (standardCapBallDiffeomorph x).val = StandardCap.transitionEnd • x.val := rfl

@[simp] theorem standardCapBallDiffeomorph_boundary (y : Sphere 2) :
    standardCapBallDiffeomorph (sphereToThreeBall y) =
      radialCapBoundary StandardCap.transitionEnd_pos y := rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private abbrev E3Ball := EuclideanSpace ℝ (Fin 3)
private local instance : Fact (Module.finrank ℝ E3Ball = 2 + 1) := ⟨by simp⟩
private local instance : ChartedSpace (EuclideanHalfSpace 3)
    {x : E3Ball // ‖x‖ ≤ transitionEnd} := closedBallChartedSpace transitionEnd_pos
private local instance : IsManifold (𝓡∂ 3) ∞
    {x : E3Ball // ‖x‖ ≤ transitionEnd} := closedBall_isManifold transitionEnd_pos
private local instance quotientBallChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3Ball (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientBallIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB
attribute [local instance] threeBallChartedSpace threeBall_isManifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}

namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d A hA D m ε)

def cap : C(ThreeBall, InsertionQuotient (inv_pos.mpr d.precision_pos)) :=
  ⟨w.data.capInclusion ∘ standardCapBallDiffeomorph,
    w.properties.cap_embedding.contMDiff.continuous.comp standardCapBallDiffeomorph.continuous⟩

theorem cap_smooth : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ w.cap :=
  isSmoothEmbedding_diffeomorph_precomp w.data.capInclusion w.properties.cap_embedding
    standardCapBallDiffeomorph

theorem cap_range : range w.cap = range w.data.capInclusion :=
  standardCapBallDiffeomorph.surjective.range_comp w.data.capInclusion

theorem cap_boundary (y : Sphere 2) :
    w.cap (sphereToThreeBall y) =
      w.retainedMap ⟨(y, 0), le_rfl, inv_pos.mpr d.precision_pos⟩ := by
  change w.data.capInclusion (standardCapBallDiffeomorph (sphereToThreeBall y)) = _
  rw [standardCapBallDiffeomorph_boundary]
  rw [← w.properties.capMap_eq]
  exact w.properties.capMap_boundary y

theorem cap_tip_interior : ∃ x : ThreeBall, ‖x.val‖ < 1 ∧ w.cap x = w.data.tip := by
  let z : ThreeBall := ⟨0, by simp [ThreeBall]⟩
  refine ⟨z, by simp [z], ?_⟩
  rw [w.properties.tip_eq]
  apply congrArg w.data.capInclusion
  apply Subtype.ext
  simp [standardCapBallDiffeomorph_apply_val, z]
  rfl

theorem capChart_range_cap : range w.capChart = range w.cap :=
  w.capChart_range.trans w.cap_range.symm

theorem exists_window_preimage_cap (w : CanonicalStaticInsertionWitness d A hA D m ε)
    (hD : transitionEnd < D + 1) (z : ThreeBall) :
    ∃ u : standardCapWindow D, ‖u.val‖ ≤ transitionEnd ∧ w.window u = w.cap z := by
  have hz : w.cap z ∈ range w.cap := ⟨z, rfl⟩
  rw [← w.capChart_range_cap] at hz
  obtain ⟨x, hx⟩ := hz
  have hxnorm : ‖x.val‖ ≤ transitionEnd := by
    simpa only [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right,
      standardCapL_eq_transitionEnd] using x.property
  refine ⟨⟨x.val, hxnorm.trans_lt hD⟩, hxnorm, ?_⟩
  exact (w.windowMap_eq_capChart x.val (hxnorm.trans_lt hD) x.property).trans hx

end CanonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OpenCoreAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OpenCoreMetric

set_option autoImplicit false

/-!
HG16 source: `docs/geometrization/blueprint/master207A.tex:18880–18915`
(the opening proof and its HG17 consumer); task CH12-CX1 in
`docs/geometrization/chapter12/codex/CODEX-PROMPT-C3a-20261006.md` at `f76cff256`.
Implementation base: `7570ef23cf047c7f3653ca2b2ffd459b84ef4905`.

The open core carries a pulled-back complete metric, not the restriction of the
ambient metric. The raw metric has curvature -1/4 and unchanged volume; the
`InteriorGeometry` wrapper scales it to the curvature -1 Thurston convention.
The smooth inward collar is extended from the actual cusp embedding. The
original inward collar is used only to separate ends topologically, because
its jets need not agree with the cusp parametrization at the boundary.
No assumption on the truncation level or additional collar data is required.
-/

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
  GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

variable {H : FiniteVolumeHyperbolicModel.{u}}

/-- Identify the whole-piece interior used by `InteriorGeometry` with the
intrinsic interior used by the geometric opening. -/
def pieceInteriorTopDiffeo_CX1 (C : CompactCarrier.{u}) :
    Diffeomorph C.model C.model (C.pieceInterior ⊤) C.interior ∞ where
  toFun x := ⟨x.val, x.property.2⟩
  invFun x := ⟨x.val, trivial, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff C.interior _).mp contMDiff_subtype_val
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff (C.pieceInterior ⊤) _).mp contMDiff_subtype_val

/-- The opening on the standard boundaryless interior atlas. -/
def truncationInteriorDiffeo_CX1 (T : HyperbolicTruncation H) :
    letI := Manifold.interiorChartedSpace T.core.model ∞ (M := T.core.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold T.core.model ∞ (M := T.core.pieceInterior ⊤)
    Diffeomorph (𝓡 3) (𝓡 3) (T.core.pieceInterior ⊤) H.Carrier ∞ := by
  let := Manifold.interiorChartedSpace T.core.model ∞ (M := T.core.pieceInterior ⊤)
  let := Manifold.interiorIsManifold T.core.model ∞ (M := T.core.pieceInterior ⊤)
  exact ((Manifold.interiorAtlasDiffeomorph T.core.model ∞
    (M := T.core.pieceInterior ⊤)).symm.trans (pieceInteriorTopDiffeo_CX1 T.core)).trans
      (openCoreDiffeo_CX1 T)

/-- Pull back the original curvature `-1/4` metric along the actual opening. -/
def truncationInteriorMetric_CX1 (T : HyperbolicTruncation H) :
    letI := Manifold.interiorChartedSpace T.core.model ∞ (M := T.core.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold T.core.model ∞ (M := T.core.pieceInterior ⊤)
    SmoothRiemannianMetric (𝓡 3) (T.core.pieceInterior ⊤) := by
  let := Manifold.interiorChartedSpace T.core.model ∞ (M := T.core.pieceInterior ⊤)
  let := Manifold.interiorIsManifold T.core.model ∞ (M := T.core.pieceInterior ⊤)
  exact Diffeomorph.pullbackMetricCross H.metric (truncationInteriorDiffeo_CX1 T)

theorem truncationInteriorMetric_properties_CX1 (T : HyperbolicTruncation H) :
    letI := Manifold.interiorChartedSpace T.core.model ∞ (M := T.core.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold T.core.model ∞ (M := T.core.pieceInterior ⊤)
    let g := truncationInteriorMetric_CX1 T
    hasConstantSectionalCurvature g (-(1 / 4 : ℝ)) ∧ RiemannianMetricComplete g ∧
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) (T.core.pieceInterior ⊤) g univ =
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric univ ∧
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) (T.core.pieceInterior ⊤) g univ < ⊤ := by
  let := Manifold.interiorChartedSpace T.core.model ∞ (M := T.core.pieceInterior ⊤)
  let := Manifold.interiorIsManifold T.core.model ∞ (M := T.core.pieceInterior ⊤)
  exact hyperbolicMetric_pullback_CX1 H (truncationInteriorDiffeo_CX1 T)

/-- The complete finite-volume hyperbolic structure on the truncated piece.
`hyperbolicGeometricStructure` performs the conventional `1/4` metric scaling. -/
def truncationInteriorGeometry_CX1 (T : HyperbolicTruncation H) :
    T.core.InteriorGeometry ⊤ := by
  let := Manifold.interiorChartedSpace T.core.model ∞ (M := T.core.pieceInterior ⊤)
  let := Manifold.interiorIsManifold T.core.model ∞ (M := T.core.pieceInterior ⊤)
  exact hyperbolicGeometricStructure (truncationInteriorMetric_CX1 T)
    (truncationInteriorMetric_properties_CX1 T).1
    (truncationInteriorMetric_properties_CX1 T).2.1
    (truncationInteriorMetric_properties_CX1 T).2.2.2

/-- HG16, in exactly the geometry-and-model form consumed by the hyperbolic
constructor. There are no additional collar or geometric hypotheses. -/
theorem hyperbolicInteriorGeometry_of_truncation_CX1 (T : HyperbolicTruncation H) :
    ∃ geometry : T.core.InteriorGeometry ⊤, isHyperbolicInteriorGeometry geometry :=
  ⟨truncationInteriorGeometry_CX1 T, rfl⟩

/-- Consumer wiring for a cut piece identified with the actual truncated core. -/
theorem hyperbolicAlternative_of_truncation_CX1 (T : HyperbolicTruncation H)
    {P : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3}
    (D : GC.Topology.TorusDecomposition P)
    (metric : ∀ i, SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (thin : Fin D.components.count → Prop) (K : ℕ) (w : ℝ)
    (i : Fin D.components.count) (hnot : ¬ thin i)
    (e : Diffeomorph D.carrier.model T.core.model
      (D.carrier.pieceInterior (D.components.piece i)) T.core.interior ∞) :
    Nonempty (HyperbolicOrThin D metric thin K w i) :=
  hyperbolicAlternative_of_diffeomorph_CX1 H D metric thin K w i hnot
    (e.trans (openCoreDiffeo_CX1 T))

end GC.LongTime.Ch12

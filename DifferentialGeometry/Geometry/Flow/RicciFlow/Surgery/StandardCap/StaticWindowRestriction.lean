import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticWindow

set_option autoImplicit false
noncomputable section
open Set Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace ThreeSpace (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {A : ℝ} {hA : 0 < A} {D D' : ℝ} {m : ℕ} {ε : ℝ}

namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d A hA D m ε)

private theorem canonical_window_close_restrict (hD'D : D' ≤ D) :
    metricDerivENormSupOn
      {x : modelWindow (D' + 1) | (riemannianEDistOf metric 0 x.val).toReal < D'} m
      (modelWindowPullback (inv_pos.mpr d.precision_pos)
        ((add_le_add hD'D (le_refl 1)).trans w.properties.window_fit)
        (scaleMetric (metricScalarAt g x₀) d.scalar_pos
          (d.oriented.positiveSideInsertionMetric hA w.properties.cut_fit)))
      (metric.restrictOpen (modelWindow (D' + 1)))
      (metric.restrictOpen (modelWindow (D' + 1))) < ENNReal.ofReal ε := by
  have hclose := w.canonical_window_close
  rw [normalizedDatum_modelWindowPullback] at hclose ⊢
  refine lt_of_le_of_lt ?_ hclose
  apply (metricDerivENormSupOn_le_iff _ _ _ _ _ _).mpr
  intro j hj x hx
  let y : modelWindow (D + 1) := ⟨x.val, x.property.trans_le (add_le_add hD'D (le_refl 1))⟩
  have hy : (riemannianEDistOf metric 0 y.val).toReal < D := hx.trans_le hD'D
  let G := insertedMetric hA w.properties.cut_fit
    d.oriented.controlledMetric_cylinder_lower.1 d.oriented.controlledMetric
  let U := insertionBall δ⁻¹
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)
  have hn := metricDerivNorm_flat
    (modelWindow_le_insertionBall ((add_le_add hD'D (le_refl 1)).trans w.properties.window_fit))
    G (metric.restrictOpen U) (metric.restrictOpen U) j x
  have hn' := metricDerivNorm_flat
    (modelWindow_le_insertionBall w.properties.window_fit)
    G (metric.restrictOpen U) (metric.restrictOpen U) j y
  rw [SmoothRiemannianMetric.restrictOpen_flat] at hn hn'
  rw [hn, ← hn']
  exact ofReal_metricDerivNorm_le_sup _ m _ _ _ hj hy

def restrictWindow (hD' : 0 < D') (hD'D : D' ≤ D) :
    CanonicalStaticInsertionWitness d A hA D' m ε := by
  apply canonicalStaticInsertionWitness d A hA D' hD' m ε
    w.properties.cut_fit ((add_le_add hD'D (le_refl 1)).trans w.properties.window_fit)
  · exact w.properties.profileTip_eq ▸ w.properties.profileTip_location
  · exact w.canonical_window_close_restrict hD'D

@[simp] theorem restrictWindow_quotientDiffeomorph (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.quotientDiffeomorph = w.data.quotientDiffeomorph :=
  (w.restrictWindow hD' hD'D).properties.quotientDiffeomorph_eq.trans
    w.properties.quotientDiffeomorph_eq.symm

@[simp] theorem restrictWindow_gluingDiffeomorph (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.gluingDiffeomorph = w.data.gluingDiffeomorph :=
  (w.restrictWindow hD' hD'D).properties.gluingDiffeomorph_eq.trans
    w.properties.gluingDiffeomorph_eq.symm

@[simp] theorem restrictWindow_profileTip (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.profileTip = w.data.profileTip :=
  (w.restrictWindow hD' hD'D).properties.profileTip_eq.trans w.properties.profileTip_eq.symm

@[simp] theorem restrictWindow_profile (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.profile = w.data.profile :=
  (w.restrictWindow hD' hD'D).properties.profile_eq.trans w.properties.profile_eq.symm

@[simp] theorem restrictWindow_outMetric (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.outMetric = w.data.outMetric :=
  (w.restrictWindow hD' hD'D).properties.outMetric_eq.trans w.properties.outMetric_eq.symm

@[simp] theorem restrictWindow_capInclusion (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.capInclusion = w.data.capInclusion :=
  (w.restrictWindow hD' hD'D).properties.capInclusion_eq.trans
    w.properties.capInclusion_eq.symm

@[simp] theorem restrictWindow_retainedInclusion (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.retainedInclusion = w.data.retainedInclusion :=
  (w.restrictWindow hD' hD'D).properties.retainedInclusion_eq.trans
    w.properties.retainedInclusion_eq.symm

@[simp] theorem restrictWindow_capMap (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.capMap = w.data.capMap := by
  rw [(w.restrictWindow hD' hD'D).properties.capMap_eq,
    w.properties.capMap_eq, restrictWindow_capInclusion]

@[simp] theorem restrictWindow_deepMap (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.deepMap = w.data.deepMap := by
  rw [(w.restrictWindow hD' hD'D).properties.deepMap_eq,
    w.properties.deepMap_eq, restrictWindow_capMap]

@[simp] theorem restrictWindow_tip (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.tip = w.data.tip := by
  rw [(w.restrictWindow hD' hD'D).properties.tip_eq,
    w.properties.tip_eq, restrictWindow_capInclusion]

@[simp] theorem restrictWindow_collapse (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).data.collapse = w.data.collapse :=
  (w.restrictWindow hD' hD'D).properties.collapse_eq.trans w.properties.collapse_eq.symm

@[simp] theorem restrictWindow_window (hD' : 0 < D') (hD'D : D' ≤ D)
    (x : standardCapWindow D') :
    (w.restrictWindow hD' hD'D).window x =
      w.window ⟨x.val, x.property.trans_le (add_le_add hD'D (le_refl 1))⟩ := by
  change (w.restrictWindow hD' hD'D).data.windowMap x = w.data.windowMap _
  rw [(w.restrictWindow hD' hD'D).properties.windowMap_eq, w.properties.windowMap_eq]
  rfl

@[simp] theorem restrictWindow_windowMetric (hD' : 0 < D') (hD'D : D' ≤ D) :
    (w.restrictWindow hD' hD'D).windowMetric =
      w.windowMetric.restrictOpenOfSubset
        (fun _ hx => hx.trans_le (add_le_add hD'D (le_refl 1)) :
          standardCapWindow D' ≤ standardCapWindow D) := by
  simp only [windowMetric, (w.restrictWindow hD' hD'D).properties.windowMap_eq,
    restrictWindow_outMetric, w.properties.windowMap_eq]
  exact modelWindowPullback_restrict (inv_pos.mpr d.precision_pos)
    (add_le_add hD'D (le_refl 1)) w.properties.window_fit _

end CanonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap

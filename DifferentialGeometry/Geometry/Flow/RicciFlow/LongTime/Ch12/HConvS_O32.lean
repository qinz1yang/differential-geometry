import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HEndParts_O32
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrBridge_S57
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchCore_S61
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.ForwardApproximation
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Pullback
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

/-! CH12-O32 G5: P1 `hconvS` of `[FROZEN] CH12-O32` from canonical pointed convergence
(`PointedSmoothConverges_S13`): S's maps are eventually GOOD at any fixed accuracy, radius and order.
Route: `eventually_map_metric_approximation` on a compact closed ball, `pullback_metric_deriv_norm_le`,
`ckErr_S45_eq_metricDerivNorm_S57`, transport along `postStage_eq_sliceStage_CX4`. -/

/-- Transport of smoothness, embedding and `ckErr_S45` along a stage equality `A = B` carrying
`HEq`-equal metrics. -/
theorem stageCast_transport_O32 (H : FiniteVolumeHyperbolicModel.{u})
    {A B : OrientedThreeStage.{u}} (h : A = B) (mA : A.Metric) (mB : B.Metric) (hm : HEq mA mB)
    (f : H.Carrier → B.Carrier) (U : TopologicalSpace.Opens H.Carrier) (c : ℝ) :
    (ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U → ContMDiffOn (𝓡 3) (𝓡 3) ∞
        (fun x => cast (congrArg (·.Carrier) h).symm (f x)) U) ∧
    (IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => cast (congrArg (·.Carrier) h).symm (f x))) ∧
    ∀ (k : ℕ) (p : H.Carrier), ckErr_S45 H mA c (fun x => cast (congrArg (·.Carrier) h).symm (f x)) k p =
      ckErr_S45 H mB c f k p := by
  subst h
  obtain rfl := eq_of_heq hm
  exact ⟨id, id, fun _ _ => rfl⟩

/-- `[FROZEN] CH12-O32 G5`: P1 from canonical convergence. -/
theorem hconvS_O32 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u})
    (S : LatePointSequence_S13 F)
    (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id)
    (C : MetricConvergenceData Φ)
    (hcan : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k) :
    ∀ (δ r : ℝ) (m : ℕ), 0 < δ → 0 < r → ∃ I : ℕ, ∀ i : ℕ, I ≤ i →
      ∃ U : TopologicalSpace.Opens H.Carrier,
        riemannianBallOf H.metric H.basepoint r ⊆ U ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (sliceApprox_O32 S H Φ i) U ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => sliceApprox_O32 S H Φ i x) ∧
        ∀ k : ℕ, k ≤ m → ∀ p ∈ riemannianBallOf H.metric H.basepoint r,
          ckErr_S45 H (postMetric F.observation (S.slices i).time) (S.slices i).time⁻¹
            (sliceApprox_O32 S H Φ i) k p < δ := by
  intro δ r m hδ _hr
  have hε : 0 < min (δ / 2) (1 / 2 : ℝ) := lt_min (by linarith) (by norm_num)
  have hε1 : min (δ / 2) (1 / 2 : ℝ) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hεδ : min (δ / 2) (1 / 2 : ℝ) < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hK : IsCompact (riemannianClosedBallOf H.metric H.basepoint r) :=
    isCompact_riemannianClosedBallOf H.complete _ _
  let U : TopologicalSpace.Opens H.Carrier :=
    ⟨riemannianBallOf H.metric H.basepoint r, isOpen_riemannianBallOf_S61 H r⟩
  have hUK : (U : Set H.Carrier) ⊆ riemannianClosedBallOf H.metric H.basepoint r :=
    fun q hq => show riemannianEDistOf (I := 𝓡 3) H.metric H.basepoint q ≤ ENNReal.ofReal r from
      le_of_lt hq
  have hUi : (U : Set H.Carrier) ⊆ interior (riemannianClosedBallOf H.metric H.basepoint r) :=
    DifferentialGeometry.Geometry.Metric.riemannianBallOf_subset_interior_riemannianClosedBallOf _ _ _
  obtain ⟨I, hI⟩ := Filter.eventually_atTop.1
    (C.eventually_map_metric_approximation hcan _ hK m hε hε1)
  refine ⟨I, fun i hi => ?_⟩
  obtain ⟨hKs, happ⟩ := hI i hi
  obtain ⟨D0⟩ := happ (U : Set H.Carrier) hUi
  let φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier (S.slices i).stage.Carrier ∞ :=
    Φ.partialDiffeomorph i
  have D : MapMetricApproximationOn (I := 𝓡 3) (U : Set H.Carrier) (min (δ / 2) (1 / 2 : ℝ)) m
      (φ : H.Carrier → (S.slices i).stage.Carrier) H.metric (S.slices i).normalizedMetric := D0
  have hUs : (U : Set H.Carrier) ⊆ φ.source := hUK.trans hKs
  have hφs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (φ : H.Carrier → (S.slices i).stage.Carrier) U :=
    φ.contMDiffOn.mono hUs
  have hloc : ∀ y ∈ U, IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ φ y := fun y hy =>
    φ.isLocalDiffeomorphAt _ _ _ (hUs hy)
  have hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ y) := fun y hy => by
    obtain ⟨e, he⟩ := (hloc y hy).isInvertible_mfderiv (by simp)
    rw [← he]
    exact e.injective
  have hemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) :=
    Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      (isLocalDiffeomorph_restrict_open U (fun x => hloc x x.2))
      (fun x y hxy => Subtype.ext (φ.injOn (hUs x.2) (hUs y.2) hxy))
  obtain ⟨t1, t2, t3⟩ := stageCast_transport_O32 H (postStage_eq_sliceStage_CX4 (S.slices i))
    (postMetric F.observation (S.slices i).time) (S.slices i).metric
    (postMetric_regularSlice F.observation (S.slices i)) φ U (S.slices i).time⁻¹
  refine ⟨U, subset_rfl, t1 hφs, t2 hemb, fun k hk p hp => ?_⟩
  have ht : 0 < (S.slices i).time⁻¹ := inv_pos.mpr (S.slices i).positive
  have hb := ckErr_S45_eq_metricDerivNorm_S57 H (S.slices i).metric _ ht φ U hφs hinj k ⟨p, hp⟩
  have heq : pullbackRestrict_S57 H (scaleMetric _ ht (S.slices i).metric) φ U hφs hinj =
      PartialDiffeomorph.pullbackMetricOn φ U hUs (S.slices i).normalizedMetric := by
    ext z v w
    rw [PartialDiffeomorph.pullbackMetricOn_inner]
    simp only [pullbackRestrict_S57, SmoothRiemannianMetric.pullbackOfImmersion_inner]
    rw [mfderiv_comp_val_C4 _ U hφs z v, mfderiv_comp_val_C4 _ U hφs z w]
    rfl
  rw [heq] at hb
  calc ckErr_S45 H (postMetric F.observation (S.slices i).time) (S.slices i).time⁻¹
        (sliceApprox_O32 S H Φ i) k p = ckErr_S45 H (S.slices i).metric (S.slices i).time⁻¹ φ k p :=
        t3 k p
    _ = _ := hb
    _ ≤ min (δ / 2) (1 / 2 : ℝ) :=
        pullback_metric_deriv_norm_le φ U hUs subset_rfl H.metric (S.slices i).normalizedMetric D hk
          ⟨p, hp⟩
    _ < δ := hεδ

end GC.LongTime.Ch12

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82SetVolume_CX11
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

set_option autoImplicit false

noncomputable section

open Set Manifold MeasureTheory TopologicalSpace DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Integral.Measure
  DifferentialGeometry.PDE.RicciFlow
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Backward volume transfer for an actual traced set, including surgery events.
The set on the right consists precisely of the initial points of the history's
backward traces. The proof uses the existing common smooth flow on the top ball;
injective local isometries identify its measures with the stage measures. -/
theorem traced_set_volume_CX11
    (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon} (hat : a < t)
    (p : (H.stageAt t).Carrier) {ρ K k : ℝ} (hρ : 0 < ρ)
    (htr : ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ,
      ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat.le) q, A.isRmBoundedBy (hat := hat.le) K)
    (B : Set (H.stageAt t).Carrier) (hB : @MeasurableSet _ (borel _) B)
    (hBball : B ⊆ riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ)
    (hRic : ∀ q ∈ B, ∀ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat.le) q,
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      ∀ w : TangentSpace ThreeModel
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)),
        -k * (H.stageMetric (H.activeStage v) v).inner _ w w ≤
          ricciTensor (H.stageMetric (H.activeStage v) v) _ w w) :
    ENNReal.ofReal (Real.exp (-(3 * k * ((t : ℝ) - a)))) *
        riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
          (H.stageMetric (H.activeStage t) t) B ≤
      riemannianVolumeMeasure ThreeModel (H.stageAt a).Carrier
        (H.stageMetric (H.activeStage a) a)
        {z | ∃ q ∈ B, ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat.le) q,
            A.point (H.activeStage a) le_rfl (H.activeStage_mono hat.le) = z} := by
  have hregion : H.isTracedRegion t p ρ ((t : ℝ) - a) K :=
    ⟨hρ, sub_pos.mpr hat, a, hat.le, by ring, htr⟩
  obtain ⟨a', hat', ha', U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, _⟩ :=
    H.exists_common_flow_of_isTracedRegion t p hregion
  have haa : a' = a := Subtype.ext (by linarith)
  subst a'
  let : MeasurableSpace (H.stageAt t).Carrier := borel _
  let : BorelSpace (H.stageAt t).Carrier := ⟨rfl⟩
  let : MeasurableSpace U := borel _
  let : BorelSpace U := ⟨rfl⟩
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  let B' : Set U := Subtype.val ⁻¹' B
  have hB' : MeasurableSet B' := continuous_subtype_val.measurable hB
  let trace (x : U) : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat.le) x.val :=
    { point := fun j hj hl => f ⟨j, hj, hl⟩ x
      endpoint_eq := hlast x
      crossing := fun i hi hl => hcross i hi hl x }
  have hRic' : ∀ v ∈ Icc (a : ℝ) t, ∀ x ∈ B', ∀ w : TangentSpace ThreeModel x,
      -k * (S.base.metric v).inner x w w ≤ ricciTensor (S.base.metric v) x w w := by
    intro v hv x hx w
    let v' : Icc (0 : ℝ) H.horizon :=
      ⟨v, a.property.1.trans hv.1, hv.2.trans t.property.2⟩
    have hav : a ≤ v' := hv.1
    have hvt : v' ≤ t := hv.2
    let j : H.StageInterval (H.activeStage a) (H.activeStage t) :=
      ⟨H.activeStage v', H.activeStage_mono hav, H.activeStage_mono hvt⟩
    rw [hmetric j v hv (H.activeStage_mem v'), ricciTensor_localPullMetric,
      localPullMetric_inner]
    exact hRic x.val hx (trace x) v' hav hvt (mfderiv ThreeModel ThreeModel (f j) x w)
  have hvol := setVolume_ge_exp_of_ricci_lower_CX11 S hS hat.le
    (by intro v hv; exact hv) (by intro v hv; exact hv) hB' hRic'
  let ja : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage a, le_rfl, H.activeStage_mono hat.le⟩
  let jt : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage t, H.activeStage_mono hat.le, le_rfl⟩
  have hvola := Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    (S.base.metric a) (H.stageMetric (H.activeStage a) a) (f ja) (hf ja) (hinj ja)
    (fun x v w => by
      rw [hmetric ja a ⟨le_rfl, hat.le⟩ (H.activeStage_mem a), localPullMetric_inner]) hB'
  have hvolt := Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    (S.base.metric t) (H.stageMetric (H.activeStage t) t) (f jt) (hf jt) (hinj jt)
    (fun x v w => by
      rw [hmetric jt t ⟨hat.le, le_rfl⟩ (H.activeStage_mem t), localPullMetric_inner]) hB'
  have himt : f jt '' B' = B := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [show f jt x = x.val from hlast x]
      exact hx
    · intro hq
      have hqU : q ∈ U := by
        change q ∈ (U : Set (H.stageAt t).Carrier)
        rw [hU]
        exact hBball hq
      exact ⟨⟨q, hqU⟩, hq, hlast _⟩
  have hima : f ja '' B' =
      {z | ∃ q ∈ B, ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat.le) q,
          A.point (H.activeStage a) le_rfl (H.activeStage_mono hat.le) = z} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, trace x, rfl⟩
    · rintro ⟨q, hq, A, rfl⟩
      have hqU : q ∈ U := by
        change q ∈ (U : Set (H.stageAt t).Carrier)
        rw [hU]
        exact hBball hq
      let x : U := ⟨q, hqU⟩
      exact ⟨x, hq, (trace x).point_unique A _ _ _⟩
  rw [hvolt, hvola, himt, hima] at hvol
  exact hvol

/-- The coefficient in the traced-set comparison for the KL82 sectional lower
bound is `6 / r0²`, independently of the upper trace bound `K`. -/
theorem traced_set_volume_of_sec_CX11
    (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon} (hat : a < t)
    (p : (H.stageAt t).Carrier) {ρ K r0 : ℝ} (hρ : 0 < ρ)
    (htr : ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ,
      ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat.le) q, A.isRmBoundedBy (hat := hat.le) K)
    (B : Set (H.stageAt t).Carrier) (hB : @MeasurableSet _ (borel _) B)
    (hBball : B ⊆ riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ)
    (hsec : ∀ q ∈ B, ∀ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat.le) q,
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
        SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (-(r0 ^ 2)⁻¹)) :
    ENNReal.ofReal (Real.exp (-6 * ((t : ℝ) - a) / r0 ^ 2)) *
        riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
          (H.stageMetric (H.activeStage t) t) B ≤
      riemannianVolumeMeasure ThreeModel (H.stageAt a).Carrier
        (H.stageMetric (H.activeStage a) a)
        {z | ∃ q ∈ B, ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat.le) q,
            A.point (H.activeStage a) le_rfl (H.activeStage_mono hat.le) = z} := by
  have hh := traced_set_volume_CX11 H hat p hρ htr B hB hBball (k := 2 / r0 ^ 2)
    (fun q hq A v hav hvt w => by
      have h := ricci_lower_of_sectionalBoundedBelowAt _ _ (hsec q hq A v hav hvt) w
      norm_num [ThreeSpace] at h
      simpa only [div_eq_mul_inv, neg_mul, mul_neg] using h)
  convert hh using 2
  congr 2
  ring

end GC.LongTime.Ch12

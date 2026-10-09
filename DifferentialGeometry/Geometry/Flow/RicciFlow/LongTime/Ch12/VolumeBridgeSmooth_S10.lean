import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalVolumeVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.VolumeContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData

set_option autoImplicit false
noncomputable section
open Set MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

variable {P : OrientedThreeStage.{u}} {D : RealTimeInterval}

/-- Volume (real) of the stage along a Ricci flow. -/
def flowVolume_S10 (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D) (t : ℝ) : ℝ :=
  (riemannianVolumeMeasure ThreeModel P.Carrier (S.family.metric t) univ).toReal

theorem flowVolume_hasDerivAt_S10 (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (hS : IsSolutionOn S) {t : ℝ} (ht : t ∈ D.regular) :
    HasDerivAt (flowVolume_S10 S)
      (∫ x, - S.scalar t x ∂(riemannianVolumeMeasure ThreeModel P.Carrier (S.family.metric t))) t := by
  have h := compact_ricciFlow_volumeVariation_on_regular S hS (fun _ _ => (1 : ℝ))
    (contMDiffOn_const) ht
  convert h using 1
  · funext s
    simp [flowVolume_S10, integral_const, Measure.real_def]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp


theorem integral_neg_scalar_le_S10 (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (t : ℝ) {k : ℝ} (hk0 : 0 ≤ k) (hk : ∀ x, -k ≤ S.scalar t x) :
    ∫ x, - S.scalar t x ∂(riemannianVolumeMeasure ThreeModel P.Carrier (S.family.metric t)) ≤
      k * flowVolume_S10 S t := by
  set μ := riemannianVolumeMeasure ThreeModel P.Carrier (S.family.metric t) with hμ
  have hV : 0 ≤ flowVolume_S10 S t := ENNReal.toReal_nonneg
  have : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := ThreeModel) (M := P.Carrier) _
  by_cases hint : Integrable (fun x => S.scalar t x) μ
  · have h1 : 0 ≤ ∫ x, (S.scalar t x + k) ∂μ :=
      integral_nonneg (fun x => by simp only [Pi.zero_apply]; linarith [hk x])
    rw [integral_add hint (integrable_const k)] at h1
    simp only [integral_const, smul_eq_mul, Measure.real_def] at h1
    rw [integral_neg]
    have : flowVolume_S10 S t = (μ univ).toReal := rfl
    rw [this]
    nlinarith
  · rw [integral_neg, integral_undef hint]
    simpa using mul_nonneg hk0 hV

/-- Normalised volume `V(t)(t+c)^{-3/2}` is antitone along a Ricci flow with `R ≥ -3/(2(t+c))`. -/
theorem flowVolume_normalized_antitone_S10 (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (hS : IsSolutionOn S) {c : ℝ} (hconv : Convex ℝ D.carrier)
    (hint : interior D.carrier ⊆ D.regular) (hpos : ∀ t ∈ D.carrier, 0 < t + c)
    (hR : ∀ t ∈ D.regular, ∀ x, -(3 / (2 * (t + c))) ≤ S.scalar t x) :
    AntitoneOn (fun t => flowVolume_S10 S t * (t + c) ^ (-(3 / 2 : ℝ))) D.carrier := by
  have hcont : ContinuousOn (flowVolume_S10 S) D.carrier := S.continuousOn_volume hS
  have hderiv : ∀ t ∈ interior D.carrier,
      HasDerivAt (fun t => flowVolume_S10 S t * (t + c) ^ (-(3 / 2 : ℝ)))
        (( ∫ x, - S.scalar t x ∂(riemannianVolumeMeasure ThreeModel P.Carrier (S.family.metric t))) *
            (t + c) ^ (-(3 / 2 : ℝ)) +
          flowVolume_S10 S t * ((-(3 / 2 : ℝ)) * (t + c) ^ (-(3 / 2 : ℝ) - 1))) t := by
    intro t ht
    have h1 := flowVolume_hasDerivAt_S10 S hS (hint ht)
    have hp : 0 < t + c := hpos t (interior_subset ht)
    have h2 : HasDerivAt (fun t => (t + c) ^ (-(3 / 2 : ℝ))) ((-(3 / 2 : ℝ)) * (t + c) ^ (-(3 / 2 : ℝ) - 1)) t := by
      have := ((hasDerivAt_id t).add_const c).rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hp.ne')
      simpa using this
    exact h1.mul h2
  refine antitoneOn_of_deriv_nonpos hconv ?_ ?_ ?_
  · exact hcont.mul (ContinuousOn.rpow_const (continuousOn_id.add continuousOn_const)
      (fun t ht => Or.inl (hpos t ht).ne'))
  · intro t ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hderiv t ht).deriv]
    have hp : 0 < t + c := hpos t (interior_subset ht)
    have hle := integral_neg_scalar_le_S10 S t (k := 3 / (2 * (t + c))) (by positivity)
      (hR t (hint ht))
    have hq : 0 < (t + c) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hp _
    have hsplit : (t + c) ^ (-(3 / 2 : ℝ) - 1) = (t + c) ^ (-(3 / 2 : ℝ)) / (t + c) := by
      rw [Real.rpow_sub hp, Real.rpow_one]
    rw [hsplit]
    have : (3 / (2 * (t + c))) * flowVolume_S10 S t * (t + c) ^ (-(3 / 2 : ℝ)) +
        flowVolume_S10 S t * (-(3 / 2 : ℝ) * ((t + c) ^ (-(3 / 2 : ℝ)) / (t + c))) = 0 := by
      field_simp
      ring
    nlinarith [mul_le_mul_of_nonneg_right hle hq.le]

end GC.LongTime.Ch12

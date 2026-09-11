import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowScalarPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedGoodPointBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues


set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

private local instance propagationC1 {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)


theorem NormalizedSequence.carrier_mem_nhdsLE
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (i : ℕ) {t : ℝ} (ht : t ∈ Icc (-X.depth i) 0) :
    (X.interval i).carrier ∈ 𝓝[≤] t := by
  rw [X.carrier_eq i]
  have hl : -(2 * X.depth i) < t := by linarith [X.depth_pos i, ht.1]
  exact Filter.mem_of_superset (Icc_mem_nhdsLE hl)
    (fun r hr => ⟨hr.1, hr.2.trans ht.2⟩)


theorem NormalizedSequence.local_propagation_of_bounds
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (hPhi : AdmissiblePinchingFunction Phi) (i : ℕ) {CStar : ℝ} (hCStar : 0 ≤ CStar)
    (hdepth : 2 * localPropagationRadius CStar ≤ X.depth i)
    (hbound : ∀ (w : (X.term i).M) (t : ℝ), t ∈ Icc (-X.depth i) 0 →
      2 ≤ (X.term i).S.scalar t w →
      (∀ a : TangentSpace I3 w, |scalarDifferential (X.term i).S t w a| ≤
        2 * CStar * ((X.term i).S.scalar t w * Real.sqrt ((X.term i).S.scalar t w)) *
          Real.sqrt (((X.term i).S.base.metric t).inner w a a)) ∧
      |derivWithin (fun rho : ℝ => (X.term i).S.scalar rho w) (Iic t) t| ≤
        CStar * (X.term i).S.scalar t w ^ 2)
    {s : ℝ} (hs : s ∈ Icc (-(X.depth i / 2)) 0) (z : (X.term i).M) :
    let L := 1 + |(X.term i).S.scalar s z|
    Icc (s - localPropagationRadius CStar / L) s ⊆ (X.interval i).carrier ∧
      ∀ y v, (y, v) ∈ frozenBackwardCylinder (X.term i).S z s
        (localPropagationRadius CStar) (localPropagationRadius CStar) L →
        -6 * (X.scale i)⁻¹ * Phi 0 ≤ (X.term i).S.scalar v y ∧
          (X.term i).S.scalar v y ≤ 4 * L ∧
          Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S v y) ≤
            4 * Real.sqrt 3 * (L + (Phi (4 * X.scale i * L) + Phi 0) / X.scale i) := by
  let S := (X.term i).S
  let L := 1 + |S.scalar s z|
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [abs_nonneg (S.scalar s z)]
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hc : 0 < localPropagationRadius CStar := localPropagationRadius_pos hCStar
  have hJ : Icc (-X.depth i) 0 ⊆ (X.interval i).carrier := by
    intro r hr
    rw [X.carrier_eq i]
    exact ⟨by linarith [hr.1, X.depth_pos i], hr.2⟩
  have hwin : Icc (s - localPropagationRadius CStar / L) s ⊆ Icc (-X.depth i) 0 := by
    intro r hr
    have hh := parabolicTime_mem_window (t0 := 0) (Q := 1) (Hd := X.depth i) (L := L)
      (c := localPropagationRadius CStar) zero_lt_one hc hL1 hdepth hs hr
    simpa only [parabolicTime, div_one, zero_add, zero_sub] using hh
  refine ⟨hwin.trans hJ, ?_⟩
  intro y v hmem
  have hv : v ∈ (X.interval i).carrier := hJ (hwin hmem.2)
  have hscalar : S.scalar v y ≤ 4 * L := by
    have hh := scalar_le_of_left_derivative_bounds (I := I3) (X.term i).isSolution
      (Q := 1) (Hd := X.depth i) (t0 := 0) (L := L) (s := s) (v := v) (z := z) (y := y)
      hCStar zero_lt_one hL1 hdepth
      (by simpa only [div_one, zero_sub] using hJ)
      (by simpa only [div_one, zero_sub] using
        fun (r : ℝ) (hr : r ∈ Icc (-X.depth i) 0) => X.carrier_mem_nhdsLE i hr)
      (by simpa only [mul_one, div_one, zero_sub] using hbound)
      (by simpa only [mul_one, zero_sub] using hs)
      (by dsimp [L]; simpa only [one_mul, add_sub_cancel_left] using le_abs_self (S.scalar s z))
      (by simpa only [one_mul] using hmem.1)
      (by simpa only [one_mul] using hmem.2)
    simpa only [one_mul] using hh
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hPhi' := hPhi.rescale (X.scale_pos i)
  have hpinch : PhiAlmostNonnegative S (X.interval i).carrier
      (rescalePinchingFunction (X.scale i) Phi) := X.pinching i
  have hlower := neg_six_mul_phi_zero_le_scalar hPhi' hpinch hdim hv y
  have hbridge : RmNormBoundOn S (2 * Real.sqrt 3) :=
    fun t w basis horth a ha =>
      sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le S t w basis horth ha
  have hrm := sqrt_rmNormSq_le_of_scalar_le (I := I3)
    (by positivity : 0 ≤ 2 * Real.sqrt 3) hbridge hPhi' hpinch hdim hv y hL hscalar
  have hrhs : 2 * (2 * Real.sqrt 3) *
      (L + rescalePinchingFunction (X.scale i) Phi (4 * L) +
        rescalePinchingFunction (X.scale i) Phi 0) =
      4 * Real.sqrt 3 * (L + (Phi (4 * X.scale i * L) + Phi 0) / X.scale i) := by
    simp only [rescalePinchingFunction, mul_zero]
    rw [show X.scale i * (4 * L) = 4 * X.scale i * L by ring]
    ring
  rw [hrhs] at hrm
  refine ⟨?_, hscalar, hrm⟩
  simpa only [rescalePinchingFunction, mul_zero, mul_assoc] using hlower


theorem local_propagation_of_modelBound
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar c C : ℝ, 0 < epsStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in atTop,
            ∀ s ∈ Icc (-(X.depth i / 2)) 0, ∀ z : (X.term i).M,
              let L := 1 + |(X.term i).S.scalar s z|
              Icc (s - c / L) s ⊆ (X.interval i).carrier ∧
                ∀ y v, (y, v) ∈ frozenBackwardCylinder (X.term i).S z s c c L →
                  -6 * (X.scale i)⁻¹ * Phi 0 ≤ (X.term i).S.scalar v y ∧
                  (X.term i).S.scalar v y ≤ 4 * L ∧
                  Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S v y) ≤
                    C * (L + (Phi (4 * X.scale i * L) + Phi 0) / X.scale i) := by
  obtain ⟨epsStar, CStar, hepsStar, hCStar, hGP⟩ :=
    good_point_derivatives_of_modelCurvatureBound hmod
  refine ⟨epsStar, localPropagationRadius CStar, 4 * Real.sqrt 3,
    hepsStar, localPropagationRadius_pos hCStar.le, by positivity, ?_⟩
  intro eps heps hepsBound sigma _ Phi hPhi X
  filter_upwards [X.depth_tendsto.eventually (eventually_ge_atTop (2 * localPropagationRadius CStar))]
    with i hi
  intro s hs z
  have hregular : interior (X.interval i).carrier ⊆ (X.interval i).regular := by
    simpa only [X.carrier_eq i, X.regular_eq i, interior_Icc] using
      (Subset.rfl : Ioo (-(2 * X.depth i)) 0 ⊆ Ioo (-(2 * X.depth i)) 0)
  have hbnd : ∀ (w : (X.term i).M) (t : ℝ), t ∈ Icc (-X.depth i) 0 →
      2 ≤ (X.term i).S.scalar t w →
      (∀ a : TangentSpace I3 w, |scalarDifferential (X.term i).S t w a| ≤
        2 * CStar * ((X.term i).S.scalar t w * Real.sqrt ((X.term i).S.scalar t w)) *
          Real.sqrt (((X.term i).S.base.metric t).inner w a a)) ∧
      |derivWithin (fun rho : ℝ => (X.term i).S.scalar rho w) (Iic t) t| ≤
        CStar * (X.term i).S.scalar t w ^ 2 := by
    intro w t ht hw
    obtain ⟨W, _⟩ := X.higher_good i t ht w hw
    have hh := hGP (X.term i).M (X.interval i) (X.term i).S (X.term i).isSolution
      hregular eps heps hepsBound w t ⟨W⟩
    simpa only [mul_assoc] using hh
  exact X.local_propagation_of_bounds hPhi i hCStar.le hi hbnd hs z


theorem canonical_neighborhood_local_propagation {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar c C : ℝ, 0 < epsStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in atTop,
            ∀ s ∈ Icc (-(X.depth i / 2)) 0, ∀ z : (X.term i).M,
              let L := 1 + |(X.term i).S.scalar s z|
              Icc (s - c / L) s ⊆ (X.interval i).carrier ∧
                ∀ y v, (y, v) ∈ frozenBackwardCylinder (X.term i).S z s c c L →
                  -6 * (X.scale i)⁻¹ * Phi 0 ≤ (X.term i).S.scalar v y ∧
                  (X.term i).S.scalar v y ≤ 4 * L ∧
                  Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S v y) ≤
                    C * (L + (Phi (4 * X.scale i * L) + Phi 0) / X.scale i) := by
  exact local_propagation_of_modelBound
    (KappaSolutions.ancientKappa_modelCurvatureBoundNearBase
      (I := I3) (by simp [ThreeSpace]) hkappa)


theorem NormalizedSequence.pinching_error_eventually
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (hPhi : AdmissiblePinchingFunction Phi) {L0 eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ i in atTop, ∀ L ∈ Icc (1 : ℝ) L0,
      (Phi (4 * X.scale i * L) + Phi 0) / X.scale i < eta := by
  obtain ⟨Q0, _, hQ0⟩ := exists_pinching_error_lt (L0 := L0) hPhi heta
  filter_upwards [X.scale_tendsto.eventually (eventually_ge_atTop Q0)] with i hi
  exact hQ0 (X.scale i) hi

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowScalarPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedGoodPointBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedUniformCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaModelCurvatureWindow
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


theorem eventually_scalar_le_of_edist_tendsto_zero {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ (s : ℕ → ℝ) (z y : ∀ i, (X.term i).M) (A : ℝ),
              (∀ᶠ i in atTop, s i ∈ Icc (-(X.depth i / 2)) 0) →
              (∀ᶠ i in atTop, |(X.term i).S.scalar (s i) (z i)| ≤ A) →
              Tendsto (fun i => riemannianEDistOf ((X.term i).S.base.metric (s i))
                (z i) (y i)) atTop (𝓝 0) →
              ∀ᶠ i in atTop, (X.term i).S.scalar (s i) (y i) ≤ 4 * (1 + A) := by
  obtain ⟨epsStar, c, C, hepsStar, hc, _, hprop⟩ := canonical_neighborhood_local_propagation hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X s z y A hs hA hd
  have hAnonneg : 0 ≤ A := by
    obtain ⟨i, hi⟩ := hA.exists
    exact (abs_nonneg _).trans hi
  have hr : 0 < c / Real.sqrt (1 + A) := div_pos hc (Real.sqrt_pos.mpr (by linarith))
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X, hs, hA,
    hd.eventually (eventually_lt_nhds (ENNReal.ofReal_pos.mpr hr))] with i hi hsi hAi hdi
  have hL : 0 < 1 + |(X.term i).S.scalar (s i) (z i)| := by positivity
  have hradius : c / Real.sqrt (1 + A) ≤
      c / Real.sqrt (1 + |(X.term i).S.scalar (s i) (z i)|) :=
    div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.mpr hL)
      (Real.sqrt_le_sqrt (by linarith))
  have hmem : (y i, s i) ∈ frozenBackwardCylinder (X.term i).S (z i) (s i) c c
      (1 + |(X.term i).S.scalar (s i) (z i)|) := by
    exact ⟨hdi.le.trans (ENNReal.ofReal_le_ofReal hradius),
      ⟨by linarith [div_pos hc hL], le_rfl⟩⟩
  exact ((hi (s i) hsi (z i)).2 (y i) (s i) hmem).2.1.trans (by linarith)


theorem eventually_edist_gt_of_scalar_tendsto_atTop {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar c : ℝ, 0 < epsStar ∧ 0 < c ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ (s : ℕ → ℝ) (z y : ∀ i, (X.term i).M) (A : ℝ),
              (∀ᶠ i in atTop, s i ∈ Icc (-(X.depth i / 2)) 0) →
              (∀ᶠ i in atTop, |(X.term i).S.scalar (s i) (z i)| ≤ A) →
              Tendsto (fun i => (X.term i).S.scalar (s i) (y i)) atTop atTop →
              ∀ᶠ i in atTop,
                ENNReal.ofReal (c / Real.sqrt (1 + A)) <
                  riemannianEDistOf ((X.term i).S.base.metric (s i)) (z i) (y i) := by
  obtain ⟨epsStar, c, C, hepsStar, hc, _, hprop⟩ := canonical_neighborhood_local_propagation hkappa
  refine ⟨epsStar, c, hepsStar, hc, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X s z y A hs hA hy
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X, hs, hA,
    hy.eventually (eventually_gt_atTop (4 * (1 + A)))] with i hi hsi hAi hyi
  by_contra hd
  have hL : 0 < 1 + |(X.term i).S.scalar (s i) (z i)| :=
    add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg _)
  have hradius : c / Real.sqrt (1 + A) ≤
      c / Real.sqrt (1 + |(X.term i).S.scalar (s i) (z i)|) :=
    div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.mpr hL)
      (Real.sqrt_le_sqrt (by linarith))
  have hmem : (y i, s i) ∈ frozenBackwardCylinder (X.term i).S (z i) (s i) c c
      (1 + |(X.term i).S.scalar (s i) (z i)|) := by
    exact ⟨(not_lt.mp hd).trans (ENNReal.ofReal_le_ofReal hradius),
      ⟨by linarith [div_pos hc hL], le_rfl⟩⟩
  have hb := ((hi (s i) hsi (z i)).2 (y i) (s i) hmem).2.1
  linarith

theorem exists_curvature_radius_lower_bound_of_scalar_tendsto_atTop {r : ℝ} (hr : 0 ≤ r) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, eps ≤ epsStar →
      ∀ (kappa sigma : ℝ) (Phi : ℝ → ℝ) (X : NormalizedSequence.{u} eps kappa sigma Phi)
        (s : ℕ → ℝ) (z y : ∀ i, (X.term i).M) (R d : ℝ) (ell : ℕ → ℝ),
        (∀ᶠ i in atTop, s i ∈ Icc (-(X.depth i)) 0) → 2 < R →
        Tendsto (fun i => (X.term i).S.scalar (s i) (z i)) atTop (𝓝 R) →
        Tendsto (fun i => (X.term i).S.scalar (s i) (y i)) atTop atTop →
        Tendsto ell atTop (𝓝 d) →
        (∀ᶠ i in atTop, riemannianEDistOf ((X.term i).S.base.metric (s i)) (z i) (y i) ≤
          ENNReal.ofReal (ell i)) → r / Real.sqrt R ≤ d := by
  obtain ⟨epsStar, hepsStar, hbound⟩ :=
    exists_windowed_curvature_radius_lower_bound_of_scalar_tendsto_atTop.{u} hr
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps kappa sigma Phi X s z y R d ell hs hR hz hy hell hdist
  apply hbound (fun i => (X.term i).M) X.interval (fun i => (X.term i).S)
    (fun _ => eps) (fun _ => kappa) s z y R d ell ?_
    (Eventually.of_forall fun _ => heps) (by linarith) hz hy hell hdist
  filter_upwards [hs, hz.eventually (eventually_gt_nhds hR)] with i hsi hzi
  obtain ⟨W, -⟩ := X.higher_good i (s i) hsi (z i) hzi.le
  exact ⟨W⟩

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

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private theorem pinching_term_le_of_scale_ge_one
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    {scale Q L : ℝ} (hs : 1 ≤ scale) (hQ : 1 ≤ Q) (hL : L ≤ 3 * Q) :
    (Phi (4 * scale * L) + Phi 0) / scale ≤ 13 * Phi 1 * Q := by
  have hspos : 0 < scale := zero_lt_one.trans_le hs
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hsq : 1 ≤ scale * Q := one_le_mul_of_one_le_of_one_le hs hQ
  have harg : 1 ≤ 12 * scale * Q := by nlinarith
  have hquot := hPhi.quotientAntitoneOn (by norm_num : (1 : ℝ) ∈ Ioi 0)
    (show 12 * scale * Q ∈ Ioi 0 from by change 0 < 12 * scale * Q; positivity) harg
  have hquot' : Phi (12 * scale * Q) / (12 * scale * Q) ≤ Phi 1 := by
    simpa using hquot
  have hPhiarg : Phi (12 * scale * Q) ≤ Phi 1 * (12 * scale * Q) :=
    (div_le_iff₀ (show 0 < 12 * scale * Q by positivity)).mp hquot'
  have hmono := hPhi.mono (show 4 * scale * L ≤ 12 * scale * Q by nlinarith)
  have hzero : Phi 0 ≤ Phi 1 := hPhi.mono (by norm_num)
  have hPhi1 : 0 < Phi 1 := hPhi.pos 1
  rw [div_le_iff₀ hspos]
  nlinarith

theorem exists_local_curvature_cylinder_at_scale
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar c C : ℝ, 0 < epsStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in atTop,
            ∀ Q : ℝ, 1 ≤ Q → ∀ z : (X.term i).M,
              |(X.term i).S.scalar 0 z| ≤ 2 * Q →
              Icc (-(c / (3 * Q))) 0 ⊆ (X.interval i).carrier ∧
              ∀ y : (X.term i).M, ∀ t ∈ Icc (-(c / (3 * Q))) 0,
                y ∈ riemannianClosedBallOf ((X.term i).S.base.metric 0) z
                  (c / Real.sqrt (3 * Q)) →
                (X.term i).S.scalar t y ≤ 12 * Q ∧
                Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S t y) ≤
                  C * (3 + 13 * Phi 1) * Q := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hprop⟩ := local_propagation_of_modelBound hmod
  refine ⟨epsStar, c, C, hepsStar, hc, hC, ?_⟩
  intro eps heps hepsStar' sigma hsigma Phi hPhi X
  filter_upwards [hprop eps heps hepsStar' sigma hsigma Phi hPhi X,
    X.scale_tendsto.eventually_ge_atTop 1] with i hi hscale
  intro Q hQ z hz
  let L := 1 + |(X.term i).S.scalar 0 z|
  have hL : 0 < L := by dsimp [L]; positivity
  have hLQ : L ≤ 3 * Q := by dsimp [L]; linarith
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have htime : Icc (-(c / (3 * Q))) 0 ⊆ Icc (0 - c / L) 0 := by
    have hdiv : c / (3 * Q) ≤ c / L :=
      div_le_div_of_nonneg_left hc.le hL hLQ
    exact Icc_subset_Icc (by linarith) le_rfl
  have hrad : c / Real.sqrt (3 * Q) ≤ c / Real.sqrt L :=
    div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.mpr hL) (Real.sqrt_le_sqrt hLQ)
  have hzero : (0 : ℝ) ∈ Icc (-(X.depth i / 2)) 0 :=
    ⟨by linarith [X.depth_pos i], le_rfl⟩
  have hpi := hi 0 hzero z
  refine ⟨htime.trans hpi.1, ?_⟩
  intro y t ht hy
  have hmem : (y, t) ∈ frozenBackwardCylinder (X.term i).S z 0 c c L :=
    ⟨hy.trans (ENNReal.ofReal_le_ofReal hrad), htime ht⟩
  obtain ⟨_, hsc, hrm⟩ := hpi.2 y t hmem
  have hPhiBound := pinching_term_le_of_scale_ge_one hPhi hscale hQ hLQ
  have hcurv : C * (L + (Phi (4 * X.scale i * L) + Phi 0) / X.scale i) ≤
      C * (3 + 13 * Phi 1) * Q := by
    calc _ ≤ C * (3 * Q + 13 * Phi 1 * Q) := by gcongr
      _ = _ := by ring
  exact ⟨by linarith, hrm.trans hcurv⟩

theorem exists_rescaled_local_curvature_cylinder
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar c C : ℝ, 0 < epsStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in atTop,
            ∀ Q : ℝ, ∀ hQ : 0 < Q, 1 ≤ Q → ∀ z : (X.term i).M,
              |(X.term i).S.scalar 0 z| ≤ 2 * Q →
              ∀ hzero : (0 : ℝ) ∈ (X.interval i).carrier,
                let S := parabolicSolution (X.term i).S 0 Q hQ hzero
                Icc (-(c / 3)) 0 ⊆
                  (parabolicInterval (X.interval i) 0 Q hzero).carrier ∧
                ∀ y : (X.term i).M, ∀ t ∈ Icc (-(c / 3)) 0,
                  y ∈ riemannianClosedBallOf (S.base.metric 0) z (c / Real.sqrt 3) →
                  S.scalar t y ≤ 12 ∧
                  Real.sqrt (FlowMetricBall.rmNormSq S t y) ≤ C * (3 + 13 * Phi 1) := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hbound⟩ :=
    exists_local_curvature_cylinder_at_scale hmod
  refine ⟨epsStar, c, C, hepsStar, hc, hC, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X
  filter_upwards [hbound eps heps hle sigma hsigma Phi hPhi X] with i hi
  intro Q hQ hQone z hz hzero
  let S := parabolicSolution (X.term i).S 0 Q hQ hzero
  obtain ⟨hwindow, hlocal⟩ := hi Q hQone z hz
  have htime : ∀ t ∈ Icc (-(c / 3)) 0,
      parabolicTime 0 Q t ∈ Icc (-(c / (3 * Q))) 0 := by
    intro t ht
    dsimp only [parabolicTime]
    rw [zero_add]
    constructor
    · rw [le_div_iff₀ hQ]
      have heq : -(c / (3 * Q)) * Q = -(c / 3) := by field_simp
      rw [heq]
      exact ht.1
    · exact div_nonpos_of_nonpos_of_nonneg ht.2 hQ.le
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [parabolicInterval_carrier]
    exact hwindow (htime t ht)
  · intro y t ht hy
    have hsqrtQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
    have hrad : Real.sqrt Q * (c / Real.sqrt (3 * Q)) = c / Real.sqrt 3 := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      field_simp
    have hball := riemannianClosedBallOf_scaleMetric Q hQ
      ((X.term i).S.base.metric 0) z (c / Real.sqrt (3 * Q))
    rw [hrad] at hball
    have hy' : y ∈ riemannianClosedBallOf ((X.term i).S.base.metric 0) z
        (c / Real.sqrt (3 * Q)) := by
      change y ∈ riemannianClosedBallOf (scaleMetric Q hQ
        ((X.term i).S.base.metric (parabolicTime 0 Q 0))) z _ at hy
      rw [parabolicTime_zero] at hy
      rwa [← hball]
    obtain ⟨hsc, hrm⟩ := hlocal y _ (htime t ht) hy'
    constructor
    · change S.scalar t y ≤ 12
      rw [parabolicSolution_scalar]
      calc Q⁻¹ * (X.term i).S.scalar (parabolicTime 0 Q t) y
          ≤ Q⁻¹ * (12 * Q) := mul_le_mul_of_nonneg_left hsc (inv_nonneg.mpr hQ.le)
        _ = 12 := by field_simp
    · change Real.sqrt (FlowMetricBall.rmNormSq S t y) ≤ _
      rw [rmNormSq_paraSolution, Real.sqrt_mul (sq_nonneg Q⁻¹),
        Real.sqrt_sq (inv_nonneg.mpr hQ.le)]
      calc Q⁻¹ * Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S (parabolicTime 0 Q t) y)
          ≤ Q⁻¹ * (C * (3 + 13 * Phi 1) * Q) :=
            mul_le_mul_of_nonneg_left hrm (inv_nonneg.mpr hQ.le)
        _ = C * (3 + 13 * Phi 1) := by field_simp

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

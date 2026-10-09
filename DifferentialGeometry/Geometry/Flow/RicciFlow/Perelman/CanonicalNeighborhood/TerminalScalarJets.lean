import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvaturePropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLocalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalFromJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.ClosedInterval
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.QuadraticForm

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_eventually_curvDerivNorm_bound_of_terminal_scalar_le {kappa : ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ A : ℝ, ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in atTop,
            ∀ m : ℕ, ∀ y : (X.term i).M, (X.term i).S.scalar 0 y ≤ A →
              curvDerivNorm (I := I3) m ((X.term i).S.base.metric 0) y ≤ C m := by
  obtain ⟨epsStar, c, C₀, hepsStar, hc, hC₀, hprop⟩ :=
    local_propagation_of_modelBound hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma Phi hPhi A
  let B : ℝ := 1 + max A (6 * Phi 0)
  have hB : 0 < B := by
    dsimp only [B]
    linarith [le_max_right A (6 * Phi 0), hPhi.pos 0]
  let delta : ℝ := c / B
  have hdelta : 0 < delta := div_pos hc hB
  let radius : ℝ := c / Real.sqrt B
  have hradius : 0 < radius := div_pos hc (Real.sqrt_pos.mpr hB)
  let K : ℝ := C₀ * (B + 1)
  have hK : 0 < K := mul_pos hC₀ (by linarith)
  let Q : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (K ^ 2)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let L : ℝ := Real.exp (2 * Q * delta)
  have hL : 1 ≤ L := Real.one_le_exp (by positivity)
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  let r : ℝ := radius / (2 * L)
  have hr : 0 < r := by dsimp only [r]; positivity
  let R : ℝ := r * Real.sqrt K
  have hR : 0 < R := mul_pos hr (Real.sqrt_pos.mpr hK)
  let C : ℕ → ℝ := fun m => max 0
    (shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m (K * delta) R * K /
      Real.sqrt delta ^ m)
  refine ⟨C, fun m => le_max_left _ _, fun X => ?_⟩
  have hsigma : 0 < sigma :=
    pos_of_mul_pos_right (X.noncollapse 0).1 (Real.sqrt_nonneg _)
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X,
    X.scale_tendsto.eventually (eventually_ge_atTop (1 : ℝ)),
    X.pinching_error_eventually hPhi (L0 := B) (eta := 1) one_pos,
    X.depth_tendsto.eventually (eventually_ge_atTop delta)]
    with i hcyl hscale hpinch hdepth
  intro m y hy
  have hzero : (0 : ℝ) ∈ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  have hlow : -6 * Phi 0 ≤ (X.term i).S.scalar 0 y := by
    have hh := neg_six_mul_phi_zero_le_scalar (hPhi.rescale (X.scale_pos i))
      (X.pinching i) (by simp [ThreeSpace]) hzero y
    have hres : rescalePinchingFunction (X.scale i) Phi 0 = (X.scale i)⁻¹ * Phi 0 := by
      simp only [rescalePinchingFunction, mul_zero]
    rw [hres] at hh
    have hinv : (X.scale i)⁻¹ * Phi 0 ≤ Phi 0 := by
      have h1 : (X.scale i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hscale
      nlinarith [hPhi.pos 0]
    linarith
  let ell : ℝ := 1 + |(X.term i).S.scalar 0 y|
  have hell1 : 1 ≤ ell := by dsimp only [ell]; linarith [abs_nonneg ((X.term i).S.scalar 0 y)]
  have hell : 0 < ell := zero_lt_one.trans_le hell1
  have hellB : ell ≤ B := by
    have hh : |(X.term i).S.scalar 0 y| ≤ max A (6 * Phi 0) :=
      abs_le.mpr ⟨by linarith [le_max_right A (6 * Phi 0)],
        hy.trans (le_max_left A (6 * Phi 0))⟩
    dsimp only [ell, B]
    linarith
  have hcarrier : Icc (-delta) 0 ⊆ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hregular : Ico (-delta) 0 ⊆ (X.interval i).regular := by
    rw [X.regular_eq i]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hs : (0 : ℝ) ∈ Icc (-(X.depth i / 2)) 0 :=
    ⟨by linarith [X.depth_pos i], le_rfl⟩
  obtain ⟨_, hbound⟩ := hcyl 0 hs y
  let U : Set (X.term i).M :=
    riemannianClosedBallOf (I := I3) ((X.term i).S.base.metric 0) y radius
  have hcurv : ∀ t ∈ Icc (-delta) 0, ∀ z ∈ U,
      curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) z ≤ K ^ 2 := by
    intro t ht z hz
    have htime : delta ≤ c / ell := div_le_div_of_nonneg_left hc.le hell hellB
    have hrad : radius ≤ c / Real.sqrt ell :=
      div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.mpr hell) (Real.sqrt_le_sqrt hellB)
    have hmem : (z, t) ∈ frozenBackwardCylinder (X.term i).S y 0 c c ell := by
      refine ⟨?_, ⟨by linarith [ht.1], ht.2⟩⟩
      exact hz.trans (ENNReal.ofReal_le_ofReal hrad)
    have herror := hpinch ell ⟨hell1, hellB⟩
    have hh := (hbound z t hmem).2.2
    have hsqrt : Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S t z) ≤ K := by
      refine hh.trans ?_
      dsimp only [K]
      exact mul_le_mul_of_nonneg_left (by linarith) hC₀.le
    exact (Real.sqrt_le_iff.mp hsqrt).2
  have hcomplete : RiemannianMetricComplete (I := I3) ((X.term i).S.base.metric 0) :=
    ⟨X.complete i 0 hzero⟩
  have hcpt : IsCompact U := hcomplete.closedEBall_isCompact y radius
  have hquad := twoTensorQuadBound_of_solutions (I := I3)
    (fun _ => (X.term i).S) U (-delta) 0 (K ^ 2)
    (fun _ t ht z hz => hcurv t ht z hz)
  have hEq := metric_uniform_equivalent_on_closed_interval_of_solution
    (X.term i).S (X.term i).isSolution (show -delta < 0 by linarith)
    hcarrier (fun t ht => hregular ⟨ht.1.le, ht.2⟩)
    (show -delta ∈ Icc (-delta) (0 : ℝ) from ⟨le_rfl, by linarith⟩)
    hQ (fun t ht z hz v => hquad.2 0 t ht z hz v)
  have hmetric : ∀ z ∈ U, ∀ v : TangentSpace I3 z,
      ((X.term i).S.base.metric 0).inner z v v ≤
        L ^ 2 * ((X.term i).S.base.metric (-delta)).inner z v v := by
    intro z hz v
    have hh := (hEq 0 0 ⟨by linarith, le_rfl⟩).2 z hz v
    have heq : metricEquivalenceFactor 1 Q 0 (-delta) = L := by
      simp only [metricEquivalenceFactor, one_mul, sub_neg_eq_add, zero_add,
        abs_of_pos hdelta, L]
    dsimp only at hh
    rw [heq] at hh
    refine hh.2.trans (mul_le_mul_of_nonneg_right ?_
      (metric_inner_self_nonneg _ z v))
    nlinarith
  have hrs : r < radius / L := by
    dsimp only [r]
    exact div_lt_div_of_pos_left hradius hLpos (by linarith)
  obtain ⟨hball, hcapture⟩ := closedBall_isCompact_subset_of_local_metric_lower
    ((X.term i).S.base.metric 0) ((X.term i).S.base.metric (-delta)) y
    hradius hLpos hrs hcpt hmetric
  have hRr : R / Real.sqrt K = r := by
    dsimp only [R]
    exact mul_div_cancel_right₀ r (Real.sqrt_pos.mpr hK).ne'
  have hshi := KappaSolutions.shi_local_curvDerivNorm_terminal_of_solution_jets
    (X.term i).S (X.term i).isSolution (by simp [ThreeSpace])
    (show -delta < 0 by linarith) hK hR hcarrier hregular y
    (by simpa only [hRr, riemannianClosedBallOf] using hball)
    (by
      intro t ht z hz
      exact hcurv t ht z (hcapture (by simpa only [hRr, riemannianClosedBallOf, Set.mem_ofPred_eq] using hz)))
    m 0 ⟨by linarith, le_rfl⟩ y
    (by rw [riemannianEDistOf_self]; exact bot_le)
  apply hshi.trans
  simpa only [sub_neg_eq_add, zero_add] using le_max_right 0
    (shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m (K * delta) R * K /
      Real.sqrt delta ^ m)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

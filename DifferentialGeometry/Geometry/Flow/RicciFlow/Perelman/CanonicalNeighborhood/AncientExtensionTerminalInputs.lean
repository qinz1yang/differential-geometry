import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLimitConstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardExtension

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def TerminalCompactnessInput (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
      BoundedAtDistance X → TerminalDerivativeBounds X →
      ∃ P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0),
        (∀ k : ℕ, P.convergence.metrics.domain k =
          CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
        ConnectedSpace P.limit.M ∧
        MetricSourceCapture P.maps ∧
        (∀ i : ℕ, IsCompact (closure (P.maps.partialDiffeomorph i).source)) ∧
        (∀ i : ℕ, IsConnected (P.maps.partialDiffeomorph i).source) ∧
        (∀ i : ℕ, closure (P.maps.partialDiffeomorph i).source ⊆
          (P.maps.partialDiffeomorph (i + 1)).source) ∧
        (∃ o : TangentOrientationSection P.limit.M,
          ∀ i y, y ∈ (P.maps.partialDiffeomorph i).source →
            ∃ hf : Function.Bijective (mfderiv I3 I3 (P.maps.partialDiffeomorph i) y),
              PreservesTangentOrientationAt o (X.orientation (P.subseq i))
                (P.maps.partialDiffeomorph i) y hf) ∧
        (∃ C : ℝ, ∀ x, metricScalarAt P.limit.metric x ≤ C) ∧
        MetricNoncollapsed P.limit kappa Set.univ

theorem terminal_limit_global_bound_of_compactnessInput {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (h : TerminalCompactnessInput.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X) :=
  terminal_limit_global_bound_of_frontier hkappa hsigma hPhi h

def TerminalSlabInputShell (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
      TerminalLimitSlabInputs X L

theorem first_backward_slab_of_slabInputShell {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (h : TerminalSlabInputShell.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
        ∃ delta : ℝ, ∃ hd : 0 < delta,
          Nonempty (BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  let _ := hkappa
  let _ := hsigma
  let _ := hPhi
  exact first_backward_slab_of_terminal_limit_slab_inputs h

def TerminalLocalPropagationBound (kappa : ℝ) (c : ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
        ∀ s ∈ Set.Icc (-(X.depth i / 2)) 0, ∀ z : (X.term i).M,
          Set.Icc (s - c / (1 + |(X.term i).S.scalar s z|)) s ⊆ (X.interval i).carrier ∧
            ∀ y v, (y, v) ∈ frozenBackwardCylinder (X.term i).S z s c c
              (1 + |(X.term i).S.scalar s z|) →
              (X.term i).S.scalar v y ≤ 4 * (1 + |(X.term i).S.scalar s z|)

theorem exists_scalar_le_of_mem_recenteredBall_of_localPropagation {kappa : ℝ} {c : ℝ}
    (hc : 0 < c) (hlocal : TerminalLocalPropagationBound.{u} kappa c) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
            ∀ s ∈ Set.Icc (-(X.depth i / 2)) 0, ∀ z y : (X.term i).M,
              (X.term i).S.scalar s z ≤ A →
              metricDistance ((X.term i).S.base.metric s) z y ≤
                c / Real.sqrt (1 + max A (6 * Phi 0)) →
                (X.term i).S.scalar s y ≤ 4 * (1 + max A (6 * Phi 0)) := by
  obtain ⟨epsStar, hepsStar, hprop⟩ := hlocal
  refine ⟨epsStar, hepsStar, fun eps heps hle sigma hsigma Phi hPhi A hA => ?_⟩
  have hPhi0 : 0 < Phi 0 := hPhi.pos 0
  have hLam : 0 < 1 + max A (6 * Phi 0) := by linarith [le_max_right A (6 * Phi 0)]
  refine ⟨4 * (1 + max A (6 * Phi 0)), by linarith, fun X => ?_⟩
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X,
    X.scale_tendsto.eventually (Filter.eventually_ge_atTop (1 : ℝ))] with i hcyl hscale
  intro s hs z y hz hd
  have hdim3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hcarrier : s ∈ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i, hs.1], hs.2⟩
  have hlow : -6 * Phi 0 ≤ (X.term i).S.scalar s z := by
    have h := neg_six_mul_phi_zero_le_scalar (hPhi.rescale (X.scale_pos i))
      (X.pinching i) hdim3 hcarrier z
    have hres : rescalePinchingFunction (X.scale i) Phi 0 = (X.scale i)⁻¹ * Phi 0 := by
      simp only [rescalePinchingFunction, mul_zero]
    rw [hres] at h
    have hinv : (X.scale i)⁻¹ * Phi 0 ≤ Phi 0 := by
      have h1 : (X.scale i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hscale
      nlinarith [hPhi0]
    linarith
  have hL : 1 + |(X.term i).S.scalar s z| ≤ 1 + max A (6 * Phi 0) := by
    have habs : |(X.term i).S.scalar s z| ≤ max A (6 * Phi 0) :=
      abs_le.mpr ⟨by linarith [le_max_right A (6 * Phi 0), hlow],
        le_trans hz (le_max_left A (6 * Phi 0))⟩
    linarith
  have hLpos : 0 < 1 + |(X.term i).S.scalar s z| := by positivity
  have hrad : c / Real.sqrt (1 + max A (6 * Phi 0)) ≤
      c / Real.sqrt (1 + |(X.term i).S.scalar s z|) :=
    div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.mpr hLpos) (Real.sqrt_le_sqrt hL)
  have hmem : (y, s) ∈ frozenBackwardCylinder (X.term i).S z s c c
      (1 + |(X.term i).S.scalar s z|) := by
    refine ⟨?_, ?_⟩
    · refine le_trans ?_ (ENNReal.ofReal_le_ofReal hrad)
      have : PreconnectedSpace (X.term i).M := (X.connected i).toPreconnectedSpace
      have hfin : riemannianEDistOf (I := I3) ((X.term i).S.base.metric s) z y ≠ ⊤ :=
        riemannianEDistOf_ne_top (I := I3) ((X.term i).S.base.metric s) z y
      exact (ENNReal.le_ofReal_iff_toReal_le hfin
        (div_pos hc (Real.sqrt_pos.mpr hLam)).le).mpr
        (by simpa only [metricDistance] using hd)
    · refine ⟨?_, le_rfl⟩
      have hcL : 0 < c / (1 + |(X.term i).S.scalar s z|) := div_pos hc hLpos
      linarith
  obtain ⟨-, hbound⟩ := hcyl s hs z
  exact le_trans (hbound y s hmem) (by linarith)

def RecenteredScalarBoundBeyondRadius (kappa sigma : ℝ) (Phi : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ A D : ℝ, 0 < A → 0 ≤ D → c / Real.sqrt (1 + max A (6 * Phi 0)) < D →
      ∃ C : ℝ, ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
        ∀ s ∈ Set.Icc (-(X.depth i / 2)) 0, ∀ z y : (X.term i).M,
          (X.term i).S.scalar s z ≤ A →
          metricDistance ((X.term i).S.base.metric s) z y ≤ D →
            (X.term i).S.scalar s y ≤ C

theorem recentered_source_bound_of_beyondRadius {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) {c : ℝ} (hc : 0 < c)
    (hlocal : TerminalLocalPropagationBound.{u} kappa c)
    (hfar : RecenteredScalarBoundBeyondRadius.{u} kappa sigma Phi c) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A D : ℝ, 0 ≤ D → ∃ C : ℝ,
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
          ∀ s ∈ Set.Icc (-(X.depth i / 2)) 0, ∀ z y : (X.term i).M,
            (X.term i).S.scalar s z ≤ A →
            metricDistance ((X.term i).S.base.metric s) z y ≤ D →
              (X.term i).S.scalar s y ≤ C := by
  obtain ⟨epsStarL, hepsStarL, hloc⟩ :=
    exists_scalar_le_of_mem_recenteredBall_of_localPropagation hc hlocal
  obtain ⟨epsStarF, hepsStarF, hfar⟩ := hfar
  refine ⟨min epsStarL epsStarF, lt_min hepsStarL hepsStarF, fun eps heps hle A D hD => ?_⟩
  have hleL : eps ≤ epsStarL := le_trans hle (min_le_left _ _)
  have hleF : eps ≤ epsStarF := le_trans hle (min_le_right _ _)
  have hA' : 0 < max A 1 := lt_of_lt_of_le zero_lt_one (le_max_right A 1)
  by_cases hDle : D ≤ c / Real.sqrt (1 + max (max A 1) (6 * Phi 0))
  · obtain ⟨_C, _hC, hbound⟩ := hloc eps heps hleL sigma hsigma Phi hPhi (max A 1) hA'
    exact ⟨4 * (1 + max (max A 1) (6 * Phi 0)), fun X => by
      filter_upwards [hbound X] with i hi
      intro s hs z y hz hd
      exact hi s hs z y (le_trans hz (le_max_left A 1)) (le_trans hd hDle)⟩
  · obtain ⟨C, hbound⟩ := hfar eps heps hleF (max A 1) D hA' hD (lt_of_not_ge hDle)
    exact ⟨C, fun X => by
      filter_upwards [hbound X] with i hi
      intro s hs z y hz hd
      exact hi s hs z y (le_trans hz (le_max_left A 1)) hd⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

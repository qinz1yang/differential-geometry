import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AdditiveDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.FlowBall.DistanceComparison

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
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem terminalParabolicBallNesting_of_ricciTensorBound
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (start K : ℝ)
    (hstart : start ≤ 0) (hK : 0 ≤ K)
    (hcarrier : ∀ i : ℕ, Set.Icc start 0 ⊆ (X.interval i).carrier)
    (hregular : ∀ i : ℕ, Set.Ioo start 0 ⊆ (X.interval i).regular)
    (hric : ∀ i : ℕ, ∀ s ∈ Set.Icc start 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
      0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
        (X.term i).S.ricciAt s x (vec2 v v) ≤
          ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
            ((X.term i).S.base.metric s).inner x v v) :
    ∀ rho : ℝ, 0 < rho → ∃ ρ : ℝ, 0 < ρ ∧
      TerminalParabolicBallNesting X start rho ρ := by
  have hdim : 2 ≤ Module.finrank ℝ ThreeSpace := by
    have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    omega
  have hcoef : 0 ≤ (10 / 3 : ℝ) * ((Module.finrank ℝ ThreeSpace : ℝ) - 1) *
      Real.sqrt K * (0 - start) := by
    have h1 : (0 : ℝ) ≤ (Module.finrank ℝ ThreeSpace : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ Module.finrank ℝ ThreeSpace := by exact_mod_cast hdim
      linarith
    have h3 : (0 : ℝ) ≤ 0 - start := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) (Real.sqrt_nonneg K)) h3
  intro rho hrho
  refine ⟨rho + (10 / 3 : ℝ) * ((Module.finrank ℝ ThreeSpace : ℝ) - 1) *
      Real.sqrt K * (0 - start), by linarith [hrho, hcoef], fun i y hy => ?_⟩
  have : PreconnectedSpace (X.term i).M := (X.connected i).toPreconnectedSpace
  have hcomp : ∀ s ∈ Set.Icc start 0,
      RiemannianMetricComplete (I := I3) ((X.term i).S.base.metric s) :=
    fun s hs => ⟨X.complete i s (hcarrier i hs)⟩
  have hadd := KappaSolutions.ricciFlow_additive_distance_bound_of_ricci_upper (I := I3)
    (S := (X.term i).S) (X.term i).isSolution hdim (X.connected i) hstart hK
    (hcarrier i) (hregular i) hcomp (hric i) (X.term i).basepoint y
  have hd0 : (riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0)
      (X.term i).basepoint y).toReal ≤ rho := by
    simpa only [metricDistance] using hy
  have hle : (riemannianEDistOf (I := I3) ((X.term i).S.base.metric start)
      (X.term i).basepoint y).toReal ≤
      rho + (10 / 3 : ℝ) * ((Module.finrank ℝ ThreeSpace : ℝ) - 1) *
        Real.sqrt K * (0 - start) := by
    linarith [hadd.2, hd0]
  exact (ENNReal.le_ofReal_iff_toReal_le
    (riemannianEDistOf_ne_top (I := I3) ((X.term i).S.base.metric start)
      (X.term i).basepoint y) (by linarith)).mpr hle

theorem terminalParabolicBallNesting_modelDepth_of_ricciTensorBound
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (heps : 0 < eps) {K : ℝ} (hK : 0 ≤ K)
    (hric : ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
      ∀ v : TangentSpace I3 x,
        0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
          (X.term i).S.ricciAt s x (vec2 v v) ≤
            ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
              ((X.term i).S.base.metric s).inner x v v) :
    ∀ rho : ℝ, 0 < rho → ∃ ρ : ℝ, 0 < ρ ∧
      TerminalParabolicBallNesting X (-(modelDepth eps)) rho ρ := by
  have hm : 0 < modelDepth eps := by
    simp only [modelDepth]
    exact inv_pos.mpr heps
  exact terminalParabolicBallNesting_of_ricciTensorBound X (-(modelDepth eps)) K
    (by linarith) hK (fun i => (normalizedSequence_modelDepth_window X heps i).1)
    (fun i s hs => (normalizedSequence_modelDepth_window X heps i).2 ⟨hs.1.le, hs.2⟩) hric

noncomputable def terminalNestingBall {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ) (r : ℝ) (hr : 0 < r) :
    FlowMetricBall (I := I3) (X.term i).S
      ⟨0, by rw [X.carrier_eq i]; exact ⟨by linarith [X.depth_pos i], le_rfl⟩⟩ :=
  { center := (X.term i).basepoint, radius := r, radius_pos := hr }

theorem terminalParabolicBallNesting_of_rmControlledBall
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (start r : ℝ)
    (hr : 0 < r) (hstart : -r ^ 2 ≤ start) (hstart0 : start ≤ 0)
    (hB : ∀ i : ℕ, (terminalNestingBall X i r hr).IsRmControlled)
    (hregular : ∀ i : ℕ, Set.Ioo start 0 ⊆ (X.interval i).regular)
    (rho : ℝ) (hrho : 0 < rho)
    (hsmall : rho * Real.exp (((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 / r ^ 2) *
      (0 - start)) < r) :
    TerminalParabolicBallNesting X start rho
      (Real.exp (((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 / r ^ 2) * (0 - start)) * rho) := by
  have hexp : 0 < Real.exp (((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 / r ^ 2) * (0 - start)) :=
    Real.exp_pos _
  intro i y hy
  have : PreconnectedSpace (X.term i).M := (X.connected i).toPreconnectedSpace
  have hsel : RiemannianMetricComplete (I := I3) ((X.term i).S.base.metric 0) :=
    ⟨X.complete i 0 (by rw [X.carrier_eq i]; exact ⟨by linarith [X.depth_pos i], le_rfl⟩)⟩
  have hd0 : riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0)
      (X.term i).basepoint y ≤ ENNReal.ofReal rho :=
    (ENNReal.le_ofReal_iff_toReal_le
      (riemannianEDistOf_ne_top (I := I3) ((X.term i).S.base.metric 0)
        (X.term i).basepoint y) hrho.le).mpr (by simpa only [metricDistance] using hy)
  have hx : ENNReal.ofReal
        (Real.exp (((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 / r ^ 2) * (0 - start))) *
      riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0) (X.term i).basepoint y <
      ENNReal.ofReal r := by
    refine (mul_le_mul' le_rfl hd0).trans_lt ?_
    rw [← ENNReal.ofReal_mul hexp.le]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).2 (by rw [mul_comm]; exact hsmall)
  have hstB : Set.Icc start 0 ⊆ Set.Icc ((0 : ℝ) - r ^ 2) 0 :=
    fun s hs => ⟨by linarith [hs.1], hs.2⟩
  have hrad : (terminalNestingBall X i r hr).radius = r := rfl
  have hcomp := FlowMetricBall.riemannianEDistOf_le_exp_mul (I := I3)
    (S := (X.term i).S) (X.term i).isSolution (B := terminalNestingBall X i r hr) (hB i)
    hstart0 (hregular i) hstB hsel (x := y) hx
  rw [hrad] at hcomp
  exact (hcomp.trans (mul_le_mul' le_rfl hd0)).trans
    (le_of_eq (ENNReal.ofReal_mul hexp.le).symm)

theorem terminalParabolicCurvatureBound_of_rmBallBound_and_ricciTensorBound
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (heps : 0 < eps) {K : ℝ} (hK : 0 ≤ K)
    (hrm : ∀ ρ : ℝ, 0 < ρ → TerminalParabolicRmBallBound X (-(modelDepth eps)) ρ)
    (hric : ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
      ∀ v : TangentSpace I3 x,
        0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
          (X.term i).S.ricciAt s x (vec2 v v) ≤
            ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
              ((X.term i).S.base.metric s).inner x v v) :
    TerminalParabolicCurvatureBound X (-(modelDepth eps)) :=
  terminalParabolicCurvatureBound_of_scale_windows X (-(modelDepth eps)) hrm
    (terminalParabolicBallNesting_modelDepth_of_ricciTensorBound X heps hK hric)

theorem bounded_curvature_at_distance_of_rmBallBound_and_ricciTensorBound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hrm : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        ∀ ρ : ℝ, 0 < ρ → TerminalParabolicRmBallBound X (-(modelDepth eps)) ρ)
    (hric : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
          0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
            (X.term i).S.ricciAt s x (vec2 v v) ≤
              ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
                ((X.term i).S.base.metric s).inner x v v) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X := by
  obtain ⟨e₁, he₁, hrm₁⟩ := hrm
  obtain ⟨e₂, he₂, hric₂⟩ := hric
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X => ?_⟩
  exact bounded_curvature_at_distance_of_parabolicCurvatureBounds X
    (parabolicCurvatureBoundsAtBase_of_terminalParabolicCurvatureControl X hp
      (terminalParabolicCurvatureControl_of_bound X hp
        (terminalParabolicCurvatureBound_of_rmBallBound_and_ricciTensorBound X hp hK
          (hrm₁ eps hp (hle.trans (min_le_left e₁ e₂)) X)
          (hric₂ eps hp (hle.trans (min_le_right e₁ e₂)) X))))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

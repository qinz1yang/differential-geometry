import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicBallNesting
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicRmBallAtBase
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AdditiveDistance

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

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

def TerminalParabolicRmBallBoundAtSameTime {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (start ρ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ i, ∀ t ∈ Set.Icc start 0, ∀ y : (X.term i).M,
    riemannianEDistOf (I := I3) ((X.term i).S.base.metric t) (X.term i).basepoint y ≤
      ENNReal.ofReal ρ →
    curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ C

theorem terminalParabolicRmBallBound_of_rmBallBoundAtSameTime
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (start ρ K : ℝ) (hρ : 0 ≤ ρ) (hK : 0 ≤ K)
    (hcarrier : ∀ i, Set.Icc start 0 ⊆ (X.interval i).carrier)
    (hregular : ∀ i, Set.Ioo start 0 ⊆ (X.interval i).regular)
    (hric : ∀ i, ∀ s ∈ Set.Icc start 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
      0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
        (X.term i).S.ricciAt s x (vec2 v v) ≤
          ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
            ((X.term i).S.base.metric s).inner x v v)
    (h : TerminalParabolicRmBallBoundAtSameTime X start ρ) :
    TerminalParabolicRmBallBound X start ρ := by
  obtain ⟨C, hC, hb⟩ := h
  have hdim : 2 ≤ Module.finrank ℝ ThreeSpace := by
    have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    omega
  refine ⟨C, hC, fun i t ht y hy => ?_⟩
  have : PreconnectedSpace (X.term i).M := (X.connected i).toPreconnectedSpace
  have hcarrier' : Set.Icc start t ⊆ (X.interval i).carrier :=
    fun s hs => hcarrier i ⟨hs.1, hs.2.trans ht.2⟩
  have hregular' : Set.Ioo start t ⊆ (X.interval i).regular :=
    fun s hs => hregular i ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
  have hcomp : ∀ s ∈ Set.Icc start t,
      RiemannianMetricComplete (I := I3) ((X.term i).S.base.metric s) :=
    fun s hs => ⟨X.complete i s (hcarrier' hs)⟩
  have hadd := KappaSolutions.ricciFlow_additive_distance_bound_of_ricci_upper (I := I3)
    (S := (X.term i).S) (X.term i).isSolution hdim (X.connected i) ht.1 hK hcarrier' hregular'
    hcomp (fun s hs => hric i s ⟨hs.1, hs.2.trans ht.2⟩) (X.term i).basepoint y
  have hstart_le : (riemannianEDistOf (I := I3) ((X.term i).S.base.metric start)
      (X.term i).basepoint y).toReal ≤ ρ :=
    (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top (I := I3)
      ((X.term i).S.base.metric start) (X.term i).basepoint y) hρ).mp hy
  have ht_le : (riemannianEDistOf (I := I3) ((X.term i).S.base.metric t)
      (X.term i).basepoint y).toReal ≤ ρ := by
    linarith [hadd.1]
  exact hb i t ht y ((ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top (I := I3)
    ((X.term i).S.base.metric t) (X.term i).basepoint y) hρ).mpr ht_le)

theorem bounded_curvature_at_distance_of_rmBallBoundAtSameTime_and_ricciTensorBound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hrm : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ ρ : ℝ, 0 < ρ →
        TerminalParabolicRmBallBoundAtSameTime X (-(modelDepth eps)) ρ)
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
  refine bounded_curvature_at_distance_of_rmBallBound_and_ricciTensorBound hK
    ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X ρ hρ => ?_⟩
    ⟨min e₁ e₂, lt_min he₁ he₂,
      fun eps hp hle X => hric₂ eps hp (hle.trans (min_le_right e₁ e₂)) X⟩
  have hm : 0 < modelDepth eps := by
    simp only [modelDepth]
    exact inv_pos.mpr hp
  have hwin := normalizedSequence_modelDepth_window X hp
  exact terminalParabolicRmBallBound_of_rmBallBoundAtSameTime X (-(modelDepth eps)) ρ K
    hρ.le hK (fun i => (hwin i).1)
    (fun i s hs => (hwin i).2 ⟨hs.1.le, hs.2⟩)
    (fun i s hs => hric₂ eps hp (hle.trans (min_le_right e₁ e₂)) X i s hs)
    (hrm₁ eps hp (hle.trans (min_le_left e₁ e₂)) X ρ hρ)

theorem exists_eventually_terminalParabolicRmBallBoundAtSameTime_of_ricciTensorBound
    {kappa K : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) (hK : 0 ≤ K) :
    ∃ epsStar c C : ℝ, 0 < epsStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            (∀ i, ∀ s ∈ Set.Icc (-(c / 2)) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
              0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
                (X.term i).S.ricciAt s x (vec2 v v) ≤
                  ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
                    ((X.term i).S.base.metric s).inner x v v) →
              ∀ᶠ i in Filter.atTop, ∀ t ∈ Set.Icc (-(c / 2)) 0, ∀ y : (X.term i).M,
                riemannianEDistOf (I := I3) ((X.term i).S.base.metric t)
                  (X.term i).basepoint y ≤ ENNReal.ofReal (c / Real.sqrt 2) →
                curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ C := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hprop⟩ :=
    exists_eventually_curvDerivNormSq_le_at_boundedDistance hmod
  refine ⟨epsStar, c, C, hepsStar, hc, hC, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hric
  have hdim : 2 ≤ Module.finrank ℝ ThreeSpace := by
    have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    omega
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X,
    X.depth_tendsto.eventually (Filter.eventually_ge_atTop (c / 4))] with i hi hdeep
  intro t ht y hy
  have hcarrier : Set.Icc (-(c / 2)) 0 ⊆ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    exact fun s hs => ⟨by linarith [hs.1, hdeep], hs.2⟩
  have hregular : Set.Ioo (-(c / 2)) 0 ⊆ (X.interval i).regular := by
    rw [X.regular_eq i]
    exact fun s hs => ⟨by linarith [hs.1, hdeep], hs.2⟩
  have : PreconnectedSpace (X.term i).M := (X.connected i).toPreconnectedSpace
  have hcomp : ∀ s ∈ Set.Icc t 0,
      RiemannianMetricComplete (I := I3) ((X.term i).S.base.metric s) :=
    fun s hs => ⟨X.complete i s (hcarrier ⟨by linarith [hs.1, ht.1], hs.2⟩)⟩
  have hadd := KappaSolutions.ricciFlow_additive_distance_bound_of_ricci_upper (I := I3)
    (S := (X.term i).S) (X.term i).isSolution hdim (X.connected i) ht.2 hK
    (fun s hs => hcarrier ⟨by linarith [hs.1, ht.1], hs.2⟩)
    (fun s hs => hregular ⟨by linarith [hs.1, ht.1], hs.2⟩) hcomp
    (fun s hs => hric i s ⟨le_trans ht.1 hs.1, hs.2⟩) (X.term i).basepoint y
  have ht_le : (riemannianEDistOf (I := I3) ((X.term i).S.base.metric t)
      (X.term i).basepoint y).toReal ≤ c / Real.sqrt 2 :=
    (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top (I := I3)
      ((X.term i).S.base.metric t) (X.term i).basepoint y) (by positivity)).mp hy
  have hzero_le : (riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0)
      (X.term i).basepoint y).toReal ≤ c / Real.sqrt 2 := by
    linarith [hadd.1]
  exact hi t ht y (by simpa only [metricDistance] using hzero_le)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

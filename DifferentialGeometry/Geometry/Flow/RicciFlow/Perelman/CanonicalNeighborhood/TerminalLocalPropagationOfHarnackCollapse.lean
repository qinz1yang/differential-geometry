import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtensionTerminalInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvaturePropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimHarnackCollapseBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimHarnackCollapseBoundReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StandardHarnackLimit

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u uE uH

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem modelCurvatureBoundNearBase_of_harnackCollapseBound (hdim : Module.finrank ℝ E = 3)
    {kappa : ℝ} (h : KappaSolutions.KLimHarnackCollapseBound.{u, uE, uH} (I := I) kappa) :
    ModelCurvatureBoundNearBase.{u, uE, uH} I kappa := by
  obtain ⟨C, hC, hbound⟩ :=
    KappaSolutions.exists_normalized_klim_local_curvature_constants_of_harnackCollapse
      (I := I) hdim h
  refine ⟨Real.sqrt 3 * C 3, mul_nonneg (Real.sqrt_nonneg _) (hC 3).le, ?_⟩
  intro L hL hbase s hs y hy
  have hK : KappaSolutions.KLim (I := I) kappa L :=
    KappaSolutions.ancientKappaThree_toKLim (I := I) L hL hdim
  have h := (hbound ancientTimeInterval L hK hbase 3 y hy s hs.2).2
  calc L.rmNormSq (I := I) s y ≤ 3 * C 3 ^ 2 := h
    _ = (Real.sqrt 3 * C 3) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem local_propagation_of_harnackCollapseBound {kappa : ℝ}
    (h : KappaSolutions.KLimHarnackCollapseBound.{u, 0, 0} (I := I3) kappa) :
    ∃ epsStar c C : ℝ, 0 < epsStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
            ∀ s ∈ Set.Icc (-(X.depth i / 2)) 0, ∀ z : (X.term i).M,
              let L := 1 + |(X.term i).S.scalar s z|
              Set.Icc (s - c / L) s ⊆ (X.interval i).carrier ∧
                ∀ y v, (y, v) ∈ frozenBackwardCylinder (X.term i).S z s c c L →
                  -6 * (X.scale i)⁻¹ * Phi 0 ≤ (X.term i).S.scalar v y ∧
                  (X.term i).S.scalar v y ≤ 4 * L ∧
                  Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S v y) ≤
                    C * (L + (Phi (4 * X.scale i * L) + Phi 0) / X.scale i) :=
  local_propagation_of_modelBound
    (modelCurvatureBoundNearBase_of_harnackCollapseBound (I := I3) (by simp [ThreeSpace]) h)

theorem good_point_derivatives_of_harnackCollapseBound {kappa : ℝ}
    (h : KappaSolutions.KLimHarnackCollapseBound.{u, 0, 0} (I := I3) kappa) :
    ∃ epsStar C : ℝ, 0 < epsStar ∧ 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → interior D.carrier ⊆ D.regular →
          ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ x t, Nonempty (WindowedModelWitness eps kappa S x t) →
            (∀ v : TangentSpace I3 x, |scalarDifferential S t x v| ≤
              2 * C * S.scalar t x * Real.sqrt (S.scalar t x) *
                Real.sqrt ((S.base.metric t).inner x v v)) ∧
            |derivWithin (fun s => S.scalar s x) (Set.Iic t) t| ≤ C * S.scalar t x ^ 2 :=
  good_point_derivatives_of_modelCurvatureBound
    (modelCurvatureBoundNearBase_of_harnackCollapseBound (I := I3) (by simp [ThreeSpace]) h)

theorem exists_terminalLocalPropagationBound_of_harnackCollapseBound {kappa : ℝ}
    (h : KappaSolutions.KLimHarnackCollapseBound.{u, 0, 0} (I := I3) kappa) :
    ∃ c : ℝ, 0 < c ∧ TerminalLocalPropagationBound.{u} kappa c := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hprop⟩ :=
    local_propagation_of_harnackCollapseBound h
  refine ⟨c, hc, epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X
  filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X] with i hi
  intro s hs z
  exact ⟨(hi s hs z).1, fun y v hv => ((hi s hs z).2 y v hv).2.1⟩

theorem terminal_local_propagation_of_harnackCollapseBound {kappa : ℝ}
    (h : KappaSolutions.KLimHarnackCollapseBound.{u, 0, 0} (I := I3) kappa) :
    ∃ c : ℝ, 0 < c ∧ TerminalLocalPropagationBound.{u} kappa c :=
  exists_terminalLocalPropagationBound_of_harnackCollapseBound h

theorem exists_terminalLocalPropagationBound_of_normalizedSeedVolumeBound_and_threeCollapseRadius
    {kappa : ℝ} (hseed : KappaSolutions.KLimNormalizedSeedVolumeBound.{u, 0, 0} (I := I3) kappa)
    (hcollapse : KappaSolutions.KLimThreeCollapseRadius.{u, 0, 0} (I := I3) kappa) :
    ∃ c : ℝ, 0 < c ∧ TerminalLocalPropagationBound.{u} kappa c :=
  exists_terminalLocalPropagationBound_of_harnackCollapseBound
    (KappaSolutions.kLimHarnackCollapseBound_of_normalizedSeedVolumeBound_and_threeCollapseRadius
      (I := I3) (by simp [ThreeSpace]) hseed hcollapse)

theorem exists_terminalLocalPropagationBound_of_nonpos {kappa : ℝ} (h : kappa ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ TerminalLocalPropagationBound.{u} kappa c :=
  exists_terminalLocalPropagationBound_of_harnackCollapseBound
    (KappaSolutions.kLimHarnackCollapseBound_of_nonpos (I := I3) (by simp [ThreeSpace]) h)

theorem recentered_source_bound_of_harnackCollapseBound {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (h : KappaSolutions.KLimHarnackCollapseBound.{u, 0, 0} (I := I3) kappa) :
    ∃ c : ℝ, 0 < c ∧ TerminalLocalPropagationBound.{u} kappa c ∧
      (RecenteredScalarBoundBeyondRadius.{u} kappa sigma Phi c →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ A D : ℝ, 0 ≤ D → ∃ C : ℝ,
            ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
              ∀ s ∈ Set.Icc (-(X.depth i / 2)) 0, ∀ z y : (X.term i).M,
                (X.term i).S.scalar s z ≤ A →
                metricDistance ((X.term i).S.base.metric s) z y ≤ D →
                  (X.term i).S.scalar s y ≤ C) := by
  obtain ⟨c, hc, hlocal⟩ := exists_terminalLocalPropagationBound_of_harnackCollapseBound h
  exact ⟨c, hc, hlocal, fun hfar =>
    recentered_source_bound_of_beyondRadius hsigma hPhi hc hlocal hfar⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

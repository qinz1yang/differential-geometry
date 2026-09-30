import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ReservedCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundImageVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedRoundCanonical
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_reservedCanonical_of_roundWindow
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 11) :
    ∃ C δ₀ : ℝ, 1 ≤ C ∧ 0 < δ₀ ∧ δ₀ < 1 ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
        {δ κ : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness δ κ S x t),
        δ ≤ δ₀ → IsSolutionOn S →
        Ioo (t - (δ * S.scalar t x)⁻¹) t ⊆ D.regular →
        IsShrinkingSphericalSpaceFormFlow W.model →
        Nonempty (ReservedCanonicalWitness (S.base.metric t) ε C C (κ/32) x) := by
  obtain ⟨C,d,hC,hd,hprod⟩ :=
    exists_windowed_bufferedCanonical_with_cap_neck_charts_of_round_model.{u} hε hsmall 1
  let A : ℝ := 2 * (Real.pi / Real.sqrt (1/6)) + 1
  have hA : 0 < A := by dsimp [A]; positivity
  let b : ℝ := ((2*A)⁻¹)^2
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨C,min d (min (1/2) b),hC,lt_min hd (lt_min (by norm_num) hb),
    lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num),?_⟩
  intro M _ _ _ _ _ D S δ κ x t W hδ hS hreg hround
  have hδhalf : δ ≤ 1/2 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδb : δ ≤ b := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hbuf : 2*A ≤ modelRadius δ := by
    calc
      2*A = modelRadius b := by
        dsimp [b,modelRadius]
        rw [Real.sqrt_sq (by positivity),inv_inv]
      _ ≤ modelRadius δ := modelRadius_anti W.eps_pos hδb
  obtain ⟨B,hB⟩ := hprod W (hδ.trans (min_le_left _ _)) hS hreg hround
  let K := B.canonicalWitnessMono B.tolerance_lt.le hsmall
  have hchart : K.capTubeHasNeckChart ε := hB.mono_eps B.tolerance_lt.le hsmall
  refine ⟨⟨K.toSpatial,K.capTubeHasNeckChart_toSpatial hchart,fun _ => ?_⟩⟩
  exact roundModelComponentVolume W hround hδhalf hbuf

theorem exists_roundWindow_ball_bound {ε κ : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 11) (hκ : 0 < κ) :
    ∃ δ₀ k : ℝ, 0 < δ₀ ∧ 0 < k ∧
      ∀ {P : OrientedThreeStage.{u}} {D : RealTimeInterval}
        {S : SolutionOn (I := I3) (M := P.Carrier) D}
        {δ : ℝ} {x : P.Carrier} {t : ℝ} (W : WindowedModelWitness δ κ S x t),
        δ ≤ δ₀ → IsSolutionOn S →
        Ioo (t - (δ * S.scalar t x)⁻¹) t ⊆ D.regular →
        IsShrinkingSphericalSpaceFormFlow W.model →
        ∀ r : ℝ, 0 < r → r^4 * DifferentialGeometry.Tensor0SBundle.normSq0S
          (S.base.metric t) x 4 (metricRm04At (S.base.metric t) x) ≤ 1 →
        ENNReal.ofReal (k*r^3) ≤ DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
          I3 P.Carrier (S.base.metric t) (riemannianBallOf (S.base.metric t) x r) := by
  obtain ⟨C,d,_,hd,_,hprod⟩ := exists_reservedCanonical_of_roundWindow.{u} hε hsmall
  obtain ⟨k,hk,hball⟩ := reservedCanonicalBallConsumer.{u} ε C C (κ/32) (by positivity)
  refine ⟨d,k,hd,hk,?_⟩
  intro P D S δ x t W hδ hS hreg hround r hr hcurv
  obtain ⟨V⟩ := hprod W hδ hS hreg hround
  exact hball V r hr hcurv

end GC.GeneralFlow

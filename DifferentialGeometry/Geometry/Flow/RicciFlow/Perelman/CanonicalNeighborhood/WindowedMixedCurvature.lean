import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedShiTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.JetPolynomialBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.MixedJetPolynomials
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.MixedCurvature

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_windowedModelWitness_normalized_mixedCurvatureNorm_bound
    (K : ℝ) (hK : 0 ≤ K) (p q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D},
        IsSolutionOn S → ∀ {eps kappa : ℝ} {x : M} {t : ℝ}
        (W : WindowedModelWitness eps kappa S x t), eps ≤ 1 / 4 →
        interior D.carrier ⊆ D.regular → t ∈ D.regular →
        (∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
          riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
            W.model.rmNormSq s y ≤ K ^ 2) →
        mixedCurvatureNorm
          (parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem) p q 0 x ≤ C := by
  classical
  obtain ⟨P, hP⟩ := exists_mixed_curvature_jet_polynomials.{u, 0, 0} 3 p q
  refine ⟨1 + curvatureJetPolynomialNormBound P (windowedShiConstant K), ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg _)
  intro M _ _ _ _ _ D S hS eps kappa x t W heps hregular ht hmodel
  let F := parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem
  have hF : IsSolutionOn F :=
    parabolicSolution_isSolutionOn S hS t _ W.scalar_pos W.time_mem
  let : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I3 2 M := IsManifold.of_le (n := ∞) (by decide)
  have hzero : (0 : ℝ) ∈ (parabolicInterval D t (S.scalar t x) W.time_mem).regular := by
    simpa only [parabolicInterval_regular, Set.mem_ofPred_eq, parabolicTime_zero] using ht
  have hdim : Module.finrank ℝ (TangentSpace I3 x) = 3 := by
    change Module.finrank ℝ ThreeSpace = 3
    simp [ThreeSpace]
  obtain ⟨basis, hON⟩ := exists_orthonormalBasisAt (I := I3) (F.base.metric 0) x hdim
  obtain ⟨_, hcomp⟩ := hP F hF 0 hzero x basis
  have hjet (j : ℕ) : curvDerivNorm (I := I3) j (F.base.metric 0) x ≤
      windowedShiConstant K j := by
    have hsq := W.normalized_terminal_curvature_derivative_bound
      hS heps hK hregular hmodel j
    have hC : 0 ≤ windowedShiConstant K j :=
      mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) (sourceCurvatureBound_pos 3 hK).le
    have hb := Real.sqrt_le_iff.mpr ⟨hC, hsq⟩
    exact (congrArg Real.sqrt (curvNormSq_eq (I := I3) F j 0 x)).le.trans hb
  have hb := norm_le_curvatureJetPolynomialNormBound F 0 basis hON P
    (mixedCurvatureTensor F p q 0 x) hcomp (windowedShiConstant K) (fun j _ => hjet j)
  exact hb.trans (le_add_of_nonneg_left zero_le_one)


theorem exists_windowedModelWitness_mixedCurvatureNorm_bound
    (K : ℝ) (hK : 0 ≤ K) (p q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D},
        IsSolutionOn S → ∀ {eps kappa : ℝ} {x : M} {t : ℝ}
        (W : WindowedModelWitness eps kappa S x t), eps ≤ 1 / 4 →
        interior D.carrier ⊆ D.regular → t ∈ D.regular →
        (∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
          riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
            W.model.rmNormSq s y ≤ K ^ 2) →
        mixedCurvatureNorm S p q t x ≤ C * (S.scalar t x) ^ (1 + (p : ℝ) / 2 + q) := by
  obtain ⟨C, hC, hbound⟩ := exists_windowedModelWitness_normalized_mixedCurvatureNorm_bound K hK p q
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ D S hS eps kappa x t W heps hregular ht hmodel
  have hb := hbound hS W heps hregular ht hmodel
  have hscale := mixedCurvatureNorm_parabolicSolution S hS t (S.scalar t x)
    W.scalar_pos W.time_mem p q (s := 0) (by simpa only [parabolicTime_zero] using ht) x
  rw [parabolicTime_zero] at hscale
  rw [hscale] at hb
  have hcancel : (S.scalar t x) ^ (1 + (p : ℝ) / 2 + q) *
      (S.scalar t x) ^ (-(1 : ℝ) - (p : ℝ) / 2 - q) = 1 := by
    rw [← Real.rpow_add W.scalar_pos,
      show (1 + (p : ℝ) / 2 + q) + (-(1 : ℝ) - (p : ℝ) / 2 - q) = 0 by ring,
      Real.rpow_zero]
  have hmul := mul_le_mul_of_nonneg_left hb
    (Real.rpow_nonneg W.scalar_pos.le (1 + (p : ℝ) / 2 + q))
  rw [← mul_assoc, hcancel, one_mul] at hmul
  simpa only [mul_comm] using hmul

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedShiTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.JetPolynomialBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.MixedJetPolynomials
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.MixedCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.MixedCurvature

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
        Ioo (t - (eps * S.scalar t x)⁻¹) t ⊆ D.regular → t ∈ D.regular →
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
        Ioo (t - (eps * S.scalar t x)⁻¹) t ⊆ D.regular → t ∈ D.regular →
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

theorem exists_windowedModelWitness_normalized_mixedCurvatureNorm_bound_on_inner_ball
    (K : ℝ) (hK : 0 ≤ K) (p q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D},
        IsSolutionOn S → ∀ {eps kappa : ℝ} {x : M} {t : ℝ}
        (W : WindowedModelWitness eps kappa S x t), eps ≤ 1 / 4 →
        Ioo (t - (eps * S.scalar t x)⁻¹) t ⊆ D.regular → t ∈ D.regular →
        (∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
          riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
            W.model.rmNormSq s y ≤ K ^ 2) →
        ∀ y ∈ riemannianClosedBallOf
          (rescaledMetric S t (S.scalar t x) W.scalar_pos (-1)) x (1 / 2),
        mixedCurvatureNorm
          (parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem) p q 0 y ≤ C := by
  let K0 := sourceCurvatureBound 3 K
  have hK0 : 0 < K0 := sourceCurvatureBound_pos 3 hK
  have hsqrt : 0 < Real.sqrt K0 := Real.sqrt_pos.mpr hK0
  obtain ⟨C, hC, hbound⟩ := exists_mixedCurvatureNorm_bound_on_curvature_cylinder.{u, 0, 0}
    3 p q (by norm_num) hK0 hsqrt (tau := 1) zero_lt_one
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ D S hS eps kappa x t W heps hregular ht hmodel y hy
  let F := parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem
  have hF : IsSolutionOn F :=
    parabolicSolution_isSolutionOn S hS t _ W.scalar_pos W.time_mem
  let D' := parabolicInterval D t (S.scalar t x) W.time_mem
  have hzero : (0 : ℝ) ∈ D'.regular := by
    simpa only [D', parabolicInterval_regular, Set.mem_ofPred_eq, parabolicTime_zero] using ht
  have hreg : Icc (-1 : ℝ) 0 ⊆ D'.regular := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | rfl
    · exact (W.normalized_fixed_window heps hregular).2 ⟨by linarith [hs.1], hlt⟩
    · exact hzero
  obtain ⟨hball, hcurv⟩ := W.unitBall_compact_curvature_bound heps hK hmodel
    (a := -1) (by norm_num)
  have hball' : IsCompact {z : M | riemannianEDistOf (I := I3) (F.base.metric (-1)) x z ≤
      ENNReal.ofReal (Real.sqrt K0 / Real.sqrt K0)} := by
    rw [div_self hsqrt.ne']
    exact hball
  have hcurv' : ∀ s ∈ Icc (-1 : ℝ) (-1 + 1), ∀ z : M,
      riemannianEDistOf (I := I3) (F.base.metric (-1)) x z ≤
        ENNReal.ofReal (Real.sqrt K0 / Real.sqrt K0) →
      curvDerivNormSq (I := I3) 0 (F.base.metric s) z ≤ K0 ^ 2 := by
    intro s hs z hz
    rw [div_self hsqrt.ne'] at hz
    exact hcurv s ⟨by linarith [hs.1], by linarith [hs.2]⟩ z hz
  have hhalf : Real.sqrt K0 / (2 * Real.sqrt K0) = (1 : ℝ) / 2 := by
    field_simp
  have hy' : riemannianEDistOf (I := I3) (F.base.metric (-1)) x y ≤
      ENNReal.ofReal (Real.sqrt K0 / (2 * Real.sqrt K0)) := by
    rw [hhalf]
    exact hy
  have h := hbound F hF (by simp [ThreeSpace]) (-1)
    (by simpa only [neg_add_cancel] using hreg) x hball' hcurv' y hy'
  simpa only [neg_add_cancel] using h

theorem exists_windowedModelWitness_mixedCurvatureNorm_bound_on_inner_ball
    (K : ℝ) (hK : 0 ≤ K) (p q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D},
        IsSolutionOn S → ∀ {eps kappa : ℝ} {x : M} {t : ℝ}
        (W : WindowedModelWitness eps kappa S x t), eps ≤ 1 / 4 →
        Ioo (t - (eps * S.scalar t x)⁻¹) t ⊆ D.regular → t ∈ D.regular →
        (∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
          riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
            W.model.rmNormSq s y ≤ K ^ 2) →
        ∀ y ∈ riemannianClosedBallOf
          (rescaledMetric S t (S.scalar t x) W.scalar_pos (-1)) x (1 / 2),
        mixedCurvatureNorm S p q t y ≤ C * (S.scalar t x) ^ (1 + (p : ℝ) / 2 + q) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_windowedModelWitness_normalized_mixedCurvatureNorm_bound_on_inner_ball K hK p q
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ D S hS eps kappa x t W heps hregular ht hmodel y hy
  have hb := hbound hS W heps hregular ht hmodel y hy
  have hscale := mixedCurvatureNorm_parabolicSolution S hS t (S.scalar t x)
    W.scalar_pos W.time_mem p q (s := 0) (by simpa only [parabolicTime_zero] using ht) y
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

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_windowedModelWitness_mixedCurvatureNorm_bound_on_terminal_ball
    (K : ℝ) (hK : 0 ≤ K) (p q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D},
        IsSolutionOn S → ∀ {eps kappa : ℝ} {x : M} {t : ℝ}
        (W : WindowedModelWitness eps kappa S x t), eps ≤ 1 / 4 →
        Ioo (t - (eps * S.scalar t x)⁻¹) t ⊆ D.regular → t ∈ D.regular →
        (∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ z ∈
          riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
            W.model.rmNormSq s z ≤ K ^ 2) →
        ∀ y ∈ riemannianClosedBallOf (S.base.metric t) x
          ((1 / (4 * Real.exp (9 * sourceCurvatureBound 3 K))) /
            Real.sqrt (S.scalar t x)),
          mixedCurvatureNorm S p q t y ≤ C * (S.scalar t x) ^ (1 + (p : ℝ) / 2 + q) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_windowedModelWitness_mixedCurvatureNorm_bound_on_inner_ball K hK p q
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ D S hS eps kappa x t W heps hregular ht hmodel y hy
  let r : ℝ := 1 / (4 * Real.exp (9 * sourceCurvatureBound 3 K))
  have hprod : Real.sqrt (S.scalar t x) * (r / Real.sqrt (S.scalar t x)) = r := by
    rw [mul_comm, div_mul_cancel₀ _ (Real.sqrt_pos.mpr W.scalar_pos).ne']
  have hball := riemannianClosedBallOf_scaleMetric (S.scalar t x) W.scalar_pos
    (S.base.metric t) x (r / Real.sqrt (S.scalar t x))
  rw [hprod] at hball
  have hynorm : y ∈ riemannianClosedBallOf
      (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x r := by
    rw [rescaledMetric, parabolicTime_zero, hball]
    exact hy
  have hyinner := (W.terminal_ball_isCompact_subset_inner_ball hS heps hK hregular hmodel).2 hynorm
  exact hbound hS W heps hregular ht hmodel y hyinner

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_windowedModelWitness_scalar_weighted_mixedCurvatureNorm_bound
    (K : ℝ) (hK : 0 ≤ K) (p q : ℕ) :
    ∃ C rho : ℝ, 0 < C ∧ 0 < rho ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D},
        IsSolutionOn S → ∀ {eps kappa : ℝ} {x : M} {t : ℝ}
        (W : WindowedModelWitness eps kappa S x t), eps ≤ 1 / 4 →
        Ioo (t - (eps * S.scalar t x)⁻¹) t ⊆ D.regular → t ∈ D.regular →
        (∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ z ∈
          riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
            W.model.rmNormSq s z ≤ K ^ 2) →
        ∀ y ∈ riemannianClosedBallOf (S.base.metric t) x
          (rho / Real.sqrt (S.scalar t x)),
          0 < S.scalar t y ∧
            mixedCurvatureNorm S p q t y ≤ C * (S.scalar t y) ^ (1 + (p : ℝ) / 2 + q) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_windowedModelWitness_mixedCurvatureNorm_bound_on_terminal_ball K hK p q
  obtain ⟨rho, hrho, hrhole, hscalar⟩ :=
    exists_windowedModelWitness_normalized_terminal_scalar_lower_bound K hK
  let w : ℝ := 1 + (p : ℝ) / 2 + q
  refine ⟨C * 2 ^ w, rho, mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), hrho, ?_⟩
  intro M _ _ _ _ _ D S hS eps kappa x t W heps hregular ht hmodel y hy
  have hprod : Real.sqrt (S.scalar t x) * (rho / Real.sqrt (S.scalar t x)) = rho := by
    rw [mul_comm, div_mul_cancel₀ _ (Real.sqrt_pos.mpr W.scalar_pos).ne']
  have hball := riemannianClosedBallOf_scaleMetric (S.scalar t x) W.scalar_pos
    (S.base.metric t) x (rho / Real.sqrt (S.scalar t x))
  rw [hprod] at hball
  have hynorm : y ∈ riemannianClosedBallOf
      (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x rho := by
    rw [rescaledMetric, parabolicTime_zero, hball]
    exact hy
  have hs := hscalar hS W heps hregular hmodel y hynorm
  rw [rescaledMetric, parabolicTime_zero, metricScalarAt_scaleMetric] at hs
  change (1 / 2 : ℝ) ≤ (S.scalar t x)⁻¹ * S.scalar t y at hs
  have hhalf : S.scalar t x / 2 ≤ S.scalar t y := by
    have hh := mul_le_mul_of_nonneg_left hs W.scalar_pos.le
    rw [← mul_assoc, mul_inv_cancel₀ W.scalar_pos.ne', one_mul] at hh
    linarith
  have hypos : 0 < S.scalar t y := (half_pos W.scalar_pos).trans_le hhalf
  refine ⟨hypos, ?_⟩
  have hybig : y ∈ riemannianClosedBallOf (S.base.metric t) x
      ((1 / (4 * Real.exp (9 * sourceCurvatureBound 3 K))) /
        Real.sqrt (S.scalar t x)) :=
    riemannianClosedBallOf_mono (S.base.metric t) x
      (div_le_div_of_nonneg_right hrhole (Real.sqrt_nonneg _)) hy
  have hb := hbound hS W heps hregular ht hmodel y hybig
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hpow : (S.scalar t x) ^ w ≤ 2 ^ w * (S.scalar t y) ^ w := by
    calc (S.scalar t x) ^ w ≤ (2 * S.scalar t y) ^ w :=
          Real.rpow_le_rpow W.scalar_pos.le (by linarith) hw
      _ = 2 ^ w * (S.scalar t y) ^ w := Real.mul_rpow (by norm_num) hypos.le
  exact hb.trans ((mul_le_mul_of_nonneg_left hpow hC.le).trans_eq (mul_assoc _ _ _).symm)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedSourceCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonSectionalCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtensionLimitInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalCurvatureBounds
import Mathlib.Analysis.SpecificLimits.Basic

section
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance sourceSectionalC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem WindowedModelWitness.source_closedBall_compact_secLower
    {eps kappa R r K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t)
    (heps : eps ≤ 1 / 4) (hR : 0 < R) (hRfull : R + 1 ≤ modelRadius eps)
    (hr : r < Real.sqrt (1 - eps) * R) (hK : 0 ≤ K)
    (hrm : ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0)
      W.model.basepoint (R + 1), W.model.rmNormSq 0 y ≤ K ^ 2) :
    IsCompact (riemannianClosedBallOf
      (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x r) ∧
      SecLower (rescaledMetric S t (S.scalar t x) W.scalar_pos 0)
        (-(4 * eps * (360 + K))) (riemannianClosedBallOf
          (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x r) := by
  have ht : (0 : ℝ) ∈ Icc (-modelDepth eps) 0 :=
    ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩
  obtain ⟨hcompact, hcapture⟩ := W.source_closedBall_compact_subset hR
    (by linarith) hr ht
  let U : TopologicalSpace.Opens W.model.M :=
    ⟨riemannianBallOf (W.model.S.base.metric 0) W.model.basepoint (R + 1),
      isOpen_lt (continuous_riemannianEDist (W.model.S.base.metric 0) W.model.basepoint)
        continuous_const⟩
  have hUball : (U : Set W.model.M) ⊆ riemannianClosedBallOf (W.model.S.base.metric 0)
      W.model.basepoint (R + 1) := by
    intro y hy
    change riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint y <
      ENNReal.ofReal (R + 1) at hy
    exact hy.le
  have hUA : (U : Set W.model.M) ⊆ riemannianClosedBallOf (W.model.S.base.metric 0)
      W.model.basepoint (modelRadius eps) :=
    hUball.trans (riemannianClosedBallOf_mono _ _ hRfull)
  have hUsource : (U : Set W.model.M) ⊆ W.embedding.source :=
    hUA.trans ((riemannianClosedBallOf_mono _ _ (le_add_of_nonneg_right zero_le_one)).trans
      W.buffered_ball)
  have hnonnegative := secLower_of_pointedFlowNonnegativeCurvatureOperator W.model 0
    (W.model_ancient.nonnegativeCurvatureOperator 0
      (by change (0 : ℝ) ≤ 0; exact le_rfl))
  have hsec := W.comparison.secLower_image U hUsource hUA ht (by linarith)
    (show 2 ≤ modelOrder eps from (by have hh := five_le_modelOrder W.eps_pos heps; omega))
    (show (0 : ℝ) ≤ 0 from le_rfl) hK (fun y _ => hnonnegative y (mem_univ _))
    (fun y hy => hrm y (hUball hy))
  refine ⟨hcompact, ?_⟩
  intro z hz v w
  obtain ⟨y, hy, rfl⟩ := hcapture hz
  have hyU : y ∈ (U : Set W.model.M) := by
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < R + 1)).mpr
      (by linarith))
  have hh := hsec (W.embedding y) ⟨y, hyU, rfl⟩ v w
  simpa only [zero_add, zero_sub] using hh

theorem exists_source_closedBall_compact_secLower_tolerance
    {r eta K : ℝ} (hr : 0 ≤ r) (heta : 0 < eta) (hK : 0 ≤ K) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
        (eps kappa : ℝ) (x : M) (t : ℝ) (W : WindowedModelWitness eps kappa S x t),
        eps ≤ delta →
        (∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0)
          W.model.basepoint (2 * r + 2), W.model.rmNormSq 0 y ≤ K ^ 2) →
        IsCompact (riemannianClosedBallOf
          (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x r) ∧
          SecLower (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) (-eta)
            (riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x r) := by
  let R := 2 * r + 2
  have hR : 0 < R := by dsimp only [R]; linarith
  let delta := min (1 / 4 : ℝ) (min (R⁻¹ ^ 2) (eta / (4 * (360 + K))))
  have hd : 0 < delta := lt_min (by norm_num)
    (lt_min (sq_pos_of_pos (inv_pos.mpr hR)) (div_pos heta (by positivity)))
  refine ⟨delta, hd, ?_⟩
  intro M _ _ _ _ D S eps kappa x t W heps hrm
  have heps4 : eps ≤ 1 / 4 := heps.trans (min_le_left _ _)
  have hepsR : eps ≤ R⁻¹ ^ 2 := heps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsK : eps ≤ eta / (4 * (360 + K)) :=
    heps.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hRfull : R ≤ modelRadius eps := by
    have hh := modelRadius_anti W.eps_pos hepsR
    rwa [modelRadius, Real.sqrt_sq (inv_nonneg.mpr hR.le), inv_inv] at hh
  have hsqrt : (1 / 2 : ℝ) < Real.sqrt (1 - eps) := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    linarith
  have hmodel : ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0)
      W.model.basepoint ((2 * r + 1) + 1), W.model.rmNormSq 0 y ≤ K ^ 2 := by
    simpa only [add_assoc, one_add_one_eq_two] using hrm
  obtain ⟨hc, hs⟩ := W.source_closedBall_compact_secLower heps4
    (show 0 < 2 * r + 1 by linarith)
    (by simpa only [R, add_assoc, one_add_one_eq_two] using hRfull)
    (show r < Real.sqrt (1 - eps) * (2 * r + 1) by nlinarith) hK hmodel
  refine ⟨hc, hs.mono ?_⟩
  have hh := (le_div_iff₀ (by positivity : 0 < 4 * (360 + K))).mp hepsK
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

end

section
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_uniform_source_closedBall_compact_secLower_tolerance
    {r eta : ℝ} (hr : 0 ≤ r) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
        (eps kappa : ℝ) (x : M) (t : ℝ) (W : WindowedModelWitness eps kappa S x t),
        eps ≤ delta →
        IsCompact (riemannianClosedBallOf
          (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x r) ∧
          SecLower (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) (-eta)
            (riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x r) := by
  obtain ⟨C, hC, hbound⟩ := KappaSolutions.exists_universal_normalized_ancient_curvature_bounds.{u}
  let K := Real.sqrt (C (2 * r + 2))
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  obtain ⟨delta, hdelta, hsource⟩ := exists_source_closedBall_compact_secLower_tolerance hr heta hK
  refine ⟨delta, hdelta, ?_⟩
  intro M _ _ _ _ D S eps kappa x t W heps
  apply hsource M D S eps kappa x t W heps
  intro y hy
  have hh := hbound kappa W.model W.model_ancient W.model_scalar_base (2 * r + 2) y hy 0 le_rfl
  have heq : K ^ 2 = C (2 * r + 2) := Real.sq_sqrt (hC _).le
  rwa [heq]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

end

section
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_uniform_windowed_tolerances_for_growing_source_balls :
    ∃ delta : ℕ → ℝ, (∀ i, 0 < delta i) ∧ Tendsto delta atTop (𝓝 0) ∧
      ∀ (M : ℕ → Type u) [∀ i, TopologicalSpace (M i)]
        [∀ i, ChartedSpace ThreeSpace (M i)] [∀ i, IsManifold I3 ∞ (M i)]
        [∀ i, T2Space (M i)] (D : ℕ → RealTimeInterval)
        (S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)) (kappa : ℝ)
        (x : ∀ i, M i) (t eps : ℕ → ℝ)
        (W : ∀ i, WindowedModelWitness (eps i) kappa (S i) (x i) (t i)),
        (∀ i, eps i ≤ delta i) → Tendsto eps atTop (𝓝 0) ∧
          ∀ i, IsCompact (riemannianClosedBallOf
              (rescaledMetric (S i) (t i) ((S i).scalar (t i) (x i)) (W i).scalar_pos 0)
              (x i) (8 * ((i : ℝ) + 1))) ∧
            SecLower (rescaledMetric (S i) (t i) ((S i).scalar (t i) (x i)) (W i).scalar_pos 0)
              (-(((i : ℝ) + 1)⁻¹ ^ 4)) (riemannianClosedBallOf
                (rescaledMetric (S i) (t i) ((S i).scalar (t i) (x i)) (W i).scalar_pos 0)
                (x i) (8 * ((i : ℝ) + 1))) := by
  have hn (i : ℕ) : 0 < (i : ℝ) + 1 := by positivity
  have htol (i : ℕ) := exists_uniform_source_closedBall_compact_secLower_tolerance
    (r := 8 * ((i : ℝ) + 1)) (eta := ((i : ℝ) + 1)⁻¹ ^ 4)
    (by positivity) (pow_pos (inv_pos.mpr (hn i)) _)
  choose d hd hspec using htol
  let delta := fun i => min (d i) (((i : ℝ) + 1)⁻¹)
  have hdelta (i : ℕ) : 0 < delta i := lt_min (hd i) (inv_pos.mpr (hn i))
  have hinv : Tendsto (fun i : ℕ => ((i : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1)) atTop (𝓝 0))
  have hzero : Tendsto delta atTop (𝓝 0) := squeeze_zero (fun i => (hdelta i).le)
    (fun i => min_le_right _ _) hinv
  refine ⟨delta, hdelta, hzero, ?_⟩
  intro M _ _ _ _ D S kappa x t eps W heps
  refine ⟨squeeze_zero (fun i => (W i).eps_pos.le) heps hzero, ?_⟩
  intro i
  exact hspec i (M i) (D i) (S i) (eps i) kappa (x i) (t i) (W i)
    ((heps i).trans (min_le_left _ _))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

end

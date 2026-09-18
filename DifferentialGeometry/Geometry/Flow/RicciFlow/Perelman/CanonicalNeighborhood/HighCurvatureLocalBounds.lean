import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedShiTerminal

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_high_curvature_rescaled_curvature_derivative_bounds :
    ∃ C : ℝ → ℕ → ℝ, (∀ r m, 0 < C r m) ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
        [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
        (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT)),
        IsSolutionOn S → TangentOrientationSection M →
        ∀ r A : ℝ, 0 < r → 0 ≤ A →
        ∃ Q0 : ℝ, ∃ hQ0 : 0 < Q0, ∀ x t, t ∈ Ico 0 T →
          ∀ hQ : Q0 ≤ S.scalar t x,
            (∀ s ∈ Icc (-A) 0, parabolicTime t (S.scalar t x) s ∈ Ico 0 T) ∧
            ∀ a ∈ Icc (-A) 0, ∀ s ∈ Icc (-A) 0, ∀ y ∈
              riemannianClosedBallOf
                (rescaledMetric S t (S.scalar t x) (hQ0.trans_le hQ) a) x r,
              ∀ m : ℕ,
                curvDerivNorm m (rescaledMetric S t (S.scalar t x) (hQ0.trans_le hQ) s) y ≤
                  C r m := by
  obtain ⟨B, hB, hmodel⟩ := KappaSolutions.exists_universal_normalized_ancient_curvature_bounds.{u}
  let K : ℝ → ℝ := fun r => Real.sqrt (B (2 * r + 1))
  let K0 : ℝ → ℝ := fun r => sourceCurvatureBound 3 (K r)
  let C : ℝ → ℕ → ℝ := fun r m =>
    shiLocalUniformBound 3 m (K0 r) (Real.sqrt (K0 r) / 2) * K0 r
  have hK0 (r : ℝ) : 0 < K0 r := sourceCurvatureBound_pos 3 (Real.sqrt_nonneg _)
  have hC (r : ℝ) (m : ℕ) : 0 ≤ C r m :=
    mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) (hK0 r).le
  refine ⟨fun r m => 1 + C r m, fun r m => by linarith [hC r m], ?_⟩
  intro M _ _ _ _ _ _ _ T hT S hS o r A hr hA
  let eps : ℝ := min (1 / 4) (min ((2 * r + 1)⁻¹ ^ 2) ((A + 2)⁻¹))
  have heps : 0 < eps := lt_min (by norm_num)
    (lt_min (sq_pos_of_pos (inv_pos.mpr (by positivity))) (inv_pos.mpr (by linarith)))
  have heps4 : eps ≤ 1 / 4 := min_le_left _ _
  have heps1 : eps < 1 := by linarith
  have hbuffer : 2 * r + 1 ≤ modelRadius eps := by
    have h := modelRadius_anti heps ((min_le_right _ _).trans (min_le_left _ _))
    have heq : modelRadius ((2 * r + 1)⁻¹ ^ 2) = 2 * r + 1 := by
      rw [modelRadius, Real.sqrt_sq (inv_nonneg.mpr (by positivity)), inv_inv]
    rwa [heq] at h
  have hdepth : A + 2 ≤ modelDepth eps := by
    have h := modelDepth_anti heps ((min_le_right _ _).trans (min_le_right _ _))
    simpa only [modelDepth, inv_inv] using h
  have hwindow : Icc (-A) 0 ⊆ Icc (-modelDepth eps) 0 :=
    fun s hs => ⟨by linarith [hs.1], hs.2⟩
  have hroot : (1 / 2 : ℝ) < Real.sqrt (1 - eps) := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    linarith
  have hradius : r < Real.sqrt (1 - eps) * (2 * r) := by nlinarith
  have hregular : interior (RealTimeInterval.closedOpen 0 T hT).carrier ⊆
      (RealTimeInterval.closedOpen 0 T hT).regular := by
    simp only [RealTimeInterval.closedOpen, interior_Ico]
    exact subset_rfl
  obtain ⟨kappa, _hkappa, hmodels⟩ := closed_flow_models hT S hS o
  obtain ⟨Q0, hQ0, hQmodel⟩ := hmodels eps heps heps1
  refine ⟨Q0, hQ0, ?_⟩
  intro x t ht hQ
  obtain ⟨W, _oN, _horient⟩ := hQmodel x t ht hQ
  constructor
  · intro s hs
    exact (W.normalized_window hregular).1 (hwindow hs)
  · intro a ha s hs y hy m
    obtain ⟨_, hcapture⟩ := W.source_closedBall_compact_subset (by positivity : 0 < 2 * r)
      (by linarith : 2 * r ≤ modelRadius eps) hradius (hwindow ha)
    obtain ⟨z, hz, rfl⟩ := hcapture hy
    have h := W.normalized_curvDerivNorm_bound_on_model_ball (K := K r) hS heps4 (Real.sqrt_nonneg _)
      (by positivity : 0 ≤ 2 * r) hbuffer hregular
      (a := s - 1) (b := s) (by linarith [hs.1]) (by linarith) hs.2
      (by
        intro v hv q hq
        dsimp only [K]
        rw [Real.sq_sqrt (hB (2 * r + 1)).le]
        exact hmodel kappa W.model W.model_ancient W.model_scalar_base (2 * r + 1)
          q hq v (hv.2.trans hs.2)) m (s := s) ⟨by linarith, le_rfl⟩ hz
    have hspan : s - (s - 1) = 1 := by ring
    have h' : curvDerivNorm m
        (rescaledMetric S t (S.scalar t x) W.scalar_pos s) (W.embedding z) ≤ C r m := by
      simpa only [hspan, mul_one, Real.sqrt_one, one_pow, div_one, C, K0] using h
    exact h'.trans (le_add_of_nonneg_left zero_le_one)

theorem exists_high_curvature_rescaled_curvature_bounds :
    ∃ C : ℝ → ℝ, (∀ r, 0 < C r) ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
        [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
        (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT)), IsSolutionOn S → TangentOrientationSection M →
        ∀ r A : ℝ, 0 < r → 0 ≤ A →
        ∃ Q0 : ℝ, ∃ hQ0 : 0 < Q0, ∀ x t, t ∈ Ico 0 T →
          ∀ hQ : Q0 ≤ S.scalar t x,
            (∀ s ∈ Icc (-A) 0, parabolicTime t (S.scalar t x) s ∈ Ico 0 T) ∧
            ∀ a ∈ Icc (-A) 0, ∀ s ∈ Icc (-A) 0, ∀ y ∈
              riemannianClosedBallOf
                (rescaledMetric S t (S.scalar t x) (hQ0.trans_le hQ) a) x r,
              normSq0S (rescaledMetric S t (S.scalar t x) (hQ0.trans_le hQ) s) y 4
                (metricRm04At (rescaledMetric S t (S.scalar t x) (hQ0.trans_le hQ) s) y) ≤
                C r := by
  obtain ⟨C, hC, hbounds⟩ := exists_high_curvature_rescaled_curvature_derivative_bounds.{u}
  refine ⟨fun r => C r 0 ^ 2, fun r => sq_pos_of_pos (hC r 0), ?_⟩
  intro M _ _ _ _ _ _ _ T hT S hS o r A hr hA
  obtain ⟨Q0, hQ0, hbound⟩ := hbounds M T hT S hS o r A hr hA
  refine ⟨Q0, hQ0, ?_⟩
  intro x t ht hQ
  refine ⟨(hbound x t ht hQ).1, ?_⟩
  intro a ha s hs y hy
  have h := (hbound x t ht hQ).2 a ha s hs y hy 0
  exact le_sq_of_sqrt_le (normSq0S_nonneg _ _ _ _) h

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

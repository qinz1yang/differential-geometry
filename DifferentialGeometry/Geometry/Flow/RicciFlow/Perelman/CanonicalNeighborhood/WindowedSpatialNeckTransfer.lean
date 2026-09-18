import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedStaticComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_windowed_spatial_neck_transfer_threshold {alpha C1 C2 : ℝ}
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) (hC1 : 0 ≤ C1) (hC2 : 1 ≤ C2) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
        (delta kappa eps : ℝ) (x : M) (t : ℝ)
        (W : WindowedModelWitness delta kappa S x t),
        delta ≤ delta₀ →
        ∀ K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0,
        ∀ y ∈ K.domain.carrier,
        ∀ nk : SpatialNeck (W.model.S.base.metric 0) (neckModelTolerance alpha) y,
          (∀ z ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹,
            nk.map z ∈ riemannianClosedBallOf (W.model.S.base.metric 0)
              W.model.basepoint (modelRadius delta)) →
          ∃ nk' : SpatialNeck (S.base.metric t) (2 * alpha) (W.embedding y),
            nk'.map = partialDiffeomorphTransMixed nk.map W.embedding := by
  let n := ⌈(2 * alpha)⁻¹⌉₊
  let B := 2 * C2 * C2 ^ (n + 2) + 243 * (1 + 3 * C2) * C2 * Real.sqrt 3
  let F := 486 * C2 * (1 + 3 * C2)
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have hB : 0 < B := by dsimp only [B]; positivity
  have hF : 0 < F := by dsimp only [F]; positivity
  have hR : 0 < 2 * C1 + 1 := by positivity
  let delta₀ := min ((2 * C1 + 1)⁻¹ ^ 2)
    (min (2 * alpha) (min (1 / 4) (min F⁻¹ (neckSourceTolerance alpha / B))))
  have hd0 : 0 < delta₀ := lt_min (sq_pos_of_pos (inv_pos.mpr hR))
    (lt_min (by positivity) (lt_min (by norm_num)
      (lt_min (inv_pos.mpr hF) (div_pos (neckSourceTolerance_pos ha) hB))))
  refine ⟨delta₀, hd0, ?_⟩
  intro M _ _ _ _ _ D S delta kappa eps x t W hd K y hy nk houter
  have hdR : delta ≤ (2 * C1 + 1)⁻¹ ^ 2 := hd.trans (min_le_left _ _)
  have hdrest := hd.trans (min_le_right _ _)
  have hdalpha : delta ≤ 2 * alpha := hdrest.trans (min_le_left _ _)
  have hdrest' := hdrest.trans (min_le_right _ _)
  have hdquarter : delta ≤ 1 / 4 := hdrest'.trans (min_le_left _ _)
  have hdrest'' := hdrest'.trans (min_le_right _ _)
  have hdF : delta ≤ F⁻¹ := hdrest''.trans (min_le_left _ _)
  have hdB : delta ≤ neckSourceTolerance alpha / B := hdrest''.trans (min_le_right _ _)
  have hbuffer : 2 * C1 ≤ modelRadius delta := by
    have hh := modelRadius_anti W.eps_pos hdR
    have heq : modelRadius ((2 * C1 + 1)⁻¹ ^ 2) = 2 * C1 + 1 := by
      rw [modelRadius, Real.sqrt_sq (inv_nonneg.mpr hR.le), inv_inv]
    rw [heq] at hh
    linarith
  have hord : n ≤ modelOrder delta := by
    have hh := Nat.ceil_le_ceil (inv_anti₀ W.eps_pos hdalpha)
    exact hh.trans (Nat.le_add_right _ 1)
  have hscalar : 486 * C2 * (1 + 3 * C2) * delta ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hdF hF.le
    rw [mul_inv_cancel₀ hF.ne'] at hh
    exact hh
  have hbudget : B * delta ≤ neckSourceTolerance alpha := by
    have hh := (le_div_iff₀ hB).mp hdB
    simpa only [mul_comm] using hh
  obtain ⟨hq, hQ, ⟨C⟩⟩ := W.exists_source_scalar_normalized_spatial_comparison
    K hdquarter hbuffer hscalar hy n hord
  exact nk.exists_transport_of_local_comparisons hQ W.embedding C ha hsmall
    (mul_nonneg hB.le W.eps_pos.le) hbudget le_rfl rfl houter
    ((riemannianClosedBallOf_mono (W.model.S.base.metric 0) W.model.basepoint
      (by linarith : modelRadius delta ≤ modelRadius delta + 1)).trans W.buffered_ball)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

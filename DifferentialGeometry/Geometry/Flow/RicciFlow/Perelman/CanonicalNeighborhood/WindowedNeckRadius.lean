import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckImageRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNeckTransport

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_windowed_neck_transfer_threshold {alpha : ℝ}
    (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ (delta kappa : ℝ) (x : M) (t : ℝ)
        (W : WindowedModelWitness delta kappa S x t),
        delta ≤ delta₀ →
        (∀ s ∈ Ioo (-modelDepth delta) 0,
          parabolicTime t (S.scalar t x) s ∈ D.regular) →
        ∀ nk : StrongNeck W.model.S (neckModelTolerance alpha) W.model.basepoint 0,
          ∃ nk' : StrongNeck S (2 * alpha) x t,
            nk'.map = partialDiffeomorphTransMixed nk.map W.embedding := by
  have hba : neckModelTolerance alpha < alpha :=
    (neckModelTolerance_le_smallness alpha).trans_lt
      (backgroundJetSmallness_ceil_lt_self _ ha hsmall)
  obtain ⟨R, hRpos, hR⟩ := exists_uniform_neck_image_radius (neckModelTolerance_pos ha) hba
  let delta₀ := min ((R + 1)⁻¹ ^ 2) (min (neckSourceTolerance alpha) (2 * alpha))
  have hRone : 0 < R + 1 := by linarith
  have hd0 : 0 < delta₀ := lt_min (sq_pos_of_pos (inv_pos.mpr hRone))
    (lt_min (neckSourceTolerance_pos ha) (by linarith))
  refine ⟨delta₀, hd0, ?_⟩
  intro M _ _ _ _ _ D S hS delta kappa x t W hd hreg nk
  have hdsq : delta ≤ (R + 1)⁻¹ ^ 2 := hd.trans (min_le_left _ _)
  have hdtol : delta ≤ neckSourceTolerance alpha :=
    hd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdalpha : delta ≤ 2 * alpha :=
    hd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrad : R ≤ modelRadius delta := by
    have hh := modelRadius_anti W.eps_pos hdsq
    have heq : modelRadius ((R + 1)⁻¹ ^ 2) = R + 1 := by
      rw [modelRadius, Real.sqrt_sq (inv_nonneg.mpr hRone.le), inv_inv]
    rw [heq] at hh
    linarith
  have horder : ⌈(2 * alpha)⁻¹⌉₊ ≤ modelOrder delta := by
    have hh := Nat.ceil_le_ceil (inv_anti₀ W.eps_pos hdalpha)
    exact hh.trans (Nat.le_add_right _ 1)
  have hmodel : rescaledMetric W.model.S 0 (W.model.S.scalar 0 W.model.basepoint) nk.Q_pos 0 =
      W.model.S.base.metric 0 := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    have hscalar : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
    simp only [rescaledMetric, scaleMetric_inner, hscalar, parabolicTime, div_one, zero_add,
      one_mul]
  have houter : ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹,
      nk.map y ∈ riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
        W.model.basepoint (modelRadius delta) := by
    intro y hy
    have hh := hR W.model.M ancientTimeInterval W.model.S W.model.basepoint 0 nk y hy
    rw [hmodel] at hh
    exact hh.trans (ENNReal.ofReal_le_ofReal hrad)
  exact W.exists_strongNeck_of_model hS hreg nk ha (by linarith) hdtol horder houter

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

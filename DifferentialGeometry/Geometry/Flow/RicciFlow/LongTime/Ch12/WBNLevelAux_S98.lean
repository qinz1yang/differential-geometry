import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BallCompact_S98
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.R3Sqrt_S98
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MetricWindow_S49
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PullbackFlowOnU_S67
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

set_option autoImplicit false

/-!
# CH12-S98 / G2b: N-level auxiliaries (two-sided C⁰ bound, Ricci naturality of `pullbackRestrict`)
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology.Manifold
open Set TopologicalSpace Manifold
open scoped Manifold ContDiff Topology ENNReal
universe u
namespace GC.LongTime.Ch12

/-- the open ball `B(2R)` as an `Opens`. -/
def ballU_S98 (H : FiniteVolumeHyperbolicModel.{u}) (R : ℝ) : Opens H.Carrier :=
  ⟨riemannianBallOf H.metric H.basepoint (2 * R), isOpen_ball_S98 H (2 * R)⟩

/-- two-sided form of `pullback_inner_le_of_ckErr_S49`. -/
theorem abs_pullback_sub_le_S98 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (p : H.Carrier) {δ : ℝ}
    (h0 : ckErr_S45 H g' c f 0 p < δ) (w : TangentSpace (𝓡 3) p) :
    |c * g'.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w) -
      H.metric.inner p w w| ≤ δ * H.metric.inner p w w := by
  change tensor0SFiberNorm H.metric p 2 (scaledMetricError_S49 H g' c f p) < δ at h0
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := 𝓡 3) H.metric p
  have hb := abs_apply_le_sqrt_normSq0S (I := 𝓡 3) H.metric p 2 basis hON
    (scaledMetricError_S49 H g' c f p) (vec2 w w)
  rw [scaledMetricError_apply_vec2_S49, Fin.prod_univ_two] at hb
  simp only [vec2, Fin.isValue, ↓reduceIte, one_ne_zero] at hb
  rw [Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right h0.le (metric_inner_self_nonneg _ _ _))

/-- Ricci curvature and inner product of the pull-back `(f|_U)^* m` at `x : U` are those of `m` at `f x`
on the pushed-forward vector (local isometry `f|_U : ↥U → N`). -/
theorem ricci_pullbackRestrict_S98 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    [T2Space N] [SigmaCompactSpace N]
    (m : SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N) (U : Opens H.Carrier)
    (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)) (x : U)
    (w : TangentSpace (𝓡 3) x) :
    ricciTensor (pullbackRestrict_S57 H m f U hF hinj) x w w =
        ricciTensor m (f x) (mfderiv (𝓡 3) (𝓡 3) f x w) (mfderiv (𝓡 3) (𝓡 3) f x w) ∧
      (pullbackRestrict_S57 H m f U hF hinj).inner x w w =
        m.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x w) (mfderiv (𝓡 3) (𝓡 3) f x w) := by
  have hloc : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun z : U => f z) :=
    isLocalDiffeomorph_of_injective_mfderiv (fun z : U => f z) (contMDiff_restrict_C4 f U hF)
      (immersion_restrict_inj_S57 H f U hF hinj) rfl
  have hmet : pullbackRestrict_S57 H m f U hF hinj =
      localPullMetric (I := 𝓡 3) (J := 𝓡 3) m (fun z : U => f z) hloc := by
    apply SmoothRiemannianMetric.ext_inner
    intro y a b
    rw [localPullMetric_inner, pullbackRestrict_S57, SmoothRiemannianMetric.pullbackOfImmersion_inner]
  have hd := mfderiv_comp_val_C4 f U hF x w
  refine ⟨?_, ?_⟩
  · rw [hmet, ricciTensor_localPull (I := 𝓡 3) (J := 𝓡 3) m _ hloc x w w, hd]
  · rw [hmet, localPullMetric_inner, hd]

end GC.LongTime.Ch12

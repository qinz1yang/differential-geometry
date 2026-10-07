import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterDefect_O7
import DifferentialGeometry.Geometry.Curvature.LocalPullbackRicci
import DifferentialGeometry.Geometry.Metric.Pullback.LocalRestriction

set_option autoImplicit false

/-!
# CH12-CX8: transport of the centre Ricci defect

The norm used by O5 is invariant under local isometries, including restriction to an open set.
The tangent map must be surjective: an estimate in a proper tangent subspace would not suffice.
Together with O7's quantitative perturbation estimate this gives the terminal step of the
parabolic centre argument, with the reference metric fixed to the Einstein limit metric.
-/

noncomputable section
open Set Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

private local instance {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

section Transport

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold ThreeModel ∞ N] [T2Space N]

/-- The full unit-ball defect set is preserved by a local pullback. -/
theorem defectSet_localPullMetric_CX8 (g : SmoothRiemannianMetric ThreeModel N)
    (f : M → N) (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f) (x : M) :
    defectSet_O5 (localPullMetric g f hf) x = defectSet_O5 g (f x) := by
  unfold defectSet_O5
  ext r
  constructor
  · rintro ⟨v, w, hv, hw, hr⟩
    refine ⟨mfderiv ThreeModel ThreeModel f x v, mfderiv ThreeModel ThreeModel f x w,
      ?_, ?_, ?_⟩
    · simpa only [localPullMetric_inner] using hv
    · simpa only [localPullMetric_inner] using hw
    · rw [ricciTensor_localPullMetric, localPullMetric_inner] at hr
      exact hr
  · rintro ⟨v, w, hv, hw, hr⟩
    let e := hf.mfderivToContinuousLinearEquiv (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
    obtain ⟨v', hv'⟩ := e.surjective v
    obtain ⟨w', hw'⟩ := e.surjective w
    have hvd : mfderiv ThreeModel ThreeModel f x v' = v := hv'
    have hwd : mfderiv ThreeModel ThreeModel f x w' = w := hw'
    refine ⟨v', w', ?_, ?_, ?_⟩
    · rw [localPullMetric_inner, hvd]
      exact hv
    · rw [localPullMetric_inner, hwd]
      exact hw
    · rw [ricciTensor_localPullMetric, localPullMetric_inner, hvd, hwd]
      exact hr

/-- Restricting a metric to an open neighbourhood leaves its centre defect unchanged. -/
theorem defectSet_restrictOpen_CX8 (g : SmoothRiemannianMetric ThreeModel M)
    (U : Opens M) (x : U) :
    defectSet_O5 (g.restrictOpen U) x = defectSet_O5 g (x : M) := by
  rw [← localPullMetric_subtype_val]
  exact defectSet_localPullMetric_CX8 g _ (isLocalDiffeomorph_subtype_val U) x

end Transport

section Limit

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- Canonical pointwise `C²` convergence to `Ric = -g/2` forces the centre defect to vanish. -/
theorem eventually_defect_lt_of_einstein_limit_CX8
    (g : SmoothRiemannianMetric ThreeModel M)
    (L : ℕ → SmoothRiemannianMetric ThreeModel M) (q : M)
    (hE : ∀ v w : TangentSpace ThreeModel q,
      ricciTensor g q v w = -(1 / 2) * g.inner q v w)
    (hconv : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k (L n) g g q < η) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, sSup (defectSet_O5 (L n) q) < ε := by
  intro ε hε
  let η := min (1 / 2) (ε / 5764)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  filter_upwards [hconv η hη] with n hn
  have hle := defect_le_of_close_einstein_O7 (L n) g q hE hη.le
    (min_le_left _ _) (fun k hk => (hn k hk).le)
  have hηε : η ≤ ε / 5764 := min_le_right _ _
  exact hle.trans_lt (by nlinarith)

end Limit

end GC.LongTime.Ch12

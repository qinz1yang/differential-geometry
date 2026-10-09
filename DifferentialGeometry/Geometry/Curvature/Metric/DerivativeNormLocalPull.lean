import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormRestriction
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.SigmaCompactOpen

/-!
# Curvature derivative norms under a (not necessarily injective) local isometry (lane BDRY-INST)

`curvatureDerivativeNorm_of_injective_local_isometry` needs a global injectivity. A local
diffeomorphism is injective on the source of each of its local charts; restricting the pulled
back metric to that open source gives the same norm at every point:

`curvatureDerivativeNorm (localPullMetric g f hf) k x = curvatureDerivativeNorm g k (f x)`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : CompleteSpace F := FiniteDimensional.complete ℝ F

/-- The curvature derivative norms of a locally pulled back metric are those of the target at
the image point (any local diffeomorphism; no injectivity). -/
theorem curvatureDerivativeNorm_localPullMetric_INST
    (g : SmoothRiemannianMetric J N) (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (k : ℕ) (x : M) :
    curvatureDerivativeNorm (localPullMetric g f hf) k x = curvatureDerivativeNorm g k (f x) := by
  obtain ⟨Φ, hxΦ, hfΦ⟩ := hf x
  let U : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  have hfU : IsLocalDiffeomorph I J ∞ (f ∘ (Subtype.val : U → M)) :=
    isLocalDiffeomorph_comp hf (isLocalDiffeomorph_subtype_val U)
  have hinj : Function.Injective (f ∘ (Subtype.val : U → M)) := by
    intro y z hyz
    apply Subtype.ext
    have hy : f y.val = Φ y.val := hfΦ y.property
    have hz : f z.val = Φ z.val := hfΦ z.property
    exact Φ.toPartialEquiv.injOn y.property z.property
      (hy.symm.trans (hyz.trans hz))
  have hmetric (y : U) (v w : TangentSpace I y) :
      ((localPullMetric g f hf).restrictOpen U).inner y v w =
        g.inner ((f ∘ (Subtype.val : U → M)) y)
          (mfderiv I J (f ∘ (Subtype.val : U → M)) y v)
          (mfderiv I J (f ∘ (Subtype.val : U → M)) y w) := by
    rw [SmoothRiemannianMetric.restrictOpen_inner]
    have hd : mfderiv I J (f ∘ (Subtype.val : U → M)) y = mfderiv I J f y.val :=
      mfderiv_restrict_open f U y
    rw [hd]
    exact localPullMetric_inner g f hf y.val v w
  have hnorm := curvatureDerivativeNorm_of_injective_local_isometry
    ((localPullMetric g f hf).restrictOpen U) g (f ∘ (Subtype.val : U → M)) hfU hinj hmetric k
    ⟨x, hxΦ⟩
  exact (curvatureDerivativeNorm_restrictOpen (localPullMetric g f hf) U k ⟨x, hxΦ⟩).symm.trans
    hnorm

end DifferentialGeometry.Geometry.Curvature

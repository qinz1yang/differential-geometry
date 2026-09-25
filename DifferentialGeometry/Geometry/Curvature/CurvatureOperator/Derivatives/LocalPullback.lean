import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Restriction
import DifferentialGeometry.Geometry.Metric.UniversalCover.ProductCurvatureJets
import DifferentialGeometry.Geometry.Metric.Pullback.Local

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem curvDerivNorm_eq_of_local_pullback
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (Phi : PartialDiffeomorph I I M N ∞) (U : TopologicalSpace.Opens M)
    (hU : (U : Set M) ⊆ Phi.source)
    (hmet : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (Phi x) (mfderiv I I (Phi : M → N) x v)
        (mfderiv I I (Phi : M → N) x w)) (q : ℕ) (x : U) :
    curvDerivNorm q g (x : M) = curvDerivNorm q h (Phi (x : M)) := by
  let V : TopologicalSpace.Opens N :=
    ⟨(Phi : M → N) '' (U : Set M), image_opens_isOpen Phi hU⟩
  let e : U ≃ₘ⟮I, I⟯ V := PartialDiffeomorph.toOpensDiffeo Phi hU
  have heq : g.restrictOpen U = Diffeomorph.pullbackMetricCross (h.restrictOpen V) e := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    have hv := PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU y v
    have hw := PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU y w
    exact (hmet y y.property v w).trans
      (congrArg₂ (fun v' w' => h.inner (Phi (y : M)) v' w') hv hw).symm
  rw [← curvDerivNorm_restrictOpen g U q x, heq,
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvDerivNorm_pullbackMetricCross,
    curvDerivNorm_restrictOpen]
  rfl

end DifferentialGeometry.CheegerGromovCompactness

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

theorem curvDerivNorm_localPullMetric
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (m : ℕ) (x : M) :
    curvDerivNorm (I := I) m (localPullMetric g f hf) x =
      curvDerivNorm (I := J) m g (f x) := by
  obtain ⟨Φ, hxΦ, hEq⟩ := hf x
  let U : Opens M := ⟨Φ.source, Φ.open_source⟩
  let V : Opens N := ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ (Subset.rfl)⟩
  let e : U ≃ₘ⟮I, J⟯ V := PartialDiffeomorph.toOpensDiffeo Φ Subset.rfl
  let xu : U := ⟨x, hxΦ⟩
  have hmetric : (localPullMetric g f hf).restrictOpen U =
      Diffeomorph.pullbackMetricCross (g.restrictOpen V) e := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    change (localPullMetric g f hf).inner (y : M)
      (show TangentSpace I (y : M) from v) (show TangentSpace I (y : M) from w) = _
    rw [localPullMetric_inner]
    have hgerm : f =ᶠ[𝓝 (y : M)] (Φ : M → N) :=
      Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds y.property) hEq
    have hde := hgerm.mfderiv_eq (I := I) (I' := J)
    rw [hgerm.eq_of_nhds, hde]
    exact congrArg₂ (fun v' w' => g.inner (Φ (y : M)) v' w')
      (PartialDiffeomorph.mfderiv_toOpensDiffeo Φ Subset.rfl y v).symm
      (PartialDiffeomorph.mfderiv_toOpensDiffeo Φ Subset.rfl y w).symm
  rw [← curvDerivNorm_restrictOpen (localPullMetric g f hf) U m xu, hmetric,
    PDE.RicciFlow.Perelman.KappaSolutions.curvDerivNorm_pullbackMetricCross,
    curvDerivNorm_restrictOpen]
  exact congrArg (fun z => curvDerivNorm (I := J) m g z) (hEq hxΦ).symm

end DifferentialGeometry.CheegerGromovCompactness

end


noncomputable section
open Set Manifold TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem curvDerivNorm_restrictOpenOfSubset {U V : Opens M} (hUV : U ≤ V)
    (g : SmoothRiemannianMetric I V) (q : ℕ) (x : U) :
    curvDerivNorm q (g.restrictOpenOfSubset hUV) x =
      curvDerivNorm q g (Opens.inclusion hUV x) := by
  have hinc : IsLocalDiffeomorph I I ∞ (Opens.inclusion hUV) := fun y =>
    isLocalDiffeomorphAt_subtypeCodRestrict (fun z : U => hUV z.property)
      (isLocalDiffeomorph_subtype_val U y)
  have heq : g.restrictOpenOfSubset hUV = localPullMetric g (Opens.inclusion hUV) hinc := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [localPullMetric_inner, mfderiv_opens_incl]
    rfl
  rw [heq, curvDerivNorm_localPullMetric]
end DifferentialGeometry.CheegerGromovCompactness

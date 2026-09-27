import DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction

set_option autoImplicit false
noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem metricRm04StandardAt_eq_of_metric_eventuallyEq
    (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
      g₁.inner y v w = g₂.inner y v w)
    (X Y Z W : TangentSpace I x) :
    metricRm04StandardAt g₁ x X Y Z W = metricRm04StandardAt g₂ x X Y Z W := by
  obtain ⟨s, hsg, hs, hxs⟩ := mem_nhds_iff.mp hmetric
  let U : Opens M :=
    ⟨s ∩ (chartAt H x).source, hs.inter (chartAt H x).open_source⟩
  let xu : U := ⟨x, hxs, mem_chart_source H x⟩
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : SecondCountableTopology H := I.secondCountableTopology
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let e : U ≃ₜ ((chartAt H x) '' (U : Set M)) :=
    (chartAt H x).homeomorphOfImageSubsetSource (fun _ hy => hy.2) rfl
  let _ : SecondCountableTopology U := e.secondCountableTopology
  let _ : SigmaCompactSpace U := inferInstance
  let toU (v : TangentSpace I x) : TangentSpace I xu :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) xu).symm
      (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
  have htoU (v : TangentSpace I x) :
      mfderiv I I (Subtype.val : U → M) xu (toU v) = v := by
    rw [mfderiv_subtype_val_apply]
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) x).injective
    change (tangentSpaceModelContinuousLinearEquiv (I := I) x)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) xu).symm
          (tangentSpaceModelContinuousLinearEquiv (I := I) x v)) =
      tangentSpaceModelContinuousLinearEquiv (I := I) x v
    rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
    exact tangentSpaceModelContinuousLinearEquiv_apply (I := I) x v
  have hrestrict : g₁.restrictOpen U = g₂.restrictOpen U := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    exact hsg y.property.1 v w
  have h₁ := metricRm04StandardAt_restrictOpen g₁ U xu (toU X) (toU Y) (toU Z) (toU W)
  have h₂ := metricRm04StandardAt_restrictOpen g₂ U xu (toU X) (toU Y) (toU Z) (toU W)
  rw [htoU, htoU, htoU, htoU] at h₁ h₂
  exact h₁.symm.trans ((congrArg
    (fun g => metricRm04StandardAt g xu (toU X) (toU Y) (toU Z) (toU W))
      hrestrict).trans h₂)

theorem metricRm04At_eq_of_metric_eventuallyEq
    (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
      g₁.inner y v w = g₂.inner y v w) :
    metricRm04At g₁ x = metricRm04At g₂ x := by
  ext v
  have hv : vec4 (v 0) (v 1) (v 2) (v 3) = v := by
    ext i
    fin_cases i <;> rfl
  simpa only [metricRm04StandardAt_apply, hv] using
    metricRm04StandardAt_eq_of_metric_eventuallyEq g₁ g₂ x hmetric
      (v 0) (v 1) (v 2) (v 3)

end DifferentialGeometry.Geometry.Curvature

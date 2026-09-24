import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem metricDerivNorm_eq_of_metric_eventuallyEq
    (a : ℕ) (A B gInf gRef : SmoothRiemannianMetric I M) (x : M)
    (hAB : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
      A.inner y v w = B.inner y v w) :
    metricDerivNorm (I := I) a A gInf gRef x =
      metricDerivNorm (I := I) a B gInf gRef x := by
  obtain ⟨s, hsg, hs, hxs⟩ := mem_nhds_iff.mp hAB
  let U : TopologicalSpace.Opens M :=
    ⟨s ∩ (chartAt H x).source, hs.inter (chartAt H x).open_source⟩
  let xu : U := ⟨x, hxs, mem_chart_source H x⟩
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : SecondCountableTopology H := I.secondCountableTopology
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let e : U ≃ₜ ((chartAt H x) '' (U : Set M)) :=
    (chartAt H x).homeomorphOfImageSubsetSource (fun _ hy => hy.2) rfl
  let _ : SecondCountableTopology U := e.secondCountableTopology
  let _ : SigmaCompactSpace U := inferInstance
  have hA : A.restrictOpen U = B.restrictOpen U := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    exact hsg y.property.1 v w
  have hleft := metricDerivNorm_restrictOpen (I := I) A gInf gRef U a xu
  have hright := metricDerivNorm_restrictOpen (I := I) B gInf gRef U a xu
  rw [hA] at hleft
  exact hleft.symm.trans hright

end DifferentialGeometry.CheegerGromovCompactness

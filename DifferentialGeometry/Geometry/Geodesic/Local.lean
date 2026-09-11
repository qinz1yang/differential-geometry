import DifferentialGeometry.Geometry.Curve.Reparametrization
import DifferentialGeometry.Geometry.Geodesic.Chart.Regularity
import DifferentialGeometry.Geometry.Geodesic.Flow.CrossVectorFieldReduction
import Mathlib.Geometry.Manifold.IntegralCurve.Transform

noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [I.Boundaryless] in
theorem eventually_isGeodesicAt {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t) :
    ∀ᶠ s in 𝓝 t, IsGeodesicAt (I := I) g γ s := by
  obtain ⟨p, f, hproj, hsrc, hf⟩ := hγ
  have hflow : ∀ᶠ s in 𝓝 t, IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g p) s :=
    eventually_eventually_nhds.mpr hf
  have hbase : ContinuousAt (fun s ↦ (f s).proj) t :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp hf.continuousAt
  filter_upwards [hflow, hbase.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hsrc)]
    with s hs hsp
  exact ⟨p, f, hproj, hsp, hs⟩

theorem contMDiffAt_of_isGeodesicAt {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t) : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t := by
  obtain ⟨U, hUsub, hUopen, htU⟩ := mem_nhds_iff.mp (eventually_isGeodesicAt hγ)
  exact isGeodesicOn_contMDiffAt_infty g hUopen htU
    (fun s hs ↦ (hUsub hs).hasGeodesicEquationAt)
    (fun s hs ↦ (hUsub hs).continuousAt.continuousWithinAt)

omit [I.Boundaryless] in
theorem isGeodesicAt_comp_add {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t) (d : ℝ) :
    IsGeodesicAt (I := I) g (fun s ↦ γ (s + d)) (t - d) := by
  obtain ⟨p, f, hproj, hsrc, hf⟩ := hγ
  refine ⟨p, fun s ↦ f (s + d), fun s ↦ hproj _, ?_, hf.comp_add d⟩
  simpa only [sub_add_cancel] using hsrc

omit [I.Boundaryless] in
theorem isGeodesicAt_congr {g : SmoothRiemannianMetric I M} {γ β : ℝ → M} {t : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t) (heq : β =ᶠ[𝓝 t] γ) :
    IsGeodesicAt (I := I) g β t := by
  obtain ⟨p, f, hproj, hsrc, hf⟩ := hγ
  let F : ℝ → TangentBundle I M := fun s ↦ ⟨β s, (f s).snd⟩
  have hF : F =ᶠ[𝓝 t] f := by
    filter_upwards [heq] with s hs
    change (⟨β s, (f s).snd⟩ : TangentBundle I M) = f s
    rw [hs, ← hproj s]
  refine ⟨p, F, fun _ ↦ rfl, ?_, ?_⟩
  · simpa only [hF.self_of_nhds] using hsrc
  · filter_upwards [hf, hF.eventually_nhds] with s hs he
    have hd := hs.congr_of_eventuallyEq he
    erw [he.self_of_nhds]
    exact hd

end DifferentialGeometry.Geometry

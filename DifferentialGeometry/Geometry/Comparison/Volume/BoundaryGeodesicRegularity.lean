import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInwardGeodesic
import DifferentialGeometry.External.TauCeti.Geometry.Manifold.IntegralCurve.Basic

/-!
Local ambient geodesics are smooth without requiring a globally defined geodesic flow.
The coordinate ODE gains each finite derivative on a suitable open time neighborhood.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

private theorem local_ode_smooth {E : Type*} [ambientNorm : NormedAddCommGroup E]
    [ambientSpace : NormedSpace ℝ E] {f : ℝ → E} {v : E → E} {t : ℝ}
    (hf : ∀ᶠ s in 𝓝 t, HasDerivAt f (v (f s)) s)
    (hv : ContDiffAt ℝ ∞ v (f t)) : ContDiffAt ℝ ∞ f t := by
  rw [contDiffAt_infty]
  intro n
  have hvn : ContDiffAt ℝ (n : ℕ) v (f t) := hv.of_le (by exact_mod_cast le_top)
  obtain ⟨u, hu, hvu⟩ := hvn.contDiffOn le_rfl (by simp)
  have hfu : ∀ᶠ s in 𝓝 t, f s ∈ u :=
    (hf.self_of_nhds.continuousAt).eventually hu
  obtain ⟨s, hs, hsopen, hst⟩ := mem_nhds_iff.mp (hf.and hfu)
  have hfs : ContDiffOn ℝ (n + 1 : ℕ) f s :=
    TauCeti.contDiffOn_succ_of_hasDerivAt_comp hsopen hvu
      (fun x hx => (hs hx).2) (fun x hx => (hs hx).1)
  exact (hfs.contDiffAt (hsopen.mem_nhds hst)).of_le
    (by exact_mod_cast Nat.le_succ n)

private theorem local_integral_smooth
    {E : Type*} [ambientNorm : NormedAddCommGroup E]
    [ambientSpace : NormedSpace ℝ E] {H : Type*}
    [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [manifoldTopology : TopologicalSpace M]
    [manifoldCharts : ChartedSpace H M] [manifoldSmooth : IsManifold I ∞ M]
    [manifoldBoundaryless : BoundarylessManifold I M]
    {f : ℝ → M} {v : (x : M) → TangentSpace I x} {t : ℝ}
    (hf : IsMIntegralCurveAt f v t)
    (hv : ContMDiffAt I I.tangent ∞
      (fun x => (⟨x, v x⟩ : TangentBundle I M)) (f t)) :
    ContMDiffAt 𝓘(ℝ) I ∞ f t := by
  rw [contMDiffAt_iff_target]
  refine ⟨hf.continuousAt, ?_⟩
  let c : ℝ → E := extChartAt I (f t) ∘ f
  let w : E → E := fun x =>
    tangentCoordChange I ((extChartAt I (f t)).symm x) (f t)
      ((extChartAt I (f t)).symm x) (v ((extChartAt I (f t)).symm x))
  have hw : ContDiffAt ℝ ∞ w (c t) := by
    rw [contMDiffAt_iff] at hv
    exact (hv.2.contDiffAt
      (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)).snd
  have hsrc : ∀ᶠ s in 𝓝 t, f s ∈ (extChartAt I (f t)).source :=
    hf.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) (f t))
  have hd : ∀ᶠ s in 𝓝 t, HasDerivAt c (w (c s)) s := by
    filter_upwards [hf.eventually_hasDerivAt, hsrc] with s hs hssrc
    apply hs.congr_deriv
    simp only [w, c, Function.comp_apply]
    rw [PartialEquiv.left_inv _ hssrc]
  exact (local_ode_smooth hd hw).contMDiffAt

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]

theorem ambient_geodesic_smooth (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (γ : ℝ → E) (t : ℝ) (hγ : IsGeodesicAt g γ t) :
    ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ γ t := by
  obtain ⟨α, f, hproj, hsrc, hf⟩ := hγ
  have hv := geodesicVectorFieldChart_contMDiffAt g α hsrc
  have hfs := local_integral_smooth hf hv
  have hbase := (contMDiff_proj (TangentSpace 𝓘(ℝ, E))).contMDiffAt.comp t hfs
  simpa only [Function.comp_def, hproj] using hbase

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

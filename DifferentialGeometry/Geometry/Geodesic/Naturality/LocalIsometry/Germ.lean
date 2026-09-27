import DifferentialGeometry.Geometry.Geodesic.Naturality.LocalIsometry.Geodesic
import DifferentialGeometry.Geometry.Geodesic.EquationGerm
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open Filter Set TopologicalSpace
open scoped Manifold ContDiff Topology

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

private theorem isGeodesicAt_map_of_local_isometry
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    {gamma : ℝ → M} {t : ℝ} (hgamma : IsGeodesicAt g gamma t) :
    IsGeodesicAt h (fun s ↦ f (gamma s)) t := by
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨U, hUsub, hUopen, htU⟩ := mem_nhds_iff.mp
    (DifferentialGeometry.Geometry.eventually_isGeodesicAt hgamma)
  have hcont : ContinuousOn gamma U :=
    fun s hs ↦ (hUsub hs).continuousAt.continuousWithinAt
  have hgeo : IsGeodesicOn g gamma U :=
    fun s hs ↦ (hUsub hs).hasGeodesicEquationAt
  apply DifferentialGeometry.Geometry.isGeodesicAt_of_isGeodesicOn h
    (hUopen.mem_nhds htU) (geoOn_map_localIso g h hf hmetric hUopen hcont hgeo)
  exact hf.contMDiff.continuous.comp_continuousOn hcont

theorem isGeodesicAt_map_of_local_isometry_on
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : IsLocalDiffeomorphOn I J ∞ f U)
    (hmetric : ∀ (x : M), x ∈ U → ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    {gamma : ℝ → M} {t : ℝ} (ht : gamma t ∈ U)
    (hgamma : IsGeodesicAt g gamma t) :
    IsGeodesicAt h (fun s ↦ f (gamma s)) t := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let O : Opens M := ⟨U, hU⟩
  let gammaO : ℝ → O := fun s ↦
    if hs : gamma s ∈ U then ⟨gamma s, hs⟩ else ⟨gamma t, ht⟩
  have hmem : ∀ᶠ s in 𝓝 t, gamma s ∈ U :=
    hgamma.continuousAt.preimage_mem_nhds (hU.mem_nhds ht)
  have heq : (fun s ↦ (gammaO s : M)) =ᶠ[𝓝 t] gamma := by
    filter_upwards [hmem] with s hs
    simp only [gammaO, dif_pos hs]
  have hgammaOamb := DifferentialGeometry.Geometry.isGeodesicAt_congr hgamma heq
  obtain ⟨V, hVsub, hVopen, htV⟩ := mem_nhds_iff.mp
    (DifferentialGeometry.Geometry.eventually_isGeodesicAt hgammaOamb)
  have hgeoO : IsGeodesicOn (g.restrictOpen O) gammaO V :=
    (geodesicOn_open_iff g O gammaO V).mpr
      (fun s hs ↦ (hVsub hs).hasGeodesicEquationAt)
  have hcontO : ContinuousOn gammaO V := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply continuous_induced_rng.mpr
    exact continuousOn_iff_continuous_domRestrict.mp
      (fun s hs ↦ (hVsub hs).continuousAt.continuousWithinAt)
  have hgammaO : IsGeodesicAt (g.restrictOpen O) gammaO t :=
    DifferentialGeometry.Geometry.isGeodesicAt_of_isGeodesicOn
      (g.restrictOpen O) (hVopen.mem_nhds htV) hgeoO hcontO
  have hfO : IsLocalDiffeomorph I J ∞ (fun x : O ↦ f (x : M)) :=
    DifferentialGeometry.isLocalDiffeomorph_restrict_open O hf
  have hmetricO (x : O) (v w : TangentSpace I x) :
      (g.restrictOpen O).inner x v w =
        h.inner (f x)
          (mfderiv I J (fun y : O ↦ f (y : M)) x v)
          (mfderiv I J (fun y : O ↦ f (y : M)) x w) := by
    have hderiv (z : TangentSpace I x) :
        mfderiv I J (fun y : O ↦ f (y : M)) x z = mfderiv I J f (x : M) z := by
      have hc := mfderiv_comp_apply x ((hf x).mdifferentiableAt (by simp))
        ((contMDiff_subtype_val (I := I) (U := O) (n := ∞)).mdifferentiable (by simp) x) z
      have hincl : mfderiv I I (fun y : O ↦ (y : M)) x z = z :=
        mfderiv_subtype_val_apply (I := I) O x z
      exact hc.trans (congrArg (mfderiv I J f (x : M)) hincl)
    rw [hderiv v, hderiv w]
    exact hmetric x x.2 v w
  have hmap := isGeodesicAt_map_of_local_isometry (g.restrictOpen O) h hfO hmetricO hgammaO
  apply DifferentialGeometry.Geometry.isGeodesicAt_congr hmap
  filter_upwards [heq] with s hs
  exact congrArg f hs.symm

end DifferentialGeometry.Geometry.Riemannian.Geodesic

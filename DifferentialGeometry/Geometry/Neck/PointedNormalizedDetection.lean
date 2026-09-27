import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.DomainMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem eventually_normalizedNeck_of_pointed_cylinder_limit
    {X : PointedRiemannianSeq.{u, 0, 0} (I := ThreeModel)}
    {L : PointedRiemannianManifold.{u, 0, 0} (I := ThreeModel)} {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (I := ThreeModel) X L subseq)
    (C : MetricConvergenceData (I := ThreeModel) Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (g : ∀ i, SmoothRiemannianMetric ThreeModel (X.obj i).M)
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i)
    (hmetric : ∀ i, (X.obj i).metric = scaleMetric (Q i) (hQ i) (g i))
    (hscalar : ∀ i, Q i = metricScalarAt (g i) (X.obj i).basepoint)
    (mark : Sphere 2) (e : NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ L.M)
    (hmark : e (mark, 0) = L.basepoint)
    (hcylinder : Diffeomorph.pullbackMetricCross L.metric e = roundCylinderMetric)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (k : ℕ) :
    ∀ᶠ i in atTop, ∃ N : NormalizedNeck (g (subseq i)) δ k,
      N.center = (X.obj (subseq i)).basepoint ∧ N.scale = Q (subseq i) ∧
      N.sphereMark = mark ∧
      ∀ z : neckBuffer δ, N.chart z = Phi.map i (e z.val) := by
  let Kbuffer : Set NeckCylinder := univ ×ˢ Icc (-δ⁻¹ - 1) (δ⁻¹ + 1)
  have hbuffer : IsCompact Kbuffer := isCompact_univ.prod isCompact_Icc
  have hUbuffer : (neckBuffer δ : Set NeckCylinder) ⊆ Kbuffer := by
    intro z hz
    exact ⟨mem_univ _, hz.1.le, hz.2.le⟩
  obtain ⟨i0, hi0⟩ := Perelman.KappaSolutions.pointedMaps_eventually_fixedDomain_metric_close
    Phi C hcanonical e (neckBuffer δ) Kbuffer hbuffer hUbuffer
    (neckClosedTest δ) (isCompact_neckClosedTest δ) k δ hδ
  filter_upwards [eventually_ge_atTop i0] with i hi
  obtain ⟨f, hf, hfmap, hclose⟩ := hi0 i hi
  have hmarked : f ⟨(mark, 0), by
      have := inv_pos.mpr hδ
      constructor <;> linarith⟩ = (X.obj (subseq i)).basepoint := by
    rw [hfmap]
    change Phi.map i (e (mark, 0)) = _
    rw [hmark]
    exact Phi.basepoint_map i
  let N : NormalizedNeck (g (subseq i)) δ k := {
    delta_pos := hδ
    delta_lt_one := hδ1
    sphereMark := mark
    center := (X.obj (subseq i)).basepoint
    chart := f
    chart_smooth := hf
    marked := hmarked
    scale := Q (subseq i)
    scale_pos := hQ (subseq i)
    scale_scalar := hscalar (subseq i)
    normalizedMetric := Perelman.KappaSolutions.immersionInducedMetric (X.obj (subseq i)).metric hf.isImmersion
    normalized_inner := by
      intro x v w
      rw [Perelman.KappaSolutions.immersionInducedMetric_inner, hmetric, scaleMetric_inner]
    closeness := by simpa only [hcylinder] using hclose }
  exact ⟨N, rfl, rfl, rfl, hfmap⟩


theorem exists_normalizedNeck_sequence_of_pointed_cylinder_limit
    {X : PointedRiemannianSeq.{u, 0, 0} (I := ThreeModel)}
    {L : PointedRiemannianManifold.{u, 0, 0} (I := ThreeModel)} {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (I := ThreeModel) X L subseq)
    (C : MetricConvergenceData (I := ThreeModel) Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (g : ∀ i, SmoothRiemannianMetric ThreeModel (X.obj i).M)
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i)
    (hmetric : ∀ i, (X.obj i).metric = scaleMetric (Q i) (hQ i) (g i))
    (hscalar : ∀ i, Q i = metricScalarAt (g i) (X.obj i).basepoint)
    (mark : Sphere 2) (e : NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ L.M)
    (hmark : e (mark, 0) = L.basepoint)
    (hcylinder : Diffeomorph.pullbackMetricCross L.metric e = roundCylinderMetric)
    (eps : ℕ → ℝ) (heps : ∀ i, 0 < eps i) (heps1 : ∀ i, eps i < 1)
    (order : ℕ → ℕ) :
    ∃ tau : ℕ → ℕ, StrictMono tau ∧
      ∃ N : ∀ i, NormalizedNeck (g (subseq (tau i))) (eps i) (order i),
        (∀ i, (N i).center = (X.obj (subseq (tau i))).basepoint) ∧
        (∀ i, (N i).scale = Q (subseq (tau i))) ∧
        (∀ i, (N i).sphereMark = mark) ∧
        ∀ i z, (N i).chart z = Phi.map (tau i) (e z.val) := by
  have hevent (i : ℕ) := eventually_normalizedNeck_of_pointed_cylinder_limit
    Phi C hcanonical g Q hQ hmetric hscalar mark e hmark hcylinder (heps i) (heps1 i) (order i)
  obtain ⟨tau, htau, hnecks⟩ := extraction_forall_of_eventually hevent
  choose N hcenter hscale hmarks hcharts using hnecks
  exact ⟨tau,htau,N,hcenter,hscale,hmarks,hcharts⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

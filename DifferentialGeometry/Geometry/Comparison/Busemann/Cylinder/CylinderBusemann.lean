import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.Busemann
import DifferentialGeometry.Geometry.Comparison.Busemann.Cylinder.CylinderMinimizingLine

set_option autoImplicit false
noncomputable section
open Bundle Set Filter Manifold Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
namespace DifferentialGeometry.Geometry.Metric

private abbrev Sphere3 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev Cyl3 := Sphere3 × ℝ
private abbrev ICyl3 := (𝓡 2).prod 𝓘(ℝ)

private local instance : NeZero
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) := ⟨by simp⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_busemann_functions_on_cylinder
    (g : SmoothRiemannianMetric ICyl3 Cyl3)
    (hcomplete : RiemannianMetricComplete g) :
    ∃ gamma : ℝ → Cyl3,
      ContMDiff 𝓘(ℝ, ℝ) ICyl3 ∞ gamma ∧ IsGeodesic g gamma ∧
      (gamma 0).2 = 0 ∧
      (∀ s t : ℝ,
        riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|) ∧
      let bplus : Cyl3 → ℝ := fun x ↦
        ⨅ t : ℝ, (riemannianEDistOf g x (gamma t)).toReal - t
      let bminus : Cyl3 → ℝ := fun x ↦
        ⨅ t : ℝ, (riemannianEDistOf g x (gamma (-t))).toReal - t
      Continuous bplus ∧ Continuous bminus ∧
      (∀ x y, |bplus x - bplus y| ≤ (riemannianEDistOf g x y).toReal) ∧
      (∀ x y, |bminus x - bminus y| ≤ (riemannianEDistOf g x y).toReal) ∧
      (∀ x, Tendsto (fun t : ℝ ↦ (riemannianEDistOf g x (gamma t)).toReal - t)
        atTop (𝓝 (bplus x))) ∧
      (∀ x, Tendsto (fun t : ℝ ↦ (riemannianEDistOf g x (gamma (-t))).toReal - t)
        atTop (𝓝 (bminus x))) ∧
      (∀ s : ℝ, bplus (gamma s) = -s ∧ bminus (gamma s) = s) ∧
      (∀ x, 0 ≤ bplus x + bminus x) := by
  obtain ⟨gamma, hsmooth, hgeo, hzero, hline⟩ :=
    exists_minimizing_line_on_cylinder g hcomplete
  have hsphereConnected : IsConnected (Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    apply isConnected_sphere _ _ (by norm_num)
    rw [← Module.finrank_eq_rank]
    norm_num
  let : ConnectedSpace Sphere3 := Subtype.connectedSpace hsphereConnected
  let : ConnectedSpace Cyl3 := inferInstance
  let : IsManifold ICyl3 1 Cyl3 :=
    IsManifold.of_le (I := ICyl3) (M := Cyl3) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace Cyl3 := Manifold.metrizableSpace ICyl3 Cyl3
  let : T3Space Cyl3 := inferInstance
  let : RiemannianBundle (fun x : Cyl3 ↦ TangentSpace ICyl3 x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2) × ℝ)
      (fun x : Cyl3 ↦ TangentSpace ICyl3 x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace Cyl3 := EMetricSpace.ofRiemannianMetric ICyl3 Cyl3
  let m : MetricSpace Cyl3 := HopfRinow.riemMetricSpace (I := ICyl3) (M := Cyl3)
  let : MetricSpace Cyl3 := m
  let : PseudoMetricSpace Cyl3 := m.toPseudoMetricSpace
  let : PseudoEMetricSpace Cyl3 := m.toPseudoEMetricSpace
  let : UniformSpace Cyl3 := m.toUniformSpace
  let : IsRiemannianManifold ICyl3 Cyl3 := ⟨by intro x y; rfl⟩
  have hEnorm : IsMetricNorm (I := ICyl3) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  have hed (x y : Cyl3) : edist x y = riemannianEDistOf g x y := by
    rw [riemannianEDistOf_eq_riemannianEDist g hEnorm]
    exact IsRiemannianManifold.out (I := ICyl3) x y
  have hdist (x y : Cyl3) : dist x y = (riemannianEDistOf g x y).toReal := by
    rw [← hed, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  have hisometry : Isometry gamma := by
    intro s t
    rw [hed, hline, edist_dist, Real.dist_eq]
  have hreverse : Isometry (fun t : ℝ ↦ gamma (-t)) := by
    apply Isometry.of_dist_eq
    intro s t
    rw [hisometry.dist_eq, Real.dist_eq, Real.dist_eq]
    have hneg : -s - -t = -(s - t) := by ring
    rw [hneg, abs_neg]
  have hplusLip := busemannFunction_lipschitz hisometry
  have hminusLip := busemannFunction_lipschitz hreverse
  refine ⟨gamma, hsmooth, hgeo, hzero, hline, ?_⟩
  change Continuous (fun x ↦ ⨅ t : ℝ, (riemannianEDistOf g x (gamma t)).toReal - t) ∧ _
  have hplus (x : Cyl3) : busemannFunction gamma x =
      ⨅ t : ℝ, (riemannianEDistOf g x (gamma t)).toReal - t := by
    simp only [busemannFunction, hdist]
  have hminus (x : Cyl3) : busemannFunction (fun t : ℝ ↦ gamma (-t)) x =
      ⨅ t : ℝ, (riemannianEDistOf g x (gamma (-t))).toReal - t := by
    simp only [busemannFunction, hdist]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [funext hplus] using hplusLip.continuous
  · simpa only [funext hminus] using hminusLip.continuous
  · intro x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, hplus, hdist] using
      hplusLip.dist_le_mul x y
  · intro x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, hminus, hdist] using
      hminusLip.dist_le_mul x y
  · intro x
    simpa only [hdist, hplus] using busemannFunction_tendsto hisometry x
  · intro x
    simpa only [hdist, hminus] using busemannFunction_tendsto hreverse x
  · intro s
    constructor
    · simpa only [hplus] using busemannFunction_apply_line hisometry s
    · simpa only [hminus] using busemannFunction_reverse_apply_line hisometry s
  · intro x
    simpa only [hplus, hminus] using busemannFunction_add_reverse_nonneg hisometry x

end DifferentialGeometry.Geometry.Metric

end

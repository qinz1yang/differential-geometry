import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarMetricControl

set_option autoImplicit false
noncomputable section
open Bundle Manifold MeasureTheory Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem collarEDist_triangle (g : SmoothRiemannianMetric I3 M) (x y z : M) :
    riemannianEDistOf (I := I3) g x z ≤
      riemannianEDistOf (I := I3) g x y + riemannianEDistOf (I := I3) g y z := by
  let : Bundle.RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_triangle

omit [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem collarEDist_comm (g : SmoothRiemannianMetric I3 M) (x y : M) :
    riemannianEDistOf (I := I3) g x y = riemannianEDistOf (I := I3) g y x := by
  let : Bundle.RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_comm

omit [T2Space M] [SigmaCompactSpace M] in
theorem exists_uniform_collar_section_diameter :
    ∃ D : ℝ, 0 < D ∧ ∀ (C : CylinderReference) (h : ℝ → SmoothRiemannianMetric IC Cylinder)
      (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
      (U : Set Cylinder) (times : Set ℝ) (order : ℕ) (eps z : ℝ),
      MetricComparisonOn h g F U times order eps → h 0 = C.metric 0 → 0 ≤ eps → eps ≤ 1 →
      0 ∈ times → U ⊆ F.source → (∀ y : Sphere 2, (y, z) ∈ U) → ∀ p q : Sphere 2,
      riemannianEDistOf (g 0) (F (p, z)) (F (q, z)) ≤ ENNReal.ofReal D := by
  obtain ⟨D, hD, hshort⟩ := exists_uniform_transverse_shortcuts (M := M)
  refine ⟨D, hD, ?_⟩
  intro C h g F U times order eps z cmp hmetric heps heps1 hzero hsource hlevel p q
  obtain ⟨gamma, hstart, hend, hgamma, -, hlen⟩ :=
    hshort C h g F U times order eps z cmp hmetric heps heps1 hzero hsource hlevel p q
  have hdist := edistOf_le_metricPathELength (g 0) (by norm_num : (0 : ℝ) ≤ 1) hgamma
  rw [hstart, hend] at hdist
  exact hdist.trans hlen

omit [T2Space M] [SigmaCompactSpace M] in
theorem exists_uniform_collar_band_diameter_of_axis :
    ∃ D : ℝ, 0 < D ∧ ∀ (C : CylinderReference) (h : ℝ → SmoothRiemannianMetric IC Cylinder)
      (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
      (U : Set Cylinder) (times : Set ℝ) (order : ℕ) (eps V : ℝ),
      MetricComparisonOn h g F U times order eps → h 0 = C.metric 0 → 0 ≤ eps → eps ≤ 1 →
      0 ∈ times → U ⊆ F.source → univ ×ˢ Icc (-10 : ℝ) 10 ⊆ U → 0 ≤ V →
      (∀ (p : Sphere 2) (z : ℝ), z ∈ Icc (-10 : ℝ) 10 →
        riemannianEDistOf (g 0) (F (p, z)) (F (p, 0)) ≤ ENNReal.ofReal V) →
      ∀ v ∈ F '' (univ ×ˢ Icc (-10 : ℝ) 10), ∀ w ∈ F '' (univ ×ˢ Icc (-10 : ℝ) 10),
        riemannianEDistOf (g 0) v w ≤ ENNReal.ofReal (D + 2 * V) := by
  obtain ⟨D, hD, hsection⟩ := exists_uniform_collar_section_diameter (M := M)
  refine ⟨D, hD, ?_⟩
  intro C h g F U times order eps V cmp hmetric heps heps1 hzero hsource hslab hV haxis
    v hv w hw
  have hlevel : ∀ y : Sphere 2, (y, (0 : ℝ)) ∈ U :=
    fun y => hslab ⟨mem_univ _, ⟨by norm_num, by norm_num⟩⟩
  obtain ⟨vx, hvx, rfl⟩ := hv
  obtain ⟨wx, hwx, rfl⟩ := hw
  have hvV : riemannianEDistOf (I := I3) (g 0) (F vx) (F (vx.1, 0)) ≤ ENNReal.ofReal V :=
    haxis vx.1 vx.2 hvx.2
  have hwV : riemannianEDistOf (I := I3) (g 0) (F (wx.1, 0)) (F wx) ≤ ENNReal.ofReal V :=
    (collarEDist_comm (g 0) (F (wx.1, 0)) (F wx)).trans_le (haxis wx.1 wx.2 hwx.2)
  have hsec := hsection C h g F U times order eps 0 cmp hmetric heps heps1 hzero hsource hlevel
    vx.1 wx.1
  have htri := collarEDist_triangle (g 0) (F vx) (F (vx.1, 0)) (F wx)
  have htri' := collarEDist_triangle (g 0) (F (vx.1, 0)) (F (wx.1, 0)) (F wx)
  have hstep : riemannianEDistOf (I := I3) (g 0) (F vx) (F (vx.1, 0)) +
      riemannianEDistOf (I := I3) (g 0) (F (vx.1, 0)) (F wx) ≤
      ENNReal.ofReal V + (ENNReal.ofReal D + ENNReal.ofReal V) :=
    add_le_add hvV (htri'.trans (add_le_add hsec hwV))
  have hsum : ENNReal.ofReal V + (ENNReal.ofReal D + ENNReal.ofReal V) =
      ENNReal.ofReal (D + 2 * V) := by
    rw [← add_assoc, ← ENNReal.ofReal_add hV hD.le,
      ← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ V + D) hV]
    congr 1
    ring
  exact htri.trans (hstep.trans hsum.le)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

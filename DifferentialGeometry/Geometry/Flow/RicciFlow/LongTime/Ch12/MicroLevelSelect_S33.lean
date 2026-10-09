import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CanonicalNbhdP6Level_S23

/-!
# CH12-S33, group G2: level selection on a metric ball of a slice

Between a point with `R ≤ a` and a point with `R ≥ b` of one metric ball `B(p, ρ)`, every level
`c ∈ [a, b]` is attained inside the ball (the ball is path-connected and `R` is continuous);
the level point lies in the connected component of `p`.  Generalises `exists_level_point_S23`
(which takes `y₁ = p` and a strict inequality).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set
open GC.LongTime
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

theorem exists_level_point_between_S33 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (p : M) {ρ a b c : ℝ} (hρ : 0 < ρ)
    {y₁ y₂ : M} (hy₁ : y₁ ∈ riemannianBallOf g p ρ) (hy₂ : y₂ ∈ riemannianBallOf g p ρ)
    (h₁ : metricScalarAt g y₁ ≤ a) (h₂ : b ≤ metricScalarAt g y₂) (hac : a ≤ c)
    (hcb : c ≤ b) :
    ∃ z ∈ riemannianBallOf g p ρ, metricScalarAt g z = c ∧ z ∈ connectedComponent p := by
  have hpc := isPathConnected_riemannianBallOf (I := ThreeModel) g p hρ
  have hpm : p ∈ riemannianBallOf g p ρ := by
    change riemannianEDistOf g p p < ENNReal.ofReal ρ
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hρ
  have hcont : Continuous (metricScalarAt g) := (metricScalar_smooth g).continuous
  have h := hpc.isConnected.isPreconnected.intermediate_value hy₁ hy₂ hcont.continuousOn
    ⟨(h₁.trans hac), (hcb.trans h₂)⟩
  obtain ⟨z, hz, hzc⟩ := h
  exact ⟨z, hz, hzc, hpc.isConnected.isPreconnected.subset_connectedComponent hpm hz⟩

theorem slice_level_point_S33 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g}
    (s : RegularSlice F.observation) (p : s.stage.Carrier) {ρ a b c : ℝ} (hρ : 0 < ρ)
    {y₁ y₂ : s.stage.Carrier} (hy₁ : y₁ ∈ riemannianBallOf s.metric p ρ)
    (hy₂ : y₂ ∈ riemannianBallOf s.metric p ρ)
    (h₁ : metricScalarAt s.metric y₁ ≤ a) (h₂ : b ≤ metricScalarAt s.metric y₂) (hac : a ≤ c)
    (hcb : c ≤ b) :
    ∃ z ∈ riemannianBallOf s.metric p ρ, metricScalarAt s.metric z = c ∧
      z ∈ connectedComponent p :=
  exists_level_point_between_S33 s.metric p hρ hy₁ hy₂ h₁ h₂ hac hcb

end GC.LongTime.Ch12

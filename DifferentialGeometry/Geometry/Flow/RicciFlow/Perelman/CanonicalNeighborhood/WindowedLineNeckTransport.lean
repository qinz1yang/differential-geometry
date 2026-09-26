import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNeckLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LineCylinderNeck

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem eventually_strongNeck_of_windowed_models_of_line
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappaL : ℝ}
    (hL : IsAncientKappaSolution kappaL L) (hbase : PointedFlowScalarAtBase L 1)
    (o : TangentOrientationSection L.M) (γ : ℝ → L.M)
    (hγ : ∀ a b, metricDistance (L.S.base.metric 0) (γ a) (γ b) = |a - b|)
    (hγ0 : γ 0 = L.basepoint)
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) :
    ∀ᶠ i in atTop,
      Nonempty (StrongNeck (S (phi i)) (2 * alpha) (x (phi i)) (t (phi i))) := by
  have htol : 0 < neckModelTolerance alpha := neckModelTolerance_pos ha
  let beta := min (neckModelTolerance alpha / 2) (1 / 22)
  have hbeta : 0 < beta := lt_min (half_pos htol) (by norm_num)
  have hbeta1 : beta < 1 / 11 := (min_le_right _ _).trans_lt (by norm_num)
  have hbetaTol : beta < neckModelTolerance alpha :=
    (min_le_left _ _).trans_lt (half_lt_self htol)
  obtain ⟨nk⟩ := KappaSolutions.exists_strongNeck_of_line L hL hbase o γ hγ hγ0 hbeta hbeta1
  let _ : ConnectedSpace L.M := hL.connected
  have hcomplete : MetricComplete (L.atTime 0) := hL.complete 0 (by simp)
  filter_upwards [StrongNeck.eventually_transport_of_windowed_models hS W hdelta hreg L
    hcomplete hphi F hcmp nk ha hsmall hbetaTol] with i hi
  obtain ⟨nk', _⟩ := hi
  have hpt : (W (phi i)).embedding (F.map i L.basepoint) = x (phi i) := by
    rw [show F.map i L.basepoint = (W (phi i)).model.basepoint from F.basepoint_map i]
    exact (W (phi i)).base_map
  exact ⟨hpt ▸ nk'⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedPositiveCanonicalLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactAncientPositiveWitness

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
  [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]

theorem CanonicalWitness.exists_eventually_buffered_of_windowed_models_of_positive
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    [PreconnectedSpace L.M] (hcomplete : MetricComplete (L.atTime 0))
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    {eps C1 C2 : ℝ} (K : CanonicalWitness L.S eps C1 C2 L.basepoint 0)
    (hscalar : L.S.scalar 0 L.basepoint = 1)
    (hpositive : ∃ whole data sec, K.alternative = CanonicalAlternative.positive whole data sec) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ i in atTop, ∀ (alpha : ℝ), 0 < alpha → ∀ (H : ℝ),
      Nonempty (BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i))) := by
  let C0 := max (sourceCurvatureBound 3 C2)
    (max (4 * C2) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C2)))
  have hC : 1 ≤ max (max C1 2) C0 + 1 := by
    linarith [le_max_left (max C1 2) C0, le_max_right C1 2]
  refine ⟨max (max C1 2) C0 + 1, hC, ?_⟩
  filter_upwards [K.eventually_positive_image_of_windowed_models hS W hdelta hreg L
    hcomplete hphi F hcmp hscalar hpositive] with i hi
  intro alpha ha H
  let tolerance := min (alpha / 2) (1 / 2 : ℝ)
  have htol : 0 < tolerance := lt_min (by positivity) (by norm_num)
  have htol1 : tolerance < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have htola : tolerance < alpha := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨Ki, _hKi, whole, data, sec, halt⟩ := hi tolerance htol htol1
  apply Ki.exists_bufferedCanonical htola
  intro cap hc
  obtain ⟨depth, hcap⟩ := hc
  rw [halt] at hcap
  cases hcap

theorem exists_eventually_buffered_of_windowed_models_of_compact_positive_limit
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    {kappaL : ℝ} (hL : IsAncientKappaSolution kappaL L) [CompactSpace L.M]
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    (hscalar : L.S.scalar 0 L.basepoint = 1) (data : PositiveComponent (univ : Set L.M)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ i in atTop, ∀ (alpha : ℝ), 0 < alpha → ∀ (H : ℝ),
      Nonempty (BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i))) := by
  let _ : ConnectedSpace L.M := hL.connected
  obtain ⟨A, C0, _hA, _hC0, hK⟩ := exists_positive_canonicalWitness_of_compact_ancientKappa
    L hL data le_rfl L.basepoint
  obtain ⟨K, _hKuniv, hpositive⟩ := hK (1 / 2) (by norm_num) (by norm_num)
  exact K.exists_eventually_buffered_of_windowed_models_of_positive hS W hdelta hreg L
    (hL.complete 0 (by simp)) hphi F hcmp hscalar hpositive

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

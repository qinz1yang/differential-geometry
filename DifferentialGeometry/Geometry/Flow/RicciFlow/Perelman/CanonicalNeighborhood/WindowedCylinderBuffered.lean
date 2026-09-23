import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BufferedCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNeckCanonicalLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderNecks
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

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

theorem exists_eventually_buffered_with_cap_tube_neck_chart_of_windowed_models_of_trivial_cylinder_limit
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
    {kappaL : ℝ} (hL : IsAncientKappaSolution kappaL L)
    (hscalar : L.S.scalar 0 L.basepoint = 1) (cover : KappaSolutions.ShrinkingCylinderCover L)
    (htrivial : cover.TrivialModel) {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ i in atTop, ∀ H : ℝ,
      ∃ B : BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i)),
        B.witness.capTubeHasNeckChart alpha := by
  let eps := neckModelTolerance (alpha / 4) / 2
  have heps : 0 < eps := half_pos (neckModelTolerance_pos (by positivity))
  have hepslt : eps < neckModelTolerance (alpha / 4) := by
    dsimp only [eps]
    exact half_lt_self (neckModelTolerance_pos (by positivity))
  have hepssmall : eps < 1 / 11 := hepslt.trans_le (neckModelTolerance_le (alpha / 4)) |>.trans (by linarith)
  obtain ⟨_mark, _e, _hmarked, _hmetric, hnecks⟩ := exists_strongNeck_of_shrinkingCylinderCover_trivialModel L cover htrivial hscalar
  obtain ⟨nk, _hnkmap, _hnkcenter⟩ := hnecks eps heps hepssmall
  obtain ⟨C0, hC0, K, _hKregion, _hKradius, data, hKalt, _hKneck⟩ := nk.exists_canonicalWitness_of_scalar_pos
    (fun y _ => KappaSolutions.ancientKappa_scalar_pos L hL le_rfl y)
  let C1 := max (sourceCurvatureBound 3 C0)
    (max (4 * C0) (2 * windowedGoodPointConstant (18 * sourceCurvatureBound 3 C0)))
  have hC1 : 1 ≤ max (max 9 2) C1 + 1 := by norm_num
  refine ⟨max (max 9 2) C1 + 1, hC1, ?_⟩
  filter_upwards [K.eventually_neck_image_of_windowed_models hS W hdelta hreg L hcomplete hphi F hcmp
    hscalar data hKalt (by positivity : 0 < alpha / 4) (by linarith) hepslt] with i hi
  obtain ⟨Ki, _hKiCarrier, datai, hKiAlt, _hmap⟩ := hi
  intro H
  obtain ⟨B, _hBeps, _hBDomain, _hBradius, nkB, halt, _hBneck⟩ := Ki.exists_bufferedCanonical_of_neck
    (H := H) (by linarith : 2 * (alpha / 4) < alpha) datai hKiAlt
  refine ⟨B, ?_⟩
  intro cap depth hdepth
  rw [halt] at hdepth
  cases hdepth

theorem exists_eventually_buffered_of_windowed_models_of_trivial_cylinder_limit
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
    {kappaL : ℝ} (hL : IsAncientKappaSolution kappaL L)
    (hscalar : L.S.scalar 0 L.basepoint = 1) (cover : KappaSolutions.ShrinkingCylinderCover L)
    (htrivial : cover.TrivialModel) {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ i in atTop, ∀ H : ℝ,
      Nonempty (BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i))) := by
  obtain ⟨C, hC, hB⟩ :=
    exists_eventually_buffered_with_cap_tube_neck_chart_of_windowed_models_of_trivial_cylinder_limit
      hS W hdelta hreg L hcomplete hphi F hcmp hL hscalar cover htrivial ha hasmall
  refine ⟨C, hC, ?_⟩
  filter_upwards [hB] with i hi
  intro H
  obtain ⟨B, _⟩ := hi H
  exact ⟨B⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

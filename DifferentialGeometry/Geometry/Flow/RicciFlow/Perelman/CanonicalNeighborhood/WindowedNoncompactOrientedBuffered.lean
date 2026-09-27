import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCylinderBuffered
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedDiagonalBuffered
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNoncompactPositiveBuffered
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.OrientedCylinderExclusion

section
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

theorem exists_eventually_buffered_with_cap_neck_charts_of_windowed_models_of_noncompact_oriented_limit
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    {kappaL : ℝ} (hL : IsAncientKappaSolution kappaL L)
    (hnoncompact : NoncompactSpace L.M) (hscalar : L.S.scalar 0 L.basepoint = 1)
    (orient : ∀ i, TangentOrientationSection (W i).model.M)
    {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ i in atTop,
      ∃ B : BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i)),
        B.witness.capTubeHasNeckChart alpha := by
  let _ : ConnectedSpace L.M := hL.connected
  have hcomplete : MetricComplete (L.atTime 0) := hL.complete 0 (by simp)
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rcases (KappaSolutions.ancientKappa_three_dimensional_split_branch L hL hdim).or with hpositive | ⟨cover, hcases⟩
  · have hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (L.S.base.metric 0) :=
      (KappaSolutions.hasPositiveSectionalCurvature_iff_forall_curvatureOperatorPositiveAt
        (L.S.base.metric 0) hdim).mpr (hpositive 0 le_rfl)
    obtain ⟨_eps, _A, _C0, C, _heps, _hepsTol, hC, _K, _cap, _v, _neck,
        _hKcap, _hmap, _hv, _hcount, _hchain, hsource⟩ :=
      exists_buffered_image_with_cap_neck_charts_of_windowed_models_of_noncompact_positive_limit
        hS W hdelta hreg L hL hnoncompact hsec hphi F hcmp hscalar ha hasmall H
    refine ⟨C, hC, hsource.mono ?_⟩
    intro i hi
    obtain ⟨_Ki, _hKi, _capi, _depthi, _hKiCap, _htubei, _hcorei, _hmapi, _ni, _hni, B, _heps, _hBU, _hBr, _hB, hcharts⟩ := hi
    exact ⟨B, hcharts⟩
  · rcases hcases with htrivial | hantipodal | hdiagonal
    · obtain ⟨C, hC, hi⟩ := exists_eventually_buffered_with_cap_tube_neck_chart_of_windowed_models_of_trivial_cylinder_limit
        hS W hdelta hreg L hcomplete hphi F hcmp hL hscalar cover htrivial ha hasmall
      exact ⟨C, hC, hi.mono fun i hi => hi H⟩
    · obtain ⟨d, _hd⟩ := hantipodal.1
      exact (KappaSolutions.pointedLimit_not_antipodalProduct_diffeomorph F orient ⟨d⟩).elim
    · exact exists_eventually_buffered_with_cap_neck_charts_of_windowed_models_of_diagonal_cylinder_limit
        hS W hdelta hreg L hcomplete hphi F hcmp hscalar cover hdiagonal ha hasmall H

theorem exists_eventually_buffered_of_windowed_models_of_noncompact_oriented_limit
    {D : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)}
    (hS : ∀ i, IsSolutionOn (S i)) {delta : ℕ → ℝ} {kappa : ℝ}
    {x : ∀ i, M i} {t : ℕ → ℝ}
    (W : ∀ i, WindowedModelWitness (delta i) kappa (S i) (x i) (t i))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hreg : ∀ i, Ioo (t i - (delta i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular)
    (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩
      (L.atTime 0) phi)
    (hcmp : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta))
    {kappaL : ℝ} (hL : IsAncientKappaSolution kappaL L)
    (hnoncompact : NoncompactSpace L.M) (hscalar : L.S.scalar 0 L.basepoint = 1)
    (orient : ∀ i, TangentOrientationSection (W i).model.M)
    {alpha : ℝ} (ha : 0 < alpha) (hasmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ i in atTop,
      Nonempty (BufferedCanonical (S (phi i)) alpha C H (x (phi i)) (t (phi i))) := by
  obtain ⟨C, hC, hB⟩ := exists_eventually_buffered_with_cap_neck_charts_of_windowed_models_of_noncompact_oriented_limit
    hS W hdelta hreg L hphi F hcmp hL hnoncompact hscalar orient ha hasmall H
  exact ⟨C, hC, hB.mono (fun _ ⟨B, _⟩ => ⟨B⟩)⟩


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

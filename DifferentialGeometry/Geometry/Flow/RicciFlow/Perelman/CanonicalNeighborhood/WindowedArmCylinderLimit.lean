import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedArmComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedArmConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedOrientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedShiTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SeparatedRayCylinderBranch
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaFixedCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderNecks

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem exists_windowed_tolerances_for_original_arm_cylinder_limit :
    ∃ delta : ℕ → ℝ, (∀ i, 0 < delta i) ∧ Tendsto delta atTop (𝓝 0) ∧
      ∀ (M : ℕ → Type u) [∀ i, TopologicalSpace (M i)]
        [∀ i, ChartedSpace ThreeSpace (M i)] [∀ i, IsManifold I3 ∞ (M i)]
        [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]
        (D : ℕ → RealTimeInterval) (S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)),
        (∀ i, IsSolutionOn (S i)) →
        (∀ i, TangentOrientationSection (M i)) → ∀ (kappa : ℝ)
          (x : ∀ i, M i) (t eps : ℕ → ℝ)
          (W : ∀ i, WindowedModelWitness (eps i) kappa (S i) (x i) (t i)),
          (∀ i, eps i ≤ delta i) →
          (∀ i, Ioo (t i - (eps i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular) →
          ∀ (arms : ∀ i, Fin 2 → MinimizingArm ((S i).base.metric (t i)) (x i))
            (ell : ℕ → Fin 2 → ℝ),
            (∀ i j, ell i j ∈ Ioc 0 (arms i j).length) →
            (∀ (i : ℕ) j, Real.sqrt ((S i).scalar (t i) (x i)) * ell i j ∈
              Icc ((i : ℝ) + 1) (2 * ((i : ℝ) + 1))) →
            ∀ theta : ℝ, 0 < theta →
              (∀ᶠ i in atTop, theta ≤ comparisonAngle (ell i 0) (ell i 1)
                (metricDistance ((S i).base.metric (t i))
                  ((arms i 0).point (ell i 0)) ((arms i 1).point (ell i 1)))) →
              ∃ (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) (phi : ℕ → ℕ),
                StrictMono phi ∧ IsAncientKappaSolution kappa L ∧ PointedFlowScalarAtBase L 1 ∧
                ∃ F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩ (L.atTime 0) phi,
                  (∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
                    ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
                      Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
                        (F.map i) K (Icc (-A) 0) order eta)) ∧
                  ∃ (p : Sphere 2) (e : Diffeomorph IC I3 Cylinder L.M ∞),
                    e (p, 0) = L.basepoint ∧
                    (∀ s : ℝ, s ≤ 0 → Diffeomorph.pullbackMetricCross (L.S.base.metric s) e =
                      cylinderReferenceMetric s) ∧
                    (∀ beta : ℝ, 0 < beta → beta < 1 / 11 →
                      ∃ nk : StrongNeck L.S beta L.basepoint 0,
                        nk.map = e.toPartialDiffeomorph ∧ nk.center = p) ∧
                    ∃ rays : Fin 2 × ℝ≥0 → L.M,
                      MapClusterPt rays atTop (fun i z =>
                        (partialDiffeomorphTransMixed (F.partialDiffeomorph i) (W (phi i)).embedding).symm
                          ((arms (phi i) z.1).point
                            ((z.2 : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))))) ∧
                      (∀ j, rays (j, 0) = L.basepoint) ∧
                      (∀ j s v, metricDistance (L.S.base.metric 0) (rays (j, s)) (rays (j, v)) =
                        |(s : ℝ) - v|) ∧
                      ∀ r : ℝ≥0, 0 < r → theta / 4 ≤ comparisonAngle r r
                        (metricDistance (L.S.base.metric 0) (rays (0, r)) (rays (1, r))) := by
  obtain ⟨delta, hdelta, hzero, hangleSource⟩ := exists_windowed_tolerances_for_original_arm_comparisonAngles.{u}
  refine ⟨delta, hdelta, hzero, ?_⟩
  intro M _ _ _ _ _ D S hS o kappa x t eps W heps hregular arms ell hell hlength theta htheta hangle
  have hepsZero : Tendsto eps atTop (𝓝 0) := squeeze_zero (fun i => (W i).eps_pos.le) heps hzero
  have hsourceAngles := hangleSource M D S kappa x t eps W heps arms ell hell hlength theta htheta hangle
  let models := fun i => (W i).model
  obtain ⟨L, phi, hphi, Phi, hL, hbase, _hK, _hconv, hcmp⟩ :=
    KappaSolutions.exists_ancientKappa_fixed_kappa_compactness models
      (fun i => (W i).model_ancient) (fun i => (W i).model_scalar_base)
  let _ : ConnectedSpace L.M := hL.connected
  have hcomplete : MetricComplete (L.atTime 0) := hL.complete 0 (by simp)
  let F : PointedRiemannianConvergenceMaps ⟨fun i => (W i).model.atTime 0⟩ (L.atTime 0) phi :=
    Phi.atTime (X := KappaSolutions.ancientPointedFlowSeq models) (L := L) 0
  have hcmp' : ∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn L.S.base.metric (W (phi i)).model.S.base.metric
          (F.map i) K (Icc (-A) 0) order eta) :=
    fun K hK A hA order eta heta => hcmp (-A) 0 (by linarith) le_rfl K hK order eta heta
  have hreg : ∀ i s, s ∈ Ioo (-modelDepth (eps i)) 0 →
      parabolicTime (t i) ((S i).scalar (t i) (x i)) s ∈ (D i).regular :=
    fun i s hs => ((W i).normalized_window (hregular i)).2 hs
  have hlong : ∀ j, Tendsto (fun i => Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))) *
      (arms (phi i) j).length) atTop atTop := by
    intro j
    have hnat : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
      tendsto_atTop_mono (fun i : ℕ => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
    have hl : ∀ i : ℕ, (i : ℝ) + 1 ≤ Real.sqrt ((S i).scalar (t i) (x i)) * (arms i j).length :=
      fun i => (hlength i j).1.trans (mul_le_mul_of_nonneg_left (hell i j).2 (Real.sqrt_nonneg _))
    exact (tendsto_atTop_mono hl hnat).comp hphi.tendsto_atTop
  obtain ⟨rays, hcluster, hraybase, hraymetric, hrayangle⟩ :=
    WindowedModelWitness.exists_composed_original_arm_rays hS W hepsZero hreg L hcomplete
      hphi.tendsto_atTop F hcmp' (fun i => arms (phi i)) hlong (half_pos htheta)
      (fun r hr => hphi.tendsto_atTop.eventually (hsourceAngles r hr))
  obtain ⟨O⟩ := WindowedModelWitness.orientable_limit_of_orientable_sources
    hS W hepsZero hreg L hL o hphi.tendsto_atTop F hcmp'
  have hangleEventually : ∀ᶠ r : ℝ≥0 in atTop, (theta / 2) / 2 ≤ comparisonAngle r r
      (metricDistance (L.S.base.metric 0) (rays (0, r)) (rays (1, r))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with r hr
    exact hrayangle r hr
  obtain ⟨C, htrivial⟩ := KappaSolutions.exists_trivial_shrinkingCylinderCover_of_rays_comparisonAngle_lower
    L hL hbase O (fun r => rays (0, r)) (fun r => rays (1, r))
    (fun s v => hraymetric 0 s v) (fun s v => hraymetric 1 s v)
    (hraybase 0) (hraybase 1) (half_pos (half_pos htheta)) hangleEventually
  obtain ⟨p, e, hmark, hmetric, hnecks⟩ :=
    exists_strongNeck_of_shrinkingCylinderCover_trivialModel L C htrivial hbase
  refine ⟨L, phi, hphi, hL, hbase, F, hcmp', p, e, hmark, hmetric, hnecks,
    rays, hcluster, hraybase, hraymetric, ?_⟩
  intro r hr
  simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hrayangle r hr

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

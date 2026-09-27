import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Curvature.PositiveSectional
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormGroup
import DifferentialGeometry.Topology.Manifold.DiffeomorphOrientationDichotomy
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormProjective

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

noncomputable def roundSphereQuotientOfSphericalSpaceFormGroup
    (G : DifferentialGeometry.Topology.SphericalSpaceFormGroup) :
    RoundSphereQuotient (EuclideanSpace ℝ (Fin 4)) 3 := by
  classical
  letI : Fintype G.group := Fintype.ofFinite G.group
  exact {
    Q := G.Orbit
    Γ := G.group
    ρ := G.group.subtype
    action_free := by
      intro γ q hq
      exact G.free γ q hq
    proj := G.projection
    proj_smooth := G.projection_isLocalDiffeomorph.contMDiff
    proj_smul := by
      intro γ q
      exact G.projection_invariant γ q
    proj_eq_imp := by
      intro q1 q2 h
      exact (G.projection_eq_iff q1 q2).mp h
    sectionAt := fun x =>
      LocalSmoothSection.ofLocal (proj := G.projection) G.projection_surjective
        G.projection_isLocalDiffeomorph x }

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry
open DifferentialGeometry.Topology

universe u

private theorem metricRm04StandardAt_eq_zero_of_not_linearIndependent
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (x : M)
    (W T : TangentSpace ThreeModel x) (hdep : ¬ LinearIndependent ℝ ![W, T]) :
    DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt
      (I := ThreeModel) (M := M) g x W T T W = 0 := by
  let B : TangentSpace ThreeModel x → TangentSpace ThreeModel x →
      TangentSpace ThreeModel x → TangentSpace ThreeModel x → ℝ :=
    fun X Y Z U => DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt
      (I := ThreeModel) (M := M) g x X Y Z U
  have hB : DifferentialGeometry.Geometry.Curvature.IsAlgCurvForm B := by
    change DifferentialGeometry.Geometry.Curvature.IsAlgCurvForm
      (DifferentialGeometry.Geometry.Curvature.tensor04StandardAt
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := ThreeModel) (M := M) g x))
    exact DifferentialGeometry.Geometry.Curvature.mem_algebraicCurvatureTensorSubmodule.mp
      (DifferentialGeometry.Geometry.Curvature.metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := ThreeModel) (M := M) g x)
  by_cases hW : W = 0
  · subst hW
    have hzero := hB.smul_left 0 (0 : TangentSpace ThreeModel x) T T 0
    simpa [B] using hzero
  · rw [LinearIndependent.pair_iff' hW] at hdep
    push Not at hdep
    obtain ⟨a, rfl⟩ := hdep
    have hdiag : B W W (a • W) W = 0 := by
      have hskew := hB.anti_first W W (a • W) W
      linarith
    have hskew := hB.anti_first W (a • W) (a • W) W
    have hsmul := hB.smul_left a W W (a • W) W
    change B W (a • W) (a • W) W = 0
    rw [hskew, hsmul, hdiag]
    ring

private theorem sectionalCurvatureDenominator_eq_zero_of_not_linearIndependent
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (x : M)
    (v w : TangentSpace ThreeModel x) (hdep : ¬ LinearIndependent ℝ ![v, w]) :
    g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 = 0 := by
  have hnonneg : 0 ≤ g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 := by
    simpa only [DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def]
      using DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_nonneg
        (I := ThreeModel) (M := M) g x v w
  have hnotpos : ¬ 0 < g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 := by
    intro hpos
    exact hdep (DifferentialGeometry.Geometry.Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos
      (I := ThreeModel) (M := M) g x v w (by
        simpa only [DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def]
          using hpos))
  exact le_antisymm (le_of_not_gt hnotpos) hnonneg

theorem sectionalCurvatureMetricBridge_holds :
    sectionalCurvatureMetricBridge.{u} := by
  intro M g hg
  obtain ⟨κ, hκpos, hκ⟩ := hg
  refine ⟨κ, hκpos, fun x X Y => ?_⟩
  by_cases hLI : LinearIndependent ℝ ![X, Y]
  · have hden : 0 < g.inner x X X * g.inner x Y Y - (g.inner x X Y) ^ 2 := by
      simpa only [DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def]
        using DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
          (I := ThreeModel) (M := M.Carrier) g x X Y hLI
    have hsec := hκ x X Y hLI
    rw [DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div]
      at hsec
    field_simp [ne_of_gt hden] at hsec
    linarith
  · have hnum := metricRm04StandardAt_eq_zero_of_not_linearIndependent
      (M := M.Carrier) g x X Y hLI
    have hden := sectionalCurvatureDenominator_eq_zero_of_not_linearIndependent
      (M := M.Carrier) g x X Y hLI
    rw [hnum]
    have hden' : g.inner x X X * g.inner x Y Y -
        g.inner x X Y * g.inner x X Y = 0 := by
      simpa only [pow_two] using hden
    rw [hden', mul_zero]

theorem roundSphereQuotientOrientedCovering_holds :
    roundSphereQuotientOrientedCovering.{u} := by
  intro M D he
  obtain ⟨e⟩ := he
  let G := sphericalSpaceFormGroupOfRoundSphereQuotient D
  let F : Diffeomorph (𝓡 3) (𝓡 3) M.Carrier G.Orbit ∞ :=
    e.trans (sphericalSpaceFormOrbitDiffeomorph D).symm
  rcases Diffeomorph.preservesOrientation_or_preservesOrientation_opposite F
      M.orientation G.manifold.orientation with hF | hF
  · exact ⟨G, ⟨⟨F, hF⟩⟩⟩
  · obtain ⟨G', ⟨f⟩⟩ := sphericalSpaceFormOrientationClosure_holds G
    let Fop : ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold G.manifold.opposite.toClosedOrientedManifold := ⟨F, hF⟩
    exact ⟨G', ⟨Fop.trans f⟩⟩

theorem sphericalSpaceFormCovering_holds : sphericalSpaceFormCovering.{u} :=
  sphericalSpaceFormCovering_of_inputs sectionalCurvatureMetricBridge_holds
    roundSphereQuotientOrientedCovering_holds

noncomputable def sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup
    (G : SphericalSpaceFormGroup) :
    SphericalSpaceFormQuotientModel ThreeModel G.manifold.Carrier where
  quotient := roundSphereQuotientOfSphericalSpaceFormGroup G
  equiv := Diffeomorph.refl ThreeModel G.manifold.Carrier ∞

private theorem isConstantPositiveSectionalCurvature_of_metric
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M)
    (hg : DifferentialGeometry.Geometry.Curvature.constantPositiveSectionalCurvatureMetric
      (I := ThreeModel) (M := M) g) :
    IsConstantPositiveSectionalCurvature g := by
  obtain ⟨c, hc, hsec⟩ := hg
  refine ⟨c, hc, fun x v w hLI => ?_⟩
  have hden : 0 < g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 := by
    simpa only [DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def]
      using DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
        (I := ThreeModel) (M := M) g x v w hLI
  rw [DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div,
    hsec x v w]
  field_simp [ne_of_gt hden]

theorem isPositiveSpaceFormModel_antipodal :
    IsPositiveSpaceFormModel SphericalSpaceFormGroup.antipodal.manifold := by
  obtain ⟨g, hg⟩ :=
    spherical_space_form_admits_constant_positive_sectional_curvature
      (I := ThreeModel) (M := SphericalSpaceFormGroup.antipodal.manifold.Carrier)
      ⟨sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup
        SphericalSpaceFormGroup.antipodal⟩
  exact ⟨g, isConstantPositiveSectionalCurvature_of_metric g hg⟩

theorem exists_isPositiveSpaceFormModel_nonsimplyConnected :
    ∃ M : ConnectedClosedOrientedManifold.{0} 3,
      IsPositiveSpaceFormModel M ∧
        ∀ p : M.Carrier, ¬ Subsingleton (FundamentalGroup M.Carrier p) :=
  ⟨SphericalSpaceFormGroup.antipodal.manifold,
    isPositiveSpaceFormModel_antipodal,
    SphericalSpaceFormGroup.not_subsingleton_fundamentalGroup_antipodal⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

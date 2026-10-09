import DifferentialGeometry.Geometry.Thurston.ProjectiveSumDihedral
import DifferentialGeometry.Geometry.Thurston.SphericalProductOrientation
import DifferentialGeometry.Geometry.Collapse.Inhabitants.SlimSpherePacket
import DifferentialGeometry.Geometry.Metric.Quotient
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Metric.Pullback.ProductReal
import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.OrthogonalAction

/-!
The standard projective-space connected sum carries an actual descended thin cylindrical
metric. The sphere and line scales are independent and positive, the quotient map is the fixed
dihedral presentation recharted on the source, and the pullback is literally that product metric.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open GC.Endpoint GC.Geometry.SphericalProduct
open scoped Manifold ContDiff

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] DifferentialGeometry.Geometry.Collapse.sphereDimension
  DifferentialGeometry.Geometry.Collapse.cylinderDimension

namespace DifferentialGeometry.Geometry.Collapse

universe u

private theorem dihedral_line_metric_invariant (b : LineIsometry) :
    Diffeomorph.pullbackMetric (DifferentialGeometry.euclideanMetric (E := ℝ)) (lineDiffeo b) =
      DifferentialGeometry.euclideanMetric (E := ℝ) := by
  have heq : lineDiffeo b =
      b.linearIsometryEquiv.toContinuousLinearEquiv.toDiffeomorph.trans
        (Topology.translateDiffeomorph (b 0)) := by
    ext x
    change b x = b.linearIsometryEquiv x + b 0
    simpa only [vadd_eq_add, add_zero] using b.map_vadd (0 : ℝ) x
  rw [heq, ← Diffeomorph.pullbackMetric_trans,
    Diffeomorph.pullbackMetric_euclidean_translation,
    LinearIsometryEquiv.pullbackMetric_euclidean]

def dihedralThinCylinderMetric (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ, ℝ)) sphereCylinder :=
  (scaleMetric (ε ^ 2) (pow_pos hε 2)
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))).prod
    (scaleMetric ((2 * L) ^ 2) (pow_pos (mul_pos (by norm_num) hL) 2)
      (DifferentialGeometry.euclideanMetric (E := ℝ)))

theorem dihedralThinCylinderMetric_invariant (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (γ : CylinderIsometry) :
    Diffeomorph.pullbackMetric (dihedralThinCylinderMetric ε L hε hL)
      (cylinderActDiffeo γ) = dihedralThinCylinderMetric ε L hε hL := by
  rw [dihedralThinCylinderMetric, cylinderActDiffeo, Diffeomorph.pullbackMetric_prodCongr]
  simp only [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    Diffeomorph.pullbackMetricCross_scaleMetric]
  simp only [Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    pullbackMetric_round_eq, dihedral_line_metric_invariant]

def dihedralRechartedMetric (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    SmoothRiemannianMetric (𝓡 3) sphereCylinderRechart :=
  Diffeomorph.pullbackMetricCross (dihedralThinCylinderMetric ε L hε hL)
    sphereCylinderRechartDiffeomorph.symm

def dihedralRechartedAction (γ : CylinderIsometry) :
    sphereCylinderRechart ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphereCylinderRechart :=
  sphereCylinderRechartDiffeomorph.symm.trans
    ((cylinderActDiffeo γ).trans sphereCylinderRechartDiffeomorph)

theorem dihedralRechartedMetric_invariant (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (γ : CylinderIsometry) :
    Diffeomorph.pullbackMetric (dihedralRechartedMetric ε L hε hL)
      (dihedralRechartedAction γ) = dihedralRechartedMetric ε L hε hL := by
  have heq : (dihedralRechartedAction γ).trans sphereCylinderRechartDiffeomorph.symm =
      sphereCylinderRechartDiffeomorph.symm.trans (cylinderActDiffeo γ) := by
    apply Diffeomorph.ext
    intro x
    change sphereCylinderRechartDiffeomorph.symm
      (sphereCylinderRechartDiffeomorph (cylinderActDiffeo γ
        (sphereCylinderRechartDiffeomorph.symm x))) =
      cylinderActDiffeo γ (sphereCylinderRechartDiffeomorph.symm x)
    exact sphereCylinderRechartDiffeomorph.symm_apply_apply _
  rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric, dihedralRechartedMetric,
    Diffeomorph.pullbackMetricCross_trans, heq, ← Diffeomorph.pullbackMetricCross_trans,
    Diffeomorph.pullbackMetricCross_eq_pullbackMetric, dihedralThinCylinderMetric_invariant]

def dihedralStandardPresentation :
    CylinderQuotientPresentation (dihedralGroup 0 (1 / 2))
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
  Classical.choice projectiveSumStandardDihedralPresentation.{u}

def dihedralProjection : sphereCylinderRechart →
    (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
  dihedralStandardPresentation.proj ∘ sphereCylinderRechartDiffeomorph.symm

theorem dihedralProjection_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ dihedralProjection.{u} :=
  isLocalDiffeomorph_comp dihedralStandardPresentation.isLocalDiffeomorph
    sphereCylinderRechartDiffeomorph.symm.isLocalDiffeomorph

theorem dihedralProjection_surjective : Surjective dihedralProjection.{u} :=
  dihedralStandardPresentation.surjective.comp sphereCylinderRechartDiffeomorph.symm.surjective

theorem dihedralProjection_fibre_invariant (γ : CylinderIsometry)
    (hγ : γ ∈ dihedralGroup 0 (1 / 2)) :
    dihedralProjection.{u} ∘ dihedralRechartedAction γ = dihedralProjection := by
  funext x
  change dihedralStandardPresentation.proj
    (sphereCylinderRechartDiffeomorph.symm (dihedralRechartedAction γ x)) =
      dihedralStandardPresentation.proj (sphereCylinderRechartDiffeomorph.symm x)
  change dihedralStandardPresentation.proj (sphereCylinderRechartDiffeomorph.symm
    (sphereCylinderRechartDiffeomorph (cylinderActDiffeo γ
      (sphereCylinderRechartDiffeomorph.symm x)))) = _
  rw [sphereCylinderRechartDiffeomorph.symm_apply_apply]
  exact (dihedralStandardPresentation.fibres _ _).mpr ⟨γ, hγ, rfl⟩ |>.symm

theorem dihedralProjection_metricFiberCompatible (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    metricFiberCompatible (dihedralRechartedMetric ε L hε hL) dihedralProjection.{u}
      dihedralProjection_localDiffeomorph := by
  intro x y hxy
  obtain ⟨γ, hγ, hact⟩ := (dihedralStandardPresentation.fibres
    (sphereCylinderRechartDiffeomorph.symm y)
    (sphereCylinderRechartDiffeomorph.symm x)).mp hxy.symm
  have heq : dihedralRechartedAction γ y = x := by
    apply sphereCylinderRechartDiffeomorph.symm.injective
    change sphereCylinderRechartDiffeomorph.symm
      (sphereCylinderRechartDiffeomorph (cylinderActDiffeo γ
        (sphereCylinderRechartDiffeomorph.symm y))) = _
    rw [sphereCylinderRechartDiffeomorph.symm_apply_apply]
    exact hact
  subst x
  exact localPushInner_eq_of_fiber_preserving_isometry
    (dihedralRechartedMetric ε L hε hL) dihedralProjection
    dihedralProjection_localDiffeomorph (dihedralRechartedAction γ)
    (dihedralProjection_fibre_invariant γ hγ)
    (dihedralRechartedMetric_invariant ε L hε hL γ) y

def dihedralMetric (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    SmoothRiemannianMetric (𝓡 3)
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier :=
  descendedMetric (dihedralRechartedMetric ε L hε hL) dihedralProjection
    dihedralProjection_localDiffeomorph dihedralProjection_surjective
    (dihedralProjection_metricFiberCompatible ε L hε hL)

theorem dihedralMetric_pullback (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    localPullMetric (dihedralMetric.{u} ε L hε hL) dihedralProjection
      dihedralProjection_localDiffeomorph = dihedralRechartedMetric ε L hε hL :=
  localPullMetric_descendedMetric (dihedralRechartedMetric ε L hε hL) dihedralProjection
    dihedralProjection_localDiffeomorph dihedralProjection_surjective
    (dihedralProjection_metricFiberCompatible ε L hε hL)

end DifferentialGeometry.Geometry.Collapse

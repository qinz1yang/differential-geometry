import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderAxialNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.EqualDimensionImmersion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalDiffeomorphEmbedding
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance reflectionSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private def neckReflectionMap (epsilon : ℝ) (x : spatialNeckBuffer epsilon) :
    spatialNeckBuffer epsilon :=
  ⟨cylinderAxialScale (-1) (by norm_num) x.val, by
    obtain ⟨hlo, hhi⟩ := x.property
    change -epsilon⁻¹ - 1 < -1 * x.val.2 ∧ -1 * x.val.2 < epsilon⁻¹ + 1
    constructor <;> linarith⟩

private theorem neckReflectionMap_involutive (epsilon : ℝ) :
    Function.Involutive (neckReflectionMap epsilon) := by
  intro x
  apply Subtype.ext
  change (x.val.1, -1 * (-1 * x.val.2)) = x.val
  simp only [neg_one_mul, neg_neg, Prod.mk.eta]

private theorem neckReflectionMap_smooth (epsilon : ℝ) :
    ContMDiff SpatialNeckCylinderModel SpatialNeckCylinderModel ∞
      (neckReflectionMap epsilon) := by
  apply (ContMDiff.subtypeVal_comp_iff (spatialNeckBuffer epsilon) _).mp
  exact (cylinderAxialScale (-1) (by norm_num)).contMDiff.comp
    (contMDiff_subtype_val (I := SpatialNeckCylinderModel))


def spatialNeckReflection (epsilon : ℝ) :
    spatialNeckBuffer epsilon ≃ₘ⟮SpatialNeckCylinderModel, SpatialNeckCylinderModel⟯
      spatialNeckBuffer epsilon where
  toEquiv :=
    { toFun := neckReflectionMap epsilon
      invFun := neckReflectionMap epsilon
      left_inv := neckReflectionMap_involutive epsilon
      right_inv := neckReflectionMap_involutive epsilon }
  contMDiff_toFun := neckReflectionMap_smooth epsilon
  contMDiff_invFun := neckReflectionMap_smooth epsilon

@[simp] theorem spatialNeckReflection_val (epsilon : ℝ)
    (x : spatialNeckBuffer epsilon) :
    (spatialNeckReflection epsilon x).val = (x.val.1, -x.val.2) := by
  change (x.val.1, -1 * x.val.2) = _
  rw [neg_one_mul]

@[simp] theorem spatialNeckReflection_involutive (epsilon : ℝ)
    (x : spatialNeckBuffer epsilon) :
    spatialNeckReflection epsilon (spatialNeckReflection epsilon x) = x :=
  neckReflectionMap_involutive epsilon x

@[simp] theorem spatialNeckReflection_central (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (y : SpatialNeckSphere) :
    spatialNeckReflection epsilon (spatialNeckCentralPoint epsilon hepsilon y) =
      spatialNeckCentralPoint epsilon hepsilon y := by
  apply Subtype.ext
  rw [spatialNeckReflection_val]
  simp only [spatialNeckCentralPoint, neg_zero]

theorem spatialNeckReflection_core_iff (epsilon : ℝ) (x : spatialNeckBuffer epsilon) :
    spatialNeckReflection epsilon x ∈ spatialNeckClosedCore epsilon ↔
      x ∈ spatialNeckClosedCore epsilon := by
  change (-epsilon⁻¹ ≤ (spatialNeckReflection epsilon x).val.2 ∧
      (spatialNeckReflection epsilon x).val.2 ≤ epsilon⁻¹) ↔
    (-epsilon⁻¹ ≤ x.val.2 ∧ x.val.2 ≤ epsilon⁻¹)
  rw [spatialNeckReflection_val]
  constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> linarith

theorem spatialNeckReflection_image_core (epsilon : ℝ) :
    spatialNeckReflection epsilon '' spatialNeckClosedCore epsilon =
      spatialNeckClosedCore epsilon := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (spatialNeckReflection_core_iff epsilon y).mpr hy
  · intro hx
    exact ⟨spatialNeckReflection epsilon x,
      (spatialNeckReflection_core_iff epsilon x).mpr hx,
      spatialNeckReflection_involutive epsilon x⟩


theorem spatialNeckReflection_mfderiv (epsilon : ℝ) (x : spatialNeckBuffer epsilon)
    (V : TangentSpace SpatialNeckCylinderModel x) :
    mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel
      (spatialNeckReflection epsilon) x V = (V.1, -V.2) := by
  let ρ := spatialNeckReflection epsilon
  let ψ := cylinderAxialScale (-1) (by norm_num)
  have hv : MDifferentiableAt SpatialNeckCylinderModel SpatialNeckCylinderModel
      (Subtype.val : spatialNeckBuffer epsilon → SpatialNeckCylinder) x :=
    (contMDiff_subtype_val (I := SpatialNeckCylinderModel) (n := ∞)).mdifferentiableAt (by decide)
  have hvρ : MDifferentiableAt SpatialNeckCylinderModel SpatialNeckCylinderModel
      (Subtype.val : spatialNeckBuffer epsilon → SpatialNeckCylinder) (ρ x) :=
    (contMDiff_subtype_val (I := SpatialNeckCylinderModel) (n := ∞)).mdifferentiableAt (by decide)
  have hρ := ρ.contMDiff.mdifferentiableAt (x := x) (by decide)
  have hψ := ψ.contMDiff.mdifferentiableAt (x := x.val) (by decide)
  have hchain : mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel
      (ψ ∘ (Subtype.val : spatialNeckBuffer epsilon → SpatialNeckCylinder)) x =
      (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel
        (Subtype.val : spatialNeckBuffer epsilon → SpatialNeckCylinder) (ρ x)).comp
        (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel ρ x) :=
    mfderiv_comp x hvρ hρ
  rw [mfderiv_comp x hψ hv, mfderiv_subtype_val, mfderiv_subtype_val] at hchain
  have hvalue := congrArg
    (fun L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ) => L V)
    hchain
  change mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel ψ x.val V =
    mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel ρ x V at hvalue
  have hscale := cylinderAxialScale_mfderiv (-1) (by norm_num) x.val V
  change (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel ψ x.val V :
    EuclideanSpace ℝ (Fin 2) × ℝ) = (V.1, -1 * V.2) at hscale
  simp only [neg_one_mul] at hscale
  exact hvalue.symm.trans hscale


theorem spatialNeckReflection_pullback_reference (epsilon : ℝ) :
    DifferentialGeometry.Diffeomorph.pullbackMetric
      (unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon))
      (spatialNeckReflection epsilon) =
      unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  let ρ := spatialNeckReflection epsilon
  have hpull := DifferentialGeometry.Diffeomorph.pullbackMetric_inner
    (unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon)) ρ x v w
  have hrestrict := SmoothRiemannianMetric.restrictOpen_inner unitCylinderMetric
    (spatialNeckBuffer epsilon) (ρ x)
    (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel ρ x v)
    (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel ρ x w)
  have hd := congrArg₂
    (fun V Z : EuclideanSpace ℝ (Fin 2) × ℝ => unitCylinderMetric.inner (ρ x).val V Z)
    (spatialNeckReflection_mfderiv epsilon x v) (spatialNeckReflection_mfderiv epsilon x w)
  have hpoint := congrArg
    (fun q : SpatialNeckCylinder => unitCylinderMetric.inner q (v.1, -v.2) (w.1, -w.2))
    (spatialNeckReflection_val epsilon x)
  have hneg := unitCylinderMetric_inner x.val.1 (-x.val.2) v.1 w.1 (-v.2) (-w.2)
  simp only [neg_mul_neg] at hneg
  have hpos := unitCylinderMetric_inner x.val.1 x.val.2 v.1 w.1 v.2 w.2
  have hright := SmoothRiemannianMetric.restrictOpen_inner unitCylinderMetric
    (spatialNeckBuffer epsilon) x v w
  exact (((hpull.trans hrestrict).trans hd).trans hpoint).trans
    ((hneg.trans hpos.symm).trans hright.symm)


theorem spatialNeckReflection_metricDerivNormSupOn (epsilon : ℝ) (p : ℕ)
    (g : SmoothRiemannianMetric SpatialNeckCylinderModel (spatialNeckBuffer epsilon)) :
    let gRef := unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon)
    metricDerivNormSupOn (I := SpatialNeckCylinderModel) (spatialNeckClosedCore epsilon) p
      (DifferentialGeometry.Diffeomorph.pullbackMetric g (spatialNeckReflection epsilon))
      gRef gRef =
      metricDerivNormSupOn (I := SpatialNeckCylinderModel) (spatialNeckClosedCore epsilon) p
        g gRef gRef := by
  have : IsManifold SpatialNeckCylinderModel 1 (spatialNeckBuffer epsilon) :=
    IsManifold.of_le (n := ∞) (by decide)
  have : IsManifold SpatialNeckCylinderModel 2 (spatialNeckBuffer epsilon) :=
    IsManifold.of_le (n := ∞) (by decide)
  have : IsManifold SpatialNeckCylinderModel ((∞ : WithTop ℕ∞) + 1)
      (spatialNeckBuffer epsilon) := by
    change IsManifold SpatialNeckCylinderModel ∞ (spatialNeckBuffer epsilon)
    infer_instance
  have hnorm := metricDerivNormSupOn_pullback_image (I := SpatialNeckCylinderModel)
    (spatialNeckClosedCore epsilon) p g
    (unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon))
    (unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon))
    (spatialNeckReflection epsilon)
  simp only [spatialNeckReflection_pullback_reference, spatialNeckReflection_image_core] at hnorm
  exact hnorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

namespace SpatialNeckWitness

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)

def reflect : SpatialNeckWitness h yStar p epsilon where
  dimension_three := W.dimension_three
  complete := W.complete
  epsilon_pos := W.epsilon_pos
  scalar_pos := W.scalar_pos
  embedding := W.embedding.comp ⟨spatialNeckReflection epsilon,
    (spatialNeckReflection epsilon).continuous⟩
  smooth_embedding := by
    have hW : IsLocalDiffeomorph SpatialNeckCylinderModel I ∞ W.embedding := fun x =>
      immersionAt_isLocalDiffeomorphAt_of_finrank_eq
        (by simpa [Module.finrank_prod] using W.dimension_three.symm)
        (W.smooth_embedding.isImmersion.isImmersionAt x)
    apply localDiffeomorph_isSmoothEmbedding_of_injective
    · intro x
      exact ((spatialNeckReflection epsilon).isLocalDiffeomorph x).comp (K := I) N
        (hW (spatialNeckReflection epsilon x))
    · exact W.smooth_embedding.isEmbedding.injective.comp
        (spatialNeckReflection epsilon).injective
  marked := by
    change W.embedding (spatialNeckReflection epsilon
      (spatialNeckCentralPoint epsilon W.epsilon_pos yStar)) = p
    rw [spatialNeckReflection_central]
    exact W.marked
  normalizedMetric := DifferentialGeometry.Diffeomorph.pullbackMetric
    W.normalizedMetric (spatialNeckReflection epsilon)
  normalized_inner := by
    intro x v w
    rw [DifferentialGeometry.Diffeomorph.pullbackMetric_inner, W.normalized_inner]
    have hd := mfderiv_comp x
      (W.smooth_embedding.contMDiff.mdifferentiableAt (by decide))
      ((spatialNeckReflection epsilon).contMDiff.mdifferentiableAt (by decide))
    have hv := congrArg (fun L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] E => L v) hd
    have hw := congrArg (fun L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] E => L w) hd
    change _ = ((spatialNeckScale h p) ^ 2)⁻¹ *
      h.inner (W.embedding (spatialNeckReflection epsilon x))
        (mfderiv SpatialNeckCylinderModel I (W.embedding ∘ spatialNeckReflection epsilon) x v)
        (mfderiv SpatialNeckCylinderModel I (W.embedding ∘ spatialNeckReflection epsilon) x w)
    exact congrArg (fun z : ℝ => ((spatialNeckScale h p) ^ 2)⁻¹ * z)
      (congrArg₂ (fun V Z : E =>
        h.inner (W.embedding (spatialNeckReflection epsilon x)) V Z) hv hw).symm
  closeness := by
    rw [spatialNeckReflection_metricDerivNormSupOn]
    exact W.closeness

@[simp] theorem reflect_embedding (x : spatialNeckBuffer epsilon) :
    W.reflect.embedding x = W.embedding (spatialNeckReflection epsilon x) := rfl

@[simp] theorem reflect_centralMap (y : SpatialNeckSphere) :
    W.reflect.centralMap y = W.centralMap y := by
  change W.embedding (spatialNeckReflection epsilon
    (spatialNeckCentralPoint epsilon W.epsilon_pos y)) = W.centralMap y
  rw [spatialNeckReflection_central]
  rfl

@[simp] theorem reflect_centralSphere : W.reflect.centralSphere = W.centralSphere := by
  rw [W.reflect.centralSphere_eq_range, W.centralSphere_eq_range]
  congr 1
  funext y
  exact W.reflect_centralMap y

@[simp] theorem reflect_core : W.reflect.core = W.core := by
  change (W.embedding ∘ spatialNeckReflection epsilon) '' spatialNeckClosedCore epsilon = _
  calc
    _ = W.embedding '' (spatialNeckReflection epsilon '' spatialNeckClosedCore epsilon) :=
      (Set.image_image W.embedding (spatialNeckReflection epsilon) _).symm
    _ = W.core := congrArg (fun K => W.embedding '' K) (spatialNeckReflection_image_core epsilon)

@[simp] theorem reflect_image : W.reflect.image = W.image := by
  ext q
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨spatialNeckReflection epsilon x, hx⟩
  · rintro ⟨x, rfl⟩
    refine ⟨spatialNeckReflection epsilon x, ?_⟩
    rw [W.reflect_embedding, spatialNeckReflection_involutive]

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

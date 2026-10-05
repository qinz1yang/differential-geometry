import DifferentialGeometry.Geometry.Neck.Normalized.Defs
import DifferentialGeometry.Geometry.Curvature.RoundCylinder
import DifferentialGeometry.Topology.Manifold.SigmaCompact

noncomputable section

section

open Set Bundle Manifold Function
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩
private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1) :=
  ⟨by simp⟩
private local instance : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) := ⟨by simp⟩
private local instance (O : TopologicalSpace.Opens NeckCylinder) : SigmaCompactSpace O :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen NeckCylinderModel O.isOpen)

theorem roundCylinderMetric_eq_geometry :
    roundCylinderMetric = (Geometry.Metric.roundCylinderMetric (E := ThreeSpace) (n := 2)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x V W
  have hkey : ∀ (V : TangentSpace NeckCylinderModel x),
      mfderiv NeckCylinderModel ThreeModel
          (fun p : NeckCylinder => (p.1.1 : ThreeSpace)) x V
        = dIncl (E := ThreeSpace) (n := 2) x.1 V.1 := by
    intro V
    have hcomp : (fun p : NeckCylinder => (p.1.1 : ThreeSpace)) =
        ((↑) : Sphere 2 → ThreeSpace) ∘ Prod.fst := by
      rw [← Function.comp_def]
    rw [hcomp]
    rw [mfderiv_comp x
      ((contMDiff_coe_sphere (E := ThreeSpace) (n := 2) (m := ∞)).contMDiffAt.mdifferentiableAt
        (by simp))
      (mdifferentiableAt_fst (x := x))]
    rw [mfderiv_fst]
    rfl
  have hsnd : ∀ (V : TangentSpace NeckCylinderModel x),
      mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) Prod.snd x V = V.2 := by
    intro V
    rw [mfderiv_snd]
    rfl
  have h := (Classical.choose_spec
    (exists_unique_shrinkingCylinderMetric (⟨0, by norm_num⟩ : Iio (1 : ℝ)))).1 x V W
  rw [roundCylinderMetric, shrinkingCylinderMetric]
  rw [h, shrinkingCylinderInner, hkey V, hkey W, hsnd V, hsnd W]
  rw [Geometry.Metric.roundCylinderMetric_inner]
  norm_num
  rfl

theorem isCompact_neckClosedTest (δ : ℝ) : IsCompact (neckClosedTest δ) := by
  rw [Topology.IsEmbedding.isCompact_iff
    (Topology.IsEmbedding.subtypeVal (p := fun q => q ∈ neckBuffer δ))]
  have himg : (Subtype.val '' neckClosedTest δ : Set NeckCylinder) =
      (Set.univ : Set (Sphere 2)) ×ˢ Icc (-δ⁻¹) δ⁻¹ := by
    ext q
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Set.mem_univ _, hy⟩
    · rintro ⟨-, hq⟩
      refine ⟨⟨q, ?_⟩, hq, rfl⟩
      change -δ⁻¹ - 1 < q.2 ∧ q.2 < δ⁻¹ + 1
      constructor <;> linarith [hq.1, hq.2]
  rw [himg]
  exact isCompact_univ.prod isCompact_Icc

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false

open Bundle Manifold Set Function Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem metricScalarAt_roundCylinderMetric_eq_one (x : NeckCylinder) :
    metricScalarAt roundCylinderMetric x = 1 := by
  let : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩
  rw [roundCylinderMetric_eq_geometry]
  rw [metricScalarAt_roundCylinder (E := ThreeSpace) (n := 2)]
  norm_num

theorem exists_center_scalar_inv_sq_roundCylinder :
    ∃ h : ℝ, 0 < h ∧ ∀ x : NeckCylinder, metricScalarAt roundCylinderMetric x = (h ^ 2)⁻¹ :=
  ⟨1, by norm_num, fun x => by rw [metricScalarAt_roundCylinderMetric_eq_one]; norm_num⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

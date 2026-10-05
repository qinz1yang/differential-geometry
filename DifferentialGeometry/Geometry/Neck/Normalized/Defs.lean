import DifferentialGeometry.Topology.ThreeManifold.Model
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Metric.Cylinder
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Geometry.Metric.Convergence.Defs
import DifferentialGeometry.Geometry.Metric.Scaling
import Mathlib.Geometry.Manifold.SmoothEmbedding

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology InnerProductSpace NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

abbrev NeckCylinder := Sphere 2 × ℝ
abbrev NeckCylinderModel := (𝓡 2).prod 𝓘(ℝ, ℝ)

def shrinkingCylinderInner (v : Iio (1 : ℝ)) (x : NeckCylinder)
    (V W : TangentSpace NeckCylinderModel x) : ℝ :=
  2 * (1 - v.1) *
      ⟪mfderiv NeckCylinderModel ThreeModel (fun p : NeckCylinder => p.1.1) x V,
        mfderiv NeckCylinderModel ThreeModel (fun p : NeckCylinder => p.1.1) x W⟫_ℝ +
    ((fun (r s : ℝ) => r * s) : ℝ → ℝ → ℝ)
      (mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) Prod.snd x V)
      (mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) Prod.snd x W)

theorem exists_unique_shrinkingCylinderMetric (v : Iio (1 : ℝ)) :
    ∃! g : SmoothRiemannianMetric NeckCylinderModel NeckCylinder,
      ∀ x V W, g.inner x V W = shrinkingCylinderInner v x V W := by
  have key : ∀ (x : NeckCylinder) (V : TangentSpace NeckCylinderModel x),
      mfderiv NeckCylinderModel ThreeModel (fun p : NeckCylinder => (p.1.1 : ThreeSpace)) x V
        = DifferentialGeometry.Geometry.dIncl (E := ThreeSpace) (n := 2) x.1 V.1 := by
    intro x V
    rw [show (fun p : NeckCylinder => (p.1.1 : ThreeSpace)) =
        ((↑) : Sphere 2 → ThreeSpace) ∘ Prod.fst from rfl]
    rw [mfderiv_comp x
      ((contMDiff_coe_sphere (E := ThreeSpace) (n := 2) (m := ∞)).contMDiffAt.mdifferentiableAt
        (by simp))
      (mdifferentiableAt_fst (x := x))]
    rw [mfderiv_fst]
    rfl
  have hpos : 0 < 2 * (1 - v.1) := by
    have hv : (v.1 : ℝ) < 1 := v.2
    linarith
  let g : SmoothRiemannianMetric NeckCylinderModel NeckCylinder :=
    DifferentialGeometry.Geometry.Metric.cylinderMetric
      (scaleMetric (2 * (1 - v.1)) hpos
        (DifferentialGeometry.Geometry.roundMetric (E := ThreeSpace) (n := 2)))
  have hg : ∀ x V W, g.inner x V W = shrinkingCylinderInner v x V W := by
    intro x V W
    have hsndV : mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) Prod.snd x V = V.2 := by
      rw [mfderiv_snd]
      rfl
    have hsndW : mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) Prod.snd x W = W.2 := by
      rw [mfderiv_snd]
      rfl
    have hround : (DifferentialGeometry.Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner x.1 V.1 W.1 =
        ⟪DifferentialGeometry.Geometry.dIncl (E := ThreeSpace) (n := 2) x.1 V.1,
          DifferentialGeometry.Geometry.dIncl (E := ThreeSpace) (n := 2) x.1 W.1⟫_ℝ :=
      DifferentialGeometry.Geometry.roundMetric_inner (E := ThreeSpace) (n := 2) x.1 V.1 W.1
    have hcyl : g.inner x V W =
        2 * (1 - v.1) *
            (DifferentialGeometry.Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner x.1 V.1 W.1 +
          V.2 * W.2 := by
      simp only [g]
      rw [DifferentialGeometry.Geometry.Metric.cylinderMetric_inner]
      rw [DifferentialGeometry.scaleMetric_inner (I := 𝓡 2) (2 * (1 - v.1)) hpos
        (DifferentialGeometry.Geometry.roundMetric (E := ThreeSpace) (n := 2)) x.1 V.1 W.1]
    have hshrink : shrinkingCylinderInner v x V W =
        2 * (1 - v.1) *
            (DifferentialGeometry.Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner x.1 V.1 W.1 +
          V.2 * W.2 := by
      rw [shrinkingCylinderInner, key x V, key x W, hsndV, hsndW]
      exact (congrArg (fun t : ℝ => 2 * (1 - v.1) * t + V.2 * W.2) hround).symm
    rw [hcyl, hshrink]
  exact ⟨g, hg, fun g' hg' =>
    SmoothRiemannianMetric.ext_inner fun x v w => (hg' x v w).trans (hg x v w).symm⟩

def shrinkingCylinderMetric (v : Iio (1 : ℝ)) :
    SmoothRiemannianMetric NeckCylinderModel NeckCylinder :=
  Classical.choose (exists_unique_shrinkingCylinderMetric v)

def roundCylinderMetric : SmoothRiemannianMetric NeckCylinderModel NeckCylinder :=
  shrinkingCylinderMetric ⟨0, by norm_num⟩


def neckBuffer (δ : ℝ) : TopologicalSpace.Opens NeckCylinder :=
  ⟨{x | -δ⁻¹ - 1 < x.2 ∧ x.2 < δ⁻¹ + 1},
    (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)⟩

def neckClosedTest (δ : ℝ) : Set (neckBuffer δ) :=
  {x | -δ⁻¹ ≤ x.1.2 ∧ x.1.2 ≤ δ⁻¹}

def neckCentralDomain (δ : ℝ) : Set (neckBuffer δ) :=
  {x | -δ⁻¹ < x.1.2 ∧ x.1.2 < δ⁻¹}

abbrev neckRetainedCollar (δ : ℝ) := {x : NeckCylinder // 0 ≤ x.2 ∧ x.2 < δ⁻¹}

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

structure NormalizedNeck (h : SmoothRiemannianMetric ThreeModel M) (δ : ℝ) (k : ℕ) where
  delta_pos : 0 < δ
  delta_lt_one : δ < 1
  sphereMark : Sphere 2
  center : M
  chart : C(neckBuffer δ, M)
  chart_smooth : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ chart
  marked : chart ⟨(sphereMark, 0), by
    have := inv_pos.mpr delta_pos
    constructor <;> linarith⟩ = center
  scale : ℝ
  scale_pos : 0 < scale
  scale_scalar : scale = metricScalarAt h center
  normalizedMetric : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ)
  normalized_inner : ∀ x V W,
    normalizedMetric.inner x V W = scale * h.inner (chart x)
      (mfderiv NeckCylinderModel ThreeModel chart x V)
      (mfderiv NeckCylinderModel ThreeModel chart x W)
  closeness : metricDerivNormSupOn (neckClosedTest δ) k normalizedMetric
    (roundCylinderMetric.restrictOpen (neckBuffer δ))
    (roundCylinderMetric.restrictOpen (neckBuffer δ)) < δ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

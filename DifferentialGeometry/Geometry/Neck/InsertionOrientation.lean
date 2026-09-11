import DifferentialGeometry.Geometry.Neck.Orientation
import DifferentialGeometry.Geometry.Neck.InsertionChart
import DifferentialGeometry.Geometry.Neck.Scaling
import DifferentialGeometry.Geometry.Neck.Naturality

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace DifferentialGeometry
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Neck
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

def controlledOrientation (B σ : ℝ) (hσ : σ ^ 2 = 1) : openCylinder B → openCylinder B :=
  fun q => ⟨(q.val.1, σ * q.val.2), by
    change -B < σ * q.val.2 ∧ σ * q.val.2 < B
    have hq : -B < q.val.2 ∧ q.val.2 < B := q.property
    rcases sq_eq_one_iff.mp hσ with rfl | rfl
    · simpa using hq
    · constructor <;> linarith [hq.1, hq.2]⟩

theorem controlledOrientation_involutive (B σ : ℝ) (hσ : σ ^ 2 = 1) :
    Involutive (controlledOrientation B σ hσ) := by
  intro q
  apply Subtype.ext
  change (q.val.1, σ * (σ * q.val.2)) = (q.val.1, q.val.2)
  congr 1
  calc
    _ = σ ^ 2 * q.val.2 := by ring
    _ = q.val.2 := by rw [hσ, one_mul]

private theorem controlledOrientation_buffered (δ σ : ℝ) (hσ : σ ^ 2 = 1)
    (q : openCylinder δ⁻¹) :
    Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ) (controlledOrientation δ⁻¹ σ hσ q) =
      bufferedCylinderOrientation δ σ hσ (Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ) q) := by
  apply Subtype.ext
  rw [bufferedCylinderOrientation_apply]
  rfl

namespace normalizedDatum
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem oriented_controlledMap (d : normalizedDatum g x₀ δ k) (q : openCylinder δ⁻¹) :
    d.oriented.controlledMap q =
      d.controlledMap (controlledOrientation δ⁻¹ d.retainedSign d.retainedSign_sq q) := by
  rw [controlledMap_apply, oriented_map, controlledMap_apply, controlledOrientation_buffered]

theorem oriented_controlledImage (d : normalizedDatum g x₀ δ k) :
    d.oriented.controlledImage = d.controlledImage := by
  apply Opens.ext
  change range d.oriented.controlledMap = range d.controlledMap
  have he : d.oriented.controlledMap =
      d.controlledMap ∘ controlledOrientation δ⁻¹ d.retainedSign d.retainedSign_sq :=
    funext d.oriented_controlledMap
  rw [he]
  exact (controlledOrientation_involutive δ⁻¹ d.retainedSign d.retainedSign_sq).surjective.range_comp _

theorem oriented_rescaled (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    (d.rescaled c hc).oriented = d.oriented.rescaled c hc := rfl

end normalizedDatum
namespace datumIsometry
variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [Fact (Module.finrank ℝ E' = 3)]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  {g : SmoothRiemannianMetric I M} {g' : SmoothRiemannianMetric J N}
  {x₀ : M} {x₀' : N} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k} {d' : normalizedDatum g' x₀' δ k}

def oriented (F : datumIsometry d d') : datumIsometry d.oriented d'.oriented where
  source := F.source
  target := F.target
  image_source := fun q => F.image_source (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq q)
  image_target := fun q => F.image_target (bufferedCylinderOrientation δ d'.retainedSign d'.retainedSign_sq q)
  equiv := F.equiv
  metric_eq := F.metric_eq
  chart_eq := by
    intro q
    have hσ : d'.retainedSign = d.retainedSign := by
      simp only [normalizedDatum.retainedSign, F.retainedSide_eq]
    have hz : bufferedCylinderOrientation δ d'.retainedSign d'.retainedSign_sq q =
        bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq q := by
      apply Subtype.ext
      simp only [bufferedCylinderOrientation_apply, hσ]
    exact (F.chart_eq (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq q)).trans
      (congrArg d'.map hz.symm)
  scalar_eq := F.scalar_eq
  retainedSide_eq := rfl

theorem oriented_equiv (F : datumIsometry d d') : F.oriented.equiv = F.equiv := rfl
end datumIsometry
end DifferentialGeometry.Geometry.Neck

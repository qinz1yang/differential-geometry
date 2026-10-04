import DifferentialGeometry.Topology.Manifold.RegularLevel.BoundarySublevel
import DifferentialGeometry.Topology.Manifold.RegularLevel.RegularSublevelSlice

/-!
# Consumers of the half-space slice construction

* (codimension zero, ambient with boundary) the slab `{0 ≤ x₀ ≤ 1}` inside the half-plane
  `ℍ²`, as a sublevel of the first coordinate: a manifold with boundary whose boundary is
  `{x₀ = 0} ∪ {x₀ = 1}`;
* (positive codimension, boundaryless ambient) the half-line `{x₁ = 0, 0 ≤ x₀}` inside `ℝ²`,
  with boundary the origin.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.RegularLevel.Examples

open DifferentialGeometry.Topology.Manifold

/-- The first coordinate on the half-plane. -/
def halfPlaneHeight (w : EuclideanHalfSpace 2) : ℝ := w.1 0

theorem contMDiff_halfPlaneHeight : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞ halfPlaneHeight :=
  ((EuclideanSpace.proj (0 : Fin 2)).contMDiff).comp (𝓡∂ 2).contMDiff

theorem mfderiv_halfPlaneHeight_ne_zero (w : EuclideanHalfSpace 2) :
    mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) halfPlaneHeight w ≠ 0 := by
  let p : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 2)
  have hp : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) p ((𝓡∂ 2) w) :=
    (p.contMDiff (n := ∞)).contMDiffAt.mdifferentiableAt (by simp)
  have hI : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡∂ 2) w :=
    ((𝓡∂ 2).contMDiff (n := ∞)).contMDiffAt.mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp w hp hI
  have hext : mfderiv (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡∂ 2) w =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) :=
    mfderiv_extChartAt_self (I := 𝓡∂ 2) (x := w)
  intro h0
  have hval := congrArg (fun L => L (EuclideanSpace.single 0 1)) h0
  change mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) (p ∘ (𝓡∂ 2)) w (EuclideanSpace.single 0 1) = 0 at hval
  rw [hcomp, hext, mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hval
  change p (EuclideanSpace.single 0 1) = 0 at hval
  simp [p] at hval

theorem isInteriorPoint_of_halfPlaneHeight_eq_one {w : EuclideanHalfSpace 2}
    (hw : halfPlaneHeight w = 1) : (𝓡∂ 2).IsInteriorPoint w := by
  change extChartAt (𝓡∂ 2) w w ∈ interior (range (𝓡∂ 2))
  rw [interior_range_modelWithCornersEuclideanHalfSpace]
  change 0 < w.1 0
  change w.1 0 = 1 at hw
  rw [hw]
  exact one_pos

/-- The slab `{0 ≤ x₀ ≤ 1} ⊆ ℍ²` is a manifold with boundary `{x₀ = 0} ∪ {x₀ = 1}`, with smooth
inclusion of bijective differential. -/
theorem slab_isManifold :
    ∃ cs : ChartedSpace (EuclideanHalfSpace 2) {w : EuclideanHalfSpace 2 // halfPlaneHeight w ≤ 1},
      letI := cs
      IsManifold (𝓡∂ 2) ∞ {w : EuclideanHalfSpace 2 // halfPlaneHeight w ≤ 1} ∧
      ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ (fun w : {w : EuclideanHalfSpace 2 // halfPlaneHeight w ≤ 1} => w.1) ∧
      (∀ w : {w : EuclideanHalfSpace 2 // halfPlaneHeight w ≤ 1},
        (𝓡∂ 2).IsBoundaryPoint w ↔ (halfPlaneHeight w.1 = 0 ∨ halfPlaneHeight w.1 = 1)) := by
  obtain ⟨cs, hM, hval, -, hbd⟩ := exists_isManifold_sublevel_of_boundary (m := 1)
    halfPlaneHeight 1 contMDiff_halfPlaneHeight (fun w _ => mfderiv_halfPlaneHeight_ne_zero w)
    (fun w hw => isInteriorPoint_of_halfPlaneHeight_eq_one hw)
  refine ⟨cs, hM, hval, fun w => (hbd w).trans ?_⟩
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_range_modelWithCornersEuclideanHalfSpace]
  change (0 = w.1.1 0 ∨ halfPlaneHeight w.1 = 1) ↔ (w.1.1 0 = 0 ∨ halfPlaneHeight w.1 = 1)
  rw [eq_comm]

/-- The half-line `{x₁ = 0, 0 ≤ x₀} ⊆ ℝ²` is a manifold with boundary `{x₀ = 0}`, through the
regular-sublevel structure. -/
theorem halfLine_regularSublevel :
    let Ψ : EuclideanSpace ℝ (Fin 2) → ℝ := EuclideanSpace.proj (1 : Fin 2)
    let B : EuclideanSpace ℝ (Fin 2) → ℝ := EuclideanSpace.proj (0 : Fin 2)
    ∃ cs : ChartedSpace (EuclideanHalfSpace (0 + 1)) {x : EuclideanSpace ℝ (Fin 2) // Ψ x = 0 ∧ 0 ≤ B x},
      letI := cs
      IsManifold (𝓡∂ (0 + 1)) ∞ {x : EuclideanSpace ℝ (Fin 2) // Ψ x = 0 ∧ 0 ≤ B x} ∧
      ContMDiff (𝓡∂ (0 + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (Subtype.val : {x : EuclideanSpace ℝ (Fin 2) // Ψ x = 0 ∧ 0 ≤ B x} → _) ∧
      (∀ x : {x : EuclideanSpace ℝ (Fin 2) // Ψ x = 0 ∧ 0 ≤ B x},
        (𝓡∂ (0 + 1)).IsBoundaryPoint x ↔ B x = 0) := by
  intro Ψ B
  let p₁ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj (1 : Fin 2)
  let p₀ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 2)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 0 + 1 + Module.finrank ℝ ℝ := by
    simp
  have hΨ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞ Ψ := p₁.contMDiff
  have hB : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞ B := p₀.contMDiff
  have hreg : ∀ x, Ψ x = 0 → 0 ≤ B x →
      Surjective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) Ψ x) := by
    intro x _ _ s
    let t : ℝ := s
    refine ⟨EuclideanSpace.single 1 t, ?_⟩
    change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) p₁ x (EuclideanSpace.single 1 t) = s
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    change (EuclideanSpace.single 1 t : EuclideanSpace ℝ (Fin 2)) 1 = t
    simp
  have hregb : ∀ x, Ψ x = 0 → B x = 0 →
      Surjective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ × ℝ) (fun y => (Ψ y, B y)) x) := by
    intro x _ _ q
    let pq : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ := p₁.prod p₀
    refine ⟨EuclideanSpace.single 1 (q : ℝ × ℝ).1 + EuclideanSpace.single 0 (q : ℝ × ℝ).2, ?_⟩
    change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ × ℝ) pq x
      (EuclideanSpace.single 1 (q : ℝ × ℝ).1 + EuclideanSpace.single 0 (q : ℝ × ℝ).2) = q
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    change pq (EuclideanSpace.single 1 (q : ℝ × ℝ).1 + EuclideanSpace.single 0 (q : ℝ × ℝ).2) = q
    ext <;> simp [pq, p₁, p₀]
  exact ⟨regularSublevelChartedSpace hdim hΨ hB hreg hregb,
    regularSublevel_isManifold hdim hΨ hB hreg hregb,
    regularSublevel_contMDiff_val hdim hΨ hB hreg hregb,
    fun x => regularSublevel_isBoundaryPoint_iff hdim hΨ hB hreg hregb (x := x)⟩

end DifferentialGeometry.Manifold.RegularLevel.Examples

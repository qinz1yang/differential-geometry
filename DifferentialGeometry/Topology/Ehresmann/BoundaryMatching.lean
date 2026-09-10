import DifferentialGeometry.Topology.Ehresmann.BoundaryEndpointTransport
import DifferentialGeometry.Topology.Ehresmann.Interval
import DifferentialGeometry.Topology.Ehresmann.SphereBoundary
import DifferentialGeometry.Topology.Homotopy.Cylinder

noncomputable section
open Set Filter Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Ehresmann

open Poincare.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
  {u : M → ℝ} {a b : ℝ} (hab : a < b) (hu : Continuous u)
  (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)

variable {ES HS S : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES]
  [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
  {IS : ModelWithCorners ℝ ES HS}

set_option backward.isDefEq.respectTransparency false in
theorem exists_prescribed_boundary_matching_of_isotopy :
    let _ : Fact (a < b) := ⟨hab⟩
    let F₀ := boundaryLevel u a b hab.ne hu hboundary
    let F₁ := boundaryLevel u b a hab.ne.symm hu (fun x hx ↦ (hboundary x hx).symm)
    ∀ (Θ : Diffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I (F₀ × Icc a b) M ∞)
      (P : Diffeomorph hI.boundaryI hI.boundaryI F₀ F₁ ∞),
      (∀ p, u (Θ p) = p.2.1) →
      (∀ x, Θ (x, ⟨a, le_rfl, hab.le⟩) = x.1.1) →
      (∀ x, (P x).1.1 = Θ (x, ⟨b, hab.le, le_rfl⟩)) →
    ∀ (η₀ : Diffeomorph IS hI.boundaryI S F₀ ∞)
      (η₁ : Diffeomorph IS hI.boundaryI S F₁ ∞)
      (A Ainv : unitInterval → S → S),
      (∀ t x, Ainv t (A t x) = x) →
      (∀ t x, A t (Ainv t x) = x) →
      ContMDiff (IS.prod (𝓡∂ 1)) IS ∞ (fun p : S × unitInterval ↦ A p.2 p.1) →
      ContMDiff (IS.prod (𝓡∂ 1)) IS ∞ (fun p : S × unitInterval ↦ Ainv p.2 p.1) →
      (∀ x, A 0 x = x) →
      (∀ x, A 1 x = (η₁.trans (η₀.trans P).symm) x) →
    ∃ Ψ : Diffeomorph (IS.prod (𝓡∂ 1)) I (S × unitInterval) M ∞,
      (∀ p, u (Ψ p) = a + (b - a) * p.2.1) ∧
      (∀ x, Ψ (x, 0) = (η₀ x).1.1) ∧
      (∀ x, Ψ (x, 1) = (η₁ x).1.1) ∧
      (∀ t : unitInterval, t.1 ≤ 1 / 3 → ∀ x,
        Ψ (x, t) = Θ (η₀ x, affineIntervalDiffeomorph a b t)) ∧
      ∀ t : unitInterval, 2 / 3 ≤ t.1 → ∀ x,
        Ψ (x, t) = Θ (P.symm (η₁ x), affineIntervalDiffeomorph a b t) := by
  let _ : Fact (a < b) := ⟨hab⟩
  dsimp only
  intro Θ P hh hl hP η₀ η₁ A Ainv hleft hright hA hAinv hzero hone
  let Hprod := unitCylinderDiffeomorphOfProduct a b η₀ Θ
  have hheight (p : S × unitInterval) : u (Hprod p) = a + (b - a) * p.2.1 := by
    rw [unitCylinderDiffeomorphOfProduct_apply, hh, affineIntervalDiffeomorph_apply]
    ring
  have hδ (x : S) : η₀ (A 1 x) = P.symm (η₁ x) := by
    rw [hone]
    exact η₀.apply_symm_apply (P.symm (η₁ x))
  obtain ⟨Ψ, ht, hlow, hhigh⟩ := exists_endpoint_flat_corrected_product
    Hprod A Ainv hleft hright hA hAinv hzero
  refine ⟨Ψ, ?_, ?_, ?_, hlow, ?_⟩
  · intro p
    have he := hheight (Hprod.symm (Ψ p))
    rw [Hprod.apply_symm_apply, ht] at he
    exact he
  · intro x
    rw [hlow 0 (by norm_num)]
    exact (unitCylinderDiffeomorphOfProduct_lower a b η₀ Θ x).trans (hl (η₀ x))
  · intro x
    rw [hhigh 1 (by norm_num)]
    have he := unitCylinderDiffeomorphOfProduct_upper a b η₀ Θ (A 1 x)
    rw [hδ, ← hP, P.apply_symm_apply] at he
    exact he
  · intro t ht x
    rw [hhigh t ht]
    change Θ (η₀ (A 1 x), affineIntervalDiffeomorph a b t) = _
    rw [hδ]

set_option backward.isDefEq.respectTransparency false in
theorem prescribed_boundary_transition_homotopic :
    let _ : Fact (a < b) := ⟨hab⟩
    let F₀ := boundaryLevel u a b hab.ne hu hboundary
    let F₁ := boundaryLevel u b a hab.ne.symm hu (fun x hx ↦ (hboundary x hx).symm)
    ∀ (Θ : Diffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I (F₀ × Icc a b) M ∞)
      (P : Diffeomorph hI.boundaryI hI.boundaryI F₀ F₁ ∞),
      (∀ x, Θ (x, ⟨a, le_rfl, hab.le⟩) = x.1.1) →
      (∀ x, (P x).1.1 = Θ (x, ⟨b, hab.le, le_rfl⟩)) →
    ∀ (η₀ : Diffeomorph IS hI.boundaryI S F₀ ∞)
      (η₁ : Diffeomorph IS hI.boundaryI S F₁ ∞)
      (Ψ : C(S × unitInterval, M)),
      (∀ x, Ψ (x, 0) = (η₀ x).1.1) →
      (∀ x, Ψ (x, 1) = (η₁ x).1.1) →
      ContinuousMap.Homotopic (ContinuousMap.id S)
        ⟨η₁.trans (η₀.trans P).symm, (η₁.trans (η₀.trans P).symm).continuous⟩ := by
  let _ : Fact (a < b) := ⟨hab⟩
  dsimp only
  intro Θ P hl hP η₀ η₁ Ψ hzero hone
  let Hprod := unitCylinderDiffeomorphOfProduct a b η₀ Θ
  refine ⟨Poincare.Topology.Homotopy.productBoundaryHomotopy Hprod.toHomeomorph _ Ψ ?_ ?_⟩
  · intro x
    change Ψ (x, 0) = Hprod (x, 0)
    exact (hzero x).trans ((unitCylinderDiffeomorphOfProduct_lower a b η₀ Θ x).trans
      (hl (η₀ x))).symm
  · intro x
    change Ψ (x, 1) = Hprod ((η₁.trans (η₀.trans P).symm) x, 1)
    have hδ : η₀ ((η₁.trans (η₀.trans P).symm) x) = P.symm (η₁ x) :=
      η₀.apply_symm_apply (P.symm (η₁ x))
    have he := unitCylinderDiffeomorphOfProduct_upper a b η₀ Θ
      ((η₁.trans (η₀.trans P).symm) x)
    rw [hδ, ← hP, P.apply_symm_apply] at he
    exact (hone x).trans he.symm

end Poincare.Topology.Ehresmann

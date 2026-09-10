import DifferentialGeometry.Topology.Ehresmann.BoundaryMatching
import DifferentialGeometry.Topology.Manifold.SphereCylinderDegree

noncomputable section
open Set Metric Manifold
open scoped ContDiff

namespace Poincare.Topology.Ehresmann

open Poincare.Geometry.Boundary Poincare.Topology.Manifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem exists_prescribed_sphere_boundary_matching_of_degree_one
    {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    {u : M → ℝ} {a b : ℝ} (hab : a < b) (hu : Continuous u)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b) :
    let _ : Fact (a < b) := ⟨hab⟩
    let F₀ := boundaryLevel u a b hab.ne hu hboundary
    let F₁ := boundaryLevel u b a hab.ne.symm hu (fun x hx ↦ (hboundary x hx).symm)
    ∀ (Θ : Diffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I (F₀ × Icc a b) M ∞)
      (P : Diffeomorph hI.boundaryI hI.boundaryI F₀ F₁ ∞),
      (∀ p, u (Θ p) = p.2.1) →
      (∀ x, Θ (x, ⟨a, le_rfl, hab.le⟩) = x.1.1) →
      (∀ x, (P x).1.1 = Θ (x, ⟨b, hab.le, le_rfl⟩)) →
    ∀ (η₀ : Diffeomorph (𝓡 2) hI.boundaryI
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) F₀ ∞)
      (η₁ : Diffeomorph (𝓡 2) hI.boundaryI
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) F₁ ∞),
      sphereDiffeomorphDegree (η₁.trans (η₀.trans P).symm) = 1 →
    ∃ Ψ : Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × unitInterval) M ∞,
      (∀ p, u (Ψ p) = a + (b - a) * p.2.1) ∧
      (∀ x, Ψ (x, 0) = (η₀ x).1.1) ∧
      (∀ x, Ψ (x, 1) = (η₁ x).1.1) ∧
      (∀ t : unitInterval, t.1 ≤ 1 / 3 → ∀ x,
        Ψ (x, t) = Θ (η₀ x, affineIntervalDiffeomorph a b t)) ∧
      ∀ t : unitInterval, 2 / 3 ≤ t.1 → ∀ x,
        Ψ (x, t) = Θ (P.symm (η₁ x), affineIntervalDiffeomorph a b t) := by
  let _ : Fact (a < b) := ⟨hab⟩
  dsimp only
  intro Θ P hh hl hP η₀ η₁ hdegree
  let δ := η₁.trans (η₀.trans P).symm
  obtain ⟨J, hJ, hJi, hJ0, hJ1⟩ := (sphereDiffeomorphDegree_eq_one_iff_isotopy δ).mp hdegree
  let A (t : unitInterval) := J (1 - t.1)
  let Ainv (t : unitInterval) := (J (1 - t.1)).symm
  have ht : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ) ∞
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × unitInterval ↦ 1 - q.2.1) :=
    contMDiff_const.sub (contMDiff_subtypeVal_Icc.comp contMDiff_snd)
  have hA : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 2) ∞
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × unitInterval ↦ A q.2 q.1) :=
    hJ.comp (ht.prodMk contMDiff_fst)
  have hAi : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 2) ∞
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × unitInterval ↦ Ainv q.2 q.1) :=
    hJi.comp (ht.prodMk contMDiff_fst)
  apply exists_prescribed_boundary_matching_of_isotopy hab hu hboundary Θ P hh hl hP η₀ η₁
    (fun t x ↦ A t x) (fun t x ↦ Ainv t x)
    (fun t x ↦ (J (1 - t.1)).symm_apply_apply x)
    (fun t x ↦ (J (1 - t.1)).apply_symm_apply x) hA hAi
  · intro x
    change J (1 - 0) x = x
    rw [sub_zero, hJ1]
    rfl
  · intro x
    change J (1 - 1) x = δ x
    rw [sub_self, hJ0]

theorem boundary_transition_degree_one_of_prescribed_sphere_matching
    {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    {u : M → ℝ} {a b : ℝ} (hab : a < b) (hu : Continuous u)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b) :
    let _ : Fact (a < b) := ⟨hab⟩
    let F₀ := boundaryLevel u a b hab.ne hu hboundary
    let F₁ := boundaryLevel u b a hab.ne.symm hu (fun x hx ↦ (hboundary x hx).symm)
    ∀ (Θ : Diffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I (F₀ × Icc a b) M ∞)
      (P : Diffeomorph hI.boundaryI hI.boundaryI F₀ F₁ ∞),
      (∀ x, Θ (x, ⟨a, le_rfl, hab.le⟩) = x.1.1) →
      (∀ x, (P x).1.1 = Θ (x, ⟨b, hab.le, le_rfl⟩)) →
    ∀ (η₀ : Diffeomorph (𝓡 2) hI.boundaryI
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) F₀ ∞)
      (η₁ : Diffeomorph (𝓡 2) hI.boundaryI
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) F₁ ∞)
      (Ψ : Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × unitInterval) M ∞),
      (∀ x, Ψ (x, 0) = (η₀ x).1.1) →
      (∀ x, Ψ (x, 1) = (η₁ x).1.1) →
      sphereDiffeomorphDegree (η₁.trans (η₀.trans P).symm) = 1 := by
  let _ : Fact (a < b) := ⟨hab⟩
  dsimp only
  intro Θ P hl hP η₀ η₁ Ψ hzero hone
  let Hprod := unitCylinderDiffeomorphOfProduct a b η₀ Θ
  let δ := η₁.trans (η₀.trans P).symm
  let C := Ψ.trans Hprod.symm
  have h₀ : ∀ x, C (x, 0) = ((Diffeomorph.refl (𝓡 2) _ ∞) x, 0) := by
    intro x
    change Hprod.symm (Ψ (x, 0)) = (x, 0)
    apply Hprod.injective
    change Hprod (Hprod.symm (Ψ (x, 0))) = Hprod (x, 0)
    rw [Hprod.apply_symm_apply, hzero]
    exact ((unitCylinderDiffeomorphOfProduct_lower a b η₀ Θ x).trans (hl (η₀ x))).symm
  have h₁ : ∀ x, C (x, 1) = (δ x, 1) := by
    intro x
    change Hprod.symm (Ψ (x, 1)) = (δ x, 1)
    apply Hprod.injective
    change Hprod (Hprod.symm (Ψ (x, 1))) = Hprod (δ x, 1)
    rw [Hprod.apply_symm_apply, hone]
    have hδ : η₀ (δ x) = P.symm (η₁ x) := η₀.apply_symm_apply (P.symm (η₁ x))
    have he := unitCylinderDiffeomorphOfProduct_upper a b η₀ Θ (δ x)
    rw [hδ, ← hP, P.apply_symm_apply] at he
    exact he.symm
  have hdegree := sphereDiffeomorphDegree_eq_of_cylinder C
    (Diffeomorph.refl (𝓡 2) _ ∞) δ h₀ h₁
  rw [← hdegree, sphereDiffeomorphDegree_eq_sign _
    (⟨EuclideanSpace.single 0 1, by simp⟩ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)]
  have hrad : sphereRadialExtension (Diffeomorph.refl (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞) = id := sphereRadialExtension_id
  rw [hrad, fderiv_id]
  simp

theorem prescribed_sphere_boundary_matching_iff_degree_one
    {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    {u : M → ℝ} {a b : ℝ} (hab : a < b) (hu : Continuous u)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b) :
    let _ : Fact (a < b) := ⟨hab⟩
    let F₀ := boundaryLevel u a b hab.ne hu hboundary
    let F₁ := boundaryLevel u b a hab.ne.symm hu (fun x hx ↦ (hboundary x hx).symm)
    ∀ (Θ : Diffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I (F₀ × Icc a b) M ∞)
      (P : Diffeomorph hI.boundaryI hI.boundaryI F₀ F₁ ∞),
      (∀ p, u (Θ p) = p.2.1) →
      (∀ x, Θ (x, ⟨a, le_rfl, hab.le⟩) = x.1.1) →
      (∀ x, (P x).1.1 = Θ (x, ⟨b, hab.le, le_rfl⟩)) →
    ∀ (η₀ : Diffeomorph (𝓡 2) hI.boundaryI
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) F₀ ∞)
      (η₁ : Diffeomorph (𝓡 2) hI.boundaryI
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) F₁ ∞),
      (∃ Ψ : Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × unitInterval) M ∞,
        (∀ x, Ψ (x, 0) = (η₀ x).1.1) ∧ (∀ x, Ψ (x, 1) = (η₁ x).1.1)) ↔
      sphereDiffeomorphDegree (η₁.trans (η₀.trans P).symm) = 1 := by
  let _ : Fact (a < b) := ⟨hab⟩
  dsimp only
  intro Θ P hh hl hP η₀ η₁
  constructor
  · rintro ⟨Ψ, hzero, hone⟩
    exact boundary_transition_degree_one_of_prescribed_sphere_matching
      hab hu hboundary Θ P hl hP η₀ η₁ Ψ hzero hone
  · intro hdegree
    obtain ⟨Ψ, _, hzero, hone, _, _⟩ :=
      exists_prescribed_sphere_boundary_matching_of_degree_one hab hu hboundary Θ P hh hl hP η₀ η₁ hdegree
    exact ⟨Ψ, hzero, hone⟩

end Poincare.Topology.Ehresmann

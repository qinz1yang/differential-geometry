import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveComponentModels

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open Metric

namespace DifferentialGeometry.Geometry.RoundSphereQuotient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] [NeZero n]

theorem finite_deckGroup (D : RoundSphereQuotient E n) : Finite D.Γ :=
  inferInstance

theorem subsingleton_deckGroup_iff_injective_proj (D : RoundSphereQuotient E n) :
    Subsingleton D.Γ ↔ Function.Injective D.proj := by
  constructor
  · intro h a b hab
    obtain ⟨γ, hγ⟩ := D.proj_eq_imp a b hab
    have hγ1 : γ = 1 := Subsingleton.elim γ 1
    have hρ : D.ρ γ = 1 := by rw [hγ1, map_one]
    have ha : sphereDiffeo (n := n) (D.ρ γ) a = a := by
      rw [hρ]
      apply Subtype.ext
      rw [sphereDiffeo_coe]
      simp
    rw [ha] at hγ
    exact hγ
  · intro h
    have hpos : 0 < Module.finrank ℝ E := by
      have hf : Module.finrank ℝ E = n + 1 := Fact.out
      rw [hf]
      exact Nat.succ_pos n
    let : Nontrivial E := Module.nontrivial_of_finrank_pos hpos
    refine ⟨fun γ γ' => ?_⟩
    obtain ⟨x⟩ : Nonempty (sphere (0 : E) 1) :=
      (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).mpr zero_le_one |>.coe_sort
    have hγx : sphereDiffeo (n := n) (D.ρ γ) x = x := h (D.proj_smul γ x)
    have hγ'x : sphereDiffeo (n := n) (D.ρ γ') x = x := h (D.proj_smul γ' x)
    rw [D.action_free γ x hγx, D.action_free γ' x hγ'x]

end DifferentialGeometry.Geometry.RoundSphereQuotient

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology

private instance roundSphereFourFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]

private theorem sphereDiffeo_one_apply (q : Sphere 3) :
    sphereDiffeo (n := 3)
      (1 : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) q = q := by
  apply Subtype.ext
  rw [sphereDiffeo_coe]
  simp

noncomputable def trivialRoundSphereQuotientSphereThree :
    RoundSphereQuotient (EuclideanSpace ℝ (Fin 4)) 3 where
  Q := Sphere 3
  Γ := PUnit
  ρ := 1
  action_free := fun γ _ _ => Subsingleton.elim γ 1
  proj := id
  proj_smooth := contMDiff_id
  proj_smul := fun γ q => by
    have hγ : γ = 1 := Subsingleton.elim γ 1
    subst hγ
    simp only [map_one, id_eq]
    rw [sphereDiffeo_one_apply]
  proj_eq_imp := fun q₁ q₂ h => by
    subst h
    exact ⟨1, by simp only [map_one]; exact sphereDiffeo_one_apply q₁⟩
  sectionAt := fun x => LocalSmoothSection.ofLocal (E := EuclideanSpace ℝ (Fin 4)) (n := 3)
    (Q := Sphere 3) (proj := id) Function.surjective_id
    (Diffeomorph.refl (𝓡 3) (Sphere 3) ∞).isLocalDiffeomorph x

noncomputable def sphericalSpaceFormQuotientModelSphereThree :
    SphericalSpaceFormQuotientModel I3 (Sphere 3) where
  quotient := trivialRoundSphereQuotientSphereThree
  equiv := Diffeomorph.refl (𝓡 3) (Sphere 3) ∞

instance instSubsingletonSphericalSpaceFormQuotientModelSphereThreeDeckGroup :
    Subsingleton sphericalSpaceFormQuotientModelSphereThree.quotient.Γ :=
  inferInstanceAs (Subsingleton PUnit)

theorem exists_subsingleton_deckGroup_sphericalSpaceFormQuotientModel_sphereThree :
    ∃ P : SphericalSpaceFormQuotientModel I3 (Sphere 3), Subsingleton P.quotient.Γ :=
  ⟨sphericalSpaceFormQuotientModelSphereThree,
    instSubsingletonSphericalSpaceFormQuotientModelSphereThreeDeckGroup⟩

theorem exists_subsingleton_deckGroup_iff_exists_injective_proj :
    (∃ P : SphericalSpaceFormQuotientModel I3 M, Subsingleton P.quotient.Γ) ↔
      (∃ P : SphericalSpaceFormQuotientModel I3 M, Function.Injective P.quotient.proj) := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P, (RoundSphereQuotient.subsingleton_deckGroup_iff_injective_proj P.quotient).mp hP⟩
  · rintro ⟨P, hP⟩
    exact ⟨P, (RoundSphereQuotient.subsingleton_deckGroup_iff_injective_proj P.quotient).mpr hP⟩

theorem nonempty_diffeomorph_sphereThree_sphereThree :
    Nonempty (Diffeomorph (𝓡 3) I3 (Sphere 3) (Sphere 3) ∞) :=
  exists_diffeomorph_sphereThree_of_sphericalSpaceFormQuotientModel
    sphericalSpaceFormQuotientModelSphereThree

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

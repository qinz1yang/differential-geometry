import DifferentialGeometry.Topology.ProjectiveSpace.Topology
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.Ball.Action
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

noncomputable section

open Metric Topology

namespace Poincare.ProjectiveSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private theorem sphere_ne_zero (x : sphere (0 : E) 1) : (x : E) ≠ 0 := by
  intro hx
  have h := mem_sphere_zero_iff_norm.mp x.prop
  simp [hx] at h


def sphereProjection (x : sphere (0 : E) 1) : Projectivization ℝ E :=
  Projectivization.mk ℝ x (sphere_ne_zero x)


@[fun_prop]
theorem continuous_sphereProjection : Continuous (sphereProjection (E := E)) :=
  (continuous_mk' ℝ E).comp (continuous_subtype_val.subtype_mk sphere_ne_zero)


def normalizeToSphere (v : {v : E // v ≠ 0}) : sphere (0 : E) 1 :=
  ⟨NormedSpace.normalize v, mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize v.prop)⟩


@[fun_prop]
theorem continuous_normalizeToSphere : Continuous (normalizeToSphere (E := E)) := by
  apply Continuous.subtype_mk
  exact ((continuous_subtype_val.norm.inv₀ (fun v ↦ norm_ne_zero_iff.mpr v.prop)).smul
    continuous_subtype_val)


@[simp]
theorem sphereProjection_normalizeToSphere (v : {v : E // v ≠ 0}) :
    sphereProjection (normalizeToSphere v) = Projectivization.mk' ℝ v := by
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  exact ⟨‖(v : E)‖⁻¹, rfl⟩

theorem isQuotientMap_sphereProjection : IsQuotientMap (sphereProjection (E := E)) := by
  apply IsQuotientMap.of_comp continuous_normalizeToSphere continuous_sphereProjection
  have h : sphereProjection (E := E) ∘ normalizeToSphere = Projectivization.mk' ℝ := by
    funext v
    exact sphereProjection_normalizeToSphere v
  rw [h]
  exact isQuotientMap_mk' ℝ E


theorem sphereProjection_eq_iff (x y : sphere (0 : E) 1) :
    sphereProjection x = sphereProjection y ↔ x = y ∨ x = -y := by
  rw [sphereProjection, sphereProjection, Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    have hn := congrArg norm ha
    rw [norm_smul, mem_sphere_zero_iff_norm.mp x.prop, mem_sphere_zero_iff_norm.mp y.prop,
      mul_one, Real.norm_eq_abs] at hn
    obtain h | h := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hn
    · left
      apply Subtype.ext
      simpa [h] using ha.symm
    · right
      apply Subtype.ext
      simpa [h] using ha.symm
  · rintro (rfl | rfl)
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simp⟩


theorem sphereProjection_surjective : Function.Surjective (sphereProjection (E := E)) :=
  isQuotientMap_sphereProjection.surjective

abbrev SphereQuotient (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  MulAction.orbitRel.Quotient (sphere (0 : ℝ) 1) (sphere (0 : E) 1)

theorem sphereProjection_eq_iff_orbitRel (x y : sphere (0 : E) 1) :
    sphereProjection x = sphereProjection y ↔
      MulAction.orbitRel (sphere (0 : ℝ) 1) (sphere (0 : E) 1) x y := by
  rw [sphereProjection, sphereProjection, Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    have hn := congrArg norm ha
    rw [norm_smul, mem_sphere_zero_iff_norm.mp x.prop, mem_sphere_zero_iff_norm.mp y.prop,
      mul_one] at hn
    exact ⟨⟨a, mem_sphere_zero_iff_norm.mpr hn⟩, Subtype.ext ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a.val, congrArg Subtype.val ha⟩

def sphereQuotientMap : SphereQuotient E → Projectivization ℝ E :=
  Quotient.lift sphereProjection (fun x y h ↦ (sphereProjection_eq_iff_orbitRel x y).mpr h)

@[simp]
theorem sphereQuotientMap_mk (x : sphere (0 : E) 1) :
    sphereQuotientMap (Quotient.mk _ x) = sphereProjection x := rfl


theorem sphereQuotientMap_bijective : Function.Bijective (sphereQuotientMap (E := E)) := by
  constructor
  · intro x y h
    induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
    exact Quotient.sound ((sphereProjection_eq_iff_orbitRel x y).mp h)
  · intro p
    obtain ⟨x, rfl⟩ := sphereProjection_surjective p
    exact ⟨Quotient.mk _ x, rfl⟩

def sphereQuotientHomeomorph : SphereQuotient E ≃ₜ Projectivization ℝ E :=
  (Equiv.ofBijective sphereQuotientMap sphereQuotientMap_bijective).toHomeomorph (fun U ↦ by
    rw [← isQuotientMap_quotient_mk'.isOpen_preimage,
      ← isQuotientMap_sphereProjection.isOpen_preimage]
    rfl)


@[simp]
theorem sphereQuotientHomeomorph_mk (x : sphere (0 : E) 1) :
    sphereQuotientHomeomorph (Quotient.mk _ x) = sphereProjection x := rfl

@[simp]
theorem sphereQuotientHomeomorph_symm_projection (x : sphere (0 : E) 1) :
    sphereQuotientHomeomorph.symm (sphereProjection x) = Quotient.mk _ x :=
  (sphereQuotientHomeomorph (E := E)).symm_apply_apply (Quotient.mk _ x)


theorem isOpenQuotientMap_sphereProjection :
    IsOpenQuotientMap (sphereProjection (E := E)) :=
  (sphereQuotientHomeomorph (E := E)).isOpenQuotientMap.comp
    (MulAction.isOpenQuotientMap_quotientMk
      (Γ := sphere (0 : ℝ) 1) (T := sphere (0 : E) 1))

instance t2Space : T2Space (Projectivization ℝ E) := by
  apply (t2Space_iff_of_isOpenQuotientMap isOpenQuotientMap_sphereProjection).mpr
  have h : {p : sphere (0 : E) 1 × sphere (0 : E) 1 |
      sphereProjection p.1 = sphereProjection p.2} =
      {p | p.1 = p.2} ∪ {p | p.1 = -p.2} := by
    ext p
    exact sphereProjection_eq_iff p.1 p.2
  rw [h]
  exact (isClosed_eq continuous_fst continuous_snd).union
    (isClosed_eq continuous_fst continuous_snd.neg)


theorem compactSpace_of_compact_sphere [CompactSpace (sphere (0 : E) 1)] :
    CompactSpace (Projectivization ℝ E) :=
  sphereProjection_surjective.compactSpace continuous_sphereProjection

instance compactSpace [FiniteDimensional ℝ E] : CompactSpace (Projectivization ℝ E) :=
  compactSpace_of_compact_sphere

end Poincare.ProjectiveSpace

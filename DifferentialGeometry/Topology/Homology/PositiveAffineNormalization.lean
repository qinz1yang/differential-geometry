import DifferentialGeometry.Topology.Homology.RelativeZero
import DifferentialGeometry.Topology.Homology.RelativeFunctoriality
import DifferentialGeometry.Topology.Homology.Homotopy
import Mathlib.Analysis.Convex.Contractible

noncomputable section

open ContinuousMap Set

namespace DifferentialGeometry.Topology

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E]

theorem integralRelativeHomologyMap_smul_pos_eq_id (n : ℕ) {r : ℝ} (hr : 0 < r) :
    integralRelativeHomologyMap n
      (⟨fun x : E => r • x, continuous_const.smul continuous_id⟩ : C(E, E))
      (show MapsTo (fun x : E => r • x) ({0}ᶜ : Set E) ({0}ᶜ : Set E) from
        fun _ hx hz => hx ((smul_eq_zero.mp hz).resolve_left hr.ne')) = LinearMap.id := by
  let f : C(E, E) := ⟨fun x => r • x, continuous_const.smul continuous_id⟩
  let U : Set E := {0}ᶜ
  have hp : MapsTo f U U :=
    fun _ hx hz => hx ((smul_eq_zero.mp hz).resolve_left hr.ne')
  have hcoef (t : unitInterval) : 0 < (1 - (t : ℝ)) + (t : ℝ) * r := by
    have h := (show Convex ℝ (Ioi (0 : ℝ)) from convex_Ioi 0)
      (by norm_num : (1 : ℝ) ∈ Ioi (0 : ℝ)) hr
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
    simpa only [smul_eq_mul, mul_one, mem_Ioi] using h
  let H : (singularPairRestriction (ContinuousMap.id E) (fun _ hx => hx)).Homotopy
      (singularPairRestriction f hp) :=
    { toFun := fun p => ⟨((1 - (p.1 : ℝ)) + (p.1 : ℝ) * r) • (p.2 : E),
        fun hz => p.2.property ((smul_eq_zero.mp hz).resolve_left (hcoef p.1).ne')⟩
      continuous_toFun := by
        exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
          ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).smul
          (continuous_subtype_val.comp continuous_snd)).subtype_mk _
      map_zero_left := by
        intro x
        apply Subtype.ext
        simp [singularPairRestriction]
      map_one_left := by
        intro x
        apply Subtype.ext
        simp [singularPairRestriction, f] }
  have heq : integralRelativeHomologyMap n f hp =
      integralRelativeHomologyMap n (ContinuousMap.id E) (fun _ hx => hx) := by
    cases n with
    | zero =>
      exact integralRelativeHomologyMap_zero_eq_of_joined f (ContinuousMap.id E) U U hp
        (fun _ hx => hx) (fun _ => ⟨PathConnectedSpace.somePath _ _⟩)
    | succ n =>
      let := integralSingularHomology_subsingleton_of_contractible (n + 1) (by omega) E
      exact (integralRelativeHomologyMap_eq_of_restriction_homotopic n
        (ContinuousMap.id E) f U U (fun _ hx => hx) hp ⟨H⟩).symm
  exact heq.trans (integralRelativeHomologyMap_id n U)

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem integralRelativeHomologyMap_smul_sub_eq_sub (n : ℕ) (a : E) {r : ℝ} (hr : 0 < r) :
    integralRelativeHomologyMap n
      (toContinuousMap ((Homeomorph.subRight a).trans (Homeomorph.smulOfNeZero r hr.ne')))
      (show MapsTo (fun x : E => r • (x - a)) ({a}ᶜ : Set E) ({0}ᶜ : Set E) from
        fun _ hx hz => hx (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hr.ne'))) =
      integralRelativeHomologyMap n (toContinuousMap (Homeomorph.subRight a))
        (show MapsTo (fun x : E => x - a) ({a}ᶜ : Set E) ({0}ᶜ : Set E) from
          fun _ hx => sub_ne_zero.mpr hx) := by
  let f := toContinuousMap (Homeomorph.subRight a)
  let g : C(E, E) := ⟨fun x => r • x, continuous_const.smul continuous_id⟩
  have hf : MapsTo f ({a}ᶜ : Set E) ({0}ᶜ : Set E) := fun _ hx => sub_ne_zero.mpr hx
  have hg : MapsTo g ({0}ᶜ : Set E) ({0}ᶜ : Set E) :=
    fun _ hx hz => hx ((smul_eq_zero.mp hz).resolve_left hr.ne')
  change integralRelativeHomologyMap n (g.comp f) (hg.comp hf) =
    integralRelativeHomologyMap n f hf
  rw [integralRelativeHomologyMap_comp n f g hf hg]
  rw [show integralRelativeHomologyMap n g hg = LinearMap.id from
    integralRelativeHomologyMap_smul_pos_eq_id n hr]
  exact LinearMap.id_comp _

end

end DifferentialGeometry.Topology

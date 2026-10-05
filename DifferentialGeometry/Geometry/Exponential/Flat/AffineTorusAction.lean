import DifferentialGeometry.Geometry.Exponential.Flat.AffineTranslations
import DifferentialGeometry.Geometry.Thurston.FlatTorusCoords
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
Actual affine group elements preserve the fibres of the periodic map of their full translation
basis. They therefore induce smooth torus homeomorphisms with a literal equivariance equation.
The kernel is exactly the translation kernel, proved using the actual discrete integer lattice.
-/

set_option autoImplicit false

noncomputable section

open Set Function Module Submodule DifferentialGeometry.Topology.Manifold
open GC.GraphManifold.FlatTorus
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => ((AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) × AddCircle (1 : ℝ))

private def affineTorusAmbientDiffeomorph (g : E3 ≃ᵃⁱ[ℝ] E3) : E3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ E3 where
  toEquiv := g.toEquiv
  contMDiff_toFun := by
    have hs : ContMDiff (𝓡 3) (𝓡 3) ∞
        (fun x => g.linearIsometryEquiv x + g 0) :=
      (g.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff).add
        contMDiff_const
    exact hs.congr (fun x => affineIsometry_apply g x)
  contMDiff_invFun := by
    let L := g.symm.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
    have hs : ContMDiff (𝓡 3) (𝓡 3) ∞
        (fun x => g.symm.linearIsometryEquiv x + g.symm 0) :=
      L.contDiff.contMDiff.add contMDiff_const
    exact hs.congr (fun x => affineIsometry_apply g.symm x)

private theorem affineTorus_period_eq {G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)}
    {b : Basis (Fin 3) ℝ E3}
    {hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G} {x y : E3} :
    periodicTriple b x = periodicTriple b y ↔ y - x ∈ affineTranslationModule G := by
  rw [← hb, periodicTriple_eq_iff, Submodule.mem_span_range_iff_exists_fun ℤ]
  exact exists_congr fun m => eq_comm

private theorem affineTorus_linear_mem_iff {G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)}
    {g : G} {v : E3} :
    (g : E3 ≃ᵃⁱ[ℝ] E3).linearIsometryEquiv v ∈ affineTranslationModule G ↔
      v ∈ affineTranslationModule G := by
  constructor
  · intro hv
    have hi := affineTranslationModule_linear_mem G g⁻¹ hv
    have he := congrArg (fun L : E3 ≃ₗᵢ[ℝ] E3 => L v)
      ((affineLinearHom.comp G.subtype).map_mul g⁻¹ g)
    simp only [inv_mul_cancel, map_one] at he
    change v = (g⁻¹ : G).val.linearIsometryEquiv (g.val.linearIsometryEquiv v) at he
    rw [← he] at hi
    exact hi
  · exact affineTranslationModule_linear_mem G g

private theorem affineTorus_cover_exists (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G) (g : G) :
    ∃ e : T3 ≃ₘ⟮addTripleModel, addTripleModel⟯ T3,
      ∀ x, e (periodicTriple b x) = periodicTriple b ((g : E3 ≃ᵃⁱ[ℝ] E3) x) := by
  let a := affineTorusAmbientDiffeomorph (g : E3 ≃ᵃⁱ[ℝ] E3)
  have hq : IsLocalDiffeomorph (𝓡 3) addTripleModel ∞ (periodicTriple b ∘ a) := by
    intro x
    exact (a.isLocalDiffeomorph x).comp addTripleModel T3
      (periodicTriple_isLocalDiffeomorph b (a x))
  apply exists_diffeomorph_of_same_cover_fibres (periodicTriple b) (periodicTriple b ∘ a)
    (periodicTriple_isLocalDiffeomorph b) hq (periodicTriple_surjective b)
    ((periodicTriple_surjective b).comp a.surjective)
  intro x y
  change periodicTriple b x = periodicTriple b y ↔
    periodicTriple b ((g : E3 ≃ᵃⁱ[ℝ] E3) x) = periodicTriple b ((g : E3 ≃ᵃⁱ[ℝ] E3) y)
  rw [affineTorus_period_eq (hb := hb), affineTorus_period_eq (hb := hb)]
  have he : (g : E3 ≃ᵃⁱ[ℝ] E3) y - (g : E3 ≃ᵃⁱ[ℝ] E3) x =
      (g : E3 ≃ᵃⁱ[ℝ] E3).linearIsometryEquiv (y - x) := by
    exact ((g : E3 ≃ᵃⁱ[ℝ] E3).map_vsub y x).symm
  change y - x ∈ affineTranslationModule G ↔
    (g : E3 ≃ᵃⁱ[ℝ] E3) y - (g : E3 ≃ᵃⁱ[ℝ] E3) x ∈ affineTranslationModule G
  rw [he]
  exact affineTorus_linear_mem_iff.symm

def affineTorusDiffeomorph (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)) (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G) (g : G) :
    T3 ≃ₘ⟮addTripleModel, addTripleModel⟯ T3 :=
  (affineTorus_cover_exists G b hb g).choose

theorem affineTorusDiffeomorph_apply (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G) (g : G) (x : E3) :
    affineTorusDiffeomorph G b hb g (periodicTriple b x) =
      periodicTriple b ((g : E3 ≃ᵃⁱ[ℝ] E3) x) :=
  (affineTorus_cover_exists G b hb g).choose_spec x

def affineTorusHom (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)) (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G) :
    G →* (T3 ≃ₜ T3) where
  toFun g := (affineTorusDiffeomorph G b hb g).toHomeomorph
  map_one' := by
    apply Homeomorph.ext
    intro z
    obtain ⟨x, rfl⟩ := periodicTriple_surjective b z
    exact affineTorusDiffeomorph_apply G b hb 1 x
  map_mul' g h := by
    apply Homeomorph.ext
    intro z
    obtain ⟨x, rfl⟩ := periodicTriple_surjective b z
    change affineTorusDiffeomorph G b hb (g * h) (periodicTriple b x) =
      affineTorusDiffeomorph G b hb g (affineTorusDiffeomorph G b hb h (periodicTriple b x))
    rw [affineTorusDiffeomorph_apply, affineTorusDiffeomorph_apply,
      affineTorusDiffeomorph_apply]
    rfl

theorem affineTorusHom_apply (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)) (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G) (g : G) (x : E3) :
    affineTorusHom G b hb g (periodicTriple b x) =
      periodicTriple b ((g : E3 ≃ᵃⁱ[ℝ] E3) x) :=
  affineTorusDiffeomorph_apply G b hb g x

theorem affineTorusHom_contMDiff (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G) (g : G) :
    ContMDiff addTripleModel addTripleModel ∞ (affineTorusHom G b hb g) :=
  (affineTorusDiffeomorph G b hb g).contMDiff

theorem affineTorusHom_symm_contMDiff (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G) (g : G) :
    ContMDiff addTripleModel addTripleModel ∞ (affineTorusHom G b hb g).symm :=
  (affineTorusDiffeomorph G b hb g).symm.contMDiff

theorem affineTorusHom_ker (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)) (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G) :
    (affineTorusHom G b hb).ker = affineTranslationKernel G := by
  ext g
  change affineTorusHom G b hb g = 1 ↔ (g : E3 ≃ᵃⁱ[ℝ] E3).linearIsometryEquiv = 1
  constructor
  · intro hg
    have hm (x : E3) : (g : E3 ≃ᵃⁱ[ℝ] E3) x - x ∈ affineTranslationModule G := by
      apply (affineTorus_period_eq (hb := hb)).mp
      rw [← affineTorusHom_apply G b hb g x, hg]
      rfl
    let L := affineTranslationModule G
    let instTranslationDiscrete : DiscreteTopology L := by
      let e : L ≃ₜ Submodule.span ℤ (Set.range b) :=
        Homeomorph.setCongr (congrArg (fun K : Submodule ℤ E3 => (K : Set E3)) hb.symm)
      exact DiscreteTopology.of_continuous_injective e.continuous e.injective
    let δ : E3 → L := fun x => ⟨(g : E3 ≃ᵃⁱ[ℝ] E3) x - x, hm x⟩
    have hδ : Continuous δ :=
      ((g : E3 ≃ᵃⁱ[ℝ] E3).continuous.sub continuous_id).subtype_mk hm
    have hc (x : E3) : (g : E3 ≃ᵃⁱ[ℝ] E3) x - x = (g : E3 ≃ᵃⁱ[ℝ] E3) 0 := by
      have he : δ x = δ 0 := PreconnectedSpace.constant inferInstance hδ
      simpa only [δ, sub_zero] using congrArg Subtype.val he
    apply LinearIsometryEquiv.ext
    intro x
    change (g : E3 ≃ᵃⁱ[ℝ] E3).linearIsometryEquiv x = x
    have he := hc x
    rw [affineIsometry_apply] at he
    linear_combination (norm := abel) he
  · intro hg
    have ht : (g : E3 ≃ᵃⁱ[ℝ] E3) =
        AffineIsometryEquiv.constVAdd ℝ E3 ((g : E3 ≃ᵃⁱ[ℝ] E3) 0) := by
      apply AffineIsometryEquiv.ext
      intro x
      rw [affineIsometry_apply, hg]
      simp [AffineIsometryEquiv.coe_constVAdd, vadd_eq_add, add_comm]
    have hzero : (g : E3 ≃ᵃⁱ[ℝ] E3) 0 ∈ affineTranslationModule G := by
      change AffineIsometryEquiv.constVAdd ℝ E3 ((g : E3 ≃ᵃⁱ[ℝ] E3) 0) ∈ G
      rw [← ht]
      exact g.property
    apply Homeomorph.ext
    intro z
    obtain ⟨x, rfl⟩ := periodicTriple_surjective b z
    rw [affineTorusHom_apply]
    apply Eq.symm
    apply (affineTorus_period_eq (hb := hb)).mpr
    have hdelta : (g : E3 ≃ᵃⁱ[ℝ] E3) x - x = (g : E3 ≃ᵃⁱ[ℝ] E3) 0 := by
      rw [affineIsometry_apply (g : E3 ≃ᵃⁱ[ℝ] E3) x, hg]
      change x + (g : E3 ≃ᵃⁱ[ℝ] E3) 0 - x = (g : E3 ≃ᵃⁱ[ℝ] E3) 0
      abel
    rw [hdelta]
    exact hzero

end DifferentialGeometry.Geometry.FlatSurface

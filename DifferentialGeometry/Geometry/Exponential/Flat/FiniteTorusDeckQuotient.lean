import DifferentialGeometry.Geometry.Exponential.Flat.AffineTorusAction
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# The actual torus quotient of an affine deck group

The induced torus action factors faithfully through the actual translation kernel. Freeness
is inherited from the original affine action, and the torus orbit quotient is identified with
the same covering base by the literal periodic and covering maps.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology
open GC.GraphManifold.FlatTorus
open scoped Manifold

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => ((AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) × AddCircle (1 : ℝ))

variable (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)) (b : Module.Basis (Fin 3) ℝ E3)
  (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)

def finiteTorusDeckHom : G ⧸ affineTranslationKernel G →* (T3 ≃ₜ T3) :=
  QuotientGroup.lift (affineTranslationKernel G) (affineTorusHom G b hb)
    (le_of_eq (affineTorusHom_ker G b hb).symm)

@[instance_reducible] def finiteTorusDeckAction :
    MulAction (G ⧸ affineTranslationKernel G) T3 :=
  MulAction.compHom T3 (finiteTorusDeckHom G b hb)

abbrev finiteTorusDeckQuotient :=
  letI _instAction := finiteTorusDeckAction G b hb
  MulAction.orbitRel.Quotient (G ⧸ affineTranslationKernel G) T3

theorem finiteTorusDeckHom_injective : Injective (finiteTorusDeckHom G b hb) :=
  (QuotientGroup.injective_lift_iff (affineTranslationKernel G) (affineTorusHom G b hb)
    (le_of_eq (affineTorusHom_ker G b hb).symm)).mpr (affineTorusHom_ker G b hb).symm

@[simp] theorem finiteTorusDeckHom_mk (g : G) :
    finiteTorusDeckHom G b hb (QuotientGroup.mk g) = affineTorusHom G b hb g := rfl

theorem finiteTorusDeckHom_apply (g : G) (x : E3) :
    finiteTorusDeckHom G b hb (QuotientGroup.mk g) (periodicTriple b x) =
      periodicTriple b ((g : E3 ≃ᵃⁱ[ℝ] E3) x) :=
  affineTorusHom_apply G b hb g x

theorem finiteTorusDeckContinuousConstSMul :
    letI _instAction := finiteTorusDeckAction G b hb
    ContinuousConstSMul (G ⧸ affineTranslationKernel G) T3 := by
  let _instAction := finiteTorusDeckAction G b hb
  exact ⟨fun γ => (finiteTorusDeckHom G b hb γ).continuous⟩

private theorem finiteTorus_period_eq {G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)}
    {b : Module.Basis (Fin 3) ℝ E3}
    {hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G} {x y : E3} :
    periodicTriple b x = periodicTriple b y ↔ y - x ∈ affineTranslationModule G := by
  rw [← hb, periodicTriple_eq_iff, Submodule.mem_span_range_iff_exists_fun ℤ]
  exact exists_congr fun m => eq_comm

include hb in
private theorem finiteTorus_fixed_translation
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : E3, (g : E3 ≃ᵃⁱ[ℝ] E3) x ≠ x)
    (g : G) (x : E3) (he : periodicTriple b ((g : E3 ≃ᵃⁱ[ℝ] E3) x) =
      periodicTriple b x) : g ∈ affineTranslationKernel G := by
  have hv := (finiteTorus_period_eq (hb := hb)).mp he
  let τ : G := ⟨AffineIsometryEquiv.constVAdd ℝ E3 (x - (g : E3 ≃ᵃⁱ[ℝ] E3) x), hv⟩
  have hfix : ((τ * g : G) : E3 ≃ᵃⁱ[ℝ] E3) x = x := by
    change x - (g : E3 ≃ᵃⁱ[ℝ] E3) x + (g : E3 ≃ᵃⁱ[ℝ] E3) x = x
    abel
  have hone : τ * g = 1 := by
    by_contra hne
    exact hfree (τ * g) hne x hfix
  have hτ : τ ∈ affineTranslationKernel G := by
    apply mem_affineTranslationKernel.mpr
    ext v
    rfl
  rw [eq_inv_of_mul_eq_one_right hone]
  exact (affineTranslationKernel G).inv_mem hτ

theorem finiteTorusDeckHom_eq_one_of_fixed
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : E3, (g : E3 ≃ᵃⁱ[ℝ] E3) x ≠ x)
    (γ : G ⧸ affineTranslationKernel G) (z : T3)
    (hfix : finiteTorusDeckHom G b hb γ z = z) : γ = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  obtain ⟨x, rfl⟩ := periodicTriple_surjective b z
  apply (QuotientGroup.eq_one_iff g).mpr
  apply finiteTorus_fixed_translation G b hb hfree g x
  simpa only [finiteTorusDeckHom_apply] using hfix

theorem finiteTorusDeckHom_free
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : E3, (g : E3 ≃ᵃⁱ[ℝ] E3) x ≠ x)
    (γ : G ⧸ affineTranslationKernel G) (hne : γ ≠ 1) (z : T3) :
    finiteTorusDeckHom G b hb γ z ≠ z :=
  fun hfix => hne (finiteTorusDeckHom_eq_one_of_fixed G b hb hfree γ z hfix)

theorem finiteTorusDeckIsCancelSMul
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : E3, (g : E3 ≃ᵃⁱ[ℝ] E3) x ≠ x) :
    letI _instAction := finiteTorusDeckAction G b hb
    IsCancelSMul (G ⧸ affineTranslationKernel G) T3 := by
  let _instAction := finiteTorusDeckAction G b hb
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro γ z hfix
  exact finiteTorusDeckHom_eq_one_of_fixed G b hb hfree γ z hfix

variable {Y : Type*} [instY : TopologicalSpace Y]

omit instY in
include hb in
private theorem finiteTorus_cover_periods {p : E3 → Y}
    (hrel : ∀ x y, p x = p y ↔ ∃ g : G, (g : E3 ≃ᵃⁱ[ℝ] E3) x = y)
    {x y : E3} (he : periodicTriple b x = periodicTriple b y) : p x = p y := by
  have hv := (finiteTorus_period_eq (hb := hb)).mp he
  let τ : G := ⟨AffineIsometryEquiv.constVAdd ℝ E3 (y - x), hv⟩
  apply (hrel x y).mpr
  refine ⟨τ, ?_⟩
  change y - x + x = y
  abel

omit instY in
private theorem finiteTorus_quotient_fibres {p : E3 → Y}
    (hrel : ∀ x y, p x = p y ↔ ∃ g : G, (g : E3 ≃ᵃⁱ[ℝ] E3) x = y)
    {x y : E3} :
    (Quotient.mk'' (periodicTriple b x) : finiteTorusDeckQuotient G b hb) =
      Quotient.mk'' (periodicTriple b y) ↔ p x = p y := by
  let _instAction := finiteTorusDeckAction G b hb
  constructor
  · intro he
    obtain ⟨γ, hγ⟩ := Quotient.exact he.symm
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    change finiteTorusDeckHom G b hb (QuotientGroup.mk g) (periodicTriple b x) =
      periodicTriple b y at hγ
    rw [finiteTorusDeckHom_apply] at hγ
    exact ((hrel x ((g : E3 ≃ᵃⁱ[ℝ] E3) x)).mpr ⟨g, rfl⟩).trans
      (finiteTorus_cover_periods G b hb (p := p) hrel hγ)
  · intro he
    obtain ⟨g, hg⟩ := (hrel x y).mp he
    apply Eq.symm
    apply Quotient.sound
    refine ⟨QuotientGroup.mk g, ?_⟩
    change finiteTorusDeckHom G b hb (QuotientGroup.mk g) (periodicTriple b x) =
      periodicTriple b y
    rw [finiteTorusDeckHom_apply, hg]

theorem exists_finiteTorusDeckQuotientHomeomorph (p : E3 → Y)
    (hp : IsCoveringMap p) (hs : Surjective p)
    (hrel : ∀ x y, p x = p y ↔ ∃ g : G, (g : E3 ≃ᵃⁱ[ℝ] E3) x = y) :
    ∃ e : finiteTorusDeckQuotient G b hb ≃ₜ Y,
      ∀ x : E3, e (Quotient.mk'' (periodicTriple b x)) = p x := by
  let _instAction := finiteTorusDeckAction G b hb
  let Q := finiteTorusDeckQuotient G b hb
  let q : E3 → Q := fun x => Quotient.mk'' (periodicTriple b x)
  have hqs : Surjective q := by
    intro z
    obtain ⟨t, rfl⟩ := Quotient.mk''_surjective z
    obtain ⟨x, rfl⟩ := periodicTriple_surjective b t
    exact ⟨x, rfl⟩
  have hqrel : ∀ x y, q x = q y ↔ p x = p y :=
    fun x y => finiteTorus_quotient_fibres G b hb (p := p) hrel
  have hπ : IsQuotientMap (periodicTriple b) :=
    (periodicTriple_isLocalDiffeomorph b).isOpenMap.isQuotientMap
      (periodicTriple_isLocalDiffeomorph b).contMDiff.continuous
      (periodicTriple_surjective b)
  have hq : IsQuotientMap q := isQuotientMap_quotient_mk'.comp hπ
  let f : Q → Y := p ∘ surjInv hqs
  have hf (x : E3) : f (q x) = p x :=
    (hqrel (surjInv hqs (q x)) x).mp (surjInv_eq hqs (q x))
  have hfi : Injective f := by
    intro a c hac
    have he := (hqrel (surjInv hqs a) (surjInv hqs c)).mpr hac
    simpa only [surjInv_eq] using he
  have hfs : Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨q x, hf x⟩
  let e : Q ≃ Y := Equiv.ofBijective f ⟨hfi, hfs⟩
  have he (x : E3) : e (q x) = p x := hf x
  have hi (x : E3) : e.symm (p x) = q x := by
    rw [← he x, e.symm_apply_apply]
  refine ⟨{ toEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }, he⟩
  · apply hq.continuous_iff.mpr
    change Continuous ((e : Q → Y) ∘ q)
    have hc : (e : Q → Y) ∘ q = p := funext he
    rw [hc]
    exact hp.continuous
  · apply (hp.isQuotientMap hs).continuous_iff.mpr
    change Continuous ((e.symm : Y → Q) ∘ p)
    have hc : (e.symm : Y → Q) ∘ p = q := funext hi
    rw [hc]
    exact hq.continuous

end DifferentialGeometry.Geometry.FlatSurface

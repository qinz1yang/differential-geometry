import DifferentialGeometry.Geometry.Exponential.Flat.FiniteTorusDeckQuotient
import DifferentialGeometry.Topology.Manifold.FibreDiffeo

/-!
# Smooth descent through the actual finite affine torus action

The actual affine torus maps make the finite translation quotient action smooth. Its free
properly discontinuous action supplies the canonical quotient atlas. Two actual smooth covers
with the same fibres identify this quotient smoothly with the original target manifold.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Topology.Manifold GC.GraphManifold.FlatTorus
open Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => ((AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) × AddCircle (1 : ℝ))
local notation "H3" => ModelProd (ModelProd ℝ ℝ) ℝ

variable (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)) (b : Module.Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)

theorem finiteTorusDeckSmooth :
    letI _instAction := finiteTorusDeckAction G b hb
    ContMDiffConstSMul addTripleModel ∞ (G ⧸ affineTranslationKernel G) T3 := by
  let instAction := finiteTorusDeckAction G b hb
  constructor
  intro γ
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  change ContMDiff addTripleModel addTripleModel ∞
    (finiteTorusDeckHom G b hb (QuotientGroup.mk g))
  rw [finiteTorusDeckHom_mk]
  exact affineTorusHom_contMDiff G b hb g

variable (hf : Finite (G ⧸ affineTranslationKernel G))
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : E3, (g : E3 ≃ᵃⁱ[ℝ] E3) x ≠ x)

@[instance_reducible] def finiteTorusDeckCharts :
    ChartedSpace H3 (finiteTorusDeckQuotient G b hb) :=
  letI _instAction := finiteTorusDeckAction G b hb
  letI _instFinite := hf
  letI _instContinuous := finiteTorusDeckContinuousConstSMul G b hb
  letI _instCancel := finiteTorusDeckIsCancelSMul G b hb hfree
  MulAction.instChartedSpaceQuotient

theorem finiteTorusDeck_quotient_localDiffeomorph :
    letI _instCharts := finiteTorusDeckCharts G b hb hf hfree
    IsLocalDiffeomorph addTripleModel addTripleModel ∞
      (fun z : T3 => (Quotient.mk'' z : finiteTorusDeckQuotient G b hb)) := by
  let instAction := finiteTorusDeckAction G b hb
  let instFinite := hf
  let instContinuous := finiteTorusDeckContinuousConstSMul G b hb
  let instCancel := finiteTorusDeckIsCancelSMul G b hb hfree
  let instSmooth := finiteTorusDeckSmooth G b hb
  exact MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul addTripleModel

variable {Y : Type*} [instY : TopologicalSpace Y] [instCY : ChartedSpace E3 Y]

theorem exists_finiteTorusDeckDiffeomorph (p : E3 → Y)
    (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (hc : IsCoveringMap p) (hs : Surjective p)
    (hrel : ∀ x y, p x = p y ↔ ∃ g : G, (g : E3 ≃ᵃⁱ[ℝ] E3) x = y) :
    letI _instCharts := finiteTorusDeckCharts G b hb hf hfree
    ∃ e : Y ≃ₘ⟮𝓡 3, addTripleModel⟯ finiteTorusDeckQuotient G b hb,
      ∀ x, e (p x) = Quotient.mk'' (periodicTriple b x) := by
  let instCharts := finiteTorusDeckCharts G b hb hf hfree
  let q : E3 → finiteTorusDeckQuotient G b hb :=
    fun x => Quotient.mk'' (periodicTriple b x)
  obtain ⟨e, he⟩ := exists_finiteTorusDeckQuotientHomeomorph G b hb p hc hs hrel
  have hq : IsLocalDiffeomorph (𝓡 3) addTripleModel ∞ q := by
    intro x
    exact (periodicTriple_isLocalDiffeomorph b x).comp addTripleModel
      (finiteTorusDeckQuotient G b hb)
      (finiteTorusDeck_quotient_localDiffeomorph G b hb hf hfree (periodicTriple b x))
  have hqs : Surjective q := by
    intro z
    obtain ⟨t, rfl⟩ := Quotient.mk''_surjective z
    obtain ⟨x, rfl⟩ := periodicTriple_surjective b t
    exact ⟨x, rfl⟩
  apply exists_diffeomorph_of_same_cover_fibres p q hp hq hs hqs
  intro x y
  constructor
  · intro hxy
    apply e.injective
    exact (he x).trans (hxy.trans (he y).symm)
  · intro hxy
    exact (he x).symm.trans ((congrArg e hxy).trans (he y))

end DifferentialGeometry.Geometry.FlatSurface

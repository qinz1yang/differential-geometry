import DifferentialGeometry.Geometry.Exponential.Flat.AffineTranslations
import DifferentialGeometry.Geometry.Exponential.Flat.LatticePointGroup
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
The actual spanning translation module of a bounded-orbit discrete affine group is an integer
lattice with a constructed full real basis. Its rotational image is contained in the existing
finite lattice point group, so the actual quotient by translations is finite.
-/

set_option autoImplicit false

noncomputable section

open Set Module Submodule

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] [instFD : FiniteDimensional ℝ V]

omit instFD in
theorem affineTranslation_discrete (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    (hdisc : ∀ R : ℝ, Set.Finite {g : G | ‖(g : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R}) :
    DiscreteTopology (affineTranslationModule G) := by
  let L := affineTranslationModule G
  have hf := affineTranslationModule_bounded_finite G 1 (hdisc 1)
  have hpre := Set.Finite.preimage (f := fun x : L => (x : V))
    Subtype.val_injective.injOn hf
  have hs : Set.Finite (Metric.closedBall (0 : L) 1) := by
    simpa only [preimage_ofPred_eq, SetLike.coe_mem, true_and,
      Metric.closedBall, dist_zero_right, Submodule.norm_coe] using hpre
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  exact isOpen_singleton_of_finite_mem_nhds (0 : L)
    (Metric.closedBall_mem_nhds _ zero_lt_one) hs

omit instFD in
theorem affineTranslation_isZLattice (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    (hdisc : ∀ R : ℝ, Set.Finite {g : G | ‖(g : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R})
    (hspan : Submodule.span ℝ (affineTranslationModule G : Set V) = ⊤) :
    ∃ hD : DiscreteTopology (affineTranslationModule G),
      letI instTranslationDiscrete : DiscreteTopology (affineTranslationModule G) := hD
      @IsZLattice ℝ inferInstance V instV inferInstance (affineTranslationModule G)
        instTranslationDiscrete :=
  by
    let instTranslationDiscrete : DiscreteTopology (affineTranslationModule G) :=
      affineTranslation_discrete G hdisc
    exact ⟨instTranslationDiscrete, ⟨hspan⟩⟩

theorem exists_affineTranslation_lattice (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    (hdisc : ∀ R : ℝ, Set.Finite {g : G | ‖(g : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R})
    (hspan : Submodule.span ℝ (affineTranslationModule G : Set V) = ⊤) :
    ∃ b : Basis (Fin (finrank ℝ V)) ℝ V,
      Submodule.span ℤ (Set.range b) = affineTranslationModule G := by
  let L := affineTranslationModule G
  let instTranslationDiscrete : DiscreteTopology L := affineTranslation_discrete G hdisc
  let instTranslationLattice : IsZLattice ℝ L := ⟨hspan⟩
  let instTranslationFinite : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let instTranslationFree : Module.Free ℤ L := ZLattice.module_free ℝ L
  let b := Module.finBasisOfFinrankEq ℤ L (ZLattice.rank ℝ L)
  exact ⟨b.ofZLatticeBasis ℝ L, b.ofZLatticeBasis_span ℝ L⟩

theorem finite_affineTranslation_quotient (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    (hdisc : ∀ R : ℝ, Set.Finite {g : G | ‖(g : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R})
    (hspan : Submodule.span ℝ (affineTranslationModule G : Set V) = ⊤) :
    Finite (G ⧸ affineTranslationKernel G) := by
  obtain ⟨b, hb⟩ := exists_affineTranslation_lattice G hdisc hspan
  let φ := affineLinearHom.comp G.subtype
  have hpoint : Set.Finite {A : V ≃ₗᵢ[ℝ] V |
      Set.MapsTo A (affineTranslationModule G) (affineTranslationModule G)} := by
    rw [← hb]
    exact finite_lattice_pointGroup b
  have hrange : Set.Finite (φ.range : Set (V ≃ₗᵢ[ℝ] V)) := by
    apply hpoint.subset
    rintro A ⟨g, rfl⟩ v hv
    exact affineTranslationModule_linear_mem G g hv
  let instRotationRangeFinite : Finite φ.range := hrange.to_subtype
  change Finite (G ⧸ φ.ker)
  exact Finite.of_equiv φ.range (QuotientGroup.quotientKerEquivRange φ).symm.toEquiv

end DifferentialGeometry.Geometry.FlatSurface

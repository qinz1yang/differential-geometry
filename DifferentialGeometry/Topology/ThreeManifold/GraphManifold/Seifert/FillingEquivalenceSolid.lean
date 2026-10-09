import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingProduct

/-!
# Meridian preserving solid torus extensions with actual collar germs

Linear extensions use the existing explicit disc rotations and reflections. General extensions
consume the existing smooth mapping class isotopy, including its jointly smooth inverse. Actual
boundary maps are straightened on a positive collar germ of the compact solid torus model.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u
namespace GC.Seifert

open ElementaryPresentation

def fillingEquivalenceDiscLift : UnitDisc.{u} ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ UnitDisc.{0} :=
  (uliftDiffeomorph (𝓡∂ 2) unitDiscSet).symm.trans
    (uliftDiffeomorph (𝓡∂ 2) unitDiscSet)

theorem fillingEquivalenceDiscCircle_boundary (t : Torus) :
    solidTorusDiscCircle (solidTorusCollar.{u} (t, halfZero)) =
      (ULift.up (fillingDiscBoundary t.1).down, t.2) := by
  rw [solidTorusCollar_eq_symm, solidTorusDiscCircle.apply_symm_apply]
  apply Prod.ext
  · apply ULift.ext
    apply Subtype.ext
    exact cliffordDiscCollarMap_zero_val t.1
  · rfl

theorem exists_solidTorusBoundaryExtension_of_discExtension
    (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (D : (UnitDisc.{0} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), (𝓡∂ 2).prod (𝓡 1)⟯
      UnitDisc.{0} × Circle)
    (hD : ∀ t : Torus, D (fillingDiscBoundary t.1, t.2) =
      (fillingDiscBoundary (φ t).1, (φ t).2)) :
    ∃ H : solidTorusSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidTorusSet.{u},
      ∀ t, H (solidTorusCollar (t, halfZero)) = solidTorusCollar (φ t, halfZero) := by
  let U := fillingEquivalenceDiscLift.{u}.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)
  let H := ((solidTorusDiscCircle.{u}.trans U).trans D).trans
    (U.symm.trans solidTorusDiscCircle.symm)
  refine ⟨H, ?_⟩
  intro t
  apply solidTorusDiscCircle.injective
  change solidTorusDiscCircle (solidTorusDiscCircle.symm
    (U.symm (D (U (solidTorusDiscCircle (solidTorusCollar (t, halfZero))))))) = _
  rw [solidTorusDiscCircle.apply_symm_apply]
  rw [fillingEquivalenceDiscCircle_boundary]
  change U.symm (D (fillingDiscBoundary t.1, t.2)) = _
  rw [hD]
  change (ULift.up (fillingDiscBoundary (φ t).1).down, (φ t).2) =
    solidTorusDiscCircle.{u} (solidTorusCollar.{u} (φ t, halfZero))
  exact (fillingEquivalenceDiscCircle_boundary.{u} (φ t)).symm

theorem exists_solidTorusGermExtension_of_boundaryExtension
    (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (H : solidTorusSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidTorusSet.{u})
    (hH : ∀ t, H (solidTorusCollar (t, halfZero)) = solidTorusCollar (φ t, halfZero)) :
    ∃ (F : solidTorusSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidTorusSet.{u}) (δ : ℝ),
      0 < δ ∧ δ ≤ 1 ∧ ∀ p ∈ halfCollarSource, p.2.val 0 < δ →
        F (solidTorusCollar p) = solidTorusCollar (φ p.1, p.2) := by
  let c₀ := solidTorusCollar.{u}.trans H.toPartialDiffeomorph
  let J := φ.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)
  let c₁ := J.toPartialDiffeomorph.trans solidTorusCollar.{u}
  have hs : ∀ t, (t, halfZero) ∈ c₀.source ∩ c₁.source := by
    intro t
    constructor
    · change (t, halfZero) ∈ solidTorusCollar.{u}.source ∧
        solidTorusCollar.{u} (t, halfZero) ∈ Set.univ
      exact ⟨solidTorusCollar_source.{u}.symm ▸ zero_mem_halfCollarSource t, trivial⟩
    · change (t, halfZero) ∈ Set.univ ∧ (φ t, halfZero) ∈ solidTorusCollar.{u}.source
      exact ⟨trivial, solidTorusCollar_source.{u}.symm ▸ zero_mem_halfCollarSource (φ t)⟩
  have he : ∀ t, c₀ (t, halfZero) = c₁ (t, halfZero) := hH
  have hb : ∀ t, (𝓡∂ 3).IsBoundaryPoint (c₀ (t, halfZero)) := by
    intro t
    change (𝓡∂ 3).IsBoundaryPoint (H (solidTorusCollar (t, halfZero)))
    rw [hH]
    exact solidTorusBoundary.{u}.boundary_zero 0 (φ t)
  obtain ⟨δ, hδ, Φ, hΦ, hfix⟩ := exists_torusCollar_straightening
    (C := solidTorusCarrier.{u}) c₀ c₁ hs he hb isOpen_univ (subset_univ _)
  refine ⟨H.trans Φ, min δ 1, lt_min hδ zero_lt_one, min_le_right δ 1, ?_⟩
  intro p hp hlt
  exact hΦ p.1 p.2 (lt_of_lt_of_le hlt (min_le_left δ 1))

theorem exists_linear_meridianPreserving_solidTorusDiffeomorph (A : GL (Fin 2) ℤ)
    (hA : A • meridianSlope = meridianSlope) :
    ∃ (F : solidTorusSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidTorusSet.{u}) (δ : ℝ),
      0 < δ ∧ δ ≤ 1 ∧ ∀ p ∈ halfCollarSource, p.2.val 0 < δ →
        F (solidTorusCollar p) = solidTorusCollar (linearTorusDiffeomorph A p.1, p.2) := by
  obtain ⟨D, hD⟩ := exists_linearSolidExtension_of_meridianStabilizer A hA
  obtain ⟨H, hH⟩ := exists_solidTorusBoundaryExtension_of_discExtension
    (linearTorusDiffeomorph A) D (fun t => hD t.1 t.2)
  exact exists_solidTorusGermExtension_of_boundaryExtension (linearTorusDiffeomorph A) H hH

theorem exists_meridianPreserving_solidTorusDiffeomorph_of_mappingClassLinear
    (hT : TorusMappingClassLinear) (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hμ : torusUnit φ • meridianSlope = meridianSlope) :
    ∃ (F : solidTorusSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidTorusSet.{u}) (δ : ℝ),
      0 < δ ∧ δ ≤ 1 ∧ ∀ p ∈ halfCollarSource, p.2.val 0 < δ →
        F (solidTorusCollar p) = solidTorusCollar (φ p.1, p.2) := by
  obtain ⟨D, hD⟩ := exists_solidExtension_of_meridianStabilizer hT φ hμ
  obtain ⟨H, hH⟩ := exists_solidTorusBoundaryExtension_of_discExtension φ D
    (fun t => hD t.1 t.2)
  exact exists_solidTorusGermExtension_of_boundaryExtension φ H hH

end GC.Seifert

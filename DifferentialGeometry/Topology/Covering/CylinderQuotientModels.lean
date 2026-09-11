import DifferentialGeometry.Topology.Covering.TwoPointDeckHomeomorphs
import DifferentialGeometry.Topology.ProjectiveSpace.CylinderHalfTurnFrame
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Descent
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open scoped Manifold ContDiff

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cylinder" => S × ℝ
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private local instance cylinderCoverModelsSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def CylinderQuotientModels (pi : Cylinder → M) : Prop :=
  ((∃ d : Cylinder ≃ₘ⟮CI, I⟯ M, ∀ p : Cylinder, d p = pi p) ∧
    (∀ d : Cylinder ≃ₜ Cylinder, pi ∘ d = pi ↔ d = Homeomorph.refl Cylinder)) ∨
  ((∃ d : (SphereAntipodalQuotient × ℝ) ≃ₘ⟮CI, I⟯ M,
      ∀ p : Cylinder, d (SphereAntipodalQuotient.productProjection p) = pi p) ∧
    (∀ d : Cylinder ≃ₜ Cylinder, pi ∘ d = pi ↔
      d = Homeomorph.refl Cylinder ∨ d = cylinderAntipodalProductDiffeomorph.toHomeomorph)) ∨
  ((∃ d : CylinderDiagonalQuotient ≃ₘ⟮CI, I⟯ M,
      ∀ p : Cylinder, d (CylinderDiagonalQuotient.proj p) = pi p) ∧
    (∀ d : Cylinder ≃ₜ Cylinder, pi ∘ d = pi ↔
      d = Homeomorph.refl Cylinder ∨ d = cylinderDiagonalDiffeomorph.toHomeomorph))

theorem cylinderQuotientModels_of_fibres
    (pi : Cylinder → M) (hlocal : IsLocalDiffeomorph CI I ∞ pi)
    (hcover : IsCoveringMap pi) (hsurj : Function.Surjective pi)
    (hfibres : (∀ p q : Cylinder, pi p = pi q ↔ q = p) ∨
      (∀ p q : Cylinder, pi p = pi q ↔ q = p ∨ q = (-p.1, p.2)) ∨
      (∀ p q : Cylinder, pi p = pi q ↔ q = p ∨ q = (-p.1, -p.2))) :
    CylinderQuotientModels (I := I) pi := by
  let _ : PreconnectedSpace S := Subtype.preconnectedSpace
    (isPreconnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simp :
        1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))
      (0 : EuclideanSpace ℝ (Fin 3)) 1)
  let _ : Nonempty S := ⟨sphereEquator 0⟩
  rcases hfibres with hsingle | hantipodal | hdiagonal
  · have hinj : Function.Injective pi := fun p q h => ((hsingle p q).mp h).symm
    refine Or.inl ⟨⟨hlocal.diffeomorphOfBijective ⟨hinj, hsurj⟩, fun _ => rfl⟩, ?_⟩
    intro d
    constructor
    · intro hd
      apply Homeomorph.ext
      intro p
      exact (hsingle p (d p)).mp (congrFun hd p).symm
    · rintro rfl
      rfl
  · obtain ⟨d, hd⟩ := SphereAntipodalQuotient.exists_product_homeomorph
      pi hlocal.contMDiff.continuous hlocal.isOpenMap hsurj hantipodal
    have hq : IsLocalDiffeomorph CI CI ∞ SphereAntipodalQuotient.productProjection :=
      isLocalDiffeomorph_prod_real SphereAntipodalQuotient.proj
        SphereAntipodalQuotient.isLocalDiffeomorph_proj
    obtain ⟨D, hD⟩ := exists_diffeomorph_of_homeomorph_comp_localDiffeomorph
      SphereAntipodalQuotient.productProjection hq
      SphereAntipodalQuotient.surjective_productProjection pi hlocal d hd
    refine Or.inr (Or.inl ⟨⟨D, ?_⟩, ?_⟩)
    · intro p
      rw [hD]
      exact hd p
    · exact covering_deck_iff_self_or_fibre_swap pi hcover
        cylinderAntipodalProductDiffeomorph.toHomeomorph hantipodal
  · obtain ⟨d, hd⟩ := CylinderDiagonalQuotient.exists_homeomorph
      pi hlocal.contMDiff.continuous hlocal.isOpenMap hsurj hdiagonal
    obtain ⟨D, hD⟩ := exists_diffeomorph_of_homeomorph_comp_localDiffeomorph
      CylinderDiagonalQuotient.proj CylinderDiagonalQuotient.isLocalDiffeomorph_proj
      CylinderDiagonalQuotient.surjective_proj pi hlocal d hd
    refine Or.inr (Or.inr ⟨⟨D, ?_⟩, ?_⟩)
    · intro p
      rw [hD]
      exact hd p
    · exact covering_deck_iff_self_or_fibre_swap pi hcover
        cylinderDiagonalDiffeomorph.toHomeomorph hdiagonal

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

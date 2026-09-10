import DifferentialGeometry.Topology.Simplex.AttachmentRelativeHomology
import DifferentialGeometry.Topology.Simplex.BoundaryEuler
import DifferentialGeometry.Topology.Homology.Algebra.FiniteTypeMap

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace Poincare.Simplex.Attachment
variable (k : Type) [Field k] {n : ℕ} {X P : TopCat.{0}}
  {g : TopCat.of (boundary (Fin (n + 1))) ⟶ X}
  {r : TopCat.of (stdSimplex ℝ (Fin (n + 1))) ⟶ P} {b : X ⟶ P}
  (h : IsPushout boundaryι g r b)
include h

private theorem finite_euler_of_attachment
    (hX : Poincare.Homology.finiteHomologyType k X) :
    Poincare.Homology.finiteHomologyType k P ∧
      Poincare.Homology.eulerChar k P = Poincare.Homology.eulerChar k X + (-1 : ℤ)^n := by
  let D := TopCat.of (stdSimplex ℝ (Fin (n + 1)))
  let B := boundary (Fin (n + 1))
  let s : Set P := Set.range b
  let R := ModuleCat.of k k
  have hB := finiteHomologyType_boundary k n
  let : ContractibleSpace D := (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
    ⟨stdSimplex.barycenter, stdSimplex.barycenter.prop⟩
  have hD : Poincare.Homology.finiteHomologyType k D :=
    Poincare.Homology.finiteHomologyType_of_contractible k
  let e : X ≃ₜ TopCat.of s := (Poincare.TopCat.Pushout.isClosedEmbedding_inr h
    isClosedEmbedding_boundaryι).isEmbedding.toHomeomorph
  have hs : Poincare.Homology.finiteHomologyType k (TopCat.of s) := (Poincare.Homology.finiteHomologyType_iff_of_homeomorph k e).mp hX
  have hCell := Poincare.Homology.finiteHomologyType_relativeChainComplex D B k hB hD
  let q := cellRelativeChainMap R h
  have : QuasiIso q := quasiIso_cellRelativeChainMap R h
  have hRel : Poincare.HomologicalComplex.finiteHomologyType
      (Poincare.Homology.relativeChainComplex P s R) :=
    (Poincare.HomologicalComplex.finiteHomologyType_iff_of_quasiIso q).mp hCell
  have hP : Poincare.Homology.finiteHomologyType k P :=
    Poincare.HomologicalComplex.finiteHomologyType_middle
      (Poincare.Homology.relativeShortComplex P s R)
      (Poincare.Homology.relativeShortExact P s R) hs hRel
  have he := Poincare.HomologicalComplex.homologyEulerChar_eq_of_quasiIso q
  change Poincare.Homology.relativeEulerChar D B k = Poincare.Homology.relativeEulerChar P s k at he
  rw [Poincare.Homology.relativeEulerChar_eq_sub D B k hB hD,
    Poincare.Homology.relativeEulerChar_eq_sub P s k hs hP] at he
  have hDχ : Poincare.Homology.eulerChar k D = 1 := Poincare.Homology.eulerChar_of_contractible k
  have hsχ := Poincare.Homology.eulerChar_eq_of_homeomorph k e
  have hBχ := eulerChar_boundary k n
  exact ⟨hP, by change Poincare.Homology.eulerChar k (TopCat.of B) = _ at hBχ; omega⟩


theorem finiteHomologyType_of_attachment (hX : Poincare.Homology.finiteHomologyType k X) :
    Poincare.Homology.finiteHomologyType k P :=
  (finite_euler_of_attachment k h hX).1


theorem eulerChar_attachment (hX : Poincare.Homology.finiteHomologyType k X) :
    Poincare.Homology.eulerChar k P = Poincare.Homology.eulerChar k X + (-1 : ℤ)^n :=
  (finite_euler_of_attachment k h hX).2

end Poincare.Simplex.Attachment

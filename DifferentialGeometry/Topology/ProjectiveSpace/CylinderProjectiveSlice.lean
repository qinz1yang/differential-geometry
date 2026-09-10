import DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotientSmoothModels

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Topology

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace CylinderDiagonalQuotient

def projectiveSlice : SphereAntipodalQuotient → CylinderDiagonalQuotient :=
  Quotient.map (fun x : SphereTwo => (x, (0 : ℝ))) (by
    intro x y h
    change y = x ∨ y = -x at h
    change (y, (0 : ℝ)) = (x, (0 : ℝ)) ∨ (y, (0 : ℝ)) = -(x, (0 : ℝ))
    rcases h with h | h
    · exact Or.inl (Prod.ext h rfl)
    · right
      exact Prod.ext h (neg_zero : -(0 : ℝ) = 0).symm)

theorem projectiveSlice_proj (x : SphereTwo) :
    projectiveSlice (SphereAntipodalQuotient.proj x) = proj (x, 0) := rfl

theorem continuous_projectiveSlice : Continuous projectiveSlice := by
  have hquotient : IsQuotientMap SphereAntipodalQuotient.proj :=
    SphereAntipodalQuotient.isOpenMap_proj.isQuotientMap
      SphereAntipodalQuotient.continuous_proj SphereAntipodalQuotient.surjective_proj
  apply hquotient.continuous_iff.mpr
  exact continuous_proj.comp (continuous_id.prodMk continuous_const)

theorem injective_projectiveSlice : Function.Injective projectiveSlice := by
  intro q r
  induction q using Quotient.inductionOn with
  | h x =>
    induction r using Quotient.inductionOn with
    | h y =>
      intro h
      apply (SphereAntipodalQuotient.proj_eq_iff x y).mpr
      rcases (proj_eq_iff (x, 0) (y, 0)).mp h with h | h
      · exact Or.inl (congrArg Prod.fst h)
      · exact Or.inr (congrArg Prod.fst h)

theorem isClosedEmbedding_projectiveSlice : IsClosedEmbedding projectiveSlice :=
  continuous_projectiveSlice.isClosedEmbedding injective_projectiveSlice

theorem isCompact_range_projectiveSlice : IsCompact (Set.range projectiveSlice) :=
  isCompact_range continuous_projectiveSlice

end CylinderDiagonalQuotient

namespace SphereAntipodalQuotient

def zeroSlice : SphereAntipodalQuotient → SphereAntipodalQuotient × ℝ :=
  fun q => (q, 0)

theorem isClosedEmbedding_zeroSlice : IsClosedEmbedding zeroSlice := by
  apply (continuous_id.prodMk continuous_const).isClosedEmbedding
  intro q r h
  exact congrArg Prod.fst h

theorem isCompact_range_zeroSlice : IsCompact (Set.range zeroSlice) :=
  isCompact_range (continuous_id.prodMk continuous_const)

end SphereAntipodalQuotient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

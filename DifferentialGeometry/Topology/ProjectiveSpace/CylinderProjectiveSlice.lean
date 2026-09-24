import DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotientSmoothModels
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Descent
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import Mathlib.Geometry.Manifold.SmoothEmbedding

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set _root_.Topology Manifold
open scoped ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "CylinderI" => ModelWithCorners.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ)

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

theorem contMDiff_projectiveSlice : ContMDiff (𝓡 2) CylinderI ∞ projectiveSlice := by
  apply contMDiff_of_comp_surjective_localDiffeomorph
    SphereAntipodalQuotient.proj SphereAntipodalQuotient.isLocalDiffeomorph_proj
    SphereAntipodalQuotient.surjective_proj
  exact isLocalDiffeomorph_proj.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)

set_option backward.isDefEq.respectTransparency false in
theorem isSmoothEmbedding_projectiveSlice :
    IsSmoothEmbedding (𝓡 2) CylinderI ∞ projectiveSlice := by
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv
    (by decide) contMDiff_projectiveSlice ?_, isClosedEmbedding_projectiveSlice.isEmbedding⟩
  intro y
  obtain ⟨x, rfl⟩ := SphereAntipodalQuotient.surjective_proj y
  let A := (SphereAntipodalQuotient.isLocalDiffeomorph_proj x).mfderivToContinuousLinearEquiv
    (by decide : (∞ : ℕ∞ω) ≠ 0)
  let B := (isLocalDiffeomorph_proj (x, 0)).mfderivToContinuousLinearEquiv
    (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hder :
      (mfderiv (𝓡 2) CylinderI projectiveSlice (SphereAntipodalQuotient.proj x)).comp
        (mfderiv (𝓡 2) (𝓡 2) SphereAntipodalQuotient.proj x) =
      (mfderiv CylinderI CylinderI proj (x, 0)).comp
        (ContinuousLinearMap.inl ℝ (TangentSpace (𝓡 2) x)
          (TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ))) := by
    calc
      _ = mfderiv (𝓡 2) CylinderI
          (projectiveSlice ∘ SphereAntipodalQuotient.proj) x :=
        (mfderiv_comp x (contMDiff_projectiveSlice.mdifferentiableAt (by decide))
          (SphereAntipodalQuotient.isLocalDiffeomorph_proj.contMDiff.mdifferentiableAt
            (by decide))).symm
      _ = mfderiv (𝓡 2) CylinderI (proj ∘ (fun z : SphereTwo => (z, (0 : ℝ)))) x := rfl
      _ = _ := by
        rw [mfderiv_comp x (isLocalDiffeomorph_proj.contMDiff.mdifferentiableAt (by decide))
          (show MDifferentiableAt (𝓡 2) CylinderI
            (fun z : SphereTwo => (z, (0 : ℝ))) x from
              mdifferentiableAt_id.prodMk mdifferentiableAt_const), mfderiv_prod_left]
  intro v w hvw
  obtain ⟨a, rfl⟩ := A.surjective v
  obtain ⟨b, rfl⟩ := A.surjective w
  have hab : B (a, 0) = B (b, 0) := by
    change (mfderiv CylinderI CylinderI proj (x, 0)) (a, 0) =
      (mfderiv CylinderI CylinderI proj (x, 0)) (b, 0)
    have ha := congrArg (fun L => L a) hder
    have hb := congrArg (fun L => L b) hder
    exact ha.symm.trans (hvw.trans hb)
  exact congrArg A (congrArg Prod.fst (B.injective hab))


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

theorem isSmoothEmbedding_zeroSlice : IsSmoothEmbedding (𝓡 2) CylinderI ∞ zeroSlice := by
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv
    (by decide) (contMDiff_id.prodMk contMDiff_const) ?_, isClosedEmbedding_zeroSlice.isEmbedding⟩
  intro x
  change Function.Injective (mfderiv (𝓡 2) CylinderI (fun q : SphereAntipodalQuotient =>
    (q, (0 : ℝ))) x)
  rw [mfderiv_prod_left]
  exact fun _ _ h => congrArg Prod.fst h


end SphereAntipodalQuotient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

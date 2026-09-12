
import DifferentialGeometry.Analysis.Integration.Measure.ModelHaar
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Determinant

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Module
open scoped ENNReal

namespace DifferentialGeometry
namespace Integral
namespace Measure

open Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private local instance instE : MeasurableSpace E := borel E
private local instance instEB : BorelSpace E := ⟨rfl⟩

noncomputable def finrankProdRealEquiv :
    Fin (Module.finrank ℝ (E × ℝ)) ≃ Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ ℝ) :=
  (finCongr (Module.finrank_prod (M := E) (M' := ℝ))).trans finSumFinEquiv.symm

theorem addHaar_chartModelBasis_prod_real :
    ENNReal.ofReal |(((chartModelBasis E).prod (chartModelBasis ℝ)).det
        ((chartModelBasis (E × ℝ)).reindex (finrankProdRealEquiv (E := E))))| •
        ((chartModelBasis (E × ℝ)).addHaar) =
      (modelHaar (E := E)).prod (modelHaar (E := ℝ)) := by
  have h := Module.Basis.det_smul_addHaar ((chartModelBasis E).prod (chartModelBasis ℝ))
    ((chartModelBasis (E × ℝ)).reindex (finrankProdRealEquiv (E := E)))
  rw [Module.Basis.addHaar_reindex, Module.Basis.prod_addHaar] at h
  exact h

theorem cast_smul_measure {X : Type*} {m₁ m₂ : MeasurableSpace X} (hm : m₁ = m₂)
    (c : ℝ≥0∞) (μ : @Measure X m₁) :
    cast (congrArg (fun m : MeasurableSpace X => @Measure X m) hm) (c • μ) =
      c • cast (congrArg (fun m : MeasurableSpace X => @Measure X m) hm) μ := by
  cases hm
  rfl

theorem cast_addHaar {ι X : Type*} [Fintype ι] [NormedAddCommGroup X]
    [NormedSpace ℝ X] {m₁ m₂ : MeasurableSpace X} (hm : m₁ = m₂)
    (b₁ : @BorelSpace X _ m₁) (b₂ : @BorelSpace X _ m₂) (b : Basis ι ℝ X) :
    cast (congrArg (fun m : MeasurableSpace X => @Measure X m) hm)
        (@Module.Basis.addHaar ι X _ _ _ m₁ b₁ b) =
      @Module.Basis.addHaar ι X _ _ _ m₂ b₂ b := by
  let _ := b₁
  let _ := b₂
  cases hm
  rfl

theorem modelHaar_prod_real :
    cast (congrArg (fun m : MeasurableSpace (E × ℝ) => @Measure (E × ℝ) m)
        (@BorelSpace.measurable_eq (E × ℝ) _
          (@Prod.instMeasurableSpace E ℝ _ _) (Prod.borelSpace)))
      ((modelHaar (E := E)).prod (modelHaar (E := ℝ))) =
    ENNReal.ofReal |(((chartModelBasis E).prod (chartModelBasis ℝ)).det
        ((chartModelBasis (E × ℝ)).reindex (finrankProdRealEquiv (E := E))))| •
      modelHaar (E := E × ℝ) := by
  have h := addHaar_chartModelBasis_prod_real (E := E)
  have h1 := congrArg
    (cast (congrArg (fun m : MeasurableSpace (E × ℝ) => @Measure (E × ℝ) m)
      (@BorelSpace.measurable_eq (E × ℝ) _
        (@Prod.instMeasurableSpace E ℝ _ _) (Prod.borelSpace)))) h
  rw [cast_smul_measure] at h1
  · rw [cast_addHaar] at h1
    · exact h1.symm
    · exact (Prod.borelSpace).measurable_eq
  · exact (Prod.borelSpace).measurable_eq

end Measure
end Integral
end DifferentialGeometry

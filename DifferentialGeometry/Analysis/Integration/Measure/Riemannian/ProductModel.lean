import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Product

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Module
open scoped ENNReal

namespace DifferentialGeometry.Integral.Measure

open Tensor.Coordinates

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private local instance instE : MeasurableSpace E := borel E
private local instance instEB : BorelSpace E := ⟨rfl⟩
private local instance instF : MeasurableSpace F := borel F
private local instance instFB : BorelSpace F := ⟨rfl⟩

noncomputable def finrankProdEquiv :
    Fin (Module.finrank ℝ (E × F)) ≃ Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ F) :=
  (finCongr (Module.finrank_prod (M := E) (M' := F))).trans finSumFinEquiv.symm

theorem addHaar_chartModelBasis_prod :
    ENNReal.ofReal |(((chartModelBasis E).prod (chartModelBasis F)).det
        ((chartModelBasis (E × F)).reindex (finrankProdEquiv (E := E) (F := F))))| •
        ((chartModelBasis (E × F)).addHaar) =
      (modelHaar (E := E)).prod (modelHaar (E := F)) := by
  have h := Module.Basis.det_smul_addHaar ((chartModelBasis E).prod (chartModelBasis F))
    ((chartModelBasis (E × F)).reindex (finrankProdEquiv (E := E) (F := F)))
  rw [Module.Basis.addHaar_reindex, Module.Basis.prod_addHaar] at h
  exact h

theorem modelHaar_prod :
    cast (congrArg (fun m : MeasurableSpace (E × F) => @Measure (E × F) m)
        (@BorelSpace.measurable_eq (E × F) _
          (@Prod.instMeasurableSpace E F _ _) (Prod.borelSpace)))
      ((modelHaar (E := E)).prod (modelHaar (E := F))) =
    ENNReal.ofReal |(((chartModelBasis E).prod (chartModelBasis F)).det
        ((chartModelBasis (E × F)).reindex (finrankProdEquiv (E := E) (F := F))))| •
      modelHaar (E := E × F) := by
  have h := addHaar_chartModelBasis_prod (E := E) (F := F)
  have h1 := congrArg
    (cast (congrArg (fun m : MeasurableSpace (E × F) => @Measure (E × F) m)
      (@BorelSpace.measurable_eq (E × F) _
        (@Prod.instMeasurableSpace E F _ _) (Prod.borelSpace)))) h
  rw [cast_smul_measure] at h1
  · rw [cast_addHaar] at h1
    · exact h1.symm
    · exact (Prod.borelSpace).measurable_eq
  · exact (Prod.borelSpace).measurable_eq

end DifferentialGeometry.Integral.Measure

import DifferentialGeometry.Analysis.Schauder.CutoffProduct

noncomputable section

namespace DifferentialGeometry.Analysis.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

def cutoffValueSupConst
    (chi : BoundedContinuousFunction V Real)
    (u : BoundedContinuousFunction V F) : NNReal :=
  ‖chi‖₊ * ‖u‖₊

omit [NormedSpace Real V] in
theorem norm_cutoffValue_le
    (chi : BoundedContinuousFunction V Real)
    (u : BoundedContinuousFunction V F) :
    ‖cutoffValue chi u‖ ≤ cutoffValueSupConst chi u := by
  simpa only [cutoffValue, cutoffValueSupConst, NNReal.coe_mul,
    coe_nnnorm] using norm_smul_le chi u

def cutoffValueHolderConst
    (Kchi Ku : NNReal)
    (chi : BoundedContinuousFunction V Real)
    (u : BoundedContinuousFunction V F) : NNReal :=
  ‖chi‖₊ * Ku + ‖u‖₊ * Kchi

omit [NormedSpace Real V] in
theorem cutoffValue_holderWith
    {alpha Kchi Ku : NNReal}
    (chi : BoundedContinuousFunction V Real)
    (u : BoundedContinuousFunction V F)
    (hchi : HolderWith Kchi alpha (chi : V → Real))
    (hu : HolderWith Ku alpha (u : V → F)) :
    HolderWith (cutoffValueHolderConst Kchi Ku chi u) alpha
      (cutoffValue chi u : V → F) := by
  simpa only [cutoffValueHolderConst, cutoffValue_apply] using
    holderWith_smul_of_norm_le hchi hu
      (fun x ↦ by simpa using chi.norm_coe_le_norm x)
      (fun x ↦ by simpa using u.norm_coe_le_norm x)

end DifferentialGeometry.Analysis.Schauder

end

import DifferentialGeometry.Topology.Homotopy.CubePrismImage
import Mathlib.Topology.Homotopy.Basic



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology



def cubePrismDeformation (n : ℕ) :
    (ContinuousMap.id (unitInterval × (Fin (n + 1) → unitInterval))).HomotopyRel
      ⟨cubePrismRetract n, continuous_cubePrismRetract n⟩
        {z | z.1 = 0 ∨ z.2 ∈ Cube.boundary (Fin (n + 1))} where
  toFun z := (Set.Icc.convexComb z.2.1 (cubePrismRetract n z.2).1 z.1,
    fun i => Set.Icc.convexComb (z.2.2 i) ((cubePrismRetract n z.2).2 i) z.1)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact Set.Icc.continuous_convexComb_prod.comp
        ((continuous_fst.comp continuous_snd).prodMk
          (((continuous_cubePrismRetract n).fst.comp continuous_snd).prodMk continuous_fst))
    · apply continuous_pi
      intro i
      exact Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (continuous_snd.comp continuous_snd)).prodMk
          ((((continuous_apply i).comp (continuous_cubePrismRetract n).snd).comp
            continuous_snd).prodMk continuous_fst))
  map_zero_left z := by
    simp only [Set.Icc.convexComb_zero]
    rfl
  map_one_left z := by
    simp only [Set.Icc.convexComb_one]
    rfl
  prop' s z hz := by
    have hR : cubePrismRetract n z = z := by
      rcases hz with hz | hz
      · have heq : z = (0, z.2) := Prod.ext hz rfl
        rw [heq]
        exact cubePrismRetract_bottom n _
      · exact cubePrismRetract_side n z.1 z.2 hz
    change (Set.Icc.convexComb z.1 (cubePrismRetract n z).1 s,
      fun i => Set.Icc.convexComb (z.2 i) ((cubePrismRetract n z).2 i) s) = z
    simp only [hR, Set.Icc.convexComb_eq]

end DifferentialGeometry.Topology

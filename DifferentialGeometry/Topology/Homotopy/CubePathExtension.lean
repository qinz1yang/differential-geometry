import DifferentialGeometry.Topology.Homotopy.CubePrismImage
import DifferentialGeometry.Topology.Homotopy.LoopTopology
import Mathlib.Topology.Piecewise







noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x y : X}



def cubePathExtension (n : ℕ) (p : Path x y) (Γ : GenLoop (Fin (n + 1)) X x)
    (z : unitInterval × (Fin (n + 1) → unitInterval)) : X :=
  if cubeRadius n z.2 ≤ 1 - z.1.val / 2 then Γ (cubePrismRetract n z).2
  else p (cubePrismRetract n z).1


theorem cubePathExtension_interface (n : ℕ) (p : Path x y) (Γ : GenLoop (Fin (n + 1)) X x)
    (z : unitInterval × (Fin (n + 1) → unitInterval))
    (hz : cubeRadius n z.2 = 1 - z.1.val / 2) :
    Γ (cubePrismRetract n z).2 = p (cubePrismRetract n z).1 := by
  rw [GenLoop.boundary Γ _ (cubePrismRetract_position_boundary n z hz.ge),
    cubePrismRetract_time_zero n z hz.le, p.source]



theorem continuous_cubePathExtension (n : ℕ) (p : Path x y)
    (Γ : GenLoop (Fin (n + 1)) X x) : Continuous (cubePathExtension n p Γ) := by
  apply Continuous.if
  · intro z hz
    have heq := frontier_le_subset_eq
      ((continuous_cubeRadius n).comp continuous_snd)
      (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)) hz
    exact cubePathExtension_interface n p Γ z heq
  · exact Γ.val.continuous.comp (continuous_cubePrismRetract n).snd
  · exact p.continuous.comp (continuous_cubePrismRetract n).fst


theorem cubePathExtension_zero (n : ℕ) (p : Path x y) (Γ : GenLoop (Fin (n + 1)) X x)
    (v : Fin (n + 1) → unitInterval) : cubePathExtension n p Γ (0, v) = Γ v := by
  have hc : cubeRadius n v ≤ 1 - (0 : ℝ) / 2 := by
    simpa only [zero_div, sub_zero] using cubeRadius_le_one n v
  change (if cubeRadius n v ≤ 1 - (0 : ℝ) / 2 then Γ (cubePrismRetract n (0, v)).2
    else p (cubePrismRetract n (0, v)).1) = Γ v
  rw [if_pos hc, cubePrismRetract_bottom]



theorem cubePathExtension_boundary (n : ℕ) (p : Path x y)
    (Γ : GenLoop (Fin (n + 1)) X x) (t : unitInterval)
    (v : Fin (n + 1) → unitInterval) (hv : v ∈ Cube.boundary (Fin (n + 1))) :
    cubePathExtension n p Γ (t, v) = p t := by
  unfold cubePathExtension
  rw [cubePrismRetract_side n t v hv]
  split_ifs with h
  · have hrad := (cubeRadius_eq_one_iff n v).mpr hv
    have ht : t = 0 := Subtype.ext (show t.val = (0 : ℝ) by
      have ht0 := t.property.1
      change cubeRadius n v ≤ 1 - t.val / 2 at h
      rw [hrad] at h
      linarith)
    rw [ht, p.source, GenLoop.boundary Γ v hv]
  · rfl


def genLoopTransport (n : ℕ) (p : Path x y) (Γ : GenLoop (Fin (n + 1)) X x) :
    GenLoop (Fin (n + 1)) X y :=
  ⟨⟨fun v => cubePathExtension n p Γ (1, v),
    (continuous_cubePathExtension n p Γ).comp (continuous_const.prodMk continuous_id)⟩,
    fun v hv => (cubePathExtension_boundary n p Γ 1 v hv).trans p.target⟩

end DifferentialGeometry.Topology

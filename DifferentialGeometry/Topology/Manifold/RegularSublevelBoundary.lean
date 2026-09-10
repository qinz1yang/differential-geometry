/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Morse.RegularLevel.Sublevel

set_option autoImplicit false

open Set
open scoped Manifold Topology

noncomputable section

namespace DifferentialGeometry.Topology.Morse

variable {m : ℕ} {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)

theorem manifoldSublevelBoundary_iff_mem_levelSet [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x : SublevelSpace f a) :
    @ModelWithCorners.IsBoundaryPoint ℝ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (SublevelSpace f a) _ (manifoldSublevelChartedSpace I f a hf hreg) x ↔
      f x.1 = a := by
  classical
  let _ : ChartedSpace (MorseHalfSpace m) (SublevelSpace f a) :=
    manifoldSublevelChartedSpace I f a hf hreg
  rw [@ModelWithCorners.isBoundaryPoint_iff ℝ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (SublevelSpace f a) _ (manifoldSublevelChartedSpace I f a hf hreg)]
  rw [frontier_morseHalfSpace_range]
  constructor
  · intro hx
    by_contra hxne
    have hlt : f x.1 < a := lt_of_le_of_ne (show f x.1 ≤ a from x.2) hxne
    have hchart : chartAt (MorseHalfSpace m) x =
        manifoldSublevelInteriorChart I f a x hlt hf := by
      change (if h : f x.1 = a then manifoldSublevelBoundaryChart I f a x h hf hreg
        else manifoldSublevelInteriorChart I f a x
          (lt_of_le_of_ne (show f x.1 ≤ a from x.2) h) hf) =
        manifoldSublevelInteriorChart I f a x hlt hf
      rw [dif_neg hxne]
    change (chartAt (MorseHalfSpace m) x).extend
      (morseModelWithCornersHalfSpace m) x ∈
        {w : MorseModel (m + 1) | w (Fin.last m) = 0} at hx
    rw [hchart] at hx
    have hpos := manifoldSublevelInteriorChart_extend_last_pos I f a hf x hlt
    have hzero :
        (manifoldSublevelInteriorChart I f a x hlt hf).extend
          (morseModelWithCornersHalfSpace m) x (Fin.last m) = 0 := by
      change (manifoldSublevelInteriorChart I f a x hlt hf).extend
        (morseModelWithCornersHalfSpace m) x ∈
          {w : MorseModel (m + 1) | w (Fin.last m) = 0} at hx
      exact hx
    rw [OpenPartialHomeomorph.extend_coe] at hzero
    change (manifoldSublevelInteriorChart I f a x hlt hf x :
      MorseModel (m + 1)) (Fin.last m) = 0 at hzero
    linarith
  · intro hx
    have hchart : chartAt (MorseHalfSpace m) x =
        manifoldSublevelBoundaryChart I f a x hx hf hreg := by
      change (if h : f x.1 = a then manifoldSublevelBoundaryChart I f a x h hf hreg
        else manifoldSublevelInteriorChart I f a x
          (lt_of_le_of_ne (show f x.1 ≤ a from x.2) h) hf) =
        manifoldSublevelBoundaryChart I f a x hx hf hreg
      rw [dif_pos hx]
    change (chartAt (MorseHalfSpace m) x).extend
      (morseModelWithCornersHalfSpace m) x ∈
        {w : MorseModel (m + 1) | w (Fin.last m) = 0}
    rw [hchart]
    have hzero := manifoldSublevelBoundaryChart_extend_last_zero I f a hf hreg x hx
    change (manifoldSublevelBoundaryChart I f a x hx hf hreg x :
      MorseModel (m + 1)) (Fin.last m) = 0
    exact hzero

end DifferentialGeometry.Topology.Morse

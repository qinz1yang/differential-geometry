import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter Topology

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normal_coefficient_nonneg_at_lower
    {a b : ℝ} (hab : a < b) (F : ℝ × E → ℝ × E)
    (L : (ℝ × E) →L[ℝ] (ℝ × E)) (z : E)
    (hF : HasFDerivWithinAt F L (Icc a b ×ˢ univ) (a, z))
    (hbound : ∀ q ∈ Icc a b ×ˢ (univ : Set E), (F q).1 ∈ Icc a b)
    (hface : (F (a, z)).1 = a) : 0 ≤ (L (1, 0)).1 := by
  have hmin : IsLocalMinOn (fun q ↦ (F q).1) (Icc a b ×ˢ (univ : Set E)) (a, z) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    change (F (a, z)).1 ≤ (F q).1
    rw [hface]
    exact (hbound q hq).1
  have ht : (1, (0 : E)) ∈ posTangentConeAt (Icc a b ×ˢ (univ : Set E)) (a, z) := by
    apply mem_posTangentConeAt_of_frequently_mem
    have he : ∀ᶠ t : ℝ in 𝓝[>] 0, (a, z) + t • (1, (0 : E)) ∈ Icc a b ×ˢ univ := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds (sub_pos.mpr hab))] with t hpos hsmall
      change 0 < t at hpos
      change t < b - a at hsmall
      refine ⟨?_, mem_univ _⟩
      change a ≤ a + t * 1 ∧ a + t * 1 ≤ b
      constructor <;> linarith
    exact he.frequently
  have hd := (show HasFDerivAt (Prod.fst : ℝ × E → ℝ)
    (ContinuousLinearMap.fst ℝ ℝ E) (F (a, z)) from hasFDerivAt_fst).comp_hasFDerivWithinAt (a, z) hF
  exact hmin.hasFDerivWithinAt_nonneg hd ht

theorem normal_coefficient_nonneg_at_upper
    {a b : ℝ} (hab : a < b) (F : ℝ × E → ℝ × E)
    (L : (ℝ × E) →L[ℝ] (ℝ × E)) (z : E)
    (hF : HasFDerivWithinAt F L (Icc a b ×ˢ univ) (b, z))
    (hbound : ∀ q ∈ Icc a b ×ˢ (univ : Set E), (F q).1 ∈ Icc a b)
    (hface : (F (b, z)).1 = b) : 0 ≤ (L (1, 0)).1 := by
  have hmax : IsLocalMaxOn (fun q ↦ (F q).1) (Icc a b ×ˢ (univ : Set E)) (b, z) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    change (F q).1 ≤ (F (b, z)).1
    rw [hface]
    exact (hbound q hq).2
  have ht : (-1, (0 : E)) ∈ posTangentConeAt (Icc a b ×ˢ (univ : Set E)) (b, z) := by
    apply mem_posTangentConeAt_of_frequently_mem
    have he : ∀ᶠ t : ℝ in 𝓝[>] 0, (b, z) + t • (-1, (0 : E)) ∈ Icc a b ×ˢ univ := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds (sub_pos.mpr hab))] with t hpos hsmall
      change 0 < t at hpos
      change t < b - a at hsmall
      refine ⟨?_, mem_univ _⟩
      change a ≤ b + t * (-1) ∧ b + t * (-1) ≤ b
      constructor <;> linarith
    exact he.frequently
  have hd := (show HasFDerivAt (Prod.fst : ℝ × E → ℝ)
    (ContinuousLinearMap.fst ℝ ℝ E) (F (b, z)) from hasFDerivAt_fst).comp_hasFDerivWithinAt (b, z) hF
  have h := hmax.hasFDerivWithinAt_nonpos hd ht
  change (L (-1, 0)).1 ≤ 0 at h
  have heq : ((-1 : ℝ), (0 : E)) = -(1, (0 : E)) := by simp
  rw [heq, map_neg] at h
  exact neg_nonpos.mp h

theorem horizontal_derivative_of_face_eq
    {a b r : ℝ} (hr : r ∈ Icc a b) (F : ℝ × E → ℝ × E) (f : E → E)
    (L : (ℝ × E) →L[ℝ] (ℝ × E)) (A : E →L[ℝ] E) (z : E)
    (hF : HasFDerivWithinAt F L (Icc a b ×ˢ univ) (r, z))
    (hf : HasFDerivAt f A z) (hface : ∀ w, F (r, w) = (r, f w)) :
    ∀ w, L (0, w) = (0, A w) := by
  have hin : HasFDerivAt (fun w : E ↦ (r, w)) (ContinuousLinearMap.inr ℝ ℝ E) z :=
    (hasFDerivAt_const r z).prodMk (hasFDerivAt_id z)
  have hcomp := (hF.comp z hin.hasFDerivWithinAt
    (show MapsTo (fun w : E ↦ (r, w)) univ (Icc a b ×ˢ univ) from fun _ _ ↦ ⟨hr, mem_univ _⟩)).hasFDerivAt_of_univ
  have heq : F ∘ (fun w : E ↦ (r, w)) = (fun w ↦ (r, f w)) := funext hface
  rw [heq] at hcomp
  have hder := hcomp.unique ((hasFDerivAt_const r z).prodMk hf)
  intro w
  exact congrArg (fun B : E →L[ℝ] (ℝ × E) ↦ B w) hder

end Poincare.Analysis

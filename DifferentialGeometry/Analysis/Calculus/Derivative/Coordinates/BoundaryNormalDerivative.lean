import DifferentialGeometry.Tensor.LinearAlgebra.BoundaryBlockDeterminant
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter Topology

namespace DifferentialGeometry.Analysis

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

theorem normal_coefficient_nonneg_of_eventually_le
    {F : ℝ × E → ℝ × E} {L : (ℝ × E) →L[ℝ] (ℝ × E)} {a : ℝ} {z : E}
    (hF : HasFDerivAt F L (a, z)) (hface : (F (a, z)).1 = a)
    (hbound : ∀ᶠ q in 𝓝 (a, z), q.1 ≤ a → (F q).1 ≤ a) :
    0 ≤ (L (1, 0)).1 := by
  have hmax : IsLocalMaxOn (fun q => (F q).1) (Iic a ×ˢ (univ : Set E)) (a, z) := by
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hbound]
      with q hq hqbound
    change (F q).1 ≤ (F (a, z)).1
    rw [hface]
    exact hqbound hq.1
  have ht : (-1, (0 : E)) ∈ posTangentConeAt (Iic a ×ˢ (univ : Set E)) (a, z) := by
    apply mem_posTangentConeAt_of_frequently_mem
    have he : ∀ᶠ t : ℝ in 𝓝[>] 0, (a, z) + t • (-1, (0 : E)) ∈ Iic a ×ˢ univ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      refine ⟨?_, mem_univ _⟩
      change a + t * (-1) ≤ a
      change 0 < t at ht
      linarith
    exact he.frequently
  have hd := (show HasFDerivAt (Prod.fst : ℝ × E → ℝ)
    (ContinuousLinearMap.fst ℝ ℝ E) (F (a, z)) from hasFDerivAt_fst).comp (a, z) hF
  have h := hmax.hasFDerivWithinAt_nonpos hd.hasFDerivWithinAt ht
  change (L (-1, 0)).1 ≤ 0 at h
  have heq : ((-1 : ℝ), (0 : E)) = -(1, (0 : E)) := by simp
  rw [heq, map_neg] at h
  exact neg_nonpos.mp h

theorem horizontal_derivative_of_eventuallyEq_face
    {F : ℝ × E → ℝ × E} {f : E → E}
    {L : (ℝ × E) →L[ℝ] (ℝ × E)} {A : E →L[ℝ] E} {a : ℝ} {z : E}
    (hF : HasFDerivAt F L (a, z)) (hf : HasFDerivAt f A z)
    (hface : (fun w => F (a, w)) =ᶠ[𝓝 z] fun w => (a, f w)) :
    ∀ w, L (0, w) = (0, A w) := by
  have hin : HasFDerivAt (fun w : E => (a, w)) (ContinuousLinearMap.inr ℝ ℝ E) z :=
    (hasFDerivAt_const a z).prodMk (hasFDerivAt_id z)
  have hder := ((hF.comp z hin).congr_of_eventuallyEq hface.symm).unique
    ((hasFDerivAt_const a z).prodMk hf)
  intro w
  exact congrArg (fun B : E →L[ℝ] (ℝ × E) => B w) hder

theorem det_pos_iff_horizontal_of_eventually_le [FiniteDimensional ℝ E]
    {F : ℝ × E → ℝ × E} {f : E → E}
    {L : (ℝ × E) →L[ℝ] (ℝ × E)} {A : E →L[ℝ] E} {a : ℝ} {z : E}
    (hF : HasFDerivAt F L (a, z)) (hf : HasFDerivAt f A z)
    (hface : (fun w => F (a, w)) =ᶠ[𝓝 z] fun w => (a, f w))
    (hL : Function.Surjective L)
    (hbound : ∀ᶠ q in 𝓝 (a, z), q.1 ≤ a → (F q).1 ≤ a) :
    0 < L.det ↔ 0 < A.det := by
  exact det_pos_iff_horizontal_of_surjective L.toLinearMap A.toLinearMap
    (horizontal_derivative_of_eventuallyEq_face hF hf hface) hL
    (normal_coefficient_nonneg_of_eventually_le hF (congrArg Prod.fst hface.eq_of_nhds) hbound)

theorem normal_derivative_pos_of_eventually_nonneg
    {f : ℝ × E → ℝ} {L : (ℝ × E) →L[ℝ] ℝ} {a : ℝ} {x : E}
    (hf : HasFDerivAt f L (a, x)) (hL : L ≠ 0)
    (hface : (fun y => f (a, y)) =ᶠ[𝓝 x] fun _ => 0)
    (hside : ∀ᶠ p in 𝓝 (a, x), a ≤ p.1 → 0 ≤ f p) :
    0 < L (1, 0) := by
  have hmin : IsLocalMinOn f (Ici a ×ˢ (univ : Set E)) (a, x) := by
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hside]
      with p hp hs
    rw [hface.eq_of_nhds]
    exact hs hp.1
  have ht : (1, (0 : E)) ∈ posTangentConeAt (Ici a ×ˢ (univ : Set E)) (a, x) := by
    apply mem_posTangentConeAt_of_frequently_mem
    have he : ∀ᶠ t : ℝ in 𝓝[>] 0, (a, x) + t • (1, (0 : E)) ∈ Ici a ×ˢ univ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact ⟨by change a ≤ a + t * 1; change 0 < t at ht; linarith, mem_univ _⟩
    exact he.frequently
  have hnonneg : 0 ≤ L (1, 0) := hmin.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt ht
  have hin : HasFDerivAt (fun y : E => (a, y)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
    (hasFDerivAt_const a x).prodMk (hasFDerivAt_id x)
  have hder := ((hf.comp x hin).congr_of_eventuallyEq hface.symm).unique
    (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x)
  have hzero (v : E) : L (0, v) = 0 :=
    congrArg (fun A : E →L[ℝ] ℝ => A v) hder
  apply lt_of_le_of_ne hnonneg
  intro h
  apply hL
  apply ContinuousLinearMap.ext
  intro p
  rw [show p = p.1 • (1, (0 : E)) + (0, p.2) from by ext <;> simp, map_add,
    map_smul, hzero, ← h]
  simp

open Metric in
theorem fderiv_norm_sq_apply_neg_of_eventually_mem_closedBall
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {g : ℝ × E → F} {L : (ℝ × E) →L[ℝ] F}
    {a : ℝ} {x : E} {r : ℝ} {d : F}
    (hg : HasFDerivAt g L (a, x)) (hL : Function.Surjective L) (hr : 0 < r)
    (hface : ∀ᶠ y in 𝓝 x, g (a, y) ∈ sphere d r)
    (hside : ∀ᶠ p in 𝓝 (a, x), a ≤ p.1 → g p ∈ closedBall d r) :
    fderiv ℝ (fun p => ‖g p - d‖ ^ 2) (a, x) (1, 0) < 0 := by
  have hnorm : ‖g (a, x) - d‖ = r := by
    simpa only [mem_sphere, dist_eq_norm] using hface.self_of_nhds
  have hne : 2 • (innerSL ℝ (g (a, x) - d)).comp L ≠ 0 := by
    intro hzero
    obtain ⟨v, hv⟩ := hL (g (a, x) - d)
    have hh := congrArg (fun A : (ℝ × E) →L[ℝ] ℝ => A v) hzero
    simp only [two_smul, add_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, zero_apply, hv, real_inner_self_eq_norm_sq, hnorm] at hh
    nlinarith
  have hd := (hg.sub_const d).norm_sq
  have hpos : 0 < (-(2 • (innerSL ℝ (g (a, x) - d)).comp L)) (1, 0) := by
    apply normal_derivative_pos_of_eventually_nonneg (hd.const_sub (r ^ 2))
      (neg_ne_zero.mpr hne)
    · filter_upwards [hface] with y hy
      have hy' : ‖g (a, y) - d‖ = r := by
        simpa only [mem_sphere, dist_eq_norm] using hy
      simp only [hy', sub_self]
    · filter_upwards [hside] with p hp ha
      exact sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) hr.le).mpr
        (by simpa only [mem_closedBall, dist_eq_norm] using hp ha))
  rw [hd.fderiv]
  exact neg_pos.mp hpos

end DifferentialGeometry.Analysis

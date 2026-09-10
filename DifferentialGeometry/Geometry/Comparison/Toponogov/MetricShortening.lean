/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Geometry.Comparison.Toponogov.MetricComparisonAngle
import DifferentialGeometry.Geometry.Comparison.Toponogov.Convexity

set_option autoImplicit false

noncomputable section

open Set

namespace Poincare.Toponogov

def RadialOn {X : Type*} [PseudoMetricSpace X]
    (o : X) (curve : ℝ → X) (T : ℝ) : Prop :=
  ∀ r ∈ Icc (0 : ℝ) T, dist o (curve r) = r


def squaredDistanceDefect {X : Type*} [PseudoMetricSpace X]
    (α β : ℝ → X) (s t : ℝ) : ℝ :=
  s ^ 2 + t ^ 2 - dist (α s) (β t) ^ 2

theorem radial_sideInequalities {X : Type*} [PseudoMetricSpace X]
    {o : X} {α β : ℝ → X} {s t : ℝ}
    (hαs : dist o (α s) = s) (hβt : dist o (β t) = t) :
    |s - t| ≤ dist (α s) (β t) ∧
      dist (α s) (β t) ≤ s + t := by
  simpa only [hαs, hβt] using
    metricComparisonAngle_sideInequalities (α s) o (β t)

theorem cos_metricComparisonAngle_of_radial
    {X : Type*} [PseudoMetricSpace X]
    {o : X} {α β : ℝ → X} {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t)
    (hαs : dist o (α s) = s) (hβt : dist o (β t) = t) :
    Real.cos (metricComparisonAngle (α s) o (β t)) =
      squaredDistanceDefect α β s t / (2 * s * t) := by
  have hside := radial_sideInequalities hαs hβt
  rw [metricComparisonAngle, hαs, hβt,
    cos_comparisonAngle hs ht hside.1 hside.2,
    comparisonCosine]
  rfl

theorem metricComparisonAngle_antitone_fst_of_convex_defect
    {X : Type*} [MetricSpace X] {o : X} {α β : ℝ → X}
    {A B s₁ s₂ t : ℝ}
    (hA : 0 < A)
    (hα : RadialOn o α A) (hβ : RadialOn o β B)
    (hconvex : ∀ t ∈ Icc (0 : ℝ) B,
      ConvexOn ℝ (Icc (0 : ℝ) A)
        (fun s ↦ squaredDistanceDefect α β s t))
    (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂) (hs₂A : s₂ ≤ A)
    (ht : 0 < t) (htB : t ≤ B) :
    metricComparisonAngle (α s₂) o (β t) ≤
      metricComparisonAngle (α s₁) o (β t) := by
  have hs₂ : 0 < s₂ := hs₁.trans_le hs₁₂
  have hs₁A : s₁ ≤ A := hs₁₂.trans hs₂A
  have hα0 : dist o (α 0) = 0 := hα 0 ⟨le_rfl, hA.le⟩
  have hαzero : α 0 = o := (dist_eq_zero.mp hα0).symm
  have hβt : dist o (β t) = t := hβ t ⟨ht.le, htB⟩
  have hzero : squaredDistanceDefect α β 0 t = 0 := by
    simp [squaredDistanceDefect, hαzero, hβt]
  have hquotient :
      squaredDistanceDefect α β s₁ t / s₁ ≤
        squaredDistanceDefect α β s₂ t / s₂ :=
    convex_div_mono_of_zero hA (hconvex t ⟨ht.le, htB⟩) hzero
      hs₁ hs₁₂ hs₂A
  have hscaled :
      squaredDistanceDefect α β s₁ t / (2 * s₁ * t) ≤
        squaredDistanceDefect α β s₂ t / (2 * s₂ * t) := by
    calc
      squaredDistanceDefect α β s₁ t / (2 * s₁ * t) =
          (squaredDistanceDefect α β s₁ t / s₁) / (2 * t) := by ring
      _ ≤ (squaredDistanceDefect α β s₂ t / s₂) / (2 * t) :=
        div_le_div_of_nonneg_right hquotient (by positivity)
      _ = squaredDistanceDefect α β s₂ t / (2 * s₂ * t) := by ring
  have hαs₁ : dist o (α s₁) = s₁ := hα s₁ ⟨hs₁.le, hs₁A⟩
  have hαs₂ : dist o (α s₂) = s₂ := hα s₂ ⟨hs₂.le, hs₂A⟩
  have hcos :
      Real.cos (metricComparisonAngle (α s₁) o (β t)) ≤
        Real.cos (metricComparisonAngle (α s₂) o (β t)) := by
    rw [cos_metricComparisonAngle_of_radial hs₁ ht hαs₁ hβt,
      cos_metricComparisonAngle_of_radial hs₂ ht hαs₂ hβt]
    exact hscaled
  have hθ1 : metricComparisonAngle (α s₁) o (β t) ∈
      Icc (0 : ℝ) Real.pi := by
    exact comparisonAngle_mem_Icc _ _ _
  have hθ2 : metricComparisonAngle (α s₂) o (β t) ∈
      Icc (0 : ℝ) Real.pi := by
    exact comparisonAngle_mem_Icc _ _ _
  rw [← Real.arccos_cos hθ2.1 hθ2.2,
    ← Real.arccos_cos hθ1.1 hθ1.2]
  exact Real.arccos_le_arccos hcos

theorem metricComparisonAngle_antitoneOn_fst_of_convex_defect
    {X : Type*} [MetricSpace X] {o : X} {α β : ℝ → X}
    {A B t : ℝ}
    (hA : 0 < A)
    (hα : RadialOn o α A) (hβ : RadialOn o β B)
    (hconvex : ∀ t ∈ Icc (0 : ℝ) B,
      ConvexOn ℝ (Icc (0 : ℝ) A)
        (fun s ↦ squaredDistanceDefect α β s t))
    (ht : t ∈ Ioc (0 : ℝ) B) :
    AntitoneOn (fun s ↦ metricComparisonAngle (α s) o (β t))
      (Ioc (0 : ℝ) A) := by
  intro s₁ hs₁ s₂ hs₂ hs₁s₂
  exact metricComparisonAngle_antitone_fst_of_convex_defect
    hA hα hβ hconvex hs₁.1 hs₁s₂ hs₂.2 ht.1 ht.2

theorem metricComparisonAngle_antitone_snd_of_convex_defect
    {X : Type*} [MetricSpace X] {o : X} {α β : ℝ → X}
    {A B s t₁ t₂ : ℝ}
    (hB : 0 < B)
    (hα : RadialOn o α A) (hβ : RadialOn o β B)
    (hconvex : ∀ s ∈ Icc (0 : ℝ) A,
      ConvexOn ℝ (Icc (0 : ℝ) B)
        (fun t ↦ squaredDistanceDefect α β s t))
    (hs : 0 < s) (hsA : s ≤ A)
    (ht₁ : 0 < t₁) (ht₁t₂ : t₁ ≤ t₂) (ht₂B : t₂ ≤ B) :
    metricComparisonAngle (α s) o (β t₂) ≤
      metricComparisonAngle (α s) o (β t₁) := by
  have ht₂ : 0 < t₂ := ht₁.trans_le ht₁t₂
  have ht₁B : t₁ ≤ B := ht₁t₂.trans ht₂B
  have hβ0 : dist o (β 0) = 0 := hβ 0 ⟨le_rfl, hB.le⟩
  have hβzero : β 0 = o := (dist_eq_zero.mp hβ0).symm
  have hαs : dist o (α s) = s := hα s ⟨hs.le, hsA⟩
  have hzero : squaredDistanceDefect α β s 0 = 0 := by
    simp [squaredDistanceDefect, hβzero, dist_comm, hαs]
  have hquotient :
      squaredDistanceDefect α β s t₁ / t₁ ≤
        squaredDistanceDefect α β s t₂ / t₂ :=
    convex_div_mono_of_zero hB (hconvex s ⟨hs.le, hsA⟩) hzero
      ht₁ ht₁t₂ ht₂B
  have hscaled :
      squaredDistanceDefect α β s t₁ / (2 * s * t₁) ≤
        squaredDistanceDefect α β s t₂ / (2 * s * t₂) := by
    calc
      squaredDistanceDefect α β s t₁ / (2 * s * t₁) =
          (squaredDistanceDefect α β s t₁ / t₁) / (2 * s) := by ring
      _ ≤ (squaredDistanceDefect α β s t₂ / t₂) / (2 * s) :=
        div_le_div_of_nonneg_right hquotient (by positivity)
      _ = squaredDistanceDefect α β s t₂ / (2 * s * t₂) := by ring
  have hβt₁ : dist o (β t₁) = t₁ := hβ t₁ ⟨ht₁.le, ht₁B⟩
  have hβt₂ : dist o (β t₂) = t₂ := hβ t₂ ⟨ht₂.le, ht₂B⟩
  have hcos :
      Real.cos (metricComparisonAngle (α s) o (β t₁)) ≤
        Real.cos (metricComparisonAngle (α s) o (β t₂)) := by
    rw [cos_metricComparisonAngle_of_radial hs ht₁ hαs hβt₁,
      cos_metricComparisonAngle_of_radial hs ht₂ hαs hβt₂]
    exact hscaled
  have hθ1 : metricComparisonAngle (α s) o (β t₁) ∈
      Icc (0 : ℝ) Real.pi := by
    exact comparisonAngle_mem_Icc _ _ _
  have hθ2 : metricComparisonAngle (α s) o (β t₂) ∈
      Icc (0 : ℝ) Real.pi := by
    exact comparisonAngle_mem_Icc _ _ _
  rw [← Real.arccos_cos hθ2.1 hθ2.2,
    ← Real.arccos_cos hθ1.1 hθ1.2]
  exact Real.arccos_le_arccos hcos

theorem metricComparisonAngle_antitoneOn_snd_of_convex_defect
    {X : Type*} [MetricSpace X] {o : X} {α β : ℝ → X}
    {A B s : ℝ}
    (hB : 0 < B)
    (hα : RadialOn o α A) (hβ : RadialOn o β B)
    (hconvex : ∀ s ∈ Icc (0 : ℝ) A,
      ConvexOn ℝ (Icc (0 : ℝ) B)
        (fun t ↦ squaredDistanceDefect α β s t))
    (hs : s ∈ Ioc (0 : ℝ) A) :
    AntitoneOn (fun t ↦ metricComparisonAngle (α s) o (β t))
      (Ioc (0 : ℝ) B) := by
  intro t₁ ht₁ t₂ ht₂ ht₁t₂
  exact metricComparisonAngle_antitone_snd_of_convex_defect
    hB hα hβ hconvex hs.1 hs.2 ht₁.1 ht₁t₂ ht₂.2

theorem metricComparisonAngle_shortening_of_convex_defect
    {X : Type*} [MetricSpace X] {o : X} {α β : ℝ → X}
    {A B s₁ s₂ t₁ t₂ : ℝ}
    (hA : 0 < A) (hB : 0 < B)
    (hα : RadialOn o α A) (hβ : RadialOn o β B)
    (hconvexFst : ∀ t ∈ Icc (0 : ℝ) B,
      ConvexOn ℝ (Icc (0 : ℝ) A)
        (fun s ↦ squaredDistanceDefect α β s t))
    (hconvexSnd : ∀ s ∈ Icc (0 : ℝ) A,
      ConvexOn ℝ (Icc (0 : ℝ) B)
        (fun t ↦ squaredDistanceDefect α β s t))
    (hs₁ : 0 < s₁) (hs₁s₂ : s₁ ≤ s₂) (hs₂A : s₂ ≤ A)
    (ht₁ : 0 < t₁) (ht₁t₂ : t₁ ≤ t₂) (ht₂B : t₂ ≤ B) :
    metricComparisonAngle (α s₂) o (β t₂) ≤
      metricComparisonAngle (α s₁) o (β t₁) := by
  have hs₂ : 0 < s₂ := hs₁.trans_le hs₁s₂
  have hs₁A : s₁ ≤ A := hs₁s₂.trans hs₂A
  exact
    (metricComparisonAngle_antitone_snd_of_convex_defect hB hα hβ
      hconvexSnd hs₂ hs₂A ht₁ ht₁t₂ ht₂B).trans
      (metricComparisonAngle_antitone_fst_of_convex_defect hA hα hβ
        hconvexFst hs₁ hs₁s₂ hs₂A ht₁
          (ht₁t₂.trans ht₂B))

end Poincare.Toponogov

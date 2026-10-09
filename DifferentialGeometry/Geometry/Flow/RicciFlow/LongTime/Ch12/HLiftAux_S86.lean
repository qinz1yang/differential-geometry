import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.S7Assembly_S86
import DifferentialGeometry.Geometry.Metric.LocalIsometryCovering
import DifferentialGeometry.Geometry.Metric.Path.Composition
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

/-!
# CH12-S86 G1 (aux): C¹ path lifts through a local diffeomorphism, reversed length comparison,
enorm comparison from a metric comparison.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic Set Manifold
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

/-- A path lift of a `C¹` path through a local diffeomorphism is `C¹`. -/
theorem isPathLiftOn_contMDiffOn_C1_S86 {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
    {F : X → Y} (hF : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ F) {γ : ℝ → Y}
    {z : X} {a t : ℝ} {η : ℝ → X} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a t))
    (hη : IsPathLiftOn F γ z a t η) : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 η (Icc a t) := by
  intro s hs
  obtain ⟨Φ, hsΦ, hfΦ⟩ := hF (η s)
  have htarget : γ s ∈ Φ.target := by
    rw [← hη.2.2 s hs, hfΦ hsΦ]
    exact Φ.map_source hsΦ
  have hsymm : ContMDiffAt (𝓡 3) (𝓡 3) 1 Φ.symm (γ s) :=
    (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds htarget)).of_le (by simp)
  have hev : ∀ᶠ r in 𝓝[Icc a t] s, η r ∈ Φ.source :=
    (hη.1 s hs).preimage_mem_nhdsWithin (Φ.open_source.mem_nhds hsΦ)
  have heq : η =ᶠ[𝓝[Icc a t] s] (Φ.symm ∘ γ) := by
    filter_upwards [hev, self_mem_nhdsWithin] with r hr hrI
    change η r = Φ.toPartialEquiv.symm (γ r)
    rw [← hη.2.2 r hrI, hfΦ hr]
    exact (Φ.toPartialEquiv.left_inv hr).symm
  exact (hsymm.comp_contMDiffWithinAt s (hγ s hs)).congr_of_eventuallyEq heq
    (heq.eq_of_nhdsWithin hs)

/-- Reversed length comparison: `|η'| ≤ C |(F ∘ η)'|` ⇒ `L(η) ≤ C L(F ∘ η)`. -/
theorem pathELength_le_comp_S86 {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
    [∀ x : X, ENorm (TangentSpace (𝓡 3) x)] [∀ y : Y, ENorm (TangentSpace (𝓡 3) y)]
    (F : X → Y) {η : ℝ → X} {a b : ℝ} (C : NNReal)
    (hη : ∀ᵐ t ∂MeasureTheory.volume.restrict (Ioo a b), MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) η t)
    (hF : ∀ᵐ t ∂MeasureTheory.volume.restrict (Ioo a b), MDifferentiableAt (𝓡 3) (𝓡 3) F (η t))
    (hnorm : ∀ᵐ t ∂MeasureTheory.volume.restrict (Ioo a b),
      ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η t 1‖ₑ ≤
        (C : ENNReal) * ‖mfderiv (𝓡 3) (𝓡 3) F (η t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η t 1)‖ₑ) :
    pathELength (𝓡 3) η a b ≤ (C : ENNReal) * pathELength (𝓡 3) (F ∘ η) a b := by
  rw [pathELength_eq_lintegral_mfderiv_Ioo, pathELength_eq_lintegral_mfderiv_Ioo,
    ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply MeasureTheory.lintegral_mono_ae
  filter_upwards [hη, hF, hnorm] with t hηt hFt hnormt
  have hcomp := mfderiv_comp t hFt hηt
  change ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η t 1‖ₑ ≤
    (C : ENNReal) * ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (F ∘ η) t 1‖ₑ
  rw [hcomp]
  exact hnormt

/-- `√a ≤ 2 √b` in `ℝ≥0∞` from `a ≤ 2 b`. -/
theorem ofReal_sqrt_le_two_mul_S86 (a b : ℝ) (h : a ≤ 2 * b) :
    ENNReal.ofReal (Real.sqrt a) ≤ ((2 : NNReal) : ENNReal) * ENNReal.ofReal (Real.sqrt b) := by
  have h1 : Real.sqrt a ≤ 2 * Real.sqrt b := by
    calc Real.sqrt a ≤ Real.sqrt (2 * b) := Real.sqrt_le_sqrt h
      _ = Real.sqrt 2 * Real.sqrt b := Real.sqrt_mul (by norm_num) b
      _ ≤ 2 * Real.sqrt b := by
        gcongr
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num
  calc ENNReal.ofReal (Real.sqrt a) ≤ ENNReal.ofReal (2 * Real.sqrt b) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ((2 : NNReal) : ENNReal) * ENNReal.ofReal (Real.sqrt b) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        simp

end GC.LongTime.Ch12

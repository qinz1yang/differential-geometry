import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DerivativeBoundExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTimeWindowContinuity

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem exists_sliver_data {Ctime Cgrad : ℝ≥0} {q t₀ ζ : ℝ} (hCt : 0 < Ctime) (hCg : 0 < Cgrad)
    (hq : 0 < q) (hζ : 0 < ζ) (ht₀ : t₀ ∈ Ioo a s)
    (hder : G.DerivativeBoundBefore Ctime q t₀) (hgrad : G.GradientBoundBefore Cgrad q t₀) :
    ∃ η : ℝ, 0 < η ∧ t₀ + η < s ∧
      G.DerivativeBoundBefore (2 * Ctime) (2 * q) (t₀ + η) ∧
      G.GradientBoundBefore (2 * Cgrad) (2 * q) (t₀ + η) ∧
      ∀ t ∈ Icc t₀ (t₀ + η), ∀ x : P.Carrier,
        G.flow.scalar t x * η ≤ ζ ∧
        |G.flow.scalar t x - G.flow.scalar t₀ x| ≤ ζ ∧
        |G.riemannNorm t x - G.riemannNorm t₀ x| ≤ ζ ∧
        ∀ v : TangentSpace ThreeModel x,
          (G.flow.base.metric t).inner x v v ≤ Real.exp 1 * (G.flow.base.metric t₀).inner x v v ∧
          (G.flow.base.metric t₀).inner x v v ≤ Real.exp 1 * (G.flow.base.metric t).inner x v v := by
  have ht₀' : t₀ ∈ Ico a s := ⟨ht₀.1.le, ht₀.2⟩
  obtain ⟨η₁, hη₁, -, h₁⟩ := G.exists_derivative_gradientBoundBefore_extend hCt hCg hq ht₀ hder hgrad
  obtain ⟨K, hK⟩ := G.exists_forall_Icc_riemannNorm_le ht₀.2
  have hK1 : 0 < max K 1 := lt_max_of_lt_right one_pos
  obtain ⟨η₂, hη₂, -, -, h₂⟩ := G.exists_sliver_forward_comparison hK1 hζ ht₀'
    fun x => (hK t₀ ⟨ht₀.1.le, le_rfl⟩ x).trans (le_max_left _ _)
  have he : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp one_ne_zero]
  obtain ⟨δ, hδ, hs₃, h₃⟩ := G.exists_forall_Icc_scalar_riemannNorm_metric_close ht₀'
    (lt_min hζ he)
  set ζ' : ℝ := min ζ (Real.exp 1 - 1) with hζ'def
  have hζ'ζ : ζ' ≤ ζ := min_le_left _ _
  have hζ'e : 1 + ζ' ≤ Real.exp 1 := by linarith [min_le_right ζ (Real.exp 1 - 1)]
  set η : ℝ := min (η₁ / 2) (min η₂ δ) with hηdef
  have hηa : η ≤ η₁ / 2 := min_le_left _ _
  have hηb : η ≤ η₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hηc : η ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  have hη : 0 < η := lt_min (half_pos hη₁) (lt_min hη₂ hδ)
  have hlt : t₀ + η < t₀ + η₁ := by linarith
  refine ⟨η, hη, by linarith, (h₁ _ hlt).1, (h₁ _ hlt).2, fun t ht x => ?_⟩
  have hw : ∀ r ∈ Icc t₀ (t₀ + η), r ∈ Icc (max a (t₀ - δ)) (t₀ + δ) := fun r hr =>
    ⟨max_le (ht₀.1.le.trans hr.1) (by linarith [hr.1]), by linarith [hr.2]⟩
  have hmt := hw t ht
  have hm₀ := hw t₀ ⟨le_rfl, by linarith⟩
  obtain ⟨hR, hRm, -⟩ := h₃ t hmt t₀ hm₀ x
  refine ⟨?_, hR.trans hζ'ζ, hRm.trans hζ'ζ, fun v => ⟨?_, ?_⟩⟩
  · have hs := ((h₂ t ⟨ht.1, ht.2.trans (by linarith)⟩).2.1 x).2
    rcases le_or_gt (G.flow.scalar t x) 0 with hneg | hpos
    · nlinarith
    · exact (mul_le_mul_of_nonneg_left hηb hpos.le).trans hs
  · exact ((h₃ t hmt t₀ hm₀ x).2.2 v).trans (mul_le_mul_of_nonneg_right hζ'e
      (metric_inner_self_nonneg (G.flow.base.metric t₀) x v))
  · exact ((h₃ t₀ hm₀ t hmt x).2.2 v).trans (mul_le_mul_of_nonneg_right hζ'e
      (metric_inner_self_nonneg (G.flow.base.metric t) x v))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

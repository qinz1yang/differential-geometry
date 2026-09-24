import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar
import DifferentialGeometry.Topology.Manifold.HalfClosedInterval
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SmoothTwoSidedCollar

variable {E F H G S M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace S] [ChartedSpace H S] [TopologicalSpace M] [ChartedSpace G M]
  {e : S → M} (c : SmoothTwoSidedCollar I J e)

def negativeHalfHomeomorph :
    S × Ico (0 : ℝ) c.radius ≃ₜ
      {q : S × symmetricOpenInterval c.radius // q.2.val ≤ 0} where
  toFun p := ⟨(p.1, ⟨-p.2.val, neg_lt_neg p.2.property.2,
    (neg_nonpos.mpr p.2.property.1).trans_lt c.radius_pos⟩),
      neg_nonpos.mpr p.2.property.1⟩
  invFun q := (q.val.1, ⟨-q.val.2.val, neg_nonneg.mpr q.property,
    neg_lt.mpr q.val.2.property.1⟩)
  left_inv p := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext (neg_neg p.2.val)
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Subtype.ext (neg_neg q.val.2.val)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def negativeHalfCollar : C(S × Ico (0 : ℝ) c.radius, M) where
  toFun p := c.toFun (c.negativeHalfHomeomorph p).val
  continuous_toFun := c.isOpenEmbedding_toFun.continuous.comp
    (continuous_subtype_val.comp c.negativeHalfHomeomorph.continuous)

theorem negativeHalfCollar_isEmbedding : _root_.Topology.IsEmbedding c.negativeHalfCollar :=
  c.isOpenEmbedding_toFun.isEmbedding.comp
    (_root_.Topology.IsEmbedding.subtypeVal.comp c.negativeHalfHomeomorph.isEmbedding)

@[simp] theorem negativeHalfCollar_zero (s : S) :
    c.negativeHalfCollar (s, ⟨0, le_rfl, c.radius_pos⟩) = e s := by
  have hp : (c.negativeHalfHomeomorph (s, ⟨0, le_rfl, c.radius_pos⟩)).val =
      (s, ⟨0, neg_lt_zero.mpr c.radius_pos, c.radius_pos⟩) := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext (neg_zero : -(0 : ℝ) = 0)
  change c.toFun _ = e s
  rw [hp]
  exact c.toFun_zero s

theorem negativeHalfCollar_contMDiff :
    letI := Manifold.halfClosedIntervalChartedSpace c.radius_pos
    ContMDiff (I.prod (𝓡∂ 1)) J ∞ c.negativeHalfCollar := by
  let := Manifold.halfClosedIntervalChartedSpace c.radius_pos
  have hinc : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞
      (Subtype.val : Ico (0 : ℝ) c.radius → ℝ) :=
    (Manifold.isSmoothEmbedding_halfClosedInterval_inclusion c.radius_pos).contMDiff
  have hneg : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞
      (fun t : Ico (0 : ℝ) c.radius => -t.val) :=
    (show ContDiff ℝ ∞ (fun t : ℝ => -t) from contDiff_neg).contMDiff.comp hinc
  have hparam : ContMDiff (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ)) ∞
      (fun p => (c.negativeHalfHomeomorph p).val) := by
    apply ContMDiff.prodMk contMDiff_fst
    apply (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval c.radius) _).mp
    exact hneg.comp contMDiff_snd
  exact (contMDiff_subtype_val.comp c.toDiffeomorph.contMDiff).comp hparam

end DifferentialGeometry.Topology.SmoothTwoSidedCollar

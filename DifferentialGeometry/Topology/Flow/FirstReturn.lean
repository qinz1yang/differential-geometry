import DifferentialGeometry.Topology.Flow.TransverseReturns
import Mathlib.Topology.Order.Compact

open Set

namespace DifferentialGeometry.Topology.Flow

private theorem first_return_to_closedSet
    {X : Type*} [TopologicalSpace X] {γ : ℝ → X} (hγ : Continuous γ)
    {K : Set X} (hK : IsClosed K) {δ : ℝ} (hδ : 0 < δ)
    (hshort : ∀ t ∈ Ioo 0 δ, γ t ∉ K) (hreturn : ∃ t > 0, γ t ∈ K) :
    ∃ T > 0, γ T ∈ K ∧ ∀ t ∈ Ioo 0 T, γ t ∉ K := by
  obtain ⟨b, hb, hbK⟩ := hreturn
  have hδb : δ ≤ b := le_of_not_gt (fun h ↦ hshort b ⟨hb, h⟩ hbK)
  let S := Icc δ b ∩ γ ⁻¹' K
  have hS : IsCompact S := isCompact_Icc.inter_right (hK.preimage hγ)
  obtain ⟨T, hT, hmin⟩ := hS.exists_isLeast ⟨b, ⟨hδb, le_rfl⟩, hbK⟩
  refine ⟨T, hδ.trans_le hT.1.1, hT.2, fun t ht hmem ↦ ?_⟩
  by_cases htδ : t < δ
  · exact hshort t ⟨ht.1, htδ⟩ hmem
  have hle := hmin (show t ∈ S from ⟨⟨le_of_not_gt htδ, ht.2.le.trans hT.1.2⟩, hmem⟩)
  exact ht.2.not_ge hle

theorem exists_first_return_to_transverse_segment
    {X : Type*} [TopologicalSpace X] [T2Space X] (φ : _root_.Flow ℝ X)
    {σ : ℝ → X} {ε r a : ℝ} (e : OpenPartialHomeomorph (ℝ × ℝ) X)
    (hsource : e.source = Ioo (-ε) ε ×ˢ Ioo (-ε) ε)
    (he : ∀ p, e p = φ p.2 (σ p.1))
    (hr : r < ε) (ha : a ∈ Icc (-r) r)
    (hreturn : ∃ t > 0, φ t (σ a) ∈ σ '' Icc (-r) r) :
    ∃ T > 0, φ T (σ a) ∈ σ '' Icc (-r) r ∧
      ∀ t ∈ Ioo 0 T, φ t (σ a) ∉ σ '' Icc (-r) r := by
  have hε : 0 < ε := by linarith [ha.1, ha.2]
  have hsmall {u : ℝ} (hu : u ∈ Icc (-r) r) : u ∈ Ioo (-ε) ε := by
    constructor <;> linarith [hu.1, hu.2]
  have hpair {u : ℝ} (hu : u ∈ Icc (-r) r) {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
      (u, t) ∈ e.source := by rw [hsource]; exact ⟨hsmall hu, ht⟩
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have hσ : ContinuousOn σ (Icc (-r) r) := by
    have hcont := e.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu ↦ hpair hu hzero)
    simpa only [Function.comp_def, id_eq, he, φ.map_zero_apply] using hcont
  have hclosed : IsClosed (σ '' Icc (-r) r) :=
    (isCompact_Icc.image_of_continuousOn hσ).isClosed
  apply first_return_to_closedSet (φ.continuous continuous_id continuous_const) hclosed hε
    (hreturn := hreturn)
  intro t ht hmem
  obtain ⟨b, hb, hbe⟩ := hmem
  have heq : e (a, t) = e (b, 0) := by
    rw [he, he, φ.map_zero_apply]
    exact hbe.symm
  have hp := e.injOn (hpair ha ⟨by linarith [ht.1], ht.2⟩) (hpair hb hzero) heq
  exact ht.1.ne' (congrArg Prod.snd hp)

end DifferentialGeometry.Topology.Flow

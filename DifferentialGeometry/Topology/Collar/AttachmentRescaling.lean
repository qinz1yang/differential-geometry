import DifferentialGeometry.Topology.Attachment.MappingCylinderGluing
import DifferentialGeometry.Topology.Collar.Rescaling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Function Topology
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Topology.Collar

variable {B X : Type*} [TopologicalSpace B] [CompactSpace B]
  [TopologicalSpace X] [T2Space X]

theorem exists_attachment_homeomorph_of_rescaling
    (f : C(B, X)) {ε δ k : ℝ} {a : Icc (0 : ℝ) ε} (ha : 0 < a.val)
    (hkδ : k < δ)
    (c : C(B × Icc (0 : ℝ) ε, X)) (hc : IsEmbedding c)
    (hzero : ∀ p, c (p, ⟨0, ⟨le_rfl, ha.le.trans a.property.2⟩⟩) = f p)
    (hopen : IsOpen (c '' {q | (q.2 : ℝ) < δ}))
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε)) (hσinj : Injective σ)
    (hσzero : σ ⟨0, ⟨le_rfl, ha.le.trans a.property.2⟩⟩ = a)
    (hσrange : range σ = {t : Icc (0 : ℝ) ε | a.val ≤ t.val})
    (hσfix : ∀ t : Icc (0 : ℝ) ε, k ≤ t.val → σ t = t) :
    ∃ h : MappingCylinder f ≃ₜ X,
      (∀ x, h (mappingCylinderOriginal f x) = rescale c hc σ x) ∧
      ∀ q : B × Icc (0 : ℝ) 1, h (mappingCylinderProduct f q) =
        c (q.1, ⟨a.val * (1 - q.2.val),
          ⟨mul_nonneg ha.le (sub_nonneg.mpr q.2.property.2), by
            have ht := q.2.property.1
            nlinarith [a.property.2]⟩⟩) := by
  let j : C(X, X) := ⟨rescale c hc σ,
    continuous_rescale c hc σ hkδ hopen hσfix⟩
  have hj : IsClosedEmbedding j := isClosedEmbedding_rescale c hc σ
    hσinj hkδ hopen hσfix
  let ρ : C(Icc (0 : ℝ) 1, Icc (0 : ℝ) ε) :=
    ⟨fun t => ⟨a.val * (1 - t.val), mul_nonneg ha.le (sub_nonneg.mpr t.property.2), by
      have ht := t.property.1
      nlinarith [a.property.2]⟩, by fun_prop⟩
  let g : C(B × Icc (0 : ℝ) 1, X) := c.comp ((ContinuousMap.id B).prodMap ρ)
  have hginj : Injective g := by
    intro p q hpq
    have hh : (p.1, ρ p.2) = (q.1, ρ q.2) := hc.injective hpq
    have hfst := congrArg (fun r : B × Icc (0 : ℝ) ε => r.1) hh
    have ht := congrArg (fun r : B × Icc (0 : ℝ) ε => r.2.val) hh
    change a.val * (1 - p.2.val) = a.val * (1 - q.2.val) at ht
    exact Prod.ext hfst (Subtype.ext (by nlinarith))
  have hg : IsClosedEmbedding g := g.continuous.isClosedEmbedding hginj
  have hseam (p : B) : g (p, 0) = j (f p) := by
    rw [← hzero p]
    change c (p, ρ 0) = rescale c hc σ (c (p, _))
    rw [rescale_apply]
    congr 1
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simpa [ρ] using congrArg Subtype.val hσzero.symm
  have hjrange : range j = (range c)ᶜ ∪ c '' {q | a.val ≤ (q.2 : ℝ)} :=
    range_rescale c hc σ hσrange
  have hgrange : range g = c '' {q | (q.2 : ℝ) ≤ a.val} := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      refine ⟨(q.1, ρ q.2), ?_, rfl⟩
      change a.val * (1 - q.2.val) ≤ a.val
      nlinarith [q.2.property.1]
    · rintro ⟨q, hq, rfl⟩
      have ht : 1 - q.2.val / a.val ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact sub_nonneg.mpr ((div_le_one ha).mpr hq)
        · exact sub_le_self _ (div_nonneg q.2.property.1 ha.le)
      refine ⟨(q.1, ⟨1 - q.2.val / a.val, ht⟩), ?_⟩
      change c (q.1, ρ _) = c q
      congr 1
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change a.val * (1 - (1 - q.2.val / a.val)) = q.2.val
        field_simp [ha.ne']
        ring
  have hcross (p : B × Icc (0 : ℝ) 1) (x : X) (h : g p = j x) : p.2 = 0 ∧ f p.1 = x := by
    have hm : g p ∈ range j := ⟨x, h.symm⟩
    rw [hjrange] at hm
    rcases hm with hm | ⟨q, hq, heq⟩
    · exact False.elim (hm ⟨(p.1, ρ p.2), rfl⟩)
    · have he : q = (p.1, ρ p.2) := hc.injective heq
      have ht : a.val ≤ a.val * (1 - p.2.val) := by
        rw [he] at hq
        exact hq
      have hp0 : p.2 = 0 := Subtype.ext (by change p.2.val = 0; nlinarith [p.2.property.1])
      refine ⟨hp0, hj.injective ?_⟩
      rw [← h, ← hseam]
      exact congrArg g (Prod.ext rfl hp0.symm)
  have hcover : range g ∪ range j = univ := by
    apply eq_univ_of_forall
    intro y
    by_cases hy : y ∈ range c
    · obtain ⟨q, rfl⟩ := hy
      by_cases hqa : q.2.val ≤ a.val
      · exact Or.inl (hgrange.symm ▸ ⟨q, hqa, rfl⟩)
      · apply Or.inr
        rw [hjrange]
        exact Or.inr ⟨q, le_of_lt (lt_of_not_ge hqa), rfl⟩
    · apply Or.inr
      rw [hjrange]
      exact Or.inl hy
  exact ⟨mappingCylinderHomeomorphOfClosedCover f g j hseam hg hj hcross hcover,
    fun _ => rfl, fun _ => rfl⟩

end DifferentialGeometry.Topology.Collar

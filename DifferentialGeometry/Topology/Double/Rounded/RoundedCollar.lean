import DifferentialGeometry.Topology.Double.Rounded.RoundedDouble

namespace DifferentialGeometry.Topology.RoundedDouble

open Set _root_.Topology

variable {X : Type*} [TopologicalSpace X] {g : X → ℝ}

def boundaryBand (g : X → ℝ) (η : ℝ) : Set (boundary g) :=
  {p | p.1.2 ∈ Icc (-η) η}

noncomputable def boundaryBandHomeomorph {δ η : ℝ} (_hη : 0 ≤ η) (hηδ : η ^ 2 ≤ δ)
    (Φ : (g ⁻¹' {0}) × Icc (-δ) δ ≃ₜ (g ⁻¹' Icc (-δ) δ))
    (hΦ : ∀ p, g (Φ p).1 = p.2.1) :
    (g ⁻¹' {0}) × Icc (-η) η ≃ₜ boundaryBand g η := by
  have hsquare {t : ℝ} (ht : t ∈ Icc (-η) η) : -t ^ 2 ∈ Icc (-δ) δ := by
    have ht2 : t ^ 2 ≤ η ^ 2 := by nlinarith [ht.1, ht.2]
    have hδ : 0 ≤ δ := le_trans (sq_nonneg η) hηδ
    constructor <;> nlinarith [sq_nonneg t]
  let F : (g ⁻¹' {0}) × Icc (-η) η → boundaryBand g η := fun p =>
    ⟨⟨((Φ (p.1, ⟨-p.2.1 ^ 2, hsquare p.2.2⟩)).1, p.2.1), by
      change g (Φ (p.1, ⟨-p.2.1 ^ 2, hsquare p.2.2⟩)).1 + p.2.1 ^ 2 = 0
      rw [hΦ]
      ring⟩, p.2.2⟩
  have hbase (p : boundaryBand g η) : g p.1.1.1 ∈ Icc (-δ) δ := by
    have hp : g p.1.1.1 + p.1.1.2 ^ 2 = 0 := p.1.2
    have heq : g p.1.1.1 = -p.1.1.2 ^ 2 := by linarith
    rw [heq]
    exact hsquare p.2
  let G : boundaryBand g η → (g ⁻¹' {0}) × Icc (-η) η := fun p =>
    ((Φ.symm ⟨p.1.1.1, hbase p⟩).1, ⟨p.1.1.2, p.2⟩)
  have hcoord (p : boundaryBand g η) :
      (Φ.symm ⟨p.1.1.1, hbase p⟩).2.1 = -p.1.1.2 ^ 2 := by
    have hc := hΦ (Φ.symm ⟨p.1.1.1, hbase p⟩)
    rw [Φ.apply_symm_apply] at hc
    have hp : g p.1.1.1 + p.1.1.2 ^ 2 = 0 := p.1.2
    dsimp only at hc
    linarith
  refine
    { toFun := F
      invFun := G
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro p
    apply Prod.ext
    · change (Φ.symm (Φ (p.1, ⟨-p.2.1 ^ 2, hsquare p.2.2⟩))).1 = p.1
      rw [Φ.symm_apply_apply]
    · rfl
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change (Φ ((Φ.symm ⟨p.1.1.1, hbase p⟩).1,
          ⟨-p.1.1.2 ^ 2, hsquare p.2⟩)).1 = p.1.1.1
      have heq : ((Φ.symm ⟨p.1.1.1, hbase p⟩).1,
          (⟨-p.1.1.2 ^ 2, hsquare p.2⟩ : Icc (-δ) δ)) =
          Φ.symm ⟨p.1.1.1, hbase p⟩ := by
        apply Prod.ext
        · rfl
        · exact Subtype.ext (hcoord p).symm
      rw [heq, Φ.apply_symm_apply]
    · rfl
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_subtype_val.comp (Φ.continuous.comp
        (continuous_fst.prodMk
          (((continuous_subtype_val.comp continuous_snd).pow 2).neg.subtype_mk _)))
    · exact continuous_subtype_val.comp continuous_snd
  · apply Continuous.prodMk
    · exact continuous_fst.comp (Φ.symm.continuous.comp
        (((continuous_subtype_val.comp continuous_subtype_val).fst).subtype_mk _))
    · exact ((continuous_subtype_val.comp continuous_subtype_val).snd).subtype_mk _

theorem boundaryBandHomeomorph_height {δ η : ℝ} (hη : 0 ≤ η) (hηδ : η ^ 2 ≤ δ)
    (Φ : (g ⁻¹' {0}) × Icc (-δ) δ ≃ₜ (g ⁻¹' Icc (-δ) δ))
    (hΦ : ∀ p, g (Φ p).1 = p.2.1) (p : (g ⁻¹' {0}) × Icc (-η) η) :
    (boundaryBandHomeomorph hη hηδ Φ hΦ p).1.1.2 = p.2.1 := rfl

theorem boundaryBandHomeomorph_zero {δ η : ℝ} (hη : 0 ≤ η) (hηδ : η ^ 2 ≤ δ)
    (Φ : (g ⁻¹' {0}) × Icc (-δ) δ ≃ₜ (g ⁻¹' Icc (-δ) δ))
    (hΦ : ∀ p, g (Φ p).1 = p.2.1)
    (hΦ0 : ∀ (h : 0 ∈ Icc (-δ) δ) (x : g ⁻¹' {0}), (Φ (x, ⟨0, h⟩)).1 = x.1)
    (x : g ⁻¹' {0}) :
    (boundaryBandHomeomorph hη hηδ Φ hΦ (x, ⟨0, ⟨neg_nonpos.mpr hη, hη⟩⟩)).1.1 =
      (x.1, 0) := by
  apply Prod.ext
  · change (Φ (x, ⟨-0 ^ 2, _⟩)).1 = x.1
    have hzero : -(0 : ℝ) ^ 2 = 0 := by norm_num
    generalize_proofs hmem
    simpa only [hzero] using hΦ0 (by simpa only [hzero] using hmem) x
  · rfl

end DifferentialGeometry.Topology.RoundedDouble

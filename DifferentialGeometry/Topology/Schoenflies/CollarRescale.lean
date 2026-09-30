import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Homeomorph.Lemmas

namespace DifferentialGeometry.Topology

open Set

noncomputable def symmetricIntervalScale {η : ℝ} (hη : 0 < η) :
    Icc (-1 : ℝ) 1 ≃ₜ Icc (-η) η where
  toFun s := ⟨η * s.1, by constructor <;> nlinarith [s.2.1, s.2.2]⟩
  invFun s := ⟨s.1 / η, by
    constructor
    · rw [le_div_iff₀ hη]; simpa only [neg_one_mul] using s.2.1
    · rw [div_le_iff₀ hη]; simpa only [one_mul] using s.2.2⟩
  left_inv s := Subtype.ext (by dsimp; field_simp)
  right_inv s := Subtype.ext (by dsimp; field_simp)
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.div_const η).subtype_mk _

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def rescaleHeightCollar {η : ℝ} (hη : 0 < η) (t : X → ℝ)
    (Φ : Y × Icc (-η) η ≃ₜ {x : X // t x ∈ Icc (-η) η}) :
    Y × Icc (-1 : ℝ) 1 ≃ₜ {x : X // t x / η ∈ Icc (-1 : ℝ) 1} :=
  ((Homeomorph.prodCongr (Homeomorph.refl Y) (symmetricIntervalScale hη)).trans Φ).trans
    (Homeomorph.setCongr (by
      ext x
      change (-η ≤ t x ∧ t x ≤ η) ↔ (-1 ≤ t x / η ∧ t x / η ≤ 1)
      rw [le_div_iff₀ hη, div_le_iff₀ hη, neg_one_mul, one_mul]))

theorem rescaleHeightCollar_height {η : ℝ} (hη : 0 < η) (t : X → ℝ)
    (Φ : Y × Icc (-η) η ≃ₜ {x : X // t x ∈ Icc (-η) η})
    (hΦ : ∀ p, t (Φ p).1 = p.2.1) (p : Y × Icc (-1 : ℝ) 1) :
    t (rescaleHeightCollar hη t Φ p).1 / η = p.2.1 := by
  change t (Φ (p.1, symmetricIntervalScale hη p.2)).1 / η = p.2.1
  rw [hΦ]
  change (η * p.2.1) / η = p.2.1
  field_simp

end DifferentialGeometry.Topology

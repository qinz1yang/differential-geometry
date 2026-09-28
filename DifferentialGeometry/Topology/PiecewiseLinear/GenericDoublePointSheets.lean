/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GluedDoublePointFaces
import DifferentialGeometry.Topology.PiecewiseLinear.GluedEdgeSides
import DifferentialGeometry.Topology.PiecewiseLinear.FreeGermVocabulary

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem eq_or_eq_of_encard_le_two {α : Type*} {s : Set α} (h : s.encard ≤ 2) {a b c : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) : c = a ∨ c = b := by
  by_contra hne
  push Not at hne
  have h3 : ({a, b, c} : Set α).encard = 3 :=
    Set.encard_eq_three.mpr ⟨a, b, c, hab, hne.1.symm, hne.2.symm, rfl⟩
  have hsub : ({a, b, c} : Set α) ⊆ s := by
    rintro z (rfl | rfl | rfl)
    · exact ha
    · exact hb
    · exact hc
  have hle := Set.encard_le_encard hsub
  rw [h3] at hle
  have : (3 : ℕ∞) ≤ 2 := hle.trans h
  norm_num at this

section Affine

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_sum_eq_one_apply_eq_sum_smul {σ : Finset E}
    (hind : AffineIndependent ℝ ((↑) : σ → E)) (hcard : σ.card = Module.finrank ℝ E + 1)
    {φ : E → F} {A : E →ᵃ[ℝ] F} (hA : ∀ v ∈ σ, A v = φ v) (z : E) :
    ∃ w : E → ℝ, ∑ v ∈ σ, w v = 1 ∧ A z = ∑ v ∈ σ, w v • φ v := by
  classical
  have htop : affineSpan ℝ (Set.range ((↑) : σ → E)) = ⊤ :=
    hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by rw [Fintype.card_coe, hcard])
  have hz : z ∈ affineSpan ℝ (Set.range ((↑) : σ → E)) := by
    rw [htop]
    exact AffineSubspace.mem_top _ _ _
  obtain ⟨w', hw', hzw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hz
  let w : E → ℝ := fun v => if h : v ∈ σ then w' ⟨v, h⟩ else 0
  have hww : ∀ i : σ, w i = w' i := fun i => dite_eq_left i.2
  refine ⟨w, ?_, ?_⟩
  · rw [← Finset.sum_coe_sort σ w]
    simp only [hww]
    exact hw'
  · have hA' : A z = Finset.univ.affineCombination ℝ (A ∘ ((↑) : σ → E)) w' := by
      rw [hzw, Finset.map_affineCombination _ _ _ hw']
    rw [hA', Finset.affineCombination_eq_linear_combination _ _ _ hw', ← Finset.sum_coe_sort σ]
    exact Finset.sum_congr rfl fun i _ => by
      rw [hww i, Function.comp_apply, hA i i.2]

theorem not_affineIndependent_insert_of_mem_range [DecidableEq E] {σ : Finset E}
    (hind : AffineIndependent ℝ ((↑) : σ → E)) (hcard : σ.card = Module.finrank ℝ E + 1)
    {φ : E → F} {A : E →ᵃ[ℝ] F} (hA : ∀ v ∈ σ, A v = φ v) {v : E} (hv : v ∉ σ) {z : E}
    (hz : φ v = A z) : ¬ AffineIndependent ℝ (fun u : (insert v σ : Finset E) => φ (u : E)) := by
  obtain ⟨w, hw, hAz⟩ := exists_sum_eq_one_apply_eq_sum_smul hind hcard hA z
  exact not_affineIndependent_insert_of_eq_sum hv hw (hz.trans hAz)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem not_affineIndependent_insert_of_eq_lineMap [DecidableEq E] {a b c : E} (hab : a ≠ b)
    (hca : c ≠ a)
    (hcb : c ≠ b) {φ : E → F} {s : ℝ} (hc : φ c = AffineMap.lineMap (φ a) (φ b) s) :
    ¬ AffineIndependent ℝ (fun u : (insert c {a, b} : Finset E) => φ (u : E)) := by
  have hv : c ∉ ({a, b} : Finset E) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hca, hcb⟩
  refine not_affineIndependent_insert_of_eq_sum (w := fun u => if u = a then 1 - s else s) hv
    ?_ ?_
  · rw [Finset.sum_pair hab, ite_eq_left rfl, ite_eq_right hab.symm]
    ring
  · rw [Finset.sum_pair hab, ite_eq_left rfl, ite_eq_right hab.symm, hc, AffineMap.lineMap_apply_module]

end Affine

theorem exists_homeomorph_apply_eq_sub (F : EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] ℝ × ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ∃ Φ : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ, ∀ z, Φ z = F (z - x) :=
  ⟨(Homeomorph.subRight x).trans F.toContinuousLinearEquiv.toHomeomorph, fun _ => rfl⟩

theorem exists_homeomorph_kinkShear (μ μ' : ℝ) :
    ∃ Ψ : ℝ × ℝ ≃ₜ ℝ × ℝ, ∀ q : ℝ × ℝ, Ψ q = (q.1 - μ' * q.2 - μ * max q.2 0, q.2) := by
  let f₁ : ℝ × ℝ → ℝ × ℝ := fun q => (q.1 - μ' * q.2 - μ * max q.2 0, q.2)
  let f₂ : ℝ × ℝ → ℝ × ℝ := fun q => (q.1 + μ' * q.2 + μ * max q.2 0, q.2)
  have hc₁ : Continuous f₁ :=
    ((continuous_fst.sub (continuous_const.mul continuous_snd)).sub
      (continuous_const.mul (continuous_snd.max continuous_const))).prodMk continuous_snd
  have hc₂ : Continuous f₂ :=
    ((continuous_fst.add (continuous_const.mul continuous_snd)).add
      (continuous_const.mul (continuous_snd.max continuous_const))).prodMk continuous_snd
  have hl : Function.LeftInverse f₂ f₁ := fun q => Prod.ext (by simp only [f₁, f₂]; ring) rfl
  have hr : Function.RightInverse f₂ f₁ := fun q => Prod.ext (by simp only [f₁, f₂]; ring) rfl
  exact ⟨⟨⟨f₁, f₂, hl, hr⟩, hc₁, hc₂⟩, fun _ => rfl⟩

section Glued

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem regionGluedMap_of_mem (D : SingularTwoCell M)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    {Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ Rc.space) :
    regionGluedMap D ec Rs φ Rc x = ec.symm (simplicialMap Rs φ x) := by
  classical
  simp only [regionGluedMap, ite_eq_left hx]

end Glued

end DifferentialGeometry.Topology.PiecewiseLinear

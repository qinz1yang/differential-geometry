/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeBase
import DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffineSimplicial
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem affineMap_apply_eq_sum_weights_smul (A : E →ᵃ[ℝ] F) {σ : Finset E} {z : E}
    (hz : z ∈ convexHull ℝ (σ : Set E)) : A z = ∑ v ∈ σ, weights σ z v • A v := by
  have hw := sum_weights hz
  have h1 : ∑ v ∈ σ, weights σ z v • v = σ.affineCombination ℝ id (weights σ z) :=
    (Finset.affineCombination_eq_linear_combination σ id (weights σ z) hw).symm
  have h2 : ∑ v ∈ σ, weights σ z v • A v = σ.affineCombination ℝ (A ∘ id) (weights σ z) :=
    (Finset.affineCombination_eq_linear_combination σ (A ∘ id) (weights σ z) hw).symm
  conv_lhs => rw [← sum_weights_smul hz]
  rw [h1, h2, Finset.map_affineCombination σ id (weights σ z) hw A]

section ConeMap

variable [DecidableEq E]

theorem simplicialMap_coneComplex_apply {p : E} {L : Geometry.SimplicialComplex ℝ E}
    (h : IsConeBase p L) {φ : E → F} {q : F} (hφp : φ p = q) {f : E → F} {σ : Finset E}
    (hσ : σ ∈ L.faces) {A : E →ᵃ[ℝ] F} (hA : EqOn f A (convexHull ℝ (σ : Set E)))
    (hφ : ∀ v ∈ σ, φ v = f v) {z : E} (hz : z ∈ convexHull ℝ (σ : Set E)) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : simplicialMap (coneComplex h) φ (p + s • (z - p)) = q + s • (f z - q) := by
  have hins : insert p σ ∈ (coneComplex h).faces := Or.inr (Or.inr ⟨σ, hσ, rfl⟩)
  have hpσ : p ∉ σ := h.notMem_face hσ
  have hx : p + s • (z - p) ∈ convexHull ℝ ((insert p σ : Finset E) : Set E) :=
    mem_convexHull_insert_of_combo hz hs0 hs1
  rw [simplicialMap_eq_of_mem _ φ hins hx]
  have hw : ∀ v ∈ insert p σ, weights (insert p σ) (p + s • (z - p)) v =
      if v = p then 1 - s else s * weights σ z v := by
    refine weights_eq ((coneComplex h).indep hins) hx ?_ ?_
    · rw [Finset.sum_insert hpσ, ite_eq_left rfl,
        Finset.sum_congr rfl fun v hv => ite_eq_right (ne_of_mem_of_not_mem hv hpσ), ← Finset.mul_sum,
        sum_weights hz]
      ring
    · rw [Finset.sum_insert hpσ, ite_eq_left rfl,
        Finset.sum_congr rfl fun v hv => by rw [ite_eq_right (ne_of_mem_of_not_mem hv hpσ)]]
      simp_rw [mul_smul]
      rw [← Finset.smul_sum, sum_weights_smul hz, add_smul_sub_eq_combo]
  rw [Finset.sum_congr rfl fun v hv => by rw [hw v hv], Finset.sum_insert hpσ, ite_eq_left rfl, hφp,
    Finset.sum_congr rfl fun v hv => by
      rw [ite_eq_right (ne_of_mem_of_not_mem hv hpσ), hφ v hv,
        hA (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))]]
  simp_rw [mul_smul]
  rw [← Finset.smul_sum, ← affineMap_apply_eq_sum_weights_smul A hz, ← hA hz, add_smul_sub_eq_combo]

theorem simplicialMap_coneComplex_apex {p : E} {L : Geometry.SimplicialComplex ℝ E}
    (h : IsConeBase p L) {φ : E → F} {q : F} (hφp : φ p = q) :
    simplicialMap (coneComplex h) φ p = q := by
  rw [simplicialMap_vertex _ φ (Or.inr (Or.inl rfl)), hφp]

theorem simplicialMap_coneComplex_eq_of_mem_space {p : E} {L : Geometry.SimplicialComplex ℝ E}
    (h : IsConeBase p L) {φ : E → F} {q : F} (hφp : φ p = q) {f : E → F}
    (hAff : ∀ σ ∈ L.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (σ : Set E)))
    (hφ : ∀ σ ∈ L.faces, ∀ v ∈ σ, φ v = f v) {z : E} (hz : z ∈ L.space) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : simplicialMap (coneComplex h) φ (p + s • (z - p)) = q + s • (f z - q) := by
  obtain ⟨σ, hσ, hzσ⟩ := L.mem_space_iff.mp hz
  obtain ⟨A, hA⟩ := hAff σ hσ
  exact simplicialMap_coneComplex_apply h hφp hσ hA (hφ σ hσ) hzσ hs0 hs1

end ConeMap

theorem exists_isPLHomeomorphOn_coneComplex [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [DecidableEq E] [DecidableEq F] {p : E} {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    (hL : IsConeBase p L) {q : F} {L' : Geometry.SimplicialComplex ℝ F} [Finite L'.faces]
    (hL' : IsConeBase q L') {f : E → F} (hf : IsPLHomeomorphOn f L.space L'.space) :
    ∃ g : E → F, IsPLHomeomorphOn g (coneComplex hL).space (coneComplex hL').space ∧
      EqOn g f L.space ∧ g p = q ∧
      ∀ z ∈ L.space, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → g (p + s • (z - p)) = q + s • (f z - q) := by
  obtain ⟨L₁, hL₁, hfin₁, hAff⟩ := hf.isPiecewiseAffineOn.exists_isSubdivision_affineOn_faces L
  obtain ⟨L'₁, hL'₁, hfin'₁, hAff'⟩ :=
    hf.isPiecewiseAffineOn_invFunOn.exists_isSubdivision_affineOn_faces L'
  have h₁ : IsConeBase p L₁ := hL.of_isSubdivision hL₁
  have h'₁ : IsConeBase q L'₁ := hL'.of_isSubdivision hL'₁
  have hC₁ : Finite (coneComplex h₁).faces := (coneComplex_faces_finite h₁ hfin₁).to_subtype
  have hC'₁ : Finite (coneComplex h'₁).faces := (coneComplex_faces_finite h'₁ hfin'₁).to_subtype
  set f' : F → E := Function.invFunOn f L.space with hf'def
  let φ : E → F := fun v => if v = p then q else f v
  let φ' : F → E := fun u => if u = q then p else f' u
  have hφp : φ p = q := by simp [φ]
  have hφ'q : φ' q = p := by simp [φ']
  have hφ : ∀ σ ∈ L₁.faces, ∀ v ∈ σ, φ v = f v := fun σ hσ v hv => by
    simp only [φ, ite_eq_right (ne_of_mem_of_not_mem hv (h₁.notMem_face hσ))]
  have hφ' : ∀ σ ∈ L'₁.faces, ∀ v ∈ σ, φ' v = f' v := fun σ hσ v hv => by
    simp only [φ', ite_eq_right (ne_of_mem_of_not_mem hv (h'₁.notMem_face hσ))]
  set g := simplicialMap (coneComplex h₁) φ with hgdef
  set g' := simplicialMap (coneComplex h'₁) φ' with hg'def
  have hspace : (coneComplex h₁).space = (coneComplex hL).space :=
    (coneComplex_isSubdivision hL hL₁).space_eq
  have hspace' : (coneComplex h'₁).space = (coneComplex hL').space :=
    (coneComplex_isSubdivision hL' hL'₁).space_eq
  have hg_apply : ∀ z ∈ L.space, ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      g (p + s • (z - p)) = q + s • (f z - q) := fun z hz s hs0 hs1 =>
    simplicialMap_coneComplex_eq_of_mem_space h₁ hφp hAff hφ (hL₁.space_eq ▸ hz) hs0 hs1
  have hg'_apply : ∀ w ∈ L'.space, ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      g' (q + s • (w - q)) = p + s • (f' w - p) := fun w hw s hs0 hs1 =>
    simplicialMap_coneComplex_eq_of_mem_space h'₁ hφ'q hAff' hφ' (hL'₁.space_eq ▸ hw) hs0 hs1
  have hgp : g p = q := simplicialMap_coneComplex_apex h₁ hφp
  have hg'q : g' q = p := simplicialMap_coneComplex_apex h'₁ hφ'q
  have hff' : ∀ z ∈ L.space, f' (f z) = z := fun z hz => hf.bijOn.invOn_invFunOn.1 hz
  have hf'f : ∀ w ∈ L'.space, f (f' w) = w := fun w hw => hf.bijOn.invOn_invFunOn.2 hw
  have hmaps : MapsTo g (coneComplex hL).space (coneComplex hL').space := by
    intro x hx
    rcases (mem_coneComplex_space_iff hL).mp hx with hxp | ⟨z, hz, s, hs, hs', rfl⟩
    · rw [hxp, hgp]
      exact apex_mem_coneComplex_space hL'
    · rw [hg_apply z hz s hs.le hs']
      exact (mem_coneComplex_space_iff hL').mpr (Or.inr ⟨f z, hf.bijOn.mapsTo hz, s, hs, hs', rfl⟩)
  have hmaps' : MapsTo g' (coneComplex hL').space (coneComplex hL).space := by
    intro y hy
    rcases (mem_coneComplex_space_iff hL').mp hy with hyq | ⟨w, hw, s, hs, hs', rfl⟩
    · rw [hyq, hg'q]
      exact apex_mem_coneComplex_space hL
    · rw [hg'_apply w hw s hs.le hs']
      exact (mem_coneComplex_space_iff hL).mpr
        (Or.inr ⟨f' w, hf.bijOn.surjOn.mapsTo_invFunOn hw, s, hs, hs', rfl⟩)
  have hinv : InvOn g' g (coneComplex hL).space (coneComplex hL').space := by
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · rcases (mem_coneComplex_space_iff hL).mp hx with hxp | ⟨z, hz, s, hs, hs', rfl⟩
      · rw [hxp, hgp, hg'q]
      · rw [hg_apply z hz s hs.le hs', hg'_apply _ (hf.bijOn.mapsTo hz) s hs.le hs', hff' z hz]
    · rcases (mem_coneComplex_space_iff hL').mp hy with hyq | ⟨w, hw, s, hs, hs', rfl⟩
      · rw [hyq, hg'q, hgp]
      · rw [hg'_apply w hw s hs.le hs', hg_apply _ (hf.bijOn.surjOn.mapsTo_invFunOn hw) s hs.le hs',
          hf'f w hw]
  have hbij : BijOn g (coneComplex hL).space (coneComplex hL').space := hinv.bijOn hmaps hmaps'
  refine ⟨g, ⟨hbij, ?_, ?_⟩, fun z hz => ?_, hgp, hg_apply⟩
  · rw [← hspace]
    exact isPiecewiseAffineOn_simplicialMap _ φ
  · have hpl : IsPiecewiseAffineOn g' (coneComplex hL').space := by
      rw [← hspace']
      exact isPiecewiseAffineOn_simplicialMap _ φ'
    refine hpl.congr fun y hy => ?_
    have h1 := hbij.invOn_invFunOn
    exact hbij.injOn (hbij.surjOn.mapsTo_invFunOn hy) (hmaps' hy) ((h1.2 hy).trans (hinv.2 hy).symm)
  · have := hg_apply z hz 1 zero_le_one le_rfl
    rwa [one_smul, add_sub_cancel, one_smul, add_sub_cancel] at this

end DifferentialGeometry.Topology.PiecewiseLinear

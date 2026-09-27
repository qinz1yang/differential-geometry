/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.WallSystemBlocks

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem AffineIndependent.comp_affineMap_of_injOn {ι E F : Type*} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ι → E} (hp : AffineIndependent ℝ p) (g : E →ᵃ[ℝ] F)
    (hg : InjOn g (convexHull ℝ (range p))) : AffineIndependent ℝ (g ∘ p) := by
  classical
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact affineIndependent_of_subsingleton ℝ _
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq] at hp ⊢
  intro w₁ w₂ hw₁ hw₂ heq
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw₁,
    Finset.affineCombination_eq_linear_combination _ _ _ hw₂] at heq
  simp only [Function.comp_apply] at heq
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  set n : ℝ := (Fintype.card ι : ℝ) with hndef
  have hn' : n ≠ 0 := hn.ne'
  set B : ℝ := ∑ i, (|w₁ i| + |w₂ i|) with hBdef
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => by positivity
  have hle₁ : ∀ i, |w₁ i| ≤ B := fun i =>
    (le_add_of_nonneg_right (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun j => |w₁ j| + |w₂ j|) (fun j _ => by positivity)
        (Finset.mem_univ i))
  have hle₂ : ∀ i, |w₂ i| ≤ B := fun i =>
    (le_add_of_nonneg_left (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun j => |w₁ j| + |w₂ j|) (fun j _ => by positivity)
        (Finset.mem_univ i))
  have hnB : 0 < 1 + n * B := by positivity
  set ε : ℝ := 1 / (1 + n * B) with hεdef
  have hε : 0 < ε := by positivity
  have hεB : ε * (1 + n * B) = 1 := by
    rw [hεdef]
    field_simp
  let W : (ι → ℝ) → ι → ℝ := fun w i => (1 - ε) / n + ε * w i
  have hWsum : ∀ w : ι → ℝ, ∑ i, w i = 1 → ∑ i, W w i = 1 := by
    intro w hw
    simp only [W, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, hw]
    rw [← hndef]
    field_simp
    ring
  have hWnn : ∀ w : ι → ℝ, (∀ i, |w i| ≤ B) → ∀ i, 0 ≤ W w i := by
    intro w hw i
    have h1 : -B ≤ w i := (abs_le.mp (hw i)).1
    have h2 : (1 - ε) / n - ε * B = 0 := by
      field_simp
      nlinarith
    have h3 : ε * (-B) ≤ ε * w i := mul_le_mul_of_nonneg_left h1 hε.le
    change 0 ≤ (1 - ε) / n + ε * w i
    nlinarith
  have hpt : ∀ w : ι → ℝ, ∑ i, w i = 1 → (∀ i, |w i| ≤ B) →
      Finset.univ.affineCombination ℝ p (W w) ∈ convexHull ℝ (range p) := fun w hw hwB =>
    affineCombination_mem_convexHull (fun i _ => hWnn w hwB i) (hWsum w hw)
  have himg : ∀ w : ι → ℝ, ∑ i, w i = 1 →
      g (Finset.univ.affineCombination ℝ p (W w)) =
        ∑ i, ((1 - ε) / n) • g (p i) + ε • ∑ i, w i • g (p i) := by
    intro w hw
    rw [Finset.univ.map_affineCombination p (W w) (hWsum w hw) g,
      Finset.affineCombination_eq_linear_combination _ _ _ (hWsum w hw)]
    simp only [W, Function.comp_apply, add_smul, Finset.sum_add_distrib, mul_smul,
      Finset.smul_sum]
  have hP : Finset.univ.affineCombination ℝ p (W w₁) =
      Finset.univ.affineCombination ℝ p (W w₂) := by
    refine hg (hpt w₁ hw₁ hle₁) (hpt w₂ hw₂ hle₂) ?_
    rw [himg w₁ hw₁, himg w₂ hw₂, heq]
  have hWeq := hp _ _ (hWsum w₁ hw₁) (hWsum w₂ hw₂) hP
  funext i
  have h := congrFun hWeq i
  simp only [W, add_right_inj] at h
  exact mul_left_cancel₀ hε.ne' h

theorem exists_affineEquiv_eqOn_convexHull {Ea : Type*} [NormedAddCommGroup Ea]
    [NormedSpace ℝ Ea] {c : Finset Ea} (hc : AffineIndependent ℝ ((↑) : c → Ea))
    (hcard : c.card = 4) (A₁ A₂ : Ea →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    (h₁ : InjOn A₁ (convexHull ℝ (c : Set Ea))) (h₂ : InjOn A₂ (convexHull ℝ (c : Set Ea))) :
    ∃ T : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
      ∀ q ∈ convexHull ℝ (c : Set Ea), T (A₁ q) = A₂ q := by
  classical
  have hrange : range ((↑) : c → Ea) = (c : Set Ea) := Subtype.range_coe
  have hi₁ := AffineIndependent.comp_affineMap_of_injOn hc A₁ (by rwa [hrange])
  have hi₂ := AffineIndependent.comp_affineMap_of_injOn hc A₂ (by rwa [hrange])
  have hcardι : Fintype.card c = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) + 1 := by
    rw [Fintype.card_coe, hcard, finrank_euclideanSpace_fin]
  have ht₁ : affineSpan ℝ (range (A₁ ∘ ((↑) : c → Ea))) = ⊤ :=
    hi₁.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr hcardι
  have ht₂ : affineSpan ℝ (range (A₂ ∘ ((↑) : c → Ea))) = ⊤ :=
    hi₂.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr hcardι
  let b₁ : AffineBasis c ℝ (EuclideanSpace ℝ (Fin 3)) := ⟨A₁ ∘ (↑), hi₁, ht₁⟩
  let b₂ : AffineBasis c ℝ (EuclideanSpace ℝ (Fin 3)) := ⟨A₂ ∘ (↑), hi₂, ht₂⟩
  have hne : c.Nonempty := Finset.card_pos.mp (by rw [hcard]; norm_num)
  let i₀ : c := ⟨hne.choose, hne.choose_spec⟩
  let L := (b₁.basisOf i₀).equiv (b₂.basisOf i₀) (Equiv.refl _)
  have hL : ∀ j, L (b₁.basisOf i₀ j) = b₂.basisOf i₀ j := fun j => Module.Basis.equiv_apply _ _ _ _
  let T : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (AffineEquiv.vaddConst ℝ (b₁ i₀)).symm.trans
      (L.toAffineEquiv.trans (AffineEquiv.vaddConst ℝ (b₂ i₀)))
  have hTapp : ∀ x, T x = L (x -ᵥ b₁ i₀) +ᵥ b₂ i₀ := fun x => rfl
  have hT : ∀ i, T (b₁ i) = b₂ i := by
    intro i
    rw [hTapp]
    by_cases hi : i = i₀
    · rw [hi, vsub_self, map_zero, zero_vadd]
    · have h1 : b₁ i -ᵥ b₁ i₀ = b₁.basisOf i₀ ⟨i, hi⟩ := (b₁.basisOf_apply i₀ ⟨i, hi⟩).symm
      rw [h1, hL, AffineBasis.basisOf_apply, vsub_vadd]
  refine ⟨T, fun q hq => ?_⟩
  have hEq : EqOn (T.toAffineMap.comp A₁) A₂ (c : Set Ea) := by
    intro v hv
    exact hT ⟨v, hv⟩
  exact AffineMap.eqOn_affineSpan hEq (convexHull_subset_affineSpan _ hq)

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

theorem IsCommonWallSystem.exists_transition {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {Cf Bf : Set (Finset Ea)} {BdM C : Set M} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb Eb' : ι → Set M}
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ec ℓ Eb Eb') {c : Finset Ea}
    (hc : c ∈ wallSystemCells Q) {i i' : ι} (hci : wallSystemCell ρ c ⊆ Eb' i)
    (hci' : wallSystemCell ρ c ⊆ Eb' i') :
    ∃ T : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
      ∀ z ∈ wallSystemCell ρ c, ec i' z = T (ec i z) := by
  obtain ⟨A₁, hA₁⟩ := hsys.chartAffine i c hc.1 hci
  obtain ⟨A₂, hA₂⟩ := hsys.chartAffine i' c hc.1 hci'
  have hpre : ∀ q ∈ convexHull ℝ (c : Set Ea), ∃ z ∈ wallSystemCell ρ c, ρ z = q := by
    intro q hq
    have hqQ : q ∈ Q.space := Q.convexHull_subset_space hc.1 hq
    rw [← hsys.rangeEq] at hqQ
    obtain ⟨z, rfl⟩ := hqQ
    exact ⟨z, hq, rfl⟩
  have hinj : ∀ (j : ι) (A : Ea →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)),
      wallSystemCell ρ c ⊆ Eb' j → (∀ z ∈ wallSystemCell ρ c, ec j z = A (ρ z)) →
      InjOn A (convexHull ℝ (c : Set Ea)) := by
    intro j A hcj hA p hp q hq hpq
    obtain ⟨z, hz, rfl⟩ := hpre p hp
    obtain ⟨z', hz', rfl⟩ := hpre q hq
    have hs : z ∈ (ec j).source := hsys.layerSource j (hcj hz)
    have hs' : z' ∈ (ec j).source := hsys.layerSource j (hcj hz')
    have h1 : ec j z = ec j z' := by rw [hA z hz, hA z' hz', hpq]
    rw [(ec j).injOn hs hs' h1]
  obtain ⟨T, hT⟩ := exists_affineEquiv_eqOn_convexHull (Q.indep hc.1) hc.2 A₁ A₂
    (hinj i A₁ hci hA₁) (hinj i' A₂ hci' hA₂)
  refine ⟨T, fun z hz => ?_⟩
  rw [hA₂ z hz, hA₁ z hz, hT (ρ z) hz]

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear

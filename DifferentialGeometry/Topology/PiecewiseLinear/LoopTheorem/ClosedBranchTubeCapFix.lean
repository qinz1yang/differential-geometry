/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeCrosscuts

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_union_of_eqOn_id {P Q X : Set E} (hP : IsPolyhedron P)
    (hQ : IsPolyhedron Q) {f g : E → E} (hf : IsPLHomeomorphOn f P P)
    (hg : IsPLHomeomorphOn g Q Q) (hPQ : P ∩ Q ⊆ X) (hfX : EqOn f id (P ∩ X))
    (hgX : EqOn g id (Q ∩ X)) :
    ∃ h : E → E, IsPLHomeomorphOn h (P ∪ Q) (P ∪ Q) ∧ EqOn h f P ∧ EqOn h g Q ∧
      EqOn h id ((P ∪ Q) ∩ X) := by
  obtain ⟨h, hh, hhf, hhg⟩ := exists_isPLHomeomorphOn_union hP hQ hf hg
    (fun p hp => (hfX ⟨hp.1, hPQ hp⟩).trans (hgX ⟨hp.2, hPQ hp⟩).symm)
    (fun p hp => ⟨p, hp, hfX ⟨hp.1, hPQ hp⟩⟩)
  refine ⟨h, hh, hhf, hhg, ?_⟩
  rintro p ⟨hp | hp, hpX⟩
  · exact (hhf hp).trans (hfX ⟨hp, hpX⟩)
  · exact (hhg hp).trans (hgX ⟨hp, hpX⟩)

theorem eq_of_isPLHomeomorphOn_of_separated {S X F J U₁ U₂ : Set E} (hS : IsPLSphere 2 S)
    {q : (Fin 3 → ℝ) → E} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) X) (hXS : X ⊆ S)
    (hqJ : q '' stdSimplexBoundary 2 = J) (hJF : J ⊆ F) (hFS : F ⊆ S) (hU₁ : IsOpen U₁)
    (hU₂ : IsOpen U₂) (hcover : S \ J ⊆ U₁ ∪ U₂) (hdisj : S ∩ (U₁ ∩ U₂) = ∅)
    (hF₁ : F \ J ⊆ U₁) (hF₂ : S \ F ⊆ U₂) {a b : E} (ha : a ∈ X \ J) (haU : a ∈ U₁)
    (hb : b ∈ S \ X) (hbU : b ∈ U₂) : X = F := by
  have hJX : J ⊆ X := by
    rw [← hqJ, ← hq.image_eq]
    exact image_mono fun x hx => hx.1
  have hnot : ∀ x ∈ S, x ∈ U₁ → x ∈ U₂ → False := fun x hx h1 h2 => by
    have hmem : x ∈ S ∩ (U₁ ∩ U₂) := ⟨hx, h1, h2⟩
    rw [hdisj] at hmem
    exact hmem
  have hconnX : IsPreconnected (X \ J) := by
    have h := hq.isConnected_sdiff_image_stdSimplexBoundary
    rw [hqJ] at h
    exact h.isPreconnected
  have hXJ : X \ J ⊆ U₁ := by
    have hsub : X \ J ⊆ U₁ ∪ U₂ := fun x hx => hcover ⟨hXS hx.1, hx.2⟩
    have hd : (X \ J) ∩ (U₁ ∩ U₂) = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun x hx => hnot x (hXS hx.1.1) hx.2.1 hx.2.2
    rcases isPreconnected_iff_subset_of_disjoint.mp hconnX U₁ U₂ hU₁ hU₂ hsub hd with h | h
    · exact h
    · exact (hnot a (hXS ha.1) haU (h ha)).elim
  have hconnC : IsPreconnected (S \ X) :=
    (hS.isConnected_sdiff_of_isPLBall_two ⟨q, hq⟩ hXS).isPreconnected
  have hCX : S \ X ⊆ U₂ := by
    have hsub : S \ X ⊆ U₁ ∪ U₂ := fun x hx => hcover ⟨hx.1, fun h => hx.2 (hJX h)⟩
    have hd : (S \ X) ∩ (U₁ ∩ U₂) = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun x hx => hnot x hx.1.1 hx.2.1 hx.2.2
    rcases isPreconnected_iff_subset_of_disjoint.mp hconnC U₁ U₂ hU₁ hU₂ hsub hd with h | h
    · exact (hnot b hb.1 (h hb) hbU).elim
    · exact h
  apply Subset.antisymm
  · intro x hx
    by_cases hxJ : x ∈ J
    · exact hJF hxJ
    · by_contra hxF
      exact hnot x (hXS hx) (hXJ ⟨hx, hxJ⟩) (hF₂ ⟨hXS hx, hxF⟩)
  · intro x hx
    by_contra hxX
    exact hnot x (hFS hx) (hF₁ ⟨hx, fun h => hxX (hJX h)⟩) (hCX ⟨hFS hx, hxX⟩)

end Generic

theorem lt_of_mem_spliceSquare_of_notMem {q : ℝ × ℝ} (hq : q ∈ spliceSquare)
    (hb : q ∉ spliceSquareBoundary) : -1 < q.1 ∧ q.1 < 1 ∧ -1 < q.2 ∧ q.2 < 1 := by
  have hq' := hq
  rw [mem_spliceSquare] at hq'
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hq'
  exact ⟨lt_of_le_of_ne h1 fun h => hb ⟨hq, Or.inl h.symm⟩,
    lt_of_le_of_ne h2 fun h => hb ⟨hq, Or.inr (Or.inl h)⟩,
    lt_of_le_of_ne h3 fun h => hb ⟨hq, Or.inr (Or.inr (Or.inl h.symm))⟩,
    lt_of_le_of_ne h4 fun h => hb ⟨hq, Or.inr (Or.inr (Or.inr h))⟩⟩

theorem zero_notMem_spliceSquareBoundary : (0 : ℝ × ℝ) ∉ spliceSquareBoundary := fun h => by
  rcases h.2 with h | h | h | h <;> norm_num at h

theorem zero_mem_spliceSquare : (0 : ℝ × ℝ) ∈ spliceSquare := by
  rw [mem_spliceSquare]
  norm_num

theorem tubeCellPole_mem_tubeCellSphere {z : ℝ} (hz : z = 0 ∨ z = 1) :
    ((0 : ℝ × ℝ), z) ∈ tubeCellSphere :=
  mem_tubeCellSphere_iff.mpr (Or.inl ⟨zero_mem_spliceSquare, hz⟩)

theorem tubeCellPole_zero_mem_tubeCellArc (k : Fin 4) :
    ((0 : ℝ × ℝ), (0 : ℝ)) ∈ tubeCellArc k :=
  ⟨0, ⟨le_rfl, zero_le_one⟩, tubeMeridianParam_zero _⟩

theorem tubeCellPole_one_mem_tubeCellArc (k : Fin 4) :
    ((0 : ℝ × ℝ), (1 : ℝ)) ∈ tubeCellArc k :=
  ⟨1, ⟨zero_le_one, le_rfl⟩, tubeMeridianParam_one _⟩

theorem isOpen_tubeCellOpenSquare (P : ℝ → Prop) (hP : IsOpen {z : ℝ | P z}) :
    IsOpen {q : (ℝ × ℝ) × ℝ | -1 < q.1.1 ∧ q.1.1 < 1 ∧ -1 < q.1.2 ∧ q.1.2 < 1 ∧ P q.2} := by
  have c1 : Continuous fun q : (ℝ × ℝ) × ℝ => q.1.1 := continuous_fst.comp continuous_fst
  have c2 : Continuous fun q : (ℝ × ℝ) × ℝ => q.1.2 := continuous_snd.comp continuous_fst
  exact (isOpen_lt continuous_const c1).inter ((isOpen_lt c1 continuous_const).inter
    ((isOpen_lt continuous_const c2).inter ((isOpen_lt c2 continuous_const).inter
      (hP.preimage continuous_snd))))

theorem eq_bottom_face_of_isPLHomeomorphOn {X : Set ((ℝ × ℝ) × ℝ)}
    {q : (Fin 3 → ℝ) → (ℝ × ℝ) × ℝ} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) X)
    (hXS : X ⊆ tubeCellSphere)
    (hqJ : q '' stdSimplexBoundary 2 = spliceSquareBoundary ×ˢ ({0} : Set ℝ))
    (h0 : ((0 : ℝ × ℝ), (0 : ℝ)) ∈ X) (h1 : ((0 : ℝ × ℝ), (1 : ℝ)) ∉ X) :
    X = spliceSquare ×ˢ ({0} : Set ℝ) := by
  refine eq_of_isPLHomeomorphOn_of_separated (a := ((0 : ℝ × ℝ), (0 : ℝ)))
    (b := ((0 : ℝ × ℝ), (1 : ℝ))) isPLSphere_tubeCellSphere hq hXS hqJ
    (prod_mono (fun x hx => hx.1) subset_rfl)
    (fun p hp => mem_tubeCellSphere_iff.mpr (Or.inl ⟨hp.1, Or.inl hp.2⟩))
    (isOpen_tubeCellOpenSquare (fun z => z < 1 / 2) (isOpen_lt continuous_id continuous_const))
    (U₂ := {q : (ℝ × ℝ) × ℝ | 0 < q.2}) (isOpen_lt continuous_const continuous_snd) ?_ ?_ ?_ ?_
    ⟨h0, fun h => zero_notMem_spliceSquareBoundary h.1⟩ (by norm_num)
    ⟨tubeCellPole_mem_tubeCellSphere (Or.inr rfl), h1⟩ (by norm_num)
  · rintro p ⟨hpS, hpJ⟩
    obtain ⟨hsq, hz0, -⟩ := mem_tubeCellSphere_bounds hpS
    rcases hz0.lt_or_eq with hz | hz
    · exact Or.inr hz
    · have hnb : p.1 ∉ spliceSquareBoundary := fun hb => hpJ ⟨hb, hz.symm⟩
      obtain ⟨a1, a2, a3, a4⟩ := lt_of_mem_spliceSquare_of_notMem hsq hnb
      exact Or.inl ⟨a1, a2, a3, a4, by linarith⟩
  · refine eq_empty_iff_forall_notMem.mpr fun p hp => ?_
    obtain ⟨hpS, ⟨a1, a2, a3, a4, a5⟩, hz⟩ := hp
    change 0 < p.2 at hz
    rcases tubeCellSphere_snd_eq_of_lt hpS a1 a2 a3 a4 with h | h <;> linarith
  · rintro p ⟨⟨hsq, hz⟩, hpJ⟩
    have hnb : p.1 ∉ spliceSquareBoundary := fun hb => hpJ ⟨hb, hz⟩
    obtain ⟨a1, a2, a3, a4⟩ := lt_of_mem_spliceSquare_of_notMem hsq hnb
    have hz' : p.2 = 0 := hz
    exact ⟨a1, a2, a3, a4, by linarith⟩
  · rintro p ⟨hpS, hpF⟩
    obtain ⟨hsq, hz0, -⟩ := mem_tubeCellSphere_bounds hpS
    rcases hz0.lt_or_eq with hz | hz
    · exact hz
    · exact absurd ⟨hsq, hz.symm⟩ hpF

theorem eq_top_face_of_isPLHomeomorphOn {X : Set ((ℝ × ℝ) × ℝ)}
    {q : (Fin 3 → ℝ) → (ℝ × ℝ) × ℝ} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) X)
    (hXS : X ⊆ tubeCellSphere)
    (hqJ : q '' stdSimplexBoundary 2 = spliceSquareBoundary ×ˢ ({1} : Set ℝ))
    (h1 : ((0 : ℝ × ℝ), (1 : ℝ)) ∈ X) (h0 : ((0 : ℝ × ℝ), (0 : ℝ)) ∉ X) :
    X = spliceSquare ×ˢ ({1} : Set ℝ) := by
  refine eq_of_isPLHomeomorphOn_of_separated (a := ((0 : ℝ × ℝ), (1 : ℝ)))
    (b := ((0 : ℝ × ℝ), (0 : ℝ))) isPLSphere_tubeCellSphere hq hXS hqJ
    (prod_mono (fun x hx => hx.1) subset_rfl)
    (fun p hp => mem_tubeCellSphere_iff.mpr (Or.inl ⟨hp.1, Or.inr hp.2⟩))
    (isOpen_tubeCellOpenSquare (fun z => 1 / 2 < z) (isOpen_lt continuous_const continuous_id))
    (U₂ := {q : (ℝ × ℝ) × ℝ | q.2 < 1}) (isOpen_lt continuous_snd continuous_const) ?_ ?_ ?_ ?_
    ⟨h1, fun h => zero_notMem_spliceSquareBoundary h.1⟩ (by norm_num)
    ⟨tubeCellPole_mem_tubeCellSphere (Or.inl rfl), h0⟩ (by norm_num)
  · rintro p ⟨hpS, hpJ⟩
    obtain ⟨hsq, -, hz1⟩ := mem_tubeCellSphere_bounds hpS
    rcases hz1.lt_or_eq with hz | hz
    · exact Or.inr hz
    · have hnb : p.1 ∉ spliceSquareBoundary := fun hb => hpJ ⟨hb, hz⟩
      obtain ⟨a1, a2, a3, a4⟩ := lt_of_mem_spliceSquare_of_notMem hsq hnb
      exact Or.inl ⟨a1, a2, a3, a4, by linarith⟩
  · refine eq_empty_iff_forall_notMem.mpr fun p hp => ?_
    obtain ⟨hpS, ⟨a1, a2, a3, a4, a5⟩, hz⟩ := hp
    change p.2 < 1 at hz
    change 1 / 2 < p.2 at a5
    rcases tubeCellSphere_snd_eq_of_lt hpS a1 a2 a3 a4 with h | h <;> linarith
  · rintro p ⟨⟨hsq, hz⟩, hpJ⟩
    have hnb : p.1 ∉ spliceSquareBoundary := fun hb => hpJ ⟨hb, hz⟩
    obtain ⟨a1, a2, a3, a4⟩ := lt_of_mem_spliceSquare_of_notMem hsq hnb
    have hz' : p.2 = 1 := hz
    exact ⟨a1, a2, a3, a4, by linarith⟩
  · rintro p ⟨hpS, hpF⟩
    obtain ⟨hsq, -, hz1⟩ := mem_tubeCellSphere_bounds hpS
    rcases hz1.lt_or_eq with hz | hz
    · exact hz
    · exact absurd ⟨hsq, hz⟩ hpF

theorem exists_tubeSector_double_move {k : Fin 4} {B₀ B₁ : Set ((ℝ × ℝ) × ℝ)}
    {γ₀ γ₁ : ℝ → (ℝ × ℝ) × ℝ} (hγ₀ : IsPLHomeomorphOn γ₀ (Icc 0 1) B₀)
    (hγ₁ : IsPLHomeomorphOn γ₁ (Icc 0 1) B₁)
    (h00 : γ₀ 0 = (fourSpokeModelLeaf k, 0)) (h01 : γ₀ 1 = (fourSpokeModelLeaf (k + 1), 0))
    (h10 : γ₁ 0 = (fourSpokeModelLeaf k, 1)) (h11 : γ₁ 1 = (fourSpokeModelLeaf (k + 1), 1))
    (hB₀ : B₀ ⊆ tubeSector k) (hB₁ : B₁ ⊆ tubeSector k)
    (hB₀J : B₀ ∩ (tubeCellArc k ∪ tubeCellArc (k + 1)) = {γ₀ 0, γ₀ 1})
    (hB₁J : B₁ ∩ (tubeCellArc k ∪ tubeCellArc (k + 1)) = {γ₁ 0, γ₁ 1})
    (hdis : Disjoint B₀ B₁) :
    ∃ M : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ, IsPLHomeomorphOn M (tubeSector k) (tubeSector k) ∧
      EqOn M id (tubeCellArc k ∪ tubeCellArc (k + 1)) ∧ M '' B₀ = tubeEdge k 0 ∧
        M '' B₁ = tubeEdge k 1 := by
  obtain ⟨u, hu, huJ⟩ := exists_tubeSector_param k
  obtain ⟨H₁, hH₁, hH₁J, hH₁B⟩ := exists_isPLHomeomorphOn_crosscut_move hu huJ hγ₀
    (isPLHomeomorphOn_tubeEdgeParam k 0) hB₀ (tubeEdge_subset_tubeSector k (by norm_num)) hB₀J
    (by rw [h00, h01]; exact tubeEdge_inter_tubeCellArc k (Or.inl rfl))
    (by rw [h00, tubeEdgeParam_zero]) (by rw [h01, tubeEdgeParam_one])
  have hB₁poly : IsPolyhedron B₁ :=
    ((isPLBall_Icc (zero_lt_one' ℝ)).of_isPLHomeomorphOn hγ₁).isPolyhedron
  have hγ₁' : IsPLHomeomorphOn (H₁ ∘ γ₁) (Icc 0 1) (H₁ '' B₁) :=
    hγ₁.trans (hH₁.restrict hB₁poly hB₁)
  have hends : γ₁ 0 ∈ B₁ ∩ (tubeCellArc k ∪ tubeCellArc (k + 1)) ∧
      γ₁ 1 ∈ B₁ ∩ (tubeCellArc k ∪ tubeCellArc (k + 1)) := by
    rw [hB₁J]
    exact ⟨Or.inl rfl, Or.inr rfl⟩
  have hH₁γ₁0 : H₁ (γ₁ 0) = γ₁ 0 := hH₁J hends.1.2
  have hH₁γ₁1 : H₁ (γ₁ 1) = γ₁ 1 := hH₁J hends.2.2
  have hB₁'S : H₁ '' B₁ ⊆ tubeSector k := (image_mono hB₁).trans hH₁.image_eq.subset
  have hB₁'e : Disjoint (H₁ '' B₁) (tubeEdge k 0) := by
    rw [← hH₁B, disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hxy := hH₁.bijOn.injOn (hB₀ hy) (hB₁ hx) hyx
    exact disjoint_left.mp hdis (hxy ▸ hy) hx
  have hB₁'U : H₁ '' B₁ ⊆ tubeSectorUpper k :=
    subset_tubeSectorUpper_of_isPreconnected
      (fun p hp => ⟨hB₁'S hp, disjoint_left.mp hB₁'e hp⟩)
      (hγ₁'.image_eq ▸ isPreconnected_Icc.image _ hγ₁'.isPiecewiseAffineOn.continuousOn)
      ⟨γ₁ 0, hends.1.1, hH₁γ₁0⟩ (by rw [h10]; norm_num)
  obtain ⟨u', hu', hu'J⟩ := exists_tubeSectorUpper_param k
  have hB₁'J : H₁ '' B₁ ∩ (tubeUpperArc k ∪ (tubeEdge k 0 ∪ tubeUpperArc (k + 1))) =
      {(H₁ ∘ γ₁) 0, (H₁ ∘ γ₁) 1} := by
    apply Subset.antisymm
    · rintro p ⟨⟨x, hx, rfl⟩, hJ⟩
      have hxJ : H₁ x ∈ tubeCellArc k ∪ tubeCellArc (k + 1) := by
        rcases hJ with hJ | hJ | hJ
        · exact Or.inl (tubeUpperArc_subset_tubeCellArc k hJ)
        · exact absurd hJ (disjoint_left.mp hB₁'e ⟨x, hx, rfl⟩)
        · exact Or.inr (tubeUpperArc_subset_tubeCellArc (k + 1) hJ)
      have hHx : H₁ (H₁ x) = H₁ x := hH₁J hxJ
      have hxeq : x = H₁ x := hH₁.bijOn.injOn (hB₁ hx) (hB₁'S ⟨x, hx, rfl⟩) hHx.symm
      have hxB : x ∈ B₁ ∩ (tubeCellArc k ∪ tubeCellArc (k + 1)) := by
        refine ⟨hx, ?_⟩
        rw [hxeq]
        exact hxJ
      rw [hB₁J] at hxB
      rcases hxB with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro p (rfl | rfl)
      · refine ⟨⟨γ₁ 0, hends.1.1, rfl⟩, Or.inl ?_⟩
        change H₁ (γ₁ 0) ∈ tubeUpperArc k
        rw [hH₁γ₁0, h10]
        exact ⟨3 / 4, ⟨by norm_num, by norm_num⟩, tubeMeridianParam_threeQuarter _⟩
      · refine ⟨⟨γ₁ 1, hends.2.1, rfl⟩, Or.inr (Or.inr ?_)⟩
        change H₁ (γ₁ 1) ∈ tubeUpperArc (k + 1)
        rw [hH₁γ₁1, h11]
        exact ⟨3 / 4, ⟨by norm_num, by norm_num⟩, tubeMeridianParam_threeQuarter _⟩
  obtain ⟨H₂, hH₂, hH₂J, hH₂B⟩ := exists_isPLHomeomorphOn_crosscut_move hu' hu'J hγ₁'
    (isPLHomeomorphOn_tubeEdgeParam k 1) hB₁'U (tubeEdge_one_subset_tubeSectorUpper k) hB₁'J
    (by
      rw [tubeEdge_one_inter_tubeSectorUpper_boundary, Function.comp_apply, Function.comp_apply,
        hH₁γ₁0, hH₁γ₁1, h10, h11])
    (by rw [Function.comp_apply, hH₁γ₁0, h10, tubeEdgeParam_zero])
    (by rw [Function.comp_apply, hH₁γ₁1, h11, tubeEdgeParam_one])
  have hL := isPolyhedron_tubeSectorLower k
  obtain ⟨H₃, hH₃, hH₃L, hH₃U⟩ := exists_isPLHomeomorphOn_union hL
    (isPolyhedron_tubeSectorUpper k) hL.isPLHomeomorphOn_id hH₂
    (fun p hp => by
      rw [tubeSectorLower_inter_tubeSectorUpper] at hp
      exact (hH₂J (Or.inr (Or.inl hp))).symm)
    (fun p hp => ⟨p, hp, rfl⟩)
  rw [tubeSectorLower_union_tubeSectorUpper] at hH₃
  refine ⟨H₃ ∘ H₁, hH₁.trans hH₃, ?_, ?_, ?_⟩
  · intro p hp
    have hH₁p : H₁ p = p := hH₁J hp
    change H₃ (H₁ p) = p
    rw [hH₁p]
    have hpS : p ∈ tubeSector k :=
      union_subset (tubeCellArc_subset_tubeSector k) (tubeCellArc_add_one_subset_tubeSector k) hp
    rw [← tubeSectorLower_union_tubeSectorUpper] at hpS
    rcases hpS with hpL | hpU
    · exact hH₃L hpL
    · rw [hH₃U hpU]
      apply hH₂J
      rcases hp with hp | hp
      · exact Or.inl (mem_tubeUpperArc_of_mem_tubeCellArc hp hpU.2)
      · exact Or.inr (Or.inr (mem_tubeUpperArc_of_mem_tubeCellArc hp hpU.2))
  · have he : tubeEdge k 0 ⊆ tubeSectorLower k := by
      rw [← tubeSectorLower_inter_tubeSectorUpper]
      exact inter_subset_left
    rw [image_comp, hH₁B, (hH₃L.mono he).image_eq, image_id]
  · rw [image_comp, (hH₃U.mono hB₁'U).image_eq, hH₂B]

theorem tubeSector_inter_tubeCellArc_subset (i j : Fin 4) :
    tubeSector j ∩ tubeCellArc i ⊆ tubeCellArc j ∪ tubeCellArc (j + 1) := by
  rintro p ⟨hpS, hpA⟩
  by_contra hn
  have hO : p ∈ tubeSector j \ (tubeCellArc j ∪ tubeCellArc (j + 1)) := ⟨hpS, hn⟩
  rw [tubeSector_sdiff] at hO
  obtain ⟨-, h1, h2⟩ := hO
  obtain ⟨-, h3, h4⟩ := (mem_tubeCellArc_iff_tubeLeafCoord i).mp hpA
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
    rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl <;>
    simp only [tubeLeafCoord_zero, tubeLeafCoord_one, tubeLeafCoord_two, tubeLeafCoord_three,
      tubeLeafCoord_zero_add_one, tubeLeafCoord_one_add_one, tubeLeafCoord_two_add_one,
      tubeLeafCoord_three_add_one] at h1 h2 h3 h4 <;>
    linarith

theorem exists_mem_tubeSector {p : (ℝ × ℝ) × ℝ} (hp : p ∈ tubeCellSphere) :
    ∃ k, p ∈ tubeSector k := by
  rcases le_total 0 p.1.1 with hx | hx <;> rcases le_total 0 p.1.2 with hy | hy
  · exact ⟨0, hp, by rw [tubeLeafCoord_zero]; exact hx,
      by rw [tubeLeafCoord_zero_add_one]; exact hy⟩
  · exact ⟨3, hp, by rw [tubeLeafCoord_three]; linarith,
      by rw [tubeLeafCoord_three_add_one]; exact hx⟩
  · exact ⟨1, hp, by rw [tubeLeafCoord_one]; exact hy,
      by rw [tubeLeafCoord_one_add_one]; linarith⟩
  · exact ⟨2, hp, by rw [tubeLeafCoord_two]; linarith,
      by rw [tubeLeafCoord_two_add_one]; linarith⟩

theorem exists_tubeCellSphere_glue {M : Fin 4 → (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ}
    (hM : ∀ k, IsPLHomeomorphOn (M k) (tubeSector k) (tubeSector k))
    (hMid : ∀ k, EqOn (M k) id (tubeCellArc k ∪ tubeCellArc (k + 1))) :
    ∃ h : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ, IsPLHomeomorphOn h tubeCellSphere tubeCellSphere ∧
      (∀ k, EqOn h (M k) (tubeSector k)) ∧ ∀ k, EqOn h id (tubeCellArc k) := by
  have hfix : ∀ k, EqOn (M k) id (tubeSector k ∩ ⋃ i, tubeCellArc i) := by
    rintro k p ⟨hpS, hpX⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hpX
    exact hMid k (tubeSector_inter_tubeCellArc_subset i k ⟨hpS, hi⟩)
  have hinter : ∀ j k : Fin 4, j ≠ k → tubeSector j ∩ tubeSector k ⊆ ⋃ i, tubeCellArc i := by
    rintro j k hjk p ⟨hj, hk⟩
    by_contra hn
    have hj' : p ∈ tubeSector j \ (tubeCellArc j ∪ tubeCellArc (j + 1)) :=
      ⟨hj, fun h => hn (h.elim (fun h => mem_iUnion.mpr ⟨j, h⟩)
        fun h => mem_iUnion.mpr ⟨j + 1, h⟩)⟩
    have hk' : p ∈ tubeSector k \ (tubeCellArc k ∪ tubeCellArc (k + 1)) :=
      ⟨hk, fun h => hn (h.elim (fun h => mem_iUnion.mpr ⟨k, h⟩)
        fun h => mem_iUnion.mpr ⟨k + 1, h⟩)⟩
    rw [tubeSector_sdiff] at hj' hk'
    exact not_tubeLeafCoord_pos_pos_of_ne hjk p.1 ⟨hj'.2.1, hj'.2.2, hk'.2.1, hk'.2.2⟩
  have hP := isPolyhedron_tubeSector
  obtain ⟨h₁, hh₁, hh₁0, hh₁1, hh₁X⟩ := exists_isPLHomeomorphOn_union_of_eqOn_id (hP 0) (hP 1)
    (hM 0) (hM 1) (hinter 0 1 (by decide)) (hfix 0) (hfix 1)
  obtain ⟨h₂, hh₂, hh₂01, hh₂2, hh₂X⟩ := exists_isPLHomeomorphOn_union_of_eqOn_id
    ((hP 0).union (hP 1)) (hP 2) hh₁ (hM 2)
    (by
      rw [union_inter_distrib_right]
      exact union_subset (hinter 0 2 (by decide)) (hinter 1 2 (by decide)))
    hh₁X (hfix 2)
  obtain ⟨h₃, hh₃, hh₃012, hh₃3, hh₃X⟩ := exists_isPLHomeomorphOn_union_of_eqOn_id
    (((hP 0).union (hP 1)).union (hP 2)) (hP 3) hh₂ (hM 3)
    (by
      rw [union_inter_distrib_right, union_inter_distrib_right]
      exact union_subset (union_subset (hinter 0 3 (by decide)) (hinter 1 3 (by decide)))
        (hinter 2 3 (by decide)))
    hh₂X (hfix 3)
  have hcover : tubeSector 0 ∪ tubeSector 1 ∪ tubeSector 2 ∪ tubeSector 3 = tubeCellSphere := by
    apply Subset.antisymm
    · exact union_subset (union_subset (union_subset (fun p hp => hp.1) fun p hp => hp.1)
        fun p hp => hp.1) fun p hp => hp.1
    · intro p hp
      obtain ⟨k, hk⟩ := exists_mem_tubeSector hp
      rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inl hk))
      · exact Or.inl (Or.inl (Or.inr hk))
      · exact Or.inl (Or.inr hk)
      · exact Or.inr hk
  rw [hcover] at hh₃
  refine ⟨h₃, hh₃, ?_, ?_⟩
  · intro k
    rcases fourSpokeIndexCases k with rfl | rfl | rfl | rfl
    · exact fun p hp =>
        (hh₃012 (Or.inl (Or.inl hp))).trans ((hh₂01 (Or.inl hp)).trans (hh₁0 hp))
    · exact fun p hp =>
        (hh₃012 (Or.inl (Or.inr hp))).trans ((hh₂01 (Or.inr hp)).trans (hh₁1 hp))
    · exact fun p hp => (hh₃012 (Or.inr hp)).trans (hh₂2 hp)
    · exact hh₃3
  · intro k p hp
    have hpS := tubeCellArc_subset_tubeCellSphere k hp
    rw [← hcover] at hpS
    exact hh₃X ⟨hpS, mem_iUnion.mpr ⟨k, hp⟩⟩

theorem exists_tubeCellSphere_capFix {Δ₀ Δ₁ : Set ((ℝ × ℝ) × ℝ)}
    {q₀ q₁ : (Fin 3 → ℝ) → (ℝ × ℝ) × ℝ}
    (hq₀ : IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ₀)
    (hq₁ : IsPLHomeomorphOn q₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ₁)
    (hΔ₀ : Δ₀ ⊆ tubeCellSphere) (hΔ₁ : Δ₁ ⊆ tubeCellSphere) (hdis : Disjoint Δ₀ Δ₁)
    (hb₀ : ∀ k, q₀ '' stdSimplexBoundary 2 ∩ tubeCellArc k = {(fourSpokeModelLeaf k, 0)})
    (hb₁ : ∀ k, q₁ '' stdSimplexBoundary 2 ∩ tubeCellArc k = {(fourSpokeModelLeaf k, 1)})
    (hp₀ : ((0 : ℝ × ℝ), (0 : ℝ)) ∈ Δ₀) (hp₁ : ((0 : ℝ × ℝ), (1 : ℝ)) ∈ Δ₁) :
    ∃ h : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ, IsPLHomeomorphOn h tubeCellSphere tubeCellSphere ∧
      (∀ k, EqOn h id (tubeCellArc k)) ∧ h '' Δ₀ = spliceSquare ×ˢ ({0} : Set ℝ) ∧
        h '' Δ₁ = spliceSquare ×ˢ ({1} : Set ℝ) := by
  have hsub : ∀ {q : (Fin 3 → ℝ) → (ℝ × ℝ) × ℝ} {Δ : Set ((ℝ × ℝ) × ℝ)},
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ → q '' stdSimplexBoundary 2 ⊆ Δ := by
    intro q Δ hq
    rw [← hq.image_eq]
    exact image_mono fun x hx => hx.1
  obtain ⟨B₀, β₀, hβ₀, hβ₀0, hβ₀1, hB₀S, hB₀J, hB₀C, hC₀B⟩ :=
    exists_tubeCrosscuts hq₀.isPLSphere_image_stdSimplexBoundary ((hsub hq₀).trans hΔ₀) hb₀
  obtain ⟨B₁, β₁, hβ₁, hβ₁0, hβ₁1, hB₁S, hB₁J, hB₁C, hC₁B⟩ :=
    exists_tubeCrosscuts hq₁.isPLSphere_image_stdSimplexBoundary ((hsub hq₁).trans hΔ₁) hb₁
  have hM : ∀ k, ∃ M : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ,
      IsPLHomeomorphOn M (tubeSector k) (tubeSector k) ∧
        EqOn M id (tubeCellArc k ∪ tubeCellArc (k + 1)) ∧ M '' B₀ k = tubeEdge k 0 ∧
          M '' B₁ k = tubeEdge k 1 := fun k =>
    exists_tubeSector_double_move (hβ₀ k) (hβ₁ k) (hβ₀0 k) (hβ₀1 k) (hβ₁0 k) (hβ₁1 k)
      (hB₀S k) (hB₁S k) (hB₀J k) (hB₁J k)
      (disjoint_of_subset ((hB₀C k).trans (hsub hq₀)) ((hB₁C k).trans (hsub hq₁)) hdis)
  choose M hMpl hMid hM0 hM1 using hM
  obtain ⟨h, hh, hhM, hhid⟩ := exists_tubeCellSphere_glue hMpl hMid
  have hfix0 : h ((0 : ℝ × ℝ), (0 : ℝ)) = ((0 : ℝ × ℝ), (0 : ℝ)) :=
    hhid 0 (tubeCellPole_zero_mem_tubeCellArc 0)
  have hfix1 : h ((0 : ℝ × ℝ), (1 : ℝ)) = ((0 : ℝ × ℝ), (1 : ℝ)) :=
    hhid 0 (tubeCellPole_one_mem_tubeCellArc 0)
  have himage : ∀ {C : Set ((ℝ × ℝ) × ℝ)} {B : Fin 4 → Set ((ℝ × ℝ) × ℝ)} {c : ℝ},
      (∀ k, B k ⊆ tubeSector k) → (∀ k, M k '' B k = tubeEdge k c) → (∀ k, B k ⊆ C) →
        C ⊆ ⋃ k, B k → h '' C = spliceSquareBoundary ×ˢ ({c} : Set ℝ) := by
    intro C B c hBS hMB hBC hCB
    rw [← iUnion_tubeEdge c]
    apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      obtain ⟨k, hk⟩ := mem_iUnion.mp (hCB hp)
      rw [hhM k (hBS k hk)]
      exact mem_iUnion.mpr ⟨k, hMB k ▸ mem_image_of_mem (M k) hk⟩
    · refine iUnion_subset fun k => ?_
      rw [← hMB k, ← ((hhM k).mono (hBS k)).image_eq]
      exact image_mono (hBC k)
  have hpoly : ∀ {q : (Fin 3 → ℝ) → (ℝ × ℝ) × ℝ} {Δ : Set ((ℝ × ℝ) × ℝ)},
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ → Δ ⊆ tubeCellSphere →
        IsPLHomeomorphOn (h ∘ q) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (h '' Δ) := fun hq hΔ =>
    hq.trans (hh.restrict (IsPLBall.isPolyhedron ⟨_, hq⟩) hΔ)
  have hsphere : ∀ {Δ : Set ((ℝ × ℝ) × ℝ)}, Δ ⊆ tubeCellSphere → h '' Δ ⊆ tubeCellSphere :=
    fun hΔ => (image_mono hΔ).trans hh.image_eq.subset
  refine ⟨h, hh, hhid, ?_, ?_⟩
  · refine eq_bottom_face_of_isPLHomeomorphOn (hpoly hq₀ hΔ₀) (hsphere hΔ₀)
      (by rw [image_comp]; exact himage hB₀S hM0 hB₀C hC₀B) ⟨_, hp₀, hfix0⟩ ?_
    rintro ⟨x, hx, hxe⟩
    have hxp := hh.bijOn.injOn (hΔ₀ hx) (hΔ₁ hp₁) (hxe.trans hfix1.symm)
    rw [hxp] at hx
    exact disjoint_left.mp hdis hx hp₁
  · refine eq_top_face_of_isPLHomeomorphOn (hpoly hq₁ hΔ₁) (hsphere hΔ₁)
      (by rw [image_comp]; exact himage hB₁S hM1 hB₁C hC₁B) ⟨_, hp₁, hfix1⟩ ?_
    rintro ⟨x, hx, hxe⟩
    have hxp := hh.bijOn.injOn (hΔ₁ hx) (hΔ₀ hp₀) (hxe.trans hfix0.symm)
    rw [hxp] at hx
    exact disjoint_left.mp hdis hp₀ hx

end DifferentialGeometry.Topology.PiecewiseLinear

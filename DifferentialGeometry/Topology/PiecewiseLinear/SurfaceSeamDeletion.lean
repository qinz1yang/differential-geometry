/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerSeams

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def IsProtectedReplacement (X Y F Ω : Set E3) : Prop :=
  Y \ Ω = X \ Ω ∧ Y ∩ F = X ∩ F

def IsSeparatorIn (I M H K : Set E3) : Prop :=
  IsClosed (((↑) : I → E3) ⁻¹' M) ∧
    Separates (((↑) : I → E3) ⁻¹' M) (((↑) : I → E3) ⁻¹' H)
      (((↑) : I → E3) ⁻¹' K)

def IsInnermostSplitStep (I H K C C' L L' T F Ω : Set E3) : Prop :=
  IsSeparatorIn I C' H K ∧ IsProtectedReplacement C C' F Ω ∧
    C' = T ∪ L' ∧ T ⊆ C' ∧ (traceCircles L T).Finite ∧ (traceCircles L' T).Finite ∧
      nullTraceCount L' T < nullTraceCount L T

theorem pairwiseDisjoint_traceCircles (L T : Set E3) :
    (traceCircles L T).PairwiseDisjoint id := by
  rintro C ⟨x, -, rfl, -⟩ D ⟨y, -, rfl, -⟩ hne
  refine disjoint_left.mpr fun z hzx hzy => ?_
  exact hne ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)

theorem traceCircles_eq_sdiff_singleton {L L' T G : Set E3}
    (hfin : (traceCircles L T).Finite)
    (hcover : L ∩ T = ⋃ H ∈ traceCircles L T, H)
    (hG : G ∈ traceCircles L T) (heq : L' ∩ T = (L ∩ T) \ G) :
    traceCircles L' T = traceCircles L T \ {G} := by
  classical
  let F := traceCircles L T \ {G}
  have hF : F.Finite := hfin.sdiff
  let _ : Finite F := hF.to_subtype
  have hFcover : L' ∩ T = ⋃ H : F, (H : Set E3) := by
    rw [heq]
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx, hxG⟩
      obtain ⟨H, hH, hxH⟩ := mem_iUnion₂.mp (hcover ▸ hx)
      exact mem_iUnion.mpr ⟨⟨H, hH, fun heq => hxG (heq ▸ hxH)⟩, hxH⟩
    · rintro x hx
      obtain ⟨H, hxH⟩ := mem_iUnion.mp hx
      refine ⟨traceCircles_subset H.property.1 hxH, ?_⟩
      exact fun hxG => disjoint_left.mp
        (pairwiseDisjoint_traceCircles L T H.property.1 hG H.property.2) hxH hxG
  have hdis : Pairwise fun H H' : F => Disjoint (H : Set E3) (H' : Set E3) := by
    intro H H' hne
    exact pairwiseDisjoint_traceCircles L T H.property.1 H'.property.1
      (fun heq => hne (Subtype.ext heq))
  rw [traceCircles_eq_range_of_finite_circle_union
    (fun H : F => traceCircles_isPLSphere H.property.1) hdis hFcover]
  exact Subtype.range_coe_subtype

theorem nullTraceCount_lt_of_erase {L L' T G : Set E3}
    (hfin : (traceCircles L T).Finite) (hG : G ∈ traceCircles L T)
    (hnull : boundsDiskIn G T) (heq : traceCircles L' T = traceCircles L T \ {G}) :
    nullTraceCount L' T < nullTraceCount L T := by
  unfold nullTraceCount
  rw [heq]
  apply Set.ncard_lt_ncard (ssubset_of_subset_not_subset ?_ ?_)
    (hfin.subset fun _ h => h.1)
  · intro H hH
    exact ⟨hH.1.1, hH.2⟩
  · intro hsub
    exact (hsub ⟨hG, hnull⟩).1.2 rfl

private theorem annulus_ends {A G J : Set E3} (hA : IsPLAnnulusWithEnds A G J) :
    G ⊆ A ∧ J ⊆ A ∧ Disjoint G J := by
  obtain ⟨Q, ρ, -, hρ, rfl, rfl⟩ := hA
  have h0 : Q ×ˢ {(0 : ℝ)} ⊆ Q ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz => ⟨hz.1, hz.2.symm ▸ ⟨le_rfl, zero_le_one⟩⟩
  have h1 : Q ×ˢ {(1 : ℝ)} ⊆ Q ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz => ⟨hz.1, hz.2.symm ▸ ⟨zero_le_one, le_rfl⟩⟩
  refine ⟨(image_mono h0).trans hρ.image_eq.subset,
    (image_mono h1).trans hρ.image_eq.subset, ?_⟩
  apply disjoint_left.mpr
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
  have hab := hρ.bijOn.injOn (h1 hb) (h0 ha) hba
  have : (1 : ℝ) = 0 := hb.2.symm.trans ((congrArg Prod.snd hab).trans ha.2)
  exact one_ne_zero this

theorem exists_disk_split_reducing_seams_with_annulus (h303 : Moise303)
    (I H K R T L Δ D₁ D₂ Ω F : Set E3) (r r₁ r₂ : (Fin 3 → ℝ) → E3)
    (hI : IsOpen I) (hIc : IsConnected I) (hHI : H ⊆ I) (hKI : K ⊆ I)
    (hHK : Disjoint H K) (hH : IsClosed (((↑) : I → E3) ⁻¹' H))
    (hK : IsClosed (((↑) : I → E3) ⁻¹' K)) (hCI : (R ∪ (T ∪ L)) ⊆ I)
    (hC : IsSeparatorIn I ((R ∪ (T ∪ L))) H K)
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ) (hΔT : Δ ⊆ T)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁)
    (hr₂ : IsPLHomeomorphOn r₂ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₂)
    (hpair : D₁ ∩ D₂ = Δ) (hD₁T : D₁ ∩ T = Δ)
    (hsub : D₁ ∪ D₂ ⊆ (R ∪ (T ∪ L))) (hnear : D₁ ∪ D₂ ∈ 𝓝ˢ[(R ∪ (T ∪ L))] Δ)
    (hΔ₁ : Δ ⊆ D₁ \ r₁ '' stdSimplexBoundary 2)
    (hΔ₂ : Δ ⊆ D₂ \ r₂ '' stdSimplexBoundary 2)
    (hΩ : IsOpen Ω) (hΔΩ : Δ ⊆ Ω) (hΩI : Ω ⊆ I) (hΩHK : Disjoint Ω (H ∪ K))
    (hR : Disjoint R Ω) (hF : Disjoint F Ω) (hfin : (traceCircles L T).Finite)
    (hcover : L ∩ T = ⋃ G ∈ traceCircles L T, G)
    (hG : r '' stdSimplexBoundary 2 ∈ traceCircles L T) :
    ∃ C' L' : Set E3, IsSeparatorIn I C' H K ∧
      IsProtectedReplacement (R ∪ (T ∪ L)) C' F Ω ∧ C' = R ∪ (T ∪ L') ∧ T ⊆ C' ∧
      traceCircles L' T = traceCircles L T \ {r '' stdSimplexBoundary 2} ∧
      nullTraceCount L' T < nullTraceCount L T ∧ L' \ Ω = L \ Ω ∧
      ∃ A Δ' J : Set E3, IsPLAnnulusWithEnds A (r '' stdSimplexBoundary 2) J ∧
        A ⊆ D₁ ∩ Ω ∧ A ∩ Δ = r '' stdSimplexBoundary 2 ∧ IsPLBall 2 Δ' ∧ Δ' ⊆ Ω ∧
        Δ' ∩ (R ∪ (T ∪ L)) = J ∧ L' = (L \ (A \ J)) ∪ Δ' ∧
        L' ∩ T = (L ∩ T) \ (r '' stdSimplexBoundary 2) ∧
        ∃ r' : (Fin 3 → ℝ) → E3, IsPLHomeomorphOn r' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ' ∧
          r' '' stdSimplexBoundary 2 = J := by
  let G := r '' stdSimplexBoundary 2
  obtain ⟨C', A, Δ', J, r', hC'cl, hC'I, hsep', hout, -, hA, hAΩ, hAΔ,
      hr', hJ, hΔ'Ω, hΔ'C, hC'eq⟩ :=
    h303 I H K ((R ∪ (T ∪ L))) Δ D₁ D₂ Ω r r₁ r₂ hI hIc hHI hKI hHK hH hK hCI hC.1 hC.2
      hr (hΔT.trans (subset_union_left.trans subset_union_right)) hr₁ hr₂ hpair hsub hnear
      hΔ₁ hΔ₂ hΩ hΔΩ hΩI hΩHK
  let L' := (L \ (A \ J)) ∪ Δ'
  obtain ⟨hGA, hJA, hGJ⟩ := annulus_ends hA
  have hAT : A ∩ T = G := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hxA, hxT⟩
      exact hAΔ.subset ⟨hxA, hD₁T.subset ⟨(hAΩ hxA).1, hxT⟩⟩
    · intro x hxG
      exact ⟨hGA hxG, (traceCircles_subset hG hxG).2⟩
  have hJT : Disjoint J T := disjoint_left.mpr fun x hxJ hxT =>
    disjoint_left.mp hGJ (hAT.subset ⟨hJA hxJ, hxT⟩) hxJ
  have hΔ'T : Disjoint Δ' T := disjoint_left.mpr fun x hxΔ hxT =>
    disjoint_left.mp hJT (hΔ'C.subset ⟨hxΔ, Or.inr (Or.inl hxT)⟩) hxT
  have hC' : C' = R ∪ (T ∪ L') := by
    rw [hC'eq]
    ext x
    have hAG : x ∈ A → x ∈ T → x ∈ G := fun hxA hxT => hAT.subset ⟨hxA, hxT⟩
    have hGT : x ∈ G → x ∈ T := fun hxG => (traceCircles_subset hG hxG).2
    have hRA : x ∈ R → x ∈ A → False :=
      fun hxR hxA => disjoint_left.mp hR hxR (hAΩ hxA).2
    simp only [L', mem_union, mem_sdiff]
    constructor
    · rintro (⟨hxC, hxcut⟩ | hxcap)
      · rcases hxC with hxR | hxT | hxL
        · exact Or.inl hxR
        · exact Or.inr (Or.inl hxT)
        · by_cases hxG : x ∈ G
          · exact Or.inr (Or.inl (hGT hxG))
          · refine Or.inr (Or.inr (Or.inl ⟨hxL, ?_⟩))
            rintro ⟨hxA, hxJ⟩
            exact hxcut ⟨hxA, fun hx => hx.elim hxG hxJ⟩
      · exact Or.inr (Or.inr (Or.inr hxcap))
    · rintro (hxR | hxT | hxL | hxcap)
      · exact Or.inl ⟨Or.inl hxR, fun hx => hRA hxR hx.1⟩
      · exact Or.inl ⟨Or.inr (Or.inl hxT), fun hx => hx.2 (Or.inl (hAG hx.1 hxT))⟩
      · exact Or.inl ⟨Or.inr (Or.inr hxL.1),
          fun hx => hxL.2 ⟨hx.1, fun hxJ => hx.2 (Or.inr hxJ)⟩⟩
      · exact Or.inr hxcap
  have htrace : L' ∩ T = (L ∩ T) \ G := by
    ext x
    have hAG : x ∈ A → x ∈ T → x ∈ G := fun hxA hxT => hAT.subset ⟨hxA, hxT⟩
    have hGAx : x ∈ G → x ∈ A := fun hxG => hGA hxG
    have hJT' : x ∈ J → x ∈ T → False := fun hxJ hxT => disjoint_left.mp hJT hxJ hxT
    have hΔ'T' : x ∈ Δ' → x ∈ T → False :=
      fun hxΔ hxT => disjoint_left.mp hΔ'T hxΔ hxT
    simp only [L', mem_inter_iff, mem_union, mem_sdiff]
    tauto
  have hseams := traceCircles_eq_sdiff_singleton hfin hcover hG htrace
  have hL'out : L' \ Ω = L \ Ω := by
    ext x
    have hAO : x ∈ A → x ∈ Ω := fun hxA => (hAΩ hxA).2
    have hΔO : x ∈ Δ' → x ∈ Ω := fun hxΔ => hΔ'Ω hxΔ
    simp only [L', mem_union, mem_sdiff]
    tauto
  have hprotected : C' ∩ F = ((R ∪ (T ∪ L))) ∩ F := by
    ext x
    constructor
    · intro hx
      have hxΩ : x ∉ Ω := disjoint_left.mp hF hx.2
      have hxC : x ∈ ((R ∪ (T ∪ L))) \ Ω := hout ▸ show x ∈ C' \ Ω from ⟨hx.1, hxΩ⟩
      exact ⟨hxC.1, hx.2⟩
    · intro hx
      have hxΩ : x ∉ Ω := disjoint_left.mp hF hx.2
      have hxC : x ∈ C' \ Ω := hout.symm ▸ show x ∈ ((R ∪ (T ∪ L))) \ Ω from ⟨hx.1, hxΩ⟩
      exact ⟨hxC.1, hx.2⟩
  refine ⟨C', L', ⟨hC'cl, hsep'⟩, ⟨hout, hprotected⟩, hC', ?_, hseams,
    nullTraceCount_lt_of_erase hfin hG ⟨Δ, r, hr, hΔT, rfl⟩ hseams, hL'out,
    A, Δ', J, hA, hAΩ, hAΔ, ⟨r', hr'⟩, hΔ'Ω, hΔ'C, rfl, htrace, r', hr', hJ.symm⟩
  rw [hC']
  exact subset_union_left.trans subset_union_right

theorem exists_disk_split_reducing_seams (h303 : Moise303)
    (I H K R T L Δ D₁ D₂ Ω F : Set E3) (r r₁ r₂ : (Fin 3 → ℝ) → E3)
    (hI : IsOpen I) (hIc : IsConnected I) (hHI : H ⊆ I) (hKI : K ⊆ I)
    (hHK : Disjoint H K) (hH : IsClosed (((↑) : I → E3) ⁻¹' H))
    (hK : IsClosed (((↑) : I → E3) ⁻¹' K)) (hCI : (R ∪ (T ∪ L)) ⊆ I)
    (hC : IsSeparatorIn I ((R ∪ (T ∪ L))) H K)
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ) (hΔT : Δ ⊆ T)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁)
    (hr₂ : IsPLHomeomorphOn r₂ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₂)
    (hpair : D₁ ∩ D₂ = Δ) (hD₁T : D₁ ∩ T = Δ)
    (hsub : D₁ ∪ D₂ ⊆ (R ∪ (T ∪ L))) (hnear : D₁ ∪ D₂ ∈ 𝓝ˢ[(R ∪ (T ∪ L))] Δ)
    (hΔ₁ : Δ ⊆ D₁ \ r₁ '' stdSimplexBoundary 2)
    (hΔ₂ : Δ ⊆ D₂ \ r₂ '' stdSimplexBoundary 2)
    (hΩ : IsOpen Ω) (hΔΩ : Δ ⊆ Ω) (hΩI : Ω ⊆ I) (hΩHK : Disjoint Ω (H ∪ K))
    (hR : Disjoint R Ω) (hF : Disjoint F Ω) (hfin : (traceCircles L T).Finite)
    (hcover : L ∩ T = ⋃ G ∈ traceCircles L T, G)
    (hG : r '' stdSimplexBoundary 2 ∈ traceCircles L T) :
    ∃ C' L' : Set E3, IsSeparatorIn I C' H K ∧
      IsProtectedReplacement (R ∪ (T ∪ L)) C' F Ω ∧ C' = R ∪ (T ∪ L') ∧ T ⊆ C' ∧
      traceCircles L' T = traceCircles L T \ {r '' stdSimplexBoundary 2} ∧
      nullTraceCount L' T < nullTraceCount L T ∧ L' \ Ω = L \ Ω := by
  obtain ⟨C', L', hsep, hprot, heq, hT, hseams, hcount, hout, -⟩ :=
    exists_disk_split_reducing_seams_with_annulus h303 I H K R T L Δ D₁ D₂ Ω F r r₁ r₂
      hI hIc hHI hKI hHK hH hK hCI hC hr hΔT hr₁ hr₂ hpair hD₁T hsub hnear hΔ₁ hΔ₂
      hΩ hΔΩ hΩI hΩHK hR hF hfin hcover hG
  exact ⟨C', L', hsep, hprot, heq, hT, hseams, hcount, hout⟩
end DifferentialGeometry.Topology.PiecewiseLinear

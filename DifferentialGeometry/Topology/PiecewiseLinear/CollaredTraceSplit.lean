/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FiniteCollaredTrace
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSeamDiskPair
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCapReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCapHomeomorph

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem HasFiniteCollaredTrace.exists_split_reducing_nullTraceCount_with_cap
    {I H K R T L O F : Set E3} (h : HasFiniteCollaredTrace L T) (hT : IsPLTorus T)
    (h303 : Moise303) (hI : IsOpen I) (hIc : IsConnected I)
    (hHI : H ⊆ I) (hKI : K ⊆ I) (hHK : Disjoint H K)
    (hH : IsClosed (((↑) : I → E3) ⁻¹' H)) (hK : IsClosed (((↑) : I → E3) ⁻¹' K))
    (hCI : R ∪ (T ∪ L) ⊆ I) (hC : IsSeparatorIn I (R ∪ (T ∪ L)) H K)
    (hO : IsOpen O) (hTO : T ⊆ O) (hOI : O ⊆ I) (hOHK : Disjoint O (H ∪ K))
    (hRO : Disjoint R O) (hFO : Disjoint F O)
    (hnull : ∃ G ∈ traceCircles L T, boundsDiskIn G T) :
    ∃ L' : Set E3, HasFiniteCollaredTrace L' T ∧
      IsSeparatorIn I (R ∪ (T ∪ L')) H K ∧ R ∪ (T ∪ L') ⊆ I ∧
      IsProtectedReplacement (R ∪ (T ∪ L)) (R ∪ (T ∪ L')) F O ∧
      L' \ O = L \ O ∧ traceCircles L' T ⊆ traceCircles L T ∧
      nullTraceCount L' T < nullTraceCount L T ∧
      ∃ (Δ : Set E3) (r : (Fin 3 → ℝ) → E3) (f : E3 → E3),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ T ∧
        L ∩ Δ = r '' stdSimplexBoundary 2 ∧ r '' stdSimplexBoundary 2 ∈ traceCircles L T ∧
        IsPLHomeomorphOn f (L ∪ Δ) L' ∧
        EqOn f id ((L \ O) ∪ ((L ∩ T) \ r '' stdSimplexBoundary 2)) ∧
        L' ∩ T = (L ∩ T) \ r '' stdSimplexBoundary 2 := by
  obtain ⟨G, Δ, Ω, r, hG, hr, hΔT, hrG, hΩ, hΔΩ, hΩO, hΔL, hisolated, hothers⟩ :=
    h.exists_innermost_disk_neighborhood hT hO hTO hnull
  have hGr : r '' stdSimplexBoundary 2 ∈ traceCircles L T := hrG.symm ▸ hG
  obtain ⟨D₁, D₂, r₁, r₂, hr₁, hr₂, hΔ₁, hΔ₂, hpair, hD₁T, hD₂T, -, hsub, hnear⟩ :=
    exists_disk_pair_of_circle_collar hT h.isPolyhedron.isClosed hr hΔT
      (hΔL.trans hrG.symm) (hrG.symm ▸ h.circleCollar G hG) hΩ hΔΩ
      (hisolated.trans hrG.symm.subset)
  have hRΩ : Disjoint R Ω := hRO.mono_right hΩO
  have hnear' : D₁ ∪ D₂ ∈ 𝓝ˢ[R ∪ (T ∪ L)] Δ := by
    obtain ⟨U, hU, hΔU, hUD⟩ := mem_nhdsSetWithin.mp hnear
    refine mem_nhdsSetWithin.mpr ⟨U ∩ Ω, hU.inter hΩ,
      fun x hx => ⟨hΔU hx, hΔΩ hx⟩, ?_⟩
    rintro x ⟨hxU, hxR | hxTL⟩
    · exact (disjoint_left.mp hRΩ hxR hxU.2).elim
    · exact hUD ⟨hxU.1, hxTL⟩
  obtain ⟨C', L', hsep, hprot, heq, -, hseams, hcount, hout,
      A, B, J, hAnn, hA, hAΔ, hB, hBΩ, hBC, hL'eq, htrace', s, hs, hsJ⟩ :=
    exists_disk_split_reducing_seams_with_annulus h303 I H K R T L Δ D₁ D₂ Ω F r r₁ r₂
      hI hIc hHI hKI hHK hH hK hCI hC hr hΔT hr₁ hr₂ hpair hD₁T
      (hsub.trans (inter_subset_left.trans subset_union_right)) hnear' hΔ₁ hΔ₂
      hΩ hΔΩ (hΩO.trans hOI) (hOHK.mono_left hΩO) hRΩ (hFO.mono_right hΩO)
      h.finiteTrace h.traceCover hGr
  have hL'poly := isPolyhedron_cap_replacement h.isPolyhedron hB.isPolyhedron hr rfl
    hAnn hA hAΔ ⟨r₁, hr₁⟩ (hΔ₁.trans sdiff_subset) hΔT hD₂T hnear'
    hΩ hΔΩ (hΩO.trans hOI) hRΩ hCI
    ((traceCircles_subset hGr).trans inter_subset_left)
    (hisolated.trans hrG.symm.subset) hBΩ hBC hsep.1 heq hL'eq htrace'
  have houtside : L' \ (A ∪ B) = L \ (A ∪ B) := by
    rw [hL'eq]
    ext x
    simp only [mem_sdiff, mem_union]
    tauto
  have hstate : HasFiniteCollaredTrace L' T := by
    refine ⟨hL'poly, ?_, ?_, ?_⟩
    · rw [hseams]
      exact h.finiteTrace.sdiff
    · refine Subset.antisymm ?_ (iUnion₂_subset fun J hJ => traceCircles_subset hJ)
      intro x hx
      obtain ⟨hxLT, hxG⟩ := htrace'.subset hx
      obtain ⟨J, hJ, hxJ⟩ := mem_iUnion₂.mp (h.traceCover.subset hxLT)
      refine mem_iUnion₂.mpr ⟨J, hseams.symm.subset ⟨hJ, ?_⟩, hxJ⟩
      exact fun he => hxG (he ▸ hxJ)
    · intro J hJ
      have hJold := hseams.subset hJ
      have hJG : J ≠ G := fun he => hJold.2 (he.trans hrG.symm)
      have hJC : Disjoint J (A ∪ B) := (hothers J hJold.1 hJG).symm.mono_right
        (union_subset (hA.trans inter_subset_right) hBΩ)
      exact (h.circleCollar J hJold.1).of_sdiff_eq
        (hAnn.isPolyhedron.isClosed.union hB.isPolyhedron.isClosed) hJC houtside
  have hL'out : L' \ O = L \ O := by
    ext x
    constructor
    · rintro ⟨hx, hxO⟩
      exact ⟨(hout.subset ⟨hx, fun hxΩ => hxO (hΩO hxΩ)⟩).1, hxO⟩
    · rintro ⟨hx, hxO⟩
      exact ⟨(hout.symm.subset ⟨hx, fun hxΩ => hxO (hΩO hxΩ)⟩).1, hxO⟩
  have hglobalOut : (R ∪ (T ∪ L')) \ O = (R ∪ (T ∪ L)) \ O := by
    simp only [union_sdiff_distrib, hL'out]
  have hC'I : R ∪ (T ∪ L') ⊆ I := by
    intro x hx
    by_cases hxO : x ∈ O
    · exact hOI hxO
    · exact hCI (hglobalOut.subset ⟨hx, hxO⟩).1
  have hAL : A ⊆ L := by
    intro x hxA
    rcases (hsub (Or.inl (hA hxA).1)).1 with hxT | hxL
    · exact (traceCircles_subset hGr
        (hAΔ.subset ⟨hxA, hD₁T.subset ⟨(hA hxA).1, hxT⟩⟩)).1
    · exact hxL
  have hJA : J ⊆ A := by
    obtain ⟨Q, ρ, -, hρ, -, hJ⟩ := hAnn
    rw [hJ]
    have h1 : Q ×ˢ {(1 : ℝ)} ⊆ Q ×ˢ Icc (0 : ℝ) 1 :=
      fun z hz => ⟨hz.1, hz.2.symm ▸ ⟨zero_le_one, le_rfl⟩⟩
    exact (image_mono h1).trans hρ.image_eq.subset
  have hBL : B ∩ L = J := Subset.antisymm
    (fun x hx => hBC.subset ⟨hx.1, Or.inr (Or.inr hx.2)⟩)
    (fun x hx => ⟨(hBC.symm.subset hx).1, hAL (hJA hx)⟩)
  have hLΔ' : L ∩ Δ = r '' stdSimplexBoundary 2 := by rw [inter_comm, hΔL, hrG]
  obtain ⟨f, hf, hfix⟩ := exists_isPLHomeomorphOn_cap_replacement h.isPolyhedron
    hL'poly hr rfl hAnn hAL hAΔ hLΔ' hs hsJ hBL hL'eq
  have hfix' : EqOn f id ((L \ O) ∪ ((L ∩ T) \ r '' stdSimplexBoundary 2)) := by
    apply hfix.mono
    intro x hx
    refine ⟨hx.elim (fun hx => hx.1) (fun hx => hx.1.1), ?_⟩
    rintro ⟨hxA, -⟩
    rcases hx with hx | hx
    · exact hx.2 (hΩO (hA hxA).2)
    · exact hx.2 (hAΔ.subset ⟨hxA, hD₁T.subset ⟨(hA hxA).1, hx.1.2⟩⟩)
  refine ⟨L', hstate, heq ▸ hsep, hC'I, ⟨hglobalOut, ?_⟩, hL'out,
    hseams.subset.trans sdiff_subset, hcount, Δ, r, f, hr, hΔT, hLΔ', hGr, hf, hfix', htrace'⟩
  rw [← heq]
  exact hprot.2

theorem HasFiniteCollaredTrace.exists_split_reducing_nullTraceCount
    {I H K R T L O F : Set E3} (h : HasFiniteCollaredTrace L T) (hT : IsPLTorus T)
    (h303 : Moise303) (hI : IsOpen I) (hIc : IsConnected I)
    (hHI : H ⊆ I) (hKI : K ⊆ I) (hHK : Disjoint H K)
    (hH : IsClosed (((↑) : I → E3) ⁻¹' H)) (hK : IsClosed (((↑) : I → E3) ⁻¹' K))
    (hCI : R ∪ (T ∪ L) ⊆ I) (hC : IsSeparatorIn I (R ∪ (T ∪ L)) H K)
    (hO : IsOpen O) (hTO : T ⊆ O) (hOI : O ⊆ I) (hOHK : Disjoint O (H ∪ K))
    (hRO : Disjoint R O) (hFO : Disjoint F O)
    (hnull : ∃ G ∈ traceCircles L T, boundsDiskIn G T) :
    ∃ L' : Set E3, HasFiniteCollaredTrace L' T ∧
      IsSeparatorIn I (R ∪ (T ∪ L')) H K ∧ R ∪ (T ∪ L') ⊆ I ∧
      IsProtectedReplacement (R ∪ (T ∪ L)) (R ∪ (T ∪ L')) F O ∧
      L' \ O = L \ O ∧ traceCircles L' T ⊆ traceCircles L T ∧
      nullTraceCount L' T < nullTraceCount L T := by
  obtain ⟨L', hstate, hsep, hsub, hprot, hout, htrace, hcount, -⟩ :=
    h.exists_split_reducing_nullTraceCount_with_cap hT h303 hI hIc hHI hKI hHK hH hK hCI hC
      hO hTO hOI hOHK hRO hFO hnull
  exact ⟨L', hstate, hsep, hsub, hprot, hout, htrace, hcount⟩

end DifferentialGeometry.Topology.PiecewiseLinear

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCompressionCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionOutsideTube

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3}

private theorem compact_compression_of_shell_fill
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hcar : Section34CompactCarrierControl K h ε H)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd) (s : Section34CompactSimplexIndex K 3)
    {w : Section34CompactVertexIndex K K'} {Dj Jd : Set E3}
    {q : (Fin 3 → ℝ) → E3}
    (hDw : Dj ⊆ section34CompactVertexBallImage srcBd f₁ w)
    (hDJ : Dj ∩ fblBd s = Jd) (hqJ : Jd = q '' stdSimplexBoundary 2)
    (hDP : Dj ∩ fbl s = q '' stdSimplexBoundary 2)
    (hwinc : Section34Incident w.1 s.1)
    (hDjT : Dj ⊆ frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
    {yJ : E3} (hyJ : yJ ∈ Jd)
    {Wc Xc Ein Eout Bin Bout Ain Aout Lin Lout Tin Tout O O₀ : Set E3}
    (hDO : Dj ⊆ O)
    (hfO₀ : fbl s ⊆ O₀)
    (hSgO₀ : frontier (⋃ u, section34CompactVertexBallImage src f₁ u) ∩ O₀ =
      frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) ∩ O₀)
    (hOO₀ : O ⊆ O₀)
    (hOMH : ∀ x ∈ O, ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      x ∈ interior (H t.1))
    (hOMV : ∀ x ∈ O, ∀ u, u ≠ w → x ∉ section34CompactVertexBallImage src f₁ u)
    (hOMf : ∀ x ∈ O, ∀ s', s' ≠ s → x ∉ fbl s')
    (hOsplit : ∀ x ∈ O, ∀ e, x ∉ section34CompactSplitDiskImage srcBd f₁ e)
    (hLΘ : ∀ x ∈ Lin ∪ Lout,
      x ∉ frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
    (hAΘ : ∀ x ∈ Ain ∪ Aout,
      x ∈ frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) →
        x ∈ q '' stdSimplexBoundary 2)
    (hcarry : CarriesFirstHomologyOnto
      ((frontier (fbl s) ∩ frontier
        (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s)) \
          q '' stdSimplexBoundary 2)
      (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
    (hcrossPΘ : ∀ x ∈ frontier (fbl s) ∩ frontier
        (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s),
      HasPLCrossingAt (frontier (fbl s))
        (frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s)) x)
    (hcTreg : ∀ x ∈ frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s),
      x ∈ closure (interior (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s)))
    (hO₀def : O₀ = (⋃ u ∈ {u : Section34CompactVertexIndex K K' |
      ¬ Section34Incident u.1 s.1}, section34CompactVertexBallImage src f₁ u)ᶜ)
    (hShell :
      IsPLBall 3 Wc ∧ IsPLBall 3 Xc ∧ Xc ⊆ interior Wc ∧ Disjoint (interior (fbl s)) Xc ∧
      Wc = (fbl s) ∪ Xc ∪ Tin ∪ Tout ∧ frontier Wc = Lout ∪ Bout ∧ frontier Xc = Lin ∪ Bin ∧
      Ein ∪ Eout = frontier (fbl s) ∧ Ein ∩ Eout = q '' stdSimplexBoundary 2 ∧
      Ein = Bin ∪ Ain ∧ Eout = Bout ∪ Aout ∧ Bin ∩ Ain ⊆ Lin ∧ Bout ∩ Aout ⊆ Lout ∧
      Disjoint Bin (q '' stdSimplexBoundary 2) ∧ Disjoint Bout (q '' stdSimplexBoundary 2) ∧
      IsClosed Ein ∧ IsClosed Eout ∧ IsClosed Ain ∧ IsClosed Aout ∧ IsClosed Lin ∧
      IsClosed Lout ∧ IsClosed Bin ∧ IsClosed Bout ∧ Ain ∪ Aout ∪ Lin ∪ Lout ∪ Tin ∪ Tout ⊆ O ∧
      (Ain ∪ Aout) ∩ (frontier (section34CompactVertexBallImage src f₁ w) ∪ (⋃ e,
        section34CompactSplitDiskImage src f₁ e)) ⊆ q '' stdSimplexBoundary 2 ∧
      Disjoint (Lin ∪ Lout) (frontier (section34CompactVertexBallImage src f₁ w) ∪ (⋃ e,
        section34CompactSplitDiskImage src f₁ e)) ∧ Lin ∩ (fbl s) ⊆ Bin ∧ Lout ∩ (fbl s) ⊆ Bout ∧
      IsPLBall 3 (Xc ∪ Tin) ∧ frontier (Xc ∪ Tin) = Dj ∪ Ein ∧
      ∃ (R Lr : Set E3) (g : E3 → E3), IsOpen R ∧ R ⊆ O ∧ Lr ⊆ O ∧
        Tout ⊆ R ∪ (Dj ∪ Aout) ∧ closure R ⊆ R ∪ (Dj ∪ Aout) ∪ Lr ∧ ContinuousOn g (R ∪ Lr) ∧
        (∀ y ∈ Lr, g y = y) ∧ MapsTo g R R ∧ (∀ y ∈ R, g y ∉ Tout) ∧ Disjoint R (fbl s) ∧
        Disjoint R (frontier (section34CompactVertexBallImage src f₁ w) ∪ (⋃ e,
          section34CompactSplitDiskImage src f₁ e)) ∧ (R ⊆ (section34CompactVertexBallImage src f₁
          w) ∨ Disjoint R (section34CompactVertexBallImage src f₁ w)) ∧ Disjoint R (Xc ∪ Tin) ∧
        Disjoint (closure R) (interior (Xc ∪ Tin)) ∧
      ∃ (R' Lr' : Set E3) (g' : E3 → E3), IsOpen R' ∧ R' ⊆ O ∧ Lr' ⊆ O ∧
        Tin ⊆ R' ∪ (Dj ∪ Ain) ∧ closure R' ⊆ R' ∪ (Dj ∪ Ain) ∪ Lr' ∧ ContinuousOn g' (R' ∪ Lr') ∧
        (∀ y ∈ Lr', g' y = y) ∧ MapsTo g' R' R' ∧ (∀ y ∈ R', g' y ∉ Tin) ∧ Disjoint R' (fbl s) ∧
        Disjoint R' (frontier (section34CompactVertexBallImage src f₁ w) ∪ (⋃ e,
          section34CompactSplitDiskImage src f₁ e)) ∧ (R' ⊆ (section34CompactVertexBallImage src
          f₁ w) ∨ Disjoint R' (section34CompactVertexBallImage src f₁ w)) ∧ R' ⊆ interior (Xc ∪
          Tin) ∧
        Disjoint Tout (interior (Xc ∪ Tin)) ∧ IsPLBall 3 Tout ∧ frontier Tout = Dj ∪ Aout ∪ Lout ∧
        Tout ∩ (fbl s) = Aout ∧ Lin ⊆ Tin)
    (hclean : Disjoint (interior (Xc ∪ Tin))
      (frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s)) ∧
      ∀ u : Section34CompactVertexIndex K K', ¬ Section34Incident u.1 s.1 →
        Disjoint (Xc ∪ Tin) (section34CompactVertexBallImage src f₁ u)) :
    ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set E3,
      Section34CompactFaceBallInvariants K K' h H (section34CompactVertexBallImage src f₁)
        (section34CompactSplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd' s + 1 ≤
        section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd s ∧
      section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd' s ≤
        section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd s := by
  classical
  obtain ⟨hfcell, hfrim, hfV, hf4, -, -, -, -, -, hsTs, -⟩ := id hinv
  obtain ⟨-, hf₁, -, -, hmark, -, -, hrimT, hnest, hVcar, -⟩ := id hgraph
  have hVcell := hcut.isPLCellOn_vertexBallImage hf₁
  have hEcell := hcut.isPLCellOn_splitDiskImage hf₁
  set T := section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s
  set Sg := frontier (⋃ u, section34CompactVertexBallImage src f₁ u)
  set Θ := frontier T
  obtain ⟨S₁, S₂, -, -, hTsolid, -⟩ := hnest s
  have hTcomp := hTsolid.isPolyhedron.isCompact
  have hTcl := hTcomp.isClosed
  have hΘT : Θ ⊆ T := hTcl.frontier_subset
  have hPb := (hfcell s).isPLBall_three
  have hPfr := (hfcell s).boundary_eq_frontier
  have hPcl := hPb.isPolyhedron.isClosed
  have hfbs := (hfcell s).boundary_subset
  have hDwV := hDw.trans (hVcell w).boundary_subset
  have hJdb : Jd ⊆ fblBd s := hDJ.symm.subset.trans inter_subset_right
  have hJdD : Jd ⊆ Dj := hDJ.symm.subset.trans inter_subset_left
  have hJD : q '' stdSimplexBoundary 2 ⊆ Dj := hqJ.symm.subset.trans hJdD
  have hJTr : q '' stdSimplexBoundary 2 ⊆ frontier (fbl s) ∩ Θ :=
    fun x hx => ⟨hPfr.subset (hJdb (hqJ.symm.subset hx)), hDjT (hJD hx)⟩
  have hwne : ∀ u : Section34CompactVertexIndex K K', ¬ Section34Incident u.1 s.1 → u ≠ w :=
    fun u hu he => hu (he ▸ hwinc)
  have hVT : ∀ u : Section34CompactVertexIndex K K', Section34Incident u.1 s.1 →
      section34CompactVertexBallImage src f₁ u ⊆ T := fun u hu x hx =>
    mem_iUnion₂.mpr ⟨⟨(s, u), hu⟩, rfl, hx⟩
  have hTinc : ∀ x ∈ T, ∃ u : Section34CompactVertexIndex K K', Section34Incident u.1 s.1 ∧
      x ∈ section34CompactVertexBallImage src f₁ u := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hx
    exact ⟨a.1.2, ha ▸ a.2, hxa⟩
  have hwt : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      Section34Incident w.1 t.1 :=
    fun t ht => hwinc.trans (convexHull_min ht (convex_convexHull ℝ _))
  have hVwt : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      section34CompactVertexBallImage src f₁ w ⊆ interior (H t.1) :=
    fun t ht x hx => hVcar w t.1 t.2.1 (hwt t ht) (Or.inr hx)
  have hDjV : ∀ u, u ≠ w → Disjoint Dj (section34CompactVertexBallImage src f₁ u) :=
    fun u hu => disjoint_left.mpr fun x hx hxV => hOMV x (hDO hx) u hu hxV
  have hy₀ : yJ ∈ fblBd s ∩ Sg := by
    refine ⟨hJdb hyJ, ?_⟩
    have hm : yJ ∈ frontier T ∩ O₀ :=
      ⟨hDjT (hJdD hyJ), hfO₀ (hfbs (hJdb hyJ))⟩
    rw [← hSgO₀] at hm
    exact hm.1
  have hcy₀ : yJ ∈ q '' stdSimplexBoundary 2 := hqJ.subset hyJ
  obtain ⟨hW, hX, hXW, hPX, hWeq,
    hWf, hXf, hEu, hEi, hEinB, hEoutB, hBAin, hBAout, hBinJ, hBoutJ, hEinc, hEoutc, hAinc,
    hAoutc, hLinc, hLoutc, hBinc, hBoutc, hsubO, hAVF, hLVF, hLinP, hLoutP, hYs, hYsf, R, Lr, g,
    hRo, hRO,
    hLrO, hToutR, hclR, hgc, hgLr, hgR, hgT, hRP, hRVF, hRV, hRY, hclRY, R', Lr', g', hR'o,
    hR'O, hLr'O, hTinR', hclR', hg'c, hg'Lr, hg'R, hg'T, hR'P, hR'VF, hR'V, hR'Y, hToutY,
    hToutb, hToutf,
    hToutP, hLinT⟩ := hShell
  have hAinO : Ain ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hx)))))
  have hAoutO : Aout ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))
  have hLinO : Lin ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inl (Or.inr hx))))
  have hLoutO : Lout ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inr hx)))
  have hTinO : Tin ⊆ O := fun x hx => hsubO (Or.inl (Or.inr hx))
  have hToutO : Tout ⊆ O := fun x hx => hsubO (Or.inr hx)
  have hPfrE : frontier (fbl s) = Bin ∪ Ain ∪ (Bout ∪ Aout) := by
    rw [← hEu, hEinB, hEoutB]
  have hVobs : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      section34CompactVertexBallImage src f₁ w ⊆
        section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t :=
    fun t ht x hx => Or.inl (mem_iUnion₂.mpr ⟨⟨(t, w), hwt t ht⟩, rfl, hx⟩)
  have hfobs : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      fbl s ⊆ section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t :=
    fun t ht x hx => Or.inr (mem_iUnion₂.mpr ⟨s, ht, hx⟩)
  have hYfr : frontier (Xc ∪ Tin) ⊆ Dj ∪ fblBd s := by
    rw [hYsf]
    exact union_subset_union_right _ (fun x hx => hPfr.symm.subset (hEu.subset (Or.inl hx)))
  have hpocketH : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      Xc ∪ Tin ⊆ interior (H t.1) := by
    intro t ht
    have hfrY : frontier (Xc ∪ Tin) ⊆ interior (H t.1) :=
      hYfr.trans (union_subset (hDwV.trans (hVwt t ht)) (hfbs.trans (hsTs s t ht)))
    have hsub := (hcar.2.2 t.1 t.2.1).isPLBall_three.subset_of_isCompact_frontier_subset
      hYs.isPolyhedron.isCompact (hfrY.trans interior_subset)
    intro x hx
    by_cases hxi : x ∈ interior (Xc ∪ Tin)
    · exact interior_mono hsub hxi
    · exact hfrY ⟨subset_closure hx, hxi⟩
  have hPkfr : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      frontier (Xc ∪ Tin) ⊆
        section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t :=
    fun t ht => hYfr.trans (union_subset (hDwV.trans (hVobs t ht)) (hfbs.trans (hfobs t ht)))
  have hTinP : Disjoint Tin (interior (fbl s)) := by
    refine Set.disjoint_left.mpr fun x hxT hxi => ?_
    rcases hTinR' hxT with hxR | hxD | hxA
    · exact Set.disjoint_left.mp hR'P hxR (interior_subset hxi)
    · exact (hJTr (hDP.subset ⟨hxD, interior_subset hxi⟩)).1.2 hxi
    · exact (hEu.subset (Or.inl (hEinB.symm.subset (Or.inr hxA)))).2 hxi
  have hYP : Disjoint (interior (fbl s)) (Xc ∪ Tin) := by
    refine Set.disjoint_left.mpr fun x hxi hx => ?_
    rcases hx with hxX | hxT
    · exact Set.disjoint_left.mp hPX hxi hxX
    · exact Set.disjoint_left.mp hTinP hxT hxi
  have hPW : fbl s ⊆ Wc := fun x hx => by
    rw [hWeq]
    exact Or.inl (Or.inl (Or.inl hx))
  have hRobsG : ∀ (t : Section34CompactSimplexIndex K 4), Section34Incident s.1 t.1 →
      ∀ A : Set E3, A ⊆ O → Disjoint A (fbl s) →
        (A ⊆ section34CompactVertexBallImage src f₁ w ∨
          Disjoint A (section34CompactVertexBallImage src f₁ w)) →
        A ⊆ section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t ∨
          Disjoint A (section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t)
      := by
    intro t ht A hAO hAP hAV
    rcases hAV with hAV | hAV
    · exact Or.inl (hAV.trans (hVobs t ht))
    · right
      refine disjoint_left.mpr fun x hx hxo => ?_
      rcases hxo with hxo | hxo
      · obtain ⟨a, -, hxa⟩ := mem_iUnion₂.mp hxo
        by_cases haw : a.1.2 = w
        · exact disjoint_left.mp hAV hx (haw ▸ hxa)
        · exact hOMV x (hAO hx) a.1.2 haw hxa
      · obtain ⟨s', -, hxs'⟩ := mem_iUnion₂.mp hxo
        by_cases hs' : s' = s
        · exact disjoint_left.mp hAP hx (hs' ▸ hxs')
        · exact hOMf x (hAO hx) s' hs' hxs'
  have hBhG : ∀ (t : Section34CompactSimplexIndex K 4), Section34Incident s.1 t.1 →
      ∀ A : Set E3, A ⊆ frontier (fbl s) → Dj ∪ A ⊆
        section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t :=
    fun t ht A hA => union_subset (hDwV.trans (hVobs t ht))
      (hA.trans (hPcl.frontier_subset.trans (hfobs t ht)))
  have hAinP : Ain ⊆ frontier (fbl s) :=
    fun x hx => hEu.subset (Or.inl (hEinB.symm.subset (Or.inr hx)))
  have hAoutP : Aout ⊆ frontier (fbl s) :=
    fun x hx => hEu.subset (Or.inr (hEoutB.symm.subset (Or.inr hx)))
  have hMkO : ∀ (t : Section34CompactSimplexIndex K 4), Section34Incident s.1 t.1 →
      ∀ u : Section34CompactVertexIndex K K', ¬ Section34Incident u.1 t.1 →
        ∀ y ∈ h '' (u.1 : Set E3), y ∉ O := by
    intro t ht u hu y hy hyO
    have huw : u ≠ w := fun he => hu (he ▸ hwt t ht)
    exact hOMV y hyO u huw (interior_subset (hmark u hy))
  have hObdd : ∀ (t : Section34CompactSimplexIndex K 4), Section34Incident s.1 t.1 →
      Bornology.IsBounded O := fun t ht =>
    (hcar.2.2 t.1 t.2.1).isCompact.isBounded.subset
      (fun x hx => interior_subset (hOMH x hx t ht))
  have hfillΘ : Disjoint Θ (interior Xc) :=
    hclean.1.symm.mono_right (interior_mono subset_union_left)
  have hfillV : ∀ u : Section34CompactVertexIndex K K', ¬ Section34Incident u.1 s.1 →
      Disjoint Xc (section34CompactVertexBallImage src f₁ u) :=
    fun u hu => (hclean.2 u hu).mono_left subset_union_left
  have hLinΘ : Disjoint Lin Θ := Set.disjoint_left.mpr fun x hx => hLΘ x (Or.inl hx)
  have hBinΘ : Disjoint Bin Θ := by
    refine disjoint_torus_of_disjoint_interior hPb hX hPX hXf
      (by rw [← hEu, hEinB, union_assoc]) hLinc (hAinc.union hEoutc) ?_ hLinΘ hfillΘ rfl
      hTcl hcrossPΘ hcTreg
    rintro x ⟨hxB, hxA | hxE⟩
    · exact hBAin ⟨hxB, hxA⟩
    · have hxJ : x ∈ q '' stdSimplexBoundary 2 :=
        hEi.subset ⟨hEinB.symm.subset (Or.inl hxB), hxE⟩
      exact absurd hxJ (Set.disjoint_left.mp hBinJ hxB)
  have hWΘ : frontier Wc ∩ Θ = (frontier (fbl s) ∩ Θ) \ q '' stdSimplexBoundary 2 := by
    rw [hWf]
    ext x
    constructor
    · rintro ⟨hxL | hxB, hxΘ⟩
      · exact absurd hxΘ (hLΘ x (Or.inr hxL))
      · exact ⟨⟨hEu.subset (Or.inr (hEoutB.symm.subset (Or.inl hxB))), hxΘ⟩,
          fun hxJ => Set.disjoint_left.mp hBoutJ hxB hxJ⟩
    · rintro ⟨⟨hxP, hxΘ⟩, hxJ⟩
      rw [hPfrE] at hxP
      rcases hxP with (hxB | hxA) | (hxB | hxA)
      · exact absurd hxΘ (Set.disjoint_left.mp hBinΘ hxB)
      · exact absurd (hAΘ x (Or.inl hxA) hxΘ) hxJ
      · exact ⟨Or.inr hxB, hxΘ⟩
      · exact absurd (hAΘ x (Or.inr hxA) hxΘ) hxJ
  have hXΘ : Disjoint Xc Θ := by
    refine Set.disjoint_left.mpr fun x hx hxΘ => ?_
    by_cases hxi : x ∈ interior Xc
    · exact Set.disjoint_left.mp hfillΘ hxΘ hxi
    · have hxf : x ∈ frontier Xc := ⟨subset_closure hx, hxi⟩
      rw [hXf] at hxf
      rcases hxf with hxL | hxB
      · exact hLΘ x (Or.inl hxL) hxΘ
      · exact Set.disjoint_left.mp hBinΘ hxB hxΘ
  have hXN : ∀ s', s' ≠ s → Xc ∩ fbl s' ⊆
      interior (⋃ u, section34CompactVertexBallImage src f₁ u) := by
    intro s' hs'
    have hTN : interior T ⊆ interior (⋃ u, section34CompactVertexBallImage src f₁ u) :=
      interior_mono fun x hx => by
        obtain ⟨u, -, hxu⟩ := hTinc x hx
        exact mem_iUnion.mpr ⟨u, hxu⟩
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hTcl
      hX.isConnected.isPreconnected hXΘ with hXT | hXT
    · exact fun x hx => hTN (hXT hx.1)
    · have hXNd : ∀ x ∈ Xc, ∀ u, x ∉ section34CompactVertexBallImage src f₁ u := by
        intro x hx u hxu
        by_cases hu : Section34Incident u.1 s.1
        · exact hXT hx (hVT u hu hxu)
        · exact disjoint_left.mp (hfillV u hu) hx hxu
      have hdisj : Disjoint (fbl s') (frontier Xc) := by
        rw [hXf]
        refine disjoint_left.mpr fun x hx hxF => ?_
        rcases hxF with hxL | hxB
        · exact hOMf x (hLinO hxL) s' hs' hx
        · have hxP : x ∈ fbl s := hPcl.frontier_subset
            (hEu.subset (Or.inl (hEinB.symm.subset (Or.inl hxB))))
          obtain ⟨u, hxu⟩ := mem_iUnion.mp (interior_subset (hf4 s s' (Ne.symm hs') ⟨hxP, hx⟩))
          exact hXNd x (hX.isPolyhedron.isClosed.frontier_subset
            (hXf.symm.subset (Or.inr hxB))) u hxu
      rintro x ⟨hxX, hxs'⟩
      exfalso
      have hsub : fbl s' ⊆ Xc :=
        IsPreconnected.subset_of_disjoint_frontier (hfcell s').isConnected.isPreconnected
          ⟨x, hxs', hxX⟩ hdisj
      obtain ⟨z, hz⟩ := (hgraph.isConnected_image_simplexRim s').nonempty
      obtain ⟨a, -, hza⟩ := mem_iUnion₂.mp (interior_subset (hrimT s' hz))
      exact hXNd z (hsub (interior_subset (hfrim s' hz))) a.1.2 hza
  have hZV : ∀ u : Section34CompactVertexIndex K K', ¬ Section34Incident u.1 s.1 →
      Disjoint (Xc ∪ Tin ∪ Tout) (section34CompactVertexBallImage src f₁ u) := by
    intro u hu
    refine disjoint_left.mpr fun x hx hxu => ?_
    rcases hx with (hx | hx) | hx
    · exact disjoint_left.mp (hfillV u hu) hx hxu
    · exact hOMV x (hTinO hx) u (hwne u hu) hxu
    · exact hOMV x (hToutO hx) u (hwne u hu) hxu
  have hZs : ∀ s', s' ≠ s → (Xc ∪ Tin ∪ Tout) ∩ fbl s' ⊆
      interior (⋃ u, section34CompactVertexBallImage src f₁ u) := by
    rintro s' hs' x ⟨(hx | hx) | hx, hxs'⟩
    · exact hXN s' hs' ⟨hx, hxs'⟩
    · exact False.elim (hOMf x (hTinO hx) s' hs' hxs')
    · exact False.elim (hOMf x (hToutO hx) s' hs' hxs')
  have hZH : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      Xc ∪ Tin ∪ Tout ⊆ interior (H t.1) := by
    intro t ht x hx
    rcases hx with hx | hx
    · exact hpocketH t ht hx
    · exact hOMH x (hToutO hx) t ht
  have hWO₀ : Wc ⊆ O₀ := by
    rw [hWeq]
    rintro x (((hx | hx) | hx) | hx)
    · exact hfO₀ hx
    · rw [hO₀def]
      intro hxA
      obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hxA
      exact disjoint_left.mp (hfillV u hu) hx hxu
    · exact hOO₀ (hTinO hx)
    · exact hOO₀ (hToutO hx)
  have hGZ : Wc ⊆ fbl s ∪ (Xc ∪ Tin ∪ Tout) := by
    rw [hWeq]
    rintro x (((hx | hx) | hx) | hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inl (Or.inl hx))
    · exact Or.inr (Or.inl (Or.inr hx))
    · exact Or.inr (Or.inr hx)
  have hr : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      ∃ (r : E3 → E3) (Y B : Set E3), IsCompact Y ∧ Bornology.IsBounded B ∧
        frontier Y ⊆
          section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t ∧
        ContinuousOn r ((section34CompactTetraObstacle
          (section34CompactVertexBallImage src f₁) fbl t)ᶜ \ Y) ∧
        MapsTo r ((section34CompactTetraObstacle (section34CompactVertexBallImage src f₁)
          fbl t)ᶜ \ Y)
          (section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t ∪
            (Xc ∪ Tin ∪ Tout))ᶜ ∧
        (∀ x ∉ B, r x = x) ∧
        ∀ u : Section34CompactVertexIndex K K', ¬ Section34Incident u.1 t.1 →
          ∀ y ∈ h '' (u.1 : Set E3), r y = y := by
    intro t ht
    obtain ⟨r, hrc, hrm, hrid, hrR⟩ := exists_compactPush hRo hclR (hBhG t ht Aout hAoutP)
      hgc hgLr hgR hgT hToutR (hRobsG t ht R hRO hRP hRV)
    refine ⟨r, Xc ∪ Tin, O, hYs.isPolyhedron.isCompact, hObdd t ht, hPkfr t ht,
      hrc.mono sdiff_subset, ?_, fun x hx => hrid x (fun h => hx (hRO h)),
      fun u hu y hy => hrid y (fun h => hMkO t ht u hu y hy (hRO h))⟩
    intro x hx
    have hm := hrm hx.1
    have hy : r x ∉ Xc ∪ Tin := by
      by_cases hxR : x ∈ R
      · exact disjoint_left.mp hRY (hrR hxR)
      · rw [hrid x hxR]
        exact hx.2
    rintro (ho | hY | hT)
    · exact hm (Or.inl ho)
    · exact hy hY
    · exact hm (Or.inr hT)
  have hOc : IsOpen (Lout ∪ Ein ∪ Aout)ᶜ := ((hLoutc.union hEinc).union hAoutc).isOpen_compl
  have hfrO : frontier Wc ∩ (Lout ∪ Ein ∪ Aout)ᶜ =
      frontier (fbl s) ∩ (Lout ∪ Ein ∪ Aout)ᶜ := by
    rw [hWf, ← hEu, hEoutB]
    ext x
    constructor
    · rintro ⟨hxL | hxB, hxO⟩
      · exact absurd (Or.inl (Or.inl hxL)) hxO
      · exact ⟨Or.inr (Or.inl hxB), hxO⟩
    · rintro ⟨hxE | hxB | hxA, hxO⟩
      · exact absurd (Or.inl (Or.inr hxE)) hxO
      · exact ⟨Or.inr hxB, hxO⟩
      · exact absurd (Or.inr hxA) hxO
  have hk2 : frontier Wc ∩ Θ ⊆ (Lout ∪ Ein ∪ Aout)ᶜ := by
    rw [hWΘ]
    rintro x ⟨⟨hxP, hxΘ⟩, hxJ⟩ ((hxL | hxE) | hxA)
    · exact hLΘ x (Or.inr hxL) hxΘ
    · rw [hEinB] at hxE
      rcases hxE with hxB | hxA
      · exact Set.disjoint_left.mp hBinΘ hxB hxΘ
      · exact hxJ (hAΘ x (Or.inl hxA) hxΘ)
    · exact hxJ (hAΘ x (Or.inr hxA) hxΘ)
  have hk4 : ∀ e : Section34CompactEdgeIndex K K',
      frontier Wc ∩ section34CompactSplitDiskImage srcBd f₁ e ⊆ (Lout ∪ Ein ∪ Aout)ᶜ := by
    rintro e x ⟨hxW, hxE⟩ ((hxL | hxI) | hxA)
    · exact hOsplit x (hLoutO hxL) e hxE
    · rw [hWf] at hxW
      rcases hxW with hxL | hxB
      · exact hOsplit x (hLoutO hxL) e hxE
      · have hxJ := hEi.subset ⟨hxI, hEoutB.symm.subset (Or.inl hxB)⟩
        exact hOsplit x (hDO (hJD hxJ)) e hxE
    · exact hOsplit x (hAoutO hxA) e hxE
  have hk3 : frontier Wc ∩ Θ = frontier (fbl s) ∩ Θ ∩ Bout := by
    rw [hWΘ]
    ext x
    constructor
    · rintro ⟨⟨hxP, hxΘ⟩, hxJ⟩
      refine ⟨⟨hxP, hxΘ⟩, ?_⟩
      rw [hPfrE] at hxP
      rcases hxP with (hxB | hxA) | (hxB | hxA)
      · exact absurd hxΘ (Set.disjoint_left.mp hBinΘ hxB)
      · exact absurd (hAΘ x (Or.inl hxA) hxΘ) hxJ
      · exact hxB
      · exact absurd (hAΘ x (Or.inr hxA) hxΘ) hxJ
    · rintro ⟨hxPΘ, hxB⟩
      exact ⟨hxPΘ, fun hxJ => Set.disjoint_left.mp hBoutJ hxB hxJ⟩
  have h7 : CarriesIntegralFirstHomologyOnto (frontier Wc ∩ Θ) T := by
    change CarriesFirstHomologyOnto (frontier Wc ∩ Θ) T
    rw [hWΘ]
    exact hcarry
  exact exists_compactCompression_of_ball hinv s hfO₀ hSgO₀ hW hWO₀
    ((hfrim s).trans (interior_mono hPW)) hGZ hZV hZs hZH hr hOc
    (by rw [hPfr]; exact hfrO) hk2 hk4 (by rw [hPfr]; exact hk3) hBoutc hy₀
    (fun hx => disjoint_left.mp hBoutJ hx hcy₀) h7

private theorem compact_compression_of_shell_tube
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hcar : Section34CompactCarrierControl K h ε H)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd) (s : Section34CompactSimplexIndex K 3)
    {w : Section34CompactVertexIndex K K'} {Dj Jd : Set E3}
    {q : (Fin 3 → ℝ) → E3}
    (hDw : Dj ⊆ section34CompactVertexBallImage srcBd f₁ w)
    (hDJ : Dj ∩ fblBd s = Jd) (hqJ : Jd = q '' stdSimplexBoundary 2)
    (hDP : Dj ∩ fbl s = q '' stdSimplexBoundary 2)
    (hwinc : Section34Incident w.1 s.1)
    (hDjT : Dj ⊆ frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
    {yJ : E3} (hyJ : yJ ∈ Jd)
    {Wc Xc Ein Eout Bin Bout Ain Aout Lin Lout Tin Tout O O₀ : Set E3}
    (hDO : Dj ⊆ O)
    (hfO₀ : fbl s ⊆ O₀)
    (hSgO₀ : frontier (⋃ u, section34CompactVertexBallImage src f₁ u) ∩ O₀ =
      frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) ∩ O₀)
    (hOO₀ : O ⊆ O₀)
    (hOMH : ∀ x ∈ O, ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      x ∈ interior (H t.1))
    (hOMV : ∀ x ∈ O, ∀ u, u ≠ w → x ∉ section34CompactVertexBallImage src f₁ u)
    (hOMf : ∀ x ∈ O, ∀ s', s' ≠ s → x ∉ fbl s')
    (hOsplit : ∀ x ∈ O, ∀ e, x ∉ section34CompactSplitDiskImage srcBd f₁ e)
    (hLΘ : ∀ x ∈ Lin ∪ Lout,
      x ∉ frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
    (hAΘ : ∀ x ∈ Ain ∪ Aout,
      x ∈ frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) →
        x ∈ q '' stdSimplexBoundary 2)
    (hcarry : CarriesFirstHomologyOnto
      ((frontier (fbl s) ∩ frontier
        (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s)) \
          q '' stdSimplexBoundary 2)
      (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
    (hShell :
      IsPLBall 3 Wc ∧ IsPLBall 3 Xc ∧ Xc ⊆ interior Wc ∧ Disjoint (interior (fbl s)) Xc ∧
      Wc = (fbl s) ∪ Xc ∪ Tin ∪ Tout ∧ frontier Wc = Lout ∪ Bout ∧ frontier Xc = Lin ∪ Bin ∧
      Ein ∪ Eout = frontier (fbl s) ∧ Ein ∩ Eout = q '' stdSimplexBoundary 2 ∧
      Ein = Bin ∪ Ain ∧ Eout = Bout ∪ Aout ∧ Bin ∩ Ain ⊆ Lin ∧ Bout ∩ Aout ⊆ Lout ∧
      Disjoint Bin (q '' stdSimplexBoundary 2) ∧ Disjoint Bout (q '' stdSimplexBoundary 2) ∧
      IsClosed Ein ∧ IsClosed Eout ∧ IsClosed Ain ∧ IsClosed Aout ∧ IsClosed Lin ∧
      IsClosed Lout ∧ IsClosed Bin ∧ IsClosed Bout ∧ Ain ∪ Aout ∪ Lin ∪ Lout ∪ Tin ∪ Tout ⊆ O ∧
      (Ain ∪ Aout) ∩ (frontier (section34CompactVertexBallImage src f₁ w) ∪ (⋃ e,
        section34CompactSplitDiskImage src f₁ e)) ⊆ q '' stdSimplexBoundary 2 ∧
      Disjoint (Lin ∪ Lout) (frontier (section34CompactVertexBallImage src f₁ w) ∪ (⋃ e,
        section34CompactSplitDiskImage src f₁ e)) ∧ Lin ∩ (fbl s) ⊆ Bin ∧ Lout ∩ (fbl s) ⊆ Bout ∧
      IsPLBall 3 (Xc ∪ Tin) ∧ frontier (Xc ∪ Tin) = Dj ∪ Ein ∧
      ∃ (R Lr : Set E3) (g : E3 → E3), IsOpen R ∧ R ⊆ O ∧ Lr ⊆ O ∧
        Tout ⊆ R ∪ (Dj ∪ Aout) ∧ closure R ⊆ R ∪ (Dj ∪ Aout) ∪ Lr ∧ ContinuousOn g (R ∪ Lr) ∧
        (∀ y ∈ Lr, g y = y) ∧ MapsTo g R R ∧ (∀ y ∈ R, g y ∉ Tout) ∧ Disjoint R (fbl s) ∧
        Disjoint R (frontier (section34CompactVertexBallImage src f₁ w) ∪ (⋃ e,
          section34CompactSplitDiskImage src f₁ e)) ∧ (R ⊆ (section34CompactVertexBallImage src f₁
          w) ∨ Disjoint R (section34CompactVertexBallImage src f₁ w)) ∧ Disjoint R (Xc ∪ Tin) ∧
        Disjoint (closure R) (interior (Xc ∪ Tin)) ∧
      ∃ (R' Lr' : Set E3) (g' : E3 → E3), IsOpen R' ∧ R' ⊆ O ∧ Lr' ⊆ O ∧
        Tin ⊆ R' ∪ (Dj ∪ Ain) ∧ closure R' ⊆ R' ∪ (Dj ∪ Ain) ∪ Lr' ∧ ContinuousOn g' (R' ∪ Lr') ∧
        (∀ y ∈ Lr', g' y = y) ∧ MapsTo g' R' R' ∧ (∀ y ∈ R', g' y ∉ Tin) ∧ Disjoint R' (fbl s) ∧
        Disjoint R' (frontier (section34CompactVertexBallImage src f₁ w) ∪ (⋃ e,
          section34CompactSplitDiskImage src f₁ e)) ∧ (R' ⊆ (section34CompactVertexBallImage src
          f₁ w) ∨ Disjoint R' (section34CompactVertexBallImage src f₁ w)) ∧ R' ⊆ interior (Xc ∪
          Tin) ∧
        Disjoint Tout (interior (Xc ∪ Tin)) ∧ IsPLBall 3 Tout ∧ frontier Tout = Dj ∪ Aout ∪ Lout ∧
        Tout ∩ (fbl s) = Aout ∧ Lin ⊆ Tin)
    (hclean : ¬ (Disjoint (interior (Xc ∪ Tin))
      (frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s)) ∧
      ∀ u : Section34CompactVertexIndex K K', ¬ Section34Incident u.1 s.1 →
        Disjoint (Xc ∪ Tin) (section34CompactVertexBallImage src f₁ u))) :
    ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set E3,
      Section34CompactFaceBallInvariants K K' h H (section34CompactVertexBallImage src f₁)
        (section34CompactSplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd' s + 1 ≤
        section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd s ∧
      section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd' s ≤
        section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd s := by
  classical
  obtain ⟨hfcell, hfrim, hfV, hf4, -, -, -, -, -, hsTs, -⟩ := id hinv
  obtain ⟨-, hf₁, -, -, hmark, -, -, hrimT, hnest, hVcar, -⟩ := id hgraph
  have hVcell := hcut.isPLCellOn_vertexBallImage hf₁
  have hEcell := hcut.isPLCellOn_splitDiskImage hf₁
  set T := section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s
  set Sg := frontier (⋃ u, section34CompactVertexBallImage src f₁ u)
  set Θ := frontier T
  obtain ⟨S₁, S₂, -, -, hTsolid, -⟩ := hnest s
  have hTcomp := hTsolid.isPolyhedron.isCompact
  have hTcl := hTcomp.isClosed
  have hΘT : Θ ⊆ T := hTcl.frontier_subset
  have hPb := (hfcell s).isPLBall_three
  have hPfr := (hfcell s).boundary_eq_frontier
  have hPcl := hPb.isPolyhedron.isClosed
  have hfbs := (hfcell s).boundary_subset
  have hDwV := hDw.trans (hVcell w).boundary_subset
  have hJdb : Jd ⊆ fblBd s := hDJ.symm.subset.trans inter_subset_right
  have hJdD : Jd ⊆ Dj := hDJ.symm.subset.trans inter_subset_left
  have hJD : q '' stdSimplexBoundary 2 ⊆ Dj := hqJ.symm.subset.trans hJdD
  have hJTr : q '' stdSimplexBoundary 2 ⊆ frontier (fbl s) ∩ Θ :=
    fun x hx => ⟨hPfr.subset (hJdb (hqJ.symm.subset hx)), hDjT (hJD hx)⟩
  have hwne : ∀ u : Section34CompactVertexIndex K K', ¬ Section34Incident u.1 s.1 → u ≠ w :=
    fun u hu he => hu (he ▸ hwinc)
  have hVT : ∀ u : Section34CompactVertexIndex K K', Section34Incident u.1 s.1 →
      section34CompactVertexBallImage src f₁ u ⊆ T := fun u hu x hx =>
    mem_iUnion₂.mpr ⟨⟨(s, u), hu⟩, rfl, hx⟩
  have hTinc : ∀ x ∈ T, ∃ u : Section34CompactVertexIndex K K', Section34Incident u.1 s.1 ∧
      x ∈ section34CompactVertexBallImage src f₁ u := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hx
    exact ⟨a.1.2, ha ▸ a.2, hxa⟩
  have hwt : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      Section34Incident w.1 t.1 :=
    fun t ht => hwinc.trans (convexHull_min ht (convex_convexHull ℝ _))
  have hVwt : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      section34CompactVertexBallImage src f₁ w ⊆ interior (H t.1) :=
    fun t ht x hx => hVcar w t.1 t.2.1 (hwt t ht) (Or.inr hx)
  have hDjV : ∀ u, u ≠ w → Disjoint Dj (section34CompactVertexBallImage src f₁ u) :=
    fun u hu => disjoint_left.mpr fun x hx hxV => hOMV x (hDO hx) u hu hxV
  have hy₀ : yJ ∈ fblBd s ∩ Sg := by
    refine ⟨hJdb hyJ, ?_⟩
    have hm : yJ ∈ frontier T ∩ O₀ :=
      ⟨hDjT (hJdD hyJ), hfO₀ (hfbs (hJdb hyJ))⟩
    rw [← hSgO₀] at hm
    exact hm.1
  have hcy₀ : yJ ∈ q '' stdSimplexBoundary 2 := hqJ.subset hyJ
  obtain ⟨hW, hX, hXW, hPX, hWeq,
    hWf, hXf, hEu, hEi, hEinB, hEoutB, hBAin, hBAout, hBinJ, hBoutJ, hEinc, hEoutc, hAinc,
    hAoutc, hLinc, hLoutc, hBinc, hBoutc, hsubO, hAVF, hLVF, hLinP, hLoutP, hYs, hYsf, R, Lr, g,
    hRo, hRO,
    hLrO, hToutR, hclR, hgc, hgLr, hgR, hgT, hRP, hRVF, hRV, hRY, hclRY, R', Lr', g', hR'o,
    hR'O, hLr'O, hTinR', hclR', hg'c, hg'Lr, hg'R, hg'T, hR'P, hR'VF, hR'V, hR'Y, hToutY,
    hToutb, hToutf,
    hToutP, hLinT⟩ := hShell
  have hAinO : Ain ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hx)))))
  have hAoutO : Aout ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))
  have hLinO : Lin ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inl (Or.inr hx))))
  have hLoutO : Lout ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inr hx)))
  have hTinO : Tin ⊆ O := fun x hx => hsubO (Or.inl (Or.inr hx))
  have hToutO : Tout ⊆ O := fun x hx => hsubO (Or.inr hx)
  have hPfrE : frontier (fbl s) = Bin ∪ Ain ∪ (Bout ∪ Aout) := by
    rw [← hEu, hEinB, hEoutB]
  have hVobs : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      section34CompactVertexBallImage src f₁ w ⊆
        section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t :=
    fun t ht x hx => Or.inl (mem_iUnion₂.mpr ⟨⟨(t, w), hwt t ht⟩, rfl, hx⟩)
  have hfobs : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      fbl s ⊆ section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t :=
    fun t ht x hx => Or.inr (mem_iUnion₂.mpr ⟨s, ht, hx⟩)
  have hYfr : frontier (Xc ∪ Tin) ⊆ Dj ∪ fblBd s := by
    rw [hYsf]
    exact union_subset_union_right _ (fun x hx => hPfr.symm.subset (hEu.subset (Or.inl hx)))
  have hpocketH : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      Xc ∪ Tin ⊆ interior (H t.1) := by
    intro t ht
    have hfrY : frontier (Xc ∪ Tin) ⊆ interior (H t.1) :=
      hYfr.trans (union_subset (hDwV.trans (hVwt t ht)) (hfbs.trans (hsTs s t ht)))
    have hsub := (hcar.2.2 t.1 t.2.1).isPLBall_three.subset_of_isCompact_frontier_subset
      hYs.isPolyhedron.isCompact (hfrY.trans interior_subset)
    intro x hx
    by_cases hxi : x ∈ interior (Xc ∪ Tin)
    · exact interior_mono hsub hxi
    · exact hfrY ⟨subset_closure hx, hxi⟩
  have hPkfr : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      frontier (Xc ∪ Tin) ⊆
        section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t :=
    fun t ht => hYfr.trans (union_subset (hDwV.trans (hVobs t ht)) (hfbs.trans (hfobs t ht)))
  have hTinP : Disjoint Tin (interior (fbl s)) := by
    refine Set.disjoint_left.mpr fun x hxT hxi => ?_
    rcases hTinR' hxT with hxR | hxD | hxA
    · exact Set.disjoint_left.mp hR'P hxR (interior_subset hxi)
    · exact (hJTr (hDP.subset ⟨hxD, interior_subset hxi⟩)).1.2 hxi
    · exact (hEu.subset (Or.inl (hEinB.symm.subset (Or.inr hxA)))).2 hxi
  have hYP : Disjoint (interior (fbl s)) (Xc ∪ Tin) := by
    refine Set.disjoint_left.mpr fun x hxi hx => ?_
    rcases hx with hxX | hxT
    · exact Set.disjoint_left.mp hPX hxi hxX
    · exact Set.disjoint_left.mp hTinP hxT hxi
  have hPW : fbl s ⊆ Wc := fun x hx => by
    rw [hWeq]
    exact Or.inl (Or.inl (Or.inl hx))
  have hRobsG : ∀ (t : Section34CompactSimplexIndex K 4), Section34Incident s.1 t.1 →
      ∀ A : Set E3, A ⊆ O → Disjoint A (fbl s) →
        (A ⊆ section34CompactVertexBallImage src f₁ w ∨
          Disjoint A (section34CompactVertexBallImage src f₁ w)) →
        A ⊆ section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t ∨
          Disjoint A (section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t)
      := by
    intro t ht A hAO hAP hAV
    rcases hAV with hAV | hAV
    · exact Or.inl (hAV.trans (hVobs t ht))
    · right
      refine disjoint_left.mpr fun x hx hxo => ?_
      rcases hxo with hxo | hxo
      · obtain ⟨a, -, hxa⟩ := mem_iUnion₂.mp hxo
        by_cases haw : a.1.2 = w
        · exact disjoint_left.mp hAV hx (haw ▸ hxa)
        · exact hOMV x (hAO hx) a.1.2 haw hxa
      · obtain ⟨s', -, hxs'⟩ := mem_iUnion₂.mp hxo
        by_cases hs' : s' = s
        · exact disjoint_left.mp hAP hx (hs' ▸ hxs')
        · exact hOMf x (hAO hx) s' hs' hxs'
  have hBhG : ∀ (t : Section34CompactSimplexIndex K 4), Section34Incident s.1 t.1 →
      ∀ A : Set E3, A ⊆ frontier (fbl s) → Dj ∪ A ⊆
        section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t :=
    fun t ht A hA => union_subset (hDwV.trans (hVobs t ht))
      (hA.trans (hPcl.frontier_subset.trans (hfobs t ht)))
  have hAinP : Ain ⊆ frontier (fbl s) :=
    fun x hx => hEu.subset (Or.inl (hEinB.symm.subset (Or.inr hx)))
  have hAoutP : Aout ⊆ frontier (fbl s) :=
    fun x hx => hEu.subset (Or.inr (hEoutB.symm.subset (Or.inr hx)))
  have hMkO : ∀ (t : Section34CompactSimplexIndex K 4), Section34Incident s.1 t.1 →
      ∀ u : Section34CompactVertexIndex K K', ¬ Section34Incident u.1 t.1 →
        ∀ y ∈ h '' (u.1 : Set E3), y ∉ O := by
    intro t ht u hu y hy hyO
    have huw : u ≠ w := fun he => hu (he ▸ hwt t ht)
    exact hOMV y hyO u huw (interior_subset (hmark u hy))
  have hObdd : ∀ (t : Section34CompactSimplexIndex K 4), Section34Incident s.1 t.1 →
      Bornology.IsBounded O := fun t ht =>
    (hcar.2.2 t.1 t.2.1).isCompact.isBounded.subset
      (fun x hx => interior_subset (hOMH x hx t ht))
  have hYintP : Disjoint (interior (Xc ∪ Tin)) (fbl s) := by
    refine disjoint_left.mpr fun x hx hxP => ?_
    have hxcl : x ∈ closure (interior (fbl s)) :=
      (hPb.closure_interior_of_finrank (by simp)).symm ▸ hxP
    obtain ⟨z, hzY, hzP⟩ := mem_closure_iff.mp hxcl _ isOpen_interior hx
    exact disjoint_left.mp hYP hzP (interior_subset hzY)
  have hz : ∃ z ∈ interior (Xc ∪ Tin), z ∉ T := by
    rcases not_and_or.mp hclean with hbad | hbad
    · rw [not_disjoint_iff] at hbad
      obtain ⟨y, hyY, hyΘ⟩ := hbad
      have hcl : y ∈ closure Tᶜ := by
        change y ∈ frontier T at hyΘ
        rw [frontier_eq_closure_inter_closure] at hyΘ
        exact hyΘ.2
      obtain ⟨z, hzY, hzT⟩ := mem_closure_iff.mp hcl _ isOpen_interior hyY
      exact ⟨z, hzY, hzT⟩
    · push Not at hbad
      obtain ⟨u, hu, hne⟩ := hbad
      rw [not_disjoint_iff] at hne
      obtain ⟨y, hyY, hyu⟩ := hne
      have hyfr : y ∉ frontier (Xc ∪ Tin) := by
        intro hyf
        rcases hYfr hyf with hyD | hyB
        · exact disjoint_left.mp (hDjV u (hwne u hu)) hyD hyu
        · exact notMem_empty y ((hfV s u hu) ▸ ⟨hfbs hyB, hyu⟩)
      have hyi : y ∈ interior (Xc ∪ Tin) := by
        by_contra hn
        exact hyfr ⟨subset_closure hyY, hn⟩
      have hycl := (hVcell u).subset_closure_interior hyu
      obtain ⟨z, hzY, hzV⟩ := mem_closure_iff.mp hycl _ isOpen_interior hyi
      refine ⟨z, hzY, fun hzT => ?_⟩
      obtain ⟨v, hv, hzv⟩ := hTinc z hzT
      have huv : u ≠ v := fun he => hu (he ▸ hv)
      exact notMem_empty z ((hcut.interior_vertexBallImage_inter hf₁ huv) ▸ ⟨hzV, hzv⟩)
  have hmainp : ∀ x ∈ Xc, x ∉ T → ∃ p ∈ interior Xc, p ∉ T := by
    intro x hx hxT
    have hxcl : x ∈ closure (interior Xc) :=
      (hX.closure_interior_of_finrank (by simp)).symm ▸ hx
    obtain ⟨p, hpT, hpX⟩ := mem_closure_iff.mp hxcl _ hTcl.isOpen_compl hxT
    exact ⟨p, hpX, hpT⟩
  obtain ⟨p, hpX, hpT⟩ : ∃ p ∈ interior Xc, p ∉ T := by
    obtain ⟨z, hzi, hzT⟩ := hz
    rcases interior_subset hzi with hzX | hzTin
    · exact hmainp z hzX hzT
    have hzD : z ∉ Dj := fun h => hzT (hΘT (hDjT h))
    have hzA : z ∉ Ain := fun h => disjoint_left.mp hYintP hzi
      (hPcl.frontier_subset (hAinP h))
    have hzR : z ∈ R' := by
      rcases hTinR' hzTin with h | h | h
      · exact h
      · exact False.elim (hzD h)
      · exact False.elim (hzA h)
    have hR'V' : Disjoint R' (section34CompactVertexBallImage src f₁ w) := by
      rcases hR'V with h | h
      · exact False.elim (hzT (hVT w hwinc (h hzR)))
      · exact h
    have hz'R := hg'R hzR
    have hz'X : g' z ∈ Xc := by
      rcases interior_subset (hR'Y hz'R) with h | h
      · exact h
      · exact False.elim (hg'T z hzR h)
    refine hmainp (g' z) hz'X fun hz'T => ?_
    obtain ⟨u, -, hzu⟩ := hTinc (g' z) hz'T
    by_cases huw : u = w
    · exact disjoint_left.mp hR'V' hz'R (huw ▸ hzu)
    · exact hOMV (g' z) (hR'O hz'R) u huw hzu
  have hTconn := isConnected_compl_of_isCombinatorialSolidTorus hTsolid
  obtain ⟨qq, hqq⟩ : (Wc ∪ T)ᶜ.Nonempty :=
    nonempty_compl.mpr (hW.isPolyhedron.isCompact.union hTcomp).ne_univ
  have hqqW : qq ∉ Wc := fun h => hqq (Or.inl h)
  have hqqT : qq ∉ T := fun h => hqq (Or.inr h)
  have hjoin : JoinedIn Tᶜ p qq :=
    ((hTcl.isOpen_compl.isConnected_iff_isPathConnected).mp hTconn).joinedIn p hpT qq hqqT
  obtain ⟨Nt, hNtc, -, hNtT, -, hG⟩ := exists_isPLBall_sdiff_interior_tube
    (∅ : Finset (E3 × E3)) hX hW hXW hTcl isOpen_univ (subset_univ _) hpX hqqW hjoin
  set G := Wc \ interior (Xc ∪ Nt) with hGdef
  have hNtc' : IsClosed Nt := hNtc.isClosed
  have hGcl : IsClosed G := hW.isPolyhedron.isClosed.sdiff isOpen_interior
  have hGsub : G ⊆ fbl s ∪ (Tin ∪ Tout) := by
    rintro x ⟨hxW, hxi⟩
    rw [hWeq] at hxW
    rcases hxW with ((hxP | hxX) | hxT) | hxT
    · exact Or.inl hxP
    · have hxf : x ∈ frontier Xc :=
        ⟨subset_closure hxX, fun h' => hxi (interior_mono subset_union_left h')⟩
      rw [hXf] at hxf
      rcases hxf with hxL | hxB
      · exact Or.inr (Or.inl (hLinT hxL))
      · exact Or.inl (hPcl.frontier_subset (hEu.subset (Or.inl (hEinB.symm.subset
          (Or.inl hxB)))))
    · exact Or.inr (Or.inl hxT)
    · exact Or.inr (Or.inr hxT)
  have hGN : G ∩ Ntᶜ = (Wc \ interior Xc) ∩ Ntᶜ := by
    ext x
    constructor
    · rintro ⟨⟨hxW, hxi⟩, hxN⟩
      exact ⟨⟨hxW, fun h' => hxi (interior_mono subset_union_left h')⟩, hxN⟩
    · rintro ⟨⟨hxW, hxi⟩, hxN⟩
      refine ⟨⟨hxW, fun h' => hxi ?_⟩, hxN⟩
      have hO' : IsOpen (interior (Xc ∪ Nt) ∩ Ntᶜ) := isOpen_interior.inter hNtc'.isOpen_compl
      exact interior_maximal (fun y hy => (interior_subset hy.1).resolve_right hy.2) hO'
        ⟨h', hxN⟩
  have hfrG : frontier G ∩ Ntᶜ = (Lout ∪ Bout ∪ (Lin ∪ Bin)) ∩ Ntᶜ := by
    rw [frontier_inter_eq_of_inter_eq hNtc'.isOpen_compl hGN,
      frontier_sdiff_interior_of_subset_interior hW.isPolyhedron.isClosed
        hX.isPolyhedron.isClosed (hX.closure_interior_of_finrank (by simp)) hXW, hWf, hXf]
  have hGΘ : frontier G ∩ Θ = (Bin ∪ Bout) ∩ Θ := by
    ext x
    constructor
    · rintro ⟨hxf, hxΘ⟩
      have hxN : x ∉ Nt := fun h' => Set.disjoint_left.mp hNtT h' (hΘT hxΘ)
      rcases (hfrG.subset ⟨hxf, hxN⟩).1 with (hxL | hxB) | (hxL | hxB)
      · exact absurd hxΘ (hLΘ x (Or.inr hxL))
      · exact ⟨Or.inr hxB, hxΘ⟩
      · exact absurd hxΘ (hLΘ x (Or.inl hxL))
      · exact ⟨Or.inl hxB, hxΘ⟩
    · rintro ⟨hxB, hxΘ⟩
      have hxN : x ∉ Nt := fun h' => Set.disjoint_left.mp hNtT h' (hΘT hxΘ)
      refine ⟨(hfrG.symm.subset ⟨?_, hxN⟩).1, hxΘ⟩
      rcases hxB with hxB | hxB
      · exact Or.inr (Or.inr hxB)
      · exact Or.inl (Or.inr hxB)
  have hBΘ : (Bin ∪ Bout) ∩ Θ = (frontier (fbl s) ∩ Θ) \ q '' stdSimplexBoundary 2 := by
    ext x
    constructor
    · rintro ⟨hxB, hxΘ⟩
      refine ⟨⟨?_, hxΘ⟩, fun hxJ => ?_⟩
      · rcases hxB with hxB | hxB
        · exact hEu.subset (Or.inl (hEinB.symm.subset (Or.inl hxB)))
        · exact hEu.subset (Or.inr (hEoutB.symm.subset (Or.inl hxB)))
      · rcases hxB with hxB | hxB
        · exact Set.disjoint_left.mp hBinJ hxB hxJ
        · exact Set.disjoint_left.mp hBoutJ hxB hxJ
    · rintro ⟨⟨hxP, hxΘ⟩, hxJ⟩
      rw [hPfrE] at hxP
      rcases hxP with (hxB | hxA) | (hxB | hxA)
      · exact ⟨Or.inl hxB, hxΘ⟩
      · exact absurd (hAΘ x (Or.inl hxA) hxΘ) hxJ
      · exact ⟨Or.inr hxB, hxΘ⟩
      · exact absurd (hAΘ x (Or.inr hxA) hxΘ) hxJ
  set Oc := (Nt ∪ (Lin ∪ Lout) ∪ (Ain ∪ Aout))ᶜ with hOcdef
  have hOc : IsOpen Oc :=
    ((hNtc'.union (hLinc.union hLoutc)).union (hAinc.union hAoutc)).isOpen_compl
  have hOcN : Oc ⊆ Ntᶜ := fun x hx h' => hx (Or.inl (Or.inl h'))
  have hfrO : frontier G ∩ Oc = frontier (fbl s) ∩ Oc := by
    ext x
    constructor
    · rintro ⟨hxf, hxO⟩
      refine ⟨?_, hxO⟩
      rw [hPfrE]
      rcases (hfrG.subset ⟨hxf, hOcN hxO⟩).1 with (hxL | hxB) | (hxL | hxB)
      · exact absurd (Or.inl (Or.inr (Or.inr hxL))) hxO
      · exact Or.inr (Or.inl hxB)
      · exact absurd (Or.inl (Or.inr (Or.inl hxL))) hxO
      · exact Or.inl (Or.inl hxB)
    · rintro ⟨hxP, hxO⟩
      refine ⟨(hfrG.symm.subset ⟨?_, hOcN hxO⟩).1, hxO⟩
      rw [hPfrE] at hxP
      rcases hxP with (hxB | hxA) | (hxB | hxA)
      · exact Or.inr (Or.inr hxB)
      · exact absurd (Or.inr (Or.inl hxA)) hxO
      · exact Or.inl (Or.inr hxB)
      · exact absurd (Or.inr (Or.inr hxA)) hxO
  have hk2 : frontier G ∩ Θ ⊆ Oc := by
    intro x hx
    rw [hGΘ] at hx
    obtain ⟨hxB, hxΘ⟩ := hx
    rintro ((hxN | hxL | hxL) | hxA | hxA)
    · exact Set.disjoint_left.mp hNtT hxN (hΘT hxΘ)
    · exact hLΘ x (Or.inl hxL) hxΘ
    · exact hLΘ x (Or.inr hxL) hxΘ
    · have hxJ := hAΘ x (Or.inl hxA) hxΘ
      rcases hxB with hxB | hxB
      · exact Set.disjoint_left.mp hBinJ hxB hxJ
      · exact Set.disjoint_left.mp hBoutJ hxB hxJ
    · have hxJ := hAΘ x (Or.inr hxA) hxΘ
      rcases hxB with hxB | hxB
      · exact Set.disjoint_left.mp hBinJ hxB hxJ
      · exact Set.disjoint_left.mp hBoutJ hxB hxJ
  have hk4 : ∀ e : Section34CompactEdgeIndex K K',
      frontier G ∩ section34CompactSplitDiskImage srcBd f₁ e ⊆ Oc := by
    rintro e x ⟨hxf, hxE⟩ ((hxN | hxL | hxL) | hxA | hxA)
    · rcases hGsub (hGcl.frontier_subset hxf) with hxP | hxT | hxT
      · obtain ⟨u, v, -, -, he⟩ := hcut.splitDiskImage_eq_inter hf₁ e
        have hxu : x ∈ section34CompactVertexBallImage src f₁ u :=
          (he ▸ (hEcell e).boundary_subset hxE).1
        have hui : Section34Incident u.1 s.1 := by
          by_contra hn
          exact notMem_empty x ((hfV s u hn) ▸ ⟨hxP, hxu⟩)
        exact disjoint_left.mp hNtT hxN (hVT u hui hxu)
      · exact hOsplit x (hTinO hxT) e hxE
      · exact hOsplit x (hToutO hxT) e hxE
    · exact hOsplit x (hLinO hxL) e hxE
    · exact hOsplit x (hLoutO hxL) e hxE
    · exact hOsplit x (hAinO hxA) e hxE
    · exact hOsplit x (hAoutO hxA) e hxE
  have hk3 : frontier G ∩ Θ = frontier (fbl s) ∩ Θ ∩ (Bin ∪ Bout) := by
    rw [hGΘ]
    ext x
    constructor
    · rintro ⟨hxB, hxΘ⟩
      refine ⟨⟨?_, hxΘ⟩, hxB⟩
      rcases hxB with hxB | hxB
      · exact hEu.subset (Or.inl (hEinB.symm.subset (Or.inl hxB)))
      · exact hEu.subset (Or.inr (hEoutB.symm.subset (Or.inl hxB)))
    · rintro ⟨⟨-, hxΘ⟩, hxB⟩
      exact ⟨hxB, hxΘ⟩
  have h7 : CarriesIntegralFirstHomologyOnto (frontier G ∩ Θ) T := by
    change CarriesFirstHomologyOnto (frontier G ∩ Θ) T
    rw [hGΘ, hBΘ]
    exact hcarry
  have hrimG : h '' section34CompactSimplexRim s.1 ⊆ interior G := by
    intro x hx
    have hxP := hfrim s hx
    have hxT := interior_subset (hrimT s hx)
    have hxN : x ∉ Nt := fun h => disjoint_left.mp hNtT h hxT
    have hOpen : IsOpen (interior (fbl s) ∩ Ntᶜ) := isOpen_interior.inter hNtc'.isOpen_compl
    refine interior_maximal (t := interior (fbl s) ∩ Ntᶜ) (s := G) (fun y hy => ?_)
      hOpen ⟨hxP, hxN⟩
    refine ⟨hPW (interior_subset hy.1), fun h => ?_⟩
    rcases interior_subset h with h | h
    · exact disjoint_left.mp hPX hy.1 h
    · exact hy.2 h
  have hGO₀ : G ⊆ O₀ := by
    intro x hx
    rcases hGsub hx with hx | hx | hx
    · exact hfO₀ hx
    · exact hOO₀ (hTinO hx)
    · exact hOO₀ (hToutO hx)
  have hZV : ∀ u : Section34CompactVertexIndex K K', ¬ Section34Incident u.1 s.1 →
      Disjoint (Tin ∪ Tout) (section34CompactVertexBallImage src f₁ u) := by
    intro u hu
    refine disjoint_left.mpr fun x hx hxu => ?_
    rcases hx with hx | hx
    · exact hOMV x (hTinO hx) u (hwne u hu) hxu
    · exact hOMV x (hToutO hx) u (hwne u hu) hxu
  have hZs : ∀ s', s' ≠ s → (Tin ∪ Tout) ∩ fbl s' ⊆
      interior (⋃ u, section34CompactVertexBallImage src f₁ u) := by
    rintro s' hs' x ⟨hx | hx, hxs'⟩
    · exact False.elim (hOMf x (hTinO hx) s' hs' hxs')
    · exact False.elim (hOMf x (hToutO hx) s' hs' hxs')
  have hZH : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      Tin ∪ Tout ⊆ interior (H t.1) := by
    intro t ht x hx
    rcases hx with hx | hx
    · exact hOMH x (hTinO hx) t ht
    · exact hOMH x (hToutO hx) t ht
  have hr : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      ∃ (r : E3 → E3) (Y B : Set E3), IsCompact Y ∧ Bornology.IsBounded B ∧
        frontier Y ⊆
          section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t ∧
        ContinuousOn r ((section34CompactTetraObstacle
          (section34CompactVertexBallImage src f₁) fbl t)ᶜ \ Y) ∧
        MapsTo r ((section34CompactTetraObstacle (section34CompactVertexBallImage src f₁)
          fbl t)ᶜ \ Y)
          (section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t ∪
            (Tin ∪ Tout))ᶜ ∧
        (∀ x ∉ B, r x = x) ∧
        ∀ u : Section34CompactVertexIndex K K', ¬ Section34Incident u.1 t.1 →
          ∀ y ∈ h '' (u.1 : Set E3), r y = y := by
    intro t ht
    set Obs := section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t
    obtain ⟨ri, hric, hrim, hriid, -⟩ := exists_compactPush hR'o hclR' (hBhG t ht Ain hAinP)
      hg'c hg'Lr hg'R hg'T hTinR' (hRobsG t ht R' hR'O hR'P hR'V)
    obtain ⟨ro, hroc, hrom, hroid, hroR⟩ := exists_compactPush hRo hclR (hBhG t ht Aout hAoutP)
      hgc hgLr hgR hgT hToutR (hRobsG t ht R hRO hRP hRV)
    have hriO : MapsTo ri Obsᶜ Obsᶜ :=
      fun x hx ho => hrim hx (Or.inl ho)
    have hid : ∀ x ∉ O, (ro ∘ ri) x = x := by
      intro x hx
      change ro (ri x) = x
      rw [hriid x (fun h => hx (hR'O h)), hroid x (fun h => hx (hRO h))]
    refine ⟨ro ∘ ri, ∅, O, isCompact_empty, hObdd t ht, by simp,
      (hroc.comp hric hriO).mono sdiff_subset, ?_, hid,
      fun u hu y hy => hid y (hMkO t ht u hu y hy)⟩
    intro x hx
    have h1 := hrim hx.1
    have h2 := hrom (hriO hx.1)
    have hn : ro (ri x) ∉ Tin := by
      by_cases hxR : ri x ∈ R
      · exact fun h => disjoint_left.mp hRY (hroR hxR) (Or.inr h)
      · rw [hroid (ri x) hxR]
        exact fun h => h1 (Or.inr h)
    rintro (ho | hTi | hTo)
    · exact h2 (Or.inl ho)
    · exact hn hTi
    · exact h2 (Or.inr hTo)
  exact exists_compactCompression_of_ball hinv s hfO₀ hSgO₀ hG hGO₀ hrimG hGsub
    hZV hZs hZH hr hOc (by rw [hPfr]; exact hfrO) hk2 hk4
    (by rw [hPfr]; exact hk3) (hBinc.union hBoutc) hy₀
    (fun hx => hx.elim (fun h => disjoint_left.mp hBinJ h hcy₀)
      (fun h => disjoint_left.mp hBoutJ h hcy₀)) h7

theorem exists_compactCompression_of_disjoint
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hcar : Section34CompactCarrierControl K h ε H)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd) (s : Section34CompactSimplexIndex K 3)
    {w : Section34CompactVertexIndex K K'} {Dj Jd : Set E3}
    (hDcell : IsPLCellOn 2 Dj Jd) (hDw : Dj ⊆ section34CompactVertexBallImage srcBd f₁ w)
    (hDJ : Dj ∩ fblBd s = Jd)
    (hDE : ∀ e, Disjoint Dj (section34CompactSplitDiskImage src f₁ e))
    (hDo : ∀ s', s' ≠ s → Disjoint (Dj \ Jd) (fbl s'))
    (hout : Disjoint (Dj \ Jd) (fbl s)) :
    ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set E3,
      Section34CompactFaceBallInvariants K K' h H (section34CompactVertexBallImage src f₁)
        (section34CompactSplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd' s + 1 ≤
        section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd s ∧
      section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd' s ≤
        section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd s := by
  classical
  obtain ⟨hfcell, hfrim, hfV, hf4, hf5, -, hf7, -, -, hsTs, -⟩ := id hinv
  obtain ⟨-, hf₁, -, -, hmark, -, -, hrimT, hnest, hVcar, -⟩ := id hgraph
  have hVcell := hcut.isPLCellOn_vertexBallImage hf₁
  have hEcell := hcut.isPLCellOn_splitDiskImage hf₁
  let _ : Finite (Section34CompactVertexIndex K K') :=
    finite_section34CompactGraphIndex hcut.2.2.1 _ 1
  let _ : Finite (Section34CompactEdgeIndex K K') :=
    finite_section34CompactGraphIndex hcut.2.2.1 _ 2
  let _ : Finite (Section34CompactSimplexIndex K 3) :=
    finite_section34CompactSimplexIndex hcut.2.1 3
  let _ : Finite (Section34CompactSimplexIndex K 4) :=
    finite_section34CompactSimplexIndex hcut.2.1 4
  set T := section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s
  set Sg := frontier (⋃ u, section34CompactVertexBallImage src f₁ u)
  set Θ := frontier T
  obtain ⟨S₁, S₂, -, -, hTsolid, -⟩ := hnest s
  have hTcomp := hTsolid.isPolyhedron.isCompact
  have hTcl := hTcomp.isClosed
  have hΘtor := hTsolid.isPLTorus_frontier
  have hΘT : Θ ⊆ T := hTcl.frontier_subset
  have hPb := (hfcell s).isPLBall_three
  have hPfr := (hfcell s).boundary_eq_frontier
  have hPcl := hPb.isPolyhedron.isClosed
  have hfbs := (hfcell s).boundary_subset
  have hVwb := (hVcell w).isPLBall_three
  have hVwfr := (hVcell w).boundary_eq_frontier
  have hDV : Dj ⊆ frontier (section34CompactVertexBallImage src f₁ w) := hDw.trans hVwfr.subset
  have hDwV := hDw.trans (hVcell w).boundary_subset
  obtain ⟨q, hq, hqJ⟩ := hDcell.exists_isPLHomeomorphOn_stdSimplex
  have hJdD := hDcell.boundary_subset
  have hJdb : Jd ⊆ fblBd s := hDJ.symm.subset.trans inter_subset_right
  obtain ⟨yJ, hyJ⟩ : Jd.Nonempty := by
    rw [hqJ]
    exact (nonempty_stdSimplexBoundary_of_pos (by decide : 0 < 2)).image q
  have hwinc : Section34Incident w.1 s.1 := by
    by_contra hn
    exact notMem_empty yJ ((hfV s w hn) ▸ ⟨hfbs (hJdb hyJ), hDwV (hJdD hyJ)⟩)
  have hwne : ∀ u : Section34CompactVertexIndex K K', ¬ Section34Incident u.1 s.1 → u ≠ w :=
    fun u hu he => hu (he ▸ hwinc)
  have hVT : ∀ u : Section34CompactVertexIndex K K', Section34Incident u.1 s.1 →
      section34CompactVertexBallImage src f₁ u ⊆ T := fun u hu x hx =>
    mem_iUnion₂.mpr ⟨⟨(s, u), hu⟩, rfl, hx⟩
  have hTinc : ∀ x ∈ T, ∃ u : Section34CompactVertexIndex K K', Section34Incident u.1 s.1 ∧
      x ∈ section34CompactVertexBallImage src f₁ u := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hx
    exact ⟨a.1.2, ha ▸ a.2, hxa⟩
  obtain ⟨Ov, hOv, hDOv, hSgOv, hOvV, hOvE⟩ := hcut.exists_isOpen_compression_disk hf₁ hDw hDE
  have hDjV : ∀ u, u ≠ w → Disjoint Dj (section34CompactVertexBallImage src f₁ u) :=
    fun u hu => (hOvV u hu).mono_left hDOv
  have hDjSg : Dj ⊆ Sg := by
    intro x hx
    have hm : x ∈ frontier (section34CompactVertexBallImage src f₁ w) ∩ Ov := ⟨hDV hx, hDOv hx⟩
    rw [← hSgOv] at hm
    exact hm.1
  set O₀ := (⋃ u ∈ {u : Section34CompactVertexIndex K K' | ¬ Section34Incident u.1 s.1},
    section34CompactVertexBallImage src f₁ u)ᶜ
  have hO₀ : IsOpen O₀ := ((Set.toFinite _).isClosed_biUnion fun u _ =>
    (hVcell u).isCompact.isClosed).isOpen_compl
  have hO₀V : ∀ u, ¬ Section34Incident u.1 s.1 →
      Disjoint O₀ (section34CompactVertexBallImage src f₁ u) :=
    fun u hu => disjoint_left.mpr fun x hx hxv => hx (mem_iUnion₂.mpr ⟨u, hu, hxv⟩)
  have hfO₀ : fbl s ⊆ O₀ := by
    intro x hx hxO
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hxO
    exact notMem_empty x ((hfV s u hu) ▸ ⟨hx, hxu⟩)
  have hDO₀ : Dj ⊆ O₀ := by
    intro x hx hxO
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hxO
    exact disjoint_left.mp (hDjV u (hwne u hu)) hx hxu
  have hSgO₀ := frontier_iUnion_inter_eq_faceTorus_inter s hO₀ hO₀V
  have hSgT : ∀ x ∈ O₀, (x ∈ Sg ↔ x ∈ Θ) := by
    intro x hx
    simpa only [mem_inter_iff, hx, and_true] using
      Iff.of_eq (congrArg (fun A => x ∈ A) hSgO₀)
  have hDjT : Dj ⊆ Θ := fun x hx => (hSgT x (hDO₀ hx)).mp (hDjSg hx)
  have hcrossPΘ : ∀ x ∈ frontier (fbl s) ∩ Θ,
      HasPLCrossingAt (frontier (fbl s)) Θ x := by
    rintro x ⟨hxP, hxΘ⟩
    have hxb := hPfr.symm.subset hxP
    have hxO := hfO₀ (hfbs hxb)
    have hcr := hf5 s x ⟨hxb, (hSgT x hxO).mpr hxΘ⟩
    rw [hPfr] at hcr
    refine hcr.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) ?_
    filter_upwards [hO₀.mem_nhds hxO] with z hz
    exact hSgT z hz
  set Oo := Ov ∩ O₀
  have hOo : IsOpen Oo := hOv.inter hO₀
  have hDO : Dj ⊆ Oo := fun x hx => ⟨hDOv hx, hDO₀ hx⟩
  have hΘO : Oo ∩ Θ = Oo ∩ frontier (section34CompactVertexBallImage src f₁ w) := by
    ext x
    by_cases hx : x ∈ Oo
    · have hv : x ∈ Sg ↔ x ∈ frontier (section34CompactVertexBallImage src f₁ w) := by
        simpa only [mem_inter_iff, hx.1, and_true] using
          Iff.of_eq (congrArg (fun A => x ∈ A) hSgOv)
      simp only [mem_inter_iff, hx, true_and]
      exact (hSgT x hx.2).symm.trans hv
    · simp only [mem_inter_iff, hx, false_and]
  have hDP : Dj ∩ fbl s = q '' stdSimplexBoundary 2 := by
    rw [← hqJ]
    apply Subset.antisymm
    · rintro x ⟨hxD, hxP⟩
      by_contra hxJ
      exact disjoint_left.mp hout ⟨hxD, hxJ⟩ hxP
    · exact fun x hx => ⟨hJdD hx, hfbs (hJdb hx)⟩
  have hJD : q '' stdSimplexBoundary 2 ⊆ Dj := hqJ.symm.subset.trans hJdD
  have hJTr : q '' stdSimplexBoundary 2 ⊆ frontier (fbl s) ∩ Θ :=
    fun x hx => ⟨hPfr.subset (hJdb (hqJ.symm.subset hx)), hDjT (hJD hx)⟩
  have hcrossVP : ∀ x ∈ q '' stdSimplexBoundary 2,
      HasPLCrossingAt (frontier (section34CompactVertexBallImage src f₁ w))
        (frontier (fbl s)) x := by
    intro x hx
    refine (hcrossPΘ x (hJTr hx)).symm.congr ?_ (Filter.Eventually.of_forall fun _ => Iff.rfl)
    filter_upwards [hOo.mem_nhds (hDO (hJD hx))] with z hz
    simpa only [mem_inter_iff, hz, true_and] using
      Iff.of_eq (congrArg (fun A => z ∈ A) hΘO)
  have hwt : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      Section34Incident w.1 t.1 :=
    fun t ht => hwinc.trans (convexHull_min ht (convex_convexHull ℝ _))
  have hVwt : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      section34CompactVertexBallImage src f₁ w ⊆ interior (H t.1) :=
    fun t ht x hx => hVcar w t.1 t.2.1 (hwt t ht) (Or.inr hx)
  have hDs' : ∀ s', s' ≠ s → Disjoint Dj (fbl s') := by
    intro s' hs'
    refine disjoint_left.mpr fun x hx hx' => ?_
    by_cases hxJ : x ∈ Jd
    · exact (hDjSg hx).2 (hf4 s s' (Ne.symm hs') ⟨hfbs (hJdb hxJ), hx'⟩)
    · exact disjoint_left.mp (hDo s' hs') ⟨hx, hxJ⟩ hx'
  set Qf := ⋃ s' ∈ {s' : Section34CompactSimplexIndex K 3 | s' ≠ s}, fbl s'
  have hQfc : IsClosed Qf := (Set.toFinite _).isClosed_biUnion fun s' _ =>
    (hfcell s').isCompact.isClosed
  set O := ((⋂ t ∈ {t : Section34CompactSimplexIndex K 4 | Section34Incident s.1 t.1},
    interior (H t.1)) ∩ Oo) ∩ Qfᶜ
  have hOo' : IsOpen O :=
    (((Set.toFinite _).isOpen_biInter fun _ _ => isOpen_interior).inter hOo).inter hQfc.isOpen_compl
  have hDO' : Dj ⊆ O := by
    intro x hx
    refine ⟨⟨mem_iInter₂.mpr fun t ht => hVwt t ht (hDwV hx), hDO hx⟩, ?_⟩
    intro hxQ
    obtain ⟨s', hs', hxs'⟩ := mem_iUnion₂.mp hxQ
    exact disjoint_left.mp (hDs' s' hs') hx hxs'
  have hOMH : ∀ x ∈ O, ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      x ∈ interior (H t.1) := fun x hx t ht => mem_iInter₂.mp hx.1.1 t ht
  have hOMV : ∀ x ∈ O, ∀ u, u ≠ w → x ∉ section34CompactVertexBallImage src f₁ u :=
    fun x hx u hu => disjoint_left.mp (hOvV u hu) hx.1.2.1
  have hOMf : ∀ x ∈ O, ∀ s', s' ≠ s → x ∉ fbl s' :=
    fun x hx s' hs' hxs' => hx.2 (mem_iUnion₂.mpr ⟨s', hs', hxs'⟩)
  have hOsplit : ∀ x ∈ O, ∀ e, x ∉ section34CompactSplitDiskImage srcBd f₁ e :=
    fun x hx e he => disjoint_left.mp (hOvE e) hx.1.2.1 ((hEcell e).boundary_subset he)
  have hOΘ : ∀ x ∈ O,
      (x ∈ Θ ↔ x ∈ frontier (section34CompactVertexBallImage src f₁ w)) := by
    intro x hx
    simpa only [mem_inter_iff, hx.1.2, true_and] using
      Iff.of_eq (congrArg (fun A => x ∈ A) hΘO)
  have hEcc : IsClosed (⋃ e, section34CompactSplitDiskImage src f₁ e) :=
    isClosed_iUnion_of_finite fun e => (hEcell e).isCompact.isClosed
  have hDEc : Disjoint (⋃ e, section34CompactSplitDiskImage src f₁ e) Dj := by
    refine disjoint_right.mpr fun x hx hxE => ?_
    obtain ⟨e, he⟩ := mem_iUnion.mp hxE
    exact disjoint_left.mp (hDE e) hx he
  obtain ⟨Wc, Xc, Ein, Eout, Bin, Bout, Ain, Aout, Lin, Lout, Tin, Tout, hShell⟩ :=
    exists_compressionShell hPb hVwb hq hDV hDP hcrossVP hEcc hDEc hOo' hDO'
  obtain ⟨hW, hX, hXW, hPX, hWeq,
    hWf, hXf, hEu, hEi, hEinB, hEoutB, hBAin, hBAout, hBinJ, hBoutJ, hEinc, hEoutc, hAinc,
    hAoutc, hLinc, hLoutc, hBinc, hBoutc, hsubO, hAVF, hLVF, hLinP, hLoutP, hYs, hYsf, R, Lr, g,
    hRo, hRO,
    hLrO, hToutR, hclR, hgc, hgLr, hgR, hgT, hRP, hRVF, hRV, hRY, hclRY, R', Lr', g', hR'o,
    hR'O, hLr'O, hTinR', hclR', hg'c, hg'Lr, hg'R, hg'T, hR'P, hR'VF, hR'V, hR'Y, hToutY,
    hToutb, hToutf,
    hToutP, hLinT⟩ := id hShell
  have hAinO : Ain ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hx)))))
  have hAoutO : Aout ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))
  have hLinO : Lin ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inl (Or.inr hx))))
  have hLoutO : Lout ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inr hx)))
  have hTinO : Tin ⊆ O := fun x hx => hsubO (Or.inl (Or.inr hx))
  have hToutO : Tout ⊆ O := fun x hx => hsubO (Or.inr hx)
  have hLΘ : ∀ x ∈ Lin ∪ Lout, x ∉ Θ := by
    intro x hx hxΘ
    have hxO : x ∈ O := hx.elim (fun h => hLinO h) (fun h => hLoutO h)
    exact Set.disjoint_left.mp hLVF hx (Or.inl ((hOΘ x hxO).mp hxΘ))
  have hAΘ : ∀ x ∈ Ain ∪ Aout, x ∈ Θ → x ∈ q '' stdSimplexBoundary 2 := by
    intro x hx hxΘ
    have hxO : x ∈ O := hx.elim (fun h => hAinO h) (fun h => hAoutO h)
    exact hAVF ⟨hx, Or.inl ((hOΘ x hxO).mp hxΘ)⟩
  have hPfrE : frontier (fbl s) = Bin ∪ Ain ∪ (Bout ∪ Aout) := by
    rw [← hEu, hEinB, hEoutB]
  have hcy₀ : yJ ∈ q '' stdSimplexBoundary 2 := hqJ.subset hyJ
  have hcTreg : ∀ x ∈ Θ, x ∈ closure (interior T) := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := hTinc x (hΘT hx)
    have hcl := (hVcell u).isPLBall_three.closure_interior_of_finrank (by simp)
    exact closure_mono (interior_mono (hVT u hu)) (hcl.symm ▸ hxu)
  obtain ⟨ι, hιfin, Cs, hC, hCd, hCeq⟩ := exists_iUnion_isPLSphere_one_of_forall_lineChart
    (hPb.isPolyhedron.frontier.inter hΘtor.1) hcrossPΘ fun x hx =>
      (hcrossPΘ x hx).exists_lineChart hx.1
        (hPb.isPLSphere_frontier.exists_isOpen_inter_homeomorph_of_two hx.1) hTcl (hcTreg x hx.2)
  have hZS : CarriesFirstHomologyOnto (id '' (frontier (fbl s) ∩ Θ)) T := by
    rw [image_id, ← hPfr]
    exact hf7 s
  have hJsph : IsPLSphere 1 (q '' stdSimplexBoundary 2) :=
    hq.isPLSphere_image_stdSimplexBoundary (n := 1)
  have hDΘ : Dj ⊆ Θ := hDjT
  have hDcl : IsClosed (Dj) := (IsPLBall.isPolyhedron ⟨q, hq⟩).isClosed
  have hDJne : (Dj \ q '' stdSimplexBoundary 2).Nonempty :=
    closure_nonempty_iff.mp ⟨yJ, mem_closure_sdiff_image_stdSimplexBoundary hq hcy₀⟩
  have hDo' : ∀ z ∈ Dj \ q '' stdSimplexBoundary 2, ∃ O' : Set E3, IsOpen O' ∧ z ∈ O' ∧
      O' ∩ Θ ⊆ Dj := by
    intro z hz
    have hS := hVwb.isPLSphere_frontier
    have hint := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDV
    refine ⟨Oo ∩ (closure (frontier (section34CompactVertexBallImage src f₁ w) \ Dj))ᶜ,
      hOo.inter isClosed_closure.isOpen_compl, ⟨hDO hz.1, fun hzc => hz.2 ?_⟩, ?_⟩
    · rw [← hint]
      exact ⟨hz.1, hzc⟩
    · rintro y ⟨⟨hyO, hycl⟩, hyΘ⟩
      have h2 : y ∈ Oo ∩ Θ := ⟨hyO, hyΘ⟩
      rw [hΘO] at h2
      by_contra hyD
      exact hycl (subset_closure ⟨h2.2, hyD⟩)
  have hΘD : (Θ \ Dj).Nonempty := by
    obtain ⟨p, hp⟩ := hJsph.nonempty
    obtain ⟨U₁, φ, r, hU₁, hpU₁, hr, hφ, hφp, hloc⟩ :=
      exists_quadrantChart hPb hVwb hq hDV hDP hp (hcrossVP p hp)
    have hpOo : p ∈ Oo := hDO (hJD hp)
    have hopen : IsOpen (φ '' (U₁ ∩ Oo)) :=
      hφ.isOpen_image_of_isOpen Metric.isOpen_ball (hU₁.inter hOo) inter_subset_left
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 ⟨p, ⟨hpU₁, hpOo⟩, hφp⟩
    have hmem : ((0 : ℝ), ε / 2, (0 : ℝ)) ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ε := by
      rw [mem_ball_zero_iff, Prod.norm_def, Prod.norm_def]
      simp only [norm_zero, Real.norm_eq_abs]
      have h1 : |ε / 2| < ε := by rw [abs_of_pos (by linarith)]; linarith
      exact max_lt hε (max_lt h1 hε)
    obtain ⟨z, ⟨hzU, hzO⟩, hzφ⟩ := hball hmem
    obtain ⟨h1, -, -, -, h5⟩ := hloc z hzU
    refine ⟨z, ?_, fun hzD => ?_⟩
    · have hzV : z ∈ frontier (section34CompactVertexBallImage src f₁ w) :=
        h1.mpr (by rw [hzφ])
      have h3 : z ∈ Oo ∩ frontier (section34CompactVertexBallImage src f₁ w) := ⟨hzO, hzV⟩
      rw [← hΘO] at h3
      exact h3.2
    · have h6 := (h5.mp hzD).2
      rw [hzφ] at h6
      change ε / 2 ≤ 0 at h6
      linarith
  have hJo : ∃ O' : Set E3, IsOpen O' ∧ q '' stdSimplexBoundary 2 ⊆ O' ∧
      frontier (fbl s) ∩ Θ ∩ O' ⊆ q '' stdSimplexBoundary 2 := by
    refine ⟨(Bin ∪ Bout)ᶜ, (hBinc.union hBoutc).isOpen_compl, fun x hx hxB => ?_, ?_⟩
    · rcases hxB with h | h
      · exact Set.disjoint_left.mp hBinJ h hx
      · exact Set.disjoint_left.mp hBoutJ h hx
    · rintro x ⟨⟨hxP, hxΘ⟩, hxO⟩
      rw [hPfrE] at hxP
      rcases hxP with (hxB | hxA) | (hxB | hxA)
      · exact absurd (Or.inl hxB) hxO
      · exact hAΘ x (Or.inl hxA) hxΘ
      · exact absurd (Or.inr hxB) hxO
      · exact hAΘ x (Or.inr hxA) hxΘ
  have hcarry : CarriesFirstHomologyOnto
      ((frontier (fbl s) ∩ Θ) \ q '' stdSimplexBoundary 2) T := by
    have hc := hΘtor.carriesFirstHomologyOnto_image_sdiff_of_disk
      (Tr := frontier (fbl s) ∩ Θ) (φ := id) hC hCd hCeq.symm inter_subset_right
      hJsph.isConnected hJsph.isPolyhedron.isClosed hJTr hJo hDΘ hJD hDcl hDJne hDo' hΘD
      continuousOn_id (fun _ _ _ _ he => he) (by simpa only [image_id] using hΘT) hZS
    simpa only [image_id] using hc
  have hy₀ : yJ ∈ fblBd s ∩ Sg := ⟨hJdb hyJ, hDjSg (hJdD hyJ)⟩
  by_cases hclean : Disjoint (interior (Xc ∪ Tin)) Θ ∧
    ∀ u : Section34CompactVertexIndex K K', ¬ Section34Incident u.1 s.1 →
      Disjoint (Xc ∪ Tin) (section34CompactVertexBallImage src f₁ u)
  · exact compact_compression_of_shell_fill hcut hcar hgraph hinv s hDw hDJ hqJ hDP hwinc hDjT hyJ
      hDO' hfO₀ hSgO₀ (fun x hx => hx.1.2.2) hOMH hOMV hOMf hOsplit hLΘ hAΘ hcarry
      hcrossPΘ hcTreg rfl hShell hclean
  · exact compact_compression_of_shell_tube hcut hcar hgraph hinv s hDw hDJ hqJ hDP hwinc hDjT hyJ
      hDO' hfO₀ hSgO₀ (fun x hx => hx.1.2.2) hOMH hOMV hOMf hOsplit hLΘ hAΘ hcarry hShell hclean

end DifferentialGeometry.Topology.PiecewiseLinear

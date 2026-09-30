/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallMarkedExtension
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsAnnularSplitBall
import DifferentialGeometry.Topology.PiecewiseLinear.PLSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionPocket
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingQuadrant
import DifferentialGeometry.Topology.PiecewiseLinear.Section34WedgeLift

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_compressionSide {P V D E E' F O : Set E3} {q : (Fin 3 → ℝ) → E3}
    (hP : IsPLBall 3 P) (hV : IsPLBall 3 V) (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDV : D ⊆ frontier V) (hDP : D ∩ P = q '' stdSimplexBoundary 2)
    (hcross : ∀ p ∈ q '' stdSimplexBoundary 2, HasPLCrossingAt (frontier V) (frontier P) p)
    {qE qE' : (Fin 3 → ℝ) → E3} (hqE : IsPLHomeomorphOn qE (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) E)
    (hqEJ : qE '' stdSimplexBoundary 2 = q '' stdSimplexBoundary 2)
    (hqE' : IsPLHomeomorphOn qE' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) E')
    (hqE'J : qE' '' stdSimplexBoundary 2 = q '' stdSimplexBoundary 2)
    (hEE' : E ∪ E' = frontier P) (hEE'J : E ∩ E' = q '' stdSimplexBoundary 2)
    (hF : IsClosed F) (hFD : Disjoint F D) (hO : IsOpen O) (hDO : D ⊆ O) :
    ∃ (L Bo Ah C T : Set E3) (ε : ℝ),
      IsPLBall 2 L ∧ IsPLBall 2 (D ∪ Ah) ∧ IsPLSphere 2 (L ∪ Bo) ∧ IsPLBall 3 T ∧
      frontier T = D ∪ Ah ∪ L ∧ E = Bo ∪ Ah ∧ L ∩ Bo = C ∧ Bo ∩ Ah = C ∧ L ∩ P = C ∧
      (∃ qB : (Fin 3 → ℝ) → E3, IsPLHomeomorphOn qB (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Bo ∧
        qB '' stdSimplexBoundary 2 = C) ∧
      Disjoint Bo (q '' stdSimplexBoundary 2) ∧ Disjoint L D ∧ T ∩ P = Ah ∧ T ⊆ O ∧
      Ah ∩ (frontier V ∪ F) ⊆ q '' stdSimplexBoundary 2 ∧ Disjoint L (frontier V ∪ F) ∧
      (ε = 1 ∨ ε = -1) ∧ (∀ y ∈ interior T, y ∈ V ↔ ε = -1) ∧
      (∀ y ∈ L, y ∉ C → (y ∈ V ↔ ε = -1)) ∧
      (∀ Y : Set E3, IsPLBall 3 Y → frontier Y = D ∪ E →
        (Disjoint (interior P) Y → interior T ⊆ interior Y) ∧
        (interior P ⊆ Y → Disjoint (interior T) Y)) ∧
      ∃ (R Lr : Set E3) (g : E3 → E3), IsOpen R ∧ R ⊆ O ∧ Lr ⊆ O ∧ T ⊆ R ∪ (D ∪ Ah) ∧
        closure R ⊆ R ∪ (D ∪ Ah) ∪ Lr ∧ ContinuousOn g (R ∪ Lr) ∧ (∀ y ∈ Lr, g y = y) ∧
        MapsTo g R R ∧ (∀ y ∈ R, g y ∉ T) ∧ Disjoint R P ∧ Disjoint R (frontier V ∪ F) ∧
        (∀ y ∈ R, y ∈ V ↔ ε = -1) ∧
        ∀ Y : Set E3, IsPLBall 3 Y → frontier Y = D ∪ E →
          (Disjoint (interior P) Y → R ⊆ interior Y) ∧ (interior P ⊆ Y → Disjoint R Y) := by
  classical
  set J := q '' stdSimplexBoundary 2 with hJdef
  set Δ := Convexity.StdSimplex.coordinateSet ℝ (Fin 3) with hΔdef
  have hdim3 : Module.finrank ℝ E3 = 2 + 1 := by simp
  have hJD : J ⊆ D := (image_mono fun _ hx => hx.1).trans hq.image_eq.subset
  have hJsph : IsPLSphere 1 J := hq.isPLSphere_image_stdSimplexBoundary (n := 1)
  have hPc : IsClosed P := hP.isPolyhedron.isClosed
  have hE'c : IsClosed E' := (IsPLBall.isPolyhedron ⟨qE', hqE'⟩).isClosed
  have hEc : IsClosed E := (IsPLBall.isPolyhedron ⟨qE, hqE⟩).isClosed
  have hES : E ⊆ frontier P := hEE' ▸ subset_union_left
  have hE'S : E' ⊆ frontier P := hEE' ▸ subset_union_right
  have hSP : frontier P ⊆ P := hPc.frontier_subset
  have hJE : J ⊆ E := fun x hx => (hEE'J ▸ hx : x ∈ E ∩ E').1
  have hJE' : J ⊆ E' := fun x hx => (hEE'J ▸ hx : x ∈ E ∩ E').2
  obtain ⟨ρ, A, -, ε, hρ, hρ0, hAE, hAO, -, -, -, hAD, hAT, hε, -, hchart, hint⟩ :=
    exists_sideCollar hP hV hq hDV hDP hcross hqE hqEJ hEE' hEE'J hE'c hF hFD hO
      (hJD.trans hDO)
  have hDAO : D ∪ A ⊆ O := union_subset hDO hAO
  have hPT : frontier P ⊆ frontier P ∪ frontier V ∪ F := fun x hx => Or.inl (Or.inl hx)
  have hVT : frontier V ⊆ frontier P ∪ frontier V ∪ F := fun x hx => Or.inl (Or.inr hx)
  obtain ⟨Epl, β, prism, b, μ, σ, c, q', hEpl, hβ, hPrc, hPri, hPrO, -, hbm, hbc, hbi, hbβ,
    hσ, hc, hc1, -, hfree, hμc, hμ01, hμ0, hq', hq'J⟩ :=
    exists_wedgeLift hq hρ hρ0 hAD hO hDAO hε hchart hint hPT hVT
  set C := ρ '' (J ×ˢ {(1 / 2 : ℝ)}) with hCdef
  set Ah := ρ '' (J ×ˢ Icc (0 : ℝ) (1 / 2)) with hAhdef
  set L := (fun x => prism (b x, σ * (c * μ x))) '' Epl with hLdef
  set Tm := frontier P ∪ frontier V ∪ F with hTmdef
  have hIsub : J ×ˢ Icc (0 : ℝ) (1 / 2) ⊆ J ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono Subset.rfl (Icc_subset_Icc le_rfl (by norm_num))
  have hρh := hρ.restrict (hJsph.isPolyhedron.prod isHPolytope_Icc.isPolyhedron) hIsub
  have hAhA : Ah ⊆ A := (image_mono hIsub).trans hρ.image_eq.subset
  have hCAh : C ⊆ Ah := image_mono (prod_mono Subset.rfl (by
    rintro t rfl
    exact ⟨by norm_num, le_rfl⟩))
  have hJAh : J ⊆ Ah := fun x hx => ⟨(x, 0), ⟨hx, le_rfl, by norm_num⟩, hρ0 x hx⟩
  have hAhE : Ah ⊆ E := hAhA.trans hAE
  have hAhP : Ah ⊆ P := hAhE.trans (hES.trans hSP)
  have hCJ : Disjoint C J := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ hJ
    have ht' : t = 1 / 2 := ht
    subst ht'
    have h1 : ρ (ρ (x, 1 / 2), 0) = ρ (x, 1 / 2) := hρ0 _ hJ
    have heq := hρ.bijOn.injOn ⟨hJ, le_rfl, zero_le_one⟩ ⟨hx, by norm_num, by norm_num⟩ h1
    have h2 := congrArg Prod.snd heq
    norm_num at h2
  have hCD : Disjoint C D := by
    refine Set.disjoint_left.mpr fun y hyC hyD => ?_
    have hyJ : y ∈ J := hAD.subset ⟨hAhA (hCAh hyC), hyD⟩
    exact Set.disjoint_left.mp hCJ hyC hyJ
  have hAhD : Ah ∩ D = J := by
    apply Subset.antisymm
    · exact (inter_subset_inter_left _ hAhA).trans hAD.subset
    · exact fun x hx => ⟨hJAh hx, hJD hx⟩
  have hAhE' : Ah ∩ E' = qE' '' stdSimplexBoundary 2 := by
    rw [hqE'J]
    apply Subset.antisymm
    · exact (inter_subset_inter_left _ hAhE).trans hEE'J.subset
    · exact fun x hx => ⟨hJAh hx, hJE' hx⟩
  obtain ⟨qh, hqh, hqhJ, -⟩ :=
    hq.exists_isPLHomeomorphOn_union_collar (a := 0) (b := 1 / 2) (by norm_num) hρh hρ0 hAhD
  have hρh' : IsPLHomeomorphOn ρ ((qE' '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) (1 / 2)) Ah := by
    rw [hqE'J]
    exact hρh
  obtain ⟨qhat, hqhat, hqhatJ, -⟩ :=
    hqE'.exists_isPLHomeomorphOn_union_collar (a := 0) (b := 1 / 2) (by norm_num) hρh'
      (by rw [hqE'J]; exact hρ0) hAhE'
  rw [hqE'J] at hqhatJ
  set Ehat := E' ∪ Ah with hEhatdef
  set Bo := closure (frontier P \ Ehat) with hBodef
  have hSph : IsPLSphere 2 (frontier P) := hP.isPLSphere_frontier
  have hEhatS : Ehat ⊆ frontier P := union_subset hE'S (hAhE.trans hES)
  have hBoball : IsPLBall 2 Bo := hSph.isPLBall_closure_sdiff ⟨qhat, hqhat⟩ hEhatS
  obtain ⟨qB, hqB⟩ := hBoball
  have hqBJ := hSph.image_stdSimplexBoundary_complement ⟨qhat, hqhat⟩ hEhatS hqB
  have hEhatBo : Ehat ∩ Bo = C := by
    have h := hSph.inter_closure_sdiff_eq_image_stdSimplexBoundary hqhat hEhatS
    rw [hqhatJ] at h
    exact h
  have hqBC : qB '' stdSimplexBoundary 2 = C := by
    rw [hqBJ, inter_comm]
    exact hEhatBo
  have hBoS : Bo ⊆ frontier P := closure_minimal sdiff_subset isClosed_frontier
  have hBoE : Bo ⊆ E := by
    refine closure_minimal ?_ hEc
    rintro x ⟨hx, hxE⟩
    rw [← hEE'] at hx
    rcases hx with hx | hx
    · exact hx
    · exact (hxE (Or.inl hx)).elim
  have hEBo : E = Bo ∪ Ah := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxA : x ∈ Ah
      · exact Or.inr hxA
      · refine Or.inl (subset_closure ⟨hES hx, ?_⟩)
        rintro (hxE' | hxA')
        · exact hxA (hJAh (hEE'J ▸ ⟨hx, hxE'⟩))
        · exact hxA hxA'
    · exact union_subset hBoE hAhE
  have hCBo : C ⊆ Bo := fun x hx => (hEhatBo ▸ hx : x ∈ Ehat ∩ Bo).2
  have hBoAh : Bo ∩ Ah = C := by
    apply Subset.antisymm
    · rintro x ⟨hxB, hxA⟩
      exact hEhatBo ▸ ⟨Or.inr hxA, hxB⟩
    · exact fun x hx => ⟨hCBo hx, hCAh hx⟩
  have hBoJ : Disjoint Bo J := by
    refine Set.disjoint_left.mpr fun x hxB hxJ => ?_
    have hxC : x ∈ C := hBoAh ▸ ⟨hxB, hJAh hxJ⟩
    exact Set.disjoint_left.mp hCJ hxC hxJ
  have hBoP : Bo ⊆ P := hBoS.trans hSP
  have hL : IsPLBall 2 L := ⟨q', hq'⟩
  have hCL : C ⊆ L := by
    rw [← hq'J, ← hq'.image_eq]
    exact image_mono fun _ hx => hx.1
  have hlift : ∀ x ∈ Epl, 0 < μ x → prism (b x, σ * (c * μ x)) ∉ Tm ∧
      prism (b x, σ * (c * μ x)) ∉ P ∧ (prism (b x, σ * (c * μ x)) ∈ V ↔ ε = -1) := by
    intro x hx hμ
    refine hfree x hx (c * μ x) ⟨mul_pos hc hμ, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_left (hμ01 x hx).2 hc.le]
  have hLC : ∀ y ∈ L, y ∈ Tm ∨ y ∈ P → y ∈ C := by
    rintro _ ⟨x, hx, rfl⟩ hy
    change prism (b x, σ * (c * μ x)) ∈ C
    rcases (hμ01 x hx).1.lt_or_eq with hμ | hμ
    · rcases hy with hy | hy
      · exact absurd hy (hlift x hx hμ).1
      · exact absurd hy (hlift x hx hμ).2.1
    · have h0 : prism (b x, σ * (c * μ x)) = β x := by
        rw [← hμ, mul_zero, mul_zero, hbβ x hx]
      rw [h0]
      exact (hμ0 x hx).mp hμ.symm
  have hCP : C ⊆ P := hCAh.trans hAhP
  have hLP : L ∩ P = C := Subset.antisymm (fun y hy => hLC y hy.1 (Or.inr hy.2))
    fun y hy => ⟨hCL hy, hCP hy⟩
  have hLBo : L ∩ Bo = C := Subset.antisymm
    (fun y hy => hLP ▸ ⟨hy.1, hBoP hy.2⟩) fun y hy => ⟨hCL hy, hCBo hy⟩
  have hLD : Disjoint L D := by
    refine Set.disjoint_left.mpr fun y hyL hyD => ?_
    have hyC := hLC y hyL (Or.inl (Or.inl (Or.inr (hDV hyD))))
    exact Set.disjoint_left.mp hCD hyC hyD
  have hLVF : Disjoint L (frontier V ∪ F) := by
    refine Set.disjoint_left.mpr fun y hyL hyVF => ?_
    have hyC : y ∈ C := by
      refine hLC y hyL (Or.inl ?_)
      rcases hyVF with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    have hyJ := hAT ⟨hAhA (hCAh hyC), hyVF⟩
    exact Set.disjoint_left.mp hCJ hyC hyJ
  have hLV : ∀ y ∈ L, y ∉ C → (y ∈ V ↔ ε = -1) := by
    rintro _ ⟨x, hx, rfl⟩ hyC
    change prism (b x, σ * (c * μ x)) ∈ V ↔ ε = -1
    rcases (hμ01 x hx).1.lt_or_eq with hμ | hμ
    · exact (hlift x hx hμ).2.2
    · refine absurd ?_ hyC
      change prism (b x, σ * (c * μ x)) ∈ C
      have h0 : prism (b x, σ * (c * μ x)) = β x := by
        rw [← hμ, mul_zero, mul_zero, hbβ x hx]
      rw [h0]
      exact (hμ0 x hx).mp hμ.symm
  have hSo : IsPLSphere 2 (L ∪ Bo) :=
    isPLSphere_union_of_inter_eq_image_stdSimplexBoundary hq' hqB (by rw [hq'J]; exact hLBo)
      (by rw [hqBC, hq'J])
  obtain ⟨f, hf⟩ := hEpl
  have hffr : f '' stdSimplexBoundary 2 = frontier Epl :=
    hf.image_stdSimplexBoundary_eq_frontier (n := 1)
  have hqhC : qh '' stdSimplexBoundary 2 = C := hqhJ
  have hβfr : β '' frontier Epl = C := by
    rw [← hffr, image_image, ← hqhC]
    exact (hf.trans hβ).image_stdSimplexBoundary_congr (m := 1) hqh
  have hEplc : IsClosed Epl := (IsPLBall.isPolyhedron ⟨f, hf⟩).isClosed
  have hEplcomp : IsCompact Epl := (IsPLBall.isPolyhedron ⟨f, hf⟩).isCompact
  have hμfr : ∀ x ∈ frontier Epl, μ x = 0 := fun x hx =>
    (hμ0 x (hEplc.frontier_subset hx)).mpr (hβfr ▸ mem_image_of_mem β hx)
  have hμpos : ∀ x ∈ interior Epl, 0 < μ x := by
    intro x hx
    refine lt_of_le_of_ne (hμ01 x (interior_subset hx)).1 fun h => ?_
    have hC : β x ∈ C := (hμ0 x (interior_subset hx)).mp h.symm
    rw [← hβfr] at hC
    obtain ⟨x', hx', hxx'⟩ := hC
    have := hβ.bijOn.injOn (hEplc.frontier_subset hx') (interior_subset hx) hxx'
    exact hx'.2 (by rw [this]; exact hx)
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  set G : EuclideanSpace ℝ (Fin 2) × ℝ → E3 := fun z => prism (b z.1, σ * z.2) with hGdef
  have hGmaps : MapsTo (fun z : EuclideanSpace ℝ (Fin 2) × ℝ => (b z.1, σ * z.2))
      (Epl ×ˢ Icc (-1 : ℝ) 1) (Δ ×ˢ Icc (-1 : ℝ) 1) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    refine ⟨hbm hx, ?_⟩
    rcases hσ with h | h <;> rw [h] <;> constructor <;> linarith [ht.1, ht.2]
  have hGc : ContinuousOn G (Epl ×ˢ Icc (-1 : ℝ) 1) :=
    hPrc.comp ((hbc.comp continuous_fst.continuousOn fun w hw => hw.1).prodMk
      (continuous_const.mul continuous_snd).continuousOn) hGmaps
  have hGi : InjOn G (Epl ×ˢ Icc (-1 : ℝ) 1) := by
    intro z hz z' hz' h
    have h1 := hPri (hGmaps hz) (hGmaps hz') h
    have h2 := congrArg Prod.fst h1
    have h3 := congrArg Prod.snd h1
    simp only at h2 h3
    exact Prod.ext (hbi hz.1 hz'.1 h2) (mul_left_cancel₀ hσ0 h3)
  set K : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    (Epl ×ˢ Icc (0 : ℝ) 1) ∩ (fun z => c * μ z.1 - z.2) ⁻¹' Ici 0 with hKdef
  set K₀ : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    (interior Epl ×ˢ Ioi (0 : ℝ)) ∩ (fun z => c * μ z.1 - z.2) ⁻¹' Ioi 0 with hK₀def
  have hKsub : K ⊆ Epl ×ˢ Icc (-1 : ℝ) 1 := fun z hz =>
    ⟨hz.1.1, by linarith [hz.1.2.1], hz.1.2.2⟩
  have hK₀K : K₀ ⊆ K := by
    rintro z ⟨⟨hz1, hz2⟩, hz3⟩
    have hz2' : 0 < z.2 := hz2
    have hz3' : 0 < c * μ z.1 - z.2 := hz3
    have hμ1 := (hμ01 z.1 (interior_subset hz1)).2
    refine ⟨⟨interior_subset hz1, hz2'.le, ?_⟩, show 0 ≤ c * μ z.1 - z.2 by linarith⟩
    nlinarith [mul_le_mul_of_nonneg_left hμ1 hc.le]
  have hfμ : ContinuousOn (fun z : EuclideanSpace ℝ (Fin 2) × ℝ => c * μ z.1 - z.2)
      (Epl ×ˢ univ) :=
    (continuousOn_const.mul (hμc.comp continuous_fst.continuousOn fun w hw => hw.1)).sub
      continuous_snd.continuousOn
  have hKc : IsCompact K := by
    refine (hEplcomp.prod isCompact_Icc).of_isClosed_subset ?_ inter_subset_left
    exact (hfμ.mono (prod_mono Subset.rfl (subset_univ _))).preimage_isClosed_of_isClosed
      (hEplc.prod isClosed_Icc) isClosed_Ici
  have hK₀o : IsOpen K₀ :=
    (hfμ.mono (prod_mono interior_subset (subset_univ _))).isOpen_inter_preimage
      (isOpen_interior.prod isOpen_Ioi) isOpen_Ioi
  set T := G '' K with hTdef
  have hTc : IsCompact T := hKc.image_of_continuousOn (hGc.mono hKsub)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = Module.finrank ℝ E3 := by
    simp [Module.finrank_prod]
  have hGK₀ : IsOpen (G '' K₀) :=
    invariance_of_domain_isOpen_image_of_finrank_eq hdim hK₀o (hGc.mono (hK₀K.trans hKsub))
      (hGi.mono (hK₀K.trans hKsub))
  have hGK₀T : G '' K₀ ⊆ interior T := interior_maximal (image_mono hK₀K) hGK₀
  have hG0 : ∀ x ∈ Epl, G (x, 0) = β x := fun x hx => by
    change prism (b x, σ * 0) = β x
    rw [mul_zero]
    exact hbβ x hx
  have hβBh : ∀ x ∈ Epl, β x ∈ D ∪ Ah := fun x hx => hβ.bijOn.mapsTo hx
  have hfrT : frontier T ⊆ D ∪ Ah ∪ L := by
    intro y hy
    obtain ⟨⟨x, t⟩, hz, rfl⟩ := hTc.isClosed.frontier_subset hy
    have hx : x ∈ Epl := hz.1.1
    have ht0 : 0 ≤ t := hz.1.2.1
    have ht1 : 0 ≤ c * μ x - t := hz.2
    have hnot : (x, t) ∉ K₀ := fun h => hy.2 (hGK₀T ⟨(x, t), h, rfl⟩)
    by_cases hxi : x ∈ interior Epl
    · rcases ht0.lt_or_eq with ht | ht
      · have htc : t = c * μ x := by
          by_contra hne
          exact hnot ⟨⟨hxi, ht⟩, show 0 < c * μ x - t by
            rcases (sub_nonneg.mp ht1).lt_or_eq with h | h
            · linarith
            · exact absurd h hne⟩
        exact Or.inr ⟨x, hx, by rw [htc]⟩
      · rw [← ht, hG0 x hx]
        exact Or.inl (hβBh x hx)
    · have hxf : x ∈ frontier Epl := ⟨subset_closure hx, hxi⟩
      have ht' : t = 0 := by
        have := hμfr x hxf
        rw [this, mul_zero] at ht1
        linarith
      rw [ht', hG0 x hx]
      exact Or.inl (hβBh x hx)
  have hBhL : (D ∪ Ah) ∩ L = C := by
    apply Subset.antisymm
    · rintro y ⟨hyB, hyL⟩
      refine hLC y hyL (Or.inl (Or.inl ?_))
      rcases hyB with h | h
      · exact Or.inr (hDV h)
      · exact Or.inl (hES (hAhE h))
    · exact fun y hy => ⟨Or.inr (hCAh hy), hCL hy⟩
  have hSig : IsPLSphere 2 (D ∪ Ah ∪ L) :=
    isPLSphere_union_of_inter_eq_image_stdSimplexBoundary hqh hq' (by rw [hqhJ]; exact hBhL)
      (by rw [hq'J, hqhJ])
  obtain ⟨Sl, hSl, hSlf, -⟩ := hSig.exists_isPLBall_frontier_eq
  have hSlc : IsClosed Sl := hSl.isPolyhedron.isClosed
  have hTSl : T ⊆ Sl :=
    hSl.subset_of_isCompact_frontier_subset hTc
      (hfrT.trans (by rw [← hSlf]; exact hSlc.frontier_subset))
  obtain ⟨x₀, hx₀⟩ := IsPLBall.interior_nonempty (n := 1) ⟨f, hf⟩
  have hμx₀ := hμpos x₀ hx₀
  have hK₀ne : (x₀, c * μ x₀ / 2) ∈ K₀ :=
    ⟨⟨hx₀, show (0 : ℝ) < c * μ x₀ / 2 by have := mul_pos hc hμx₀; linarith⟩,
      show (0 : ℝ) < c * μ x₀ - c * μ x₀ / 2 by have := mul_pos hc hμx₀; linarith⟩
  have hSlT : Sl ⊆ T := by
    refine hSl.subset_of_disjoint_interior_frontier hTc.isClosed
      (disjoint_interior_frontier.mono_right (hfrT.trans hSlf.symm.subset)) ?_
    exact ⟨G (x₀, c * μ x₀ / 2), interior_mono hTSl (hGK₀T ⟨_, hK₀ne, rfl⟩),
      interior_subset (hGK₀T ⟨_, hK₀ne, rfl⟩)⟩
  have hTeq : T = Sl := Subset.antisymm hTSl hSlT
  have hTball : IsPLBall 3 T := by rw [hTeq]; exact hSl
  have hTfr : frontier T = D ∪ Ah ∪ L := by rw [hTeq]; exact hSlf
  have hGfree : ∀ z ∈ K, 0 < z.2 → G z ∉ Tm ∧ G z ∉ P ∧ (G z ∈ V ↔ ε = -1) := by
    rintro ⟨x, t⟩ hz ht
    have hμ1 := (hμ01 x hz.1.1).2
    have ht1 : t ≤ c * μ x := by linarith [show 0 ≤ c * μ x - t from hz.2]
    exact hfree x hz.1.1 t ⟨ht, by nlinarith [mul_le_mul_of_nonneg_left hμ1 hc.le]⟩
  have hTP : T ∩ P = Ah := by
    apply Subset.antisymm
    · rintro _ ⟨⟨⟨x, t⟩, hz, rfl⟩, hyP⟩
      have ht0 : (0 : ℝ) ≤ t := hz.1.2.1
      rcases ht0.lt_or_eq with ht | ht
      · exact absurd hyP (hGfree _ hz ht).2.1
      · have hG : G (x, t) = β x := by rw [← ht]; exact hG0 x hz.1.1
        rw [hG] at hyP ⊢
        rcases hβBh x hz.1.1 with h | h
        · exact hJAh (hDP ▸ ⟨h, hyP⟩)
        · exact h
    · intro y hy
      refine ⟨hTc.isClosed.frontier_subset ?_, hAhP hy⟩
      rw [hTfr]
      exact Or.inl (Or.inr hy)
  have hTO : T ⊆ O := by
    rintro _ ⟨z, hz, rfl⟩
    exact hPrO ⟨_, hGmaps (hKsub hz), rfl⟩
  have hintT : ∀ y ∈ interior T, ∃ z ∈ K, 0 < z.2 ∧ G z = y := by
    intro y hy
    obtain ⟨⟨x, t⟩, hz, rfl⟩ := interior_subset hy
    refine ⟨(x, t), hz, ?_, rfl⟩
    have ht0 : (0 : ℝ) ≤ t := hz.1.2.1
    rcases ht0.lt_or_eq with ht | ht
    · exact ht
    · exfalso
      have hfr : G (x, t) ∈ frontier T := by
        rw [hTfr, ← ht, hG0 x hz.1.1]
        exact Or.inl (hβBh x hz.1.1)
      exact hfr.2 hy
  have hTV : ∀ y ∈ interior T, y ∈ V ↔ ε = -1 := by
    intro y hy
    obtain ⟨z, hz, ht, rfl⟩ := hintT y hy
    exact (hGfree z hz ht).2.2
  have hDAhT : D ∪ Ah ⊆ frontier T := fun y hy => hTfr ▸ Or.inl hy
  have hintTDE : Disjoint (interior T) (D ∪ E) := by
    refine Set.disjoint_left.mpr fun y hyi hy => ?_
    rcases hy with hyD | hyE
    · exact (hDAhT (Or.inl hyD)).2 hyi
    · have hyAh : y ∈ Ah := hTP ▸ ⟨interior_subset hyi, hSP (hES hyE)⟩
      exact (hDAhT (Or.inr hyAh)).2 hyi
  set K₂ : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    (Epl ×ˢ Icc (0 : ℝ) 1) ∩ (fun z => 2 * (c * μ z.1) - z.2) ⁻¹' Ici 0 with hK₂def
  set R₀ : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    (interior Epl ×ˢ Ioi (0 : ℝ)) ∩ (fun z => 2 * (c * μ z.1) - z.2) ⁻¹' Ioi 0 with hR₀def
  have hcμle : ∀ x ∈ Epl, c * μ x ≤ c := fun x hx => by
    nlinarith [mul_le_mul_of_nonneg_left (hμ01 x hx).2 hc.le]
  have hcμ0 : ∀ x ∈ Epl, 0 ≤ c * μ x := fun x hx => mul_nonneg hc.le (hμ01 x hx).1
  have hK₂sub : K₂ ⊆ Epl ×ˢ Icc (-1 : ℝ) 1 := fun z hz =>
    ⟨hz.1.1, by linarith [hz.1.2.1], hz.1.2.2⟩
  have hR₀K₂ : R₀ ⊆ K₂ := by
    rintro z ⟨⟨hz1, hz2⟩, hz3⟩
    have hz2' : 0 < z.2 := hz2
    have hz3' : 0 < 2 * (c * μ z.1) - z.2 := hz3
    have := hcμle z.1 (interior_subset hz1)
    exact ⟨⟨interior_subset hz1, hz2'.le, by linarith⟩,
      show 0 ≤ 2 * (c * μ z.1) - z.2 by linarith⟩
  have hfμ2 : ContinuousOn (fun z : EuclideanSpace ℝ (Fin 2) × ℝ => 2 * (c * μ z.1) - z.2)
      (Epl ×ˢ univ) :=
    (continuousOn_const.mul (continuousOn_const.mul
      (hμc.comp continuous_fst.continuousOn fun w hw => hw.1))).sub continuous_snd.continuousOn
  have hK₂c : IsCompact K₂ := by
    refine (hEplcomp.prod isCompact_Icc).of_isClosed_subset ?_ inter_subset_left
    exact (hfμ2.mono (prod_mono Subset.rfl (subset_univ _))).preimage_isClosed_of_isClosed
      (hEplc.prod isClosed_Icc) isClosed_Ici
  have hR₀o : IsOpen R₀ :=
    (hfμ2.mono (prod_mono interior_subset (subset_univ _))).isOpen_inter_preimage
      (isOpen_interior.prod isOpen_Ioi) isOpen_Ioi
  set R := G '' R₀ with hRdef
  set Lr := (fun x => G (x, 2 * (c * μ x))) '' Epl with hLrdef
  have hRo : IsOpen R :=
    invariance_of_domain_isOpen_image_of_finrank_eq hdim hR₀o (hGc.mono (hR₀K₂.trans hK₂sub))
      (hGi.mono (hR₀K₂.trans hK₂sub))
  have hGO : ∀ z ∈ Epl ×ˢ Icc (-1 : ℝ) 1, G z ∈ O := fun z hz => hPrO ⟨_, hGmaps hz, rfl⟩
  have hRO : R ⊆ O := by
    rintro _ ⟨z, hz, rfl⟩
    exact hGO z (hK₂sub (hR₀K₂ hz))
  have hLrK₂ : ∀ x ∈ Epl, (x, 2 * (c * μ x)) ∈ K₂ := fun x hx =>
    ⟨⟨hx, by linarith [hcμ0 x hx], by linarith [hcμle x hx]⟩,
      show (0 : ℝ) ≤ 2 * (c * μ x) - 2 * (c * μ x) by linarith⟩
  have hLrO : Lr ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    exact hGO _ (hK₂sub (hLrK₂ x hx))
  have hTR : T ⊆ R ∪ (D ∪ Ah) := by
    rintro _ ⟨⟨x, t⟩, hz, rfl⟩
    have ht0 : (0 : ℝ) ≤ t := hz.1.2.1
    have ht1 : 0 ≤ c * μ x - t := hz.2
    rcases ht0.lt_or_eq with ht | ht
    · have hxi : x ∈ interior Epl := by
        by_contra hxi
        have hμ := hμfr x ⟨subset_closure hz.1.1, hxi⟩
        rw [hμ, mul_zero] at ht1
        linarith
      have hμp := mul_pos hc (hμpos x hxi)
      exact Or.inl ⟨(x, t), ⟨⟨hxi, ht⟩, show 0 < 2 * (c * μ x) - t by linarith⟩, rfl⟩
    · refine Or.inr ?_
      rw [← ht, hG0 x hz.1.1]
      exact hβBh x hz.1.1
  have hclR : closure R ⊆ R ∪ (D ∪ Ah) ∪ Lr := by
    have hK₂T : IsCompact (G '' K₂) := hK₂c.image_of_continuousOn (hGc.mono hK₂sub)
    have hsub : closure R ⊆ G '' K₂ := closure_minimal (image_mono hR₀K₂) hK₂T.isClosed
    intro y hy
    obtain ⟨⟨x, t⟩, hz, rfl⟩ := hsub hy
    have hx : x ∈ Epl := hz.1.1
    have ht0 : (0 : ℝ) ≤ t := hz.1.2.1
    have ht1 : 0 ≤ 2 * (c * μ x) - t := hz.2
    by_cases hR : (x, t) ∈ R₀
    · exact Or.inl (Or.inl ⟨_, hR, rfl⟩)
    by_cases htz : t = 0
    · refine Or.inl (Or.inr ?_)
      rw [htz, hG0 x hx]
      exact hβBh x hx
    by_cases htt : t = 2 * (c * μ x)
    · exact Or.inr ⟨x, hx, by rw [htt]⟩
    exfalso
    have ht0' : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htz)
    have ht1' : 0 < 2 * (c * μ x) - t := lt_of_le_of_ne ht1 (fun h => htt (by linarith))
    refine hR ⟨⟨?_, ht0'⟩, ht1'⟩
    by_contra hxi
    have hμ := hμfr x ⟨subset_closure hx, hxi⟩
    rw [hμ] at ht1'
    linarith
  set Ginv := Function.invFunOn G K₂ with hGinvdef
  have hGiK₂ : InjOn G K₂ := hGi.mono hK₂sub
  have hGinvc : ContinuousOn Ginv (G '' K₂) :=
    continuousOn_invFunOn_image_of_isCompact hK₂c (hGc.mono hK₂sub) hGiK₂
  have hGinv : ∀ z ∈ K₂, Ginv (G z) = z := fun z hz => hGiK₂.leftInvOn_invFunOn hz
  have hGinvm : MapsTo Ginv (G '' K₂) K₂ := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hGinv z hz]
    exact hz
  set ψ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2) × ℝ :=
    fun z => (z.1, c * μ z.1 + z.2 / 2) with hψdef
  have hψc : ContinuousOn ψ K₂ :=
    continuous_fst.continuousOn.prodMk ((continuousOn_const.mul
      (hμc.comp continuous_fst.continuousOn fun w hw => hw.1.1)).add
      (continuous_snd.continuousOn.div_const 2))
  have hψm : MapsTo ψ K₂ K₂ := by
    rintro ⟨x, t⟩ hz
    have hx : x ∈ Epl := hz.1.1
    have ht0 : (0 : ℝ) ≤ t := hz.1.2.1
    have ht1 : 0 ≤ 2 * (c * μ x) - t := hz.2
    have h1 := hcμ0 x hx
    have h2 := hcμle x hx
    exact ⟨⟨hx, show 0 ≤ c * μ x + t / 2 by linarith, show c * μ x + t / 2 ≤ 1 by linarith⟩,
      show 0 ≤ 2 * (c * μ x) - (c * μ x + t / 2) by linarith⟩
  set g : E3 → E3 := fun y => G (ψ (Ginv y)) with hgdef
  have hgc' : ContinuousOn g (G '' K₂) :=
    (hGc.mono hK₂sub).comp (hψc.comp hGinvc hGinvm) (hψm.comp hGinvm)
  have hRK₂ : R ⊆ G '' K₂ := image_mono hR₀K₂
  have hLrK : Lr ⊆ G '' K₂ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, hLrK₂ x hx, rfl⟩
  have hgc : ContinuousOn g (R ∪ Lr) := hgc'.mono (union_subset hRK₂ hLrK)
  have hgLr : ∀ y ∈ Lr, g y = y := by
    rintro _ ⟨x, hx, rfl⟩
    change G (ψ (Ginv (G (x, 2 * (c * μ x))))) = G (x, 2 * (c * μ x))
    rw [hGinv _ (hLrK₂ x hx)]
    change G (x, c * μ x + 2 * (c * μ x) / 2) = G (x, 2 * (c * μ x))
    congr 2
    ring
  have hgR : MapsTo g R R := by
    rintro _ ⟨⟨x, t⟩, hz, rfl⟩
    refine ⟨ψ (x, t), ?_, ?_⟩
    · obtain ⟨⟨hx, ht⟩, ht2⟩ := hz
      have ht' : 0 < t := ht
      have ht2' : 0 < 2 * (c * μ x) - t := ht2
      have h1 := hcμ0 x (interior_subset hx)
      exact ⟨⟨hx, show 0 < c * μ x + t / 2 by linarith⟩,
        show 0 < 2 * (c * μ x) - (c * μ x + t / 2) by linarith⟩
    · change G (ψ (x, t)) = G (ψ (Ginv (G (x, t))))
      rw [hGinv _ (hR₀K₂ hz)]
  have hgT : ∀ y ∈ R, g y ∉ T := by
    rintro _ ⟨⟨x, t⟩, hz, rfl⟩ ⟨⟨x', t'⟩, hz', heq⟩
    change G (x', t') = G (ψ (Ginv (G (x, t)))) at heq
    rw [hGinv _ (hR₀K₂ hz)] at heq
    have h := hGi (hKsub hz') (hK₂sub (hψm (hR₀K₂ hz))) heq
    have h' : (x', t') = (x, c * μ x + t / 2) := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
    have ht' : 0 < t := hz.1.2
    have ht1 : 0 ≤ c * μ x' - (c * μ x' + t / 2) := hz'.2
    linarith
  have hRfree : ∀ y ∈ R, y ∉ Tm ∧ y ∉ P ∧ (y ∈ V ↔ ε = -1) := by
    rintro _ ⟨⟨x, t⟩, ⟨⟨hx, ht⟩, ht2⟩, rfl⟩
    have ht' : 0 < t := ht
    have ht2' : 0 < 2 * (c * μ x) - t := ht2
    have := hcμle x (interior_subset hx)
    exact hfree x (interior_subset hx) t ⟨ht', by linarith⟩
  have hRP : Disjoint R P := Set.disjoint_left.mpr fun y hy => (hRfree y hy).2.1
  have hRVF : Disjoint R (frontier V ∪ F) := by
    refine Set.disjoint_left.mpr fun y hy hyVF => (hRfree y hy).1 ?_
    rcases hyVF with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hRV : ∀ y ∈ R, y ∈ V ↔ ε = -1 := fun y hy => (hRfree y hy).2.2
  have hRDE : Disjoint R (D ∪ E) := by
    refine Set.disjoint_left.mpr fun y hy hyDE => ?_
    rcases hyDE with h | h
    · exact (hRfree y hy).1 (Or.inl (Or.inr (hDV h)))
    · exact (hRfree y hy).2.1 (hSP (hES h))
  have hRc : IsPreconnected R := by
    have heq : R₀ = (fun z : EuclideanSpace ℝ (Fin 2) × ℝ => (z.1, z.2 * (2 * (c * μ z.1)))) ''
        (interior Epl ×ˢ Ioo (0 : ℝ) 1) := by
      ext ⟨x, t⟩
      constructor
      · rintro ⟨⟨hx, ht⟩, ht2⟩
        have ht' : 0 < t := ht
        have ht2' : 0 < 2 * (c * μ x) - t := ht2
        have hpos : 0 < 2 * (c * μ x) := by linarith
        refine ⟨(x, t / (2 * (c * μ x))), ⟨hx, div_pos ht' hpos,
          (div_lt_one hpos).mpr (by linarith)⟩, ?_⟩
        change (x, t / (2 * (c * μ x)) * (2 * (c * μ x))) = (x, t)
        rw [div_mul_cancel₀ _ hpos.ne']
      · rintro ⟨⟨x', s'⟩, ⟨hx', hs0, hs1⟩, heq⟩
        have h' : (x', s' * (2 * (c * μ x'))) = (x, t) := heq
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
        have hpos : 0 < 2 * (c * μ x') := by
          have := mul_pos hc (hμpos x' hx')
          linarith
        refine ⟨⟨hx', show 0 < s' * (2 * (c * μ x')) from mul_pos hs0 hpos⟩, ?_⟩
        change 0 < 2 * (c * μ x') - s' * (2 * (c * μ x'))
        nlinarith [mul_pos (sub_pos.mpr hs1) hpos]
    have hR₀c : IsPreconnected R₀ := by
      rw [heq]
      refine ((IsPLBall.isConnected_interior_of_finrank (n := 1) (by simp)
        ⟨f, hf⟩).isPreconnected.prod isPreconnected_Ioo).image _ ?_
      exact continuous_fst.continuousOn.prodMk (continuous_snd.continuousOn.mul
        (continuousOn_const.mul (continuousOn_const.mul
          (hμc.comp continuous_fst.continuousOn fun w hw => interior_subset hw.1))))
    exact hR₀c.image G (hGc.mono (hR₀K₂.trans hK₂sub))
  have hY3 : ∀ Y : Set E3, IsPLBall 3 Y → frontier Y = D ∪ E →
      (Disjoint (interior P) Y → interior T ⊆ interior Y) ∧
      (interior P ⊆ Y → Disjoint (interior T) Y) ∧ (Disjoint (interior P) Y → R ⊆ interior Y) ∧
      (interior P ⊆ Y → Disjoint R Y) := by
    intro Y hY hYf
    obtain ⟨p, hp⟩ := hJsph.nonempty
    obtain ⟨U, φ, r, hU, hpU, hr, hφ, hφp, hloc⟩ := hchart p hp
    have hpBo : p ∉ Bo := fun h => Set.disjoint_left.mp hBoJ h hp
    have hopen : IsOpen (φ '' (U ∩ Boᶜ)) :=
      hφ.isOpen_image_of_isOpen Metric.isOpen_ball (hU.inter isClosed_closure.isOpen_compl)
        inter_subset_left
    have h0 : (0 : ℝ × ℝ × ℝ) ∈ φ '' (U ∩ Boᶜ) := ⟨p, ⟨hpU, hpBo⟩, hφp⟩
    obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
    have hr' : 0 < min r₁ r := lt_min hr₁ hr
    obtain ⟨hU₂, hφ₂⟩ := hφ.restrict_ball hU (min_le_right r₁ r)
    set U₂ := U ∩ φ ⁻¹' Metric.ball 0 (min r₁ r) with hU₂def
    have hU₂Bo : ∀ y ∈ U₂, y ∉ Bo := by
      intro y hy
      obtain ⟨y', ⟨hy'U, hy'B⟩, hy'y⟩ := hball (Metric.ball_subset_ball (min_le_left r₁ r) hy.2)
      rw [hφ.bijOn.injOn hy'U hy.1 hy'y] at hy'B
      exact hy'B
    have hpU₂ : p ∈ U₂ := ⟨hpU, by rw [mem_preimage, hφp]; exact Metric.mem_ball_self hr'⟩
    have hYU : ∀ y ∈ U₂, y ∈ frontier Y ↔
        ((φ y).2.2 = 0 ∧ (φ y).2.1 ≤ 0) ∨ ((φ y).2.1 = 0 ∧ 0 ≤ ε * (φ y).2.2) := by
      intro y hy
      rw [← (hloc y hy.1).1, hYf]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · rw [hEBo] at h
          rcases h with h | h
          · exact absurd h (hU₂Bo y hy)
          · exact Or.inr (hAhA h)
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (hAE h)
    have hPU : ∀ y ∈ U₂, 0 < (φ y).2.1 → y ∈ interior P := by
      have hopenP : IsOpen (U₂ ∩ φ ⁻¹' {z : ℝ × ℝ × ℝ | 0 < z.2.1}) :=
        hφ₂.isPiecewiseAffineOn.continuousOn.isOpen_inter_preimage hU₂
          (isOpen_lt continuous_const (continuous_fst.comp continuous_snd))
      intro y hy hv
      refine interior_maximal (fun w hw => ?_) hopenP ⟨hy, hv⟩
      exact ((hloc w hw.1.1).2.2.1).mpr (le_of_lt hw.2)
    obtain ⟨hpocket, hbig⟩ :=
      bentSide_of_chart (P := P) hU₂ hpU₂ hr' hφ₂ hφp hε hY hYU hPU
    have hpBh : p ∈ D ∪ Ah := Or.inl (hJD hp)
    obtain ⟨xp, hxp, hxpp⟩ := hβ.bijOn.surjOn hpBh
    have hxpi : xp ∈ interior Epl := by
      by_contra hni
      have hC : β xp ∈ C := hβfr ▸ mem_image_of_mem β ⟨subset_closure hxp, hni⟩
      rw [hxpp] at hC
      exact Set.disjoint_left.mp hCJ hC hp
    have hμxp := hμpos xp hxpi
    have hfc : ContinuousAt (fun t : ℝ => G (xp, t)) 0 := by
      have hcon : ContinuousOn (fun t : ℝ => G (xp, t)) (Icc (-1 : ℝ) 1) :=
        hGc.comp (continuousOn_const.prodMk continuousOn_id) fun t ht => ⟨hxp, ht⟩
      exact hcon.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
    have hf0 : G (xp, 0) = p := by rw [hG0 xp hxp, hxpp]
    have hpre : (fun t : ℝ => G (xp, t)) ⁻¹' U₂ ∈ 𝓝 (0 : ℝ) := by
      apply hfc.preimage_mem_nhds
      rw [hf0]
      exact hU₂.mem_nhds hpU₂
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hpre
    set t₁ := min (δ / 2) (c * μ xp / 2) with ht₁def
    have hcμ : 0 < c * μ xp := mul_pos hc hμxp
    have ht₁ : 0 < t₁ := lt_min (by linarith) (by linarith)
    have ht₁δ : t₁ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have ht₁c : t₁ < c * μ xp := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hzK₀ : (xp, t₁) ∈ K₀ := ⟨⟨hxpi, ht₁⟩, show 0 < c * μ xp - t₁ by linarith⟩
    have hy₁T : G (xp, t₁) ∈ interior T := hGK₀T ⟨_, hzK₀, rfl⟩
    have hy₁U : G (xp, t₁) ∈ U₂ := hδU (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht₁]
      exact ht₁δ)
    obtain ⟨hy₁Tm, hy₁P, hy₁V⟩ := hGfree _ (hK₀K hzK₀) ht₁
    obtain ⟨-, hlT, hlP, hlV⟩ := hloc _ hy₁U.1
    have hv : (φ (G (xp, t₁))).2.1 < 0 := by
      by_contra h
      exact hy₁P (hlP.mpr (not_lt.mp h))
    have hw0 : (φ (G (xp, t₁))).2.2 ≠ 0 := fun h => hy₁Tm (hlT.mpr (Or.inr h))
    have hw : 0 < ε * (φ (G (xp, t₁))).2.2 := by
      rcases hε with h | h
      · rw [h, one_mul]
        refine lt_of_le_of_ne ?_ (Ne.symm hw0)
        by_contra hneg
        have := hy₁V.mp (hlV.mpr (le_of_lt (not_le.mp hneg)))
        rw [h] at this
        norm_num at this
      · rw [h, neg_one_mul, neg_pos]
        exact lt_of_le_of_ne (hlV.mp (hy₁V.mpr h)) hw0
    have hTconn : IsPreconnected (interior T) :=
      (hTball.isConnected_interior_of_finrank hdim3).isPreconnected
    have hYc : IsClosed Y := hY.isPolyhedron.isClosed
    have hy₁R : G (xp, t₁) ∈ R := ⟨(xp, t₁), ⟨⟨hxpi, ht₁⟩, show 0 < 2 * (c * μ xp) - t₁ by
      linarith⟩, rfl⟩
    refine ⟨fun hdis => ?_, fun hsub => ?_, fun hdis => ?_, fun hsub => ?_⟩
    · have hy₁Y := hpocket hdis _ hy₁U hv hw
      exact subset_interior_of_isPreconnected_of_disjoint_frontier hTconn (hYf ▸ hintTDE)
        ⟨_, hy₁T, hy₁Y⟩
    · have hy₁Y := hbig hsub _ hy₁U hv hw
      rcases subset_interior_or_subset_compl_of_disjoint_frontier hYc hTconn (hYf ▸ hintTDE)
        with h | h
      · exact absurd (interior_subset (h hy₁T)) hy₁Y
      · exact Set.disjoint_left.mpr fun y hy hyY => h hy hyY
    · have hy₁Y := hpocket hdis _ hy₁U hv hw
      exact subset_interior_of_isPreconnected_of_disjoint_frontier hRc (hYf ▸ hRDE)
        ⟨_, hy₁R, hy₁Y⟩
    · have hy₁Y := hbig hsub _ hy₁U hv hw
      rcases subset_interior_or_subset_compl_of_disjoint_frontier hYc hRc (hYf ▸ hRDE)
        with h | h
      · exact absurd (interior_subset (h hy₁R)) hy₁Y
      · exact Set.disjoint_left.mpr fun y hy hyY => h hy hyY
  refine ⟨L, Bo, Ah, C, T, ε, hL, ⟨qh, hqh⟩, hSo, hTball, hTfr, hEBo, hLBo, hBoAh, hLP,
    ⟨qB, hqB, hqBC⟩, hBoJ, hLD, hTP, hTO, fun y hy => hAT ⟨hAhA hy.1, hy.2⟩, hLVF, hε, hTV,
    hLV, fun Y hY hYf => ⟨(hY3 Y hY hYf).1, (hY3 Y hY hYf).2.1⟩, R, Lr, g, hRo, hRO, hLrO,
    hTR, hclR, hgc, hgLr, hgR, hgT, hRP, hRVF, hRV, fun Y hY hYf => (hY3 Y hY hYf).2.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear

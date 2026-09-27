/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingBlock
import DifferentialGeometry.Topology.PiecewiseLinear.PieceRestrict
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import DifferentialGeometry.Topology.PiecewiseLinear.Product

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section PL

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem IsPLHomeomorphOn.inter_preimage_of_isPolyhedron [FiniteDimensional ℝ E] {p : E → F}
    {s : Set E} (h : IsPLHomeomorphOn p s (p '' s)) {P : Set F} (hP : IsPolyhedron P) :
    IsPLHomeomorphOn p (s ∩ p ⁻¹' P) (p '' (s ∩ p ⁻¹' P)) := by
  have hinj : InjOn p (s ∩ p ⁻¹' P) := h.bijOn.injOn.mono inter_subset_left
  refine ⟨hinj.bijOn_image, h.isPiecewiseAffineOn.inter_preimage_of_isPolyhedron hP, ?_⟩
  have himg : p '' (s ∩ p ⁻¹' P) = p '' s ∩ P := image_inter_preimage p s P
  rw [himg]
  refine (h.isPiecewiseAffineOn_invFunOn.inter_of_isPolyhedron hP).congr fun y hy => ?_
  have hy' : y ∈ p '' (s ∩ p ⁻¹' P) := himg ▸ hy
  have h1 : Function.invFunOn p (s ∩ p ⁻¹' P) y ∈ s ∩ p ⁻¹' P :=
    hinj.bijOn_image.surjOn.mapsTo_invFunOn hy'
  have h2 : p (Function.invFunOn p (s ∩ p ⁻¹' P) y) = y :=
    hinj.bijOn_image.invOn_invFunOn.2 hy'
  have h3 : Function.invFunOn p s y ∈ s := h.bijOn.surjOn.mapsTo_invFunOn hy.1
  have h4 : p (Function.invFunOn p s y) = y := h.bijOn.invOn_invFunOn.2 hy.1
  exact h.bijOn.injOn h1.1 h3 (h2.trans h4.symm)

theorem IsPLHomeomorphOn.comp_of_univ [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]
    {p : E → F} {s : Set E} {t : Set F} (h : IsPLHomeomorphOn p s t) {Φ : F → G}
    (hΦ : IsPLHomeomorphOn Φ univ univ) : IsPLHomeomorphOn (Φ ∘ p) s (Φ '' t) := by
  have hΦt : BijOn Φ t (Φ '' t) := (hΦ.bijOn.injOn.mono (subset_univ t)).bijOn_image
  have hbij : BijOn (Φ ∘ p) s (Φ '' t) := hΦt.comp h.bijOn
  refine ⟨hbij, ?_, ?_⟩
  · have hc := hΦ.isPiecewiseAffineOn.comp h.isPiecewiseAffineOn
    rwa [preimage_univ, inter_univ] at hc
  · have hc := h.isPiecewiseAffineOn_invFunOn.comp hΦ.isPiecewiseAffineOn_invFunOn
    have hset : univ ∩ Function.invFunOn Φ univ ⁻¹' t = Φ '' t := by
      ext z
      constructor
      · rintro ⟨-, hz⟩
        exact ⟨_, hz, hΦ.bijOn.invOn_invFunOn.2 (mem_univ z)⟩
      · rintro ⟨w, hw, rfl⟩
        refine ⟨mem_univ _, ?_⟩
        rw [mem_preimage, hΦ.bijOn.invOn_invFunOn.1 (mem_univ w)]
        exact hw
    rw [hset] at hc
    refine hc.congr fun z hz => ?_
    have h1 : Function.invFunOn (Φ ∘ p) s z ∈ s := hbij.surjOn.mapsTo_invFunOn hz
    have h2 : Φ (p (Function.invFunOn (Φ ∘ p) s z)) = z := hbij.invOn_invFunOn.2 hz
    have hψ : Function.invFunOn Φ univ z ∈ t := by
      obtain ⟨w, hw, rfl⟩ := hz
      rw [hΦ.bijOn.invOn_invFunOn.1 (mem_univ w)]
      exact hw
    have h3 : Function.invFunOn p s (Function.invFunOn Φ univ z) ∈ s :=
      h.bijOn.surjOn.mapsTo_invFunOn hψ
    have h4 : p (Function.invFunOn p s (Function.invFunOn Φ univ z)) =
        Function.invFunOn Φ univ z := h.bijOn.invOn_invFunOn.2 hψ
    have h5 : Φ (Function.invFunOn Φ univ z) = z := hΦ.bijOn.invOn_invFunOn.2 (mem_univ z)
    refine h.bijOn.injOn h1 h3 (hΦ.bijOn.injOn (mem_univ _) (mem_univ _) ?_)
    rw [h2, Function.comp_apply, h4, h5]

theorem IsPLHomeomorphOn.image_mem_nhds_of_univ [FiniteDimensional ℝ G] {Φ : F → G}
    (hΦ : IsPLHomeomorphOn Φ univ univ) {q : F} {V : Set F} (hV : V ∈ 𝓝 q) :
    Φ '' V ∈ 𝓝 (Φ q) := by
  have hψc : Continuous (Function.invFunOn Φ univ) :=
    continuousOn_univ.mp hΦ.isPiecewiseAffineOn_invFunOn.continuousOn
  have hψq : Function.invFunOn Φ univ (Φ q) = q := hΦ.bijOn.invOn_invFunOn.1 (mem_univ q)
  refine Filter.mem_of_superset (hψc.continuousAt.preimage_mem_nhds (by rwa [hψq])) ?_
  intro z hz
  exact ⟨_, hz, hΦ.bijOn.invOn_invFunOn.2 (mem_univ z)⟩

end PL

def blockSwap : ℝ × ℝ × ℝ ≃ᵃ[ℝ] ℝ × ℝ × ℝ :=
  (LinearEquiv.ofInvolutive
    ((LinearMap.fst ℝ ℝ ℝ ∘ₗ LinearMap.snd ℝ ℝ (ℝ × ℝ)).prod
      ((LinearMap.fst ℝ ℝ (ℝ × ℝ)).prod (LinearMap.snd ℝ ℝ ℝ ∘ₗ LinearMap.snd ℝ ℝ (ℝ × ℝ))))
    fun _ => rfl).toAffineEquiv

theorem blockSwap_apply (w : ℝ × ℝ × ℝ) : blockSwap w = (w.2.1, w.1, w.2.2) :=
  rfl

theorem blockSwap_mem_blockBox_iff {r tlo : ℝ} {w : ℝ × ℝ × ℝ} :
    blockSwap w ∈ blockBox r tlo ↔ w ∈ blockBox r tlo := by
  rw [blockSwap_apply]
  simp only [blockBox, mem_ofPred_eq]
  exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

section Ambient

variable {M : Type u} [TopologicalSpace M]

theorem chartBlock_trans_blockSwap (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ) :
    chartBlock ec (A.trans blockSwap) r tlo = chartBlock ec A r tlo := by
  ext z
  simp only [chartBlock, mem_inter_iff, mem_preimage, AffineEquiv.coe_trans, Function.comp_apply,
    blockSwap_mem_blockBox_iff]

theorem innerChartBlock_trans_blockSwap
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ) :
    innerChartBlock ec (A.trans blockSwap) r tlo = innerChartBlock ec A r tlo :=
  chartBlock_trans_blockSwap ec A (r / 2) (tlo / 2)

theorem blockSheetProjA_trans_blockSwap
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (f : EuclideanSpace ℝ (Fin 2) → M) :
    blockSheetProjA ec (A.trans blockSwap) f = blockSheetProjB ec A f :=
  rfl

theorem blockSheetProjA_transfer {f : EuclideanSpace ℝ (Fin 2) → M}
    {S SA : Set (EuclideanSpace ℝ (Fin 2))}
    {ec ec' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {A A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo r' tlo' : ℝ}
    {a a' : ℝ × ℝ → ℝ} {α β γ : ℝ → ℝ}
    (hpre : ∀ x ∈ SA, f x ∈ chartBlock ec A r tlo)
    (hgraph : ∀ x ∈ SA, (A (ec (f x))).1 = a ((A (ec (f x))).2.1, (A (ec (f x))).2.2))
    (hpl : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA))
    (hΦ : IsPLHomeomorphOn (fun q : ℝ × ℝ => (q.1 + β q.2, γ q.2)) univ univ)
    (hg : IsPiecewiseAffineOn (fun q : ℝ × ℝ => a q + α q.2) univ)
    (ha'eq : ∀ v t, a' (v + β t, γ t) = a (v, t) + α t)
    (hr' : 0 < r') (htlo' : tlo' = -r' ∨ tlo' = 0)
    (hlow : tlo' = 0 → tlo = 0 ∧ ∀ t, 0 ≤ γ t ↔ 0 ≤ t)
    (hrel : ∀ z ∈ chartBlock ec A r tlo, z ∈ chartBlock ec' A' r' tlo' ↔
      ((A (ec z)).1 + α (A (ec z)).2.2, (A (ec z)).2.1 + β (A (ec z)).2.2,
        γ (A (ec z)).2.2) ∈ blockBox r' tlo')
    (heq : ∀ z ∈ chartBlock ec' A' r' tlo', A' (ec' z) =
      ((A (ec z)).1 + α (A (ec z)).2.2, (A (ec z)).2.1 + β (A (ec z)).2.2, γ (A (ec z)).2.2))
    (hgood : ∀ x ∈ SA, f x ∈ innerChartBlock ec' A' r' tlo' → SA ∈ 𝓝[S] x ∧
      ∃ U ∈ 𝓝 (blockSheetProjA ec A f x), U ∩ (fun q : ℝ × ℝ => (q.1 + β q.2, γ q.2)) ⁻¹'
        blockHalfPlane tlo' ⊆ blockSheetProjA ec A f '' SA) :
    (∀ x ∈ SA ∩ f ⁻¹' chartBlock ec' A' r' tlo', (A' (ec' (f x))).1 =
        a' ((A' (ec' (f x))).2.1, (A' (ec' (f x))).2.2)) ∧
      IsPLHomeomorphOn (blockSheetProjA ec' A' f) (SA ∩ f ⁻¹' chartBlock ec' A' r' tlo')
        (blockSheetProjA ec' A' f '' (SA ∩ f ⁻¹' chartBlock ec' A' r' tlo')) ∧
      ∀ x ∈ SA ∩ f ⁻¹' chartBlock ec' A' r' tlo', f x ∈ innerChartBlock ec' A' r' tlo' →
        SA ∩ f ⁻¹' chartBlock ec' A' r' tlo' ∈ 𝓝[S] x ∧
          blockSheetProjA ec' A' f '' (SA ∩ f ⁻¹' chartBlock ec' A' r' tlo') ∈
            𝓝[blockHalfPlane tlo'] (blockSheetProjA ec' A' f x) := by
  set Φ : ℝ × ℝ → ℝ × ℝ := fun q => (q.1 + β q.2, γ q.2)
  set g : ℝ × ℝ → ℝ := fun q => a q + α q.2
  set N := chartBlock ec' A' r' tlo'
  set pA := blockSheetProjA ec A f
  have hA : ∀ x ∈ SA, A (ec (f x)) = (a (pA x), pA x) := fun x hx => Prod.ext (hgraph x hx) rfl
  have hmemN : ∀ x ∈ SA, f x ∈ N ↔ (g (pA x), Φ (pA x)) ∈ blockBox r' tlo' := by
    intro x hx
    have h := hrel (f x) (hpre x hx)
    rw [hA x hx] at h
    exact h
  have hA' : ∀ x ∈ SA, f x ∈ N → A' (ec' (f x)) = (g (pA x), Φ (pA x)) := by
    intro x hx hxN
    exact (heq _ hxN).trans (congrArg
      (fun w : ℝ × ℝ × ℝ => (w.1 + α w.2.2, w.2.1 + β w.2.2, γ w.2.2)) (hA x hx))
  have hproj' : ∀ x ∈ SA, f x ∈ N → blockSheetProjA ec' A' f x = Φ (pA x) := by
    intro x hx hxN
    simp only [blockSheetProjA, hA' x hx hxN, Prod.mk.eta]
  have himage : blockSheetProjA ec' A' f '' (SA ∩ f ⁻¹' N) = Φ '' (pA '' (SA ∩ f ⁻¹' N)) := by
    rw [image_image]
    exact image_congr fun x hx => hproj' x hx.1 hx.2
  set P : Set (ℝ × ℝ) := {q | (g q, Φ q) ∈ blockBox r' tlo'} with hPdef
  have hSA' : SA ∩ f ⁻¹' N = SA ∩ pA ⁻¹' P := by
    ext x
    exact ⟨fun hx => ⟨hx.1, (hmemN x hx.1).1 hx.2⟩, fun hx => ⟨hx.1, (hmemN x hx.1).2 hx.2⟩⟩
  have hΦc : Continuous Φ := continuousOn_univ.mp hΦ.isPiecewiseAffineOn.continuousOn
  have hgc : Continuous g := continuousOn_univ.mp hg.continuousOn
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [hA' x hx.1 hx.2]
    change g (pA x) = a' ((pA x).1 + β (pA x).2, γ (pA x).2)
    exact (ha'eq (pA x).1 (pA x).2).symm
  · have hbox : IsPolyhedron (Icc (-r') r' ×ˢ Icc tlo' r') :=
      (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
    have hP1 : IsPolyhedron (univ ∩ Φ ⁻¹' (Icc (-r') r' ×ˢ Icc tlo' r')) :=
      hΦ.isPolyhedron_preimage hbox (subset_univ _)
    have hP2 := (hg.mono_of_isPolyhedron hP1 (subset_univ _)).isPolyhedron_sublevel hP1 r'
    have hgneg : IsPiecewiseAffineOn (fun q => -g q) univ :=
      (hg.affine_comp (-AffineMap.id ℝ ℝ)).congr fun _ _ => rfl
    have hP3 := (hgneg.mono_of_isPolyhedron hP2 (subset_univ _)).isPolyhedron_sublevel hP2 r'
    have hPpoly : IsPolyhedron P := by
      convert hP3 using 1
      ext q
      simp only [hPdef, blockBox, mem_ofPred_eq, mem_inter_iff, mem_univ, true_and,
        mem_preimage, mem_prod, mem_Icc, abs_le]
      constructor
      · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩
        exact ⟨⟨⟨⟨h3, h4⟩, h5, h6⟩, h2⟩, by linarith⟩
      · rintro ⟨⟨⟨⟨h3, h4⟩, h5, h6⟩, h2⟩, h1⟩
        exact ⟨⟨by linarith, h2⟩, ⟨h3, h4⟩, h5, h6⟩
    have h2 := (hpl.inter_preimage_of_isPolyhedron hPpoly).comp_of_univ hΦ
    rw [← hSA'] at h2
    rw [himage]
    exact h2.congr fun x hx => hproj' x hx.1 hx.2
  · intro x hx hxin
    obtain ⟨hSnhds, U, hU, hUsub⟩ := hgood x hx.1 hxin
    have hin : (g (pA x), Φ (pA x)) ∈ blockBox (r' / 2) (tlo' / 2) := by
      have h := hxin.2
      rw [mem_preimage, mem_preimage, hA' x hx.1 hx.2] at h
      exact h
    have hin1 : |g (pA x)| ≤ r' / 2 := hin.1
    have hin2 : |(Φ (pA x)).1| ≤ r' / 2 := hin.2.1
    have hin3 : tlo' / 2 ≤ (Φ (pA x)).2 := hin.2.2.1
    have hin4 : (Φ (pA x)).2 ≤ r' / 2 := hin.2.2.2
    let W : Set (ℝ × ℝ × ℝ) :=
      {w | |w.1| < r' ∧ |w.2.1| < r' ∧ w.2.2 < r' ∧ tlo' / 2 - r' / 2 < w.2.2}
    have hWo : IsOpen W :=
      (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
        ((isOpen_lt (continuous_abs.comp continuous_snd.fst) continuous_const).inter
          ((isOpen_lt continuous_snd.snd continuous_const).inter
            (isOpen_lt continuous_const continuous_snd.snd)))
    have hGc : Continuous fun q : ℝ × ℝ => (g q, Φ q) := hgc.prodMk hΦc
    let O : Set (ℝ × ℝ) := (fun q : ℝ × ℝ => (g q, Φ q)) ⁻¹' W
    have hOo : IsOpen O := hWo.preimage hGc
    have hpO : pA x ∈ O := by
      change |g (pA x)| < r' ∧ |(Φ (pA x)).1| < r' ∧ (Φ (pA x)).2 < r' ∧
        tlo' / 2 - r' / 2 < (Φ (pA x)).2
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    have hOP : ∀ q ∈ O, q ∈ Φ ⁻¹' blockHalfPlane tlo' → q ∈ P := by
      intro q hqO hqH
      have h1 : |g q| < r' := hqO.1
      have h2 : |(Φ q).1| < r' := hqO.2.1
      have h3 : (Φ q).2 < r' := hqO.2.2.1
      have h4 : tlo' / 2 - r' / 2 < (Φ q).2 := hqO.2.2.2
      have h5 : tlo' = 0 → 0 ≤ (Φ q).2 := hqH
      change |g q| ≤ r' ∧ |(Φ q).1| ≤ r' ∧ tlo' ≤ (Φ q).2 ∧ (Φ q).2 ≤ r'
      refine ⟨h1.le, h2.le, ?_, h3.le⟩
      rcases htlo' with ht | ht
      · rw [ht] at h4 ⊢
        linarith
      · rw [ht]
        exact h5 ht
    have hSAH : ∀ x' ∈ SA, pA x' ∈ Φ ⁻¹' blockHalfPlane tlo' := by
      intro x' hx' ht0
      obtain ⟨htlo, hγ⟩ := hlow ht0
      have hb := (hpre x' hx').2
      rw [mem_preimage, mem_preimage] at hb
      have ht : 0 ≤ (A (ec (f x'))).2.2 := htlo ▸ hb.2.2.1
      exact (hγ _).2 ht
    refine ⟨?_, ?_⟩
    · have hpc : ContinuousWithinAt pA SA x := hpl.isPiecewiseAffineOn.continuousOn x hx.1
      have h1 : pA ⁻¹' O ∈ 𝓝[SA] x := hpc.preimage_mem_nhdsWithin (hOo.mem_nhds hpO)
      have h2 : pA ⁻¹' O ∈ 𝓝[S] x := nhdsWithin_le_of_mem hSnhds h1
      filter_upwards [hSnhds, h2] with x' hx'SA hx'O
      exact ⟨hx'SA, (hmemN x' hx'SA).2 (hOP _ hx'O (hSAH x' hx'SA))⟩
    · have hsub2 : (U ∩ O) ∩ Φ ⁻¹' blockHalfPlane tlo' ⊆ pA '' (SA ∩ f ⁻¹' N) := by
        rintro q ⟨⟨hqU, hqO⟩, hqH⟩
        obtain ⟨x', hx', rfl⟩ := hUsub ⟨hqU, hqH⟩
        exact ⟨x', ⟨hx', (hmemN x' hx').2 (hOP _ hqO hqH)⟩, rfl⟩
      rw [himage, hproj' x hx.1 hx.2]
      have hV : Φ '' (U ∩ O) ∈ 𝓝 (Φ (pA x)) :=
        hΦ.image_mem_nhds_of_univ (Filter.inter_mem hU (hOo.mem_nhds hpO))
      refine Filter.mem_of_superset (inter_mem_nhdsWithin (blockHalfPlane tlo') hV) ?_
      rintro z ⟨hzH, q, hq, rfl⟩
      exact ⟨q, hsub2 ⟨hq, hzH⟩, rfl⟩

theorem IsStableCrossingBlock.transfer {f : EuclideanSpace ℝ (Fin 2) → M}
    {S SA SB : Set (EuclideanSpace ℝ (Fin 2))}
    {ec ec' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ ℓ' : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo r' tlo' : ℝ}
    {a b a' b' : ℝ × ℝ → ℝ} {La Lb η : ℝ} {α β γ : ℝ → ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hγ : Function.Surjective γ)
    (hΦA : IsPLHomeomorphOn (fun q : ℝ × ℝ => (q.1 + β q.2, γ q.2)) univ univ)
    (hΦB : IsPLHomeomorphOn (fun q : ℝ × ℝ => (q.1 + α q.2, γ q.2)) univ univ)
    (hgA : IsPiecewiseAffineOn (fun q : ℝ × ℝ => a q + α q.2) univ)
    (hgB : IsPiecewiseAffineOn (fun q : ℝ × ℝ => b q + β q.2) univ)
    (ha'eq : ∀ v t, a' (v + β t, γ t) = a (v, t) + α t)
    (hb'eq : ∀ u t, b' (u + α t, γ t) = b (u, t) + β t)
    (ha' : IsPiecewiseAffineOn a' univ) (hb' : IsPiecewiseAffineOn b' univ)
    (hr' : 0 < r') (hcpt : IsCompact (closure (chartBlock ec' A' r' tlo')))
    (hsrc : closure (chartBlock ec' A' r' tlo') ⊆ ec'.source)
    (hside : (tlo' = -r' ∧ Disjoint (chartBlock ec' A' r' tlo') BdM) ∨
      (tlo' = 0 ∧ tlo = 0 ∧ (∀ t, 0 ≤ γ t ↔ 0 ≤ t) ∧ (∀ t, γ t = 0 ↔ t = 0) ∧
        ∀ z, (A' z).2.2 = ℓ' z))
    (hsub : chartBlock ec' A' r' tlo' ⊆ chartBlock ec A r tlo)
    (hrel : ∀ z ∈ chartBlock ec A r tlo, z ∈ chartBlock ec' A' r' tlo' ↔
      ((A (ec z)).1 + α (A (ec z)).2.2, (A (ec z)).2.1 + β (A (ec z)).2.2,
        γ (A (ec z)).2.2) ∈ blockBox r' tlo')
    (heq : ∀ z ∈ chartBlock ec' A' r' tlo', A' (ec' z) =
      ((A (ec z)).1 + α (A (ec z)).2.2, (A (ec z)).2.1 + β (A (ec z)).2.2, γ (A (ec z)).2.2))
    (hgoodA : ∀ x ∈ SA, f x ∈ innerChartBlock ec' A' r' tlo' → SA ∈ 𝓝[S] x ∧
      ∃ U ∈ 𝓝 (blockSheetProjA ec A f x), U ∩ (fun q : ℝ × ℝ => (q.1 + β q.2, γ q.2)) ⁻¹'
        blockHalfPlane tlo' ⊆ blockSheetProjA ec A f '' SA)
    (hgoodB : ∀ x ∈ SB, f x ∈ innerChartBlock ec' A' r' tlo' → SB ∈ 𝓝[S] x ∧
      ∃ U ∈ 𝓝 (blockSheetProjB ec A f x), U ∩ (fun q : ℝ × ℝ => (q.1 + α q.2, γ q.2)) ⁻¹'
        blockHalfPlane tlo' ⊆ blockSheetProjB ec A f '' SB) :
    IsStableCrossingBlock f S ec' ℓ' BdM A' r' tlo' (SA ∩ f ⁻¹' chartBlock ec' A' r' tlo')
      (SB ∩ f ⁻¹' chartBlock ec' A' r' tlo') a' b' La Lb η := by
  obtain ⟨hr, hη, hLa, hLb, hmar, -, -, hside0, hpre, hdisj, hgrA, hgrB, hplA, hplB, -, -,
    hLipa, hLipb, -, -⟩ := h
  have htlo' : tlo' = -r' ∨ tlo' = 0 := by
    rcases hside with ⟨ht, -⟩ | ⟨ht, -⟩
    · exact Or.inl ht
    · exact Or.inr ht
  have hlow : tlo' = 0 → tlo = 0 ∧ ∀ t, 0 ≤ γ t ↔ 0 ≤ t := by
    intro ht0
    rcases hside with ⟨ht, -⟩ | ⟨-, htlo, hγ0, -⟩
    · exfalso
      linarith
    · exact ⟨htlo, hγ0⟩
  have hpreS : ∀ x ∈ SA ∪ SB, x ∈ S ∧ f x ∈ chartBlock ec A r tlo := by
    intro x hx
    rw [← hpre] at hx
    exact hx
  obtain ⟨hgrA', hplA', hnA'⟩ := blockSheetProjA_transfer (fun x hx => (hpreS x (Or.inl hx)).2)
    hgrA hplA hΦA hgA ha'eq hr' htlo' hlow hrel heq hgoodA
  obtain ⟨hgrB', hplB', hnB'⟩ := blockSheetProjA_transfer (A := A.trans blockSwap)
    (A' := A'.trans blockSwap) (a := b) (a' := b') (α := β) (β := α) (S := S)
    (fun x hx => by rw [chartBlock_trans_blockSwap]; exact (hpreS x (Or.inr hx)).2)
    hgrB (by rw [blockSheetProjA_trans_blockSwap]; exact hplB) hΦB hgB hb'eq hr' htlo' hlow
    (fun z hz => by
      rw [chartBlock_trans_blockSwap] at hz ⊢
      exact (hrel z hz).trans blockSwap_mem_blockBox_iff.symm)
    (fun z hz => by
      rw [chartBlock_trans_blockSwap] at hz
      exact congrArg blockSwap (heq z hz))
    (fun x hx hxin => hgoodB x hx (by rwa [innerChartBlock_trans_blockSwap] at hxin))
  rw [chartBlock_trans_blockSwap, innerChartBlock_trans_blockSwap,
    blockSheetProjA_trans_blockSwap] at hnB'
  rw [chartBlock_trans_blockSwap, blockSheetProjA_trans_blockSwap] at hplB'
  rw [chartBlock_trans_blockSwap] at hgrB'
  refine ⟨hr', hη, hLa, hLb, hmar, hcpt, hsrc, ?_, ?_, ?_, hgrA', fun x hx => hgrB' x hx, hplA',
    hplB', hnA', hnB', ?_, ?_, ha', hb'⟩
  · rcases hside with ⟨ht, hd⟩ | ⟨ht, htlo, -, hγ00, hheight⟩
    · exact Or.inl ⟨ht, hd⟩
    · refine Or.inr ⟨ht, hheight, fun x hx => ?_⟩
      rcases hside0 with ⟨htl, -⟩ | ⟨-, -, hfr⟩
      · exfalso
        linarith
      have hx₀ : x ∈ SA ∪ SB := hx.imp (fun h => h.1) (fun h => h.1)
      have hxN : f x ∈ chartBlock ec' A' r' tlo' := hx.elim (fun h => h.2) (fun h => h.2)
      rw [hfr x hx₀, heq (f x) hxN]
      exact (hγ00 _).symm
  · ext x
    constructor
    · rintro ⟨hxS, hxN⟩
      have hx : x ∈ SA ∪ SB := by
        rw [← hpre]
        exact ⟨hxS, hsub hxN⟩
      rcases hx with hx | hx
      · exact Or.inl ⟨hx, hxN⟩
      · exact Or.inr ⟨hx, hxN⟩
    · rintro (⟨hx, hxN⟩ | ⟨hx, hxN⟩)
      · exact ⟨(hpreS x (Or.inl hx)).1, hxN⟩
      · exact ⟨(hpreS x (Or.inr hx)).1, hxN⟩
  · exact (hdisj.mono_left inter_subset_left).mono_right inter_subset_left
  · intro v v' t
    obtain ⟨s, rfl⟩ := hγ t
    have h1 := ha'eq (v - β s) s
    have h2 := ha'eq (v' - β s) s
    rw [sub_add_cancel] at h1 h2
    rw [h1, h2, add_sub_add_right_eq_sub]
    have h3 := hLipa (v - β s) (v' - β s) s
    rwa [sub_sub_sub_cancel_right] at h3
  · intro u u' t
    obtain ⟨s, rfl⟩ := hγ t
    have h1 := hb'eq (u - α s) s
    have h2 := hb'eq (u' - α s) s
    rw [sub_add_cancel] at h1 h2
    rw [h1, h2, add_sub_add_right_eq_sub]
    have h3 := hLipb (u - α s) (u' - α s) s
    rwa [sub_sub_sub_cancel_right] at h3

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear

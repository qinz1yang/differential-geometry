/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlaneBoxGraphPerturbation
import DifferentialGeometry.Topology.PiecewiseLinear.SheetBlockAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.CollarSectorPolyhedron

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem IsPiecewiseAffineOn.exists_lipschitzOnWith_of_isPolyhedron {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {P : Set E} (hf : IsPiecewiseAffineOn f P)
    (hP : IsPolyhedron P) : ∃ k : NNReal, LipschitzOnWith k f P := by
  obtain ⟨g, k, -, hk, hgf, -, -⟩ := hf.exists_lipschitz_extension hP isOpen_univ (subset_univ P)
  refine ⟨k, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  rw [← hgf hx, ← hgf hy]
  exact hk.dist_le_mul x y

theorem AffineEquiv.apply_add_eq_add_linear (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ)
    (z v : EuclideanSpace ℝ (Fin 3)) : A (z + v) = A z + A.linear v := by
  have h := A.map_vadd z v
  rw [vadd_eq_add, vadd_eq_add] at h
  rw [add_comm z v, h, add_comm]

section Ambient

variable {M : Type u} [TopologicalSpace M]

theorem blockSheetProjA_perturbation {f g : EuclideanSpace ℝ (Fin 2) → M}
    {S SA : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r' tlo' s tl : ℝ}
    {a' c : ℝ × ℝ → ℝ} {ψ : ℝ × ℝ → ℝ × ℝ}
    (hpl : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA))
    (hB₀ : Icc (-s) s ×ˢ Icc tl s ⊆ blockSheetProjA ec A f '' SA)
    (hψ : IsPLHomeomorphOn ψ univ univ)
    (hc : IsPiecewiseAffineOn c (Icc (-s) s ×ˢ Icc tl s))
    (ha' : ∀ q ∈ Icc (-s) s ×ˢ Icc tl s, a' (ψ q) = c q)
    (hnew : ∀ x ∈ SA, blockSheetProjA ec A f x ∈ Icc (-s) s ×ˢ Icc tl s →
      g x ∈ ec.source ∧
        A (ec (g x)) = (c (blockSheetProjA ec A f x), ψ (blockSheetProjA ec A f x)))
    (hbox : ∀ x ∈ SA, g x ∈ chartBlock ec A r' tlo' →
      |(blockSheetProjA ec A f x).1| < s ∧ (blockSheetProjA ec A f x).2 < s ∧
        (tl < (blockSheetProjA ec A f x).2 ∨ tlo' = 0))
    (hr' : 0 < r') (htlo' : tlo' = -r' ∨ tlo' = 0)
    (hlow : tlo' = 0 → tl = 0 ∧ (∀ x ∈ SA, 0 ≤ (blockSheetProjA ec A f x).2) ∧
      (∀ q : ℝ × ℝ, q.2 < 0 → (ψ q).2 < 0) ∧ ∀ x ∈ SA, 0 ≤ (A (ec (g x))).2.2)
    (hSnhds : ∀ x ∈ SA, g x ∈ innerChartBlock ec A r' tlo' → SA ∈ 𝓝[S] x) :
    (∀ x ∈ SA ∩ g ⁻¹' chartBlock ec A r' tlo', (A (ec (g x))).1 =
        a' ((A (ec (g x))).2.1, (A (ec (g x))).2.2)) ∧
      IsPLHomeomorphOn (blockSheetProjA ec A g) (SA ∩ g ⁻¹' chartBlock ec A r' tlo')
        (blockSheetProjA ec A g '' (SA ∩ g ⁻¹' chartBlock ec A r' tlo')) ∧
      ∀ x ∈ SA ∩ g ⁻¹' chartBlock ec A r' tlo', g x ∈ innerChartBlock ec A r' tlo' →
        SA ∩ g ⁻¹' chartBlock ec A r' tlo' ∈ 𝓝[S] x ∧
          blockSheetProjA ec A g '' (SA ∩ g ⁻¹' chartBlock ec A r' tlo') ∈
            𝓝[blockHalfPlane tlo'] (blockSheetProjA ec A g x) := by
  set B₀ : Set (ℝ × ℝ) := Icc (-s) s ×ˢ Icc tl s
  set N := chartBlock ec A r' tlo'
  set pA := blockSheetProjA ec A f
  set F : ℝ × ℝ → ℝ × ℝ × ℝ := fun q => (c q, ψ q)
  have hK1 : ∀ q : ℝ × ℝ, |q.1| < s → q.2 < s → (tl < q.2 ∨ tlo' = 0) →
      (tlo' = 0 → 0 ≤ q.2) → q ∈ B₀ := by
    intro q h1 h2 h3 h4
    refine ⟨⟨by linarith [neg_abs_le q.1], by linarith [le_abs_self q.1]⟩, ?_, h2.le⟩
    rcases h3 with h3 | h3
    · exact h3.le
    · rw [(hlow h3).1]
      exact h4 h3
  have hmemN : ∀ x ∈ SA, g x ∈ N ↔ pA x ∈ B₀ ∧ F (pA x) ∈ blockBox r' tlo' := by
    intro x hx
    constructor
    · intro hxN
      obtain ⟨hb1, hb2, hb3⟩ := hbox x hx hxN
      have hq : pA x ∈ B₀ := hK1 _ hb1 hb2 hb3 fun h0 => (hlow h0).2.1 x hx
      refine ⟨hq, ?_⟩
      have h := hxN.2
      rw [mem_preimage, mem_preimage, (hnew x hx hq).2] at h
      exact h
    · rintro ⟨hq, hF⟩
      refine ⟨(hnew x hx hq).1, ?_⟩
      rw [mem_preimage, mem_preimage, (hnew x hx hq).2]
      exact hF
  have hproj' : ∀ x ∈ SA, pA x ∈ B₀ → blockSheetProjA ec A g x = ψ (pA x) := by
    intro x hx hq
    simp only [blockSheetProjA, (hnew x hx hq).2, Prod.mk.eta]
  set P : Set (ℝ × ℝ) := B₀ ∩ F ⁻¹' blockBox r' tlo'
  have hSA' : SA ∩ g ⁻¹' N = SA ∩ pA ⁻¹' P := by
    ext x
    exact ⟨fun hx => ⟨hx.1, (hmemN x hx.1).1 hx.2⟩, fun hx => ⟨hx.1, (hmemN x hx.1).2 hx.2⟩⟩
  have hB₀poly : IsPolyhedron B₀ := (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  have hψB : IsPiecewiseAffineOn ψ B₀ :=
    hψ.isPiecewiseAffineOn.mono_of_isPolyhedron hB₀poly (subset_univ _)
  have hFpl : IsPiecewiseAffineOn F B₀ := hc.prod_mk hψB
  have hPpoly : IsPolyhedron P :=
    hFpl.isPolyhedron_inter_preimage_of_isPolyhedron hB₀poly
      (isHPolytope_blockBox r' tlo').isPolyhedron
  have himage : blockSheetProjA ec A g '' (SA ∩ g ⁻¹' N) = ψ '' (pA '' (SA ∩ g ⁻¹' N)) := by
    rw [image_image]
    exact image_congr fun x hx => hproj' x hx.1 ((hmemN x hx.1).1 hx.2).1
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hq := ((hmemN x hx.1).1 hx.2).1
    rw [(hnew x hx.1 hq).2]
    change c (pA x) = a' ((ψ (pA x)).1, (ψ (pA x)).2)
    rw [Prod.mk.eta]
    exact (ha' _ hq).symm
  · have h2 := (hpl.inter_preimage_of_isPolyhedron hPpoly).comp_of_univ hψ
    rw [← hSA'] at h2
    rw [himage]
    exact h2.congr fun x hx => hproj' x hx.1 ((hmemN x hx.1).1 hx.2).1
  · intro x hx hxin
    have hq : pA x ∈ B₀ := ((hmemN x hx.1).1 hx.2).1
    obtain ⟨hb1, hb2, hb3⟩ := hbox x hx.1 hx.2
    have hin : F (pA x) ∈ blockBox (r' / 2) (tlo' / 2) := by
      have h := hxin.2
      rw [mem_preimage, mem_preimage, (hnew x hx.1 hq).2] at h
      exact h
    have hin1 : |(F (pA x)).1| ≤ r' / 2 := hin.1
    have hin2 : |(F (pA x)).2.1| ≤ r' / 2 := hin.2.1
    have hin3 : tlo' / 2 ≤ (F (pA x)).2.2 := hin.2.2.1
    have hin4 : (F (pA x)).2.2 ≤ r' / 2 := hin.2.2.2
    let W : Set (ℝ × ℝ × ℝ) :=
      {w | |w.1| < r' ∧ |w.2.1| < r' ∧ w.2.2 < r' ∧ tlo' / 2 - r' / 2 < w.2.2}
    have hWo : IsOpen W :=
      (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
        ((isOpen_lt (continuous_abs.comp continuous_snd.fst) continuous_const).inter
          ((isOpen_lt continuous_snd.snd continuous_const).inter
            (isOpen_lt continuous_const continuous_snd.snd)))
    have hFW : F (pA x) ∈ W := ⟨by linarith, by linarith, by linarith, by linarith⟩
    have hK2 : ∀ q : ℝ × ℝ, F q ∈ W → (tlo' = 0 → 0 ≤ (F q).2.2) → F q ∈ blockBox r' tlo' := by
      intro q hqW hq0
      obtain ⟨h1, h2, h3, h4⟩ := hqW
      refine ⟨h1.le, h2.le, ?_, h3.le⟩
      rcases htlo' with ht | ht
      · rw [ht] at h4 ⊢
        linarith
      · rw [ht]
        exact hq0 ht
    have hFc : ContinuousWithinAt F B₀ (pA x) := hFpl.continuousOn _ hq
    obtain ⟨V₁, hV₁o, hpV₁, hV₁sub⟩ :=
      mem_nhdsWithin.mp (hFc.preimage_mem_nhdsWithin (hWo.mem_nhds hFW))
    let G₀ : Set (ℝ × ℝ) := {q | |q.1| < s ∧ q.2 < s ∧ (tl < q.2 ∨ tlo' = 0)}
    have hG₀o : IsOpen G₀ := by
      have e : G₀ = {q : ℝ × ℝ | |q.1| < s} ∩ ({q : ℝ × ℝ | q.2 < s} ∩
          ({q : ℝ × ℝ | tl < q.2} ∪ {_q : ℝ × ℝ | tlo' = 0})) := by
        ext q
        simp only [G₀, mem_ofPred_eq, mem_inter_iff, mem_union]
      rw [e]
      exact (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
        ((isOpen_lt continuous_snd continuous_const).inter
          ((isOpen_lt continuous_const continuous_snd).union isOpen_const))
    have hpG₀ : pA x ∈ G₀ := ⟨hb1, hb2, hb3⟩
    have hgood : ∀ q ∈ G₀ ∩ V₁, (tlo' = 0 → 0 ≤ q.2) → (tlo' = 0 → 0 ≤ (ψ q).2) →
        q ∈ P := by
      intro q hq hq0 hψ0
      have hqB : q ∈ B₀ := hK1 q hq.1.1 hq.1.2.1 hq.1.2.2 hq0
      exact ⟨hqB, hK2 q (hV₁sub ⟨hq.2, hqB⟩) hψ0⟩
    refine ⟨?_, ?_⟩
    · have hpc : ContinuousWithinAt pA SA x := hpl.isPiecewiseAffineOn.continuousOn x hx.1
      have h1 : pA ⁻¹' (G₀ ∩ V₁) ∈ 𝓝[SA] x :=
        hpc.preimage_mem_nhdsWithin ((hG₀o.inter hV₁o).mem_nhds ⟨hpG₀, hpV₁⟩)
      have hSn := hSnhds x hx.1 hxin
      have h2 : pA ⁻¹' (G₀ ∩ V₁) ∈ 𝓝[S] x := nhdsWithin_le_of_mem hSn h1
      filter_upwards [hSn, h2] with x' hx'SA hx'O
      refine ⟨hx'SA, (hmemN x' hx'SA).2 ?_⟩
      have hq0 : tlo' = 0 → 0 ≤ (pA x').2 := fun h0 => (hlow h0).2.1 x' hx'SA
      have hqB : pA x' ∈ B₀ := hK1 _ hx'O.1.1 hx'O.1.2.1 hx'O.1.2.2 hq0
      have hψ0 : tlo' = 0 → 0 ≤ (ψ (pA x')).2 := by
        intro h0
        have h := (hlow h0).2.2.2 x' hx'SA
        rw [(hnew x' hx'SA hqB).2] at h
        exact h
      exact hgood _ hx'O hq0 hψ0
    · rw [himage, hproj' x hx.1 hq]
      have hV : ψ '' (G₀ ∩ V₁) ∈ 𝓝 (ψ (pA x)) :=
        hψ.image_mem_nhds_of_univ ((hG₀o.inter hV₁o).mem_nhds ⟨hpG₀, hpV₁⟩)
      refine Filter.mem_of_superset (inter_mem_nhdsWithin (blockHalfPlane tlo') hV) ?_
      rintro z ⟨hzH, q, hqV, rfl⟩
      have hψ0 : tlo' = 0 → 0 ≤ (ψ q).2 := hzH
      have hq0 : tlo' = 0 → 0 ≤ q.2 := by
        intro h0
        by_contra hneg
        exact absurd (hψ0 h0) (not_le.mpr ((hlow h0).2.2.1 q (not_le.mp hneg)))
      have hqP := hgood q hqV hq0 hψ0
      obtain ⟨x', hx', hx'q⟩ := hB₀ hqP.1
      refine ⟨pA x', ⟨x', ⟨hx', (hmemN x' hx').2 ?_⟩, rfl⟩, by rw [hx'q]⟩
      rw [hx'q]
      exact hqP

theorem exists_perturbed_blockSheetA {f g : EuclideanSpace ℝ (Fin 2) → M}
    {S SA : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r' tlo' s tl La : ℝ}
    {a : ℝ × ℝ → ℝ} {Lσ Lt Lℓ lam : NNReal}
    {δ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hs : 0 < s) (htl : tl ≤ 0) (hLa : 0 ≤ La)
    (hgraph : ∀ x ∈ SA, (A (ec (f x))).1 = a (blockSheetProjA ec A f x))
    (hpl : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA))
    (ha : IsPiecewiseAffineOn a univ)
    (haLip : ∀ v v' t : ℝ, |a (v, t) - a (v', t)| ≤ La * |v - v'|)
    (hB₀ : Icc (-s) s ×ˢ Icc tl s ⊆ blockSheetProjA ec A f '' SA)
    (hσ : LipschitzOnWith Lσ (Function.invFunOn (blockSheetProjA ec A f) SA)
      (Icc (-s) s ×ˢ Icc tl s))
    (haT : LipschitzOnWith Lt a (Icc (-s) s ×ˢ Icc tl s))
    (hAL : LipschitzWith Lℓ A.linear)
    (hδ : IsPiecewiseAffineOn δ univ) (hδL : LipschitzWith lam δ)
    (hμ : ((Lℓ * (lam * Lσ) : NNReal) : ℝ) ≤ 1 / 2)
    (hG : ∀ x ∈ SA, g x ∈ ec.source ∧ ec (g x) = ec (f x) + δ x)
    (hbox : ∀ x ∈ SA, g x ∈ chartBlock ec A r' tlo' →
      |(blockSheetProjA ec A f x).1| < s ∧ (blockSheetProjA ec A f x).2 < s ∧
        (tl < (blockSheetProjA ec A f x).2 ∨ tlo' = 0))
    (hr' : 0 < r') (htlo' : tlo' = -r' ∨ tlo' = 0)
    (hlow : tlo' = 0 → tl = 0 ∧ (∀ x ∈ SA, 0 ≤ (blockSheetProjA ec A f x).2) ∧
      (∀ x ∈ SA, (A (ec (f x))).2.2 = 0 → (A.linear (δ x)).2.2 = 0) ∧
      ∀ x ∈ SA, 0 ≤ (A (ec (g x))).2.2)
    (hSnhds : ∀ x ∈ SA, g x ∈ innerChartBlock ec A r' tlo' → SA ∈ 𝓝[S] x) :
    ∃ a' : ℝ × ℝ → ℝ, IsPiecewiseAffineOn a' univ ∧
      (∀ v v' t : ℝ, |a' (v, t) - a' (v', t)| ≤
        (La + 2 * (La + Lt + 1) * ((Lℓ * (lam * Lσ) : NNReal) : ℝ)) * |v - v'|) ∧
      (∀ x ∈ SA ∩ g ⁻¹' chartBlock ec A r' tlo', (A (ec (g x))).1 =
        a' ((A (ec (g x))).2.1, (A (ec (g x))).2.2)) ∧
      IsPLHomeomorphOn (blockSheetProjA ec A g) (SA ∩ g ⁻¹' chartBlock ec A r' tlo')
        (blockSheetProjA ec A g '' (SA ∩ g ⁻¹' chartBlock ec A r' tlo')) ∧
      ∀ x ∈ SA ∩ g ⁻¹' chartBlock ec A r' tlo', g x ∈ innerChartBlock ec A r' tlo' →
        SA ∩ g ⁻¹' chartBlock ec A r' tlo' ∈ 𝓝[S] x ∧
          blockSheetProjA ec A g '' (SA ∩ g ⁻¹' chartBlock ec A r' tlo') ∈
            𝓝[blockHalfPlane tlo'] (blockSheetProjA ec A g x) := by
  set B₀ : Set (ℝ × ℝ) := Icc (-s) s ×ˢ Icc tl s
  set pA := blockSheetProjA ec A f
  set σ := Function.invFunOn pA SA
  have hB₀poly : IsPolyhedron B₀ := (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  have hσPL : IsPiecewiseAffineOn σ B₀ :=
    hpl.isPiecewiseAffineOn_invFunOn.mono_of_isPolyhedron hB₀poly hB₀
  have hσmem : ∀ q ∈ B₀, σ q ∈ SA ∧ pA (σ q) = q := fun q hq =>
    ⟨hpl.bijOn.surjOn.mapsTo_invFunOn (hB₀ hq), hpl.bijOn.invOn_invFunOn.2 (hB₀ hq)⟩
  have hσpA : ∀ x ∈ SA, σ (pA x) = x := fun x hx => hpl.bijOn.invOn_invFunOn.1 hx
  set e : ℝ × ℝ → ℝ × ℝ × ℝ := fun q => A.linear (δ (σ q)) with he
  have hePL : IsPiecewiseAffineOn e B₀ := by
    have h1 := hδ.comp hσPL
    rw [preimage_univ, inter_univ] at h1
    exact h1.affine_comp A.linear.toAffineMap
  have heLip : LipschitzOnWith (Lℓ * (lam * Lσ)) e B₀ :=
    hAL.comp_lipschitzOnWith (hδL.comp_lipschitzOnWith hσ)
  have heUPL : IsPiecewiseAffineOn (fun q => (e q).1) B₀ :=
    hePL.affine_comp (LinearMap.fst ℝ ℝ (ℝ × ℝ)).toAffineMap
  have hePPL : IsPiecewiseAffineOn (fun q => (e q).2) B₀ :=
    hePL.affine_comp (LinearMap.snd ℝ ℝ (ℝ × ℝ)).toAffineMap
  have heULip : LipschitzOnWith (Lℓ * (lam * Lσ)) (fun q => (e q).1) B₀ := by
    have h := (LipschitzWith.prod_fst (α := ℝ) (β := ℝ × ℝ)).comp_lipschitzOnWith heLip
    rw [one_mul] at h
    exact h
  have hePLip : LipschitzOnWith (Lℓ * (lam * Lσ)) (fun q => (e q).2) B₀ := by
    have h := (LipschitzWith.prod_snd (α := ℝ) (β := ℝ × ℝ)).comp_lipschitzOnWith heLip
    rw [one_mul] at h
    exact h
  obtain ⟨a', hψ, ha'PL, ha'eq, ha'Lip⟩ := exists_graph_of_planeBoxClamp_perturbation hs.le
    (by linarith) hLa ha haLip haT heUPL hePPL heULip hePLip hμ
  set ψ : ℝ × ℝ → ℝ × ℝ := fun w => w + (e (planeBoxClamp s tl w)).2 with hψdef
  set c : ℝ × ℝ → ℝ := fun q => a q + (e q).1
  have hψB : ∀ q ∈ B₀, ψ q = q + (e q).2 := by
    intro q hq
    simp only [hψdef, planeBoxClamp_eq_self hq]
  have hnew : ∀ x ∈ SA, pA x ∈ B₀ → g x ∈ ec.source ∧ A (ec (g x)) = (c (pA x), ψ (pA x)) := by
    intro x hx hq
    obtain ⟨hgs, hgeq⟩ := hG x hx
    refine ⟨hgs, ?_⟩
    have h1 : A (ec (g x)) = A (ec (f x)) + A.linear (δ x) := by
      rw [hgeq, AffineEquiv.apply_add_eq_add_linear]
    have h2 : A (ec (f x)) = (a (pA x), pA x) := Prod.ext (hgraph x hx) rfl
    have h3 : A.linear (δ x) = e (pA x) := by
      simp only [he, hσpA x hx]
    rw [h1, h2, h3, hψB _ hq]
    rfl
  have hc : IsPiecewiseAffineOn c B₀ :=
    (ha.mono_of_isPolyhedron hB₀poly (subset_univ _)).add heUPL
  have ha' : ∀ q ∈ B₀, a' (ψ q) = c q := by
    intro q hq
    rw [hψB q hq]
    exact ha'eq q hq
  have hlow' : tlo' = 0 → tl = 0 ∧ (∀ x ∈ SA, 0 ≤ (pA x).2) ∧
      (∀ q : ℝ × ℝ, q.2 < 0 → (ψ q).2 < 0) ∧ ∀ x ∈ SA, 0 ≤ (A (ec (g x))).2.2 := by
    intro h0
    obtain ⟨htl0, hpos, hfr, hg0⟩ := hlow h0
    refine ⟨htl0, hpos, fun q hq => ?_, hg0⟩
    have hclB : planeBoxClamp s tl q ∈ B₀ := planeBoxClamp_mem hs.le (by linarith) q
    have hcl2 : (planeBoxClamp s tl q).2 = 0 := by
      change max tl (min s q.2) = 0
      rw [htl0]
      exact max_eq_left ((min_le_right _ _).trans hq.le)
    obtain ⟨hσS, hσq⟩ := hσmem _ hclB
    have hf0 : (A (ec (f (σ (planeBoxClamp s tl q))))).2.2 = 0 := by
      have h := congrArg Prod.snd hσq
      change (A (ec (f (σ (planeBoxClamp s tl q))))).2.2 = (planeBoxClamp s tl q).2 at h
      rw [h, hcl2]
    have he0 : (e (planeBoxClamp s tl q)).2.2 = 0 := hfr _ hσS hf0
    change q.2 + (e (planeBoxClamp s tl q)).2.2 < 0
    rw [he0, add_zero]
    exact hq
  obtain ⟨hC1, hC2, hC3⟩ := blockSheetProjA_perturbation hpl hB₀ hψ hc ha' hnew hbox hr'
    htlo' hlow' hSnhds
  exact ⟨a', ha'PL, ha'Lip, hC1, hC2, hC3⟩

theorem mem_blockBox_add_of_norm_sub_le {w w' : ℝ × ℝ × ℝ} {ρ t d : ℝ}
    (hw : w ∈ blockBox ρ t) (hd : ‖w - w'‖ ≤ d) : w' ∈ blockBox (ρ + d) (t - d) := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  have d1 : |w.1 - w'.1| ≤ d := (norm_fst_le (w - w')).trans hd
  have d2 : |w.2.1 - w'.2.1| ≤ d :=
    ((norm_fst_le (w - w').2).trans (norm_snd_le (w - w'))).trans hd
  have d3 : |w.2.2 - w'.2.2| ≤ d :=
    ((norm_snd_le (w - w').2).trans (norm_snd_le (w - w'))).trans hd
  have e1 := abs_sub_abs_le_abs_sub w'.1 w.1
  have e2 := abs_sub_abs_le_abs_sub w'.2.1 w.2.1
  rw [abs_sub_comm] at e1 e2
  obtain ⟨e3, e4⟩ := abs_le.mp d3
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem blockBox_mono {ρ ρ' t t' : ℝ} (hρ : ρ ≤ ρ') (ht : t' ≤ t) :
    blockBox ρ t ⊆ blockBox ρ' t' := by
  rintro w ⟨h1, h2, h3, h4⟩
  exact ⟨h1.trans hρ, h2.trans hρ, ht.trans h3, h4.trans hρ⟩

theorem perturbed_margin_le {La Lb η cA cB μ₀ μA μB : ℝ} (hLa : 0 ≤ La) (hLb : 0 ≤ Lb)
    (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) (hμA0 : 0 ≤ μA) (hμB0 : 0 ≤ μB) (hμA : μA ≤ μ₀)
    (hμB : μB ≤ μ₀) (hμ₀1 : μ₀ ≤ 1 / 2)
    (hμ₀2 : μ₀ * (4 * (cA * Lb + cB * La + cA * cB) + 4) ≤ η) (hmar : La * Lb ≤ 1 - η) :
    (La + 2 * cA * μA) * (Lb + 2 * cB * μB) ≤ 1 - η / 2 := by
  have hμ₀0 : 0 ≤ μ₀ := hμA0.trans hμA
  have e1 : La + 2 * cA * μA ≤ La + 2 * cA * μ₀ := by
    have := mul_le_mul_of_nonneg_left hμA (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hcA)
    linarith
  have e2 : Lb + 2 * cB * μB ≤ Lb + 2 * cB * μ₀ := by
    have := mul_le_mul_of_nonneg_left hμB (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hcB)
    linarith
  have hprod : (La + 2 * cA * μA) * (Lb + 2 * cB * μB) ≤
      (La + 2 * cA * μ₀) * (Lb + 2 * cB * μ₀) :=
    mul_le_mul e1 e2 (add_nonneg hLb (mul_nonneg (mul_nonneg (by norm_num) hcB) hμB0))
      (add_nonneg hLa (mul_nonneg (mul_nonneg (by norm_num) hcA) hμ₀0))
  have hsq : 4 * cA * cB * μ₀ ^ 2 ≤ 2 * cA * cB * μ₀ := by
    have h1 : 0 ≤ cA * cB * μ₀ := mul_nonneg (mul_nonneg hcA hcB) hμ₀0
    nlinarith
  nlinarith [hprod, hsq, hμ₀2, hmar, hμ₀0]

theorem IsStableCrossingBlock.exists_pos_squares_subset_sheetProj
    {f : EuclideanSpace ℝ (Fin 2) → M} {S SA SB : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) {y₀ : M}
    (hy₀ : y₀ ∈ doublePointSet f S) (hy₀s : y₀ ∈ ec.source) (hA0 : A (ec y₀) = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
      Icc (-s) s ×ˢ Icc (tlo * (s / r)) s ⊆ blockSheetProjA ec A f '' SA ∧
        Icc (-s) s ×ˢ Icc (tlo * (s / r)) s ⊆ blockSheetProjB ec A f '' SB := by
  obtain ⟨hr, -, -, -, -, -, -, hside, -, -, -, -, -, -, hnA, hnB, -, -, -, -⟩ := id h
  have htlo : tlo = -r ∨ tlo = 0 := hside.imp (fun h => h.1) (fun h => h.1)
  have htle : tlo ≤ 0 := by rcases htlo with ht | ht <;> linarith
  have htge : -r ≤ tlo := by rcases htlo with ht | ht <;> linarith
  have h0box : ∀ ρ : ℝ, 0 ≤ ρ → ∀ t : ℝ, t ≤ 0 → (0 : ℝ × ℝ × ℝ) ∈ blockBox ρ t := by
    intro ρ hρ t ht
    change |(0 : ℝ)| ≤ ρ ∧ |(0 : ℝ)| ≤ ρ ∧ t ≤ 0 ∧ (0 : ℝ) ≤ ρ
    rw [abs_zero]
    exact ⟨hρ, hρ, ht, hρ⟩
  have hy₀B : y₀ ∈ chartBlock ec A r tlo := by
    refine ⟨hy₀s, ?_⟩
    rw [mem_preimage, mem_preimage, hA0]
    exact h0box r hr.le tlo htle
  have hy₀in : y₀ ∈ innerChartBlock ec A r tlo := by
    refine ⟨hy₀s, ?_⟩
    rw [mem_preimage, mem_preimage, hA0]
    exact h0box (r / 2) (by linarith) (tlo / 2) (by linarith)
  obtain ⟨⟨xA, hxA, hfxA⟩, ⟨xB, hxB, hfxB⟩⟩ :=
    sheets_nonempty_of_isStableCrossingBlock h hy₀ hy₀B
  have hfxA' : f xA = y₀ := hfxA
  have hfxB' : f xB = y₀ := hfxB
  have hpA0 : blockSheetProjA ec A f xA = 0 := by
    change ((A (ec (f xA))).2.1, (A (ec (f xA))).2.2) = 0
    rw [hfxA', hA0]
    rfl
  have hpB0 : blockSheetProjB ec A f xB = 0 := by
    change ((A (ec (f xB))).1, (A (ec (f xB))).2.2) = 0
    rw [hfxB', hA0]
    rfl
  have himA := (hnA xA hxA (by rw [hfxA']; exact hy₀in)).2
  have himB := (hnB xB hxB (by rw [hfxB']; exact hy₀in)).2
  rw [hpA0] at himA
  rw [hpB0] at himB
  obtain ⟨εA, hεA, hballA⟩ := Metric.mem_nhdsWithin_iff.mp himA
  obtain ⟨εB, hεB, hballB⟩ := Metric.mem_nhdsWithin_iff.mp himB
  refine ⟨min εA εB, lt_min hεA hεB, fun s hs hsε => ?_⟩
  have hsA : s < εA := hsε.trans_le (min_le_left _ _)
  have hsB : s < εB := hsε.trans_le (min_le_right _ _)
  have hsr0 : 0 ≤ s / r := (div_pos hs hr).le
  have htls : -s ≤ tlo * (s / r) := by
    have h1 : -r * (s / r) = -s := by rw [neg_mul, mul_div_cancel₀ s hr.ne']
    have h2 : -r * (s / r) ≤ tlo * (s / r) := mul_le_mul_of_nonneg_right htge hsr0
    linarith
  have hmem : ∀ q ∈ Icc (-s) s ×ˢ Icc (tlo * (s / r)) s,
      ‖q‖ ≤ s ∧ q ∈ blockHalfPlane tlo := by
    intro q hq
    refine ⟨?_, fun h0 => ?_⟩
    · rw [Prod.norm_def]
      exact max_le (abs_le.mpr ⟨hq.1.1, hq.1.2⟩) (abs_le.mpr ⟨by linarith [hq.2.1], hq.2.2⟩)
    · have h1 := hq.2.1
      rw [h0, zero_mul] at h1
      exact h1
  refine ⟨fun q hq => hballA ⟨?_, (hmem q hq).2⟩, fun q hq => hballB ⟨?_, (hmem q hq).2⟩⟩
  · rw [mem_ball, dist_zero_right]
    linarith [(hmem q hq).1]
  · rw [mem_ball, dist_zero_right]
    linarith [(hmem q hq).1]

theorem exists_perturbed_blockSheet_of_block {f g : EuclideanSpace ℝ (Fin 2) → M}
    {S SA : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {A A₁ : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ}
    {r tlo s r' tlo' La : ℝ} {a : ℝ × ℝ → ℝ} {Lσ Lt Lℓ lam : NNReal}
    {δ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r / 2) (hr' : r' = s / 4)
    (htlo : tlo = -r ∨ tlo = 0) (htlo' : tlo' = tlo * (r' / r))
    (hA₁box : ∀ ρ t, chartBlock ec A₁ ρ t = chartBlock ec A ρ t)
    (hA₁t : ∀ z, (A₁ z).2.2 = (A z).2.2)
    (hA₁mem : ∀ z ρ t, A₁ z ∈ blockBox ρ t ↔ A z ∈ blockBox ρ t)
    (hLa : 0 ≤ La) (hgraph : ∀ x ∈ SA, (A₁ (ec (f x))).1 = a (blockSheetProjA ec A₁ f x))
    (hpl : IsPLHomeomorphOn (blockSheetProjA ec A₁ f) SA (blockSheetProjA ec A₁ f '' SA))
    (ha : IsPiecewiseAffineOn a univ)
    (haLip : ∀ v v' t : ℝ, |a (v, t) - a (v', t)| ≤ La * |v - v'|)
    (hsq : Icc (-s) s ×ˢ Icc (tlo * (s / r)) s ⊆ blockSheetProjA ec A₁ f '' SA)
    (hσ : LipschitzOnWith Lσ (Function.invFunOn (blockSheetProjA ec A₁ f) SA)
      (Icc (-s) s ×ˢ Icc (tlo * (s / r)) s))
    (haT : LipschitzOnWith Lt a (Icc (-s) s ×ˢ Icc (tlo * (s / r)) s))
    (hAL : LipschitzWith Lℓ A₁.linear)
    (hδ : IsPiecewiseAffineOn δ univ) (hδL : LipschitzWith lam δ)
    (hμ : ((Lℓ * (lam * Lσ) : NNReal) : ℝ) ≤ 1 / 2)
    (hSA : ∀ x ∈ SA, x ∈ S ∧ f x ∈ chartBlock ec A r tlo)
    (hside0 : tlo = 0 → (∀ z, (A z).2.2 = ℓ z) ∧
      ∀ x ∈ SA, (x ∈ frontier S ↔ (A (ec (f x))).2.2 = 0))
    (hnb : ∀ x ∈ SA, f x ∈ innerChartBlock ec A r tlo → SA ∈ 𝓝[S] x)
    (hclose : ∀ x ∈ S, g x ∈ chartBlock ec A r' tlo' →
      f x ∈ ec.source ∧ ‖A (ec (g x)) - A (ec (f x))‖ ≤ s / 4)
    (hG1' : tlo = 0 → ∀ x ∈ S, f x ∈ ec.source → 0 ≤ ℓ (ec (f x)))
    (hG : ∀ x ∈ SA, g x ∈ ec.source ∧ ec (g x) = ec (f x) + δ x)
    (hG4 : tlo = 0 → ∀ x ∈ SA, 0 ≤ ℓ (ec (g x)) ∧ (x ∈ frontier S ↔ ℓ (ec (g x)) = 0)) :
    ∃ a' : ℝ × ℝ → ℝ, IsPiecewiseAffineOn a' univ ∧
      (∀ v v' t : ℝ, |a' (v, t) - a' (v', t)| ≤
        (La + 2 * (La + Lt + 1) * ((Lℓ * (lam * Lσ) : NNReal) : ℝ)) * |v - v'|) ∧
      (∀ x ∈ SA ∩ g ⁻¹' chartBlock ec A r' tlo', (A₁ (ec (g x))).1 =
        a' ((A₁ (ec (g x))).2.1, (A₁ (ec (g x))).2.2)) ∧
      IsPLHomeomorphOn (blockSheetProjA ec A₁ g) (SA ∩ g ⁻¹' chartBlock ec A r' tlo')
        (blockSheetProjA ec A₁ g '' (SA ∩ g ⁻¹' chartBlock ec A r' tlo')) ∧
      ∀ x ∈ SA ∩ g ⁻¹' chartBlock ec A r' tlo', g x ∈ innerChartBlock ec A r' tlo' →
        SA ∩ g ⁻¹' chartBlock ec A r' tlo' ∈ 𝓝[S] x ∧
          blockSheetProjA ec A₁ g '' (SA ∩ g ⁻¹' chartBlock ec A r' tlo') ∈
            𝓝[blockHalfPlane tlo'] (blockSheetProjA ec A₁ g x) := by
  have hr'0 : 0 < r' := by
    rw [hr']
    exact div_pos hs (by norm_num)
  have hr'r : 0 < r' / r := div_pos hr'0 hr
  have htle : tlo ≤ 0 := by rcases htlo with ht | ht <;> linarith
  have htlo'eq : tlo' = -r' ∨ tlo' = 0 := by
    rcases htlo with ht | ht
    · left
      rw [htlo', ht, neg_mul, mul_div_cancel₀ r' hr.ne']
    · right
      rw [htlo', ht, zero_mul]
  have htlo'0 : tlo' = 0 → tlo = 0 := by
    intro h0
    rw [htlo'] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · exact absurd h1 hr'r.ne'
  have htlo'ge : -r' ≤ tlo' := by rcases htlo'eq with ht | ht <;> linarith
  have htlo'le : tlo' ≤ 0 := by rcases htlo'eq with ht | ht <;> linarith
  have htl_neg : tlo ≠ 0 → tlo * (s / r) = -s := by
    intro ht
    rcases htlo with ht' | ht'
    · rw [ht', neg_mul, mul_div_cancel₀ s hr.ne']
    · exact absurd ht' ht
  have hA₁inner : ∀ ρ t, innerChartBlock ec A₁ ρ t = innerChartBlock ec A ρ t :=
    fun ρ t => hA₁box (ρ / 2) (t / 2)
  have hfbox : ∀ x ∈ S, g x ∈ chartBlock ec A r' tlo' → f x ∈ ec.source ∧
      A (ec (f x)) ∈ blockBox (s / 2) (-(s / 2)) := by
    intro x hx hxN
    obtain ⟨hfs, hd⟩ := hclose x hx hxN
    exact ⟨hfs, blockBox_mono (by linarith) (by linarith)
      (mem_blockBox_add_of_norm_sub_le hxN.2 hd)⟩
  have hfinner : ∀ x ∈ S, g x ∈ innerChartBlock ec A r' tlo' →
      f x ∈ innerChartBlock ec A r tlo := by
    intro x hx hxin
    have hxN : g x ∈ chartBlock ec A r' tlo' :=
      chartBlock_mono_of_half ec A hr'0.le htlo'le hxin
    obtain ⟨hfs, hd⟩ := hclose x hx hxN
    obtain ⟨f1, f2, f3, f4⟩ := mem_blockBox_add_of_norm_sub_le hxin.2 hd
    refine ⟨hfs, f1.trans (by linarith), f2.trans (by linarith), ?_, f4.trans (by linarith)⟩
    rcases htlo with ht | ht
    · rw [ht]
      linarith
    · rw [ht, zero_div, (hside0 ht).1]
      exact hG1' ht x hx hfs
  have hbox : ∀ x ∈ SA, g x ∈ chartBlock ec A₁ r' tlo' →
      |(blockSheetProjA ec A₁ f x).1| < s ∧ (blockSheetProjA ec A₁ f x).2 < s ∧
        (tlo * (s / r) < (blockSheetProjA ec A₁ f x).2 ∨ tlo' = 0) := by
    intro x hx hxN
    rw [hA₁box] at hxN
    obtain ⟨-, hb⟩ := hfbox x (hSA x hx).1 hxN
    obtain ⟨-, b2, b3, b4⟩ := (hA₁mem _ _ _).2 hb
    refine ⟨?_, ?_, ?_⟩
    · change |(A₁ (ec (f x))).2.1| < s
      linarith
    · change (A₁ (ec (f x))).2.2 < s
      linarith
    · by_cases ht : tlo' = 0
      · exact Or.inr ht
      · left
        have htlo0 : tlo ≠ 0 := fun h0 => ht (by rw [htlo', h0, zero_mul])
        rw [htl_neg htlo0]
        change -s < (A₁ (ec (f x))).2.2
        linarith
  have hlow : tlo' = 0 → tlo * (s / r) = 0 ∧ (∀ x ∈ SA, 0 ≤ (blockSheetProjA ec A₁ f x).2) ∧
      (∀ x ∈ SA, (A₁ (ec (f x))).2.2 = 0 → (A₁.linear (δ x)).2.2 = 0) ∧
      ∀ x ∈ SA, 0 ≤ (A₁ (ec (g x))).2.2 := by
    intro h0
    have ht := htlo'0 h0
    obtain ⟨hAℓ, hfr⟩ := hside0 ht
    refine ⟨by rw [ht, zero_mul], fun x hx => ?_, fun x hx hx0 => ?_, fun x hx => ?_⟩
    · obtain ⟨-, -, -, hb3, -⟩ := (hSA x hx).2
      rw [ht] at hb3
      change 0 ≤ (A₁ (ec (f x))).2.2
      rw [hA₁t]
      exact hb3
    · have hx0' : (A (ec (f x))).2.2 = 0 := by rw [← hA₁t]; exact hx0
      have hxfr : x ∈ frontier S := (hfr x hx).2 hx0'
      have hg0 : (A₁ (ec (g x))).2.2 = 0 := by
        rw [hA₁t, hAℓ]
        exact (hG4 ht x hx).2.1 hxfr
      have e := AffineEquiv.apply_add_eq_add_linear A₁ (ec (f x)) (δ x)
      rw [← (hG x hx).2] at e
      have e2 := congrArg (fun w : ℝ × ℝ × ℝ => w.2.2) e
      simp only [Prod.snd_add] at e2
      linarith
    · rw [hA₁t, hAℓ]
      exact (hG4 ht x hx).1
  have hSnhds : ∀ x ∈ SA, g x ∈ innerChartBlock ec A₁ r' tlo' → SA ∈ 𝓝[S] x := by
    intro x hx hxin
    rw [hA₁inner] at hxin
    exact hnb x hx (hfinner x (hSA x hx).1 hxin)
  have hS1 := exists_perturbed_blockSheetA (S := S) (SA := SA) (A := A₁) (a := a) (g := g)
    (r' := r') (tlo' := tlo') hs (mul_nonpos_of_nonpos_of_nonneg htle (div_pos hs hr).le) hLa
    hgraph hpl ha haLip hsq hσ haT hAL hδ hδL hμ hG hbox hr'0 htlo'eq hlow hSnhds
  rw [hA₁box, hA₁inner] at hS1
  exact hS1

theorem IsStableCrossingBlock.perturbation_of_squares {f g : EuclideanSpace ℝ (Fin 2) → M}
    {S SA SB : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {a b : ℝ × ℝ → ℝ} {La Lb η s r' tlo' μ₀ : ℝ} {LσA LσB LtA LtB LℓA LℓB lam : NNReal}
    {δA δB : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hs : 0 < s) (hsr : s ≤ r / 2) (hr' : r' = s / 4) (htlo' : tlo' = tlo * (r' / r))
    (hsqA : Icc (-s) s ×ˢ Icc (tlo * (s / r)) s ⊆ blockSheetProjA ec A f '' SA)
    (hsqB : Icc (-s) s ×ˢ Icc (tlo * (s / r)) s ⊆ blockSheetProjB ec A f '' SB)
    (hσA : LipschitzOnWith LσA (Function.invFunOn (blockSheetProjA ec A f) SA)
      (Icc (-s) s ×ˢ Icc (tlo * (s / r)) s))
    (hσB : LipschitzOnWith LσB (Function.invFunOn (blockSheetProjB ec A f) SB)
      (Icc (-s) s ×ˢ Icc (tlo * (s / r)) s))
    (htA : LipschitzOnWith LtA a (Icc (-s) s ×ˢ Icc (tlo * (s / r)) s))
    (htB : LipschitzOnWith LtB b (Icc (-s) s ×ˢ Icc (tlo * (s / r)) s))
    (hALA : LipschitzWith LℓA A.linear) (hALB : LipschitzWith LℓB (A.trans blockSwap).linear)
    (hμA : ((LℓA * (lam * LσA) : NNReal) : ℝ) ≤ μ₀)
    (hμB : ((LℓB * (lam * LσB) : NNReal) : ℝ) ≤ μ₀) (hμ₀1 : μ₀ ≤ 1 / 2)
    (hμ₀2 : μ₀ * (4 * ((La + LtA + 1) * Lb + (Lb + LtB + 1) * La +
      (La + LtA + 1) * (Lb + LtB + 1)) + 4) ≤ η)
    (hδA : IsPiecewiseAffineOn δA univ) (hδAL : LipschitzWith lam δA)
    (hδB : IsPiecewiseAffineOn δB univ) (hδBL : LipschitzWith lam δB)
    (hclose : ∀ x ∈ S, g x ∈ chartBlock ec A r' tlo' →
      f x ∈ ec.source ∧ ‖A (ec (g x)) - A (ec (f x))‖ ≤ s / 4)
    (hG1' : tlo = 0 → ∀ x ∈ S, f x ∈ ec.source → 0 ≤ ℓ (ec (f x)))
    (hGA : ∀ x ∈ SA, g x ∈ ec.source ∧ ec (g x) = ec (f x) + δA x)
    (hGB : ∀ x ∈ SB, g x ∈ ec.source ∧ ec (g x) = ec (f x) + δB x)
    (hG4 : tlo = 0 → ∀ x ∈ SA ∪ SB,
      0 ≤ ℓ (ec (g x)) ∧ (x ∈ frontier S ↔ ℓ (ec (g x)) = 0)) :
    ∃ (a' b' : ℝ × ℝ → ℝ) (La' Lb' : ℝ),
      IsStableCrossingBlock g S ec ℓ BdM A r' tlo' (SA ∩ g ⁻¹' chartBlock ec A r' tlo')
        (SB ∩ g ⁻¹' chartBlock ec A r' tlo') a' b' La' Lb' (η / 2) := by
  obtain ⟨hr, hη, hLa, hLb, hmar, hcpt, hsrc, hside, hpre, hdisj, hgrA, hgrB, hplA, hplB, hnA,
    hnB, hLipa, hLipb, hpa, hpb⟩ := h
  have htlo : tlo = -r ∨ tlo = 0 := hside.imp (fun h => h.1) (fun h => h.1)
  have hsideA : tlo = 0 → (∀ z, (A z).2.2 = ℓ z) ∧
      ∀ x ∈ SA ∪ SB, (x ∈ frontier S ↔ (A (ec (f x))).2.2 = 0) := by
    intro ht
    rcases hside with ⟨ht', -⟩ | ⟨-, hz, hfr⟩
    · exfalso
      linarith
    · exact ⟨hz, hfr⟩
  have hSAS : ∀ x ∈ SA, x ∈ S ∧ f x ∈ chartBlock ec A r tlo := by
    intro x hx
    have h1 : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by
      rw [hpre]
      exact Or.inl hx
    exact h1
  have hSBS : ∀ x ∈ SB, x ∈ S ∧ f x ∈ chartBlock ec A r tlo := by
    intro x hx
    have h1 : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by
      rw [hpre]
      exact Or.inr hx
    exact h1
  have hr'0 : 0 < r' := by
    rw [hr']
    exact div_pos hs (by norm_num)
  have hr'r1 : r' / r ≤ 1 := (div_le_one hr).mpr (by linarith)
  have htle : tlo ≤ 0 := by rcases htlo with ht | ht <;> linarith
  have htlotlo' : tlo ≤ tlo' := by
    have h1 : tlo * 1 ≤ tlo * (r' / r) := mul_le_mul_of_nonpos_left hr'r1 htle
    rw [htlo']
    linarith
  have hsubB : chartBlock ec A r' tlo' ⊆ chartBlock ec A r tlo := by
    rintro z ⟨hzs, hzb⟩
    exact ⟨hzs, blockBox_mono (by linarith) htlotlo' hzb⟩
  obtain ⟨a', ha'PL, ha'Lip, hC1A, hC2A, hC3A⟩ := exists_perturbed_blockSheet_of_block
    (A := A) (A₁ := A) (a := a) hr hs hsr hr' htlo htlo' (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ _ => Iff.rfl) hLa hgrA hplA hpa hLipa hsqA hσA htA hALA hδA hδAL
    (hμA.trans hμ₀1) hSAS (fun ht => ⟨(hsideA ht).1, fun x hx => (hsideA ht).2 x (Or.inl hx)⟩)
    (fun x hx hfin => (hnA x hx hfin).1) hclose hG1' hGA
    (fun ht x hx => hG4 ht x (Or.inl hx))
  obtain ⟨b', hb'PL, hb'Lip, hC1B, hC2B, hC3B⟩ := exists_perturbed_blockSheet_of_block
    (A := A) (A₁ := A.trans blockSwap) (a := b) hr hs hsr hr' htlo htlo'
    (chartBlock_trans_blockSwap ec A) (fun _ => rfl) (fun _ _ _ => blockSwap_mem_blockBox_iff)
    hLb hgrB hplB hpb hLipb hsqB hσB htB hALB hδB hδBL (hμB.trans hμ₀1) hSBS
    (fun ht => ⟨(hsideA ht).1, fun x hx => (hsideA ht).2 x (Or.inr hx)⟩)
    (fun x hx hfin => (hnB x hx hfin).1) hclose hG1' hGB
    (fun ht x hx => hG4 ht x (Or.inr hx))
  have hLtA0 : (0 : ℝ) ≤ LtA := NNReal.coe_nonneg _
  have hLtB0 : (0 : ℝ) ≤ LtB := NNReal.coe_nonneg _
  have hcA0 : (0 : ℝ) ≤ La + LtA + 1 := by linarith
  have hcB0 : (0 : ℝ) ≤ Lb + LtB + 1 := by linarith
  have hμA0 : (0 : ℝ) ≤ ((LℓA * (lam * LσA) : NNReal) : ℝ) := NNReal.coe_nonneg _
  have hμB0 : (0 : ℝ) ≤ ((LℓB * (lam * LσB) : NNReal) : ℝ) := NNReal.coe_nonneg _
  have hmar' := perturbed_margin_le hLa hLb hcA0 hcB0 hμA0 hμB0 hμA hμB hμ₀1 hμ₀2 hmar
  refine ⟨a', b', La + 2 * (La + LtA + 1) * ((LℓA * (lam * LσA) : NNReal) : ℝ),
    Lb + 2 * (Lb + LtB + 1) * ((LℓB * (lam * LσB) : NNReal) : ℝ), hr'0, half_pos hη,
    add_nonneg hLa (mul_nonneg (mul_nonneg (by norm_num) hcA0) hμA0),
    add_nonneg hLb (mul_nonneg (mul_nonneg (by norm_num) hcB0) hμB0), hmar',
    hcpt.of_isClosed_subset isClosed_closure (closure_mono hsubB),
    (closure_mono hsubB).trans hsrc, ?_, ?_, hdisj.mono inter_subset_left inter_subset_left,
    hC1A, hC1B, hC2A, hC2B, hC3A, hC3B, ha'Lip, hb'Lip, ha'PL, hb'PL⟩
  · rcases htlo with ht | ht
    · left
      refine ⟨?_, ?_⟩
      · rw [htlo', ht, neg_mul, mul_div_cancel₀ r' hr.ne']
      · rcases hside with ⟨-, hdis⟩ | ⟨ht0, -⟩
        · exact hdis.mono_left hsubB
        · exfalso
          linarith
    · right
      obtain ⟨hAℓ, -⟩ := hsideA ht
      refine ⟨by rw [htlo', ht, zero_mul], hAℓ, fun x hx => ?_⟩
      have hxAB : x ∈ SA ∪ SB := hx.imp (fun h => h.1) (fun h => h.1)
      rw [hAℓ]
      exact (hG4 ht x hxAB).2
  · ext x
    constructor
    · rintro ⟨hxS, hxN⟩
      obtain ⟨hfs, hb⟩ := hclose x hxS hxN
      have hfx : f x ∈ chartBlock ec A r tlo := by
        refine ⟨hfs, ?_⟩
        obtain ⟨f1, f2, f3, f4⟩ := mem_blockBox_add_of_norm_sub_le hxN.2 hb
        refine ⟨f1.trans (by linarith), f2.trans (by linarith), ?_, f4.trans (by linarith)⟩
        rcases htlo with ht | ht
        · have : -r' ≤ tlo' := by
            rw [htlo', ht, neg_mul, mul_div_cancel₀ r' hr.ne']
          rw [ht]
          linarith
        · rw [ht, (hsideA ht).1]
          exact hG1' ht x hxS hfs
      have hxAB : x ∈ SA ∪ SB := by
        rw [← hpre]
        exact ⟨hxS, hfx⟩
      rcases hxAB with hxA' | hxB'
      · exact Or.inl ⟨hxA', hxN⟩
      · exact Or.inr ⟨hxB', hxN⟩
    · rintro (⟨hxA', hxN⟩ | ⟨hxB', hxN⟩)
      · exact ⟨(hSAS x hxA').1, hxN⟩
      · exact ⟨(hSBS x hxB').1, hxN⟩

theorem IsStableCrossingBlock.exists_perturbation {f : EuclideanSpace ℝ (Fin 2) → M}
    {S SA SB : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) {y₀ : M}
    (hy₀ : y₀ ∈ doublePointSet f S) (hy₀s : y₀ ∈ ec.source) (hA0 : A (ec y₀) = 0) :
    ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧
      (∀ z ∈ ec.source, ‖A (ec z)‖ < r' / 2 → (tlo = 0 → 0 ≤ (A (ec z)).2.2) →
        z ∈ innerChartBlock ec A r' (tlo * (r' / r))) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ (g : EuclideanSpace ℝ (Fin 2) → M)
          (δA δB : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (lam : NNReal),
          (lam : ℝ) ≤ lam₀ →
          IsPiecewiseAffineOn δA univ → LipschitzWith lam δA →
          IsPiecewiseAffineOn δB univ → LipschitzWith lam δB →
          (∀ x ∈ S, g x ∈ chartBlock ec A r' (tlo * (r' / r)) →
            f x ∈ ec.source ∧ ‖ec (g x) - ec (f x)‖ ≤ ε₀) →
          (tlo = 0 → ∀ x ∈ S, f x ∈ ec.source → 0 ≤ ℓ (ec (f x))) →
          (∀ x ∈ SA, g x ∈ ec.source ∧ ec (g x) = ec (f x) + δA x) →
          (∀ x ∈ SB, g x ∈ ec.source ∧ ec (g x) = ec (f x) + δB x) →
          (tlo = 0 → ∀ x ∈ SA ∪ SB,
            0 ≤ ℓ (ec (g x)) ∧ (x ∈ frontier S ↔ ℓ (ec (g x)) = 0)) →
          ∃ (a' b' : ℝ × ℝ → ℝ) (La' Lb' : ℝ),
            IsStableCrossingBlock g S ec ℓ BdM A r' (tlo * (r' / r))
              (SA ∩ g ⁻¹' chartBlock ec A r' (tlo * (r' / r)))
              (SB ∩ g ⁻¹' chartBlock ec A r' (tlo * (r' / r))) a' b' La' Lb' (η / 2) := by
  obtain ⟨hr, hη, hLa, hLb, -, -, -, hside, -, -, -, -, hplA, hplB, -, -, -, -, hpa, hpb⟩ :=
    id h
  have htlo : tlo = -r ∨ tlo = 0 := hside.imp (fun h => h.1) (fun h => h.1)
  obtain ⟨ε, hε, hsq⟩ := h.exists_pos_squares_subset_sheetProj hy₀ hy₀s hA0
  set s : ℝ := min ε r / 2 with hsdef
  have hs : 0 < s := half_pos (lt_min hε hr)
  have hsε : s < ε := by
    have := min_le_left ε r
    linarith
  have hsr : s ≤ r / 2 := by
    have := min_le_right ε r
    linarith
  obtain ⟨hsqA, hsqB⟩ := hsq s hs hsε
  have hB₀poly : IsPolyhedron (Icc (-s) s ×ˢ Icc (tlo * (s / r)) s) :=
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  obtain ⟨LσA, hσA⟩ := (hplA.isPiecewiseAffineOn_invFunOn.mono_of_isPolyhedron hB₀poly
    hsqA).exists_lipschitzOnWith_of_isPolyhedron hB₀poly
  obtain ⟨LσB, hσB⟩ := (hplB.isPiecewiseAffineOn_invFunOn.mono_of_isPolyhedron hB₀poly
    hsqB).exists_lipschitzOnWith_of_isPolyhedron hB₀poly
  obtain ⟨LtA, htA⟩ := (hpa.mono_of_isPolyhedron hB₀poly
    (subset_univ _)).exists_lipschitzOnWith_of_isPolyhedron hB₀poly
  obtain ⟨LtB, htB⟩ := (hpb.mono_of_isPolyhedron hB₀poly
    (subset_univ _)).exists_lipschitzOnWith_of_isPolyhedron hB₀poly
  set LℓA : NNReal := ‖LinearMap.toContinuousLinearMap A.linear.toLinearMap‖₊
  set LℓB : NNReal := ‖LinearMap.toContinuousLinearMap (A.trans blockSwap).linear.toLinearMap‖₊
  have hALA : LipschitzWith LℓA A.linear :=
    (LinearMap.toContinuousLinearMap A.linear.toLinearMap).lipschitzWith
  have hALB : LipschitzWith LℓB (A.trans blockSwap).linear :=
    (LinearMap.toContinuousLinearMap (A.trans blockSwap).linear.toLinearMap).lipschitzWith
  have hAnorm : ∀ v : EuclideanSpace ℝ (Fin 3), ‖A.linear v‖ ≤ LℓA * ‖v‖ := fun v =>
    (LinearMap.toContinuousLinearMap A.linear.toLinearMap).le_opNorm v
  have hLtA0 : (0 : ℝ) ≤ LtA := NNReal.coe_nonneg _
  have hLtB0 : (0 : ℝ) ≤ LtB := NNReal.coe_nonneg _
  set Q : ℝ := (La + LtA + 1) * Lb + (Lb + LtB + 1) * La + (La + LtA + 1) * (Lb + LtB + 1)
    with hQdef
  have hQ : 0 ≤ Q := by
    have h1 : 0 ≤ La + LtA + 1 := by linarith
    have h2 : 0 ≤ Lb + LtB + 1 := by linarith
    have := mul_nonneg h1 hLb
    have := mul_nonneg h2 hLa
    have := mul_nonneg h1 h2
    linarith
  set μ₀ : ℝ := min (1 / 2) (η / (4 * Q + 4))
  have hμ₀pos : 0 < μ₀ := lt_min (by norm_num) (div_pos hη (by linarith))
  have hμ₀1 : μ₀ ≤ 1 / 2 := min_le_left _ _
  have hμ₀2 : μ₀ * (4 * Q + 4) ≤ η := by
    have h1 : μ₀ ≤ η / (4 * Q + 4) := min_le_right _ _
    rwa [le_div_iff₀ (by linarith)] at h1
  set K : ℝ := LℓA * LσA + LℓB * LσB + 1 with hK
  have hKpos : 0 < K := by
    have := mul_nonneg (NNReal.coe_nonneg LℓA) (NNReal.coe_nonneg LσA)
    have := mul_nonneg (NNReal.coe_nonneg LℓB) (NNReal.coe_nonneg LσB)
    linarith
  set ε₀ : ℝ := s / (4 * (LℓA + 1)) with hε₀
  have hε₀pos : 0 < ε₀ := div_pos hs (by positivity)
  have hLε : (LℓA : ℝ) * ε₀ ≤ s / 4 := by
    rw [hε₀, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [NNReal.coe_nonneg LℓA]
  refine ⟨s / 4, div_pos hs (by norm_num), by linarith, ?_, ε₀, hε₀pos, μ₀ / K,
    div_pos hμ₀pos hKpos, ?_⟩
  · intro z hz hzn hz0
    refine ⟨hz, ?_⟩
    rw [mem_preimage, mem_preimage]
    have h1 := (norm_fst_le (A (ec z))).trans hzn.le
    have h2 := ((norm_fst_le (A (ec z)).2).trans (norm_snd_le (A (ec z)))).trans hzn.le
    have h3 := ((norm_snd_le (A (ec z)).2).trans (norm_snd_le (A (ec z)))).trans hzn.le
    rw [Real.norm_eq_abs] at h1 h2 h3
    have h3' := abs_le.mp h3
    refine ⟨h1, h2, ?_, h3'.2⟩
    rcases htlo with ht | ht
    · have e : tlo * (s / 4 / r) / 2 = -(s / 4 / 2) := by
        rw [ht, neg_mul, mul_div_cancel₀ (s / 4) hr.ne', neg_div]
      rw [e]
      exact h3'.1
    · rw [ht, zero_mul, zero_div]
      exact hz0 ht
  intro g δA δB lam hlam hδA hδAL hδB hδBL hG1 hG1' hGA hGB hG4
  have hlamK : (lam : ℝ) * K ≤ μ₀ := by
    rwa [le_div_iff₀ hKpos] at hlam
  have hμA : ((LℓA * (lam * LσA) : NNReal) : ℝ) ≤ μ₀ := by
    have e : ((LℓA * (lam * LσA) : NNReal) : ℝ) = (lam : ℝ) * (LℓA * LσA) := by
      push_cast
      ring
    rw [e]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg lam)) hlamK
    have := mul_nonneg (NNReal.coe_nonneg LℓB) (NNReal.coe_nonneg LσB)
    rw [hK]
    linarith
  have hμB : ((LℓB * (lam * LσB) : NNReal) : ℝ) ≤ μ₀ := by
    have e : ((LℓB * (lam * LσB) : NNReal) : ℝ) = (lam : ℝ) * (LℓB * LσB) := by
      push_cast
      ring
    rw [e]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg lam)) hlamK
    have := mul_nonneg (NNReal.coe_nonneg LℓA) (NNReal.coe_nonneg LσA)
    rw [hK]
    linarith
  have hclose : ∀ x ∈ S, g x ∈ chartBlock ec A (s / 4) (tlo * (s / 4 / r)) →
      f x ∈ ec.source ∧ ‖A (ec (g x)) - A (ec (f x))‖ ≤ s / 4 := by
    intro x hx hxN
    obtain ⟨hfs, hd⟩ := hG1 x hx hxN
    refine ⟨hfs, ?_⟩
    have e : A (ec (g x)) - A (ec (f x)) = A.linear (ec (g x) - ec (f x)) := by
      have h1 := AffineEquiv.apply_add_eq_add_linear A (ec (f x)) (ec (g x) - ec (f x))
      rw [add_sub_cancel] at h1
      rw [h1, add_sub_cancel_left]
    rw [e]
    calc ‖A.linear (ec (g x) - ec (f x))‖ ≤ LℓA * ‖ec (g x) - ec (f x)‖ := hAnorm _
      _ ≤ LℓA * ε₀ := mul_le_mul_of_nonneg_left hd (NNReal.coe_nonneg _)
      _ ≤ s / 4 := hLε
  exact h.perturbation_of_squares hs hsr rfl rfl hsqA hsqB hσA hσB htA htB hALA hALB hμA hμB
    hμ₀1 hμ₀2 hδA hδAL hδB hδBL hclose hG1' hGA hGB hG4

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear

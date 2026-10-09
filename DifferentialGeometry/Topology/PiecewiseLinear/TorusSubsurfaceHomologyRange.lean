/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TorusSubsurfaceCarrier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] {φ : E3 → Y} {S : Set Y}

open Classical in
theorem IsPLTorus.range_integralSingularHomologyMap_le_or_eq_bot_of_disjoint {ι : Type*} [Finite ι]
    {Θ K W : Set E3} {C : ι → Set E3} (hΘ : IsPLTorus Θ) (hK : IsPLSphere 1 K) (hKΘ : K ⊆ Θ)
    (hKsep : IsPreconnected (Θ \ K)) (hC : ∀ i, IsPLSphere 1 (C i)) (hCΘ : ∀ i, C i ⊆ Θ)
    (hCd : Pairwise fun i j => Disjoint (C i) (C j)) (hCK : ∀ i, Disjoint (C i) K)
    (hWΘ : W ⊆ Θ) (hWc : IsClosed W) (hWK : Disjoint W K)
    (hWfr : W ∩ closure (Θ \ W) ⊆ ⋃ i, C i) (hφ : ContinuousOn φ Θ) (hφi : InjOn φ Θ)
    (hS : φ '' Θ ⊆ S) :
    (∃ i, LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion ((image_mono hWΘ).trans hS), continuous_inclusion _⟩ : C(φ '' W, S))) ≤
      LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion ((image_mono (hCΘ i)).trans hS), continuous_inclusion _⟩ : C(φ '' C i, S)))) ∨
      LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion ((image_mono hWΘ).trans hS), continuous_inclusion _⟩ : C(φ '' W, S))) = ⊥ := by
  obtain ⟨L, hLfin, hL, hLc, hLT⟩ := hΘ.exists_combinatorial_triangulation
  let _ : Finite L.faces := hLfin.to_subtype
  have hLo := hL.isOrientable_euclidean_three L hLc
  have hβ := hΘ.bettiOne_le_two
  rw [← hLT] at hβ
  have hχ := hL.eulerChar_eq_two_sub_bettiOne_of_isOrientable L hLc hLo
  have hKL : K ⊆ L.space := by
    rw [hLT]
    exact hKΘ
  have hKsep' : IsPreconnected (L.space \ K) := by
    rw [hLT]
    exact hKsep
  have hZc : IsClosed (W ∪ ⋃ i, C i) :=
    hWc.union (isClosed_iUnion_of_finite fun i => (hC i).isPolyhedron.isClosed)
  have hKZ : K ⊆ (W ∪ ⋃ i, C i)ᶜ := by
    rintro x hxK (hxW | hxC)
    · exact disjoint_left.mp hWK hxW hxK
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hxC
      exact disjoint_left.mp (hCK i) hi hxK
  have hU : L.space \ (W ∪ ⋃ i, C i) ∈ 𝓝ˢ[L.space] K :=
    mem_nhdsSetWithin.mpr ⟨_, hZc.isOpen_compl, hKZ, fun x hx => ⟨hx.2, hx.1⟩⟩
  obtain ⟨R, hRfin, hR, -, hRc, hRχ, N, ρ, -, -, hNU, -, hρ, -, -, -, hRbd, -, hcover,
      hKm, hKp, hdis⟩ := hL.exists_connected_annulus_complement L hLo hK hKL hKsep' hU
  let _ : Finite R.faces := hRfin.to_subtype
  have hRbd' := hRbd.trans (show ρ '' (K ×ˢ {(-1 : ℝ), 1}) =
      ρ '' (K ×ˢ {(-1 : ℝ)}) ∪ ρ '' (K ×ˢ {(1 : ℝ)}) by
    rw [← singleton_union, prod_union, image_union])
  have hRχ0 : eulerChar R = 0 := by
    have hle := hR.eulerChar_nonpos_of_boundary_eq_union R hRc hKm hKp hdis hRbd'
    omega
  obtain ⟨h, hh, hh0, hh1⟩ :=
    hR.exists_isPLHomeomorphOn_annulus_of_eulerChar_eq_zero R hRc hRχ0 hKm hKp hdis hRbd'
  have hρN : ρ '' (K ×ˢ Icc (-1 : ℝ) 1) = N := hρ.image_eq
  have hKIcc : ∀ t ∈ ({(-1 : ℝ), 1} : Set ℝ), t ∈ Icc (-1 : ℝ) 1 := by
    rintro t (rfl | rfl)
    · exact ⟨le_rfl, by norm_num⟩
    · exact ⟨by norm_num, le_rfl⟩
  have hbdN : ρ '' (K ×ˢ {(-1 : ℝ)}) ∪ ρ '' (K ×ˢ {(1 : ℝ)}) ⊆ N := by
    rw [← hρN]
    rintro _ (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨y, ⟨hy.1, hKIcc _ (Or.inl hy.2)⟩, rfl⟩
    · exact ⟨y, ⟨hy.1, hKIcc _ (Or.inr hy.2)⟩, rfl⟩
  have hRΘ : R.space ⊆ Θ := by
    intro x hx
    have hxL : x ∈ L.space := by
      rw [← hcover]
      exact Or.inr hx
    rwa [hLT] at hxL
  have hNΘ : N ⊆ Θ := by
    intro x hx
    have hxL : x ∈ L.space := by
      rw [← hcover]
      exact Or.inl hx
    rwa [hLT] at hxL
  have hsubR : ∀ X ⊆ Θ, Disjoint X N → X ⊆ R.space := by
    intro X hXΘ hXN x hx
    have hxL : x ∈ L.space := by
      rw [hLT]
      exact hXΘ hx
    rw [← hcover] at hxL
    exact hxL.resolve_left (disjoint_left.mp hXN hx)
  have hWN : Disjoint W N := disjoint_left.mpr fun x hxW hxN => (hNU hxN).2 (Or.inl hxW)
  have hCN : ∀ i, Disjoint (C i) N := fun i =>
    disjoint_left.mpr fun x hxC hxN => (hNU hxN).2 (Or.inr (mem_iUnion.mpr ⟨i, hxC⟩))
  have hWR : W ⊆ R.space := hsubR W hWΘ hWN
  have hCR : ∀ i, C i ⊆ R.space := fun i => hsubR (C i) (hCΘ i) (hCN i)
  have hhs : IsPLHomeomorphOn (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
      R.space (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := hh.symm
  have hopen : ∀ x ∈ R.space, x ∉ N →
      Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) x ∈
        stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1 := by
    intro x hxR hxN
    have hyA := hhs.bijOn.mapsTo hxR
    have hhy := hh.bijOn.invOn_invFunOn.2 hxR
    refine ⟨hyA.1, lt_of_le_of_ne hyA.2.1 fun h0 => hxN ?_,
      lt_of_le_of_ne hyA.2.2 fun h1 => hxN ?_⟩
    · have hx0 : x ∈ h '' (stdSimplexBoundary 2 ×ˢ ({0} : Set ℝ)) := ⟨_, ⟨hyA.1, h0.symm⟩, hhy⟩
      rw [hh0] at hx0
      exact hbdN (Or.inl hx0)
    · have hx1 : x ∈ h '' (stdSimplexBoundary 2 ×ˢ ({1} : Set ℝ)) := ⟨_, ⟨hyA.1, h1⟩, hhy⟩
      rw [hh1] at hx1
      exact hbdN (Or.inr hx1)
  have hC' : ∀ i,
      IsPLSphere 1 (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' C i) :=
    fun i => (hC i).of_isPLHomeomorphOn (hhs.restrict (hC i).isPolyhedron (hCR i))
  have hhC' : ∀ i,
      h '' (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' C i) = C i :=
    fun i => LeftInvOn.image_image (hh.bijOn.invOn_invFunOn.2.mono (hCR i))
  have hC'A : ∀ i, Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' C i ⊆
      stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1 := by
    rintro i _ ⟨x, hx, rfl⟩
    exact hopen x (hCR i hx) (disjoint_left.mp (hCN i) hx)
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hBcpt : IsCompact (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact (isPolyhedron_space _).isCompact
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
  have hhΘ : ∀ p ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1, h p ∈ Θ :=
    fun p hp => hRΘ (hh.bijOn.mapsTo hp)
  have hKmΘ : ρ '' (K ×ˢ {(-1 : ℝ)}) ⊆ Θ := fun x hx => hNΘ (hbdN (Or.inl hx))
  have hWcpt : IsCompact W := hΘ.1.isCompact.of_isClosed_subset hWc hWΘ
  have hKmle : LinearMap.range (integralSingularHomologyMap 1
      (⟨inclusion ((image_mono hWΘ).trans hS), continuous_inclusion _⟩ : C(φ '' W, S))) ≤
    LinearMap.range (integralSingularHomologyMap 1
      (⟨inclusion ((image_mono hKmΘ).trans hS), continuous_inclusion _⟩ :
        C(φ '' (ρ '' (K ×ˢ {(-1 : ℝ)})), S))) := by
    have hmemA : ∀ q ∈ W ×ˢ Icc (0 : ℝ) 1,
        ((Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) q.1).1,
          (1 - q.2) * (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) q.1).2) ∈
            stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := by
      intro q hq
      have hyA := hhs.bijOn.mapsTo (hWR hq.1)
      have ht := hq.2
      refine ⟨hyA.1, mul_nonneg (by linarith [ht.2]) hyA.2.1, ?_⟩
      nlinarith [ht.1, ht.2, hyA.2.1, hyA.2.2, mul_nonneg ht.1 hyA.2.1]
    have hc1 : ContinuousOn (fun q : E3 × ℝ =>
        Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) q.1) (W ×ˢ Icc (0 : ℝ) 1) :=
      (hhs.isPiecewiseAffineOn.continuousOn.mono hWR).comp continuousOn_fst fun q hq => hq.1
    have hc2 : ContinuousOn (fun q : E3 × ℝ =>
        ((Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) q.1).1,
          (1 - q.2) * (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) q.1).2))
        (W ×ˢ Icc (0 : ℝ) 1) :=
      (continuous_fst.comp_continuousOn hc1).prodMk
        ((continuousOn_const.sub continuousOn_snd).mul (continuous_snd.comp_continuousOn hc1))
    have hFc : ContinuousOn (fun q : E3 × ℝ => φ (h
        ((Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) q.1).1,
          (1 - q.2) * (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) q.1).2)))
        (W ×ˢ Icc (0 : ℝ) 1) :=
      hφ.comp (hh.isPiecewiseAffineOn.continuousOn.comp hc2 hmemA) fun q hq => hhΘ _ (hmemA q hq)
    have hF0 : ∀ p ∈ W, φ (h ((Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) p).1,
        (1 - 0) * (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) p).2)) = φ p := by
      intro p hp
      rw [sub_zero, one_mul, Prod.mk.eta, hh.bijOn.invOn_invFunOn.2 (hWR hp)]
    have hle := range_integralSingularHomologyMap_le_of_continuousOn
      (F := fun q : E3 × ℝ => φ (h
        ((Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) q.1).1,
          (1 - q.2) * (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) q.1).2)))
      hWcpt ((image_mono hWΘ).trans hS) ((image_mono hKmΘ).trans hS) hFc
      (fun q hq => hS (mem_image_of_mem φ (hhΘ _ (hmemA q hq))))
      (fun a ha b hb hab => hφi (hWΘ ha) (hWΘ hb) ((hF0 a ha).symm.trans (hab.trans (hF0 b hb))))
      (image_congr fun p hp => hF0 p hp)
      (fun p hp => by
        refine ⟨h ((Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) p).1, 0), ?_, ?_⟩
        · rw [← hh0]
          exact ⟨((Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) p).1, 0),
            ⟨(hhs.bijOn.mapsTo (hWR hp)).1, rfl⟩, rfl⟩
        · simp)
    exact hle
  by_cases hall : ∀ i, ∃ (D : Set ((Fin 3 → ℝ) × ℝ)) (r : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ∧
        r '' stdSimplexBoundary 2 =
          Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' C i
  · right
    choose D' r hr hDA hrb using hall
    obtain ⟨Sg, hSgdef⟩ : ∃ Sg : Set ((Fin 3 → ℝ) × ℝ),
        Sg = Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
      ⟨_, rfl⟩
    have hSg : IsPLSphere 2 Sg := by
      rw [hSgdef]
      exact isPLSphere_stdSimplex_prism_boundary
    have hASg : stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ⊆ Sg := by
      rw [hSgdef]
      exact subset_union_right
    have hcΔ : (fun _ : Fin 3 => (1 / 3 : ℝ)) ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
      ⟨fun _ => by norm_num, by rw [Fin.sum_univ_three]; norm_num⟩
    have hcB : (fun _ : Fin 3 => (1 / 3 : ℝ)) ∉ stdSimplexBoundary 2 := by
      rintro ⟨-, i, hi⟩
      norm_num at hi
    have hptSg : ((fun _ : Fin 3 => (1 / 3 : ℝ)), (0 : ℝ)) ∈ Sg := by
      rw [hSgdef]
      exact Or.inl ⟨hcΔ, Or.inl rfl⟩
    have hptA : ((fun _ : Fin 3 => (1 / 3 : ℝ)), (0 : ℝ)) ∉
        stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := fun hp => hcB hp.1
    have hDSg : ∀ i, D' i ⊆ Sg := fun i => (hDA i).trans hASg
    have hDc : ∀ i, IsClosed (D' i) := fun i => (IsPLBall.isPolyhedron ⟨r i, hr i⟩).isClosed
    have hfr : ∀ i, D' i ∩ closure (Sg \ D' i) =
        Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' C i := fun i => by
      rw [← hrb i]
      exact hSg.inter_closure_sdiff_eq_image_stdSimplexBoundary (hr i) (hDSg i)
    have hin : ∀ i, ∀ x ∈ Sg, x ∉ closure (Sg \ D' i) → x ∈ D' i := fun i x hx hxc => by
      by_contra hxD
      exact hxc (subset_closure ⟨hx, hxD⟩)
    have hside : ∀ i (Z : Set ((Fin 3 → ℝ) × ℝ)), Z ⊆ Sg → IsPreconnected Z →
        Disjoint Z (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' C i) →
        Z ⊆ (closure (Sg \ D' i))ᶜ ∨ Disjoint Z (D' i) := by
      intro i Z hZSg hZ hZC
      have hcov : Z ⊆ (closure (Sg \ D' i))ᶜ ∪ (D' i)ᶜ := by
        intro z hz
        by_cases hzD : z ∈ D' i
        · refine Or.inl fun hcl => disjoint_left.mp hZC hz ?_
          rw [← hfr i]
          exact ⟨hzD, hcl⟩
        · exact Or.inr hzD
      have hemp : Z ∩ ((closure (Sg \ D' i))ᶜ ∩ (D' i)ᶜ) = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun z hz => hz.2.1 (subset_closure ⟨hZSg hz.1, hz.2.2⟩)
      rcases isPreconnected_iff_subset_of_disjoint.mp hZ _ _ isClosed_closure.isOpen_compl
        (hDc i).isOpen_compl hcov hemp with hsub | hsub
      · exact Or.inl hsub
      · exact Or.inr (disjoint_left.mpr fun z hz hzD => hsub hz hzD)
    have hC'conn : ∀ i,
        IsPreconnected (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' C i) :=
      fun i => (hC' i).isPathConnected_one.isConnected.isPreconnected
    have hDconn : ∀ i, IsPreconnected (D' i) :=
      fun i => (IsPLBall.isConnected ⟨r i, hr i⟩).isPreconnected
    have hC'D : ∀ i, Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' C i ⊆ D' i :=
      fun i => by
        rw [← hrb i, ← (hr i).image_eq]
        exact image_mono fun x hx => hx.1
    have hC'disj : ∀ i j, i ≠ j →
        Disjoint (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' C i)
          (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' C j) := by
      intro i j hij
      refine disjoint_left.mpr ?_
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have hba := hhs.bijOn.injOn (hCR j hb) (hCR i ha) hab
      exact disjoint_left.mp (hCd hij) ha (hba ▸ hb)
    have hnest : ∀ i j, D' i ⊆ D' j ∨ D' j ⊆ D' i ∨ Disjoint (D' i) (D' j) := by
      intro i j
      rcases eq_or_ne i j with rfl | hij
      · exact Or.inl Subset.rfl
      have hCC := hC'disj i j hij
      rcases hside i _ ((hC'D j).trans (hDSg j)) (hC'conn j) hCC.symm with hα | hβ
      · rcases hside j _ ((hC'D i).trans (hDSg i)) (hC'conn i) hCC with hγ | hδ
        · exfalso
          have hZ := (hSg.isConnected_sdiff_of_isPLBall_two ⟨r i, hr i⟩ (hDSg i)).isPreconnected
          have hZC : Disjoint (Sg \ D' i)
              (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' C j) :=
            disjoint_left.mpr fun z hz hzC =>
              hz.2 (hin i z ((hC'D j).trans (hDSg j) hzC) (hα hzC))
          rcases hside j _ sdiff_subset hZ hZC with h1 | h1
          · have hpt : ((fun _ : Fin 3 => (1 / 3 : ℝ)), (0 : ℝ)) ∈ Sg \ D' i :=
              ⟨hptSg, fun hp => hptA (hDA i hp)⟩
            exact hptA (hDA j (hin j _ hptSg (h1 hpt)))
          · obtain ⟨x, hx⟩ := (hC' i).nonempty
            have hx' := hx
            rw [← hfr i] at hx'
            obtain ⟨z, hzu, hzZ⟩ :=
              mem_closure_iff.mp hx'.2 _ isClosed_closure.isOpen_compl (hγ hx)
            exact disjoint_left.mp h1 hzZ (hin j z hzZ.1 hzu)
        · rcases hside i _ (hDSg j) (hDconn j) hδ.symm with h2 | h2
          · exact Or.inr (Or.inl fun x hx => hin i x (hDSg j hx) (h2 hx))
          · exfalso
            obtain ⟨x, hx⟩ := (hC' j).nonempty
            exact disjoint_left.mp h2 (hC'D j hx)
              (hin i x ((hC'D j).trans (hDSg j) hx) (hα hx))
      · rcases hside j _ ((hC'D i).trans (hDSg i)) (hC'conn i) hCC with hγ | hδ
        · rcases hside j _ (hDSg i) (hDconn i) hβ.symm with h2 | h2
          · exact Or.inl fun x hx => hin j x (hDSg i hx) (h2 hx)
          · exfalso
            obtain ⟨x, hx⟩ := (hC' i).nonempty
            exact disjoint_left.mp h2 (hC'D i hx)
              (hin j x ((hC'D i).trans (hDSg i) hx) (hγ hx))
        · rcases hside j _ (hDSg i) (hDconn i) hβ.symm with h2 | h2
          · exfalso
            obtain ⟨x, hx⟩ := (hC' i).nonempty
            exact disjoint_left.mp hδ hx
              (hin j x ((hC'D i).trans (hDSg i) hx) (h2 (hC'D i hx)))
          · exact Or.inr (Or.inr h2)
    have hfinD : (range D').Finite := finite_range D'
    obtain ⟨M, hMdef⟩ : ∃ M : Set (Set ((Fin 3 → ℝ) × ℝ)),
        M = {b | Maximal (· ∈ range D') b} := ⟨_, rfl⟩
    have hMmax : ∀ b ∈ M, Maximal (· ∈ range D') b := by
      rw [hMdef]
      exact fun b hb => hb
    have hMmem : ∀ b, Maximal (· ∈ range D') b → b ∈ M := by
      rw [hMdef]
      exact fun b hb => hb
    have hMfin : M.Finite := hfinD.subset fun b hb => (hMmax b hb).1
    have hMdisj : ∀ b₁ ∈ M, ∀ b₂ ∈ M, b₁ ≠ b₂ → Disjoint b₁ b₂ := by
      intro b₁ hb₁ b₂ hb₂ hne
      obtain ⟨i, rfl⟩ := (hMmax b₁ hb₁).1
      obtain ⟨j, rfl⟩ := (hMmax b₂ hb₂).1
      rcases hnest i j with h1 | h1 | h1
      · exact absurd (Subset.antisymm h1 ((hMmax _ hb₁).2 (hMmax _ hb₂).1 h1)) hne
      · exact absurd (Subset.antisymm ((hMmax _ hb₂).2 (hMmax _ hb₁).1 h1) h1) hne
      · exact h1
    have hMD : ∀ b : M, ∃ i, D' i = (b : Set ((Fin 3 → ℝ) × ℝ)) := fun b => (hMmax b b.2).1
    have : Finite M := hMfin.to_subtype
    have hMball : ∀ b : M, IsPLBall 2 (b : Set ((Fin 3 → ℝ) × ℝ)) := fun b => by
      obtain ⟨i, hi⟩ := hMD b
      rw [← hi]
      exact ⟨r i, hr i⟩
    have hMA : ∀ b : M, (b : Set ((Fin 3 → ℝ) × ℝ)) ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
      fun b => by
        obtain ⟨i, hi⟩ := hMD b
        rw [← hi]
        exact hDA i
    have hQ := hSg.isConnected_sdiff_iUnion_of_isPLBall_two hMball (fun b => (hMA b).trans hASg)
      (fun b₁ b₂ hne => hMdisj _ b₁.2 _ b₂.2 (Subtype.coe_injective.ne hne))
    have hunion : ∀ x, x ∈ (⋃ b : M, (b : Set ((Fin 3 → ℝ) × ℝ))) ↔ x ∈ ⋃ i, D' i := by
      intro x
      constructor
      · intro hx
        obtain ⟨b, hxb⟩ := mem_iUnion.mp hx
        obtain ⟨i, hi⟩ := hMD b
        exact mem_iUnion.mpr ⟨i, hi ▸ hxb⟩
      · intro hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        obtain ⟨b, hib, hb⟩ := hfinD.exists_le_maximal (mem_range_self i)
        exact mem_iUnion.mpr ⟨⟨b, hMmem b hb⟩, (show D' i ⊆ b from hib) hi⟩
    have hW'A : Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' W ⊆
        stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := by
      rintro _ ⟨x, hx, rfl⟩
      exact hhs.bijOn.mapsTo (hWR hx)
    have hW'c : IsClosed (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' W) :=
      (hWcpt.image_of_continuousOn (hhs.isPiecewiseAffineOn.continuousOn.mono hWR)).isClosed
    have hloc : ∀ p ∈ W, Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) p ∉
        ⋃ i, D' i → Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) p ∉
          closure (Sg \ Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' W) := by
      intro p hpW hxD hcl
      have hpcl : p ∉ closure (Θ \ W) := fun hp => by
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hWfr ⟨hpW, hp⟩)
        exact hxD (mem_iUnion.mpr ⟨i, hC'D i ⟨p, hi, rfl⟩⟩)
      have hyA := hhs.bijOn.mapsTo (hWR hpW)
      have hyo := hopen p (hWR hpW) (disjoint_left.mp hWN hpW)
      have hhy : h (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) p) = p :=
        hh.bijOn.invOn_invFunOn.2 (hWR hpW)
      have hpre : h ⁻¹' (closure (Θ \ W))ᶜ ∈ 𝓝[stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1]
          (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) p) :=
        (hh.isPiecewiseAffineOn.continuousOn _ hyA).preimage_mem_nhdsWithin
          (isClosed_closure.isOpen_compl.mem_nhds (by rw [hhy]; exact hpcl))
      obtain ⟨V, hV, hyV, hVA⟩ := mem_nhdsWithin.mp hpre
      have hV2 : IsOpen (V ∩ ({z : (Fin 3 → ℝ) × ℝ | 0 < z.2} ∩
          {z : (Fin 3 → ℝ) × ℝ | z.2 < 1})) :=
        hV.inter ((isOpen_lt continuous_const continuous_snd).inter
          (isOpen_lt continuous_snd continuous_const))
      obtain ⟨z, ⟨hzV, hz0, hz1⟩, hzSg, hzW⟩ :=
        mem_closure_iff.mp hcl _ hV2 ⟨hyV, hyo.2.1, hyo.2.2⟩
      have hzA : z ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := by
        rw [hSgdef] at hzSg
        rcases hzSg with ⟨-, h0 | h1⟩ | hzA
        · exact absurd h0 (ne_of_gt hz0)
        · exact absurd h1 (ne_of_lt hz1)
        · exact hzA
      have hhzW : h z ∈ W := by
        by_contra hhzW
        exact hVA ⟨hzV, hzA⟩ (subset_closure ⟨hhΘ z hzA, hhzW⟩)
      exact hzW ⟨h z, hhzW, hh.bijOn.invOn_invFunOn.1 hzA⟩
    have hW'D : Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' W ⊆
        ⋃ i, D' i := by
      have hcov : Sg \ ⋃ b : M, (b : Set ((Fin 3 → ℝ) × ℝ)) ⊆
          (closure (Sg \ Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' W))ᶜ ∪
            (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' W)ᶜ := by
        intro x hx
        by_cases hxW : x ∈ Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' W
        · obtain ⟨p, hpW, rfl⟩ := hxW
          exact Or.inl (hloc p hpW fun hxD => hx.2 ((hunion _).mpr hxD))
        · exact Or.inr hxW
      have hemp : (Sg \ ⋃ b : M, (b : Set ((Fin 3 → ℝ) × ℝ))) ∩
          ((closure (Sg \ Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' W))ᶜ ∩
            (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' W)ᶜ) = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun x hx => hx.2.1 (subset_closure ⟨hx.1.1, hx.2.2⟩)
      rcases isPreconnected_iff_subset_of_disjoint.mp hQ.isPreconnected _ _
        isClosed_closure.isOpen_compl hW'c.isOpen_compl hcov hemp with hsub | hsub
      · exfalso
        have hptQ : ((fun _ : Fin 3 => (1 / 3 : ℝ)), (0 : ℝ)) ∈
            Sg \ ⋃ b : M, (b : Set ((Fin 3 → ℝ) × ℝ)) := by
          refine ⟨hptSg, fun hp => ?_⟩
          obtain ⟨i, hi⟩ := mem_iUnion.mp ((hunion _).mp hp)
          exact hptA (hDA i hi)
        exact hsub hptQ (subset_closure ⟨hptSg, fun hp => hptA (hW'A hp)⟩)
      · intro x hx
        by_contra hxD
        exact hsub ⟨hASg (hW'A hx), fun hxM => hxD ((hunion x).mp hxM)⟩ hx
    have hhbΘ : ∀ b : M, h '' (b : Set ((Fin 3 → ℝ) × ℝ)) ⊆ Θ := by
      rintro b _ ⟨y, hy, rfl⟩
      exact hhΘ y (hMA b hy)
    have hWsub : φ '' W ⊆ ⋃ b : M, φ '' (h '' (b : Set ((Fin 3 → ℝ) × ℝ))) := by
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨b, hpb⟩ := mem_iUnion.mp ((hunion _).mpr (hW'D ⟨p, hp, rfl⟩))
      have hhy : h (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) p) = p :=
        hh.bijOn.invOn_invFunOn.2 (hWR hp)
      exact mem_iUnion.mpr ⟨b, ⟨_, ⟨_, hpb, rfl⟩, congrArg φ hhy⟩⟩
    have hsubS : (⋃ b : M, φ '' (h '' (b : Set ((Fin 3 → ℝ) × ℝ)))) ⊆ S :=
      iUnion_subset fun b => (image_mono (hhbΘ b)).trans hS
    have hsing : Subsingleton (integralSingularHomology 1
        (⋃ b : M, φ '' (h '' (b : Set ((Fin 3 → ℝ) × ℝ))))) := by
      refine (carriesFirstHomologyOnto_self _).subsingleton_of_iUnion
        (fun b => ?_) (fun b₁ b₂ hne => ?_) (fun b => ?_)
      · exact (((hMball b).isPolyhedron.isCompact.image_of_continuousOn
          (hh.isPiecewiseAffineOn.continuousOn.mono (hMA b))).image_of_continuousOn
            (hφ.mono (hhbΘ b))).isClosed
      · have hbd := hMdisj _ b₁.2 _ b₂.2 (Subtype.coe_injective.ne hne)
        refine disjoint_left.mpr ?_
        rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ ⟨_, ⟨c, hc, rfl⟩, hac⟩
        have hca := hh.bijOn.injOn (hMA b₂ hc) (hMA b₁ ha)
          (hφi (hhΘ c (hMA b₂ hc)) (hhΘ a (hMA b₁ ha)) hac)
        exact disjoint_left.mp hbd ha (hca ▸ hc)
      · obtain ⟨i, hi⟩ := hMD b
        rw [← hi, ← (hr i).image_eq, image_image, image_image]
        have hmaps : ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), r i x ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
          fun x hx => hDA i ((hr i).bijOn.mapsTo hx)
        exact subsingleton_integralSingularHomology_image_of_convex
          (f := fun x => φ (h (r i x))) (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin 3))
          (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)) ⟨_, Convexity.StdSimplex.single_mem_coordinateSet ℝ (0 : Fin 3)⟩
          (hφ.comp (hh.isPiecewiseAffineOn.continuousOn.comp (hr i).isPiecewiseAffineOn.continuousOn
            hmaps) fun x hx => hhΘ _ (hmaps x hx))
          (fun x hx y hy hxy => (hr i).bijOn.injOn hx hy (hh.bijOn.injOn (hmaps x hx) (hmaps y hy)
            (hφi (hhΘ _ (hmaps x hx)) (hhΘ _ (hmaps y hy)) hxy)))
    have hle := range_integralSingularHomologyMap_inclusion_mono
      ((image_mono hWΘ).trans hS) hsubS hWsub
    refine le_antisymm (hle.trans ?_) bot_le
    rintro _ ⟨a, rfl⟩
    have ha : a = 0 := @Subsingleton.elim _ hsing a 0
    rw [ha, map_zero]
    exact Submodule.zero_mem _
  · left
    obtain ⟨i, hi⟩ := not_forall.mp hall
    rcases (hC' i).exists_disk_or_annulus_of_subset_prism_lateral (hC'A i) with
      hd | ⟨ψ, hψ, hψA, hψ0, hψ1⟩
    · exact absurd hd hi
    have hi0 : InjOn (fun x => φ (h (ψ (x, 0)))) (stdSimplexBoundary 2) := by
      intro a ha b hb hab
      have hma : (a, (0 : ℝ)) ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := ⟨ha, h0mem⟩
      have hmb : (b, (0 : ℝ)) ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := ⟨hb, h0mem⟩
      simp only [hψ0 a ha, hψ0 b hb] at hab
      exact congrArg Prod.fst (hh.bijOn.injOn hma hmb (hφi (hhΘ _ hma) (hhΘ _ hmb) hab))
    have hi1 : InjOn (fun x => φ (h (ψ (x, 1)))) (stdSimplexBoundary 2) := by
      intro a ha b hb hab
      have hma : (a, (1 : ℝ)) ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := ⟨ha, h1mem⟩
      have hmb : (b, (1 : ℝ)) ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := ⟨hb, h1mem⟩
      have hψa := hψA ⟨_, hma, rfl⟩
      have hψb := hψA ⟨_, hmb, rfl⟩
      have hab' := hh.bijOn.injOn hψa hψb (hφi (hhΘ _ hψa) (hhΘ _ hψb) hab)
      exact congrArg Prod.fst (hψ.bijOn.injOn hma hmb hab')
    have hc0 : (fun x => φ (h (ψ (x, 0)))) '' stdSimplexBoundary 2 =
        φ '' (ρ '' (K ×ˢ {(-1 : ℝ)})) := by
      rw [← hh0, prod_singleton, image_image, image_image]
      exact image_congr fun x hx => by rw [hψ0 x hx]
    have hc1 : (fun x => φ (h (ψ (x, 1)))) '' stdSimplexBoundary 2 = φ '' C i := by
      rw [← hhC' i, ← hψ1, prod_singleton, image_image, image_image, image_image]
    have heq := range_integralSingularHomologyMap_eq_of_continuousOn
      (F := fun p => φ (h (ψ p))) hBcpt ((image_mono hKmΘ).trans hS)
      ((image_mono (hCΘ i)).trans hS)
      (hφ.comp (hh.isPiecewiseAffineOn.continuousOn.comp hψ.isPiecewiseAffineOn.continuousOn
        fun p hp => hψA ⟨p, hp, rfl⟩) fun p hp => hhΘ _ (hψA ⟨p, hp, rfl⟩))
      (fun p hp => hS (mem_image_of_mem φ (hhΘ _ (hψA ⟨p, hp, rfl⟩)))) hi0 hi1 hc0 hc1
    exact ⟨i, hKmle.trans heq.le⟩

end DifferentialGeometry.Topology.PiecewiseLinear

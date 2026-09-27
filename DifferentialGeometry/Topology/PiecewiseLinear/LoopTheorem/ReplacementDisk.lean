/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CellGluing
import DifferentialGeometry.External.Schoenflies.BoundaryContinuity2

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem isCutPair_image_endpoints_of_isPLHomeomorphOn
    {J A C S : Set (EuclideanSpace ℝ (Fin 2))}
    {p q r s : EuclideanSpace ℝ (Fin 2)}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hA : IsPLBall 1 A) (hC : IsPLBall 1 C)
    (hAarc : Schoenflies.IsArcBetween A p q) (hCarc : Schoenflies.IsArcBetween C r s)
    (hg : IsPLHomeomorphOn g A C) (hcut : Schoenflies.IsCutPair J r s C S) :
    Schoenflies.IsCutPair J (g p) (g q) C S := by
  rcases IsPLHomeomorphOn.maps_arc_endpoints hA hC hAarc hCarc hg with
    ⟨hgp, hgq⟩ | ⟨hgp, hgq⟩
  · rw [hgp, hgq]
    exact hcut
  · rw [hgp, hgq]
    exact ⟨hcut.fst.reverse, hcut.snd.reverse, hcut.union_eq, by
      rw [hcut.inter_eq, pair_comm]⟩

namespace SingularTwoCell

private theorem range_map_boundary_eq_image
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (G : SingularTwoCell M) {R : Set (EuclideanSpace ℝ (Fin 2))}
    {a' b' : frontier G.domain} (ρ : Path a' b')
    (hρ : Set.range (fun t => ((ρ t : frontier G.domain) : EuclideanSpace ℝ (Fin 2))) = R) :
    Set.range (ρ.map G.boundary.continuous) = G '' R := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨ρ t, ?_, rfl⟩
    rw [← hρ]
    exact ⟨t, rfl⟩
  · rintro ⟨w, hwR, rfl⟩
    rw [← hρ] at hwR
    obtain ⟨t, htw⟩ := hwR
    exact ⟨t, congrArg G htw⟩

open Classical in
theorem exists_direct_reglued_cell_with_boundary_arcs
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D D₁ D₃ : SingularTwoCell M)
    {A C : Set (EuclideanSpace ℝ (Fin 2))} {p q : EuclideanSpace ℝ (Fin 2)}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hA : IsPLBall 1 A)
    (hA₁ : A ⊆ frontier D₁.domain) (hC₃ : C ⊆ frontier D₃.domain)
    (hcut₁ : Schoenflies.IsCutPair (frontier D₁.domain) p q A
      (D₁.domain ∩ frontier D.domain))
    (hcut₃ : Schoenflies.IsCutPair (frontier D₃.domain) (g p) (g q) C
      (D₃.domain ∩ frontier D.domain))
    (hg : IsPLHomeomorphOn g A C) (hcompat₁₃ : EqOn D₁ (D₃ ∘ g) A)
    (hU₁D : D₁.domain ⊆ D.domain) (hU₃D : D₃.domain ⊆ D.domain)
    (hfun₁ : D₁.toFun = D.toFun) (hfun₃ : D₃.toFun = D.toFun) :
    ∃ (G : SingularTwoCell M) (R T : Set (EuclideanSpace ℝ (Fin 2))),
      IsPLBall 1 R ∧ IsPLBall 1 T ∧ frontier G.domain = R ∪ T ∧
      G '' R = D '' (D₁.domain ∩ frontier D.domain) ∧
      G '' T = D '' (D₃.domain ∩ frontier D.domain) ∧
      G '' G.domain ⊆ D '' D.domain ∧
      ∃ (x y : M) (σ : Path x y) (ω : Path y x)
          (e : loopCircle ≃ₜ frontier G.domain),
        Set.range σ = D '' (D₁.domain ∩ frontier D.domain) ∧
        Set.range ω = D '' (D₃.domain ∩ frontier D.domain) ∧
        ∀ θ, G (e θ) = pathToCircle (σ.trans ω) θ := by
  obtain ⟨G, P, Q, f₁, f₃, hP, hQ, -, hGdomain, -, -, -, hf₁, hf₃, -,
    hf₁seam, hf₃seam, hG₁, hG₃, a, b, R, T, hcutP, hcutQ, hR, hT, hfrontG,
    hf₁a, hf₁b, hf₃a, hf₃b⟩ :=
    D₁.exists_glue_of_isPLHomeomorphOn_boundary_arc D₃ hA hcut₁.fst hA₁ hg hC₃
      hcompat₁₃
  have hRP : R ⊆ P := hcutP.snd_subset.trans hP.isPolyhedron.isClosed.frontier_subset
  have hTQ : T ⊆ Q := hcutQ.snd_subset.trans hQ.isPolyhedron.isClosed.frontier_subset
  have hRimage : f₁ '' R = D₁.domain ∩ frontier D.domain :=
    image_cutArc_eq_of_isPLHomeomorphOn hP D₁.isPLBall_domain hf₁ hcutP hf₁seam hf₁a
      hf₁b hcut₁
  have hTimage : f₃ '' T = D₃.domain ∩ frontier D.domain :=
    image_cutArc_eq_of_isPLHomeomorphOn hQ D₃.isPLBall_domain hf₃ hcutQ hf₃seam hf₃a
      hf₃b hcut₃
  have hGR : G '' R = D '' (D₁.domain ∩ frontier D.domain) := by
    calc
      G '' R = (D₁ ∘ f₁) '' R := Set.image_congr (hG₁.mono hRP)
      _ = D₁ '' (f₁ '' R) := image_comp D₁ f₁ R
      _ = D₁ '' (D₁.domain ∩ frontier D.domain) := congrArg (D₁ '' ·) hRimage
      _ = D '' (D₁.domain ∩ frontier D.domain) := by rw [hfun₁]
  have hGT : G '' T = D '' (D₃.domain ∩ frontier D.domain) := by
    calc
      G '' T = (D₃ ∘ f₃) '' T := Set.image_congr (hG₃.mono hTQ)
      _ = D₃ '' (f₃ '' T) := image_comp D₃ f₃ T
      _ = D₃ '' (D₃.domain ∩ frontier D.domain) := congrArg (D₃ '' ·) hTimage
      _ = D '' (D₃.domain ∩ frontier D.domain) := by rw [hfun₃]
  have hG₁' : EqOn G (D ∘ f₁) P := by
    intro z hz
    simpa only [Function.comp_apply, hfun₁] using hG₁ hz
  have hG₃' : EqOn G (D ∘ f₃) Q := by
    intro z hz
    simpa only [Function.comp_apply, hfun₃] using hG₃ hz
  have hGimage : G '' G.domain ⊆ D '' D.domain := by
    rintro z ⟨w, hw, rfl⟩
    rw [hGdomain] at hw
    rcases hw with hwP | hwQ
    · exact ⟨f₁ w, hU₁D (hf₁.bijOn.mapsTo hwP), (hG₁' hwP).symm⟩
    · exact ⟨f₃ w, hU₃D (hf₃.bijOn.mapsTo hwQ), (hG₃' hwQ).symm⟩
  have hRT : R ∩ T = {a, b} := by
    apply Subset.antisymm
    · rintro x ⟨hxR, hxT⟩
      exact hcutP.inter_eq.subset ⟨⟨hRP hxR, hTQ hxT⟩, hxR⟩
    · rintro x (rfl | rfl)
      · exact ⟨hcutP.snd.left_mem, hcutQ.snd.left_mem⟩
      · exact ⟨hcutP.snd.right_mem, hcutQ.snd.right_mem⟩
  obtain ⟨a', b', ρ, κ, ev, hρrange, hκrange, hev, -, -⟩ :=
    exists_boundaryParam_paths_of_isCutPair_union hcutP.snd hcutQ.snd hRT hfrontG
  refine ⟨G, R, T, hR, hT, hfrontG, hGR, hGT, hGimage, G.boundary a',
    G.boundary b', ρ.map G.boundary.continuous, κ.map G.boundary.continuous, ev,
    ?_, ?_, ?_⟩
  · rw [← hGR]
    exact G.range_map_boundary_eq_image ρ hρrange
  · rw [← hGT]
    exact G.range_map_boundary_eq_image κ hκrange
  · intro θ
    rw [hev θ]
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    simp only [pathToCircle_coe]
    change ((ρ.trans κ).map G.boundary.continuous) t =
      ((ρ.map G.boundary.continuous).trans (κ.map G.boundary.continuous)) t
    rw [Path.map_trans]

open Classical in
theorem exists_cross_reglued_cell_with_boundary_arcs
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D D₁ D₂ D₃ : SingularTwoCell M)
    {A C : Set (EuclideanSpace ℝ (Fin 2))} {p q : EuclideanSpace ℝ (Fin 2)}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hA : IsPLBall 1 A) (hAC : Disjoint A C)
    (hcover : D₁.domain ∪ D₂.domain ∪ D₃.domain = D.domain)
    (hinter₁₂ : D₁.domain ∩ D₂.domain = A)
    (hinter₂₃ : D₂.domain ∩ D₃.domain = C)
    (hA₁ : A ⊆ frontier D₁.domain) (hA₂ : A ⊆ frontier D₂.domain)
    (hC₂ : C ⊆ frontier D₂.domain) (hC₃ : C ⊆ frontier D₃.domain)
    (hcut₁ : Schoenflies.IsCutPair (frontier D₁.domain) p q A
      (D₁.domain ∩ frontier D.domain))
    (hcut₃ : Schoenflies.IsCutPair (frontier D₃.domain) (g p) (g q) C
      (D₃.domain ∩ frontier D.domain))
    (hg : IsPLHomeomorphOn g A C)
    (hcompat₁₂ : EqOn D₁ (D₂ ∘ g) A) (hcompat₂₃ : EqOn D₂ (D₃ ∘ g) A)
    (hfun₁ : D₁.toFun = D.toFun) (hfun₂ : D₂.toFun = D.toFun)
    (hfun₃ : D₃.toFun = D.toFun) :
    ∃ (G : SingularTwoCell M) (R T : Set (EuclideanSpace ℝ (Fin 2))),
      IsPLBall 1 R ∧ IsPLBall 1 T ∧ frontier G.domain = R ∪ T ∧
      G '' R = D '' ((D₁.domain ∪ D₂.domain) ∩ frontier D.domain) ∧
      G '' T = D '' (D₃.domain ∩ frontier D.domain) ∧
      G '' G.domain ⊆ D '' D.domain ∧
      ∃ (x y : M) (σ : Path x y) (ω : Path y x)
          (e : loopCircle ≃ₜ frontier G.domain),
        Set.range σ = D '' ((D₁.domain ∪ D₂.domain) ∩ frontier D.domain) ∧
        Set.range ω = D '' (D₃.domain ∩ frontier D.domain) ∧
        ∀ θ, G (e θ) = pathToCircle (σ.trans ω) θ := by
  have hU₁D : D₁.domain ⊆ D.domain := by
    intro x hx
    rw [← hcover]
    exact Or.inl (Or.inl hx)
  have hU₂D : D₂.domain ⊆ D.domain := by
    intro x hx
    rw [← hcover]
    exact Or.inl (Or.inr hx)
  have hU₃D : D₃.domain ⊆ D.domain := by
    intro x hx
    rw [← hcover]
    exact Or.inr hx
  have hAU₂ : A ⊆ D₂.domain := by
    rw [← hinter₁₂]
    exact inter_subset_right
  have hCU₂ : C ⊆ D₂.domain := by
    rw [← hinter₂₃]
    exact inter_subset_left
  have hCU₃ : C ⊆ D₃.domain := by
    rw [← hinter₂₃]
    exact inter_subset_right
  obtain ⟨H, P, Q, f₁, f₂, hP, hQ, -, hHdomain, -, -, -, hf₁, hf₂, -,
    hf₁seam, hf₂seam, hH₁, hH₂, pH, qH, R₀, T₀, hcutP, hcutQ, hR₀, -, hfrontH,
    hf₁pH, hf₁qH, hf₂pH, hf₂qH⟩ :=
    D₁.exists_glue_of_isPLHomeomorphOn_boundary_arc D₂ hA hcut₁.fst hA₁ hg hC₂
      hcompat₁₂
  have hR₀P : R₀ ⊆ P := hcutP.snd_subset.trans hP.isPolyhedron.isClosed.frontier_subset
  have hT₀Q : T₀ ⊆ Q := hcutQ.snd_subset.trans hQ.isPolyhedron.isClosed.frontier_subset
  have hR₀image : f₁ '' R₀ = D₁.domain ∩ frontier D.domain :=
    image_cutArc_eq_of_isPLHomeomorphOn hP D₁.isPLBall_domain hf₁ hcutP hf₁seam
      hf₁pH hf₁qH hcut₁
  have hfrontD₂ : frontier D₂.domain = (D₂.domain ∩ frontier D.domain) ∪ A ∪ C :=
    frontier_middle_eq_union_seams hcover D₁.isPLBall_domain.isPolyhedron.isClosed
      D₂.isPLBall_domain.isPolyhedron.isClosed D₃.isPLBall_domain.isPolyhedron.isClosed
      hinter₁₂ hinter₂₃ hA₂ hC₂
  obtain ⟨S₂, hcut₂, -, -⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere D₂.isPLSphere_frontier hcut₃.fst hC₂
  have hmeet : C ∩ ((D₂.domain ∩ frontier D.domain) ∪ A) ⊆ {g p, g q} := by
    rintro x ⟨hxC, hx⟩
    rcases hx with ⟨-, hxF⟩ | hxA
    · exact hcut₃.inter_eq.subset ⟨hxC, ⟨hCU₃ hxC, hxF⟩⟩
    · exact absurd hxA (Set.disjoint_right.mp hAC hxC)
  have hS₂eq : S₂ = (D₂.domain ∩ frontier D.domain) ∪ A :=
    isCutPair_snd_eq_of_union_eq hcut₂ hfrontD₂ hmeet
      ⟨hCU₂ hcut₃.fst.left_mem, hcut₃.snd.left_mem.2⟩
      ⟨hCU₂ hcut₃.fst.right_mem, hcut₃.snd.right_mem.2⟩
  have hT₀image : f₂ '' T₀ = S₂ :=
    image_cutArc_eq_of_isPLHomeomorphOn hQ D₂.isPLBall_domain hf₂ hcutQ hf₂seam
      hf₂pH hf₂qH hcut₂
  set j := Function.invFunOn f₂ Q
  set A' := j '' A
  have hjA : IsPLHomeomorphOn j A A' := hf₂.symm.restrict hA.isPolyhedron hAU₂
  have hA' : IsPLBall 1 A' := hA.of_isPLHomeomorphOn hjA
  have hA'arc : Schoenflies.IsArcBetween A' (j p) (j q) :=
    hcut₁.fst.image_of_injOn (subset_refl A) hjA.isPiecewiseAffineOn.continuousOn
      hjA.bijOn.injOn
  have hjfront : j '' frontier D₂.domain = frontier Q :=
    hf₂.symm.image_frontier (by simp) D₂.isPLBall_domain.isPolyhedron.isClosed
      hQ.isPolyhedron.isClosed
  have hA'frontQ : A' ⊆ frontier Q := by
    rw [← hjfront]
    exact image_mono hA₂
  have hA'seam : Disjoint A' (P ∩ Q) := by
    rw [Set.disjoint_left]
    rintro x ⟨y, hyA, rfl⟩ hxseam
    have hf₂j : f₂ (j y) = y := hf₂.bijOn.invOn_invFunOn.2 (hAU₂ hyA)
    have hCmem : f₂ (j y) ∈ C := by
      rw [← hf₂seam]
      exact ⟨j y, hxseam, rfl⟩
    exact Set.disjoint_left.mp hAC hyA (hf₂j ▸ hCmem)
  have hA'T : A' ⊆ T₀ := by
    intro x hxA'
    have hxfront := hA'frontQ hxA'
    rw [← hcutQ.union_eq] at hxfront
    exact hxfront.resolve_left (Set.disjoint_left.mp hA'seam hxA')
  have hA'frontH : A' ⊆ frontier H.domain := by
    rw [hfrontH]
    exact hA'T.trans subset_union_right
  have hA'Q : A' ⊆ Q := by
    rintro x ⟨y, hyA, rfl⟩
    exact hf₂.bijOn.surjOn.mapsTo_invFunOn (hAU₂ hyA)
  have hf₂A'image : f₂ '' A' = A := by
    calc
      f₂ '' A' = (f₂ ∘ j) '' A := (image_comp f₂ j A).symm
      _ = id '' A := Set.image_congr fun y hy => hf₂.bijOn.invOn_invFunOn.2 (hAU₂ hy)
      _ = A := image_id A
  have hf₂A' : IsPLHomeomorphOn f₂ A' A := by
    have hres := hf₂.restrict hA'.isPolyhedron hA'Q
    rwa [hf₂A'image] at hres
  have hk : IsPLHomeomorphOn (g ∘ f₂) A' C := hf₂A'.trans hg
  have hcompatH₃ : EqOn H (D₃ ∘ (g ∘ f₂)) A' := by
    intro x hx
    calc
      H x = D₂ (f₂ x) := hH₂ (hA'Q hx)
      _ = D₃ (g (f₂ x)) := hcompat₂₃ (hf₂A'.bijOn.mapsTo hx)
      _ = (D₃ ∘ (g ∘ f₂)) x := rfl
  obtain ⟨G, P', Q', h, f₃, hP', hQ', -, hGdomain, -, -, -, hh, hf₃, -,
    hhseam, hf₃seam, hGH, hG₃, a, b, R', T', hcutP', hcutQ', hR', hT',
    hfrontG, hha, hhb, hf₃a, hf₃b⟩ :=
    H.exists_glue_of_isPLHomeomorphOn_boundary_arc D₃ hA' hA'arc hA'frontH hk hC₃ hcompatH₃
  have hf₂jp : f₂ (j p) = p := hf₂.bijOn.invOn_invFunOn.2 (hAU₂ hcut₁.fst.left_mem)
  have hf₂jq : f₂ (j q) = q := hf₂.bijOn.invOn_invFunOn.2 (hAU₂ hcut₁.fst.right_mem)
  have hf₃aeq : f₃ a = g p := by
    rw [hf₃a]
    exact congrArg g hf₂jp
  have hf₃beq : f₃ b = g q := by
    rw [hf₃b]
    exact congrArg g hf₂jq
  have hT'image : f₃ '' T' = D₃.domain ∩ frontier D.domain :=
    image_cutArc_eq_of_isPLHomeomorphOn hQ' D₃.isPLBall_domain hf₃ hcutQ' hf₃seam
      hf₃aeq hf₃beq hcut₃
  obtain ⟨SH, hcutH, -, hSH⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere H.isPLSphere_frontier hA'arc
      hA'frontH
  have hR'image : h '' R' = SH :=
    image_cutArc_eq_of_isPLHomeomorphOn hP' H.isPLBall_domain hh hcutP' hhseam hha hhb
      hcutH
  have hR₀T₀ : R₀ ∩ T₀ = {pH, qH} := by
    apply Subset.antisymm
    · rintro x ⟨hxR, hxT⟩
      exact hcutP.inter_eq.subset ⟨⟨hR₀P hxR, hT₀Q hxT⟩, hxR⟩
    · rintro x (rfl | rfl)
      · exact ⟨hcutP.snd.left_mem, hcutQ.snd.left_mem⟩
      · exact ⟨hcutP.snd.right_mem, hcutQ.snd.right_mem⟩
  have hR₀SH : R₀ ⊆ SH := by
    have hsub : R₀ \ {pH, qH} ⊆ SH := by
      intro x hx
      have hxfront : x ∈ frontier H.domain := by
        rw [hfrontH]
        exact Or.inl hx.1
      rcases hcutH.union_eq.symm.subset hxfront with hxA' | hxSH
      · exact absurd (hR₀T₀.subset ⟨hx.1, hA'T hxA'⟩) hx.2
      · exact hxSH
    calc
      R₀ ⊆ closure (R₀ \ {pH, qH}) := hR₀.subset_closure_sdiff_finite (Set.toFinite _)
      _ ⊆ closure SH := closure_mono hsub
      _ = SH := hSH.isPolyhedron.isClosed.closure_eq
  have hA'char : ∀ x ∈ Q, f₂ x ∈ A → x ∈ A' := by
    intro x hxQ hxA
    have hxD₂ : f₂ x ∈ D₂.domain := hf₂.bijOn.mapsTo hxQ
    have hjx : j (f₂ x) ∈ Q := hf₂.bijOn.surjOn.mapsTo_invFunOn hxD₂
    have hfix : j (f₂ x) = x :=
      hf₂.bijOn.injOn hjx hxQ (hf₂.bijOn.invOn_invFunOn.2 hxD₂)
    have hmem : j (f₂ x) ∈ A' := mem_image_of_mem j hxA
    rwa [hfix] at hmem
  have hAF : A ∩ frontier D.domain ⊆ {p, q} := by
    rintro x ⟨hxA, hxF⟩
    refine hcut₁.inter_eq.subset ⟨hxA, ⟨?_, hxF⟩⟩
    rw [← hinter₁₂] at hxA
    exact hxA.1
  have hpF : p ∈ D₂.domain ∩ frontier D.domain :=
    ⟨hAU₂ hcut₁.fst.left_mem, hcut₁.snd.left_mem.2⟩
  have hqF : q ∈ D₂.domain ∩ frontier D.domain :=
    ⟨hAU₂ hcut₁.fst.right_mem, hcut₁.snd.right_mem.2⟩
  have hSHT₀image : f₂ '' (SH ∩ T₀) = D₂.domain ∩ frontier D.domain := by
    apply Subset.antisymm
    · rintro y ⟨x, ⟨hxSH, hxT₀⟩, rfl⟩
      have hmem : f₂ x ∈ S₂ := by
        rw [← hT₀image]
        exact mem_image_of_mem f₂ hxT₀
      rw [hS₂eq] at hmem
      rcases hmem with hgood | hxA
      · exact hgood
      · have hxpair : x ∈ ({j p, j q} : Set (EuclideanSpace ℝ (Fin 2))) :=
          hcutH.inter_eq.subset ⟨hA'char x (hT₀Q hxT₀) hxA, hxSH⟩
        rcases hxpair with rfl | rfl
        · rw [hf₂jp]
          exact hpF
        · rw [hf₂jq]
          exact hqF
    · intro y hy
      have hyT₀ : y ∈ f₂ '' T₀ := by
        rw [hT₀image, hS₂eq]
        exact Or.inl hy
      obtain ⟨x, hxT₀, hxy⟩ := hyT₀
      by_cases hxA' : x ∈ A'
      · have hyA : y ∈ A := by
          rw [← hf₂A'image]
          exact ⟨x, hxA', hxy⟩
        rcases hAF ⟨hyA, hy.2⟩ with rfl | rfl
        · exact ⟨j y, ⟨hcutH.snd.left_mem, hA'T (mem_image_of_mem j hyA)⟩, hf₂jp⟩
        · exact ⟨j y, ⟨hcutH.snd.right_mem, hA'T (mem_image_of_mem j hyA)⟩, hf₂jq⟩
      · refine ⟨x, ⟨?_, hxT₀⟩, hxy⟩
        have hxfront : x ∈ frontier H.domain := by
          rw [hfrontH]
          exact Or.inr hxT₀
        exact (hcutH.union_eq.symm.subset hxfront).resolve_left hxA'
  have hHR₀ : H '' R₀ = D '' (D₁.domain ∩ frontier D.domain) := by
    calc
      H '' R₀ = (D₁ ∘ f₁) '' R₀ := Set.image_congr (hH₁.mono hR₀P)
      _ = D₁ '' (f₁ '' R₀) := image_comp D₁ f₁ R₀
      _ = D₁ '' (D₁.domain ∩ frontier D.domain) := congrArg (D₁ '' ·) hR₀image
      _ = D '' (D₁.domain ∩ frontier D.domain) := by rw [hfun₁]
  have hHmid : H '' (SH ∩ T₀) = D '' (D₂.domain ∩ frontier D.domain) := by
    calc
      H '' (SH ∩ T₀) = (D₂ ∘ f₂) '' (SH ∩ T₀) :=
        Set.image_congr (hH₂.mono fun x hx => hT₀Q hx.2)
      _ = D₂ '' (f₂ '' (SH ∩ T₀)) := image_comp D₂ f₂ _
      _ = D₂ '' (D₂.domain ∩ frontier D.domain) := congrArg (D₂ '' ·) hSHT₀image
      _ = D '' (D₂.domain ∩ frontier D.domain) := by rw [hfun₂]
  have hSHsplit : SH = R₀ ∪ SH ∩ T₀ := by
    apply Subset.antisymm
    · intro x hx
      have hxfront : x ∈ frontier H.domain := hcutH.snd_subset hx
      rw [hfrontH] at hxfront
      rcases hxfront with hxR | hxT
      · exact Or.inl hxR
      · exact Or.inr ⟨hx, hxT⟩
    · exact union_subset hR₀SH fun x hx => hx.1
  have hHSH : H '' SH = D '' ((D₁.domain ∪ D₂.domain) ∩ frontier D.domain) := by
    rw [union_inter_distrib_right, image_union, hSHsplit, image_union]
    exact congrArg₂ (· ∪ ·) hHR₀ hHmid
  have hR'P' : R' ⊆ P' := hcutP'.snd_subset.trans hP'.isPolyhedron.isClosed.frontier_subset
  have hT'Q' : T' ⊆ Q' := hcutQ'.snd_subset.trans hQ'.isPolyhedron.isClosed.frontier_subset
  have hGR' : G '' R' = D '' ((D₁.domain ∪ D₂.domain) ∩ frontier D.domain) := by
    calc
      G '' R' = (H ∘ h) '' R' := Set.image_congr (hGH.mono hR'P')
      _ = H '' (h '' R') := image_comp H h R'
      _ = H '' SH := congrArg (H '' ·) hR'image
      _ = D '' ((D₁.domain ∪ D₂.domain) ∩ frontier D.domain) := hHSH
  have hGT' : G '' T' = D '' (D₃.domain ∩ frontier D.domain) := by
    calc
      G '' T' = (D₃ ∘ f₃) '' T' := Set.image_congr (hG₃.mono hT'Q')
      _ = D₃ '' (f₃ '' T') := image_comp D₃ f₃ T'
      _ = D₃ '' (D₃.domain ∩ frontier D.domain) := congrArg (D₃ '' ·) hT'image
      _ = D '' (D₃.domain ∩ frontier D.domain) := by rw [hfun₃]
  have hH₁' : EqOn H (D ∘ f₁) P := by
    intro z hz
    simpa only [Function.comp_apply, hfun₁] using hH₁ hz
  have hH₂' : EqOn H (D ∘ f₂) Q := by
    intro z hz
    simpa only [Function.comp_apply, hfun₂] using hH₂ hz
  have hG₃' : EqOn G (D ∘ f₃) Q' := by
    intro z hz
    simpa only [Function.comp_apply, hfun₃] using hG₃ hz
  have hHimage : H '' H.domain ⊆ D '' D.domain := by
    rintro z ⟨w, hw, rfl⟩
    rw [hHdomain] at hw
    rcases hw with hwP | hwQ
    · exact ⟨f₁ w, hU₁D (hf₁.bijOn.mapsTo hwP), (hH₁' hwP).symm⟩
    · exact ⟨f₂ w, hU₂D (hf₂.bijOn.mapsTo hwQ), (hH₂' hwQ).symm⟩
  have hGimage : G '' G.domain ⊆ D '' D.domain := by
    rintro z ⟨w, hw, rfl⟩
    rw [hGdomain] at hw
    rcases hw with hwP' | hwQ'
    · obtain ⟨u, hu, hGu⟩ := hHimage ⟨h w, hh.bijOn.mapsTo hwP', rfl⟩
      exact ⟨u, hu, hGu.trans (hGH hwP').symm⟩
    · exact ⟨f₃ w, hU₃D (hf₃.bijOn.mapsTo hwQ'), (hG₃' hwQ').symm⟩
  have hR'T' : R' ∩ T' = {a, b} := by
    apply Subset.antisymm
    · rintro x ⟨hxR, hxT⟩
      exact hcutP'.inter_eq.subset ⟨⟨hR'P' hxR, hT'Q' hxT⟩, hxR⟩
    · rintro x (rfl | rfl)
      · exact ⟨hcutP'.snd.left_mem, hcutQ'.snd.left_mem⟩
      · exact ⟨hcutP'.snd.right_mem, hcutQ'.snd.right_mem⟩
  obtain ⟨a', b', ρ, κ, ev, hρrange, hκrange, hev, -, -⟩ :=
    exists_boundaryParam_paths_of_isCutPair_union hcutP'.snd hcutQ'.snd hR'T' hfrontG
  refine ⟨G, R', T', hR', hT', hfrontG, hGR', hGT', hGimage, G.boundary a',
    G.boundary b', ρ.map G.boundary.continuous, κ.map G.boundary.continuous, ev,
    ?_, ?_, ?_⟩
  · rw [← hGR']
    exact G.range_map_boundary_eq_image ρ hρrange
  · rw [← hGT']
    exact G.range_map_boundary_eq_image κ hκrange
  · intro θ
    rw [hev θ]
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    simp only [pathToCircle_coe]
    change ((ρ.trans κ).map G.boundary.continuous) t =
      ((ρ.map G.boundary.continuous).trans (κ.map G.boundary.continuous)) t
    rw [Path.map_trans]

end SingularTwoCell

end DifferentialGeometry.Topology.PiecewiseLinear

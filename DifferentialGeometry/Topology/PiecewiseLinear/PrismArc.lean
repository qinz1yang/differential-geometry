/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PrismHomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.CircleParametrization
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_isPiecewiseAffineOn_prism_of_isPLHomeomorphOn {J : Set E} {θ : ℝ → E}
    (hθ : IsPLHomeomorphOn θ (Icc (0 : ℝ) 1) J) {f g : E → F}
    (hf : IsPiecewiseAffineOn f J) (hg : IsPiecewiseAffineOn g J) :
    ∃ Φ : E × ℝ → F, IsPiecewiseAffineOn Φ (J ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ y ∈ J, Φ (y, 0) = f y) ∧ (∀ y ∈ J, Φ (y, 1) = g y) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (θ 0, t) = f (θ 0) + t • (g (θ 0) - f (θ 0))) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (θ 1, t) = f (θ 1) + t • (g (θ 1) - f (θ 1))) ∧
      (∀ (S : Set F), Convex ℝ S → MapsTo f J S → MapsTo g J S →
        MapsTo Φ (J ×ˢ Icc (0 : ℝ) 1) S) := by
  classical
  have hcomp : ∀ h : E → F, IsPiecewiseAffineOn h J → IsPiecewiseAffineOn (h ∘ θ) (Icc (0 : ℝ) 1) :=
      by
    intro h hh
    have hcc := hh.comp hθ.isPiecewiseAffineOn
    have hset : Icc (0 : ℝ) 1 ∩ θ ⁻¹' J = Icc (0 : ℝ) 1 :=
      inter_eq_left.mpr (fun x hx => hθ.bijOn.mapsTo hx)
    rwa [hset] at hcc
  obtain ⟨n, s, Φ₁, hs0, hsn, hmono, hPA₁, hbot₁, htop₁, hl₁, hr₁, himg₁⟩ :=
    exists_isPiecewiseAffineOn_prism (hcomp f hf) (hcomp g hg)
  set ψ : E × ℝ → ℝ × ℝ := Prod.map (Function.invFunOn θ (Icc (0 : ℝ) 1)) id with hψ
  have hψPA : IsPiecewiseAffineOn ψ (J ×ˢ Icc (0 : ℝ) 1) :=
    hθ.isPiecewiseAffineOn_invFunOn.prodMap (isPiecewiseAffineOn_of_affine_of_isHPolytope
      (AffineMap.id ℝ ℝ) isHPolytope_Icc)
  have hψmaps : MapsTo ψ (J ×ˢ Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    fun z hz => ⟨hθ.bijOn.surjOn.mapsTo_invFunOn hz.1, hz.2⟩
  have hinv : ∀ y ∈ J, θ (Function.invFunOn θ (Icc (0 : ℝ) 1) y) = y :=
    fun y hy => hθ.bijOn.invOn_invFunOn.2 hy
  have hinv0 : Function.invFunOn θ (Icc (0 : ℝ) 1) (θ 0) = 0 :=
    hθ.bijOn.invOn_invFunOn.1 ⟨le_rfl, zero_le_one⟩
  have hinv1 : Function.invFunOn θ (Icc (0 : ℝ) 1) (θ 1) = 1 :=
    hθ.bijOn.invOn_invFunOn.1 ⟨zero_le_one, le_rfl⟩
  refine ⟨Φ₁ ∘ ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hPA₁.comp hψPA
    convert h using 1
    exact (Set.inter_eq_self_of_subset_left (fun z hz => hψmaps hz)).symm
  · intro y hy
    have : ψ (y, 0) = (Function.invFunOn θ (Icc (0 : ℝ) 1) y, 0) := rfl
    rw [Function.comp_apply, this,
      hbot₁ _ (hθ.bijOn.surjOn.mapsTo_invFunOn hy), Function.comp_apply, hinv y hy]
  · intro y hy
    have : ψ (y, 1) = (Function.invFunOn θ (Icc (0 : ℝ) 1) y, 1) := rfl
    rw [Function.comp_apply, this,
      htop₁ _ (hθ.bijOn.surjOn.mapsTo_invFunOn hy), Function.comp_apply, hinv y hy]
  · intro t ht
    have hz : ψ (θ 0, t) = ((0 : ℝ), t) := by rw [hψ]; simp [hinv0]
    rw [Function.comp_apply, hz, hl₁ t ht]
    rfl
  · intro t ht
    have hz : ψ (θ 1, t) = ((1 : ℝ), t) := by rw [hψ]; simp [hinv1]
    rw [Function.comp_apply, hz, hr₁ t ht]
    rfl
  · intro S hS hfS hgS z hz
    refine mapsTo_of_forall_mem_convexHull_cell hS himg₁ (fun i hi => ?_) (hψmaps hz)
    have hsm : ∀ j, j ≤ n → s j ∈ Icc (0 : ℝ) 1 :=
      fun j hj => mem_Icc_of_forall_lt_succ hmono hs0 hsn hj
    have hJ : ∀ j, j ≤ n → θ (s j) ∈ J := fun j hj => hθ.bijOn.mapsTo (hsm j hj)
    exact ⟨hfS (hJ i (by omega)), hfS (hJ (i + 1) (by omega)), hgS (hJ i (by omega)),
      hgS (hJ (i + 1) (by omega))⟩

theorem exists_isPiecewiseAffineOn_prism_of_isPLHomeomorphOn_mapsTo_space
    (L : Geometry.SimplicialComplex ℝ F) {J : Set E} {θ : ℝ → E}
    (hθ : IsPLHomeomorphOn θ (Icc (0 : ℝ) 1) J) {f g : E → F}
    (hf : IsPiecewiseAffineOn f J) (hg : IsPiecewiseAffineOn g J)
    {δ : ℝ} (hδ : 0 < δ) (T : Finset ℝ) (hT : ∀ x ∈ T, x ∈ Icc (0 : ℝ) 1)
    (hface : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b → b - a < δ →
      (∀ x ∈ T, ¬(a < x ∧ x < b)) →
      ∃ u ∈ L.faces, ({f (θ a), f (θ b), g (θ a), g (θ b)} : Set F) ⊆ convexHull ℝ (u : Set F)) :
    ∃ Φ : E × ℝ → F, IsPiecewiseAffineOn Φ (J ×ˢ Icc (0 : ℝ) 1) ∧
      MapsTo Φ (J ×ˢ Icc (0 : ℝ) 1) L.space ∧
      (∀ y ∈ J, Φ (y, 0) = f y) ∧ (∀ y ∈ J, Φ (y, 1) = g y) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (θ 0, t) = f (θ 0) + t • (g (θ 0) - f (θ 0))) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (θ 1, t) = f (θ 1) + t • (g (θ 1) - f (θ 1))) := by
  classical
  have hcomp : ∀ h : E → F, IsPiecewiseAffineOn h J →
      IsPiecewiseAffineOn (h ∘ θ) (Icc (0 : ℝ) 1) := by
    intro h hh
    have hcc := hh.comp hθ.isPiecewiseAffineOn
    have hset : Icc (0 : ℝ) 1 ∩ θ ⁻¹' J = Icc (0 : ℝ) 1 :=
      inter_eq_left.mpr (fun x hx => hθ.bijOn.mapsTo hx)
    rwa [hset] at hcc
  obtain ⟨Φ₁, hPA₁, hmaps₁, hbot₁, htop₁, hl₁, hr₁⟩ :=
    exists_isPiecewiseAffineOn_prism_mapsTo_space L (hcomp f hf) (hcomp g hg) hδ T hT hface
  set ψ : E × ℝ → ℝ × ℝ := Prod.map (Function.invFunOn θ (Icc (0 : ℝ) 1)) id with hψ
  have hψPA : IsPiecewiseAffineOn ψ (J ×ˢ Icc (0 : ℝ) 1) :=
    hθ.isPiecewiseAffineOn_invFunOn.prodMap (isPiecewiseAffineOn_of_affine_of_isHPolytope
      (AffineMap.id ℝ ℝ) isHPolytope_Icc)
  have hψmaps : MapsTo ψ (J ×ˢ Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    fun z hz => ⟨hθ.bijOn.surjOn.mapsTo_invFunOn hz.1, hz.2⟩
  have hinv : ∀ y ∈ J, θ (Function.invFunOn θ (Icc (0 : ℝ) 1) y) = y :=
    fun y hy => hθ.bijOn.invOn_invFunOn.2 hy
  have hinv0 : Function.invFunOn θ (Icc (0 : ℝ) 1) (θ 0) = 0 :=
    hθ.bijOn.invOn_invFunOn.1 ⟨le_rfl, zero_le_one⟩
  have hinv1 : Function.invFunOn θ (Icc (0 : ℝ) 1) (θ 1) = 1 :=
    hθ.bijOn.invOn_invFunOn.1 ⟨zero_le_one, le_rfl⟩
  refine ⟨Φ₁ ∘ ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hPA₁.comp hψPA
    convert h using 1
    exact (Set.inter_eq_self_of_subset_left (fun z hz => hψmaps hz)).symm
  · exact fun z hz => hmaps₁ (hψmaps hz)
  · intro y hy
    have hz : ψ (y, 0) = (Function.invFunOn θ (Icc (0 : ℝ) 1) y, 0) := rfl
    rw [Function.comp_apply, hz,
      hbot₁ _ (hθ.bijOn.surjOn.mapsTo_invFunOn hy), Function.comp_apply, hinv y hy]
  · intro y hy
    have hz : ψ (y, 1) = (Function.invFunOn θ (Icc (0 : ℝ) 1) y, 1) := rfl
    rw [Function.comp_apply, hz,
      htop₁ _ (hθ.bijOn.surjOn.mapsTo_invFunOn hy), Function.comp_apply, hinv y hy]
  · intro t ht
    have hz : ψ (θ 0, t) = ((0 : ℝ), t) := by rw [hψ]; simp [hinv0]
    rw [Function.comp_apply, hz, hl₁ t ht]
    rfl
  · intro t ht
    have hz : ψ (θ 1, t) = ((1 : ℝ), t) := by rw [hψ]; simp [hinv1]
    rw [Function.comp_apply, hz, hr₁ t ht]
    rfl

open Classical in
theorem exists_isPiecewiseAffineOn_prism_of_isPLSphere_one {J : Set E} (hJ : IsPLSphere 1 J)
    {f g : E → F} (hf : IsPiecewiseAffineOn f J) (hg : IsPiecewiseAffineOn g J) :
    ∃ Φ : E × ℝ → F, IsPiecewiseAffineOn Φ (J ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ y ∈ J, Φ (y, 0) = f y) ∧ (∀ y ∈ J, Φ (y, 1) = g y) ∧
      (∀ (S : Set F), Convex ℝ S → MapsTo f J S → MapsTo g J S →
        MapsTo Φ (J ×ˢ Icc (0 : ℝ) 1) S) := by
  classical
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_ne_mem_of_isPLSphere_one hJ
  obtain ⟨A, B, γ, δ, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hunion, hinter⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hJ hp hq hpq
  have hone : (0 : ℝ) < 1 := by norm_num
  have hApoly : IsPolyhedron A := ((isPLBall_Icc hone).of_isPLHomeomorphOn hγ).isPolyhedron
  have hBpoly : IsPolyhedron B := ((isPLBall_Icc hone).of_isPLHomeomorphOn hδ).isPolyhedron
  have hAJ : A ⊆ J := by rw [← hunion]; exact subset_union_left
  have hBJ : B ⊆ J := by rw [← hunion]; exact subset_union_right
  obtain ⟨ΦA, hPAA, hbotA, htopA, hlA, hrA, hSA⟩ :=
    exists_isPiecewiseAffineOn_prism_of_isPLHomeomorphOn hγ
      (hf.mono_of_isPolyhedron hApoly hAJ) (hg.mono_of_isPolyhedron hApoly hAJ)
  obtain ⟨ΦB, hPAB, hbotB, htopB, hlB, hrB, hSB⟩ :=
    exists_isPiecewiseAffineOn_prism_of_isPLHomeomorphOn hδ
      (hf.mono_of_isPolyhedron hBpoly hBJ) (hg.mono_of_isPolyhedron hBpoly hBJ)
  have hsets : A ×ˢ Icc (0 : ℝ) 1 ∪ B ×ˢ Icc (0 : ℝ) 1 = J ×ˢ Icc (0 : ℝ) 1 := by
    rw [← union_prod, hunion]
  have heq : EqOn ΦA ΦB (A ×ˢ Icc (0 : ℝ) 1 ∩ B ×ˢ Icc (0 : ℝ) 1) := by
    rintro ⟨y, t⟩ ⟨⟨hyA, ht⟩, hyB, -⟩
    have hy : y ∈ A ∩ B := ⟨hyA, hyB⟩
    rw [hinter] at hy
    rcases hy with rfl | rfl
    · have e1 := hlA t ht
      have e2 := hlB t ht
      rw [hγ0] at e1
      rw [hδ0] at e2
      rw [e1, e2]
    · have e1 := hrA t ht
      have e2 := hrB t ht
      rw [hγ1] at e1
      rw [hδ1] at e2
      rw [e1, e2]
  set G : E × ℝ → F := @Set.piecewise (E × ℝ) (fun _ => F) (A ×ˢ Icc (0 : ℝ) 1) ΦA ΦB
    (fun j => Classical.propDecidable _) with hGdef
  have hGmem : ∀ z ∈ A ×ˢ Icc (0 : ℝ) 1, G z = ΦA z := by
    intro z hz
    rw [hGdef]
    exact ite_eq_left hz
  have hGnot : ∀ z ∉ A ×ˢ Icc (0 : ℝ) 1, G z = ΦB z := by
    intro z hz
    rw [hGdef]
    exact ite_eq_right hz
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · rw [← hsets]
    exact hPAA.piecewise_of_isClosed hPAB (hApoly.isClosed.prod isClosed_Icc)
      (hBpoly.isClosed.prod isClosed_Icc) heq
  · intro y hy
    by_cases hyA : y ∈ A
    · rw [hGmem _ ⟨hyA, le_rfl, zero_le_one⟩]
      exact hbotA y hyA
    · rw [hGnot _ (fun h => hyA h.1)]
      exact hbotB y ((hunion ▸ hy).resolve_left hyA)
  · intro y hy
    by_cases hyA : y ∈ A
    · rw [hGmem _ ⟨hyA, zero_le_one, le_rfl⟩]
      exact htopA y hyA
    · rw [hGnot _ (fun h => hyA h.1)]
      exact htopB y ((hunion ▸ hy).resolve_left hyA)
  · intro S hS hfS hgS z hz
    by_cases hzA : z ∈ A ×ˢ Icc (0 : ℝ) 1
    · rw [hGmem _ hzA]
      exact hSA S hS (fun y hy => hfS (hAJ hy)) (fun y hy => hgS (hAJ hy)) hzA
    · rw [hGnot _ hzA]
      refine hSB S hS (fun y hy => hfS (hBJ hy)) (fun y hy => hgS (hBJ hy)) ?_
      rw [← hsets] at hz
      exact hz.resolve_left hzA

open Classical in
theorem exists_isPiecewiseAffineOn_prism_of_arcs_mapsTo_space
    (L : Geometry.SimplicialComplex ℝ F) {J A B : Set E} {γ κ : ℝ → E} {p q : E}
    (hγ : IsPLHomeomorphOn γ (Icc (0 : ℝ) 1) A) (hκ : IsPLHomeomorphOn κ (Icc (0 : ℝ) 1) B)
    (hγ0 : γ 0 = p) (hγ1 : γ 1 = q) (hκ0 : κ 0 = p) (hκ1 : κ 1 = q)
    (hunion : A ∪ B = J) (hinter : A ∩ B = {p, q})
    {f g : E → F} (hf : IsPiecewiseAffineOn f J) (hg : IsPiecewiseAffineOn g J)
    {δ : ℝ} (hδ : 0 < δ) (T : Finset ℝ) (hT : ∀ x ∈ T, x ∈ Icc (0 : ℝ) 1)
    (hfaceγ : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b → b - a < δ →
      (∀ x ∈ T, ¬(a < x ∧ x < b)) →
      ∃ u ∈ L.faces, ({f (γ a), f (γ b), g (γ a), g (γ b)} : Set F) ⊆ convexHull ℝ (u : Set F))
    (hfaceκ : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b → b - a < δ →
      (∀ x ∈ T, ¬(a < x ∧ x < b)) →
      ∃ u ∈ L.faces, ({f (κ a), f (κ b), g (κ a), g (κ b)} : Set F) ⊆ convexHull ℝ (u : Set F)) :
    ∃ Φ : E × ℝ → F, IsPiecewiseAffineOn Φ (J ×ˢ Icc (0 : ℝ) 1) ∧
      MapsTo Φ (J ×ˢ Icc (0 : ℝ) 1) L.space ∧
      (∀ y ∈ J, Φ (y, 0) = f y) ∧ (∀ y ∈ J, Φ (y, 1) = g y) := by
  classical
  have hone : (0 : ℝ) < 1 := by norm_num
  have hApoly : IsPolyhedron A := ((isPLBall_Icc hone).of_isPLHomeomorphOn hγ).isPolyhedron
  have hBpoly : IsPolyhedron B := ((isPLBall_Icc hone).of_isPLHomeomorphOn hκ).isPolyhedron
  have hAJ : A ⊆ J := by rw [← hunion]; exact subset_union_left
  have hBJ : B ⊆ J := by rw [← hunion]; exact subset_union_right
  obtain ⟨ΦA, hPAA, hmapA, hbotA, htopA, hlA, hrA⟩ :=
    exists_isPiecewiseAffineOn_prism_of_isPLHomeomorphOn_mapsTo_space L hγ
      (hf.mono_of_isPolyhedron hApoly hAJ) (hg.mono_of_isPolyhedron hApoly hAJ) hδ T hT hfaceγ
  obtain ⟨ΦB, hPAB, hmapB, hbotB, htopB, hlB, hrB⟩ :=
    exists_isPiecewiseAffineOn_prism_of_isPLHomeomorphOn_mapsTo_space L hκ
      (hf.mono_of_isPolyhedron hBpoly hBJ) (hg.mono_of_isPolyhedron hBpoly hBJ) hδ T hT hfaceκ
  have hsets : A ×ˢ Icc (0 : ℝ) 1 ∪ B ×ˢ Icc (0 : ℝ) 1 = J ×ˢ Icc (0 : ℝ) 1 := by
    rw [← union_prod, hunion]
  have heq : EqOn ΦA ΦB (A ×ˢ Icc (0 : ℝ) 1 ∩ B ×ˢ Icc (0 : ℝ) 1) := by
    rintro ⟨y, t⟩ ⟨⟨hyA, ht⟩, hyB, -⟩
    have hy : y ∈ A ∩ B := ⟨hyA, hyB⟩
    rw [hinter] at hy
    rcases hy with rfl | rfl
    · have e1 := hlA t ht
      have e2 := hlB t ht
      rw [hγ0] at e1
      rw [hκ0] at e2
      rw [e1, e2]
    · have e1 := hrA t ht
      have e2 := hrB t ht
      rw [hγ1] at e1
      rw [hκ1] at e2
      rw [e1, e2]
  set G : E × ℝ → F := @Set.piecewise (E × ℝ) (fun _ => F) (A ×ˢ Icc (0 : ℝ) 1) ΦA ΦB
    (fun j => Classical.propDecidable _) with hGdef
  have hGmem : ∀ z ∈ A ×ˢ Icc (0 : ℝ) 1, G z = ΦA z := by
    intro z hz
    rw [hGdef]
    exact ite_eq_left hz
  have hGnot : ∀ z ∉ A ×ˢ Icc (0 : ℝ) 1, G z = ΦB z := by
    intro z hz
    rw [hGdef]
    exact ite_eq_right hz
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · rw [← hsets]
    exact hPAA.piecewise_of_isClosed hPAB (hApoly.isClosed.prod isClosed_Icc)
      (hBpoly.isClosed.prod isClosed_Icc) heq
  · intro z hz
    by_cases hzA : z ∈ A ×ˢ Icc (0 : ℝ) 1
    · rw [hGmem _ hzA]
      exact hmapA hzA
    · rw [hGnot _ hzA]
      refine hmapB ?_
      rw [← hsets] at hz
      exact hz.resolve_left hzA
  · intro y hy
    by_cases hyA : y ∈ A
    · rw [hGmem _ ⟨hyA, le_rfl, zero_le_one⟩]
      exact hbotA y hyA
    · rw [hGnot _ (fun h => hyA h.1)]
      exact hbotB y ((hunion ▸ hy).resolve_left hyA)
  · intro y hy
    by_cases hyA : y ∈ A
    · rw [hGmem _ ⟨hyA, zero_le_one, le_rfl⟩]
      exact htopA y hyA
    · rw [hGnot _ (fun h => hyA h.1)]
      exact htopB y ((hunion ▸ hy).resolve_left hyA)

end DifferentialGeometry.Topology.PiecewiseLinear

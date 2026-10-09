/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndMap
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.PLSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PrismDiskPair
import DifferentialGeometry.Topology.PiecewiseLinear.PrismFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBall
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.SphereGluing
import DifferentialGeometry.Topology.PiecewiseLinear.SphereSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitLocalTrace

open Set Topology

namespace DifferentialGeometry.Topology

namespace PiecewiseLinear

section General

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem isPLSphere_union_of_inter_eq_image_stdSimplexBoundary {P Q : Set E}
    {p q : (Fin 3 → ℝ) → E} (hp : IsPLHomeomorphOn p (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P)
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q)
    (hPQ : P ∩ Q = p '' stdSimplexBoundary 2)
    (hpq : q '' stdSimplexBoundary 2 = p '' stdSimplexBoundary 2) :
    IsPLSphere 2 (P ∪ Q) := by
  have hP : IsPLBall 2 P := ⟨p, hp⟩
  have hQ : IsPLBall 2 Q := ⟨q, hq⟩
  obtain ⟨KP, hKPfin, hKPspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  obtain ⟨KQ, hKQfin, hKQspace⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite KP.faces := hKPfin.to_subtype
  let _ : Finite KQ.faces := hKQfin.to_subtype
  have h₁ : p '' stdSimplexBoundary 2 = (boundaryComplex 2 KP).space :=
    hp.image_stdSimplexBoundary_eq_boundaryComplex KP hKPspace
  have h₂ : q '' stdSimplexBoundary 2 = (boundaryComplex 2 KQ).space :=
    hq.image_stdSimplexBoundary_eq_boundaryComplex KQ hKQspace
  have h := isPLSphere_union_of_isPLBall KP KQ (hKPspace.symm ▸ hP) (hKQspace.symm ▸ hQ)
    (by rw [hKPspace, hKQspace, hPQ, h₁]) (by rw [hKPspace, hKQspace, hPQ, ← hpq, h₂])
  rwa [hKPspace, hKQspace] at h

open Classical in
theorem IsPLHomeomorphOn.image_image_stdSimplexBoundary {P : Set E} {Q : Set F}
    {p : (Fin 3 → ℝ) → E} {q : (Fin 3 → ℝ) → F}
    (hp : IsPLHomeomorphOn p (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P)
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q) {f : E → F}
    (hf : IsPLHomeomorphOn f P Q) :
    f '' (p '' stdSimplexBoundary 2) = q '' stdSimplexBoundary 2 := by
  have hP : IsPLBall 2 P := ⟨p, hp⟩
  obtain ⟨KP, hKPfin, hKPspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  have hQ : IsPLBall 2 Q := ⟨q, hq⟩
  obtain ⟨KQ, hKQfin, hKQspace⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite KP.faces := hKPfin.to_subtype
  let _ : Finite KQ.faces := hKQfin.to_subtype
  have h₁ : p '' stdSimplexBoundary 2 = (boundaryComplex 2 KP).space :=
    hp.image_stdSimplexBoundary_eq_boundaryComplex KP hKPspace
  have h₂ : q '' stdSimplexBoundary 2 = (boundaryComplex 2 KQ).space :=
    hq.image_stdSimplexBoundary_eq_boundaryComplex KQ hKQspace
  have hf' : IsPLHomeomorphOn f KP.space KQ.space := by
    rw [hKPspace, hKQspace]
    exact hf
  have h := boundaryComplex_space_of_isPLHomeomorphOn_of_isPLBall KP KQ
    (hKPspace.symm ▸ hP) hf'
  rw [h₁, h₂, h]

open Classical in
theorem IsPLBall.exists_prism_of_disjoint_frontier_disks (hdim : Module.finrank ℝ F = 3)
    {P : Set E} {p : (Fin 3 → ℝ) → E} (hp : IsPLHomeomorphOn p (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P)
    {W D₀ D₁ : Set F} (hW : IsPLBall 3 W) (hD₀W : D₀ ⊆ frontier W) (hD₁ : IsPLBall 2 D₁)
    (hD₁W : D₁ ⊆ frontier W) (hdis : Disjoint D₀ D₁) {g : E → F}
    (hg : IsPLHomeomorphOn g P D₀) :
    ∃ G : E × ℝ → F, IsPLHomeomorphOn G (P ×ˢ Icc (0 : ℝ) 1) W ∧
      (∀ x ∈ P, G (x, 0) = g x) ∧ G '' (P ×ˢ {(1 : ℝ)}) = D₁ ∧
      frontier W = G '' (P ×ˢ {(0 : ℝ), 1} ∪ (p '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) := by
  have hP : IsPLBall 2 P := ⟨p, hp⟩
  obtain ⟨KW, hKWfin, hKWspace⟩ := hW.isPolyhedron.exists_simplicialComplex
  let _ : Finite KW.faces := hKWfin.to_subtype
  have hKW : IsPLBall 3 KW.space := hKWspace.symm ▸ hW
  have hfr : frontier KW.space = (boundaryComplex 3 KW).space :=
    frontier_space_eq_boundaryComplex_space_of_finrank hdim KW
      hKW.isCombinatorialManifoldWithBoundary
  obtain ⟨G, hG, hG₀, hG₁⟩ := exists_isPLHomeomorphOn_prism_map_ends hP zero_lt_one KW hKW
    (by rw [← hfr, hKWspace]; exact hD₀W) hD₁ (by rw [← hfr, hKWspace]; exact hD₁W) hdis hg
  obtain ⟨L, hLfin, hLspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hGL : IsPLHomeomorphOn G (L.space ×ˢ Icc (0 : ℝ) 1) KW.space := by
    rw [hLspace]
    exact hG
  have hfront :=
    IsPLHomeomorphOn.frontier_prism_image L (hLspace.symm ▸ hP) zero_lt_one hGL hdim
  have hbd : p '' stdSimplexBoundary 2 = (boundaryComplex 2 L).space :=
    hp.image_stdSimplexBoundary_eq_boundaryComplex L hLspace
  rw [hKWspace] at hG hfront
  rw [hLspace, ← hbd] at hfront
  exact ⟨G, hG, hG₀, hG₁, hfront⟩

end General

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_annular_split_ball
    (M C Δ D₁ D₂ Ω : Set E3) (r r₁ r₂ : (Fin 3 → ℝ) → E3)
    (hM : IsOpen M) (hCM : C ⊆ M) (hC : IsClosed (((↑) : M → E3) ⁻¹' C))
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ) (hΔC : Δ ⊆ C)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁)
    (hr₂ : IsPLHomeomorphOn r₂ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₂)
    (hmeet : D₁ ∩ D₂ = Δ) (hDC : D₁ ∪ D₂ ⊆ C)
    (hnear : D₁ ∪ D₂ ∈ 𝓝ˢ[C] Δ)
    (hΔ₁ : Δ ⊆ D₁ \ r₁ '' stdSimplexBoundary 2)
    (hΔ₂ : Δ ⊆ D₂ \ r₂ '' stdSimplexBoundary 2)
    (hΩ : IsOpen Ω) (hΔΩ : Δ ⊆ Ω) (hΩM : Ω ⊆ M) :
    ∃ (A₁ Δ₁ J₁ Q O J S : Set E3) (r' : (Fin 3 → ℝ) → E3) (ψ : E3 × ℝ → E3),
      IsPLAnnulusWithEnds A₁ (r '' stdSimplexBoundary 2) J₁ ∧
      A₁ ⊆ D₁ ∩ Ω ∧ A₁ ∩ Δ = r '' stdSimplexBoundary 2 ∧
      IsPLHomeomorphOn r' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ₁ ∧
      J₁ = r' '' stdSimplexBoundary 2 ∧ Δ₁ ⊆ Ω ∧ Δ₁ ∩ C = J₁ ∧
      IsPLBall 3 Q ∧ Q ⊆ Ω ∧ A₁ ⊆ Q ∧ Δ₁ ⊆ Q ∧
      IsOpen O ∧ C ∩ O = A₁ \ (r '' stdSimplexBoundary 2 ∪ J₁) ∧
      IsPLSphere 1 J ∧ IsPLHomeomorphOn ψ (J ×ˢ Icc (0 : ℝ) 1) S ∧
      frontier Q \ ((C \ (A₁ \ (r '' stdSimplexBoundary 2 ∪ J₁))) ∪ Δ₁) =
        ψ '' (J ×ˢ Ioo (0 : ℝ) 1) ∧
      Disjoint (ψ '' (J ×ˢ Ioo (0 : ℝ) 1)) C := by
  let _ := hM
  let _ := hCM
  let _ := hC
  let _ := hΔC
  let _ := hΩM
  have hD₁ball : IsPLBall 2 D₁ := ⟨r₁, hr₁⟩
  have hD₂ball : IsPLBall 2 D₂ := ⟨r₂, hr₂⟩
  have hΔball : IsPLBall 2 Δ := ⟨r, hr⟩
  have hΔpoly : IsPolyhedron Δ := hΔball.isPolyhedron
  have hΔD₁ : Δ ⊆ D₁ := fun x hx => (hΔ₁ hx).1
  have hΔD₂ : Δ ⊆ D₂ := fun x hx => (hΔ₂ hx).1
  have hΔint₁ : Δ ⊆ r₁ '' openSimplex (stdVertices 1) := by
    rw [hr₁.image_openSimplex_stdVertices]
    exact hΔ₁
  have hΔint₂ : Δ ⊆ r₂ '' openSimplex (stdVertices 1) := by
    rw [hr₂.image_openSimplex_stdVertices]
    exact hΔ₂
  obtain ⟨T, hT, hTcard, hTsub⟩ := exists_affineIndependent_openSimplex_superset 3 (by simp)
    (hD₁ball.isPolyhedron.isCompact.union hD₂ball.isPolyhedron.isCompact).isBounded
  have hTball : IsPLBall 3 (convexHull ℝ (T : Set E3)) :=
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  obtain ⟨K, hKfin, hKspace⟩ := hTball.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hKball : IsPLBall 3 K.space := hKspace.symm ▸ hTball
  have hK : IsCombinatorialManifoldWithBoundary 3 K := hKball.isCombinatorialManifoldWithBoundary
  have hKint : interior K.space = openSimplex T := by
    rw [hKspace]
    exact interior_convexHull_eq_openSimplex hT (by simp [hTcard])
  have hDK : D₁ ∪ D₂ ⊆ interior K.space := hKint ▸ hTsub
  have hUo : IsOpen (Ω ∩ interior K.space) := hΩ.inter isOpen_interior
  have hΔU : Δ ⊆ Ω ∩ interior K.space := fun x hx => ⟨hΔΩ hx, hDK (Or.inl (hΔD₁ hx))⟩
  obtain ⟨N, B, g, q₁, Atr, Δbig, _, hBfin, hN, hB, hΔN, -, hNU, -, hBN, hg, -, hAtr, -,
      -, -, hboundary, -, -, hCtrace, -, -, hq₁, hD₁B, hJ₁B, hJ₁dis, -, -, hAtrbd⟩ :=
    hK.exists_surface_split_local_traces_with_side_trace hΔball hr₁ hr₂ hΔint₁ hΔint₂
      hΔD₁ hΔD₂ hmeet ((subset_union_left.trans hDK).trans interior_subset)
      ((subset_union_right.trans hDK).trans interior_subset)
      (subset_union_left.trans hDC) (subset_union_right.trans hDC) hnear
      (Filter.mem_inf_of_left (hUo.mem_nhdsSet.mpr hΔU))
      (by
        rw [← frontier_space_eq_boundaryComplex_space_of_finrank
          (d := fun a b => Classical.propDecidable (a = b)) (by simp) K hK]
        exact disjoint_left.mpr fun x hx hxF => hxF.2 hx.2)
  let _ : Finite B.faces := hBfin.to_subtype
  have hBK : IsCombinatorialManifoldWithBoundary 3 B := hB.isCombinatorialManifoldWithBoundary
  have hfrontB : frontier B.space = (D₂ ∩ N) ∪ Δbig := by
    rw [frontier_space_eq_boundaryComplex_space_of_finrank
      (d := fun a b => Classical.propDecidable (a = b)) (by simp) B hBK, hboundary]
  have hBclosed : IsClosed B.space := (isPolyhedron_space B).isClosed
  have hmidF : D₂ ∩ N ⊆ frontier B.space := hfrontB ▸ subset_union_left
  have hJ₁F : q₁ '' stdSimplexBoundary 2 ⊆ frontier B.space := by
    rw [hfrontB, ← hboundary]
    exact hJ₁B
  have hAtrF : Atr ∩ frontier B.space ⊆ (D₂ ∩ N) ∪ q₁ '' stdSimplexBoundary 2 := by
    rw [hfrontB, ← hboundary]
    exact hAtrbd
  have hSph : IsPLSphere 2 ((D₂ ∩ N) ∪ Δbig) := hfrontB ▸ hB.isPLSphere_frontier
  have hE₂ball : IsPLBall 2 (D₂ ∩ N) := ⟨g, hg⟩
  have hJ₁sph : IsPLSphere 1 (q₁ '' stdSimplexBoundary 2) :=
    hq₁.isPLSphere_image_stdSimplexBoundary
  obtain ⟨Δs, qs, hqs, hΔsS, hE₂Δs, hqsbd⟩ :=
    hSph.exists_isPLBall_with_boundary_disjoint_of_isPreconnected
      hE₂ball.isConnected.isPreconnected subset_union_left hJ₁sph (hfrontB ▸ hJ₁F)
      hJ₁dis.symm
  have hΔsball : IsPLBall 2 Δs := ⟨qs, hqs⟩
  have hΔsF : Δs ⊆ frontier B.space := hfrontB ▸ hΔsS
  have hΔE₂ : Δ ⊆ D₂ ∩ N := fun x hx => ⟨hΔD₂ hx, hΔN hx⟩
  have hΔΔs : Disjoint Δ Δs := hE₂Δs.mono_left hΔE₂
  have hJ₁Q₁ : q₁ '' stdSimplexBoundary 2 ⊆ D₁ ∩ N := by
    rw [← hq₁.image_eq]
    exact image_mono (fun x hx => hx.1)
  have hJ₁Δs : q₁ '' stdSimplexBoundary 2 ⊆ Δs := by
    rw [← hqsbd, ← hqs.image_eq]
    exact image_mono (fun x hx => hx.1)
  have hQ₁sub : D₁ ∩ N ⊆ Δ ∪ Atr := by
    rintro z ⟨hzD, hzN⟩
    by_cases hzΔ : z ∈ Δ
    · exact Or.inl hzΔ
    · rw [hAtr]
      exact Or.inr ⟨hzN, subset_closure ⟨hzD, hzΔ⟩⟩
  have hQ₁B : D₁ ∩ N ⊆ B.space := by
    rw [← hD₁B]
    exact inter_subset_right
  have hQ₁Δs : (D₁ ∩ N) ∩ Δs = q₁ '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro z ⟨hzQ, hzs⟩
      rcases hQ₁sub hzQ with hzΔ | hzA
      · exact (disjoint_left.mp hΔΔs hzΔ hzs).elim
      · rcases hAtrF ⟨hzA, hΔsF hzs⟩ with hz | hz
        · exact (disjoint_left.mp hE₂Δs hz hzs).elim
        · exact hz
    · exact fun z hz => ⟨hJ₁Q₁ hz, hJ₁Δs hz⟩
  have hSig := isPLSphere_union_of_inter_eq_image_stdSimplexBoundary hq₁ hqs hQ₁Δs hqsbd
  obtain ⟨W, hW, hWfront, -⟩ := hSig.exists_isPLBall_frontier_eq
  obtain ⟨G', hG', hG'₀, hG'₁, hG'front⟩ :=
    IsPLBall.exists_prism_of_disjoint_frontier_disks (by simp) hr hW
      (hWfront ▸ ((subset_inter hΔD₁ hΔN).trans subset_union_left))
      hΔsball (hWfront ▸ subset_union_right) hΔΔs hΔpoly.isPLHomeomorphOn_id
  set J := r '' stdSimplexBoundary 2 with hJdef
  have hJsph : IsPLSphere 1 J := hr.isPLSphere_image_stdSimplexBoundary
  have hJΔ : J ⊆ Δ := by
    rw [hJdef, ← hr.image_eq]
    exact image_mono (fun x hx => hx.1)
  have hG'inj := hG'.bijOn.injOn
  have hJI : J ×ˢ Icc (0 : ℝ) 1 ⊆ Δ ×ˢ Icc (0 : ℝ) 1 := prod_mono hJΔ Subset.rfl
  have hone : ({(1 : ℝ)} : Set ℝ) ⊆ Icc (0 : ℝ) 1 := singleton_subset_iff.mpr ⟨zero_le_one, le_rfl⟩
  set A₁ := G' '' (J ×ˢ Icc (0 : ℝ) 1) with hA₁def
  have hJ₁eq : G' '' (J ×ˢ {(1 : ℝ)}) = q₁ '' stdSimplexBoundary 2 := by
    have hf := (hΔpoly.isPLHomeomorphOn_prod_const 1).trans
      (hG'.restrict (isPolyhedron_prod_singleton hΔpoly 1) (prod_mono Subset.rfl hone))
    rw [hG'₁] at hf
    have h := IsPLHomeomorphOn.image_image_stdSimplexBoundary hr hqs hf
    rw [← hqsbd, ← h, image_comp, prod_singleton]
  have hA₁Δs : A₁ ∩ Δs = q₁ '' stdSimplexBoundary 2 := by
    rw [← hJ₁eq]
    apply Subset.antisymm
    · rintro z ⟨⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩, hzs⟩
      rw [← hG'₁] at hzs
      obtain ⟨⟨y, s⟩, ⟨hy, hs⟩, hys⟩ := hzs
      have heq := hG'inj (hJI ⟨hx, ht⟩) ⟨hy, hone hs⟩ hys.symm
      exact ⟨(x, t), ⟨hx, (congrArg Prod.snd heq).trans hs⟩, rfl⟩
    · rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      refine ⟨⟨(x, t), ⟨hx, hone ht⟩, rfl⟩, ?_⟩
      rw [← hG'₁]
      exact ⟨(x, t), ⟨hJΔ hx, ht⟩, rfl⟩
  have hJ₁A₁ : q₁ '' stdSimplexBoundary 2 ⊆ A₁ := hA₁Δs ▸ inter_subset_left
  have hA₁Q₁ : A₁ ⊆ D₁ ∩ N := by
    intro z hz
    have hzW : z ∈ frontier W := by
      rw [hG'front]
      exact image_mono subset_union_right hz
    rw [hWfront] at hzW
    rcases hzW with h | h
    · exact h
    · exact hJ₁Q₁ (hA₁Δs.subset ⟨hz, h⟩)
  have hA₁Δ : A₁ ∩ Δ = J := by
    apply Subset.antisymm
    · rintro z ⟨⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩, hzΔ⟩
      have heq := hG'inj (hJI ⟨hx, ht⟩)
        (show (G' (x, t), (0 : ℝ)) ∈ Δ ×ˢ Icc (0 : ℝ) 1 from ⟨hzΔ, le_rfl, zero_le_one⟩)
        (hG'₀ _ hzΔ).symm
      have hx' : x = G' (x, t) := congrArg Prod.fst heq
      rw [← hx']
      exact hx
    · intro z hz
      exact ⟨⟨(z, 0), ⟨hz, le_rfl, zero_le_one⟩, hG'₀ z (hJΔ hz)⟩, hJΔ hz⟩
  have hQ₁sub' : D₁ ∩ N ⊆ Δ ∪ A₁ := by
    intro z hz
    have hzW : z ∈ frontier W := by
      rw [hWfront]
      exact Or.inl hz
    rw [hG'front] at hzW
    obtain ⟨⟨y, t⟩, hyt, rfl⟩ := hzW
    rcases hyt with ⟨hy, ht⟩ | ⟨hy, ht⟩
    · rcases ht with ht | ht
      · have ht' : t = 0 := ht
        rw [ht', hG'₀ y hy]
        exact Or.inl hy
      · have hzs : G' (y, t) ∈ Δs := by
          rw [← hG'₁]
          exact ⟨(y, t), ⟨hy, ht⟩, rfl⟩
        exact Or.inr (hJ₁A₁ (hQ₁Δs.subset ⟨hz, hzs⟩))
    · exact Or.inr ⟨(y, t), ⟨hy, ht⟩, rfl⟩
  have hAtrQ₁ : Atr ⊆ D₁ ∩ N := by
    rw [hAtr]
    exact fun z hz => ⟨closure_minimal sdiff_subset hD₁ball.isPolyhedron.isClosed hz.2, hz.1⟩
  have hA₁E₂ : A₁ ∩ (D₂ ∩ N) ⊆ J := by
    rintro z ⟨hzA, hzD, -⟩
    rw [← hA₁Δ, ← hmeet]
    exact ⟨hzA, (hA₁Q₁ hzA).1, hzD⟩
  have hCO : C ∩ interior B.space = A₁ \ (J ∪ q₁ '' stdSimplexBoundary 2) := by
    apply Subset.antisymm
    · rintro z ⟨hzC, hzB⟩
      have hzF : z ∉ frontier B.space := fun h => h.2 hzB
      have hzCB : z ∈ (D₂ ∩ N) ∪ Atr := by
        rw [← hCtrace]
        exact ⟨hzC, interior_subset hzB⟩
      rcases hzCB with hzE | hzA
      · exact (hzF (hmidF hzE)).elim
      · rcases hQ₁sub' (hAtrQ₁ hzA) with hzΔ | hzA₁
        · exact (hzF (hmidF (hΔE₂ hzΔ))).elim
        · refine ⟨hzA₁, ?_⟩
          rintro (hzJ | hzJ₁)
          · exact hzF (hmidF (hΔE₂ (hJΔ hzJ)))
          · exact hzF (hJ₁F hzJ₁)
    · rintro z ⟨hzA, hzJ⟩
      have hzQ := hA₁Q₁ hzA
      refine ⟨hDC (Or.inl hzQ.1), (mem_interior_iff_notMem_frontier (hQ₁B hzQ)).mpr ?_⟩
      intro hzF
      have hzF' := hzF
      rw [hfrontB] at hzF'
      rcases hzF' with hzE | -
      · exact hzJ (Or.inl (hA₁E₂ ⟨hzA, hzE⟩))
      · have hzAtr : z ∈ Atr := by
          rcases hQ₁sub hzQ with hzΔ | hzAtr
          · exact (hzJ (Or.inl (hA₁Δ.subset ⟨hzA, hzΔ⟩))).elim
          · exact hzAtr
        rcases hAtrF ⟨hzAtr, hzF⟩ with hzE | hzJ₁
        · exact hzJ (Or.inl (hA₁E₂ ⟨hzA, hzE⟩))
        · exact hzJ (Or.inr hzJ₁)
  have hΔsC : Δs ∩ C = q₁ '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro z ⟨hzs, hzC⟩
      have hzCB : z ∈ (D₂ ∩ N) ∪ Atr := by
        rw [← hCtrace]
        exact ⟨hzC, hBclosed.frontier_subset (hΔsF hzs)⟩
      rcases hzCB with hzE | hzA
      · exact (disjoint_left.mp hE₂Δs hzE hzs).elim
      · rcases hAtrF ⟨hzA, hΔsF hzs⟩ with hzE | hzJ
        · exact (disjoint_left.mp hE₂Δs hzE hzs).elim
        · exact hzJ
    · exact fun z hz => ⟨hJ₁Δs hz, hDC (Or.inl (hJ₁Q₁ hz).1)⟩
  have hann : IsPLAnnulusWithEnds A₁ J (q₁ '' stdSimplexBoundary 2) := by
    refine ⟨J, G', hJsph,
      hG'.restrict (hJsph.isPolyhedron.prod (isPLBall_Icc zero_lt_one).isPolyhedron) hJI, ?_,
      hJ₁eq.symm⟩
    ext z
    constructor
    · intro hz
      exact ⟨(z, 0), ⟨hz, rfl⟩, hG'₀ z (hJΔ hz)⟩
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht' : t = 0 := ht
      rw [ht', hG'₀ x (hJΔ hx)]
      exact hx
  obtain ⟨G, hG, hG₀, hG₁, hGfront⟩ :=
    IsPLBall.exists_prism_of_disjoint_frontier_disks (by simp) hg hB hmidF hΔsball hΔsF hE₂Δs
      hE₂ball.isPolyhedron.isPLHomeomorphOn_id
  set Jg := g '' stdSimplexBoundary 2 with hJgdef
  have hJgsph : IsPLSphere 1 Jg := hg.isPLSphere_image_stdSimplexBoundary
  have hJgE₂ : Jg ⊆ D₂ ∩ N := by
    rw [hJgdef, ← hg.image_eq]
    exact image_mono (fun x hx => hx.1)
  have hGinj := hG.bijOn.injOn
  have hJgI : Jg ×ˢ Icc (0 : ℝ) 1 ⊆ (D₂ ∩ N) ×ˢ Icc (0 : ℝ) 1 := prod_mono hJgE₂ Subset.rfl
  have hE₂mem (x : E3) (hx : x ∈ Jg) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (hz : G (x, t) ∈ D₂ ∩ N) : t = 0 := by
    have heq := hGinj (hJgI ⟨hx, ht⟩)
      (show (G (x, t), (0 : ℝ)) ∈ (D₂ ∩ N) ×ˢ Icc (0 : ℝ) 1 from ⟨hz, le_rfl, zero_le_one⟩)
      (hG₀ _ hz).symm
    exact congrArg Prod.snd heq
  have hΔsmem (x : E3) (hx : x ∈ Jg) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (hz : G (x, t) ∈ Δs) : t = 1 := by
    rw [← hG₁] at hz
    obtain ⟨⟨y, s⟩, ⟨hy, hs⟩, hys⟩ := hz
    have heq := hGinj (hJgI ⟨hx, ht⟩) ⟨hy, hone hs⟩ hys.symm
    exact (congrArg Prod.snd heq).trans hs
  have hsafe : Disjoint (G '' (Jg ×ˢ Ioo (0 : ℝ) 1)) C := by
    rw [disjoint_left]
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ hzC
    have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    have hzF : G (x, t) ∈ frontier B.space := by
      rw [hGfront]
      exact ⟨(x, t), Or.inr ⟨hx, htI⟩, rfl⟩
    have hzCB : G (x, t) ∈ (D₂ ∩ N) ∪ Atr := by
      rw [← hCtrace]
      exact ⟨hzC, hBclosed.frontier_subset hzF⟩
    rcases hzCB with hzE | hzA
    · exact ht.1.ne' (hE₂mem x hx t htI hzE)
    · rcases hAtrF ⟨hzA, hzF⟩ with hzE | hzJ
      · exact ht.1.ne' (hE₂mem x hx t htI hzE)
      · exact ht.2.ne (hΔsmem x hx t htI (hJ₁Δs hzJ))
  have hfrontQ : frontier B.space \
      ((C \ (A₁ \ (J ∪ q₁ '' stdSimplexBoundary 2))) ∪ Δs) = G '' (Jg ×ˢ Ioo (0 : ℝ) 1) := by
    apply Subset.antisymm
    · rintro z ⟨hzF, hzn⟩
      have hzn₁ : z ∉ Δs := fun h => hzn (Or.inr h)
      have hzE : z ∉ D₂ ∩ N := fun h =>
        hzn (Or.inl ⟨hDC (Or.inr h.1), fun hzA => hzA.2 (Or.inl (hA₁E₂ ⟨hzA.1, h⟩))⟩)
      rw [hGfront] at hzF
      obtain ⟨⟨x, t⟩, hxt, rfl⟩ := hzF
      rcases hxt with ⟨hx, ht⟩ | ⟨hx, ht⟩
      · rcases ht with ht | ht
        · have ht' : t = 0 := ht
          rw [ht', hG₀ x hx] at hzE
          exact (hzE hx).elim
        · exact (hzn₁ (by rw [← hG₁]; exact ⟨(x, t), ⟨hx, ht⟩, rfl⟩)).elim
      · have ht' : t ∈ Icc (0 : ℝ) 1 := ht
        refine ⟨(x, t), ⟨hx, ?_, ?_⟩, rfl⟩
        · rcases ht'.1.lt_or_eq with h | h
          · exact h
          · rw [← h, hG₀ x (hJgE₂ hx)] at hzE
            exact (hzE (hJgE₂ hx)).elim
        · rcases ht'.2.lt_or_eq with h | h
          · exact h
          · exact (hzn₁ (by rw [← hG₁]; exact ⟨(x, t), ⟨hJgE₂ hx, h⟩, rfl⟩)).elim
    · rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
      refine ⟨by rw [hGfront]; exact ⟨(x, t), Or.inr ⟨hx, htI⟩, rfl⟩, ?_⟩
      rintro (⟨hzC, -⟩ | hzs)
      · exact disjoint_left.mp hsafe ⟨(x, t), ⟨hx, ht⟩, rfl⟩ hzC
      · exact ht.2.ne (hΔsmem x hx t htI hzs)
  exact ⟨A₁, Δs, q₁ '' stdSimplexBoundary 2, B.space, interior B.space, Jg,
    G '' (Jg ×ˢ Icc (0 : ℝ) 1), qs, G, hann,
    fun z hz => ⟨(hA₁Q₁ hz).1, (hNU (hA₁Q₁ hz).2).1⟩, hA₁Δ, hqs, hqsbd.symm,
    fun z hz => (hNU (hBN (hBclosed.frontier_subset (hΔsF hz)))).1, hΔsC, hB,
    fun z hz => (hNU (hBN hz)).1, fun z hz => hQ₁B (hA₁Q₁ hz),
    fun z hz => hBclosed.frontier_subset (hΔsF hz), isOpen_interior, hCO, hJgsph,
    hG.restrict (hJgsph.isPolyhedron.prod (isPLBall_Icc zero_lt_one).isPolyhedron) hJgI,
    hfrontQ, hsafe⟩

end PiecewiseLinear

end DifferentialGeometry.Topology

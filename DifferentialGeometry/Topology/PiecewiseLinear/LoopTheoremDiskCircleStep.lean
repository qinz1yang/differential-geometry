/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.HandlePieceChart
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.InnermostCleanDisk
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskMeetsPseudoCells
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskPushOff
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarOuterCollar
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellCircleDisk
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsLoopTheoremDisk.of_boundary_eq {Kimg N' B Δ Δ₁ : Set E3}
    (hΔ : IsLoopTheoremDisk Kimg N' B Δ) {r₁ : (Fin 3 → ℝ) → E3}
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ₁) (hsub : Δ₁ ⊆ interior N' \ Kimg)
    (hB : Δ₁ ∩ B = Δ ∩ B) (hbd : r₁ '' stdSimplexBoundary 2 = Δ ∩ B) :
    IsLoopTheoremDisk Kimg N' B Δ₁ := by
  obtain ⟨r, -, -, hΔB, hb, hnull⟩ := hΔ
  rw [hΔB] at hB hbd
  have key : ∀ S T : Set E3, S = T →
      (∃ hT : T ⊆ B, ¬ (⟨Set.inclusion hT, continuous_inclusion hT⟩ : C(T, B)).Nullhomotopic) →
      ∃ hS : S ⊆ B, ¬ (⟨Set.inclusion hS, continuous_inclusion hS⟩ : C(S, B)).Nullhomotopic := by
    rintro S T rfl hST
    exact hST
  exact ⟨r₁, hr₁, hsub, hB.trans hbd.symm, key _ _ hbd ⟨hb, hnull⟩⟩

theorem IsPLHomeomorphOn.exists_planarModel {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {Δ : Set F} {r : (Fin 3 → ℝ) → F}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ) :
    ∃ (Pl : Set (EuclideanSpace ℝ (Fin 2))) (ρ : EuclideanSpace ℝ (Fin 2) → F),
      IsPLBall 2 Pl ∧ IsPLHomeomorphOn ρ Pl Δ ∧ ρ '' frontier Pl = r '' stdSimplexBoundary 2 := by
  obtain ⟨T, hT, hTcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1)
    (0 : EuclideanSpace ℝ (Fin 2)) (Filter.univ_mem : univ ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 2)))
  have hball : IsPLBall 2 (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2)))) :=
    isPLBall_convexHull_of_affineIndependent T hT (by omega)
  obtain ⟨u, hu⟩ : ∃ u : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2)))) := hball
  refine ⟨convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2))),
    r ∘ Function.invFunOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)),
    ⟨u, hu⟩, hu.symm.trans hr, ?_⟩
  rw [← hu.image_stdSimplexBoundary_eq_frontier (n := 1)]
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    change r x = r (Function.invFunOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (u x))
    rw [hu.bijOn.invOn_invFunOn.1 hx.1]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨u x, ⟨x, hx, rfl⟩, ?_⟩
    change r (Function.invFunOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (u x)) = r x
    rw [hu.bijOn.invOn_invFunOn.1 hx.1]

section CircleStep

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsPolyhedralTubeNeighborhood.exists_isLoopTheoremDisk_circleStep
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    (h8 : ∀ v₁ ∈ K.vertices, ∀ e₁ ∈ K.faces, e₁.card = 2 →
      ∀ (Δ : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ → Δ ⊆ Cpp v₁ ∩ interior N' →
        Δ ∩ Ec e₁ = r '' stdSimplexBoundary 2 →
        (∃ DJ DJint : Set (EuclideanSpace ℝ (Fin 3)),
          IsTopologicalCellWithInterior 2 DJ DJint ∧ DJ ⊆ Ec e₁ ∧
            DJ \ DJint = r '' stdSimplexBoundary 2 ∧ h (e₁.centroid ℝ id) ∈ DJint) →
        (∀ e ∈ K.faces, e.card = 2 → e ≠ e₁ → Disjoint Δ (Ec e)) →
        (Δ ∩ h '' K.space).Nonempty)
    {Δ : Set E3} (hΔ : IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ)
    {Cs : Set (Set E3)} (hfin : Cs.Finite) (hdisj : Cs.PairwiseDisjoint id)
    (hA : Δ ∩ (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) = ⋃₀ Cs)
    (hCs : ∀ S ∈ Cs, (IsPLSphere 1 S ∧ Disjoint S (frontier XK.space)) ∨
      ∃ q : (Fin 2 → ℝ) → E3, IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) S ∧
        q '' stdSimplexBoundary 1 = S ∩ frontier XK.space)
    (hcirc : ∃ S ∈ Cs, IsPLSphere 1 S ∧ Disjoint S (frontier XK.space)) :
    ∃ (Δ' : Set E3) (Cs' : Set (Set E3)),
      IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ' ∧ Cs' ⊆ Cs ∧ Cs' ≠ Cs ∧
        Δ' ∩ (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) = ⋃₀ Cs' := by
  classical
  set A := ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e with hAdef
  have : Finite XK.faces := h2.facesFinite.to_subtype
  have hΔ₀ := hΔ
  obtain ⟨r, hr, hΔsub, hΔB, -, -⟩ := hΔ₀
  have hCsΔ : ∀ S ∈ Cs, S ⊆ Δ := fun S hS y hy =>
    ((hA.symm ▸ mem_sUnion_of_mem hy hS : y ∈ Δ ∩ A)).1
  have hCsA : ∀ S ∈ Cs, S ⊆ A := fun S hS y hy =>
    ((hA.symm ▸ mem_sUnion_of_mem hy hS : y ∈ Δ ∩ A)).2
  have hCspoly : ∀ S ∈ Cs, IsPolyhedron S := by
    intro S hS
    rcases hCs S hS with ⟨hSs, -⟩ | ⟨q, hq, -⟩
    · exact hSs.isPolyhedron
    · exact IsPLBall.isPolyhedron (n := 1) ⟨q, hq⟩
  have hCspre : ∀ S ∈ Cs, IsPreconnected S := by
    intro S hS
    rcases hCs S hS with ⟨hSs, -⟩ | ⟨q, hq, -⟩
    · exact hSs.isConnected_one.isPreconnected
    · rw [← hq.image_eq]
      exact (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin 2)).isPreconnected.image q
        hq.isPiecewiseAffineOn.continuousOn
  have hstd1 : (stdSimplexBoundary 1).Nonempty :=
    ⟨Pi.single 0 1, Convexity.StdSimplex.single_mem_coordinateSet ℝ 0, 1, by simp⟩
  have hCsX : ∀ S ∈ Cs, ¬ (IsPLSphere 1 S ∧ Disjoint S (frontier XK.space)) →
      (S ∩ frontier XK.space).Nonempty := by
    intro S hS hn
    rcases hCs S hS with h1 | ⟨q, hq, hqb⟩
    · exact absurd h1 hn
    · rw [← hqb]
      exact hstd1.image q
  have hV : IsOpen (interior N' \ h '' K.space) :=
    isOpen_interior.sdiff hd.tube.isCompact_image_space.isClosed
  have hCppc : ∀ v ∈ K.vertices, IsClosed (Cpp v) := fun v hv => by
    rw [hd.componentClosure v hv]
    exact isClosed_closure
  obtain ⟨Pl, ρ, hPl, hρ, hρb⟩ := hr.exists_planarModel
  set σρ := Function.invFunOn ρ Pl with hσρdef
  have hσρ : IsPLHomeomorphOn σρ Δ Pl := hρ.symm
  have hρσ : ∀ y ∈ Δ, ρ (σρ y) = y := fun y hy => hρ.bijOn.invOn_invFunOn.2 hy
  have hσρρ : ∀ x ∈ Pl, σρ (ρ x) = x := fun x hx => hρ.bijOn.invOn_invFunOn.1 hx
  have hρc : ContinuousOn ρ Pl := hρ.isPiecewiseAffineOn.continuousOn
  have hσρc : ContinuousOn σρ Δ := hσρ.isPiecewiseAffineOn.continuousOn
  have hρinj : InjOn ρ Pl := hρ.bijOn.injOn
  have hPlc : IsCompact Pl := hPl.isPolyhedron.isCompact
  have hPlcl : IsClosed Pl := hPlc.isClosed
  have hfrPl : frontier Pl ⊆ Pl := hPlcl.frontier_subset
  have hPlΔ : ∀ {T : Set (EuclideanSpace ℝ (Fin 2))}, T ⊆ Pl → ρ '' T ⊆ Δ :=
    fun hT => (image_mono hT).trans hρ.image_eq.subset
  have hbdry : ∀ y ∈ Δ, (y ∈ frontier XK.space ↔ σρ y ∈ frontier Pl) := by
    intro y hy
    constructor
    · intro hyX
      have hy' : y ∈ ρ '' frontier Pl := by
        rw [hρb, ← hΔB]
        exact ⟨hy, hyX⟩
      obtain ⟨x, hx, rfl⟩ := hy'
      rwa [hσρρ x (hfrPl hx)]
    · intro hx
      have h1 : y ∈ Δ ∩ frontier XK.space := by
        rw [hΔB, ← hρb]
        exact ⟨σρ y, hx, hρσ y hy⟩
      exact h1.2
  have hpreimg : ∀ S ∈ Cs, ∀ x ∈ Pl, (x ∈ σρ '' S ↔ ρ x ∈ S) := by
    intro S hS x hx
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [hρσ y (hCsΔ S hS hy)]
    · intro hxS
      exact ⟨ρ x, hxS, hσρρ x hx⟩
  have hpreSub : ∀ S ∈ Cs, σρ '' S ⊆ Pl := fun S hS =>
    image_subset_iff.mpr fun y hy => hσρ.bijOn.mapsTo (hCsΔ S hS hy)
  have hρσimg : ∀ S ∈ Cs, ρ '' (σρ '' S) = S := by
    intro S hS
    rw [image_image]
    exact (image_congr fun y hy => hρσ y (hCsΔ S hS hy)).trans (image_id' S)
  have hdisjimg : ∀ S ∈ Cs, ∀ T ∈ Cs, S ≠ T → Disjoint (σρ '' S) (σρ '' T) := by
    intro S hS T hT hST
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
    have hzy' := hσρ.bijOn.injOn (hCsΔ T hT hz) (hCsΔ S hS hy) hzy
    exact Set.disjoint_left.mp (hdisj hS hT hST) hy (hzy' ▸ hz)
  set Circ := {S ∈ Cs | IsPLSphere 1 S ∧ Disjoint S (frontier XK.space)} with hCircdef
  have hsphere' : ∀ S ∈ Circ, IsPLSphere 1 (σρ '' S) := fun S hS =>
    hS.2.1.of_isPLHomeomorphOn (hσρ.restrict hS.2.1.isPolyhedron (hCsΔ S hS.1))
  have hintPl : ∀ S ∈ Circ, σρ '' S ⊆ interior Pl := by
    intro S hS
    rintro _ ⟨y, hy, rfl⟩
    rw [← self_sdiff_frontier]
    exact ⟨hσρ.bijOn.mapsTo (hCsΔ S hS.1 hy), fun hx =>
      Set.disjoint_left.mp hS.2.2 hy ((hbdry y (hCsΔ S hS.1 hy)).mpr hx)⟩
  have hC'fin : ((fun S => σρ '' S) '' Circ).Finite := (hfin.subset fun S hS => hS.1).image _
  have hC'ne : ((fun S => σρ '' S) '' Circ).Nonempty := by
    obtain ⟨S, hS, hSs⟩ := hcirc
    exact ⟨_, S, ⟨hS, hSs⟩, rfl⟩
  have hC'disj : ((fun S => σρ '' S) '' Circ).PairwiseDisjoint id := by
    rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩ hne
    exact hdisjimg S hS.1 T hT.1 fun h' => hne (h' ▸ rfl)
  obtain ⟨_, ⟨J₀, hJ₀, rfl⟩, Q, hQball, hQint, hfrQ, hQinter, -⟩ :=
    exists_innermost_isPLBall_subset_interior_of_pairwiseDisjoint hPl hC'fin hC'ne
      (by rintro _ ⟨S, hS, rfl⟩; exact hsphere' S hS)
      (by rintro _ ⟨S, hS, rfl⟩; exact hintPl S hS) hC'disj
  obtain ⟨hJ₀Cs, hJ₀s, hJ₀X⟩ := hJ₀
  change frontier Q = σρ '' J₀ at hfrQ
  change (⋃₀ ((fun S => σρ '' S) '' Circ)) ∩ Q = σρ '' J₀ at hQinter
  have hQPl : Q ⊆ Pl := hQint.trans interior_subset
  have hQpoly : IsPolyhedron Q := hQball.isPolyhedron
  have hQcl : IsClosed Q := hQpoly.isClosed
  have hQmiss : ∀ S ∈ Cs, S ≠ J₀ → Disjoint (σρ '' S) Q := by
    intro S hS hSJ
    by_cases hSc : IsPLSphere 1 S ∧ Disjoint S (frontier XK.space)
    · refine Set.disjoint_left.mpr fun x hxS hxQ => ?_
      have hx : x ∈ (⋃₀ ((fun S => σρ '' S) '' Circ)) ∩ Q :=
        ⟨mem_sUnion_of_mem hxS ⟨S, ⟨hS, hSc⟩, rfl⟩, hxQ⟩
      rw [hQinter] at hx
      exact Set.disjoint_left.mp (hdisjimg S hS J₀ hJ₀Cs hSJ) hxS hx
    · obtain ⟨y, hyS, hyX⟩ := hCsX S hS hSc
      have hyfr : σρ y ∈ frontier Pl := (hbdry y (hCsΔ S hS hyS)).mp hyX
      have hpre : IsPreconnected (σρ '' S) := (hCspre S hS).image σρ (hσρc.mono (hCsΔ S hS))
      have hfrQJ : Disjoint (σρ '' S) (frontier Q) := hfrQ ▸ hdisjimg S hS J₀ hJ₀Cs hSJ
      have hcov : σρ '' S ⊆ interior Q ∪ Qᶜ := by
        intro x hx
        by_cases hxQ : x ∈ Q
        · left
          rw [← self_sdiff_frontier]
          exact ⟨hxQ, fun hfx => Set.disjoint_left.mp hfrQJ hx hfx⟩
        · exact Or.inr hxQ
      rcases hpre.subset_or_subset isOpen_interior hQcl.isOpen_compl
          (disjoint_compl_right.mono_left interior_subset) hcov with h1 | h1
      · exact absurd hyfr (Set.disjoint_left.mp disjoint_interior_frontier
          (hQint (interior_subset (h1 ⟨y, hyS, rfl⟩))))
      · exact Set.disjoint_left.mpr fun x hx hxQ => h1 hx hxQ
  obtain ⟨q₀, hq₀⟩ := id hQball
  have hr₀ : IsPLHomeomorphOn (ρ ∘ q₀) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (ρ '' Q) :=
    hq₀.trans (hρ.restrict hQpoly hQPl)
  have hr₀b : (ρ ∘ q₀) '' stdSimplexBoundary 2 = J₀ := by
    rw [image_comp, hq₀.image_stdSimplexBoundary_eq_frontier (n := 1), hfrQ, hρσimg J₀ hJ₀Cs]
  have hΔ₀A : ρ '' Q ∩ A = J₀ := by
    apply Subset.antisymm
    · rintro _ ⟨⟨x, hxQ, rfl⟩, hxA⟩
      have hxPl := hQPl hxQ
      obtain ⟨S, hS, hxS⟩ := mem_sUnion.mp (hA.subset ⟨hρ.bijOn.mapsTo hxPl, hxA⟩)
      by_cases hSJ : S = J₀
      · exact hSJ ▸ hxS
      · exact absurd hxQ (Set.disjoint_left.mp (hQmiss S hS hSJ)
          ((hpreimg S hS x hxPl).mpr hxS))
    · intro y hy
      refine ⟨?_, hCsA J₀ hJ₀Cs hy⟩
      rw [← hρσimg J₀ hJ₀Cs] at hy
      exact image_mono (hfrQ ▸ hQcl.frontier_subset) hy
  have hQΔ : ρ '' Q ⊆ Δ := hPlΔ hQPl
  have hZpre : IsPreconnected (ρ '' interior Q) :=
    hQball.isConnected_interior.isPreconnected.image ρ (hρc.mono (interior_subset.trans hQPl))
  have hZne : (ρ '' interior Q).Nonempty := hQball.interior_nonempty.image ρ
  have hZN : ρ '' interior Q ⊆ interior N' := fun y hy =>
    (hΔsub (hPlΔ (interior_subset.trans hQPl) hy)).1
  have hZA : Disjoint (ρ '' interior Q) A := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ hxA
    have h1 : ρ x ∈ ρ '' Q ∩ A := ⟨mem_image_of_mem ρ (interior_subset hx), hxA⟩
    rw [hΔ₀A] at h1
    have h2 : x ∈ σρ '' J₀ := (hpreimg J₀ hJ₀Cs x (hQPl (interior_subset hx))).mpr h1
    rw [← hfrQ] at h2
    exact h2.2 hx
  obtain ⟨v₀, hv₀, hZv₀⟩ := hd.exists_subset_handlePiece hZpre hZne hZN hZA
  have hΔ₀v : ρ '' Q ⊆ Cpp v₀ := by
    have h1 : ρ '' Q ⊆ closure (ρ '' interior Q) := by
      conv_lhs => rw [← hQball.closure_interior]
      exact (hρc.mono (hQball.closure_interior.symm ▸ hQPl)).image_closure
    exact h1.trans (closure_minimal hZv₀ (hCppc v₀ hv₀))
  obtain ⟨y₀, hy₀⟩ := hJ₀s.nonempty
  obtain ⟨e₀, ⟨he₀, hcard₀⟩, hy₀e⟩ := mem_iUnion₂.mp (hCsA J₀ hJ₀Cs hy₀)
  have hJ₀e : J₀ ⊆ Ec e₀ := hd.subset_pseudoCell_of_isPreconnected (hCspre J₀ hJ₀Cs)
    (hCsA J₀ hJ₀Cs) he₀ hcard₀ ⟨y₀, hy₀, hy₀e⟩
  have hΔ₀E : ρ '' Q ∩ Ec e₀ = (ρ ∘ q₀) '' stdSimplexBoundary 2 := by
    rw [hr₀b]
    apply Subset.antisymm
    · intro y hy
      rw [← hΔ₀A]
      exact ⟨hy.1, mem_iUnion₂.mpr ⟨e₀, ⟨he₀, hcard₀⟩, hy.2⟩⟩
    · intro y hy
      exact ⟨(hΔ₀A.symm.subset hy).1, hJ₀e hy⟩
  have hgood : ¬ ∃ DJ DJint : Set E3, IsTopologicalCellWithInterior 2 DJ DJint ∧
      DJ ⊆ Ec e₀ ∧ DJ \ DJint = J₀ ∧ h (e₀.centroid ℝ id) ∈ DJint := by
    rintro ⟨DJ, DJint, hc, hsub, hsd, hP⟩
    obtain ⟨y, hyΔ, hyK⟩ := h8 v₀ hv₀ e₀ he₀ hcard₀ (ρ '' Q) (ρ ∘ q₀) hr₀
      (fun y hy => ⟨hΔ₀v hy, (hΔsub (hQΔ hy)).1⟩) hΔ₀E
      ⟨DJ, DJint, hc, hsub, hsd.trans hr₀b.symm, hP⟩
      (fun e he hcard hne => by
        refine Set.disjoint_left.mpr fun y hyQ hye => ?_
        have hyJ : y ∈ J₀ := hΔ₀A ▸ ⟨hyQ, mem_iUnion₂.mpr ⟨e, ⟨he, hcard⟩, hye⟩⟩
        exact Set.disjoint_left.mp (hd.pseudoCellDisjoint e₀ he₀ hcard₀ e he hcard hne.symm)
          (hJ₀e hyJ) hye)
    exact (hΔsub (hQΔ hyΔ)).2 hyK
  obtain ⟨c, hcCs, Dc, rc, hcs, hce, hcX, hrc, hrcb, hDcE, hDcN, hDcX, hDcΔ⟩ :=
    h2.exists_circle_eDisk hd h34 he₀ hcard₀ hΔsub hfin hdisj hA
      (fun S hS => ⟨hCspre S hS, by
        by_cases hSc : IsPLSphere 1 S ∧ Disjoint S (frontier XK.space)
        · exact Or.inl hSc
        · exact Or.inr (hCsX S hS hSc)⟩)
      hJ₀Cs hJ₀e hJ₀s hJ₀X hgood
  have hcCirc : c ∈ Circ := ⟨hcCs, hcs, hcX⟩
  have hc's : IsPLSphere 1 (σρ '' c) := hsphere' c hcCirc
  have hc'int : σρ '' c ⊆ interior Pl := hintPl c hcCirc
  have hc'J : Schoenflies.IsJordanCurve (σρ '' c) := isJordanCurve_of_isPLSphere_one hc's
  have hQc : IsPLBall 2 (closure (Schoenflies.inside (σρ '' c))) :=
    isPLBall_closure_inside_of_isPLSphere_one hc's
  have hQcint : closure (Schoenflies.inside (σρ '' c)) ⊆ interior Pl :=
    closure_inside_subset_interior_of_subset_interior hPl hc'J hc'int
  have hQcPl : closure (Schoenflies.inside (σρ '' c)) ⊆ Pl := hQcint.trans interior_subset
  have hfrQc : frontier (closure (Schoenflies.inside (σρ '' c))) = σρ '' c :=
    frontier_closure_inside_of_isPLSphere_one hc's
  set Qc := closure (Schoenflies.inside (σρ '' c)) with hQcdef
  have hQccl : IsClosed Qc := isClosed_closure
  set Pc' := closure (Pl \ Qc) with hPc'def
  have hPc'Pl : Pc' ⊆ Pl := closure_minimal sdiff_subset hPlcl
  have hPc'int : Disjoint Pc' (interior Qc) :=
    ((Set.disjoint_left.mpr fun x hx hx' => hx'.2 (interior_subset hx)).closure_right
      isOpen_interior).symm
  have hPc'Qc : Pc' ∩ Qc = σρ '' c := by
    apply Subset.antisymm
    · rintro x ⟨hxP, hxQ⟩
      rw [← hfrQc]
      exact ⟨subset_closure hxQ, fun hxi => Set.disjoint_left.mp hPc'int hxP hxi⟩
    · intro x hx
      have hxfr : x ∈ frontier Qc := hfrQc.symm ▸ hx
      refine ⟨?_, hQccl.frontier_subset hxfr⟩
      rw [mem_closure_iff]
      intro U hU hxU
      have hU' : U ∩ interior Pl ∈ 𝓝 x :=
        Filter.inter_mem (hU.mem_nhds hxU) (isOpen_interior.mem_nhds (hc'int hx))
      obtain ⟨z, ⟨hzU, hzP⟩, hzQ⟩ :=
        mem_closure_iff_nhds.mp (frontier_eq_closure_inter_closure.subset hxfr).2 _ hU'
      exact ⟨z, hzU, interior_subset hzP, hzQ⟩
  have hPc'Qc_union : Pc' ∪ Qc = Pl := by
    apply Subset.antisymm (union_subset hPc'Pl hQcPl)
    intro x hx
    by_cases hxQ : x ∈ Qc
    · exact Or.inr hxQ
    · exact Or.inl (subset_closure ⟨hx, hxQ⟩)
  have hfrPlPc' : frontier Pl ⊆ Pc' := fun x hx => subset_closure ⟨hfrPl hx, fun hxQ =>
    Set.disjoint_left.mp disjoint_interior_frontier (hQcint hxQ) hx⟩
  have hPc'poly : IsPolyhedron Pc' := hPl.isPolyhedron.closure_sdiff hQc.isPolyhedron
  have hPcpoly : IsPolyhedron (ρ '' Pc') := hPc'poly.image_of_isPiecewiseAffineOn
    (hρ.isPiecewiseAffineOn.mono_of_isPolyhedron hPc'poly hPc'Pl) (hρinj.mono hPc'Pl)
  have hΔccl : IsClosed (ρ '' Qc) :=
    ((hPlc.of_isClosed_subset hQccl hQcPl).image_of_continuousOn (hρc.mono hQcPl)).isClosed
  have hPcΔc : ρ '' Pc' ∩ ρ '' Qc = c := by
    rw [← hρinj.image_inter hPc'Pl hQcPl, hPc'Qc, hρσimg c hcCs]
  have hPcΔc_union : ρ '' Pc' ∪ ρ '' Qc = Δ := by
    rw [← image_union, hPc'Qc_union, hρ.image_eq]
  obtain ⟨qc, hqc⟩ := id hQc
  have hrΔc : IsPLHomeomorphOn (ρ ∘ qc) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (ρ '' Qc) :=
    hqc.trans (hρ.restrict hQc.isPolyhedron hQcPl)
  have hrΔcb : (ρ ∘ qc) '' stdSimplexBoundary 2 = c := by
    rw [image_comp, hqc.image_stdSimplexBoundary_eq_frontier (n := 1), hfrQc, hρσimg c hcCs]
  have hcPc : c ⊆ ρ '' Pc' := by
    rw [← hρσimg c hcCs]
    exact image_mono (hPc'Qc ▸ inter_subset_left)
  have hcDc : c ⊆ Dc := by
    rw [← hrcb, ← hrc.image_eq]
    exact image_mono fun x hx => hx.1
  have hPcDc : ρ '' Pc' ∩ Dc = c := by
    apply Subset.antisymm
    · intro y hy
      rw [← hDcΔ]
      exact ⟨hy.2, hPlΔ hPc'Pl hy.1⟩
    · exact subset_inter hcPc hcDc
  obtain ⟨H, hH, hHid⟩ :=
    exists_isPLHomeomorphOn_replace_ball hPcpoly hrΔc hrc hrΔcb hrcb hPcΔc hPcDc
  rw [hPcΔc_union] at hH
  have hr₁ : IsPLHomeomorphOn (H ∘ r) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (ρ '' Pc' ∪ Dc) := hr.trans hH
  have hbdΔ : r '' stdSimplexBoundary 2 ⊆ ρ '' Pc' := by
    rw [← hρb]
    exact image_mono hfrPlPc'
  have hr₁b : (H ∘ r) '' stdSimplexBoundary 2 = Δ ∩ frontier XK.space := by
    rw [image_comp, (hHid.mono hbdΔ).image_eq, image_id, hΔB]
  have hΔ₁sub : ρ '' Pc' ∪ Dc ⊆ interior N' \ h '' K.space :=
    union_subset ((hPlΔ hPc'Pl).trans hΔsub) hDcN
  have hΔ₁B : (ρ '' Pc' ∪ Dc) ∩ frontier XK.space = Δ ∩ frontier XK.space := by
    rw [union_inter_distrib_right, hDcX.inter_eq, union_empty]
    apply Subset.antisymm
    · exact inter_subset_inter_left _ (hPlΔ hPc'Pl)
    · intro y hy
      have h1 : y ∈ r '' stdSimplexBoundary 2 := hΔB ▸ hy
      exact ⟨hbdΔ h1, hy.2⟩
  have hΔ₁ : IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) (ρ '' Pc' ∪ Dc) :=
    hΔ.of_boundary_eq hr₁ hΔ₁sub hΔ₁B hr₁b
  set Cs' := {S ∈ Cs | S ≠ c ∧ S ⊆ ρ '' Pc'} with hCs'def
  have hPcA : ρ '' Pc' ∩ A ⊆ c ∪ ⋃₀ Cs' := by
    rintro y ⟨hyP, hyA⟩
    obtain ⟨S, hS, hyS⟩ := mem_sUnion.mp (hA.subset ⟨hPlΔ hPc'Pl hyP, hyA⟩)
    by_cases hSc : S = c
    · exact Or.inl (hSc ▸ hyS)
    · right
      refine mem_sUnion_of_mem hyS ⟨hS, hSc, ?_⟩
      have hcov : S ⊆ ρ '' Pc' ∪ ρ '' Qc := hPcΔc_union.symm ▸ hCsΔ S hS
      have hdisjSc : S ∩ (ρ '' Pc' ∩ ρ '' Qc) = ∅ := by
        rw [hPcΔc]
        exact (hdisj hS hcCs hSc).inter_eq
      rcases (isPreconnected_iff_subset_of_disjoint_closed.mp (hCspre S hS)) (ρ '' Pc')
          (ρ '' Qc) hPcpoly.isClosed hΔccl hcov hdisjSc with h1 | h1
      · exact h1
      · exfalso
        have h2 : y ∈ ρ '' Pc' ∩ ρ '' Qc := ⟨hyP, h1 hyS⟩
        rw [hPcΔc] at h2
        exact Set.disjoint_left.mp (hdisj hS hcCs hSc) hyS h2
  have hCs'fin : Cs'.Finite := hfin.subset fun S hS => hS.1
  have hFc : IsCompact (⋃₀ Cs') :=
    hCs'fin.isCompact_sUnion fun S hS => (hCspoly S hS.1).isCompact
  have hFPc : ⋃₀ Cs' ⊆ ρ '' Pc' := sUnion_subset fun S hS => hS.2.2
  have hFc_disj : Disjoint (⋃₀ Cs') c :=
    Set.disjoint_sUnion_left.mpr fun S hS => hdisj hS.1 hcCs hS.2.1
  have hFA : ⋃₀ Cs' ⊆ A := sUnion_subset fun S hS => hCsA S hS.1
  have hFΔ : ⋃₀ Cs' ⊆ Δ := hFPc.trans (hPlΔ hPc'Pl)
  have hσF : IsCompact (σρ '' ⋃₀ Cs') := hFc.image_of_continuousOn (hσρc.mono hFΔ)
  have hc'U₀ : frontier Qc ⊆ (σρ '' ⋃₀ Cs')ᶜ := by
    rw [hfrQc]
    rintro _ ⟨y, hy, rfl⟩ ⟨z, hzF, hzy⟩
    have hzy' := hσρ.bijOn.injOn (hFΔ hzF) (hCsΔ c hcCs hy) hzy
    exact Set.disjoint_left.mp hFc_disj hzF (hzy' ▸ hy)
  obtain ⟨Acol, -, ρcol, -, -, hAsub, -, hρcol, hρcol1, -, hAnhds, hmaps, -⟩ :=
    hPl.exists_outer_boundary_collar hQc hQcint hσF.isClosed.isOpen_compl hc'U₀
  rw [hfrQc] at hρcol hρcol1 hAnhds hmaps
  have hρcolc : ContinuousOn ρcol ((σρ '' c) ×ˢ Icc (0 : ℝ) 1) :=
    hρcol.isPiecewiseAffineOn.continuousOn
  have hY'pre : IsPreconnected (ρcol '' ((σρ '' c) ×ˢ Ico (0 : ℝ) 1)) :=
    (hc's.isConnected_one.isPreconnected.prod isPreconnected_Ico).image _
      (hρcolc.mono (prod_mono subset_rfl Ico_subset_Icc_self))
  have hY'ne : (ρcol '' ((σρ '' c) ×ˢ Ico (0 : ℝ) 1)).Nonempty := by
    obtain ⟨x, hx⟩ := hc's.nonempty
    exact ⟨_, (x, 0), ⟨hx, le_rfl, zero_lt_one⟩, rfl⟩
  have hY'PlQ : ρcol '' ((σρ '' c) ×ˢ Ico (0 : ℝ) 1) ⊆ Pl \ Qc :=
    image_subset_iff.mpr fun z hz => hmaps hz
  have hY'A : ρcol '' ((σρ '' c) ×ˢ Ico (0 : ℝ) 1) ⊆ Acol :=
    (image_mono (prod_mono subset_rfl Ico_subset_Icc_self)).trans hρcol.image_eq.subset
  have hc'cl : σρ '' c ⊆ closure (ρcol '' ((σρ '' c) ×ˢ Ico (0 : ℝ) 1)) := by
    intro x hx
    have hmem : (x, (1 : ℝ)) ∈ closure ((σρ '' c) ×ˢ Ico (0 : ℝ) 1) := by
      rw [closure_prod_eq, closure_Ico zero_ne_one]
      exact ⟨subset_closure hx, zero_le_one, le_rfl⟩
    have h1 := ((hρcolc (x, 1) ⟨hx, zero_le_one, le_rfl⟩).mono
      (prod_mono subset_rfl Ico_subset_Icc_self)).mem_closure_image hmem
    rwa [hρcol1 x hx] at h1
  have hZ₁pre : IsPreconnected (ρ '' (ρcol '' ((σρ '' c) ×ˢ Ico (0 : ℝ) 1))) :=
    hY'pre.image ρ (hρc.mono (hY'PlQ.trans sdiff_subset))
  have hZ₁N : ρ '' (ρcol '' ((σρ '' c) ×ˢ Ico (0 : ℝ) 1)) ⊆ interior N' := fun y hy =>
    (hΔsub (hPlΔ (hY'PlQ.trans sdiff_subset) hy)).1
  have hZ₁A : Disjoint (ρ '' (ρcol '' ((σρ '' c) ×ˢ Ico (0 : ℝ) 1))) A := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ hxA
    have hxPl := (hY'PlQ hx).1
    have hxPc : ρ x ∈ ρ '' Pc' := mem_image_of_mem ρ (subset_closure (hY'PlQ hx))
    rcases hPcA ⟨hxPc, hxA⟩ with h1 | h1
    · have h2 : x ∈ σρ '' c := (hpreimg c hcCs x hxPl).mpr h1
      exact (hY'PlQ hx).2 (hQccl.frontier_subset (hfrQc.symm ▸ h2))
    · exact (hAsub (hY'A hx)).1 ⟨ρ x, h1, hσρρ x hxPl⟩
  obtain ⟨v, hv, hZ₁v⟩ := hd.exists_subset_handlePiece hZ₁pre (hY'ne.image ρ) hZ₁N hZ₁A
  have hcv : c ⊆ Cpp v := by
    have h1 : c ⊆ closure (ρ '' (ρcol '' ((σρ '' c) ×ˢ Ico (0 : ℝ) 1))) := by
      intro y hy
      rw [← hρσimg c hcCs] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact (hρc.mono (closure_minimal (hY'PlQ.trans sdiff_subset) hPlcl)).image_closure
        (mem_image_of_mem ρ (hc'cl hx))
    exact h1.trans (closure_minimal hZ₁v (hCppc v hv))
  have hve : v ∈ e₀ := by
    by_contra hn
    obtain ⟨y, hy⟩ := hcs.nonempty
    have h1 := hd.handlePiece_inter_pseudoCell_eq_empty hv he₀ hcard₀ hn
    have h2 : y ∈ Cpp v ∩ Ec e₀ := ⟨hcv hy, hce hy⟩
    rw [h1] at h2
    exact h2
  have hDcv : Dc ⊆ Cpp v := hDcE.trans (hd.pseudoCell_subset_handlePiece he₀ hcard₀ hve)
  obtain ⟨V', hV'o, hc'V', hV'A⟩ : ∃ V' : Set (EuclideanSpace ℝ (Fin 2)), IsOpen V' ∧
      σρ '' c ⊆ V' ∧ V' ∩ (interior Qc)ᶜ ⊆ Acol := by
    rw [nhdsSetWithin, Filter.mem_inf_principal] at hAnhds
    obtain ⟨V₀, hV₀, hcV₀, hV₀sub⟩ := mem_nhdsSet_iff_exists.mp hAnhds
    exact ⟨V₀, hV₀, hcV₀, fun x hx => hV₀sub hx.1 hx.2⟩
  have hAY : Acol ⊆ ρcol '' ((σρ '' c) ×ˢ Ico (0 : ℝ) 1) ∪ σρ '' c := by
    rw [← hρcol.image_eq]
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht0, ht1⟩, rfl⟩
    rcases ht1.lt_or_eq with hlt | heq
    · exact Or.inl ⟨(x, t), ⟨hx, ht0, hlt⟩, rfl⟩
    · right
      have ht : t = 1 := heq
      subst ht
      rw [hρcol1 x hx]
      exact hx
  have hWcc : IsCompact (ρ '' (Pc' \ V')) :=
    (hPlc.of_isClosed_subset (isClosed_closure.sdiff hV'o)
      (sdiff_subset.trans hPc'Pl)).image_of_continuousOn (hρc.mono (sdiff_subset.trans hPc'Pl))
  have hcW : Disjoint c (ρ '' (Pc' \ V')) := by
    rw [← hρσimg c hcCs]
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨z, hz, hzx⟩
    have hzx' := hρinj (hPc'Pl hz.1) (hpreSub c hcCs hx) hzx
    exact hz.2 (hzx' ▸ hc'V' hx)
  have hWPc : ρ '' Pc' \ ρ '' (Pc' \ V') ⊆ Cpp v := by
    rintro _ ⟨⟨x, hx, rfl⟩, hxW⟩
    have hxV : x ∈ V' := by
      by_contra hn
      exact hxW ⟨x, ⟨hx, hn⟩, rfl⟩
    have hxA : x ∈ Acol := hV'A ⟨hxV, fun hxi => Set.disjoint_left.mp hPc'int hx hxi⟩
    rcases hAY hxA with h1 | h1
    · exact hZ₁v (mem_image_of_mem ρ h1)
    · exact hcv ((hρσimg c hcCs).subset (mem_image_of_mem ρ h1))
  have hO : IsOpen ((interior N' \ h '' K.space) ∩ (⋃₀ Cs')ᶜ ∩ (frontier XK.space)ᶜ ∩
      (ρ '' (Pc' \ V'))ᶜ) :=
    ((hV.inter hFc.isClosed.isOpen_compl).inter isClosed_frontier.isOpen_compl).inter
      hWcc.isClosed.isOpen_compl
  have hDcc : IsCompact Dc := by
    rw [← hrc.image_eq]
    exact (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)).image_of_continuousOn
      hrc.isPiecewiseAffineOn.continuousOn
  have hDcO : Dc ⊆ (interior N' \ h '' K.space) ∩ (⋃₀ Cs')ᶜ ∩ (frontier XK.space)ᶜ ∩
      (ρ '' (Pc' \ V'))ᶜ := by
    intro y hy
    refine ⟨⟨⟨hDcN hy, fun hyF => ?_⟩, fun hyX => Set.disjoint_left.mp hDcX hy hyX⟩,
      fun hyW => ?_⟩
    · have h1 : y ∈ c := hDcΔ ▸ ⟨hy, hFΔ hyF⟩
      exact Set.disjoint_left.mp hFc_disj hyF h1
    · have h1 : y ∈ c := hDcΔ ▸ ⟨hy, hPlΔ (sdiff_subset.trans hPc'Pl) hyW⟩
      exact Set.disjoint_left.mp hcW h1 hyW
  have hΔ₁O : (ρ '' Pc' ∪ Dc) ∩ ((interior N' \ h '' K.space) ∩ (⋃₀ Cs')ᶜ ∩
      (frontier XK.space)ᶜ ∩ (ρ '' (Pc' \ V'))ᶜ) ⊆ Cpp v := by
    rintro y ⟨hy | hy, hyO⟩
    · exact hWPc ⟨hy, hyO.2⟩
    · exact hDcv hy
  have hΔ₁Z : (ρ '' Pc' ∪ Dc) ∩ ((interior N' \ h '' K.space) ∩ (⋃₀ Cs')ᶜ ∩
      (frontier XK.space)ᶜ ∩ (ρ '' (Pc' \ V'))ᶜ) ∩ A ⊆ Dc := by
    rintro y ⟨⟨hy | hy, hyO⟩, hyA⟩
    · rcases hPcA ⟨hy, hyA⟩ with h1 | h1
      · exact hcDc h1
      · exact absurd h1 hyO.1.1.2
    · exact hy
  obtain ⟨Δ₂, hΔ₂, hΔ₂A⟩ := h2.exists_isLoopTheoremDisk_pushOff hd hv hΔ₁ hO
    (fun y hy => hy.1.1.1.1) (Set.disjoint_left.mpr fun y hy hyK => hy.1.1.1.2 hyK)
    hDcc hDcO hDcv hΔ₁O hΔ₁Z
  refine ⟨Δ₂, Cs', hΔ₂, fun S hS => hS.1, fun heq => ?_, ?_⟩
  · have h1 : c ∈ Cs' := heq ▸ hcCs
    exact h1.2.1 rfl
  · rw [hΔ₂A]
    apply Subset.antisymm
    · rintro y ⟨⟨hy1 | hy1, hyO⟩, hyA⟩
      · rcases hPcA ⟨hy1, hyA⟩ with h1 | h1
        · exact absurd (hDcO (hcDc h1)) hyO
        · exact h1
      · exact absurd (hDcO hy1) hyO
    · intro y hy
      exact ⟨⟨Or.inl (hFPc hy), fun hyO => hyO.1.1.2 hy⟩, hFA hy⟩

end CircleStep

end DifferentialGeometry.Topology.PiecewiseLinear

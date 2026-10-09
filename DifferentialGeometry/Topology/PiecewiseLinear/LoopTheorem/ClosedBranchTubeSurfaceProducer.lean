/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellCapNeighbors
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedSurfaceArcsAndCaps
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarMarkedRays
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeSourceCells
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.MarkedBranchSurfaceSubdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isSourceTrackedBranchTube_of_sourceCollar
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {D : SingularTwoCell L.space} {BdM B : Set L.space}
      (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch},
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
        {τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
        {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)},
        IsPLSphere 1 J → hD.IsBranchDeckInvolution c J τ →
        hD.IsTwoSidedBranchCollar c J Q C ρ →
        ∃ (Pc : Geometry.SimplicialComplex ℝ (ℝ × ℝ)) (_ : Finite Pc.faces)
          (N : Geometry.SimplicialComplex ℝ E) (_ : Finite N.faces)
          (φ : (ℝ × ℝ) × ℝ → E) (u : ℝ × ℝ → ℝ × ℝ),
          IsSourceTrackedBranchTube hD c Subtype.val L J ρ N Pc φ u fourSpokeModelLeaf := by
  let _ := combinatorialChartedSpace L hL
  intro D BdM B hD c hc J Q C τ ρ hJ hτ hρ
  obtain ⟨hpreJ, hJne, -, hτJ, -, hτne, -, hDτ, hfiber⟩ := id hτ
  obtain ⟨a₀, ha₀⟩ := hJne
  let a₀' : Bool → EuclideanSpace ℝ (Fin 2) := fun b => if b then τ a₀ else a₀
  have ha₀' : ∀ b, a₀' b ∈ J := by
    intro b
    cases b
    · exact ha₀
    · exact hτJ ha₀
  obtain ⟨R₀, hR₀L, hR₀fin, hpR₀, -, -, -, -, harms₀⟩ :=
    exists_subdivision_branchCarrier_collarArms L hL hD hc hρ a₀' ha₀'
  let _ : Finite R₀.faces := hR₀fin.to_subtype
  obtain ⟨t, R, ψ, V, Ω, W, A, P, q, hRR₀, hRfin, hΓsp, hcharts, hcells⟩ :=
    exists_subdivision_marked_branchSurface_disks L hL hD hc hτ hρ R₀ inferInstance hR₀L
  let _ : Finite R.faces := hRfin.to_subtype
  have hRL := hRR₀.trans hR₀L
  have hR : IsCombinatorialManifold 3 R := hL.of_isSubdivision hRL
  let Γ := PiecewiseLinear.restrict R (Subtype.val '' hD.singularSet.branchCarrier c)
  let _ : Finite Γ.faces := (restrict_faces_finite R _).to_subtype
  have hΓR : Γ.faces ⊆ R.faces := restrict_faces_subset R _
  have hΓsphere : IsPLSphere 1 Γ.space := hΓsp.symm ▸
    isPLSphere_one_val_image_branchCarrier L hL D BdM hD.singularSet c hc
  have hpR : {((D a₀ : L.space) : E)} ∈ R.faces := hRR₀.singleton_mem hpR₀
  have ha₀Γ : D a₀ ∈ hD.singularSet.branchCarrier c :=
    (show a₀ ∈ hD.branchPreimage c from hpreJ.symm ▸ ha₀).2
  have hpΓ : {((D a₀ : L.space) : E)} ∈ Γ.faces := by
    refine ⟨hpR, ?_⟩
    simpa only [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff] using
      (show ((D a₀ : L.space) : E) ∈ Subtype.val '' hD.singularSet.branchCarrier c from
        ⟨D a₀, ha₀Γ, rfl⟩)
  have harms : ∀ a ∈ J, D a = D a₀ → ∀ σ : Bool,
      (PiecewiseLinear.restrict R
        ((fun u : ℝ => ((D (ρ (a, u)) : L.space) : E)) ''
          (if σ then Icc (0 : ℝ) 1 else Icc (-1 : ℝ) 0))).space =
        (fun u : ℝ => ((D (ρ (a, u)) : L.space) : E)) ''
          (if σ then Icc (0 : ℝ) 1 else Icc (-1 : ℝ) 0) := by
    intro a ha hDa σ
    obtain ⟨b, rfl⟩ : ∃ b, a = a₀' b := by
      rcases (hfiber a₀ ha₀ a ha).mp hDa.symm with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    have hsub := hRR₀.restrict (PiecewiseLinear.restrict R₀
      ((fun u : ℝ => ((D (ρ (a₀' b, u)) : L.space) : E)) ''
        (if σ then Icc (0 : ℝ) 1 else Icc (-1 : ℝ) 0))) (restrict_faces_subset R₀ _)
    rw [harms₀ b σ] at hsub
    exact hsub.space_eq.trans (harms₀ b σ)
  obtain ⟨m, s, D₀, D₁, q₀, q₁, y₀, y₁, hm, hs0, hsΓ, hKfin, hK, hS,
    hq₀, hq₁, hD₀S, hD₁S, hdis, hcap, hcapc, hadj, hadjc, hfar, hN,
    hy₀, hy₁, hpoles, hcore⟩ := exists_derivedCellChain R Γ hR hΓR
      (IsPLSphere.isCombinatorialManifold (n := 0) hΓsphere) hΓsphere.isConnected hpΓ
  let K : ℕ → Geometry.SimplicialComplex ℝ E := fun k => derivedNeighborhoodCellBase R (s k)
  let H : ℕ → Set E := fun k => (derivedNeighborhoodCell R (s k)).space
  have hH : ∀ k, H k = coneSet ((s k).centroid ℝ id) (K k).space :=
    fun k => derivedNeighborhoodCell_space_eq_coneSet R (hΓR (hsΓ k))
  have hHraw : ∀ k, H k = coneSet ((s k).centroid ℝ id)
      (upperLink (barycentricSubdivision R) {(s k).centroid ℝ id}).space := hH
  choose j hstar hcell using (fun k => hcells (s k) (hsΓ k))
  let A' : ℕ → Bool → Set (EuclideanSpace ℝ (Fin 2)) := fun k => A (j k)
  let T : ℕ → Fin 4 → Set E := fun k i => (K k).space ∩ P (j k) i
  have hA : ∀ k b, IsCompact (A' k b) ∧ A' k b ⊆ C ∧ InjOn D (A' k b) := by
    intro k
    obtain ⟨-, -, -, -, -, -, -, hA, -, -, -, -⟩ := hcharts (j k)
    exact hA
  have hAA : ∀ k, Disjoint (A' k false) (A' k true) := by
    intro k
    obtain ⟨-, -, -, -, -, -, -, -, hAA, -, -, -⟩ := hcharts (j k)
    exact hAA
  have hpre : ∀ k, ∀ x ∈ D.domain, ((D x : L.space) : E) ∈ H k →
      x ∈ A' k false ∪ A' k true := by
    intro k x hx hxH
    obtain ⟨-, -, -, -, -, -, -, -, -, hpre, -, -⟩ := hcharts (j k)
    exact hpre x hx (hcell k hxH)
  have hAc : ∀ k b, ∀ y ∈ hD.singularSet.branchCarrier c,
      (y : E) ∈ H k → y ∈ D '' (A' k b ∩ J) := by
    intro k b y hy hyH
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hAc, -⟩ := hcharts (j k)
    exact hAc b y hy (hcell k hyH)
  have hbaseH : ∀ k, (K k).space ⊆ H k := by
    intro k
    rw [hH]
    exact subset_coneSet _ _
  have hread : ∀ k i, T k i = (K k).space ∩
      (Subtype.val ∘ D) '' (A' k (fourSpokeLabel i).1 ∩ collarHalf J ρ (fourSpokeLabel i).2) := by
    intro k i
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hdata⟩ := hcharts (j k)
    ext x
    constructor
    · rintro ⟨hxK, hxP⟩
      exact ⟨hxK, (((hdata i).2.2.2 x
        ⟨hRL.space_eq ▸ derivedNeighborhoodCell_space_subset R (s k) (hbaseH k hxK),
          hcell k (hbaseH k hxK)⟩).2.1).mp hxP⟩
    · rintro ⟨hxK, hxP⟩
      exact ⟨hxK, (((hdata i).2.2.2 x
        ⟨hRL.space_eq ▸ derivedNeighborhoodCell_space_subset R (s k) (hbaseH k hxK),
          hcell k (hbaseH k hxK)⟩).2.1).mpr hxP⟩
  have harcs : ∀ k, ∃ γ : Fin 4 → ℝ → E,
      (∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (T k i)) ∧
      (∀ i, γ i 0 = y₀ k) ∧ (∀ i, γ i 1 = y₁ k) ∧
      (∀ i l, i ≠ l → T k i ∩ T k l = {y₀ k, y₁ k}) ∧
      (∀ i : Fin 4, ∀ U ⊆ (K k).space \ (T k i ∪ T k (i + 2)), IsPreconnected U →
        (U ∩ T k (i + 1)).Nonempty → (U ∩ T k (i + 3)).Nonempty → False) ∧
      ∀ z ∈ Γ.faces, s k ≠ z → (s k ⊆ z ∨ z ⊆ s k) →
        ∀ r : (Fin 3 → ℝ) → E, IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
          (H k ∩ (derivedNeighborhoodCell R z).space) →
          ∀ i, ∃ x, r '' stdSimplexBoundary 2 ∩ T k i = {x} ∧
            T k i ∩ (H k ∩ (derivedNeighborhoodCell R z).space) =
              segment ℝ (({(s k).centroid ℝ id, z.centroid ℝ id} : Finset E).centroid ℝ id) x ∧
            ({(s k).centroid ℝ id, z.centroid ℝ id} : Finset E).centroid ℝ id ≠ x := by
    intro k
    obtain ⟨-, -, -, hWΩ, hψ, -, hΓchart, -, -, -, -, hdata⟩ := hcharts (j k)
    apply exists_derived_surface_arcs_and_caps R Γ hR hΓR (hsΓ k)
      (hRL.space_eq.symm ▸ hψ) hWΩ
      (by rw [hΓsp]; exact hΓchart) (fun i => (hdata i).1) (fun i => (hdata i).2.2.1)
      (fun x hx i => ((hdata i).2.2.2 x (hRL.space_eq ▸ hx)).1)
      (fun x hx i => by rw [hΓsp]; exact ((hdata i).2.2.2 x (hRL.space_eq ▸ hx)).2.2)
      (hstar k) (hcell k) (hpoles k)
  choose γ hγ hγ0 hγ1 hTT hsep htrace using harcs
  have hbottom : ∀ k ≤ m, ∃ z ∈ Γ.faces, s k ≠ z ∧
      (s k ⊆ z ∨ z ⊆ s k) ∧ H k ∩ (derivedNeighborhoodCell R z).space = D₀ k ∧
      ({(s k).centroid ℝ id, z.centroid ℝ id} : Finset E).centroid ℝ id = y₀ k := by
    intro k hk
    have hp : Γ.space ∩ (K k).space = {y₁ k, y₀ k} := (hpoles k).trans (pair_comm _ _)
    by_cases hk0 : k = 0
    · subst k
      have hcap0 : H 0 ∩ H m = D₀ 0 := (inter_comm _ _).trans hadjc
      obtain ⟨hne, hcomp, hcenter⟩ := derived_cap_neighbor_data R Γ hΓR (hsΓ 0) (hsΓ m)
        hp hcap0 (hD₀S 0) (hdis 0).symm (hy₁ 0) (hy₀ 0)
      exact ⟨s m, hsΓ m, hne, hcomp, hcap0, hcenter⟩
    · obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
      have hl : l < m := by omega
      have hcap0 : H (l + 1) ∩ H l = D₀ (l + 1) :=
        (inter_comm _ _).trans ((hadj l hl).trans (hcap l hl))
      obtain ⟨hne, hcomp, hcenter⟩ := derived_cap_neighbor_data R Γ hΓR
        (hsΓ (l + 1)) (hsΓ l) hp hcap0 (hD₀S (l + 1)) (hdis (l + 1)).symm
        (hy₁ (l + 1)) (hy₀ (l + 1))
      exact ⟨s l, hsΓ l, hne, hcomp, hcap0, hcenter⟩
  have htop : ∀ k ≤ m, ∃ z ∈ Γ.faces, s k ≠ z ∧
      (s k ⊆ z ∨ z ⊆ s k) ∧ H k ∩ (derivedNeighborhoodCell R z).space = D₁ k ∧
      ({(s k).centroid ℝ id, z.centroid ℝ id} : Finset E).centroid ℝ id = y₁ k := by
    intro k hk
    rcases eq_or_lt_of_le hk with heq | hk
    · subst k
      have hcap1 : H m ∩ H 0 = D₁ m := hadjc.trans hcapc.symm
      obtain ⟨hne, hcomp, hcenter⟩ := derived_cap_neighbor_data R Γ hΓR (hsΓ m) (hsΓ 0)
        (hpoles m) hcap1 (hD₁S m) (hdis m) (hy₀ m) (hy₁ m)
      exact ⟨s 0, hsΓ 0, hne, hcomp, hcap1, hcenter⟩
    · obtain ⟨hne, hcomp, hcenter⟩ := derived_cap_neighbor_data R Γ hΓR
        (hsΓ k) (hsΓ (k + 1)) (hpoles k) (hadj k hk) (hD₁S k) (hdis k) (hy₀ k) (hy₁ k)
      exact ⟨s (k + 1), hsΓ (k + 1), hne, hcomp, hadj k hk, hcenter⟩
  have htrace₀ : ∀ k ≤ m, ∀ i, ∃ x, q₀ k '' stdSimplexBoundary 2 ∩ T k i = {x} ∧
      T k i ∩ D₀ k = segment ℝ (y₀ k) x ∧ y₀ k ≠ x := by
    intro k hk i
    obtain ⟨z, hz, hne, hcomp, hcap0, hcenter⟩ := hbottom k hk
    obtain ⟨x, hx⟩ := htrace k z hz hne hcomp (q₀ k) (hcap0.symm ▸ hq₀ k) i
    rw [hcap0, hcenter] at hx
    exact ⟨x, hx⟩
  have htrace₁ : ∀ k ≤ m, ∀ i, ∃ x, q₁ k '' stdSimplexBoundary 2 ∩ T k i = {x} ∧
      T k i ∩ D₁ k = segment ℝ (y₁ k) x ∧ y₁ k ≠ x := by
    intro k hk i
    obtain ⟨z, hz, hne, hcomp, hcap1, hcenter⟩ := htop k hk
    obtain ⟨x, hx⟩ := htrace k z hz hne hcomp (q₁ k) (hcap1.symm ▸ hq₁ k) i
    rw [hcap1, hcenter] at hx
    exact ⟨x, hx⟩
  have hcenter : ((D a₀ : L.space) : E) ∈ H 0 := by
    rw [hH, hs0, Finset.centroid_singleton, id_eq]
    exact mem_coneSet_iff.mpr (Or.inl rfl)
  obtain ⟨a, ⟨haA, haJ⟩, hDa⟩ := hAc 0 false (D a₀) ha₀Γ hcenter
  let a' : Bool → EuclideanSpace ℝ (Fin 2) := fun b => if b then τ a else a
  have ha' : ∀ b, a' b ∈ J := by
    intro b
    cases b
    · exact haJ
    · exact hτJ haJ
  have hDa' : ∀ b, D (a' b) = D a₀ := by
    intro b
    cases b
    · exact hDa
    · exact (hDτ a haJ).trans hDa
  have ha'A : ∀ b, a' b ∈ A' 0 b := by
    intro b
    cases b
    · exact haA
    · have hτdom : τ a ∈ D.domain :=
        (show τ a ∈ hD.branchPreimage c from hpreJ.symm ▸ hτJ haJ).1
      have hτH : ((D (τ a) : L.space) : E) ∈ H 0 := by rw [hDτ a haJ, hDa]; exact hcenter
      rcases hpre 0 (τ a) hτdom hτH with h | h
      · exact (hτne a haJ ((hA 0 false).2.2 h haA (hDτ a haJ))).elim
      · exact h
  have hs0' : s 0 = {((D (a' false) : L.space) : E)} := by rw [hDa' false]; exact hs0
  obtain ⟨z₀, hz₀, hne₀, -, hcap0, -⟩ := hbottom 0 (Nat.zero_le m)
  obtain ⟨z₁, hz₁, hne₁, -, hcap1, -⟩ := htop 0 (Nat.zero_le m)
  have hPL : IsPiecewiseAffineOn (Subtype.val ∘ D) D.domain :=
    isPiecewiseAffineOn_val_comp_of_isPLOn L hL D.domain D.toFun D.isPLOn
  obtain ⟨v, hv, hv0, hv1, hv2, hv3, hray⟩ := hD.exists_four_derived_collar_marks_outside_caps
    (D₀ := D₀ 0) (D₁ := D₁ 0)
    Subtype.val_injective hPL hρ R Γ hΓR hΓsp ha'
    (by rw [hDa' false]; exact hpR) (fun b => (hDa' b).trans (hDa' false).symm)
    (fun b => harms (a' b) (ha' b) (hDa' b)) (fun b => (hA 0 b).1.isClosed) (hAA 0) ha'A
    (by rw [← hs0']; exact hpre 0) hz₀ hz₁ (hs0' ▸ hne₀.symm) (hs0' ▸ hne₁.symm)
    (by rw [← hcap0]; exact inter_subset_right) (by rw [← hcap1]; exact inter_subset_right)
  let α : Fin 4 → EuclideanSpace ℝ (Fin 2) := fun i => a' (fourSpokeLabel i).1
  have hrayT : ∀ i, ((D (ρ (α i, v i)) : L.space) : E) ∈ T 0 i \ (D₀ 0 ∪ D₁ 0) := by
    intro i
    rw [hread]
    dsimp only [K]
    rw [hs0']
    exact hray i
  let ν : ℕ → ℕ := fun k => if k ≤ m then k else 0
  have hν : ∀ k ≤ m, ν k = k := fun k hk => ite_eq_left hk
  have hνle : ∀ k, ν k ≤ m := by
    intro k
    dsimp only [ν]
    split_ifs with hk
    · exact hk
    · exact Nat.zero_le m
  have hν0 := hν 0 (Nat.zero_le m)
  have hνm := hν m le_rfl
  have hN' : (⋃ k ≤ m, coneSet ((s (ν k)).centroid ℝ id) (K (ν k)).space) =
      (derivedNeighborhood R Γ).space := by
    calc
      _ = ⋃ k ≤ m, H k := by
        apply iUnion_congr
        intro k
        apply iUnion_congr
        intro hk
        rw [hν k hk, hH]
      _ = _ := hN
  have hcore' : (⋃ k ≤ m, coneSet ((s (ν k)).centroid ℝ id) {y₀ (ν k), y₁ (ν k)}) =
      Subtype.val '' hD.singularSet.branchCarrier c := by
    calc
      _ = ⋃ k ≤ m, coneSet ((s k).centroid ℝ id) {y₀ k, y₁ k} := by
        apply iUnion_congr
        intro k
        apply iUnion_congr
        intro hk
        rw [hν k hk]
      _ = _ := hcore.trans hΓsp
  obtain ⟨Pc, hPcfin, φ, u, htube⟩ := exists_isSourceTrackedBranchTube_of_sourceCells hD
    continuous_subtype_val Subtype.val_injective hL hJ hτ hρ hRfin hRL hm
    (fun k => hKfin (ν k)) (fun k => hK (ν k)) (fun k => hS (ν k))
    (fun k => hγ (ν k)) (fun k => hγ0 (ν k)) (fun k => hγ1 (ν k))
    (fun k => hTT (ν k)) (fun k => hsep (ν k))
    (fun k => hq₀ (ν k)) (fun k => hq₁ (ν k)) (fun k => hD₀S (ν k)) (fun k => hD₁S (ν k))
    (fun k => hdis (ν k)) (fun k => hy₀ (ν k)) (fun k => hy₁ (ν k))
    (fun k hk => by rw [hν k (by omega), hν (k + 1) (by omega)]; exact hcap k hk)
    (by rw [hνm, hν0]; exact hcapc)
    (fun k hk => by
      rw [hν k (by omega), hν (k + 1) (by omega), ← hHraw, ← hHraw]
      exact hadj k hk)
    (by rw [hνm, hν0, ← hHraw, ← hHraw]; exact hadjc)
    (fun j k hjk hkm hjk' => by
      rw [hν j (by omega), hν k hkm, ← hHraw, ← hHraw]
      exact hfar j k hjk hkm hjk') hN' hcore'
    (fun k => by rw [← hΓsp]; exact hpoles (ν k)) (fun k => hA (ν k)) (fun k => hAA (ν k))
    (fun k x hx hxH => hpre (ν k) x hx ((hH (ν k)).symm ▸ hxH))
    (fun k b y hy hyH => hAc (ν k) b y hy ((hH (ν k)).symm ▸ hyH))
    (fun k => hread (ν k)) (fun k => htrace₀ (ν k) (hνle k)) (fun k => htrace₁ (ν k) (hνle k))
    (fun i => ha' (fourSpokeLabel i).1) hv (by rw [hν0]; exact hrayT)
    (by rw [hν0, hs0', Finset.centroid_singleton]; rfl)
    (show α 2 = α 0 from rfl) (show α 1 = τ (α 0) from rfl) (show α 3 = α 1 from rfl)
    hv0 hv1 hv2 hv3
  exact ⟨Pc, hPcfin, derivedNeighborhood R Γ, (derivedNeighborhood_faces_finite R Γ).to_subtype,
    φ, u, htube⟩

end DifferentialGeometry.Topology.PiecewiseLinear

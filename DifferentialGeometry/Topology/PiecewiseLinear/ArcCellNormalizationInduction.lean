/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcCellNormalization

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_normalized_trimmedArcCellUnion_of_cutModel [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j)
    (hinterior : ∀ j, 1 ≤ j → j ≤ 2 * n - 1 →
      arcChainFace v j ∉ (boundaryComplex 3 K).faces)
    (hnpos : 0 < n) (hn : Module.finrank ℝ E = 3)
    {p₁ p₂ z y₁ y₂ : E} {L₁ L₂ L₀ L : Geometry.SimplicialComplex ℝ E}
    (hfin₁ : L₁.faces.Finite) (hfin₂ : L₂.faces.Finite)
    (hfin₀ : L₀.faces.Finite) (hfin : L.faces.Finite)
    (hL₁ : IsConeBase p₁ L₁) (hL₂ : IsConeBase p₂ L₂)
    (hL₀ : IsConeBase z L₀) (hL : IsConeBase p₁ L)
    (hS₁ : IsPLSphere 2 L₁.space) (hS₂ : IsPLSphere 2 L₂.space)
    (hS₀ : IsPLSphere 1 L₀.space) (hS : IsPLSphere 2 L.space)
    (hD₁ : coneSet z L₀.space ⊆ L₁.space) (hD₂ : coneSet z L₀.space ⊆ L₂.space)
    (hy₁ : y₁ ∈ L₁.space) (hy₁D : y₁ ∉ coneSet z L₀.space)
    (hy₂ : y₂ ∈ L₂.space) (hy₂D : y₂ ∉ coneSet z L₀.space)
    (hmeet : coneSet p₁ L₁.space ∩ coneSet p₂ L₂.space = coneSet z L₀.space)
    (hcone : coneSet p₁ L.space = coneSet p₁ L₁.space ∪ coneSet p₂ L₂.space)
    (harc : coneSet p₁ ({y₁, y₂} : Set E) =
      coneSet p₁ ({z, y₁} : Set E) ∪ coneSet p₂ ({z, y₂} : Set E))
    (hy₁L : y₁ ∈ L.space) (hy₂L : y₂ ∈ L.space)
    (hL₂sub : L₂.space ⊆ L.space ∪ coneSet z L₀.space)
    {k : ℕ} (hk0 : 1 ≤ k) (hkn : k + 1 ≤ 2 * n) :
    ∃ Φ : E → E,
      IsPLHomeomorphOn Φ (trimmedArcCellUnion K v k) (coneSet p₁ L₁.space) ∧
      Φ '' (trimmedArcCellUnion K v k ∩ (arcComplexIn K v n).space) =
        coneSet p₁ {z, y₁} ∧
      Φ '' coneSet (arcCellCrossing v k) (arcCellInterfaceBase K v k).space =
        coneSet z L₀.space ∧
      Φ (arcCellCrossing v k) = z ∧ Φ (arcCellCrossing v 0) = y₁ := by
  have _ : Finite L₁.faces := hfin₁.to_subtype
  have _ : Finite L₂.faces := hfin₂.to_subtype
  have _ : Finite L₀.faces := hfin₀.to_subtype
  have _ : Finite L.faces := hfin.to_subtype
  let State := fun j : ℕ => ∃ Φ : E → E,
    IsPLHomeomorphOn Φ (trimmedArcCellUnion K v j) (coneSet p₁ L₁.space) ∧
    Φ '' (trimmedArcCellUnion K v j ∩ (arcComplexIn K v n).space) =
      coneSet p₁ {z, y₁} ∧
    Φ '' coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space =
      coneSet z L₀.space ∧
    Φ (arcCellCrossing v j) = z ∧ Φ (arcCellCrossing v 0) = y₁
  have hstate : ∀ m : ℕ, m + 2 ≤ 2 * n → State (m + 1) := by
    intro m
    induction m with
    | zero =>
        intro hm
        obtain ⟨p, w, y, M, M₀, F, hfinM, hfinM₀, hM, hM₀, hSM, hSM₀, hDM,
          hyM, hF, hFarc, hFD, hFw, hFy⟩ :=
          exists_normalized_trimmedArcCellUnion_one_of_interior hK hvert hedge hinj
            (hinterior 1 (by omega) (by omega)) hnpos hn
        have _ : Finite M.faces := hfinM.to_subtype
        have _ : Finite M₀.faces := hfinM₀.to_subtype
        have hDball : IsPLBall 2 (coneSet w M₀.space) := by
          rw [← coneComplex_space_eq_coneSet hM₀]
          exact hM₀.isPLBall_of_isPLSphere hSM₀
        have hwM : w ∈ M.space := hDM (apex_mem_coneSet _ _)
        have hyMspace : y ∈ M.space :=
          closure_minimal sdiff_subset hSM.isPolyhedron.isClosed hyM.1
        have hX : ({w, y} : Set E) ⊆ M.space := by
          intro x hx
          rcases Set.mem_insert_iff.mp hx with hx | hx
          · simpa [hx] using hwM
          · simpa [Set.mem_singleton_iff.mp hx] using hyMspace
        obtain ⟨f₀, hf₀⟩ := hSM₀.exists_isPLHomeomorphOn (F := E) hS₀
        obtain ⟨g, hg, -, hgw, -⟩ :=
          exists_isPLHomeomorphOn_coneSet_pair hM₀ (subset_refl M₀.space) hL₀ hf₀ hf₀.image_eq
        have hgX : g '' (({w, y} : Set E) ∩ coneSet w M₀.space) =
            ({z, y₁} : Set E) ∩ coneSet z L₀.space := by
          rw [pair_inter_coneSet hyM.2, pair_inter_coneSet hy₁D, Set.image_singleton, hgw]
        obtain ⟨G, hG, hGeq, -, hGX, -, hGy⟩ :=
          exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked hM hX hSM hL₁ hS₁ hDball hDM hD₁
            hg hyM ⟨subset_closure ⟨hy₁, hy₁D⟩, hy₁D⟩
            (pair_eq_inter_coneSet_union hyM.2) (pair_eq_inter_coneSet_union hy₁D) hgX
        refine ⟨G ∘ F, hF.trans hG, ?_, ?_, ?_, ?_⟩
        · change (fun x => G (F x)) ''
            (trimmedArcCellUnion K v 1 ∩ (arcComplexIn K v n).space) = _
          rw [← Set.image_image G F, hFarc, hGX]
        · change (fun x => G (F x)) '' coneSet (arcCellCrossing v 1)
            (arcCellInterfaceBase K v 1).space = _
          rw [← Set.image_image G F, hFD, hGeq.image_eq, hg.image_eq]
        · change G (F (arcCellCrossing v 1)) = z
          rw [hFw, hGeq (apex_mem_coneSet _ _), hgw]
        · change G (F (arcCellCrossing v 0)) = y₁
          rw [hFy, hGy]
    | succ m ih =>
        intro hm
        have hprev : m + 2 ≤ 2 * n := by omega
        obtain ⟨Φ, hΦ, hΦarc, hΦD, hΦz, hΦy⟩ := ih hprev
        let j := m + 1
        have hj0 : 1 ≤ j := by simp [j]
        have hjn : j + 2 ≤ 2 * n := by omega
        have _ : Finite (arcCellBase K v (j + 1)).faces :=
          (arcCellBase_faces_finite v (j + 1)).to_subtype
        have _ : Finite (arcCellInterfaceBase K v j).faces :=
          (arcCellInterfaceBase_faces_finite v j).to_subtype
        have _ : Finite (arcCellInterfaceBase K v (j + 1)).faces :=
          (arcCellInterfaceBase_faces_finite v (j + 1)).to_subtype
        have hLc := isConeBase_arcCellBase (K := K) hvert hedge (j := j + 1) (by omega)
        have hSc := hK.isPLSphere_arcCellBase_of_interior hvert hedge
          (j := j + 1) (by omega) (hinterior (j + 1) (by omega) (by omega))
        have hLd := isConeBase_arcCellInterfaceBase (K := K) hvert hedge hinj (j := j) (by omega)
        have hSd := hK.isPLSphere_arcCellInterfaceBase_of_interior_left
          hvert hedge hinj (j := j) (by omega) (hinterior j (by omega) (by omega))
        have hLd' := isConeBase_arcCellInterfaceBase (K := K) hvert hedge hinj
          (j := j + 1) hjn
        have hSd' := hK.isPLSphere_arcCellInterfaceBase_of_interior_left hvert hedge hinj
          (j := j + 1) hjn (hinterior (j + 1) (by omega) (by omega))
        have hDinBase := arcCellInterface_subset_arcCellBase_right
          (K := K) hvert hedge hinj (j := j) (by omega)
        have hDoutBase := arcCellInterface_subset_arcCellBase_left
          (K := K) hvert hedge hinj (j := j + 1) hjn
        have hDinBall : IsPLBall 2
            (coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space) := by
          rw [← coneComplex_space_eq_coneSet hLd]
          exact hLd.isPLBall_of_isPLSphere hSd
        have hDoutBall : IsPLBall 2
            (coneSet (arcCellCrossing v (j + 1))
              (arcCellInterfaceBase K v (j + 1)).space) := by
          rw [← coneComplex_space_eq_coneSet hLd']
          exact hLd'.isPLBall_of_isPLSphere hSd'
        have hDinBk : coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space ⊆
            trimmedArcCellUnion K v j := by
          rw [← trimmedArcCellUnion_inter_next_eq_coneSet
            (K := K) hvert hedge hinj hj0 (by omega)]
          exact inter_subset_left
        have hΦDin : IsPLHomeomorphOn Φ
            (coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space)
            (coneSet z L₀.space) := by
          have hres := hΦ.restrict hDinBall.isPolyhedron hDinBk
          rw [show Φ '' coneSet (arcCellCrossing v j)
            (arcCellInterfaceBase K v j).space = coneSet z L₀.space by
              simpa only [j] using hΦD] at hres
          exact hres
        have hzin : arcCellCrossing v j ∈ (arcCellBase K v (j + 1)).space :=
          hDinBase (apex_mem_coneSet _ _)
        have hyout : arcCellCrossing v (j + 1) ∈ (arcCellBase K v (j + 1)).space :=
          hDoutBase (apex_mem_coneSet _ _)
        have hXc : ({arcCellCrossing v j, arcCellCrossing v (j + 1)} : Set E) ⊆
            (arcCellBase K v (j + 1)).space := by
          intro x hx
          rcases Set.mem_insert_iff.mp hx with hx | hx
          · simpa [hx] using hzin
          · simpa [Set.mem_singleton_iff.mp hx] using hyout
        have hySrc := next_arcCellCrossing_mem_closure_diff_interface
          (K := K) hvert hedge hinj (j := j) hjn
        have hyTgt : y₂ ∈ closure (L₂.space \ coneSet z L₀.space) \ coneSet z L₀.space :=
          ⟨subset_closure ⟨hy₂, hy₂D⟩, hy₂D⟩
        have hΦX : Φ '' (({arcCellCrossing v j, arcCellCrossing v (j + 1)} : Set E) ∩
            coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space) =
            ({z, y₂} : Set E) ∩ coneSet z L₀.space := by
          rw [pair_inter_coneSet (next_arcCellCrossing_not_mem_interface
            (K := K) hvert hedge hinj (j := j) hjn),
            pair_inter_coneSet hy₂D, Set.image_singleton, hΦz]
        obtain ⟨G₂, hG₂, hG₂eq, -, hG₂arc, hG₂base, hG₂y⟩ :=
          exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked hLc hXc hSc hL₂ hS₂ hDinBall
            hDinBase hD₂ hΦDin hySrc hyTgt
            (pair_eq_inter_coneSet_union (next_arcCellCrossing_not_mem_interface
              (K := K) hvert hedge hinj (j := j) hjn))
            (pair_eq_inter_coneSet_union hy₂D) hΦX
        have hcell : (derivedNeighborhoodCell K (arcChainFace v (j + 1))).space =
            coneSet (arcCellApex v (j + 1)) (arcCellBase K v (j + 1)).space :=
          derivedNeighborhoodCell_arcChainFace_space_eq_coneSet (K := K) hvert hedge (by omega)
        have hG₂cell : IsPLHomeomorphOn G₂
            (derivedNeighborhoodCell K (arcChainFace v (j + 1))).space
            (coneSet p₂ L₂.space) := by
          rwa [hcell]
        have hC₁ball : IsPLBall 3 (coneSet p₁ L₁.space) := by
          rw [← coneComplex_space_eq_coneSet hL₁]
          exact hL₁.isPLBall_of_isPLSphere hS₁
        have hBkball : IsPLBall 3 (trimmedArcCellUnion K v j) :=
          hC₁ball.of_isPLHomeomorphOn hΦ.symm
        have hcellball : IsPLBall 3
            (derivedNeighborhoodCell K (arcChainFace v (j + 1))).space := by
          rw [hcell, ← coneComplex_space_eq_coneSet hLc]
          exact hLc.isPLBall_of_isPLSphere hSc
        have hinter := trimmedArcCellUnion_inter_next_eq_coneSet
          (K := K) hvert hedge hinj hj0 (by omega)
        have hEq : EqOn Φ G₂
            (trimmedArcCellUnion K v j ∩
              (derivedNeighborhoodCell K (arcChainFace v (j + 1))).space) := by
          rw [hinter]
          exact hG₂eq.symm
        have himg : Φ '' (trimmedArcCellUnion K v j ∩
              (derivedNeighborhoodCell K (arcChainFace v (j + 1))).space) =
            coneSet p₁ L₁.space ∩ coneSet p₂ L₂.space := by
          rw [hinter, hΦD, hmeet]
        let Ψ := (trimmedArcCellUnion K v j).piecewise Φ G₂
        have hΨraw := hΦ.piecewise hG₂cell hBkball.isPolyhedron hcellball.isPolyhedron hEq himg
        have hsucc := trimmedArcCellUnion_succ K v j
        have hΨ : IsPLHomeomorphOn Ψ (trimmedArcCellUnion K v (j + 1))
            (coneSet p₁ L₁.space ∪ coneSet p₂ L₂.space) := by
          simpa only [Ψ, hsucc] using hΨraw
        have hΨold : EqOn Ψ Φ (trimmedArcCellUnion K v j) :=
          (trimmedArcCellUnion K v j).piecewise_eqOn Φ G₂
        have hΨnew : EqOn Ψ G₂
            (derivedNeighborhoodCell K (arcChainFace v (j + 1))).space := by
          intro x hx
          by_cases hxold : x ∈ trimmedArcCellUnion K v j
          · rw [show Ψ x = Φ x from Set.piecewise_eq_of_mem _ _ _ hxold]
            exact hEq ⟨hxold, hx⟩
          · exact Set.piecewise_eq_of_notMem _ _ _ hxold
        have hcellarc := derivedNeighborhoodCell_arcChainFace_inter_arcComplexIn_space_eq
          (K := K) hvert hedge hinj (j := j + 1) (by omega) hjn
        have hcellarc' :
            (derivedNeighborhoodCell K (arcChainFace v (j + 1))).space ∩
                (arcComplexIn K v n).space =
              coneSet (arcCellApex v (j + 1))
                {arcCellCrossing v j, arcCellCrossing v (j + 1)} := by
          simpa only [Nat.add_sub_cancel] using hcellarc
        have hΨarc : Ψ '' (trimmedArcCellUnion K v (j + 1) ∩
              (arcComplexIn K v n).space) =
            coneSet p₁ ({z, y₁} : Set E) ∪ coneSet p₂ ({z, y₂} : Set E) := by
          rw [trimmedArcCellUnion_succ_inter_arcComplexIn_space, Set.image_union,
            (hΨold.mono inter_subset_left).image_eq,
            (hΨnew.mono inter_subset_left).image_eq, hΦarc, hcellarc', hG₂arc]
        have hcrossNextCell : arcCellCrossing v (j + 1) ∈
            (derivedNeighborhoodCell K (arcChainFace v (j + 1))).space :=
          (arcCellCrossing_mem_adjacent_derivedNeighborhoodCells
            (K := K) hvert hedge hinj (j := j + 1) hjn).1
        have hΨnext : Ψ (arcCellCrossing v (j + 1)) = y₂ :=
          (hΨnew hcrossNextCell).trans hG₂y
        have hcrossZeroBk : arcCellCrossing v 0 ∈ trimmedArcCellUnion K v j :=
          arcCellCrossing_zero_mem_trimmedArcCellUnion
            (K := K) hvert hedge hinj hj0 (by omega)
        have hΨzero : Ψ (arcCellCrossing v 0) = y₁ :=
          (hΨold hcrossZeroBk).trans hΦy
        let D' := G₂ '' coneSet (arcCellCrossing v (j + 1))
          (arcCellInterfaceBase K v (j + 1)).space
        have hDoutCell : coneSet (arcCellCrossing v (j + 1))
            (arcCellInterfaceBase K v (j + 1)).space ⊆
            (derivedNeighborhoodCell K (arcChainFace v (j + 1))).space := by
          rw [hcell]
          exact hDoutBase.trans (subset_coneSet _ _)
        have hG₂Dout : IsPLHomeomorphOn G₂
            (coneSet (arcCellCrossing v (j + 1))
              (arcCellInterfaceBase K v (j + 1)).space) D' := by
          exact hG₂cell.restrict hDoutBall.isPolyhedron hDoutCell
        have hD'ball : IsPLBall 2 D' := hDoutBall.of_isPLHomeomorphOn hG₂Dout
        have hD'L₂ : D' ⊆ L₂.space := by
          intro x hx
          rw [← hG₂base]
          exact image_mono hDoutBase hx
        have hDoutDin : Disjoint
            (coneSet (arcCellCrossing v (j + 1))
              (arcCellInterfaceBase K v (j + 1)).space)
            (coneSet (arcCellCrossing v j) (arcCellInterfaceBase K v j).space) :=
          (disjoint_trimmedArcCellUnion_next_interface
            (K := K) hvert hedge hinj hjn).symm.mono (subset_refl _) hDinBk
        have hD'D₀ : Disjoint D' (coneSet z L₀.space) := by
          apply Set.disjoint_left.mpr
          rintro x ⟨a, ha, rfl⟩ hxD₀
          have hximg : G₂ a ∈ G₂ '' coneSet (arcCellCrossing v j)
              (arcCellInterfaceBase K v j).space := by
            rw [hG₂eq.image_eq, hΦD]
            exact hxD₀
          obtain ⟨b, hb, hba⟩ := hximg
          have hab := hG₂.bijOn.injOn (hcell ▸ hDoutCell ha)
            (subset_coneSet _ _ (hDinBase hb)) hba.symm
          exact Set.disjoint_left.mp hDoutDin ha (hab ▸ hb)
        have hD'L : D' ⊆ L.space := by
          intro x hx
          rcases hL₂sub (hD'L₂ hx) with hxL | hxD₀
          · exact hxL
          · exact False.elim (Set.disjoint_left.mp hD'D₀ hx hxD₀)
        have hy₂D' : y₂ ∈ D' :=
          ⟨arcCellCrossing v (j + 1), apex_mem_coneSet _ _, hG₂y⟩
        have hΨDout : Ψ '' coneSet (arcCellCrossing v (j + 1))
            (arcCellInterfaceBase K v (j + 1)).space = D' :=
          (hΨnew.mono hDoutCell).image_eq
        have hy₁D' : y₁ ∉ D' := by
          intro hyD'
          obtain ⟨a, ha, hGa⟩ := hyD'
          have haCell := hDoutCell ha
          have haUnion : a ∈ trimmedArcCellUnion K v (j + 1) := by
            rw [hsucc]
            exact Or.inr haCell
          have hzeroUnion : arcCellCrossing v 0 ∈ trimmedArcCellUnion K v (j + 1) := by
            rw [hsucc]
            exact Or.inl hcrossZeroBk
          have hΨa : Ψ a = Ψ (arcCellCrossing v 0) :=
            (hΨnew haCell).trans (hGa.trans hΨzero.symm)
          have ha0 := hΨ.bijOn.injOn haUnion hzeroUnion hΨa
          exact Set.disjoint_left.mp
            (disjoint_trimmedArcCellUnion_next_interface
              (K := K) hvert hedge hinj hjn) hcrossZeroBk (ha0 ▸ ha)
        have hyOuter : y₁ ∈ closure (L.space \ D') \ D' :=
          ⟨subset_closure ⟨hy₁L, hy₁D'⟩, hy₁D'⟩
        have hXouter : ({y₂, y₁} : Set E) ⊆ L.space := by
          intro x hx
          rcases Set.mem_insert_iff.mp hx with hx | hx
          · simpa [hx] using hy₂L
          · simpa [Set.mem_singleton_iff.mp hx] using hy₁L
        obtain ⟨f₀, hf₀⟩ := hSd'.exists_isPLHomeomorphOn (F := E) hS₀
        obtain ⟨g₀, hg₀, -, hg₀z, -⟩ :=
          exists_isPLHomeomorphOn_coneSet_pair hLd'
            (subset_refl (arcCellInterfaceBase K v (j + 1)).space) hL₀ hf₀ hf₀.image_eq
        let g := g₀ ∘ Function.invFunOn G₂
          (coneSet (arcCellCrossing v (j + 1))
            (arcCellInterfaceBase K v (j + 1)).space)
        have hg : IsPLHomeomorphOn g D' (coneSet z L₀.space) := hG₂Dout.symm.trans hg₀
        have hgy₂ : g y₂ = z := by
          change g₀ (Function.invFunOn G₂
            (coneSet (arcCellCrossing v (j + 1))
              (arcCellInterfaceBase K v (j + 1)).space) y₂) = z
          rw [← hG₂y, hG₂Dout.bijOn.invOn_invFunOn.1 (apex_mem_coneSet _ _), hg₀z]
        have hpairD' : ({y₂, y₁} : Set E) ∩ D' = {y₂} := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨hx | hx, hxD⟩
            · exact hx
            · rw [hx] at hxD
              exact absurd hxD hy₁D'
          · intro hx
            exact ⟨Or.inl hx, hx ▸ hy₂D'⟩
        have hsplit : ({y₂, y₁} : Set E) = ({y₂, y₁} : Set E) ∩ D' ∪ {y₁} := by
          rw [hpairD', Set.singleton_union]
        have hgX : g '' (({y₂, y₁} : Set E) ∩ D') =
            ({z, y₁} : Set E) ∩ coneSet z L₀.space := by
          rw [hpairD', pair_inter_coneSet hy₁D, Set.image_singleton, hgy₂]
        obtain ⟨H, hH, hHeq, -, hHX, -, hHy₁⟩ :=
          exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked hL hXouter hS hL₁ hS₁ hD'ball hD'L
            hD₁ hg hyOuter ⟨subset_closure ⟨hy₁, hy₁D⟩, hy₁D⟩ hsplit
            (pair_eq_inter_coneSet_union hy₁D) hgX
        have hΨouter : IsPLHomeomorphOn Ψ (trimmedArcCellUnion K v (j + 1))
            (coneSet p₁ L.space) := by
          rw [hcone]
          exact hΨ
        refine ⟨H ∘ Ψ, hΨouter.trans hH, ?_, ?_, ?_, ?_⟩
        · change (fun x => H (Ψ x)) '' (trimmedArcCellUnion K v (j + 1) ∩
            (arcComplexIn K v n).space) = _
          rw [← Set.image_image H Ψ, hΨarc, ← harc, Set.pair_comm, hHX]
        · change (fun x => H (Ψ x)) '' coneSet (arcCellCrossing v (j + 1))
            (arcCellInterfaceBase K v (j + 1)).space = _
          rw [← Set.image_image H Ψ, hΨDout, hHeq.image_eq, hg.image_eq]
        · change H (Ψ (arcCellCrossing v (j + 1))) = z
          rw [hΨnext, hHeq hy₂D', hgy₂]
        · change H (Ψ (arcCellCrossing v 0)) = y₁
          rw [hΨzero, hHy₁]
  have hk : k - 1 + 1 = k := by omega
  simpa only [hk] using hstate (k - 1) (by omega)

end DifferentialGeometry.Topology.PiecewiseLinear

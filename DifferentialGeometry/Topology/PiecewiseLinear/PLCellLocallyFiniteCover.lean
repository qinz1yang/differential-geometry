/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ExhaustionGeneral
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPolytope
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLCellOn_locallyFinite_cover_of_isOpen {X : Type*} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [HasGroupoid X (plGroupoid 3)] {Y : Set X} (hY : IsOpen Y) (N : X → Set X)
    (hN : ∀ y ∈ Y, N y ∈ 𝓝 y) :
    ∃ (ι : Type) (C G : ι → Set X), (∀ i, IsPLCellOn 3 (C i) (frontier (C i))) ∧
      (∀ i, IsOpen (G i)) ∧ (∀ i, G i ⊆ interior (C i)) ∧ (∀ i, C i ⊆ Y) ∧
      (∀ i, ∃ y ∈ Y, C i ⊆ N y) ∧
      (∀ i, ∃ c ∈ (plGroupoid 3).maximalAtlas X, C i ⊆ c.source) ∧ (Y ⊆ ⋃ i, G i) ∧
      ∀ y ∈ Y, ∃ V ∈ 𝓝 y, {i | (C i ∩ V).Nonempty}.Finite := by
  by_cases hYne : Y.Nonempty
  · obtain ⟨y₀, hy₀⟩ := hYne
    classical
    let _ : Nonempty X := ⟨y₀⟩
    obtain ⟨K, hK, hKunion⟩ := exists_exhaustion_of_isOpen (m := 2) hY
    let L : ℕ → Set X := fun n => Nat.rec ∅ (fun n _ => K n) n
    have hLunion : (⋃ n, L n) = Y := by
      rw [← hKunion]
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨n, hx⟩
        cases n with
        | zero => simp [L] at hx
        | succ n => exact ⟨n, by simpa [L] using hx⟩
      · rintro ⟨n, hx⟩
        exact ⟨n + 1, by simpa [L] using hx⟩
    let prev : ℕ → Set X := fun n => if n = 0 then ∅ else L (n - 1)
    let shell : ℕ → Set X := fun n => L (n + 1) \ interior (L n)
    let margin : ℕ → Set X := fun n => interior (L (n + 2)) \ prev n
    have hLcompact : ∀ n, IsCompact (L n) := by
      intro n
      cases n with
      | zero => simp [L]
      | succ n => simpa [L] using (hK n).1
    have hLsub : ∀ n, L n ⊆ interior (L (n + 1)) := by
      intro n
      cases n with
      | zero => simp [L]
      | succ n => simpa [L] using (hK n).2.2
    have hLmono : Monotone L :=
      monotone_nat_of_le_succ fun n => (hLsub n).trans interior_subset
    have hshellcompact : ∀ n, IsCompact (shell n) := by
      intro n
      exact (hLcompact (n + 1)).diff isOpen_interior
    have hshellsub : ∀ n, shell n ⊆ margin n := by
      intro n x hx
      refine ⟨hLsub (n + 1) hx.1, ?_⟩
      intro hprev
      by_cases hn : n = 0
      · simp [prev, hn] at hprev
      · have hprevmem : x ∈ L (n - 1) := by
          simpa [prev, hn] using hprev
        have hprev' := hLsub (n - 1) hprevmem
        rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)] at hprev'
        exact hx.2 hprev'
    have hmarginY : ∀ n, margin n ⊆ Y := by
      intro n z hz
      rw [← hLunion]
      exact mem_iUnion.mpr ⟨n + 2, interior_subset hz.1⟩
    have hshellY : ∀ n, shell n ⊆ Y := by
      intro n z hz
      rw [← hLunion]
      exact mem_iUnion.mpr ⟨n + 1, hz.1⟩
    have hlocal : ∀ n (x : shell n), ∃ C G : Set X,
        ∃ c ∈ (plGroupoid 3).maximalAtlas X,
          IsPLCellOn 3 C (frontier C) ∧ IsOpen G ∧ G ⊆ interior C ∧
            C ⊆ margin n ∩ N (x : X) ∧ (x : X) ∈ G ∧ C ⊆ c.source := by
      intro n x
      have hxY : (x : X) ∈ Y := hshellY n x.2
      have hxmargin : (x : X) ∈ margin n := hshellsub n x.2
      obtain ⟨O, hON, hOopen, hxO⟩ := mem_nhds_iff.mp (hN _ hxY)
      have hprevclosed : IsClosed (prev n) := by
        simp only [prev]
        split
        · exact isClosed_empty
        · rename_i hn
          exact hLcompact (n - 1) |>.isClosed
      have hmarginopen : IsOpen (margin n) := by
        dsimp [margin]
        exact isOpen_interior.inter hprevclosed.isOpen_compl
      have hXO : (x : X) ∈ margin n ∩ O := ⟨hxmargin, hxO⟩
      have hXOopen : IsOpen (margin n ∩ O) := hmarginopen.inter hOopen
      obtain ⟨P, hP, hPt, hPnhds, hPU⟩ :=
        exists_isHPolytope_image_symm_mem_nhds_subset (n := 3) hXOopen hXO
      let e := chartAt (EuclideanSpace ℝ (Fin 3)) (x : X)
      let C : Set X := e.symm '' P
      let G : Set X := interior C
      have hCsub : C ⊆ margin n ∩ N (x : X) := by
        intro z hz
        exact ⟨(hPU hz).1, hON (hPU hz).2⟩
      have hCopen : IsOpen G := isOpen_interior
      have hCnhds : C ∈ 𝓝 (x : X) := by
        simpa [C, e] using hPnhds
      have hxG : (x : X) ∈ G := mem_interior_iff_mem_nhds.mpr hCnhds
      have hPnhds' : P ∈ 𝓝 (e (x : X)) := by
        rw [← e.image_symm_image_of_subset_target hPt]
        exact e.image_mem_nhds (mem_chart_source _ (x : X)) hCnhds
      have hPinter : (interior P).Nonempty :=
        ⟨e (x : X), mem_interior_iff_mem_nhds.mpr hPnhds'⟩
      have hball : IsPLBall 3 P := by
        simpa only [finrank_euclideanSpace_fin] using hP.isPLBall hPinter
      have hEpl : IsPLOn 3 3 e.symm P :=
        (isPLOn_chart_symm (x : X)).mono_of_isPolyhedron hP.isPolyhedron hPt
      have hEemb : IsPLHomeomorphInto 3 e.symm P :=
        hEpl.isPLHomeomorphInto hP.isCompact (injOn_symm_of_subset_target e hPt)
      obtain ⟨r, hr⟩ := hball
      have hmodel : IsPLCellOn 3 P (r '' stdSimplexBoundary 3) :=
        isPLCellOn_id_of_isPLBall hr
      rw [hmodel.boundary_eq_frontier] at hmodel
      have hcell : IsPLCellOn 3 C (frontier C) := by
        rw [show C = e.symm '' P by rfl, ← (hmodel.image_boundary_interior hEemb).1]
        exact hmodel.image hEemb
      have hemax : e ∈ (plGroupoid 3).maximalAtlas X := by
        dsimp [e]
        exact StructureGroupoid.chart_mem_maximalAtlas _ _
      have hCsource : C ⊆ e.source := by
        rintro z ⟨w, hw, rfl⟩
        exact e.map_target (hPt hw)
      have hGC : G ⊆ interior C := by
        intro z hz
        exact hz
      exact ⟨C, G, e, hemax, hcell, hCopen, hGC, hCsub, hxG, hCsource⟩
    choose C G c hc hcell hG hGC hCmarg hcore hCsource using fun n x => hlocal n x
    have hfiniteCover : ∀ n, ∃ q : ℕ, ∃ a : Fin q → shell n,
        shell n ⊆ ⋃ j, G n (a j) := by
      intro n
      obtain ⟨t, ht⟩ := (hshellcompact n).elim_finite_subcover (fun x : shell n => G n x)
        (fun x => hG n x) (by
          intro x hx
          exact mem_iUnion.mpr ⟨⟨x, hx⟩, hcore n ⟨x, hx⟩⟩)
      let e := Fintype.equivFin t
      refine ⟨Fintype.card t, fun j => (e.symm j).1, ?_⟩
      intro z hz
      obtain ⟨x, hxt, hzG⟩ := mem_iUnion₂.mp (ht hz)
      refine mem_iUnion.mpr ⟨e ⟨x, hxt⟩, ?_⟩
      change z ∈ G n ((e.symm (e ⟨x, hxt⟩)).1)
      rw [e.symm_apply_apply]
      exact hzG
    choose q a hs using hfiniteCover
    refine ⟨Σ n : ℕ, Fin (q n), fun i => C i.1 (a i.1 i.2), fun i => G i.1 (a i.1 i.2), ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact hcell i.1 (a i.1 i.2)
    · intro i
      exact hG i.1 (a i.1 i.2)
    · intro i
      exact hGC i.1 (a i.1 i.2)
    · intro i z hz
      exact hmarginY i.1 (hCmarg i.1 (a i.1 i.2) hz).1
    · intro i
      refine ⟨(a i.1 i.2 : X), hshellY i.1 (a i.1 i.2).2, ?_⟩
      exact (hCmarg i.1 (a i.1 i.2)).trans inter_subset_right
    · intro i
      exact ⟨c i.1 (a i.1 i.2), hc i.1 (a i.1 i.2), hCsource i.1 (a i.1 i.2)⟩
    · intro y hy
      have hyL : y ∈ ⋃ n, L n := by
        rwa [hLunion]
      have hyL' : ∃ n, y ∈ L n := by
        simpa only [mem_iUnion] using hyL
      let k : ℕ := @Nat.find (fun n : ℕ => y ∈ L n) (Classical.decPred _) hyL'
      have hyk : y ∈ L k := by
        dsimp [k]
        exact @Nat.find_spec (fun n : ℕ => y ∈ L n) (Classical.decPred _) hyL'
      have hkpos : 0 < k := by
        by_contra hk
        have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk
        have hyzero : y ∈ L 0 := hkzero ▸ hyk
        simp [L] at hyzero
      let n := k - 1
      have hn : n + 1 = k := by
        dsimp [n]
        exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hkpos)
      have hynshell : y ∈ shell n := by
        change y ∈ L (n + 1) ∧ y ∉ interior (L n)
        refine ⟨?_, ?_⟩
        · rw [hn]
          exact hyk
        intro hyint
        have hynlt : n < k := by
          dsimp [n]
          omega
        have hnot : y ∉ L n := by
          exact @Nat.find_min (fun r : ℕ => y ∈ L r) (Classical.decPred _) hyL' n
            (by simpa [k] using hynlt)
        exact hnot (interior_subset hyint)
      obtain ⟨j, hyG⟩ := mem_iUnion.mp (hs n hynshell)
      exact mem_iUnion.mpr ⟨⟨n, j⟩, hyG⟩
    · intro y hy
      have hyL : y ∈ ⋃ n, L n := by
        rwa [hLunion]
      obtain ⟨k, hyk⟩ : ∃ n, y ∈ L n := by
        simpa only [mem_iUnion] using hyL
      refine ⟨interior (L (k + 1)), isOpen_interior.mem_nhds (hLsub k hyk), ?_⟩
      have hboundfinite : {i : (Σ n : ℕ, Fin (q n)) | i.1 ≤ k + 1}.Finite := by
        let t : Finset (Σ n : ℕ, Fin (q n)) :=
          (Finset.range (k + 3)).sigma fun n => Finset.univ
        refine t.finite_toSet.subset ?_
        intro i hi
        change i.1 ≤ k + 1 at hi
        change i ∈ t
        dsimp [t]
        refine Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_univ _⟩
        omega
      refine hboundfinite.subset ?_
      intro i hi
      obtain ⟨z, hzC, hzV⟩ := hi
      by_contra hle
      have hlt : k + 1 < i.1 := Nat.lt_of_not_ge hle
      have hi0 : i.1 ≠ 0 := by omega
      have hznotprev : z ∉ prev i.1 := (hCmarg i.1 (a i.1 i.2) hzC).1.2
      have hzprev : z ∈ prev i.1 := by
        change z ∈ if i.1 = 0 then ∅ else L (i.1 - 1)
        rw [ite_eq_right hi0]
        exact hLmono (a := k + 1) (b := i.1 - 1) (by omega) (interior_subset hzV)
      exact hznotprev hzprev
  · have hYempty : Y = ∅ := not_nonempty_iff_eq_empty.mp hYne
    subst hYempty
    let C : Empty → Set X := fun i => nomatch i
    let G : Empty → Set X := fun i => nomatch i
    refine ⟨Empty, C, G, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact nomatch i
    · intro i; exact nomatch i
    · intro i; exact nomatch i
    · intro i; exact nomatch i
    · intro i; exact nomatch i
    · intro i; exact nomatch i
    · exact empty_subset _
    · intro y hy
      simp at hy

end DifferentialGeometry.Topology.PiecewiseLinear

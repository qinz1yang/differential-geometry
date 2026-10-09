/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcCapParameters
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellCore
import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeSheetPermutation
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCapMatching
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCellSheetLabels
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeAssembly

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isSourceTrackedBranchTube_of_sourceCells
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
    {D : SingularTwoCell M} {BdM B : Set M} (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {ι : M → E} (hιc : Continuous ι) (hι : Function.Injective ι)
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsCombinatorialManifold 3 L)
    {J Q C : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J)
    {τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hτ : hD.IsBranchDeckInvolution c J τ) (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {R Γ : Geometry.SimplicialComplex ℝ E} (hRfin : R.faces.Finite) (hRL : IsSubdivision R L)
    {m : ℕ} (hm : 2 ≤ m) {cc : ℕ → E} {K : ℕ → Geometry.SimplicialComplex ℝ E}
    (hKfin : ∀ k, (K k).faces.Finite) (hK : ∀ k, IsConeBase (cc k) (K k))
    (hS : ∀ k, IsPLSphere 2 (K k).space)
    {y₀ y₁ : ℕ → E} {T : ℕ → Fin 4 → Set E} {γ : ℕ → Fin 4 → ℝ → E}
    (hγ : ∀ k i, IsPLHomeomorphOn (γ k i) (Icc 0 1) (T k i))
    (hγzero : ∀ k i, γ k i 0 = y₀ k) (hγone : ∀ k i, γ k i 1 = y₁ k)
    (hTT : ∀ k i j, i ≠ j → T k i ∩ T k j = {y₀ k, y₁ k})
    (hsep : ∀ k, ∀ i : Fin 4, ∀ U ⊆ (K k).space \ (T k i ∪ T k (i + 2)),
      IsPreconnected U → (U ∩ T k (i + 1)).Nonempty → (U ∩ T k (i + 3)).Nonempty → False)
    {q₀ q₁ : ℕ → (Fin 3 → ℝ) → E} {D₀ D₁ : ℕ → Set E}
    (hq₀ : ∀ k, IsPLHomeomorphOn (q₀ k) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D₀ k))
    (hq₁ : ∀ k, IsPLHomeomorphOn (q₁ k) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D₁ k))
    (hD₀S : ∀ k, D₀ k ⊆ (K k).space) (hD₁S : ∀ k, D₁ k ⊆ (K k).space)
    (hdis : ∀ k, Disjoint (D₀ k) (D₁ k)) (hy₀ : ∀ k, y₀ k ∈ D₀ k) (hy₁ : ∀ k, y₁ k ∈ D₁ k)
    (hcap : ∀ k < m, D₁ k = D₀ (k + 1)) (hcapc : D₁ m = D₀ 0)
    (hadj : ∀ k < m,
      coneSet (cc k) (K k).space ∩ coneSet (cc (k + 1)) (K (k + 1)).space = D₁ k)
    (hadjc : coneSet (cc m) (K m).space ∩ coneSet (cc 0) (K 0).space = D₀ 0)
    (hfar : ∀ j k, j + 1 < k → k ≤ m → (j ≠ 0 ∨ k ≠ m) →
      Disjoint (coneSet (cc j) (K j).space) (coneSet (cc k) (K k).space))
    (hN : ⋃ k ≤ m, coneSet (cc k) (K k).space = (derivedNeighborhood R Γ).space)
    (hcore : ⋃ k ≤ m, coneSet (cc k) {y₀ k, y₁ k} = ι '' hD.singularSet.branchCarrier c)
    (hpoles : ∀ k, (ι '' hD.singularSet.branchCarrier c) ∩ (K k).space = {y₀ k, y₁ k})
    {A : ℕ → Bool → Set (EuclideanSpace ℝ (Fin 2))}
    (hA : ∀ k b, IsCompact (A k b) ∧ A k b ⊆ C ∧ InjOn D (A k b))
    (hAA : ∀ k, Disjoint (A k false) (A k true))
    (hpre : ∀ k, ∀ x ∈ D.domain, ι (D x) ∈ coneSet (cc k) (K k).space →
      x ∈ A k false ∪ A k true)
    (hAc : ∀ k b, ∀ y ∈ hD.singularSet.branchCarrier c,
      ι y ∈ coneSet (cc k) (K k).space → y ∈ D '' (A k b ∩ J))
    (hread : ∀ k i, T k i = (K k).space ∩
      (ι ∘ D) '' (A k (fourSpokeLabel i).1 ∩ collarHalf J ρ (fourSpokeLabel i).2))
    (htrace₀ : ∀ k i, ∃ x, q₀ k '' stdSimplexBoundary 2 ∩ T k i = {x} ∧
      T k i ∩ D₀ k = segment ℝ (y₀ k) x ∧ y₀ k ≠ x)
    (htrace₁ : ∀ k i, ∃ x, q₁ k '' stdSimplexBoundary 2 ∩ T k i = {x} ∧
      T k i ∩ D₁ k = segment ℝ (y₁ k) x ∧ y₁ k ≠ x)
    {α : Fin 4 → EuclideanSpace ℝ (Fin 2)} {v : Fin 4 → ℝ}
    (hαJ : ∀ i, α i ∈ J) (hv : ∀ i, v i ∈ Icc (-1 : ℝ) 1)
    (hray : ∀ i, ι (D (ρ (α i, v i))) ∈ T 0 i \ (D₀ 0 ∪ D₁ 0))
    (hbase : cc 0 = ι (D (α 0))) (hα2 : α 2 = α 0) (hα1 : α 1 = τ (α 0))
    (hα3 : α 3 = α 1) (hv0 : 0 < v 0) (hv1 : 0 < v 1) (hv2 : v 2 < 0) (hv3 : v 3 < 0) :
    ∃ (Pc : Geometry.SimplicialComplex ℝ (ℝ × ℝ)) (_ : Finite Pc.faces)
      (φ : (ℝ × ℝ) × ℝ → E) (u : ℝ × ℝ → ℝ × ℝ),
      IsSourceTrackedBranchTube hD c ι L J ρ (derivedNeighborhood R Γ) Pc φ u
        fourSpokeModelLeaf := by
  let H : ℕ → Set E := fun k => coneSet (cc k) (K k).space
  have hHclosed : ∀ k, IsClosed (H k) := by
    intro k
    let _ : Finite (K k).faces := (hKfin k).to_subtype
    change IsClosed (coneSet (cc k) (K k).space)
    rw [← coneComplex_space_eq_coneSet (hK k)]
    exact ((hK k).isPLBall_of_isPLSphere (hS k)).isPolyhedron.isClosed
  have hAdom : ∀ k b, A k b ⊆ D.domain :=
    fun k b => (hA k b).2.1.trans (hρ.2.2.1.trans interior_subset)
  have hΓcap : ∀ k, (ι '' hD.singularSet.branchCarrier c) ∩ D₀ k = {y₀ k} ∧
      (ι '' hD.singularSet.branchCarrier c) ∩ D₁ k = {y₁ k} :=
    fun k => inter_cap_eq_singleton_of_pair_inter (hpoles k) (hD₀S k) (hD₁S k)
      (hdis k) (hy₀ k) (hy₁ k)
  have hy₀Γ : ∀ k, y₀ k ∈ ι '' hD.singularSet.branchCarrier c :=
    fun k => ((hpoles k).symm.subset (Or.inl rfl)).1
  have hy₁Γ : ∀ k, y₁ k ∈ ι '' hD.singularSet.branchCarrier c :=
    fun k => ((hpoles k).symm.subset (Or.inr rfl)).1
  have hcover : ι '' hD.singularSet.branchCarrier c ⊆ ⋃ k ≤ m, H k := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp (hcore.symm ▸ hx)
    refine mem_iUnion₂.mpr ⟨k, hk, ?_⟩
    rcases mem_coneSet_iff.mp hxk with rfl | ⟨y, hy, t, ht, ht1, rfl⟩
    · exact mem_coneSet_iff.mpr (Or.inl rfl)
    · apply mem_coneSet_iff.mpr
      refine Or.inr ⟨y, ?_, t, ht, ht1, rfl⟩
      rcases hy with rfl | rfl
      · exact hD₀S k (hy₀ k)
      · exact hD₁S k (hy₁ k)
  have hcadj : ∀ k < m, (ι '' hD.singularSet.branchCarrier c) ∩ (H k ∩ H (k + 1)) =
      {y₁ k} := fun k hk => by rw [hadj k hk]; exact (hΓcap k).2
  have hcseam : (ι '' hD.singularSet.branchCarrier c) ∩ (H 0 ∩ H m) = {y₀ 0} := by
    rw [inter_comm (H 0), hadjc]
    exact (hΓcap 0).1
  let a₀ : hD.branchPreimage c := ⟨α 0, hτ.1.symm ▸ hαJ 0⟩
  obtain ⟨b, hb0, hb, hbc⟩ := hD.exists_source_sheet_labels_on_cyclic_cells hιc hι hJ hτ.1 a₀
    H A (fun k _ => hHclosed k) hcover (fun k u => (hA k u).1) hAdom
    (fun k u => (hA k u).2.2) hAA hpre hAc y₁ (fun k _ => hy₁Γ k) hcadj (hy₀Γ 0)
    hcseam hfar false
  let π : ℕ → Equiv.Perm (Fin 4) := fun k => fourSpokeSheetPerm (b k)
  have hπ0 : ∀ i, π 0 i = i := by
    intro i
    change fourSpokeSheetPerm (b 0) i = i
    rw [hb0]
    rfl
  let T' : ℕ → Fin 4 → Set E := fun k i => T k (π k i)
  have hcapread {Z : Set E} {k : ℕ} (hZ : Z ⊆ (K k).space) (i : Fin 4) :
      T k i ∩ Z = Z ∩ (ι ∘ D) ''
        (A k (fourSpokeLabel i).1 ∩ collarHalf J ρ (fourSpokeLabel i).2) := by
    rw [hread]
    ext x
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hZ h.1, h.2⟩, h.1⟩⟩
  have hmatch {j k : ℕ} {i l : Fin 4} {Z : Set E}
      (hZ₁ : Z ⊆ (K j).space) (hZ₂ : Z ⊆ (K k).space)
      (hconn₁ : IsPreconnected (T j i ∩ Z)) (hconn₂ : IsPreconnected (T k l ∩ Z))
      (hside : (fourSpokeLabel i).2 = (fourSpokeLabel l).2)
      {a : EuclideanSpace ℝ (Fin 2)} (haJ : a ∈ J)
      (ha₁ : a ∈ A j (fourSpokeLabel i).1) (ha₂ : a ∈ A k (fourSpokeLabel l).1)
      (haZ : ι (D a) ∈ Z) : T j i ∩ Z = T k l ∩ Z := by
    rw [hcapread hZ₁ i, hcapread hZ₂ l]
    rw [hcapread hZ₁ i] at hconn₁
    rw [hcapread hZ₂ l] at hconn₂
    rw [← hside] at hconn₂ ⊢
    exact hD.source_quarter_cap_eq_of_common_source_point hιc hι hρ
      (fun u => (hA j u).1) (fun u => (hA k u).1) (hAdom j) (hAdom k)
      (fun u => (hA j u).2.2) (fun u => (hA k u).2.2) (hAA j) (hAA k)
      (fun x hx hxZ => hpre j x hx (subset_coneSet _ _ (hZ₁ hxZ)))
      (fun x hx hxZ => hpre k x hx (subset_coneSet _ _ (hZ₂ hxZ)))
      _ _ _ hconn₁ hconn₂ haJ ha₁ ha₂ haZ
  have hconn₀ : ∀ k i, IsPreconnected (T k i ∩ D₀ k) := by
    intro k i
    obtain ⟨x, -, hseg, -⟩ := htrace₀ k i
    rw [hseg]
    exact (convex_segment _ _).isPreconnected
  have hconn₁ : ∀ k i, IsPreconnected (T k i ∩ D₁ k) := by
    intro k i
    obtain ⟨x, -, hseg, -⟩ := htrace₁ k i
    rw [hseg]
    exact (convex_segment _ _).isPreconnected
  have harm : ∀ k < m, ∀ i, T' k i ∩ D₁ k = T' (k + 1) i ∩ D₀ (k + 1) := by
    intro k hk i
    obtain ⟨a, haJ, ha₁, ha₂, hay⟩ := hb k hk (fourSpokeLabel i).1
    change T k (π k i) ∩ D₁ k = T (k + 1) (π (k + 1) i) ∩ D₀ (k + 1)
    rw [← hcap k hk]
    refine hmatch (hD₁S k) (by rw [hcap k hk]; exact hD₀S (k + 1))
      (hconn₁ k _) (by rw [hcap k hk]; exact hconn₀ (k + 1) _)
      (by simp only [π, fourSpokeLabel_sheetPerm]) haJ ?_ ?_ ?_
    · simpa only [π, fourSpokeLabel_sheetPerm] using ha₁
    · simpa only [π, fourSpokeLabel_sheetPerm] using ha₂
    · rw [hay]
      exact hy₁ k
  have harmc : ∀ i, T' m i ∩ D₁ m = T' 0 (fourSpokeFlipPerm i) ∩ D₀ 0 := by
    intro i
    obtain ⟨a, haJ, ha₁, ha₂, haz⟩ := hbc (fourSpokeLabel i).1
    change T m (π m i) ∩ D₁ m = T 0 (π 0 (fourSpokeFlipPerm i)) ∩ D₀ 0
    rw [hcapc]
    refine hmatch (by rw [← hcapc]; exact hD₁S m) (hD₀S 0)
      (by rw [← hcapc]; exact hconn₁ m _) (hconn₀ 0 _)
      (by simp only [π, fourSpokeLabel_sheetPerm, fourSpokeLabel_flip]) haJ ?_ ?_ ?_
    · simpa only [π, fourSpokeLabel_sheetPerm] using ha₁
    · simpa only [π, fourSpokeLabel_sheetPerm, fourSpokeLabel_flip] using ha₂
    · rw [haz]
      exact hy₀ 0
  have hδexists : ∀ k i, ∃ δ : ℝ → E, IsPLHomeomorphOn δ (Icc 0 1) (T' k i) ∧
      δ 0 = y₀ k ∧ δ 1 = y₁ k ∧
      q₀ k '' stdSimplexBoundary 2 ∩ T' k i = {δ (1 / 4)} ∧
      q₁ k '' stdSimplexBoundary 2 ∩ T' k i = {δ (3 / 4)} ∧
      (k = 0 → δ (1 / 2) = ι (D (ρ (α i, v i)))) := by
    intro k i
    obtain ⟨x₀, hbd₀, hseg₀, hne₀⟩ := htrace₀ k (π k i)
    obtain ⟨x₁, hbd₁, hseg₁, hne₁⟩ := htrace₁ k (π k i)
    rw [← hγzero k (π k i)] at hseg₀ hne₀
    rw [← hγone k (π k i)] at hseg₁ hne₁
    by_cases hk : k = 0
    · subst k
      have hmid : ι (D (ρ (α i, v i))) ∈ T 0 (π 0 i) \ (D₀ 0 ∪ D₁ 0) := by
        rw [hπ0]
        exact hray i
      obtain ⟨δ, hδ, hδ0, hδa, hδb, hδc, hδ1⟩ :=
        (hγ 0 (π 0 i)).exists_parametrization_terminal_segments hseg₀ hseg₁ hne₀ hne₁ hmid
      exact ⟨δ, hδ, hδ0.trans (hγzero 0 _), hδ1.trans (hγone 0 _),
        hbd₀.trans (congrArg singleton hδa.symm), hbd₁.trans (congrArg singleton hδc.symm),
        fun _ => hδb⟩
    · obtain ⟨x, hx⟩ := (hγ k (π k i)).exists_mem_sdiff_of_disjoint_terminal_segments
        hseg₀ hseg₁ (hdis k)
      obtain ⟨δ, hδ, hδ0, hδa, -, hδc, hδ1⟩ :=
        (hγ k (π k i)).exists_parametrization_terminal_segments hseg₀ hseg₁ hne₀ hne₁ hx
      exact ⟨δ, hδ, hδ0.trans (hγzero k _), hδ1.trans (hγone k _),
        hbd₀.trans (congrArg singleton hδa.symm), hbd₁.trans (congrArg singleton hδc.symm),
        fun h => (hk h).elim⟩
  choose δ hδ hδ0 hδ1 hδcap0 hδcap1 hδmid using hδexists
  have hpt : ∀ k < m, ∀ i, δ k i (3 / 4) = δ (k + 1) i (1 / 4) := by
    intro k hk i
    have hq : IsPLHomeomorphOn (q₀ (k + 1)) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D₁ k) :=
      (hcap k hk).symm ▸ hq₀ (k + 1)
    exact eq_of_cap_boundary_singletons_of_inter_eq (hq₁ k) hq (hδcap1 k i) (hδcap0 (k + 1) i)
      (by simpa only [← hcap k hk] using harm k hk i)
  have hptc : ∀ i, δ m i (3 / 4) = δ 0 (fourSpokeFlipPerm i) (1 / 4) := by
    intro i
    exact eq_of_cap_boundary_singletons_of_inter_eq (hcapc ▸ hq₁ m) (hq₀ 0)
      (hδcap1 m i) (hδcap0 0 (fourSpokeFlipPerm i)) (by simpa only [hcapc] using harmc i)
  exact exists_isSourceTrackedBranchTube_of_markedCells hD hιc hι hL hJ hτ hRfin hRL hm
    hKfin hK hS hδ hδ0 hδ1
    (fun k i => by
      change T k (π k i) ⊆ (K k).space
      rw [hread]
      exact inter_subset_left)
    (fun k i j hij => hTT k (π k i) (π k j) ((π k).injective.ne hij))
    (fun k => fourSpoke_separated_sheetPerm (hsep k) (b k)) hq₀ hq₁ hD₀S hD₁S hdis
    hδcap0 hδcap1 hy₀ hy₁ hcap hcapc harm harmc hpt hptc hadj hadjc hfar hN hcore
    hαJ hv (fun i => hδmid 0 i rfl) hbase hα2 hα1 hα3 hv0 hv1 hv2 hv3

end DifferentialGeometry.Topology.PiecewiseLinear

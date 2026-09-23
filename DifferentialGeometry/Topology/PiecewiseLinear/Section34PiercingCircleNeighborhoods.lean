import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCores
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

open Set Topology Function

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem lens_disjoint_nonincident {X V E : Type*} (C : V → Set X) (ends : E → V × V)
    (hnonadj : ∀ w w', w ≠ w' → (¬ ∃ e,
      (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1)) →
      Disjoint (C w) (C w'))
    (hdisj : Pairwise (Disjoint on fun e => C (ends e).1 ∩ C (ends e).2))
    (e : E) (w : V) (hw₀ : w ≠ (ends e).1) (hw₁ : w ≠ (ends e).2) :
    Disjoint (C (ends e).1 ∩ C (ends e).2) (C w) := by
  classical
  apply Set.disjoint_left.mpr
  intro x hx hxw
  have hadj : ∃ d, ((ends e).1 = (ends d).1 ∧ w = (ends d).2) ∨
      ((ends e).1 = (ends d).2 ∧ w = (ends d).1) := by
    by_contra hn
    exact Set.disjoint_left.mp (hnonadj _ w hw₀.symm hn) hx.1 hxw
  obtain ⟨d, hd⟩ := hadj
  have hde : d ≠ e := by
    intro he
    subst d
    exact hd.elim (fun h => hw₁ h.2) (fun h => hw₀ h.2)
  have hxd : x ∈ C (ends d).1 ∩ C (ends d).2 := by
    rcases hd with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact ⟨ha ▸ hx.1, hb ▸ hxw⟩
    · exact ⟨hb ▸ hxw, ha ▸ hx.1⟩
  exact Set.disjoint_left.mp (hdisj hde) hxd hx

theorem exists_section34_piercing_circle_neighborhoods
    {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    (hU : IsOpen U)
    (ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (Cp CpBd Cc Kcore : Section34VertexIndex 𝒦 𝒦' → Set M)
    (hCp : ∀ w, IsPLCellOn 3 (Cp w) (CpBd w)) (hCpU : ∀ w, Cp w ⊆ U)
    (hCc : ∀ w, Cp w ⊆ interior (Cc w))
    (hcover : graphSkeletonSpace 𝒦 ⊆ ⋃ w, interior (Cp w))
    (hLF : LocallyFinite fun w => {x : U | (x : M) ∈ Cp w})
    (hcore : ∀ w, IsCompact (Kcore w) ∧ Kcore w ⊆ interior (Cp w))
    (hnonadj : ∀ w w', w ≠ w' → (¬ ∃ e : Section34EdgeIndex 𝒦 𝒦',
      (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1)) →
      Disjoint (Cp w) (Cp w'))
    (O : Section34EdgeIndex 𝒦 𝒦' → Set M) (hO : ∀ e, IsOpen (O e))
    (hOLF : LocallyFinite fun e => {x : U | (x : M) ∈ O e})
    (hdisj : Pairwise (Disjoint on O))
    (hlens : ∀ e, Cp (ends e).1 ∩ Cp (ends e).2 ⊆ O e) :
    ∃ V : Section34EdgeIndex 𝒦 𝒦' → Set M,
      (∀ e, IsOpen (V e)) ∧ (∀ e, CpBd (ends e).1 ∩ CpBd (ends e).2 ⊆ V e) ∧
      (∀ e, V e ⊆ O e ∩ (interior (Cc (ends e).1) ∩ interior (Cc (ends e).2))) ∧
      (∀ e, V e ⊆ U) ∧ (LocallyFinite fun e => {x : U | (x : M) ∈ V e}) ∧
      Pairwise (Disjoint on V) ∧ (∀ e, Disjoint (V e) (graphSkeletonSpace 𝒦)) ∧
      (∀ e w, Disjoint (V e) (Kcore w)) ∧
      ∀ e w, w ≠ (ends e).1 → w ≠ (ends e).2 → Disjoint (V e) (Cp w) := by
  have hCpClosed (w) := (hCp w).isCompact.isClosed
  have hBd (w) : CpBd w = frontier (Cp w) := (hCp w).boundary_eq_frontier
  let J := fun e => CpBd (ends e).1 ∩ CpBd (ends e).2
  have hJL (e) : J e ⊆ Cp (ends e).1 ∩ Cp (ends e).2 := by
    dsimp only [J]
    rw [hBd, hBd]
    exact inter_subset_inter (hCpClosed _).frontier_subset (hCpClosed _).frontier_subset
  have hpair : Pairwise (Disjoint on fun e => Cp (ends e).1 ∩ Cp (ends e).2) :=
    fun e d hed => (hdisj hed).mono (hlens e) (hlens d)
  have hforeign (e w) (hw₀ : w ≠ (ends e).1) (hw₁ : w ≠ (ends e).2) :
      Disjoint (J e) (Cp w) :=
    (lens_disjoint_nonincident Cp ends hnonadj hpair e w hw₀ hw₁).mono_left (hJL e)
  have hJI (e w) : Disjoint (J e) (interior (Cp w)) := by
    apply Set.disjoint_left.mpr
    intro x hx hxi
    by_cases hw₀ : w = (ends e).1
    · exact ((hBd _).subset hx.1).2 (hw₀ ▸ hxi)
    · by_cases hw₁ : w = (ends e).2
      · exact ((hBd _).subset hx.2).2 (hw₁ ▸ hxi)
      · exact Set.disjoint_left.mp (hforeign e w hw₀ hw₁) hx (interior_subset hxi)
  have hJG (e) : Disjoint (J e) (graphSkeletonSpace 𝒦) := by
    apply Set.disjoint_left.mpr
    intro x hx hxg
    obtain ⟨w, hw⟩ := mem_iUnion.mp (hcover hxg)
    exact Set.disjoint_left.mp (hJI e w) hx hw
  let F : Set U := ⋃ w, (Subtype.val : U → M) ⁻¹' Kcore w
  have hF : IsClosed F :=
    (hLF.subset (fun w _ hx =>
      (interior_subset : interior (Cp w) ⊆ Cp w) ((hcore w).2 hx))).isClosed_iUnion
      (fun w => (hcore w).1.isClosed.preimage continuous_subtype_val)
  let B := fun e => ⋃ w : {w // w ≠ (ends e).1 ∧ w ≠ (ends e).2},
    (Subtype.val : U → M) ⁻¹' Cp w.1
  have hB (e) : IsClosed (B e) :=
    (hLF.comp_injective Subtype.val_injective).isClosed_iUnion
      (fun w => (hCpClosed w.1).preimage continuous_subtype_val)
  let W := fun e => Subtype.val ''
    ({x : U | (x : M) ∈ graphSkeletonSpace 𝒦} ∪ F ∪ B e)ᶜ
  have hW (e) : IsOpen (W e) := hU.isOpenMap_subtype_val _
    (((isClosed_graphSkeletonSpace_in_domain 𝒦).union hF).union (hB e)).isOpen_compl
  let V := fun e => W e ∩ (O e ∩ (interior (Cc (ends e).1) ∩ interior (Cc (ends e).2)))
  have hVO (e) : V e ⊆ O e := fun _ hx => hx.2.1
  refine ⟨V, fun e => (hW e).inter ((hO e).inter (isOpen_interior.inter isOpen_interior)),
    ?_, fun _ => inter_subset_right, ?_, hOLF.subset (fun e _ hx => hVO e hx),
    fun e d hed => (hdisj hed).mono (hVO e) (hVO d), ?_, ?_, ?_⟩
  · intro e x hx
    refine ⟨⟨⟨x, hCpU _ (hJL e hx).1⟩, ?_, rfl⟩,
      hlens e (hJL e hx), hCc _ (hJL e hx).1, hCc _ (hJL e hx).2⟩
    rintro ((hxG | hxF) | hxB)
    · exact Set.disjoint_left.mp (hJG e) hx hxG
    · obtain ⟨w, hw⟩ := mem_iUnion.mp hxF
      exact Set.disjoint_left.mp (hJI e w) hx ((hcore w).2 hw)
    · obtain ⟨w, hw⟩ := mem_iUnion.mp hxB
      exact Set.disjoint_left.mp (hforeign e w.1 w.2.1 w.2.2) hx hw
  · rintro e x ⟨⟨y, -, rfl⟩, -⟩
    exact y.2
  · intro e
    apply Set.disjoint_left.mpr
    rintro x ⟨⟨y, hy, rfl⟩, -⟩ hxG
    exact hy (Or.inl (Or.inl hxG))
  · intro e w
    apply Set.disjoint_left.mpr
    rintro x ⟨⟨y, hy, rfl⟩, -⟩ hxK
    exact hy (Or.inl (Or.inr (mem_iUnion.mpr ⟨w, hxK⟩)))
  · intro e w hw₀ hw₁
    apply Set.disjoint_left.mpr
    rintro x ⟨⟨y, hy, rfl⟩, -⟩ hxC
    exact hy (Or.inr (mem_iUnion.mpr ⟨⟨w, hw₀, hw₁⟩, hxC⟩))

end DifferentialGeometry.Topology.PiecewiseLinear

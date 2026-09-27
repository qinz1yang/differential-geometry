import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import Mathlib.Analysis.Normed.Module.Connected

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

private theorem isConnected_of_isTopologicalSolidTorus {M : Type*} [TopologicalSpace M]
    {S : Set M} (hS : IsTopologicalSolidTorus S) : IsConnected S := by
  obtain ⟨f⟩ := hS
  let _ : ConnectedSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isConnected_iff_connectedSpace.mp (Metric.isConnected_closedBall zero_le_one)
  let _ : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)
  exact isConnected_iff_connectedSpace.mpr (f.connectedSpace_iff.mpr inferInstance)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U W : Set M₁} {h : M₁ → M₂}
  {η ψ : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
  {Sd : Section34SimplexIndex 𝒦 3 → Set (EuclideanSpace ℝ (Fin 3))}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem section34_lens_disjoint_other_cell
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e : Section34EdgeIndex 𝒦 𝒦') (w : Section34VertexIndex 𝒦 𝒦')
    (hw₁ : w ≠ (ends e).1) (hw₂ : w ≠ (ends e).2) :
    Disjoint (G (ends e).1 '' Cp (ends e).1 ∩ G (ends e).2 '' Cp (ends e).2)
      (G w '' Cp w) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnonedge, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hsep, -, -, -, -, -, -, hlens, -⟩ := hpack
  refine Set.disjoint_left.mpr ?_
  intro y hy hyw
  by_cases hed : ∃ d : Section34EdgeIndex 𝒦 𝒦',
      ((ends e).1 = (ends d).1 ∧ w = (ends d).2) ∨
        ((ends e).1 = (ends d).2 ∧ w = (ends d).1)
  · obtain ⟨d, hd | hd⟩ := hed
    · have hne : e ≠ d := by
        intro he
        subst d
        exact hw₂ hd.2
      exact Set.disjoint_left.mp (hlens e d hne) hy
        ⟨hd.1 ▸ hy.1, hd.2 ▸ hyw⟩
    · have hne : e ≠ d := by
        intro he
        subst d
        exact hw₁ hd.2
      exact Set.disjoint_left.mp (hlens e d hne) hy
        ⟨hd.2 ▸ hyw, hd.1 ▸ hy.1⟩
  · exact Set.disjoint_left.mp (hsep _ _ (hnonedge _ _ hw₁.symm hed)) hy.1 hyw

omit [FiniteDimensional ℝ Ea] in
theorem section34_support_isConnected
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e : Section34EdgeIndex 𝒦 𝒦') : IsConnected (Sp e) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htor, hSnCc, -⟩ := hprep
  obtain ⟨hG, -, -, hSp, -⟩ := hpack
  rw [(hSp e).1]
  exact (isConnected_of_isTopologicalSolidTorus (htor e).2.1).image _
    ((hG _).continuousOn.mono (hSnCc e _ (Or.inl rfl)))

omit [FiniteDimensional ℝ Ea] in
theorem section34_support_inter_lens_nonempty
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e : Section34EdgeIndex 𝒦 𝒦') :
    (Sp e ∩ (G (ends e).1 '' Cp (ends e).1 ∩ G (ends e).2 '' Cp (ends e).2)).Nonempty := by
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, hBbSp, -, -, -, -, -, hin, -⟩ := hpack
  obtain ⟨y, hy, -⟩ := hin e
  exact ⟨y, interior_subset ((hBbSp e).1 hy.1), hy.2,
    image_mono ((hBb e).1.trans (hCp _).boundary_subset) hy.1⟩

omit [FiniteDimensional ℝ Ea] in
theorem section34_support_disjoint_other_cell
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e : Section34EdgeIndex 𝒦 𝒦') (w : Section34VertexIndex 𝒦 𝒦')
    (hw₁ : w ≠ (ends e).1) (hw₂ : w ≠ (ends e).2) : Disjoint (Sp e) (G w '' Cp w) := by
  have hconn := (section34_support_isConnected hprep hpack e).isPreconnected
  have hlens := section34_lens_disjoint_other_cell hprep hpack e w hw₁ hw₂
  obtain ⟨y, hySp, hyLens⟩ := section34_support_inter_lens_nonempty hprep hpack e
  obtain ⟨-, -, -, -, hCp, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -, hbd, -⟩ := hpack
  have hclosed : IsClosed (G w '' Cp w) := ((hCp w).image (hG w)).isCompact.isClosed
  have hfront : Disjoint (Sp e) (frontier (G w '' Cp w)) := by
    rw [← ((hCp w).image_boundary_interior (hG w)).1]
    exact hbd e w hw₁ hw₂
  have hcover : Sp e ⊆ interior (G w '' Cp w) ∪ (G w '' Cp w)ᶜ := by
    intro x hx
    by_cases hxi : x ∈ interior (G w '' Cp w)
    · exact Or.inl hxi
    · exact Or.inr fun hxG => Set.disjoint_left.mp hfront hx
        ⟨subset_closure hxG, hxi⟩
  rcases hconn.subset_or_subset isOpen_interior hclosed.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover with hinside | houtside
  · exact (Set.disjoint_left.mp hlens hyLens (interior_subset (hinside hySp))).elim
  · exact Set.disjoint_left.mpr fun x hxSp hxG => houtside hxSp hxG

omit [FiniteDimensional ℝ Ea] in
theorem section34_support_disjoint_other_lens
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e d : Section34EdgeIndex 𝒦 𝒦') (hed : e ≠ d) :
    Disjoint (Sp e)
      (G (ends d).1 '' Cp (ends d).1 ∩ G (ends d).2 '' Cp (ends d).2) := by
  have hisolate := section34_support_disjoint_other_cell hprep hpack e
  obtain ⟨-, -, -, -, -, -, -, -, hends, -⟩ := hprep
  by_cases hda : (ends d).1 = (ends e).1 ∨ (ends d).1 = (ends e).2
  · by_cases hdb : (ends d).2 = (ends e).1 ∨ (ends d).2 = (ends e).2
    · exfalso
      apply hed
      apply Subtype.ext
      apply Finset.coe_injective
      rw [(hends e).2.1, (hends d).2.1]
      rcases hda with hda | hda <;> rcases hdb with hdb | hdb
      · exact ((hends d).1 (hda.trans hdb.symm)).elim
      · rw [hda, hdb]
      · rw [hda, hdb, union_comm]
      · exact ((hends d).1 (hda.trans hdb.symm)).elim
    · exact (hisolate _ (fun h => hdb (Or.inl h)) (fun h => hdb (Or.inr h))).mono_right
        inter_subset_right
  · exact (hisolate _ (fun h => hda (Or.inl h)) (fun h => hda (Or.inr h))).mono_right
      inter_subset_left

end DifferentialGeometry.Topology.PiecewiseLinear

import DifferentialGeometry.Topology.PiecewiseLinear.IndexedEssentialCircleOrder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingEssentialEquivalence

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34_piercing_first_circle_order
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    (hess : ∀ i < cnt e, ¬ ∃ D : Set M₂,
      IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e) :
    ∃ (σ : Fin (cnt e) ≃ Fin (cnt e)) (D₀ D₁ : Fin (cnt e) → Set M₂),
      (∀ i, IsPLCellOn 2 (D₀ i) (Pg e (σ i).val) ∧
        IsPLCellOn 2 (D₁ i) (Pg e (σ i).val) ∧
        D₀ i ∪ D₁ i = G (ends e).1 '' CpBd (ends e).1 ∧
        D₀ i ∩ D₁ i = Pg e (σ i).val ∧
        G (ends e).1 '' Ab₀ e ⊆ D₀ i ∧ G (ends e).1 '' Ab₁ e ⊆ D₁ i) ∧
      StrictMono D₀ ∧ StrictAnti D₁ ∧
      (∀ i j, i < j → Disjoint (D₀ i) (D₁ j)) ∧
      (∀ i j, Pg e (σ i).val ⊆ D₀ j ↔ i ≤ j) ∧
      (∀ i j, Pg e (σ i).val ⊆ D₁ j ↔ j ≤ i) := by
  have hann := (section34_piercing_annuli hprep hpack e).1
  have hfirst (i : Fin (cnt e)) : ¬ ∃ D : Set M₂,
      IsPLCellOn 2 D (Pg e i.val) ∧ D ⊆ G (ends e).1 '' Aa e :=
    (section34_piercing_generators_of_essential_second hprep hpack e i.isLt
      (hess i.val i.isLt)).2.2
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGcp, -, -, -, -, -, -, hPg, hdisj, -⟩ := hpack
  have hACp := ((hAa e).1 ▸ inter_subset_left).trans (hCp (ends e).1).boundary_subset
  have hends (i : Fin (cnt e)) : Disjoint (Pg e i.val)
      (G (ends e).1 '' Ab₀ e ∪ G (ends e).1 '' Ab₁ e) := by
    rw [← image_union]
    refine disjoint_left.mpr ?_
    rintro y hy ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := ((hPg e i.val i.isLt).2 hy).1
    have hzCp := hACp ((union_subset (hAa e).2.first_subset (hAa e).2.second_subset) hz)
    have heq := (hGcp (ends e).1).injOn (hACp hx.1) hzCp (hxy.trans hzy.symm)
    exact hx.2 (heq.symm ▸ hz)
  have hcell := (hCp (ends e).1).image (hGcp (ends e).1)
  refine hcell.exists_ordered_disk_caps_of_essential_sequence hann
      (image_mono ((hAa e).1 ▸ inter_subset_left)) (fun i : Fin (cnt e) => Pg e i.val)
      (fun i => (hPg e i.val i.isLt).1) ?_ hends ?_ hfirst
  · intro i x hx
    exact image_mono sdiff_subset ((hPg e i.val i.isLt).2 hx).1
  · intro i j hij
    exact hdisj e i.val i.isLt j.val j.isLt (fun h => hij (Fin.ext h))

theorem exists_section34_piercing_second_circle_order
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    (hess : ∀ i < cnt e, ¬ ∃ D : Set M₂,
      IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e) :
    ∃ (σ : Fin (cnt e) ≃ Fin (cnt e)) (D₀ D₁ : Fin (cnt e) → Set M₂),
      (∀ i, IsPLCellOn 2 (D₀ i) (Pg e (σ i).val) ∧
        IsPLCellOn 2 (D₁ i) (Pg e (σ i).val) ∧
        D₀ i ∪ D₁ i = G (ends e).2 '' CpBd (ends e).2 ∧
        D₀ i ∩ D₁ i = Pg e (σ i).val ∧
        G (ends e).2 '' Bb₀ e ⊆ D₀ i ∧ G (ends e).2 '' Bb₁ e ⊆ D₁ i) ∧
      StrictMono D₀ ∧ StrictAnti D₁ ∧
      (∀ i j, i < j → Disjoint (D₀ i) (D₁ j)) ∧
      (∀ i j, Pg e (σ i).val ⊆ D₀ j ↔ i ≤ j) ∧
      (∀ i j, Pg e (σ i).val ⊆ D₁ j ↔ j ≤ i) := by
  have hann := (section34_piercing_annuli hprep hpack e).2
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGcp, -, -, -, -, -, -, hPg, hdisj, -⟩ := hpack
  have hBCp := (hBb e).1.trans (hCp (ends e).2).boundary_subset
  have hends (i : Fin (cnt e)) : Disjoint (Pg e i.val)
      (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) := by
    rw [← image_union]
    refine disjoint_left.mpr ?_
    rintro y hy ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := ((hPg e i.val i.isLt).2 hy).2
    have hzCp := hBCp ((union_subset (hBb e).2.first_subset (hBb e).2.second_subset) hz)
    have heq := (hGcp (ends e).2).injOn (hBCp hx.1) hzCp (hxy.trans hzy.symm)
    exact hx.2 (heq.symm ▸ hz)
  have hcell := (hCp (ends e).2).image (hGcp (ends e).2)
  refine hcell.exists_ordered_disk_caps_of_essential_sequence hann (image_mono (hBb e).1)
      (fun i : Fin (cnt e) => Pg e i.val) (fun i => (hPg e i.val i.isLt).1) ?_ hends ?_
      (fun i => hess i.val i.isLt)
  · intro i x hx
    exact image_mono sdiff_subset ((hPg e i.val i.isLt).2 hx).2
  · intro i j hij
    exact hdisj e i.val i.isLt j.val j.isLt (fun h => hij (Fin.ext h))

end DifferentialGeometry.Topology.PiecewiseLinear

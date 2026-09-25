import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnerFirstMotionStep
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetFirstDiskCancellation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingDiskRims
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingDiskTraceDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ContactSupport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.subset_interior_of_boundary_subset {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {C B T : Set M} (hC : IsPLCellOn 3 C B) (hCT : C ⊆ T) (hBT : B ⊆ interior T) :
    C ⊆ interior T := by
  intro x hx
  by_cases hxi : x ∈ interior C
  · exact interior_mono hCT hxi
  · apply hBT
    rw [hC.boundary_eq_frontier]
    exact ⟨subset_closure hx, hxi⟩

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

theorem exists_section34_removal_step_of_interior_disk_filling
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e₀ : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e₀)
    {D F C : Set M₂} (hD : IsPLCellOn 2 D (Pg e₀ i)) (hF : IsPLCellOn 2 F (Pg e₀ i))
    (hFA : F ⊆ G (ends e₀).1 '' Aa e₀) (hC : IsPLCellOn 3 C (D ∪ F))
    (hCT : C ⊆ interior (Tp e₀)) (hmeet : G (ends e₀).1 '' CpBd (ends e₀).1 ∩ C = F)
    (htrace : D ∩ G (ends e₀).1 '' CpBd (ends e₀).1 = Pg e₀ i)
    (hDB : D ⊆ G (ends e₀).2 '' CpBd (ends e₀).2) :
    ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
          Sp Tp cnt' Pg' G' ∧ cnt' e₀ < cnt e₀ ∧
        (∀ e, e ≠ e₀ → cnt' e = cnt e) ∧
        (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}) ∧
        ∀ e, e ≠ e₀ → G' (ends e).1 '' Aa e = G (ends e).1 '' Aa e ∧
          G' (ends e).2 '' Bb e = G (ends e).2 '' Bb e := by
  obtain ⟨I, -, hcard, hsubtrace, -, hclosed⟩ :=
    exists_section34_strict_trace_subfamily_after_disk hprep hpack e₀ hi hF hFA
  have hTS := section34_inner_tube_subset_interior_outer hprep hpack e₀
  obtain ⟨-, hCc, hCpCc, -, hCp, -, -, -, -, -, -, -, hSnCc, -⟩ := id hprep
  obtain ⟨hG, -, -, htube, -, -, -, -, -, -, hGCp, -⟩ := id hpack
  obtain ⟨P, r, u, hr, hu, hCcEq, -⟩ := (hCc (ends e₀).1).image (hG (ends e₀).1)
  have hSpCc : Sp e₀ ⊆ G (ends e₀).1 '' Cc (ends e₀).1 := by
    rw [(htube e₀).1]
    exact image_mono (hSnCc e₀ _ (Or.inl rfl))
  have hAP : G (ends e₀).1 '' Cp (ends e₀).1 ⊆ u '' P := by
    rw [← hCcEq]
    exact image_mono (hCpCc _).2.1
  have hΩP : interior (Tp e₀) ⊆ interior (u '' P) := by
    rw [← hCcEq]
    exact (interior_subset.trans hTS).trans (interior_mono hSpCc)
  have hR : ((G (ends e₀).1 '' CpBd (ends e₀).1 \ C) ∩
      G (ends e₀).2 '' CpBd (ends e₀).2) =
      (G (ends e₀).1 '' CpBd (ends e₀).1 ∩ G (ends e₀).2 '' CpBd (ends e₀).2) \ F := by
    rw [← hmeet]
    ext x
    simp only [mem_inter_iff, mem_sdiff]
    tauto
  obtain ⟨K, φ, hK, hKT, hfix, hφ, hKR, -, hcancel⟩ :=
    hu.exists_relative_first_disk_cancellation ⟨r, hr⟩ ((hCp _).image (hGCp _)) hAP
      ((hCp _).image (hGCp _)) hC hD hF hmeet htrace hDB (hR ▸ hclosed)
      isOpen_interior hCT hΩP
  rw [← hCcEq] at hφ
  rw [hR, hsubtrace] at hKR hcancel
  exact section34_removal_step_of_inner_first_motion hprep hpack e₀ I hcard φ hK
    hKT hfix hφ
    (fun j => hKR.mono_right (subset_iUnion (fun k : I => Pg e₀ k.1.val) j)) hcancel

theorem exists_section34_removal_step_of_interior_disk_pair
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e₀ : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e₀)
    {D F : Set M₂} (hD : IsPLCellOn 2 D (Pg e₀ i)) (hF : IsPLCellOn 2 F (Pg e₀ i))
    (hDT : D ⊆ G (ends e₀).2 '' Bb e₀ ∩ interior (Tp e₀))
    (hFT : F ⊆ G (ends e₀).1 '' Aa e₀ ∩ interior (Tp e₀))
    (htrace : D ∩ G (ends e₀).1 '' CpBd (ends e₀).1 = Pg e₀ i) :
    ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
          Sp Tp cnt' Pg' G' ∧ cnt' e₀ < cnt e₀ ∧
        (∀ e, e ≠ e₀ → cnt' e = cnt e) ∧
        (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}) ∧
        ∀ e, e ≠ e₀ → G' (ends e).1 '' Aa e = G (ends e).1 '' Aa e ∧
          G' (ends e).2 '' Bb e = G (ends e).2 '' Bb e := by
  have hFA := hFT.trans inter_subset_left
  have hFA' : F ⊆ G (ends e₀).1 '' CpBd (ends e₀).1 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hAa, -⟩ := hprep
    exact hFA.trans (image_mono ((hAa e₀).1 ▸ inter_subset_left))
  have hDF : D ∩ F = Pg e₀ i := Subset.antisymm
    (fun _ hx => htrace.subset ⟨hx.1, hFA' hx.2⟩)
    (fun _ hx => ⟨hD.boundary_subset hx, hF.boundary_subset hx⟩)
  obtain ⟨C, hC, hCT⟩ := exists_section34_filling_of_disk_pair hprep hpack e₀ hD hF
    ((hDT.trans inter_subset_right).trans interior_subset)
    ((hFT.trans inter_subset_right).trans interior_subset) hDF
  have hCint := hC.subset_interior_of_boundary_subset hCT
    (union_subset (hDT.trans inter_subset_right) (hFT.trans inter_subset_right))
  obtain ⟨k, hk, -, hgen, -⟩ := exists_section34_piercing_circle_carrying_generators hprep hpack e₀
  have htor := (section34_tubes_are_topological_solid_tori hprep hpack e₀).2
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, hBb, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -, -, -, -, -, -, hPg, -⟩ := id hpack
  have hJne : (Pg e₀ k).Nonempty := by
    obtain ⟨P, hP⟩ := (hPg e₀ k hk).1
    exact P.piece.bijOn.image_eq ▸ hP.nonempty.image P.piece.map
  have hnot : ¬ Pg e₀ k ⊆ C := fun hsub =>
    htor.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hC hCT hJne hsub hgen
  obtain ⟨z, hzJ, hzC⟩ := not_subset.mp hnot
  have hzA : z ∈ G (ends e₀).1 '' CpBd (ends e₀).1 :=
    image_mono (((hAa e₀).1 ▸ inter_subset_left) : Aa e₀ ⊆ CpBd (ends e₀).1)
      (image_mono sdiff_subset ((hPg e₀ k hk).2 hzJ).1)
  have hfront : frontier C ∩ G (ends e₀).1 '' CpBd (ends e₀).1 ⊆ F := by
    rw [← hC.boundary_eq_frontier]
    rintro x ⟨hxD | hxF, hxA⟩
    · exact hF.boundary_subset (htrace.subset ⟨hxD, hxA⟩)
    · exact hxF
  have hmeet := ((hCp _).image (hG _)).inter_eq_disk_of_frontier_inter_subset hF hFA'
    (fun _ hxF => hC.boundary_subset (Or.inr hxF)) hfront ⟨z, hzA, hzC⟩
  exact exists_section34_removal_step_of_interior_disk_filling hprep hpack e₀ hi hD hF hFA
    hC hCint hmeet htrace ((hDT.trans inter_subset_left).trans (image_mono (hBb e₀).1))

end DifferentialGeometry.Topology.PiecewiseLinear

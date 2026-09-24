import DifferentialGeometry.Topology.PiecewiseLinear.Section34CarrierDiskFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CarryingTraceDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnermostAnnulusDisk
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InteriorInnermostDisk
import DifferentialGeometry.Topology.PiecewiseLinear.Section34DiskFillingForeignSupport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetDiskCancellation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.disjoint_closure_sdiff_of_annular_contact {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ C : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) (hcontact : C ∩ B ⊆ A) (hends : Disjoint C (A₀ ∪ A₁)) :
    Disjoint C (closure (B \ A)) := by
  obtain ⟨hchart⟩ := hS.nonempty_chartedSpace_boundary
  let _ := hchart
  let A' := (Subtype.val : B → M) ⁻¹' A
  have hB : IsClosed B := hS.boundary_eq_frontier ▸ isClosed_frontier
  have himage : (Subtype.val : B → M) '' A'ᶜ = B \ A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hxB, hxA⟩
      exact ⟨⟨x, hxB⟩, hxA, rfl⟩
  have hfront := (hA.preimage_subtype hAB).frontier_eq_ends
  refine disjoint_left.mpr fun x hxC hx => ?_
  have hx' : x ∈ (Subtype.val : B → M) '' closure A'ᶜ := by
    rw [← hB.isClosedEmbedding_subtypeVal.closure_image_eq, himage]
    exact hx
  obtain ⟨y, hy, rfl⟩ := hx'
  have hyfront : y ∈ frontier A' := by
    refine ⟨subset_closure (hcontact ⟨hxC, y.2⟩), ?_⟩
    simpa only [closure_compl, mem_compl_iff] using hy
  exact disjoint_left.mp hends hxC (hfront.subset hyfront)

theorem IsPLHomeomorphInto.exists_innermost_disk_cancellation_retaining_carrier
    {M ι : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [Finite ι]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsPLBall 3 P)
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary 3 L) (hLP : L.space ⊆ P)
    (hT : IsTopologicalSolidTorus L.space)
    {A Ab B Bb Aa Aa₀ Aa₁ Ba Ba₀ Ba₁ : Set M} {J : ι → Set M}
    (hA : IsPLCellOn 3 A Ab) (hAP : A ⊆ u '' P) (hB : IsPLCellOn 3 B Bb)
    (hAa : IsAnnulusOn Aa Aa₀ Aa₁) (hAaB : Aa ⊆ Ab)
    (hAaT : Aa ⊆ interior (u '' L.space))
    (hBa : IsAnnulusOn Ba Ba₀ Ba₁) (hBaB : Ba ⊆ Bb)
    (hBaT : Ba ⊆ interior (u '' L.space))
    (hJ : ∀ j, IsPolyhedralSphere (n := 3) 1 (J j))
    (hJA : ∀ j, J j ⊆ Aa) (hJB : ∀ j, J j ⊆ Ba)
    (hendsA : ∀ j, Disjoint (J j) (Aa₀ ∪ Aa₁))
    (hendsB : ∀ j, Disjoint (J j) (Ba₀ ∪ Ba₁))
    (hdis : Pairwise fun j k => Disjoint (J j) (J k)) (htrace : Ab ∩ Bb = ⋃ j, J j)
    (k : ι) (hcarry : CarriesFundamentalGroupOnto (J k) (u '' L.space))
    (hdisk : ∃ (i : ι) (D : Set M), IsPLCellOn 2 D (J i) ∧ D ⊆ Ba) :
    ∃ I : Set ι, k ∈ I ∧ Nat.card I < Nat.card ι ∧
      (∀ j, CarriesFundamentalGroupOnto (J j) (u '' L.space) → j ∈ I) ∧
      ∃ (C K : Set M) (ψ : M ≃ₜ M), IsCompact C ∧ C ⊆ interior (u '' L.space) ∧
        C ∩ Bb ⊆ Ba ∧ IsCompact K ∧ K ⊆ interior (u '' L.space) ∧ EqOn ψ id Kᶜ ∧
        IsPLOn 3 3 ψ (interior (u '' P)) ∧ Disjoint K (Aa₀ ∪ Aa₁) ∧
        Disjoint K (Ba₀ ∪ Ba₁) ∧ Disjoint K (closure (Bb \ Ba)) ∧
        (∀ j : I, Disjoint K (J j.1)) ∧
        (∀ j : I, ∀ x ∈ J j.1, ψ =ᶠ[𝓝 x] id) ∧ Ab ∩ ψ '' Bb = ⋃ j : I, J j.1 := by
  have hT' := hT.image_of_continuousOn_injOn (hu.continuousOn.mono hLP)
    (hu.injOn.mono hLP)
  have hconn (j : ι) : IsConnected (J j) := by
    obtain ⟨Q, hQ⟩ := hJ j
    exact Q.piece.bijOn.image_eq ▸ hQ.isConnected.image _ Q.piece.continuousOn
  have hclosed (j : ι) : IsClosed (J j) := by
    obtain ⟨Q, -⟩ := hJ j
    exact Q.piece.isCompact.isClosed
  have hgen := hAa.carriesFundamentalGroupOnto_first_of_subset
    (hAaT.trans interior_subset) (hJA k) (hconn k).nonempty hcarry
  obtain ⟨i, D, hD, hDBa, -, hDj⟩ := hB.exists_innermost_boundary_disk_subset hBaB hJ
    (fun j => (hJB j).trans hBaB) hdis hdisk
  have hDtrace : D ∩ Ab = J i := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp (htrace.subset ⟨hx.2, hBaB (hDBa hx.1)⟩)
      by_cases hji : j = i
      · exact hji ▸ hxj
      · exact (disjoint_left.mp (hDj j hji) hx.1 hxj).elim
    · exact subset_inter hD.boundary_subset ((hJA i).trans hAaB)
  obtain ⟨F, C, hF, hFA, hC, hCT, -⟩ := hu.exists_interior_filling_of_annular_disk
    L hL hLP hT hA hAa hAaB hAaT (hJ i) (hJA i) (hendsA i) hgen hD
    (hDBa.trans hBaT) hDtrace
  have hFAb := hFA.trans hAaB
  have hnot : ¬ J k ⊆ C := fun hsub =>
    hT'.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hC (hCT.trans interior_subset)
      (hconn k).nonempty hsub hcarry
  obtain ⟨z, hzJ, hzC⟩ := not_subset.mp hnot
  have hfrontA : frontier C ∩ Ab ⊆ F := by
    rw [← hC.boundary_eq_frontier]
    rintro x ⟨hxD | hxF, hxA⟩
    · exact hF.boundary_subset (hDtrace.subset ⟨hxD, hxA⟩)
    · exact hxF
  have hmeet := hA.inter_eq_disk_of_frontier_inter_subset hF hFAb
    (subset_union_right.trans hC.boundary_subset) hfrontA ⟨z, hAaB (hJA k hzJ), hzC⟩
  have hFrim := hA.disjoint_annulus_ends_of_disk_subset hAa hAaB hF hFA (hendsA i)
  have hDrim := hB.disjoint_annulus_ends_of_disk_subset hBa hBaB hD hDBa (hendsB i)
  have hBrim : Disjoint (D ∪ F) (Ba₀ ∪ Ba₁) := by
    refine disjoint_left.mpr ?_
    rintro x (hxD | hxF) hxrim
    · exact disjoint_left.mp hDrim hxD hxrim
    · have hxB := hBaB ((union_subset hBa.first_subset hBa.second_subset) hxrim)
      obtain ⟨j, hxj⟩ := mem_iUnion.mp (htrace.subset ⟨hFAb hxF, hxB⟩)
      exact disjoint_left.mp (hendsB j) hxj hxrim
  have hCBends := hBa.disjoint_ends_of_cell_in_solid_torus (hBaT.trans interior_subset)
    (hJB k) (hconn k).nonempty hcarry hT' hC (hCT.trans interior_subset) hBrim
  have hfrontB : frontier C ∩ Bb ⊆ Ba := by
    rw [← hC.boundary_eq_frontier]
    rintro x ⟨hxD | hxF, hxB⟩
    · exact hDBa hxD
    · obtain ⟨j, hxj⟩ := mem_iUnion.mp (htrace.subset ⟨hFAb hxF, hxB⟩)
      exact hJB j hxj
  have hCB := hB.inter_subset_annulus_of_frontier_inter_subset hBa hBaB
    hC.isCompact.isClosed hfrontB hCBends
  have hCoutside := hB.disjoint_closure_sdiff_of_annular_contact hBa hBaB hCB hCBends
  obtain ⟨I, hkI, hcard, hsubtrace, -, hclose, hkeep⟩ :=
    hA.exists_strict_trace_subfamily_retaining_carrier hT' i k hF hFAb
      ((hFA.trans hAaT).trans interior_subset) hconn (fun j => (hJA j).trans hAaB)
      hclosed hdis hcarry
  have hR : (Ab \ C) ∩ Bb = (⋃ j, J j) \ F := by
    rw [← htrace, ← hmeet]
    ext x
    simp only [mem_inter_iff, mem_sdiff]
    tauto
  let Ω := interior (u '' L.space) \
    (((Aa₀ ∪ Aa₁) ∪ (Ba₀ ∪ Ba₁)) ∪ closure (Bb \ Ba))
  have hΩ : IsOpen Ω := isOpen_interior.sdiff
    (((hAa.ends_isCompact.1.union hAa.ends_isCompact.2).union
      (hBa.ends_isCompact.1.union hBa.ends_isCompact.2)).isClosed.union isClosed_closure)
  have hCΩ : C ⊆ Ω := by
    intro x hx
    refine ⟨hCT hx, ?_⟩
    rintro ((hxa | hxb) | hxout)
    · have hxA := hAaB ((union_subset hAa.first_subset hAa.second_subset) hxa)
      exact disjoint_left.mp hFrim (hmeet.subset ⟨hxA, hx⟩) hxa
    · exact disjoint_left.mp hCBends hx hxb
    · exact disjoint_left.mp hCoutside hx hxout
  obtain ⟨K, ψ, hK, hKΩ, hfix, hψ, hKrest, hnear, hcancel⟩ :=
    hu.exists_relative_second_disk_cancellation hP hA hAP hB hC hD hF hmeet hDtrace
      (hDBa.trans hBaB) (hR ▸ hclose) hΩ hCΩ
      (sdiff_subset.trans (interior_mono (image_mono hLP)))
  rw [hR, hsubtrace] at hKrest hnear hcancel
  refine ⟨I, hkI, hcard, hkeep, C, K, ψ, hC.isCompact, hCT, hCB, hK,
    hKΩ.trans sdiff_subset, hfix, hψ, ?_, ?_, ?_, ?_, ?_, hcancel⟩
  · exact disjoint_left.mpr fun x hx hxR => (hKΩ hx).2 (Or.inl (Or.inl hxR))
  · exact disjoint_left.mpr fun x hx hxR => (hKΩ hx).2 (Or.inl (Or.inr hxR))
  · exact disjoint_left.mpr fun x hx hxR => (hKΩ hx).2 (Or.inr hxR)
  · exact fun j => hKrest.mono_right (subset_iUnion (fun l : I => J l.1) j)
  · exact fun j x hx => hnear x (mem_iUnion.mpr ⟨j, hx⟩)

end DifferentialGeometry.Topology.PiecewiseLinear

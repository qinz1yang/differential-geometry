import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetDiskCancellation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ContactSupport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingDiskRims

open Set Topology

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

theorem exists_section34_piercing_disk_cancellation_motion
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    {D : Set M₂} (hD : IsPLCellOn 2 D (Pg e i))
    (hDT : D ⊆ G (ends e).2 '' Bb e ∩ Tp e)
    (htrace : D ∩ G (ends e).1 '' CpBd (ends e).1 = Pg e i) :
    ∃ I : Set (Fin (cnt e)), I.Nonempty ∧ Nat.card I < cnt e ∧
      ∃ (K : Set M₂) (ψ : M₂ ≃ₜ M₂), IsCompact K ∧ K ⊆ interior (Sp e) ∧ EqOn ψ id Kᶜ ∧
        IsPLOn 3 3 ψ (interior (G (ends e).1 '' Cc (ends e).1)) ∧
        Disjoint K (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) ∧
        Disjoint K (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) ∧
        (∀ j : I, Disjoint K (Pg e j.1.val)) ∧
        G (ends e).1 '' CpBd (ends e).1 ∩ ψ '' (G (ends e).2 '' CpBd (ends e).2) =
          ⋃ j : I, Pg e j.1.val := by
  obtain ⟨F, C, hF, hFA, hC, hCT, hmeet, -, -⟩ :=
    exists_section34_filling_with_exact_first_trace hprep hpack e hi hD hDT htrace
  obtain ⟨I, hne, hcard, hsubtrace, -, hclosed⟩ :=
    exists_section34_strict_trace_subfamily_after_disk hprep hpack e hi hF hFA
  have hFrim := section34_piercing_disk_disjoint_first_rims hprep hpack e hi hF hFA
  have hArimclosed : IsClosed (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) := by
    rw [image_union]
    have hends := (section34_piercing_annuli hprep hpack e).1.ends_isCompact
    exact (hends.1.union hends.2).isClosed
  have hTS := section34_inner_tube_subset_interior_outer hprep hpack e
  have hrimclosed : IsClosed (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) := by
    rw [image_union]
    have hends := (section34_piercing_annuli hprep hpack e).2.ends_isCompact
    exact (hends.1.union hends.2).isClosed
  obtain ⟨-, hCc, hCpCc, -, hCp, -, -, -, -, -, -, -, hSnCc, -, hAa, hBb, -⟩ := hprep
  obtain ⟨hG, -, -, htube, -, -, -, -, hBrim, -, hGCp, -⟩ := hpack
  obtain ⟨P, r, u, hr, hu, hCcEq, -⟩ := (hCc (ends e).1).image (hG (ends e).1)
  have hSpCc : Sp e ⊆ G (ends e).1 '' Cc (ends e).1 := by
    rw [(htube e).1]
    exact image_mono (hSnCc e _ (Or.inl rfl))
  have hAP : G (ends e).1 '' Cp (ends e).1 ⊆ u '' P := by
    rw [← hCcEq]
    exact image_mono (hCpCc _).2.1
  have hΩP : interior (Sp e) ⊆ interior (u '' P) := by
    rw [← hCcEq]
    exact interior_mono hSpCc
  have hArimBd : G (ends e).1 '' (Ab₀ e ∪ Ab₁ e) ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    image_mono ((union_subset (hAa e).2.first_subset (hAa e).2.second_subset).trans
      ((hAa e).1 ▸ inter_subset_left))
  have hCΩ : C ⊆ interior (Sp e) \
      (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e) ∪ G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) := by
    intro x hx
    refine ⟨hTS (hCT hx), ?_⟩
    rintro (hxA | hxB)
    · exact disjoint_left.mp hFrim (hmeet.subset ⟨hArimBd hxA, hx⟩) hxA
    · exact disjoint_left.mp (hBrim e).2 hxB (hCT hx)
  have hR : ((G (ends e).1 '' CpBd (ends e).1 \ C) ∩
      G (ends e).2 '' CpBd (ends e).2) =
      (G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2) \ F := by
    rw [← hmeet]
    ext x
    simp only [mem_inter_iff, mem_sdiff]
    tauto
  obtain ⟨K, ψ, hK, hKS, hfix, hψ, hKR, -, hcancel⟩ :=
    hu.exists_relative_second_disk_cancellation ⟨r, hr⟩ ((hCp _).image (hGCp _)) hAP
      ((hCp _).image (hGCp _)) hC hD hF hmeet htrace
      ((hDT.trans inter_subset_left).trans (image_mono (hBb e).1))
      (hR ▸ hclosed) (isOpen_interior.sdiff (hArimclosed.union hrimclosed)) hCΩ
      (sdiff_subset.trans hΩP)
  rw [← hCcEq] at hψ
  rw [hR, hsubtrace] at hKR hcancel
  refine ⟨I, hne, hcard, K, ψ, hK, hKS.trans sdiff_subset, hfix, hψ, ?_, ?_, ?_, hcancel⟩
  · exact disjoint_left.mpr fun _ hx hxR => (hKS hx).2 (Or.inl hxR)
  · exact disjoint_left.mpr fun _ hx hxR => (hKS hx).2 (Or.inr hxR)
  · exact fun j => hKR.mono_right (subset_iUnion (fun k : I => Pg e k.1.val) j)

end DifferentialGeometry.Topology.PiecewiseLinear

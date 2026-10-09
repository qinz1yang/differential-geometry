import DifferentialGeometry.Topology.PiecewiseLinear.Section34SynchronizedCrosscutNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCrosscutCancellation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem Section34SeamMarkedBandFilling.exists_second_trace_motion_avoiding
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Cc Cp Cq As Bs S T D F J₀ J₁ : Set M}
    (h : Section34SeamMarkedBandFilling Cc Cp Cq As Bs S T D F J₀ J₁)
    (hAs : As ⊆ Cc) {ι : Type*} [Finite ι] {Γ : ι → Set M}
    (hΓ : ∀ i, IsPolyhedralSphere (n := 3) 1 (Γ i))
    (hΓdis : Pairwise fun i j => Disjoint (Γ i) (Γ j)) (hfull : As ∩ Bs = ⋃ i, Γ i)
    {Z : Set M} (hZ : IsClosed Z) (hZsheet : Z ⊆ As ∪ Bs)
    (hZfaces : Disjoint Z (D ∪ F)) :
    ∃ (I : Set ι) (ψ : M ≃ₜ M) (K : Set M), Nat.card I < Nat.card ι ∧
      IsCompact K ∧ K ⊆ interior S ∧ EqOn ψ id Kᶜ ∧ IsPLOn 3 3 ψ (interior Cc) ∧
      J₀ ∪ J₁ ⊆ K ∧ (∀ i : I, Disjoint K (Γ i.1)) ∧
      (∀ i : I, ∀ x ∈ Γ i.1, ψ =ᶠ[𝓝 x] id) ∧ As ∩ ψ '' Bs = ⋃ i : I, Γ i.1 ∧
      Disjoint K Z ∧ K ∩ (As ∩ Bs) = J₀ ∪ J₁ := by
  obtain ⟨P, V, u, N, X, Y, H, δ, ε, p, e, r,
    ⟨hP, hu, hcell, hVP, hVS, hN, -, hH, hends, hfront,
    hδ, hε, hXN, hYN, hXends, hYends, hXY, hpne, hpN, hPg, hfirst, hsecond,
    hcharts⟩, havoid⟩ := h.exists_crosscut_neighborhood_avoiding hZ hZsheet hZfaces
  have hV : IsCompact V := by
    rw [← hH.image_eq]
    exact (hN.isPolyhedron.isCompact.prod isCompact_Icc).image_of_continuousOn
      hH.isPiecewiseAffineOn.continuousOn
  obtain ⟨I, ψ, hlt, hcompact, hfix, hPL, hkeep, hgerms, hfinal⟩ :=
    hu.exists_second_trace_motion_of_two_interior_crossings hP.isPolyhedron hV hVP
      (hAs.trans hcell.symm.subset) hN hε hYN hYends hδ hXN hXends p hpN hpne
      ((inter_comm Y X).trans hXY) e r (fun k => (hcharts k).1)
      (fun k => (hcharts k).2.2.2.1) (fun k => (hcharts k).2.2.1)
      (fun k => (hcharts k).2.2.2.2.1) (fun k => (hcharts k).2.2.2.2.2)
      hH hends hfront.subset hsecond hfirst hΓ hΓdis hfull
  have hXP : H '' (X ×ˢ Icc (0 : ℝ) 1) ⊆ P :=
    ((image_mono (prod_mono_left hXN)).trans hH.image_eq.subset).trans
      (hVP.trans interior_subset)
  have hYP : H '' (Y ×ˢ Icc (0 : ℝ) 1) ⊆ P :=
    ((image_mono (prod_mono_left hYN)).trans hH.image_eq.subset).trans
      (hVP.trans interior_subset)
  have hsupportTrace : u '' V ∩ (As ∩ Bs) = J₀ ∪ J₁ := by
    calc
      u '' V ∩ (As ∩ Bs) = (u '' V ∩ As) ∩ (u '' V ∩ Bs) := by
        ext x
        simp only [mem_inter_iff]
        tauto
      _ = u '' (H '' (X ×ˢ Icc (0 : ℝ) 1) ∩ H '' (Y ×ˢ Icc (0 : ℝ) 1)) := by
        rw [hfirst, hsecond, image_comp, image_comp, hu.injOn.image_inter hXP hYP]
      _ = (u ∘ H) '' ((X ∩ Y) ×ˢ Icc (0 : ℝ) 1) := by
        rw [hH.inter_images_base_regions hends hXN hYN, image_comp]
      _ = J₀ ∪ J₁ := by
        rw [hXY, ← singleton_union, union_prod, image_union, hPg 0, hPg 1]
        rfl
  refine ⟨I, ψ, u '' V, hlt, hcompact, hVS, hfix, hcell ▸ hPL, ?_, hkeep, hgerms,
    hfinal, havoid, hsupportTrace⟩
  have hsub (k : Fin 2) : ![J₀, J₁] k ⊆ u '' V := by
    rw [← hPg k, image_comp, ← hH.image_eq]
    exact image_mono (image_mono (prod_mono_left
      (singleton_subset_iff.mpr (interior_subset (hpN k)))))
  exact union_subset (hsub 0) (hsub 1)

theorem Section34SeamMarkedBandFilling.exists_second_trace_motion
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Cc Cp Cq As Bs S T D F J₀ J₁ : Set M}
    (h : Section34SeamMarkedBandFilling Cc Cp Cq As Bs S T D F J₀ J₁)
    (hAs : As ⊆ Cc) {ι : Type*} [Finite ι] {Γ : ι → Set M}
    (hΓ : ∀ i, IsPolyhedralSphere (n := 3) 1 (Γ i))
    (hΓdis : Pairwise fun i j => Disjoint (Γ i) (Γ j)) (hfull : As ∩ Bs = ⋃ i, Γ i) :
    ∃ (I : Set ι) (ψ : M ≃ₜ M) (K : Set M), Nat.card I < Nat.card ι ∧
      IsCompact K ∧ K ⊆ interior S ∧ EqOn ψ id Kᶜ ∧ IsPLOn 3 3 ψ (interior Cc) ∧
      J₀ ∪ J₁ ⊆ K ∧ (∀ i : I, Disjoint K (Γ i.1)) ∧
      (∀ i : I, ∀ x ∈ Γ i.1, ψ =ᶠ[𝓝 x] id) ∧ As ∩ ψ '' Bs = ⋃ i : I, Γ i.1 := by
  obtain ⟨I, ψ, K, hlt, hK, hKS, hfix, hPL, hJ, hkeep, hgerms, htrace, -⟩ :=
    h.exists_second_trace_motion_avoiding hAs hΓ hΓdis hfull isClosed_empty
      (empty_subset _) (empty_disjoint _)
  exact ⟨I, ψ, K, hlt, hK, hKS, hfix, hPL, hJ, hkeep, hgerms, htrace⟩

end DifferentialGeometry.Topology.PiecewiseLinear

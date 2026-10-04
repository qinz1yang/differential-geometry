import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCrosscutCancellation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredCylinderFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_relative_annular_trace_cancellation_avoiding
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P V : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hP : IsPolyhedron P) (hu : IsPLHomeomorphInto 3 u P)
    (hVP : V ⊆ interior P) {As Bs S J₀ J₁ Z : Set M}
    (hVS : u '' V ⊆ interior S) (hAs : As ⊆ u '' P)
    {N X Y : Set (ℝ × ℝ)} (hN : IsPLBall 2 N)
    {H : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hH : IsCylindricalDiagram H N V) (hends : ∀ z ∈ N, H (z, 0) = H (z, 1))
    {δ ε : ℝ → ℝ × ℝ}
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) X)
    (hε : IsPLHomeomorphOn ε (Icc 0 1) Y)
    (hXN : X ⊆ N) (hYN : Y ⊆ N)
    (hXends : X ∩ frontier N = {δ 0, δ 1})
    (hYends : Y ∩ frontier N = {ε 0, ε 1})
    (p : Fin 2 → ℝ × ℝ) (hXY : X ∩ Y = {p 0, p 1})
    (hpne : p 0 ≠ p 1) (hpN : ∀ k, p k ∈ interior N)
    (hPg : ∀ k, (u ∘ H) '' ({p k} ×ˢ Icc (0 : ℝ) 1) = ![J₀, J₁] k)
    (hfirst : u '' V ∩ As = (u ∘ H) '' (X ×ˢ Icc (0 : ℝ) 1))
    (hsecond : u '' V ∩ Bs = (u ∘ H) '' (Y ×ˢ Icc (0 : ℝ) 1))
    (e : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) (r : Fin 2 → ℝ)
    (hr : ∀ k, 0 < r k)
    (hsource : ∀ k, Ioo (-r k) (r k) ×ˢ Ioo (-r k) (r k) ⊆ (e k).source)
    (hcenter : ∀ k, e k (0, 0) = p k)
    (hcurve : ∀ k, ∀ z ∈ Ioo (-r k) (r k) ×ˢ Ioo (-r k) (r k), e k z ∈ X ↔ z.2 = 0)
    (haxis : ∀ k, ∀ s ∈ Ioo (-r k) (r k), e k (0, s) ∈ Y)
    {ι : Type*} [Finite ι] {Γ : ι → Set M}
    (hΓ : ∀ i, IsPolyhedralSphere (n := 3) 1 (Γ i))
    (hΓdis : Pairwise fun i j => Disjoint (Γ i) (Γ j)) (hfull : As ∩ Bs = ⋃ i, Γ i)
    (havoid : Disjoint (u '' V) Z) :
    ∃ (I : Set ι) (ψ : M ≃ₜ M), Nat.card I < Nat.card ι ∧
      IsCompact (u '' V) ∧ u '' V ⊆ interior S ∧ EqOn ψ id (u '' V)ᶜ ∧
      IsPLOn 3 3 ψ (interior (u '' P)) ∧
      J₀ ∪ J₁ ⊆ u '' V ∧ (∀ i : I, Disjoint (u '' V) (Γ i.1)) ∧
      (∀ i : I, ∀ x ∈ Γ i.1, ψ =ᶠ[𝓝 x] id) ∧ As ∩ ψ '' Bs = ⋃ i : I, Γ i.1 ∧
      Disjoint (u '' V) Z ∧ (u '' V) ∩ (As ∩ Bs) = J₀ ∪ J₁ := by
  have hV : IsCompact V := by
    rw [← hH.image_eq]
    exact (hN.isPolyhedron.isCompact.prod isCompact_Icc).image_of_continuousOn
      hH.isPiecewiseAffineOn.continuousOn
  obtain ⟨I, ψ, hlt, hcompact, hfix, hPL, hkeep, hgerms, hfinal⟩ :=
    hu.exists_second_trace_motion_of_two_interior_crossings hP hV hVP
      hAs hN hε hYN hYends hδ hXN hXends p hpN hpne
      ((inter_comm Y X).trans hXY) e r hr
      hsource hcenter
      hcurve haxis
      hH hends (hH.frontier_eq_image_base_frontier hN (by simp) (by simp)).subset hsecond hfirst hΓ hΓdis hfull
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
  have hsub (k : Fin 2) : ![J₀, J₁] k ⊆ u '' V := by
    rw [← hPg k, image_comp, ← hH.image_eq]
    exact image_mono (image_mono (prod_mono_left
      (singleton_subset_iff.mpr (interior_subset (hpN k)))))
  exact ⟨I, ψ, hlt, hcompact, hVS, hfix, hPL,
    union_subset (hsub 0) (hsub 1), hkeep, hgerms, hfinal, havoid, hsupportTrace⟩

theorem exists_relative_annular_trace_cancellation
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P V : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hP : IsPolyhedron P) (hu : IsPLHomeomorphInto 3 u P)
    (hVP : V ⊆ interior P) {As Bs S J₀ J₁ : Set M}
    (hVS : u '' V ⊆ interior S) (hAs : As ⊆ u '' P)
    {N X Y : Set (ℝ × ℝ)} (hN : IsPLBall 2 N)
    {H : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hH : IsCylindricalDiagram H N V) (hends : ∀ z ∈ N, H (z, 0) = H (z, 1))
    {δ ε : ℝ → ℝ × ℝ}
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) X)
    (hε : IsPLHomeomorphOn ε (Icc 0 1) Y)
    (hXN : X ⊆ N) (hYN : Y ⊆ N)
    (hXends : X ∩ frontier N = {δ 0, δ 1})
    (hYends : Y ∩ frontier N = {ε 0, ε 1})
    (p : Fin 2 → ℝ × ℝ) (hXY : X ∩ Y = {p 0, p 1})
    (hpne : p 0 ≠ p 1) (hpN : ∀ k, p k ∈ interior N)
    (hPg : ∀ k, (u ∘ H) '' ({p k} ×ˢ Icc (0 : ℝ) 1) = ![J₀, J₁] k)
    (hfirst : u '' V ∩ As = (u ∘ H) '' (X ×ˢ Icc (0 : ℝ) 1))
    (hsecond : u '' V ∩ Bs = (u ∘ H) '' (Y ×ˢ Icc (0 : ℝ) 1))
    (e : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) (r : Fin 2 → ℝ)
    (hr : ∀ k, 0 < r k)
    (hsource : ∀ k, Ioo (-r k) (r k) ×ˢ Ioo (-r k) (r k) ⊆ (e k).source)
    (hcenter : ∀ k, e k (0, 0) = p k)
    (hcurve : ∀ k, ∀ z ∈ Ioo (-r k) (r k) ×ˢ Ioo (-r k) (r k), e k z ∈ X ↔ z.2 = 0)
    (haxis : ∀ k, ∀ s ∈ Ioo (-r k) (r k), e k (0, s) ∈ Y)
    {ι : Type*} [Finite ι] {Γ : ι → Set M}
    (hΓ : ∀ i, IsPolyhedralSphere (n := 3) 1 (Γ i))
    (hΓdis : Pairwise fun i j => Disjoint (Γ i) (Γ j)) (hfull : As ∩ Bs = ⋃ i, Γ i) :
    ∃ (I : Set ι) (ψ : M ≃ₜ M), Nat.card I < Nat.card ι ∧
      IsCompact (u '' V) ∧ u '' V ⊆ interior S ∧ EqOn ψ id (u '' V)ᶜ ∧
      IsPLOn 3 3 ψ (interior (u '' P)) ∧
      J₀ ∪ J₁ ⊆ u '' V ∧ (∀ i : I, Disjoint (u '' V) (Γ i.1)) ∧
      (∀ i : I, ∀ x ∈ Γ i.1, ψ =ᶠ[𝓝 x] id) ∧ As ∩ ψ '' Bs = ⋃ i : I, Γ i.1 ∧
      (u '' V) ∩ (As ∩ Bs) = J₀ ∪ J₁ := by
  obtain ⟨I, ψ, hlt, hcompact, hVS, hfix, hPL, hJ, hkeep, hgerms, htrace, -, hinter⟩ :=
    exists_relative_annular_trace_cancellation_avoiding
    hP hu hVP hVS hAs hN hH hends hδ hε hXN hYN hXends hYends p hXY hpne hpN hPg
    hfirst hsecond e r hr hsource hcenter hcurve haxis hΓ hΓdis hfull (disjoint_empty _)
  exact ⟨I, ψ, hlt, hcompact, hVS, hfix, hPL, hJ, hkeep, hgerms, htrace, hinter⟩

end DifferentialGeometry.Topology.PiecewiseLinear

import DifferentialGeometry.Topology.PiecewiseLinear.BranchBoundaryCollar
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarBallExterior

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem notMem_of_mem_frontier_of_subset_interior {D G : SingularTwoCell M}
    (hGdom : D.domain ⊆ interior G.domain) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ frontier G.domain) : x ∉ D.domain := by
  intro hxD
  have hmem : x ∈ closure G.domain \ interior G.domain := hx
  exact hmem.2 (hGdom hxD)

theorem range_boundary_subset_boundary_of_boundarySweep {D G : SingularTwoCell M}
    {BdM : Set M} {g : EuclideanSpace ℝ (Fin 2) → M}
    {ρ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {τ : EuclideanSpace ℝ (Fin 2) → ℝ} {Φ : M → ℝ → M}
    (hGdom : D.domain ⊆ interior G.domain)
    (hρfr : MapsTo ρ (G.domain \ D.domain) (frontier D.domain))
    (hτ1 : ∀ x ∈ frontier G.domain, τ x = 1)
    (hGann : ∀ x ∈ G.domain \ D.domain, G x = Φ (g (ρ x)) (τ x))
    (hΦ1 : ∀ z ∈ frontier D.domain, Φ (g z) 1 ∈ BdM) :
    Set.range G.boundary ⊆ BdM := by
  rintro _ ⟨z, rfl⟩
  have hzfr : (z : EuclideanSpace ℝ (Fin 2)) ∈ frontier G.domain := z.2
  have hzd : (z : EuclideanSpace ℝ (Fin 2)) ∈ G.domain \ D.domain :=
    ⟨G.frontier_subset_domain hzfr, notMem_of_mem_frontier_of_subset_interior hGdom hzfr⟩
  rw [SingularTwoCell.boundary_apply, hGann _ hzd, hτ1 _ hzfr]
  exact hΦ1 _ (hρfr hzd)

theorem image_sdiff_inter_boundary_subset_of_boundarySweep {D G : SingularTwoCell M}
    {BdM : Set M} {g : EuclideanSpace ℝ (Fin 2) → M}
    {ρ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {τ : EuclideanSpace ℝ (Fin 2) → ℝ} {Φ : M → ℝ → M}
    (hGdom : D.domain ⊆ interior G.domain)
    (hρfr : MapsTo ρ (G.domain \ D.domain) (frontier D.domain))
    (hρsurj : frontier D.domain ⊆ ρ '' frontier G.domain)
    (hτ1 : ∀ x ∈ frontier G.domain, τ x = 1)
    (hGann : ∀ x ∈ G.domain \ D.domain, G x = Φ (g (ρ x)) (τ x))
    (hΦfix : ∀ y ∈ BdM, ∀ s : ℝ, Φ y s = y)
    (hΦmem : ∀ z ∈ frontier D.domain, ∀ s : ℝ, Φ (g z) s ∈ BdM → g z ∈ BdM ∨ s = 1) :
    G '' (G.domain \ D.domain) ∩ BdM ⊆ Set.range G.boundary := by
  rintro _ ⟨⟨x, hx, rfl⟩, hmem⟩
  have hzfr : ρ x ∈ frontier D.domain := hρfr hx
  obtain ⟨x', hx'fr, hx'eq⟩ := hρsurj hzfr
  have hx'd : x' ∈ G.domain \ D.domain :=
    ⟨G.frontier_subset_domain hx'fr, notMem_of_mem_frontier_of_subset_interior hGdom hx'fr⟩
  rw [hGann x hx] at hmem
  have hkey : G x = G x' := by
    rw [hGann x hx, hGann x' hx'd, hx'eq, hτ1 x' hx'fr]
    rcases hΦmem (ρ x) hzfr (τ x) hmem with hbd | hs
    · rw [hΦfix _ hbd, hΦfix _ hbd]
    · rw [hs]
  exact ⟨⟨x', hx'fr⟩, hkey.symm⟩

theorem image_frontier_inter_boundary_subset_of_boundarySweep {D G : SingularTwoCell M}
    {BdM : Set M} {g : EuclideanSpace ℝ (Fin 2) → M}
    {ρ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {τ : EuclideanSpace ℝ (Fin 2) → ℝ} {Φ : M → ℝ → M}
    (hGdom : D.domain ⊆ interior G.domain)
    (hρsurj : frontier D.domain ⊆ ρ '' frontier G.domain)
    (hτ1 : ∀ x ∈ frontier G.domain, τ x = 1)
    (hGann : ∀ x ∈ G.domain \ D.domain, G x = Φ (g (ρ x)) (τ x))
    (hΦfix : ∀ y ∈ BdM, ∀ s : ℝ, Φ y s = y) :
    g '' frontier D.domain ∩ BdM ⊆ Set.range G.boundary := by
  rintro _ ⟨⟨z, hz, rfl⟩, hmem⟩
  obtain ⟨x', hx'fr, hx'eq⟩ := hρsurj hz
  have hx'd : x' ∈ G.domain \ D.domain :=
    ⟨G.frontier_subset_domain hx'fr, notMem_of_mem_frontier_of_subset_interior hGdom hx'fr⟩
  refine ⟨⟨x', hx'fr⟩, ?_⟩
  change G x' = g z
  rw [hGann x' hx'd, hx'eq, hτ1 x' hx'fr, hΦfix _ hmem]

open Classical in
theorem exists_singularTwoCell_of_boundarySweep {D : SingularTwoCell M}
    {g : EuclideanSpace ℝ (Fin 2) → M} {Δ' : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {τ : EuclideanSpace ℝ (Fin 2) → ℝ} {Φ : M → ℝ → M}
    (hgpl : IsPLOn 2 3 g D.domain) (hΔ' : IsPLBall 2 Δ') (hsub : D.domain ⊆ Δ')
    (hρid : ∀ x ∈ D.domain, ρ x = x) (hτ0 : ∀ x ∈ D.domain, τ x = 0)
    (hΦ0 : ∀ y : M, Φ y 0 = y)
    (hann : IsPLOn 2 3 (fun x => Φ (g (ρ x)) (τ x)) (Δ' \ interior D.domain)) :
    ∃ G : SingularTwoCell M, G.domain = Δ' ∧ (∀ x ∈ D.domain, G x = g x) ∧
      ∀ x ∈ Δ' \ D.domain, G x = Φ (g (ρ x)) (τ x) := by
  have hDclosed : IsClosed D.domain := D.isPLBall_domain.isPolyhedron.isCompact.isClosed
  have hΔclosed : IsClosed Δ' := hΔ'.isPolyhedron.isCompact.isClosed
  have hQclosed : IsClosed (Δ' \ interior D.domain) := hΔclosed.sdiff isOpen_interior
  have hunion : D.domain ∪ (Δ' \ interior D.domain) = Δ' := by
    apply Subset.antisymm
    · exact union_subset hsub Set.sdiff_subset
    · intro x hx
      by_cases hxi : x ∈ interior D.domain
      · exact Or.inl (interior_subset hxi)
      · exact Or.inr ⟨hx, hxi⟩
  have hagree : EqOn g (fun x => Φ (g (ρ x)) (τ x))
      (D.domain ∩ (Δ' \ interior D.domain)) := by
    rintro x ⟨hxD, -⟩
    change g x = Φ (g (ρ x)) (τ x)
    rw [hρid x hxD, hτ0 x hxD, hΦ0]
  have hpl : IsPLOn 2 3 (D.domain.piecewise g (fun x => Φ (g (ρ x)) (τ x))) Δ' := by
    have hpiece := hgpl.piecewise_of_isClosed hann hDclosed hQclosed hagree
    rwa [hunion] at hpiece
  refine ⟨⟨Δ', hΔ', D.domain.piecewise g (fun x => Φ (g (ρ x)) (τ x)), hpl⟩, rfl, ?_, ?_⟩
  · intro x hx
    change D.domain.piecewise g (fun x => Φ (g (ρ x)) (τ x)) x = g x
    exact Set.piecewise_eq_of_mem _ _ _ hx
  · rintro x ⟨-, hx⟩
    change D.domain.piecewise g (fun x => Φ (g (ρ x)) (τ x)) x = Φ (g (ρ x)) (τ x)
    exact Set.piecewise_eq_of_notMem _ _ _ hx

open Classical in
theorem exists_collarExtension_image_inter_boundary_of_exteriorCollapse
    {D : SingularTwoCell M} {BdM N : Set M} {h : M → M}
    {P : Set (EuclideanSpace ℝ (Fin 2))} {Φ : M → ℝ → M}
    {Δ' : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {τ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hbdpre : D.domain ∩ D ⁻¹' BdM ⊆ frontier D.domain)
    (hDN : MapsTo D D.domain N)
    (hrefl : ∀ x ∈ N, h x ∈ BdM → x ∈ BdM)
    (hgpl : IsPLOn 2 3 (P.piecewise (h ∘ D) D) D.domain)
    (hΔ'ball : IsPLBall 2 Δ') (hsubint : D.domain ⊆ interior Δ')
    (hρid : ∀ x ∈ D.domain, ρ x = x)
    (hρfr : MapsTo ρ (Δ' \ D.domain) (frontier D.domain))
    (hρsurj : frontier D.domain ⊆ ρ '' frontier Δ')
    (hτ0 : ∀ x ∈ D.domain, τ x = 0) (hτ1 : ∀ x ∈ frontier Δ', τ x = 1)
    (hΦ0 : ∀ y : M, Φ y 0 = y)
    (hΦ1 : ∀ z ∈ frontier D.domain, Φ (P.piecewise (h ∘ D) D z) 1 ∈ BdM)
    (hΦfix : ∀ y ∈ BdM, ∀ s : ℝ, Φ y s = y)
    (hΦmem : ∀ z ∈ frontier D.domain, ∀ s : ℝ,
      Φ (P.piecewise (h ∘ D) D z) s ∈ BdM → P.piecewise (h ∘ D) D z ∈ BdM ∨ s = 1)
    (hann : IsPLOn 2 3 (fun x => Φ (P.piecewise (h ∘ D) D (ρ x)) (τ x))
      (Δ' \ interior D.domain)) :
    ∃ G : SingularTwoCell M, G.domain = Δ' ∧
      EqOn G (P.piecewise (h ∘ D) D) D.domain ∧
      Set.range G.boundary ⊆ BdM ∧
      G '' G.domain ∩ BdM = Set.range G.boundary := by
  obtain ⟨G, hGdomeq, hGdisk, hGann⟩ :=
    exists_singularTwoCell_of_boundarySweep hgpl hΔ'ball (hsubint.trans interior_subset)
      hρid hτ0 hΦ0 hann
  have hGsub : D.domain ⊆ interior G.domain := by rw [hGdomeq]; exact hsubint
  have hGannG : ∀ x ∈ G.domain \ D.domain, G x = Φ (P.piecewise (h ∘ D) D (ρ x)) (τ x) := by
    rw [hGdomeq]
    exact hGann
  have hρfrG : MapsTo ρ (G.domain \ D.domain) (frontier D.domain) := by
    rw [hGdomeq]; exact hρfr
  have hρsurjG : frontier D.domain ⊆ ρ '' frontier G.domain := by
    rw [hGdomeq]; exact hρsurj
  have hτ1G : ∀ x ∈ frontier G.domain, τ x = 1 := by rw [hGdomeq]; exact hτ1
  have houter : Set.range G.boundary ⊆ BdM :=
    range_boundary_subset_boundary_of_boundarySweep hGsub hρfrG hτ1G hGannG hΦ1
  have hannulus : G '' (G.domain \ D.domain) ∩ BdM ⊆ Set.range G.boundary :=
    image_sdiff_inter_boundary_subset_of_boundarySweep hGsub hρfrG hρsurjG hτ1G hGannG hΦfix hΦmem
  have hseam : P.piecewise (h ∘ D) D '' frontier D.domain ∩ BdM ⊆ Set.range G.boundary :=
    image_frontier_inter_boundary_subset_of_boundarySweep hGsub hρsurjG hτ1G hGannG hΦfix
  exact ⟨G, hGdomeq, fun x hx => hGdisk x hx, houter,
    image_inter_boundary_of_collarExtension hbdpre hDN hrefl (fun x hx => hGdisk x hx)
      houter hannulus hseam⟩

open Classical in
theorem exists_collarExtension_image_inter_boundary_of_boundarySweep
    {D : SingularTwoCell M} {BdM N : Set M} {h : M → M}
    {P : Set (EuclideanSpace ℝ (Fin 2))} {Φ : M → ℝ → M}
    (hbdpre : D.domain ∩ D ⁻¹' BdM ⊆ frontier D.domain)
    (hDN : MapsTo D D.domain N)
    (hrefl : ∀ x ∈ N, h x ∈ BdM → x ∈ BdM)
    (hgpl : IsPLOn 2 3 (P.piecewise (h ∘ D) D) D.domain)
    (hΦ0 : ∀ y : M, Φ y 0 = y)
    (hΦ1 : ∀ z ∈ frontier D.domain, Φ (P.piecewise (h ∘ D) D z) 1 ∈ BdM)
    (hΦfix : ∀ y ∈ BdM, ∀ s : ℝ, Φ y s = y)
    (hΦmem : ∀ z ∈ frontier D.domain, ∀ s : ℝ,
      Φ (P.piecewise (h ∘ D) D z) s ∈ BdM → P.piecewise (h ∘ D) D z ∈ BdM ∨ s = 1)
    (hann : ∀ (Δ' : Set (EuclideanSpace ℝ (Fin 2)))
      (ρ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (τ : EuclideanSpace ℝ (Fin 2) → ℝ),
      IsPLBall 2 Δ' → D.domain ⊆ interior Δ' →
      IsPiecewiseAffineOn ρ Δ' → IsPiecewiseAffineOn τ Δ' →
      MapsTo ρ Δ' D.domain → (∀ x ∈ D.domain, ρ x = x) →
      MapsTo ρ (Δ' \ D.domain) (frontier D.domain) →
      frontier D.domain ⊆ ρ '' frontier Δ' →
      (∀ x ∈ D.domain, τ x = 0) → (∀ x ∈ frontier Δ', τ x = 1) →
      IsPLOn 2 3 (fun x => Φ (P.piecewise (h ∘ D) D (ρ x)) (τ x)) (Δ' \ interior D.domain)) :
    ∃ G : SingularTwoCell M, D.domain ⊆ G.domain ∧
      EqOn G (P.piecewise (h ∘ D) D) D.domain ∧
      Set.range G.boundary ⊆ BdM ∧
      G '' G.domain ∩ BdM = Set.range G.boundary := by
  obtain ⟨Δ', ρ, τ, hΔ'ball, hsubint, hρpl, hτpl, hρmaps, hρid, hρfr, hρsurj, hτ0, hτ1, -⟩ :=
    exists_exteriorCollapse_of_isPLBall_two D.isPLBall_domain
  have hρid' : ∀ x ∈ D.domain, ρ x = x := fun x hx => hρid hx
  have hτ0' : ∀ x ∈ D.domain, τ x = 0 := fun x hx => by simpa using hτ0 hx
  have hτ1' : ∀ x ∈ frontier Δ', τ x = 1 := fun x hx => by simpa using hτ1 hx
  obtain ⟨G, hGdomeq, hGdisk, houter, himage⟩ :=
    exists_collarExtension_image_inter_boundary_of_exteriorCollapse hbdpre hDN hrefl hgpl
      hΔ'ball hsubint hρid' hρfr hρsurj hτ0' hτ1' hΦ0 hΦ1 hΦfix hΦmem
      (hann Δ' ρ τ hΔ'ball hsubint hρpl hτpl hρmaps hρid' hρfr hρsurj hτ0' hτ1')
  exact ⟨G, by rw [hGdomeq]; exact hsubint.trans interior_subset, hGdisk, houter, himage⟩

end DifferentialGeometry.Topology.PiecewiseLinear

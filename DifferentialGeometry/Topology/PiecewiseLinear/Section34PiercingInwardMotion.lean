import DifferentialGeometry.Topology.PiecewiseLinear.Section34ContactSupport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetTubeMotion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ProtectedCellMotion

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


theorem exists_section34_piercing_inward_motion
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ (O : Set M₂) (ψ : M₂ ≃ₜ M₂), IsOpen O ∧ IsCompact (closure O) ∧
      closure O ⊆ interior (Sp e) ∩ interior (Q (ends e).1) ∩
        interior (Q (ends e).2) ∧
      Disjoint (closure O) (G (ends e).1 '' CpBd (ends e).1) ∧
      (∀ d, d ≠ e → ((ends e).2 = (ends d).1 ∨ (ends e).2 = (ends d).2) →
        Disjoint (closure O) (G (ends e).2 '' Sn d)) ∧
      Disjoint (closure O) (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) ∧
      EqOn ψ id Oᶜ ∧ IsPLOn 3 3 ψ (interior (G (ends e).1 '' Cc (ends e).1)) ∧
      ψ '' (G (ends e).1 '' Cp (ends e).1) = G (ends e).1 '' Cp (ends e).1 ∧
      MapsTo ψ (Tp e) (Tp e) ∧
      MapsTo ψ (frontier (Tp e) ∩ G (ends e).2 '' Bb e) (interior (Tp e)) ∧
      ∀ x ∈ Tp e, ψ x ∈ frontier (Tp e) → ψ x = x := by
  have hZ : IsCompact (frontier (Tp e) ∩ G (ends e).2 '' Bb e) :=
    ((section34_piercing_annuli hprep hpack e).2.isCompact).inter_left isClosed_frontier
  obtain ⟨O, hO, hOc, hZO, hOsub, hOfirst, hOforeign, hOrim⟩ :=
    exists_section34_contact_support hprep hpack e
  obtain ⟨P, u, _, _, hP, hu, hCc, hN, -⟩ := exists_section34_inner_tube_bicollar hprep e
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, htor, hSnCc, -⟩ := hprep
  obtain ⟨hG, -, -, htube, -, -, -, -, -, -, hGp, -⟩ := hpack
  have hNP : Tn e ⊆ interior (u '' P) := by
    rw [← hCc]
    exact (htor e).1.trans (interior_mono (hSnCc e _ (Or.inl rfl)))
  obtain ⟨A, hAfin, hAspace, hA⟩ :=
    hu.exists_simplicialComplex_invFunOn_image hN (hNP.trans interior_subset)
  let _ : Finite A.faces := hAfin.to_subtype
  have hAP : A.space ⊆ interior P := by
    rw [hAspace]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hu.image_interior.symm.subset (hNP hy)
    rw [hu.injOn.leftInvOn_invFunOn (interior_subset hx)]
    exact hx
  have hback : u '' A.space = Tn e := by
    rw [hAspace, image_image]
    exact (image_congr fun x hx => hu.injOn.bijOn_image.invOn_invFunOn.2
      (interior_subset (hNP hx))).trans (image_id' _)
  let v := G (ends e).1 ∘ u
  have hv : IsPLHomeomorphInto 3 v P := hu.comp_of_image_eq (hCc ▸ hG (ends e).1)
  have hvP : v '' P = G (ends e).1 '' Cc (ends e).1 := by
    rw [hCc, ← image_comp]
  have hvA : v '' A.space = Tp e := by
    change (G (ends e).1 ∘ u) '' A.space = Tp e
    rw [image_comp, hback, ← (htube e).2]
  have hSpP : Sp e ⊆ v '' P := by
    rw [(htube e).1, hvP]
    exact image_mono (hSnCc e _ (Or.inl rfl))
  have hOP : closure O ⊆ interior (v '' P) :=
    (hOsub.trans (inter_subset_left.trans inter_subset_left)).trans (interior_mono hSpP)
  obtain ⟨ψ, hfix, hψpl, hmap, hpush, hboundary⟩ :=
    hv.exists_target_inward_motion hP hA hAP hZ (hvA.symm ▸ inter_subset_left)
      hO hOc hZO hOP
  rw [hvA] at hmap hpush hboundary
  rw [hvP] at hψpl
  have hfirst := ((hCp (ends e).1).image (hGp (ends e).1)).image_eq_of_supported_off_boundary
    ψ isClosed_closure hOfirst (hfix.mono (compl_subset_compl.mpr subset_closure))
  exact ⟨O, ψ, hO, hOc, hOsub, hOfirst, hOforeign, hOrim, hfix, hψpl, hfirst,
    hmap, hpush, hboundary⟩

end DifferentialGeometry.Topology.PiecewiseLinear

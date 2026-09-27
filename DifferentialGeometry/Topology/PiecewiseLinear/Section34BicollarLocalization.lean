import DifferentialGeometry.Topology.PiecewiseLinear.AmbientExtension
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BicollarInwardMove

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_bicollar_protected_base {B W Z O : Set E} {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (B ×ˢ Icc (-1 : ℝ) 1) W) (hB : IsPolyhedron B)
    (hbottom : ∀ x ∈ B, ρ (x, 0) = x) (hZ : IsCompact Z)
    (hO : IsOpen O) (hZO : Z ⊆ O) :
    ∃ (A : Set E) (δ : ℝ), IsPolyhedron A ∧ A ⊆ B ∧ Disjoint A Z ∧
      0 < δ ∧ δ ≤ 1 ∧ ∀ x ∈ B \ A, ∀ t ∈ Icc (-δ) δ, ρ (x, t) ∈ O := by
  obtain ⟨D, hD, hBD, hDZ⟩ :=
    exists_isPolyhedron_neighborhood (hB.isCompact.diff hO) hZ.isClosed.isOpen_compl
      fun x hx hxZ => hx.2 (hZO hxZ)
  let A := B ∩ D
  let C := B \ interior D
  have hCc : IsCompact C := hB.isCompact.diff isOpen_interior
  have hCO : C ⊆ O := by
    intro x hx
    by_contra hxO
    exact hx.2 (hBD ⟨hx.1, hxO⟩)
  obtain ⟨V, hVopen, hV⟩ :=
    continuousOn_iff'.mp hρ.isPiecewiseAffineOn.continuousOn O hO
  let Λ := (C ×ˢ Icc (-1 : ℝ) 1) \ V
  have hΛc : IsCompact Λ := (hCc.prod isCompact_Icc).diff hVopen
  have hΛpos : ∀ z ∈ Λ, 0 < |z.2| := by
    intro z hz
    apply abs_pos.mpr
    intro ht
    have hzO : ρ z ∈ O := by
      rw [show z = (z.1, 0) from Prod.ext rfl ht, hbottom _ hz.1.1.1]
      exact hCO hz.1.1
    have hmem : z ∈ ρ ⁻¹' O ∩ (B ×ˢ Icc (-1 : ℝ) 1) :=
      ⟨hzO, hz.1.1.1, hz.1.2⟩
    rw [hV] at hmem
    exact hz.2 hmem.1
  obtain ⟨r, hr, hrle⟩ : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Λ, r ≤ |z.2| := by
    by_cases hne : Λ.Nonempty
    · obtain ⟨z, hz, hmin⟩ := hΛc.exists_isMinOn hne continuous_snd.abs.continuousOn
      exact ⟨|z.2|, hΛpos z hz, fun y hy => hmin hy⟩
    · exact ⟨1, zero_lt_one, fun z hz => False.elim (hne ⟨z, hz⟩)⟩
  let δ := min (r / 2) 1
  have hδ : 0 < δ := lt_min (half_pos hr) zero_lt_one
  have hδone : δ ≤ 1 := min_le_right _ _
  have hδr : δ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  refine ⟨A, δ, hB.inter hD, inter_subset_left, ?_, hδ, hδone, ?_⟩
  · exact disjoint_left.mpr fun x hx hxZ => hDZ hx.2 hxZ
  · intro x hx t ht
    have hxC : x ∈ C := ⟨hx.1, fun hxD => hx.2 ⟨hx.1, interior_subset hxD⟩⟩
    have htI : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2.trans hδone⟩
    have hnotΛ : (x, t) ∉ Λ := by
      intro hmem
      have hle := hrle (x, t) hmem
      have habs : |t| ≤ δ := abs_le.mpr ht
      exact (not_le_of_gt hδr) (hle.trans habs)
    have hmem : (x, t) ∈ V ∩ (B ×ˢ Icc (-1 : ℝ) 1) :=
      ⟨by
        by_contra hnotV
        exact hnotΛ ⟨⟨hxC, htI⟩, hnotV⟩,
        hx.1, htI⟩
    rw [← hV] at hmem
    exact hmem.1

theorem IsPLHomeomorphOn.exists_bicollar_inward_supported {B W R Z O : Set E}
    {ρ : E × ℝ → E} (hρ : IsPLHomeomorphOn ρ (B ×ˢ Icc (-1 : ℝ) 1) W)
    (hB : IsPolyhedron B) (hW : IsPolyhedron W) (hR : IsPolyhedron R)
    (hBR : Disjoint B R) (hbottom : ∀ x ∈ B, ρ (x, 0) = x)
    (hZ : IsCompact Z) (hZB : Z ⊆ B) (hO : IsOpen O) (hZO : Z ⊆ O) :
    ∃ f : E → E, IsPLHomeomorphOn f (W ∪ R) (W ∪ R) ∧ EqOn f id Oᶜ ∧
      EqOn f id R ∧ MapsTo f (ρ '' (B ×ˢ Icc (0 : ℝ) 1))
        (ρ '' (B ×ˢ Icc (0 : ℝ) 1)) ∧ Disjoint (f '' Z) B ∧
      ∀ x ∈ ρ '' (B ×ˢ Icc (0 : ℝ) 1), f x ∈ B → f x = x := by
  obtain ⟨A, δ, hA, hAB, hAZ, hδ, -, hsmall⟩ :=
    exists_bicollar_protected_base hρ hB hbottom hZ hO hZO
  obtain ⟨f, hf, hfix, hmap, hBiff, hfib, hoff, hhigh⟩ :=
    hρ.exists_relative_bicollar_inward_below hW hR hBR hbottom hA hAB hδ
  let τ := Function.invFunOn ρ (B ×ˢ Icc (-1 : ℝ) 1)
  have hτ : MapsTo τ W (B ×ˢ Icc (-1 : ℝ) 1) := hρ.symm.bijOn.mapsTo
  have hright : RightInvOn τ ρ W := hρ.bijOn.invOn_invFunOn.2
  have hBhalf : B ⊆ ρ '' (B ×ˢ Icc (0 : ℝ) 1) :=
    fun x hx => ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩, hbottom x hx⟩
  refine ⟨f, hf, ?_, fun x hx => hfix (Or.inr hx), hmap, ?_, ?_⟩
  · intro x hx
    by_cases hxW : x ∈ W
    · by_cases hxA : (τ x).1 ∈ A
      · exact hfib ⟨τ x, ⟨hxA, (hτ hxW).2⟩, hright hxW⟩
      · by_cases hxhigh : δ ≤ |(τ x).2|
        · exact hhigh x hxW hxhigh
        · have ht := (abs_lt.mp (lt_of_not_ge hxhigh))
          have hmem := hsmall (τ x).1 ⟨(hτ hxW).1, hxA⟩ (τ x).2 ⟨ht.1.le, ht.2.le⟩
          rw [hright hxW] at hmem
          exact (hx hmem).elim
    · exact hoff hxW
  · apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hfx
    exact disjoint_left.mp hAZ ((hBiff x (hBhalf (hZB hx))).mp hfx) hx
  · intro x hx hfx
    exact hfix (Or.inl ((hBiff x hx).mp hfx))


theorem IsPLHomeomorphOn.exists_bicollar_inward_ambient {B W P Z O : Set E}
    {ρ : E × ℝ → E} (hρ : IsPLHomeomorphOn ρ (B ×ˢ Icc (-1 : ℝ) 1) W)
    (hB : IsPolyhedron B) (hW : IsPolyhedron W) (hP : IsPolyhedron P)
    (hBW : B ⊆ interior W) (hWP : W ⊆ interior P)
    (hbottom : ∀ x ∈ B, ρ (x, 0) = x) (hZ : IsCompact Z) (hZB : Z ⊆ B)
    (hO : IsOpen O) (hZO : Z ⊆ O) (hOP : O ⊆ interior P) :
    ∃ φ : E ≃ₜ E, IsPLHomeomorphOn φ univ univ ∧
      EqOn φ id (O ∩ interior W)ᶜ ∧
      MapsTo φ (ρ '' (B ×ˢ Icc (0 : ℝ) 1)) (ρ '' (B ×ˢ Icc (0 : ℝ) 1)) ∧
      Disjoint (φ '' Z) B ∧
      ∀ x ∈ ρ '' (B ×ˢ Icc (0 : ℝ) 1), φ x ∈ B → φ x = x := by
  let R := closure (P \ W)
  have hR : IsPolyhedron R := hP.closure_sdiff hW
  have hBR : Disjoint B R := by
    apply disjoint_left.mpr
    intro x hxB hxR
    have hxcl : x ∈ closure Wᶜ := closure_mono (sdiff_subset_compl P W) hxR
    rw [closure_compl] at hxcl
    exact hxcl (hBW hxB)
  have hWR : W ∪ R = P := by
    apply Subset.antisymm
    · exact union_subset (hWP.trans interior_subset)
        (closure_minimal sdiff_subset hP.isClosed)
    · intro x hx
      by_cases hxW : x ∈ W
      · exact Or.inl hxW
      · exact Or.inr (subset_closure ⟨hx, hxW⟩)
  obtain ⟨f, hf, hfix, -, hmap, hdis, hboundary⟩ :=
    hρ.exists_bicollar_inward_supported hB hW hR hBR hbottom hZ hZB
      (hO.inter isOpen_interior) (fun x hx => ⟨hZO hx, hBW (hZB hx)⟩)
  rw [hWR] at hf
  have hfront : EqOn f id (frontier P) := by
    intro x hx
    exact hfix fun hmem => hx.2 (hOP hmem.1)
  obtain ⟨φ, hφ, hφf, hφoff⟩ := hf.exists_extension_of_eqOn_frontier hP hfront
  have hhalfP : ρ '' (B ×ˢ Icc (0 : ℝ) 1) ⊆ P := by
    apply (image_subset_iff.mpr fun p hp => hρ.bijOn.mapsTo
      ⟨hp.1, by linarith [hp.2.1], hp.2.2⟩).trans
    exact hWP.trans interior_subset
  have hBP : B ⊆ P := hBW.trans (interior_subset.trans (hWP.trans interior_subset))
  refine ⟨φ, hφ, ?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxP : x ∈ P
    · exact (hφf hxP).trans (hfix hx)
    · exact hφoff hxP
  · intro x hx
    rw [hφf (hhalfP hx)]
    exact hmap hx
  · rw [(hφf.mono (hZB.trans hBP)).image_eq]
    exact hdis
  · intro x hx hφx
    rw [hφf (hhalfP hx)] at hφx ⊢
    exact hboundary x hx hφx


theorem IsPLHomeomorphOn.exists_bicollar_inward_preserving_region {W P T Z O : Set E}
    {ρ : E × ℝ → E} (hρ : IsPLHomeomorphOn ρ (frontier T ×ˢ Icc (-1 : ℝ) 1) W)
    (hB : IsPolyhedron (frontier T)) (hW : IsPolyhedron W) (hP : IsPolyhedron P)
    (hBW : frontier T ⊆ interior W) (hWP : W ⊆ interior P)
    (hbottom : ∀ x ∈ frontier T, ρ (x, 0) = x)
    (hhalf : ρ '' (frontier T ×ˢ Icc (0 : ℝ) 1) = W ∩ T)
    (hZ : IsCompact Z) (hZB : Z ⊆ frontier T) (hO : IsOpen O)
    (hZO : Z ⊆ O) (hOP : O ⊆ interior P) :
    ∃ φ : E ≃ₜ E, IsPLHomeomorphOn φ univ univ ∧
      EqOn φ id (O ∩ interior W)ᶜ ∧ MapsTo φ T T ∧ MapsTo φ Z (interior T) ∧
      ∀ x ∈ T, φ x ∈ frontier T → φ x = x := by
  obtain ⟨φ, hφ, hfix, hmap, hdis, hboundary⟩ :=
    hρ.exists_bicollar_inward_ambient hB hW hP hBW hWP hbottom hZ hZB hO hZO hOP
  rw [hhalf] at hmap hboundary
  have hφT : MapsTo φ T T := by
    intro x hx
    by_cases hxW : x ∈ W
    · exact (hmap ⟨hxW, hx⟩).2
    · rw [hfix (fun hmem => hxW (interior_subset hmem.2))]
      exact hx
  refine ⟨φ, hφ, hfix, hφT, ?_, ?_⟩
  · intro x hx
    have hxhalf : x ∈ ρ '' (frontier T ×ˢ Icc (0 : ℝ) 1) :=
      ⟨(x, 0), ⟨hZB hx, le_rfl, zero_le_one⟩, hbottom x (hZB hx)⟩
    rw [hhalf] at hxhalf
    have hφxT := hφT hxhalf.2
    by_contra hnot
    exact disjoint_left.mp hdis ⟨x, hx, rfl⟩ ⟨subset_closure hφxT, hnot⟩
  · intro x hx hφx
    by_cases hxW : x ∈ W
    · exact hboundary x ⟨hxW, hx⟩ hφx
    · exact hfix (fun hmem => hxW (interior_subset hmem.2))

end DifferentialGeometry.Topology.PiecewiseLinear

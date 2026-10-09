import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnermostCarrierCancellation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.image_of_supported_isPLOn {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {d : ℕ} {S B O K : Set M} (hS : IsPLCellOn d S B) (ψ : M ≃ₜ M)
    (hψ : IsPLOn 3 3 ψ O) (hO : IsOpen O) (hK : IsClosed K) (hKO : K ⊆ O)
    (hfix : EqOn ψ id Kᶜ) : IsPLCellOn d (ψ '' S) (ψ '' B) := by
  obtain ⟨P, r, u, hr, hu, hS, hB⟩ := hS
  have hψu := hu.postcomp_of_supported_isPLOn (isPLCellOn_id_of_isPLBall hr) ψ hψ
    hO hK hKO hfix
  exact ⟨P, r, ψ ∘ u, hr, hψu, by rw [hS, image_comp], by rw [hB, image_comp]⟩

theorem IsPLHomeomorphInto.isPLOn_id_interior_image {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) : IsPLOn 3 3 (id : M → M) (interior (u '' P)) := by
  have hinv := hu.isPLOn_inverse hu.injOn.leftInvOn_invFunOn
  have hcomp := hu.isPLOn.comp_of_mapsTo hinv hu.injOn.bijOn_image.surjOn.mapsTo_invFunOn
  have hid : IsPLOn 3 3 (id : M → M) (u '' P) := hcomp.congr fun x hx =>
    (hu.injOn.bijOn_image.invOn_invFunOn.2 hx).symm
  exact hid.mono_of_isOpen isOpen_interior interior_subset

theorem IsPLHomeomorphInto.exists_single_carrier_trace_of_annular_disks
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
    (hdisk : ∀ j, j ≠ k → ∃ D : Set M, IsPLCellOn 2 D (J j) ∧ D ⊆ Aa) :
    ∃ (K : Set M) (ψ : M ≃ₜ M), IsCompact K ∧ K ⊆ interior (u '' L.space) ∧
      EqOn ψ id Kᶜ ∧ IsPLOn 3 3 ψ (interior (u '' P)) ∧
      Disjoint K (Aa₀ ∪ Aa₁) ∧ Disjoint K (Ba₀ ∪ Ba₁) ∧
      Disjoint K (closure (Bb \ Ba)) ∧ Disjoint K (J k) ∧ Ab ∩ ψ '' Bb = J k := by
  classical
  by_cases hall : ∀ j, j = k
  · refine ⟨∅, Homeomorph.refl M, isCompact_empty, empty_subset _, ?_,
      hu.isPLOn_id_interior_image, by simp, by simp, by simp, by simp, ?_⟩
    · exact fun _ _ => rfl
    · change Ab ∩ id '' Bb = J k
      rw [image_id, htrace]
      apply Subset.antisymm
      · intro x hx
        obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        exact hall j ▸ hj
      · exact subset_iUnion J k
  · obtain ⟨j, hj⟩ := not_forall.mp hall
    obtain ⟨D, hD, hDA⟩ := hdisk j hj
    have hT' := hT.image_of_continuousOn_injOn (hu.continuousOn.mono hLP)
      (hu.injOn.mono hLP)
    have hkne : (J k).Nonempty := by
      obtain ⟨Q, hQ⟩ := hJ k
      exact Q.piece.bijOn.image_eq ▸ hQ.nonempty.image Q.piece.map
    have hBcarry := hBa.carriesFundamentalGroupOnto_first_of_subset
      (hBaT.trans interior_subset) (hJB k) hkne hcarry
    obtain ⟨D', hD', hDBa⟩ := hB.exists_annular_disk_of_disk_in_solid_torus hBa hBaB
      (hBaT.trans interior_subset) (hJ j) (hJB j) (hendsB j) hT' hBcarry hD
      ((hDA.trans hAaT).trans interior_subset)
    obtain ⟨I, hkI, hcard, -, C, K₁, ψ₁, -, -, -, hK₁, hK₁T, hfix₁, hψ₁,
      hArim₁, hBrim₁, hout₁, hkeep₁, -, htrace₁⟩ :=
      hu.exists_innermost_disk_cancellation_retaining_carrier hP L hL hLP hT
        hA hAP hB hAa hAaB hAaT hBa hBaB hBaT hJ hJA hJB hendsA hendsB hdis htrace
        k hcarry ⟨j, D', hD', hDBa⟩
    have hKP₁ := hK₁T.trans (interior_mono (image_mono hLP))
    have hB' := hB.image_of_supported_isPLOn ψ₁ hψ₁ isOpen_interior hK₁.isClosed hKP₁ hfix₁
    have hBa₀ : ψ₁ '' Ba₀ = Ba₀ := by
      exact (image_congr fun x hx => hfix₁
        (disjoint_right.mp hBrim₁ (Or.inl hx))).trans (image_id' _)
    have hBa₁ : ψ₁ '' Ba₁ = Ba₁ := by
      exact (image_congr fun x hx => hfix₁
        (disjoint_right.mp hBrim₁ (Or.inr hx))).trans (image_id' _)
    have hBa' := hBa.image_of_continuousOn_injOn ψ₁.continuous.continuousOn ψ₁.injective.injOn
    rw [hBa₀, hBa₁] at hBa'
    have himageT : ψ₁ '' interior (u '' L.space) = interior (u '' L.space) :=
      image_eq_of_homeomorph_eqOn_compl_of_subset ψ₁ hfix₁ hK₁T
    have hBaT' : ψ₁ '' Ba ⊆ interior (u '' L.space) := himageT ▸ image_mono hBaT
    have hJB' (j : I) : J j.1 ⊆ ψ₁ '' Ba := by
      intro x hx
      exact ⟨x, hJB j.1 hx, hfix₁ (disjoint_right.mp (hkeep₁ j) hx)⟩
    have hdis' : Pairwise fun j l : I => Disjoint (J j.1) (J l.1) :=
      fun j l hjl => hdis (fun heq => hjl (Subtype.ext heq))
    have hdisk' (j : I) (hjk : j ≠ ⟨k, hkI⟩) :
        ∃ D : Set M, IsPLCellOn 2 D (J j.1) ∧ D ⊆ Aa :=
      hdisk j.1 (fun heq => hjk (Subtype.ext heq))
    obtain ⟨K₂, ψ₂, hK₂, hK₂T, hfix₂, hψ₂, hArim₂, hBrim₂, hout₂, hkeep₂, htrace₂⟩ :=
      hu.exists_single_carrier_trace_of_annular_disks hP L hL hLP hT hA hAP hB'
        hAa hAaB hAaT hBa' (image_mono hBaB) hBaT'
        (fun j : I => hJ j.1) (fun j : I => hJA j.1) hJB'
        (fun j : I => hendsA j.1) (fun j : I => hendsB j.1) hdis' htrace₁
        ⟨k, hkI⟩ hcarry hdisk'
    have houtimage : ψ₁ '' Bb \ ψ₁ '' Ba = Bb \ Ba := by
      rw [← image_sdiff ψ₁.injective]
      exact (image_congr fun x hx => hfix₁
        (disjoint_right.mp hout₁ (subset_closure hx))).trans (image_id' _)
    rw [houtimage] at hout₂
    have himageP : ψ₁ '' interior (u '' P) = interior (u '' P) :=
      image_eq_of_homeomorph_eqOn_compl_of_subset ψ₁ hfix₁ hKP₁
    have hcomp : IsPLOn 3 3 (ψ₂ ∘ ψ₁) (interior (u '' P)) :=
      hψ₂.comp_of_mapsTo hψ₁ fun x hx => himageP.subset (mem_image_of_mem ψ₁ hx)
    refine ⟨K₁ ∪ K₂, ψ₁.trans ψ₂, hK₁.union hK₂, union_subset hK₁T hK₂T, ?_, hcomp,
      disjoint_union_left.mpr ⟨hArim₁, hArim₂⟩,
      disjoint_union_left.mpr ⟨hBrim₁, hBrim₂⟩,
      disjoint_union_left.mpr ⟨hout₁, hout₂⟩,
      disjoint_union_left.mpr ⟨hkeep₁ ⟨k, hkI⟩, hkeep₂⟩, ?_⟩
    · intro x hx
      change ψ₂ (ψ₁ x) = x
      calc
        ψ₂ (ψ₁ x) = ψ₂ x := congrArg ψ₂ (hfix₁ (fun hxK => hx (Or.inl hxK)))
        _ = x := hfix₂ (fun hxK => hx (Or.inr hxK))
    · change Ab ∩ (ψ₂ ∘ ψ₁) '' Bb = J k
      rw [image_comp]
      exact htrace₂
termination_by Nat.card ι

end DifferentialGeometry.Topology.PiecewiseLinear

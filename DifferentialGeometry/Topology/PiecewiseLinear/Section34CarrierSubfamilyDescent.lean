import DifferentialGeometry.Topology.PiecewiseLinear.Section34CarrierCancellationDescent
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentMotionComposition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.exists_carrier_subfamily_without_annular_disks
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
    (k : ι) (hcarry : CarriesFundamentalGroupOnto (J k) (u '' L.space)) :
    ∃ I : Set ι, k ∈ I ∧
      (∀ j, CarriesFundamentalGroupOnto (J j) (u '' L.space) → j ∈ I) ∧
      (∀ j : I, ¬ ∃ D : Set M, IsPLCellOn 2 D (J j.1) ∧ D ⊆ Aa) ∧
      ∃ (K : Set M) (ψ : M ≃ₜ M), IsCompact K ∧ K ⊆ interior (u '' L.space) ∧
        EqOn ψ id Kᶜ ∧ IsPLOn 3 3 ψ (interior (u '' P)) ∧
        Disjoint K (Aa₀ ∪ Aa₁) ∧ Disjoint K (Ba₀ ∪ Ba₁) ∧
        Disjoint K (closure (Bb \ Ba)) ∧ (∀ j : I, Disjoint K (J j.1)) ∧
        (∀ j : I, ∀ x ∈ J j.1, ψ =ᶠ[𝓝 x] id) ∧ Ab ∩ ψ '' Bb = ⋃ j : I, J j.1 := by
  classical
  by_cases hall : ∀ j, ¬ ∃ D : Set M, IsPLCellOn 2 D (J j) ∧ D ⊆ Aa
  · refine ⟨univ, mem_univ k, fun _ _ => mem_univ _, fun j => hall j.1,
      ∅, Homeomorph.refl M, isCompact_empty, empty_subset _, fun _ _ => rfl,
      hu.isPLOn_id_interior_image, by simp, by simp, by simp,
      fun _ => by simp, fun _ _ _ => Filter.EventuallyEq.refl _ _, ?_⟩
    change Ab ∩ id '' Bb = _
    simpa only [image_id, iUnion_subtype, mem_univ, iUnion_true] using htrace
  · obtain ⟨j, hj⟩ := not_forall.mp hall
    obtain ⟨D, hD, hDA⟩ := not_not.mp hj
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
    obtain ⟨I, hkI, hcard, hcar₁, C, K₁, ψ₁, -, -, -, hK₁, hK₁T, hfix₁, hψ₁,
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
    obtain ⟨I₂, hk₂, hcar₂, hess₂, K₂, ψ₂, hK₂, hK₂T, hfix₂, hψ₂,
      hArim₂, hBrim₂, hout₂, hkeep₂, -, htrace₂⟩ :=
      hu.exists_carrier_subfamily_without_annular_disks hP L hL hLP hT hA hAP hB'
        hAa hAaB hAaT hBa' (image_mono hBaB) hBaT'
        (fun j : I => hJ j.1) (fun j : I => hJA j.1) hJB'
        (fun j : I => hendsA j.1) (fun j : I => hendsB j.1) hdis' htrace₁
        ⟨k, hkI⟩ hcarry
    have houtimage : ψ₁ '' Bb \ ψ₁ '' Ba = Bb \ Ba := by
      rw [← image_sdiff ψ₁.injective]
      exact (image_congr fun x hx => hfix₁
        (disjoint_right.mp hout₁ (subset_closure hx))).trans (image_id' _)
    rw [houtimage] at hout₂
    have hZ₁ := disjoint_union_right.mpr
      ⟨disjoint_union_right.mpr ⟨hArim₁, hBrim₁⟩, hout₁⟩
    have hZ₂ := disjoint_union_right.mpr
      ⟨disjoint_union_right.mpr ⟨hArim₂, hBrim₂⟩, hout₂⟩
    obtain ⟨-, -, hK, hKT, hfix, hPL, -, -, hkeep, hnear, htrace'⟩ :=
      supported_second_trace_motion_comp ψ₁ ψ₂ hK₁ hK₂ hK₁T hK₂T
        (interior_mono (image_mono hLP)) hfix₁ hfix₂ hψ₁ hψ₂ hZ₁ hZ₂
        I I₂ hkeep₁ hkeep₂ htrace₂
    refine ⟨Subtype.val '' I₂, ⟨⟨k, hkI⟩, hk₂, rfl⟩, ?_, ?_,
      K₁ ∪ K₂, ψ₁.trans ψ₂, hK, hKT, hfix, hPL,
      disjoint_union_left.mpr ⟨hArim₁, hArim₂⟩,
      disjoint_union_left.mpr ⟨hBrim₁, hBrim₂⟩,
      disjoint_union_left.mpr ⟨hout₁, hout₂⟩, hkeep, hnear, htrace'⟩
    · intro j hj
      exact ⟨⟨j, hcar₁ j hj⟩, hcar₂ ⟨j, hcar₁ j hj⟩ hj, rfl⟩
    · intro j
      obtain ⟨i, hi, hij⟩ := j.2
      exact hij ▸ hess₂ ⟨i, hi⟩
termination_by Nat.card ι

end DifferentialGeometry.Topology.PiecewiseLinear

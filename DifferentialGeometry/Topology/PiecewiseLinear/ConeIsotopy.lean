import DifferentialGeometry.Topology.PiecewiseLinear.AmbientExtension

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLHomeomorphOn_coneComplex_of_continuous
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] (p : X → E) (hp : Continuous p)
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hL : ∀ t, IsConeBase (p t) L)
    {N : Set E} (hN : IsPolyhedron N)
    (hLN : ∀ t, (coneComplex (hL t)).space \ L.space ⊆ interior N) (t₀ t₁ : X) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧ EqOn h id Nᶜ ∧ h (p t₀) = p t₁ ∧
      ∀ z ∈ L.space, ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        h (p t₀ + s • (z - p t₀)) = p t₁ + s • (z - p t₁) := by
  let R : X → X → Prop := fun t u =>
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧ EqOn h id Nᶜ ∧ h (p t) = p u ∧
      ∀ z ∈ L.space, ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        h (p t + s • (z - p t)) = p u + s • (z - p u)
  have hrefl : ∀ t, R t t := by
    intro t
    refine ⟨Homeomorph.refl E, ?_, fun _ _ => rfl, rfl, fun _ _ _ _ _ => rfl⟩
    refine ⟨bijOn_id univ, isPiecewiseAffineOn_id isOpen_univ, ?_⟩
    exact (isPiecewiseAffineOn_id isOpen_univ).congr fun _ hx =>
      (bijOn_id univ).invOn_invFunOn.1 hx
  have hsymm : ∀ {t u}, R t u → R u t := by
    rintro t u ⟨h, hh, hfix, hpoint, hrad⟩
    refine ⟨h.symm, hh.homeomorph_symm, ?_, ?_, ?_⟩
    · intro x hx
      exact h.injective ((h.apply_symm_apply x).trans (hfix hx).symm)
    · exact h.symm_apply_eq.mpr hpoint.symm
    · intro z hz s hs hs'
      exact h.symm_apply_eq.mpr (hrad z hz s hs hs').symm
  have htrans : ∀ {t u v}, R t u → R u v → R t v := by
    rintro t u v ⟨h, hh, hfix, hpoint, hrad⟩ ⟨g, hg, gfix, gpoint, grad⟩
    refine ⟨h.trans g, hh.trans hg, ?_, ?_, ?_⟩
    · intro x hx
      change g (h x) = x
      rw [hfix hx, id_eq, gfix hx]
      rfl
    · change g (h (p t)) = p v
      rw [hpoint, gpoint]
    · intro z hz s hs hs'
      change g (h (p t + s • (z - p t))) = _
      rw [hrad z hz s hs hs', grad z hz s hs hs']
  have hlocal : ∀ t, ∀ᶠ u in 𝓝 t, R t u := by
    intro t
    have : Finite (coneComplex (hL t)).faces :=
      (coneComplex_faces_finite (hL t) (Set.toFinite L.faces)).to_subtype
    have hstar : openStar (coneComplex (hL t)) (p t) ⊆ interior N := by
      intro x hx
      apply hLN t
      refine ⟨hx.1, fun hxL => ?_⟩
      obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hxL
      exact hx.2 (mem_iUnion₂.mpr ⟨s, ⟨Or.inl hs, (hL t).notMem_face hs⟩, hxs⟩)
    obtain ⟨δ, hδ, hmove⟩ :=
      exists_isPLHomeomorphOn_of_small_vertex_move (coneComplex (hL t)) (p t) hN hstar
    filter_upwards [hp.continuousAt.preimage_mem_nhds (ball_mem_nhds (p t) hδ)] with u hu
    obtain ⟨h, hh, hfix, hmap⟩ := hmove (p u) hu
    refine ⟨h, hh, hfix, ?_, ?_⟩
    · rw [hmap (apex_mem_coneComplex_space (hL t)),
        simplicialMap_coneComplex_apex (hL t) (Function.update_self (p t) (p u) id)]
    · intro z hz s hs hs'
      have hx : p t + s • (z - p t) ∈ (coneComplex (hL t)).space := by
        by_cases hs0 : s = 0
        · simp only [hs0, zero_smul, add_zero]
          exact apex_mem_coneComplex_space (hL t)
        · exact (mem_coneComplex_space_iff (hL t)).mpr (Or.inr ⟨z, hz, s, lt_of_le_of_ne hs (Ne.symm hs0), hs', rfl⟩)
      rw [hmap hx]
      exact simplicialMap_coneComplex_eq_of_mem_space (hL t)
        (Function.update_self (p t) (p u) id)
        (fun _ _ => ⟨AffineMap.id ℝ E, fun _ _ => rfl⟩)
        (fun σ hσ v hv => Function.update_of_ne (ne_of_mem_of_not_mem hv ((hL t).notMem_face hσ)) _ _)
        hz hs hs'
  have hopen : IsOpen {t | R t₀ t} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    filter_upwards [hlocal t] with u hu
    exact htrans ht hu
  have hclosed : IsClosed {t | R t₀ t} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro t ht
    filter_upwards [hlocal t] with u hu
    exact fun htu => ht (htrans htu (hsymm hu))
  have hall : {t | R t₀ t} = univ := (show IsClopen {t | R t₀ t} from ⟨hclosed, hopen⟩).eq_univ ⟨t₀, hrefl t₀⟩
  exact (show t₁ ∈ {t | R t₀ t} by rw [hall]; exact mem_univ t₁)

end DifferentialGeometry.Topology.PiecewiseLinear

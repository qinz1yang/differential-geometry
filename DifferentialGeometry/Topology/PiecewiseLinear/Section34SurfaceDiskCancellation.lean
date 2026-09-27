import DifferentialGeometry.Topology.PiecewiseLinear.Section34SurfaceCoincidentPush
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SurfaceDiskSurgery

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLBall.exists_relative_surface_disk_cancellation
    {C Ω : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsPLBall 3 C)
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite K.faces] [Finite L.faces]
    (h₁ : IsCombinatorialManifold 2 K) (h₂ : IsCombinatorialManifold 2 L)
    (hD : IsPLBall 2 (K.space ∩ C)) (hDC : K.space ∩ C ⊆ frontier C)
    (hcap : closure (frontier C \ K.space) ⊆ L.space)
    (hrest : IsClosed ((K.space \ C) ∩ L.space)) (hΩ : IsOpen Ω) (hCΩ : C ⊆ Ω) :
    ∃ Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn Φ univ univ ∧ EqOn Φ id Ωᶜ ∧
      EqOn Φ id ((K.space \ C) ∩ L.space) ∧ Φ '' K.space ∩ L.space = (K.space \ C) ∩ L.space := by
  let D := K.space ∩ C
  let A := closure (K.space \ C)
  let F := closure (frontier C \ K.space)
  have hclosedC := hC.isPolyhedron.isClosed
  have hAS : A ⊆ K.space := closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have hFC : F ⊆ C := closure_minimal
    (sdiff_subset.trans hclosedC.frontier_subset) hclosedC
  have hAde : A = closure (K.space \ D) := by
    dsimp only [A]
    apply congrArg closure
    ext x
    simp only [D, mem_sdiff, mem_inter_iff]
    tauto
  have hFde : F = closure (frontier C \ D) := by
    dsimp only [F]
    apply congrArg closure
    ext x
    constructor
    · exact fun hx => ⟨hx.1, fun hxD => hx.2 hxD.1⟩
    · exact fun hx => ⟨hx.1, fun hxS => hx.2 ⟨hxS, hclosedC.frontier_subset hx.1⟩⟩
  have hF : IsPLBall 2 F := hFde ▸ hC.isPLSphere_frontier.isPLBall_closure_sdiff hD hDC
  obtain ⟨r, hr⟩ := hD
  have hACF : A ∩ C ⊆ F := by
    intro x hx
    have hxJ : x ∈ r '' stdSimplexBoundary 2 :=
      (h₁.inter_closure_sdiff_eq_image_stdSimplexBoundary K hr inter_subset_left).subset
        ⟨⟨hAS hx.1, hx.2⟩, hAde ▸ hx.1⟩
    have hxF := (hC.isPLSphere_frontier.inter_closure_sdiff_eq_image_stdSimplexBoundary
      hr hDC).superset hxJ
    exact hFde.symm ▸ hxF.2
  have hFR : Disjoint F ((K.space \ C) ∩ L.space) :=
    disjoint_left.mpr fun _ hxF hxR => hxR.1.2 (hFC hxF)
  obtain ⟨φ, hφ, hfix, hfixA, himage⟩ :=
    hC.exists_relative_surface_disk_surgery K h₁ ⟨r, hr⟩ hDC hΩ hCΩ
  have hφK := hφ.restrict (isPolyhedron_space K) (subset_univ _)
  have hpoly := (isPolyhedron_space K).image_of_isPiecewiseAffineOn
    hφK.isPiecewiseAffineOn hφK.bijOn.injOn
  obtain ⟨N, hNfin, hNspace⟩ := hpoly.exists_simplicialComplex
  let _ : Finite N.faces := hNfin.to_subtype
  have hφKN : IsPLHomeomorphOn φ K.space N.space := hNspace.symm ▸ hφK
  have hnew := h₁.of_isPLHomeomorphOn hφKN
  have hFnew : F ⊆ φ '' K.space := himage.symm ▸ subset_union_right
  have htrace : (φ '' K.space) ∩ L.space ⊆ F ∪ ((K.space \ C) ∩ L.space) := by
    rw [himage]
    rintro x ⟨hxA | hxF, hx₂⟩
    · by_cases hxC : x ∈ C
      · exact Or.inl (hACF ⟨hxA, hxC⟩)
      · exact Or.inr ⟨⟨hAS hxA, hxC⟩, hx₂⟩
    · exact Or.inl hxF
  obtain ⟨ψ, hψ, hψfix, hψrest, -, hψtrace⟩ :=
    hnew.exists_relative_push_of_coincident_disk N L h₂ hF (hNspace.symm ▸ hFnew)
      hcap hrest hFR (by rwa [hNspace]) hΩ (hFC.trans hCΩ)
  rw [hNspace] at hψtrace
  refine ⟨ψ ∘ φ, hφ.trans hψ, ?_, ?_, ?_⟩
  · intro x hx
    change ψ (φ x) = x
    rw [hfix hx]
    exact hψfix hx
  · intro x hx
    change ψ (φ x) = x
    rw [hfixA (subset_closure hx.1)]
    exact hψrest hx
  · rw [image_comp, hψtrace, himage]
    ext x
    constructor
    · rintro ⟨⟨hxA | hxF, hxnotF⟩, hx₂⟩
      · exact ⟨⟨hAS hxA, fun hxC => hxnotF (hACF ⟨hxA, hxC⟩)⟩, hx₂⟩
      · exact (hxnotF hxF).elim
    · rintro ⟨⟨hxS, hxC⟩, hx₂⟩
      exact ⟨⟨Or.inl (subset_closure ⟨hxS, hxC⟩), fun hxF => hxC (hFC hxF)⟩, hx₂⟩

theorem IsPLBall.exists_relative_surface_disk_cancellation_fixed_near_trace
    {C Ω : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsPLBall 3 C)
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite K.faces] [Finite L.faces]
    (h₁ : IsCombinatorialManifold 2 K) (h₂ : IsCombinatorialManifold 2 L)
    (hD : IsPLBall 2 (K.space ∩ C)) (hDC : K.space ∩ C ⊆ frontier C)
    (hcap : closure (frontier C \ K.space) ⊆ L.space)
    (hrest : IsClosed ((K.space \ C) ∩ L.space)) (hΩ : IsOpen Ω) (hCΩ : C ⊆ Ω) :
    ∃ (O : Set (EuclideanSpace ℝ (Fin 3)))
      (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
      IsOpen O ∧ C ⊆ O ∧ closure O ⊆ Ω ∧
      Disjoint (closure O) ((K.space \ C) ∩ L.space) ∧
      IsPLHomeomorphOn Φ univ univ ∧ EqOn Φ id Oᶜ ∧
      (∀ x ∈ (K.space \ C) ∩ L.space, Φ =ᶠ[𝓝 x] id) ∧
      Φ '' K.space ∩ L.space = (K.space \ C) ∩ L.space := by
  have hCV : C ⊆ Ω \ ((K.space \ C) ∩ L.space) :=
    fun _ hx => ⟨hCΩ hx, fun hxR => hxR.1.2 hx⟩
  obtain ⟨O, hO, hCO, hOV⟩ := hC.isPolyhedron.isCompact.exists_isOpen_closure_subset
    ((hΩ.sdiff hrest).mem_nhdsSet.mpr hCV)
  obtain ⟨Φ, hΦ, hfix, -, htrace⟩ := hC.exists_relative_surface_disk_cancellation
    K L h₁ h₂ hD hDC hcap hrest hO hCO
  have hdis : Disjoint (closure O) ((K.space \ C) ∩ L.space) :=
    disjoint_left.mpr fun _ hx hxR => (hOV hx).2 hxR
  refine ⟨O, Φ, hO, hCO, hOV.trans sdiff_subset, hdis, hΦ, hfix, ?_, htrace⟩
  intro x hx
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds
    (disjoint_right.mp hdis hx)] with y hy
  exact hfix (fun hyO => hy (subset_closure hyO))

theorem IsPLBall.exists_relative_second_surface_disk_cancellation
    {C Ω : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsPLBall 3 C)
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite K.faces] [Finite L.faces]
    (h₁ : IsCombinatorialManifold 2 K) (h₂ : IsCombinatorialManifold 2 L)
    (hD : IsPLBall 2 (K.space ∩ C)) (hDC : K.space ∩ C ⊆ frontier C)
    (hcap : closure (frontier C \ K.space) ⊆ L.space)
    (hrest : IsClosed ((K.space \ C) ∩ L.space)) (hΩ : IsOpen Ω) (hCΩ : C ⊆ Ω) :
    ∃ (O : Set (EuclideanSpace ℝ (Fin 3)))
      (ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
      IsOpen O ∧ C ⊆ O ∧ closure O ⊆ Ω ∧
      Disjoint (closure O) ((K.space \ C) ∩ L.space) ∧
      IsPLHomeomorphOn ψ univ univ ∧ EqOn ψ id Oᶜ ∧
      (∀ x ∈ (K.space \ C) ∩ L.space, ψ =ᶠ[𝓝 x] id) ∧
      K.space ∩ ψ '' L.space = (K.space \ C) ∩ L.space := by
  obtain ⟨O, Φ, hO, hCO, hOΩ, hdis, hΦ, hfix, hgerm, htrace⟩ :=
    hC.exists_relative_surface_disk_cancellation_fixed_near_trace
      K L h₁ h₂ hD hDC hcap hrest hΩ hCΩ
  let ψ := Function.invFunOn Φ univ
  have hleft : Function.LeftInverse ψ Φ := fun x => hΦ.bijOn.invOn_invFunOn.1 (mem_univ x)
  have hright : Function.RightInverse ψ Φ := fun x => hΦ.bijOn.invOn_invFunOn.2 (mem_univ x)
  have hfix' {x : EuclideanSpace ℝ (Fin 3)} (hx : Φ x = x) : ψ x = x := by
    exact (congrArg ψ hx.symm).trans (hleft x)
  refine ⟨O, ψ, hO, hCO, hOΩ, hdis, hΦ.symm, fun _ hx => hfix' (hfix hx), ?_, ?_⟩
  · intro x hx
    exact (hgerm x hx).mono fun _ hy => hfix' hy
  · ext x
    constructor
    · rintro ⟨hx₁, y, hy₂, hyx⟩
      have hx₂ : Φ x ∈ L.space := by rw [← hyx, hright]; exact hy₂
      have hxR := htrace.subset ⟨⟨x, hx₁, rfl⟩, hx₂⟩
      have heq : Φ x = x := hΦ.bijOn.injOn (mem_univ (Φ x)) (mem_univ x)
        ((hgerm (Φ x) hxR).self_of_nhds)
      exact heq ▸ hxR
    · intro hx
      exact ⟨hx.1.1, x, hx.2, hfix' (hgerm x hx).self_of_nhds⟩

end DifferentialGeometry.Topology.PiecewiseLinear

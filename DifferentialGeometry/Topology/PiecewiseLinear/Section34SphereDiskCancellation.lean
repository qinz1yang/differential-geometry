import DifferentialGeometry.Topology.PiecewiseLinear.Section34SphereCoincidentPush
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RelativeSphereSurgery

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLSphere.inter_eq_disk_of_frontier_inter_subset
    {S C F : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPLSphere 2 S) (hF : IsPLBall 2 F)
    (hFS : F ⊆ S) (hFC : F ⊆ C) (hfront : frontier C ∩ S ⊆ F)
    (houtside : (S \ C).Nonempty) : S ∩ C = F := by
  have hconn := (hS.isConnected_sdiff_of_isPLBall_two hF hFS).isPreconnected
  have havoid : Disjoint (S \ F) (frontier Cᶜ) := by
    rw [frontier_compl]
    exact disjoint_left.mpr fun _ hx hxC => hx.2 (hfront ⟨hxC, hx.1⟩)
  obtain ⟨z, hzS, hzC⟩ := houtside
  have hsub : S \ F ⊆ Cᶜ := IsPreconnected.subset_of_disjoint_frontier hconn
    ⟨z, ⟨hzS, fun hzF => hzC (hFC hzF)⟩, hzC⟩ havoid
  apply Subset.antisymm
  · intro x hx
    by_contra hxF
    exact hsub ⟨hx.1, hxF⟩ hx.2
  · exact subset_inter hFS hFC

theorem IsPLBall.exists_relative_sphere_disk_cancellation
    {S₁ S₂ C Ω : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsPLBall 3 C)
    (h₁ : IsPLSphere 2 S₁) (h₂ : IsPLSphere 2 S₂)
    (hD : IsPLBall 2 (S₁ ∩ C)) (hDC : S₁ ∩ C ⊆ frontier C)
    (hcap : closure (frontier C \ S₁) ⊆ S₂)
    (hrest : IsClosed ((S₁ \ C) ∩ S₂)) (hΩ : IsOpen Ω) (hCΩ : C ⊆ Ω) :
    ∃ Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn Φ univ univ ∧ EqOn Φ id Ωᶜ ∧
      EqOn Φ id ((S₁ \ C) ∩ S₂) ∧ Φ '' S₁ ∩ S₂ = (S₁ \ C) ∩ S₂ := by
  let D := S₁ ∩ C
  let A := closure (S₁ \ C)
  let F := closure (frontier C \ S₁)
  have hclosedC := hC.isPolyhedron.isClosed
  have hAS : A ⊆ S₁ := closure_minimal sdiff_subset h₁.isPolyhedron.isClosed
  have hFC : F ⊆ C := closure_minimal
    (sdiff_subset.trans hclosedC.frontier_subset) hclosedC
  have hAde : A = closure (S₁ \ D) := by
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
      (h₁.inter_closure_sdiff_eq_image_stdSimplexBoundary hr inter_subset_left).subset
        ⟨⟨hAS hx.1, hx.2⟩, hAde ▸ hx.1⟩
    have hxF := (hC.isPLSphere_frontier.inter_closure_sdiff_eq_image_stdSimplexBoundary
      hr hDC).superset hxJ
    exact hFde.symm ▸ hxF.2
  have hFR : Disjoint F ((S₁ \ C) ∩ S₂) :=
    disjoint_left.mpr fun _ hxF hxR => hxR.1.2 (hFC hxF)
  obtain ⟨φ, hφ, hfix, hfixA, himage⟩ :=
    hC.exists_relative_sphere_surgery h₁ ⟨r, hr⟩ hDC hΩ hCΩ
  have hnew : IsPLSphere 2 (φ '' S₁) :=
    h₁.of_isPLHomeomorphOn (hφ.restrict h₁.isPolyhedron (subset_univ _))
  have hFnew : F ⊆ φ '' S₁ := himage.symm ▸ subset_union_right
  have htrace : (φ '' S₁) ∩ S₂ ⊆ F ∪ ((S₁ \ C) ∩ S₂) := by
    rw [himage]
    rintro x ⟨hxA | hxF, hx₂⟩
    · by_cases hxC : x ∈ C
      · exact Or.inl (hACF ⟨hxA, hxC⟩)
      · exact Or.inr ⟨⟨hAS hxA, hxC⟩, hx₂⟩
    · exact Or.inl hxF
  obtain ⟨ψ, hψ, hψfix, hψrest, -, hψtrace⟩ :=
    hnew.exists_relative_push_of_coincident_disk h₂ hF hFnew hcap hrest hFR htrace hΩ
      (hFC.trans hCΩ)
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

theorem IsPLBall.exists_relative_sphere_disk_cancellation_fixed_near_trace
    {S₁ S₂ C Ω : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsPLBall 3 C)
    (h₁ : IsPLSphere 2 S₁) (h₂ : IsPLSphere 2 S₂)
    (hD : IsPLBall 2 (S₁ ∩ C)) (hDC : S₁ ∩ C ⊆ frontier C)
    (hcap : closure (frontier C \ S₁) ⊆ S₂)
    (hrest : IsClosed ((S₁ \ C) ∩ S₂)) (hΩ : IsOpen Ω) (hCΩ : C ⊆ Ω) :
    ∃ (O : Set (EuclideanSpace ℝ (Fin 3)))
      (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
      IsOpen O ∧ C ⊆ O ∧ closure O ⊆ Ω ∧
      Disjoint (closure O) ((S₁ \ C) ∩ S₂) ∧
      IsPLHomeomorphOn Φ univ univ ∧ EqOn Φ id Oᶜ ∧
      (∀ x ∈ (S₁ \ C) ∩ S₂, Φ =ᶠ[𝓝 x] id) ∧
      Φ '' S₁ ∩ S₂ = (S₁ \ C) ∩ S₂ := by
  have hCV : C ⊆ Ω \ ((S₁ \ C) ∩ S₂) :=
    fun _ hx => ⟨hCΩ hx, fun hxR => hxR.1.2 hx⟩
  obtain ⟨O, hO, hCO, hOV⟩ := hC.isPolyhedron.isCompact.exists_isOpen_closure_subset
    ((hΩ.sdiff hrest).mem_nhdsSet.mpr hCV)
  obtain ⟨Φ, hΦ, hfix, -, htrace⟩ := hC.exists_relative_sphere_disk_cancellation
    h₁ h₂ hD hDC hcap hrest hO hCO
  have hdis : Disjoint (closure O) ((S₁ \ C) ∩ S₂) :=
    disjoint_left.mpr fun _ hx hxR => (hOV hx).2 hxR
  refine ⟨O, Φ, hO, hCO, hOV.trans sdiff_subset, hdis, hΦ, hfix, ?_, htrace⟩
  intro x hx
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds
    (disjoint_right.mp hdis hx)] with y hy
  exact hfix (fun hyO => hy (subset_closure hyO))

theorem IsPLBall.exists_relative_second_sphere_disk_cancellation
    {S₁ S₂ C Ω : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsPLBall 3 C)
    (h₁ : IsPLSphere 2 S₁) (h₂ : IsPLSphere 2 S₂)
    (hD : IsPLBall 2 (S₁ ∩ C)) (hDC : S₁ ∩ C ⊆ frontier C)
    (hcap : closure (frontier C \ S₁) ⊆ S₂)
    (hrest : IsClosed ((S₁ \ C) ∩ S₂)) (hΩ : IsOpen Ω) (hCΩ : C ⊆ Ω) :
    ∃ (O : Set (EuclideanSpace ℝ (Fin 3)))
      (ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
      IsOpen O ∧ C ⊆ O ∧ closure O ⊆ Ω ∧
      Disjoint (closure O) ((S₁ \ C) ∩ S₂) ∧
      IsPLHomeomorphOn ψ univ univ ∧ EqOn ψ id Oᶜ ∧
      (∀ x ∈ (S₁ \ C) ∩ S₂, ψ =ᶠ[𝓝 x] id) ∧
      S₁ ∩ ψ '' S₂ = (S₁ \ C) ∩ S₂ := by
  obtain ⟨O, Φ, hO, hCO, hOΩ, hdis, hΦ, hfix, hgerm, htrace⟩ :=
    hC.exists_relative_sphere_disk_cancellation_fixed_near_trace h₁ h₂ hD hDC hcap hrest hΩ hCΩ
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
      have hx₂ : Φ x ∈ S₂ := by rw [← hyx, hright]; exact hy₂
      have hxR := htrace.subset ⟨⟨x, hx₁, rfl⟩, hx₂⟩
      have heq : Φ x = x := hΦ.bijOn.injOn (mem_univ (Φ x)) (mem_univ x)
        ((hgerm (Φ x) hxR).self_of_nhds)
      exact heq ▸ hxR
    · intro hx
      exact ⟨hx.1.1, x, hx.2, hfix' (hgerm x hx).self_of_nhds⟩

end DifferentialGeometry.Topology.PiecewiseLinear

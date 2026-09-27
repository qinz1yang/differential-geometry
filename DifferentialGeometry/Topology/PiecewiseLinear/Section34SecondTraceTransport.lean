import DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelTraceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CapDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SupportedVertexModification

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.invFunOn_second_trace_family
    {M ι : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) {A B : Set M} (hAP : A ⊆ u '' P)
    {Γ : ι → Set M} (hΓ : ∀ i, IsPolyhedralSphere (n := 3) 1 (Γ i))
    (hdis : Pairwise fun i j => Disjoint (Γ i) (Γ j)) (hfull : A ∩ B = ⋃ i, Γ i) :
    (∀ i, IsPLSphere 1 (Function.invFunOn u P '' Γ i)) ∧
      (Pairwise fun i j => Disjoint (Function.invFunOn u P '' Γ i)
        (Function.invFunOn u P '' Γ j)) ∧
      (P ∩ u ⁻¹' B) ∩ (Function.invFunOn u P '' A) =
        ⋃ i, Function.invFunOn u P '' Γ i := by
  let τ := Function.invFunOn u P
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτmap : MapsTo τ (u '' P) P := hu.injOn.bijOn_image.surjOn.mapsTo_invFunOn
  have hΓP (i : ι) : Γ i ⊆ u '' P :=
    (subset_iUnion Γ i).trans (hfull.symm.subset.trans (inter_subset_left.trans hAP))
  refine ⟨fun i => hu.isPLSphere_invFunOn_image (hΓ i) (hΓP i), ?_, ?_⟩
  · intro i j hij
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have heq : y = x := (hright (hΓP j hy)).symm.trans
      ((congrArg u hyx).trans (hright (hΓP i hx)))
    exact disjoint_left.mp (hdis hij) hx (heq ▸ hy)
  · change (P ∩ u ⁻¹' B) ∩ (τ '' A) = ⋃ i, τ '' Γ i
    rw [← image_iUnion, ← hfull]
    ext x
    constructor
    · rintro ⟨⟨hxP, hxB⟩, a, ha, hax⟩
      have hxa : u x = a := hax ▸ hright (hAP ha)
      exact ⟨a, ⟨ha, hxa ▸ hxB⟩, hax⟩
    · rintro ⟨a, ⟨ha, hb⟩, rfl⟩
      refine ⟨⟨hτmap (hAP ha), ?_⟩, a, ha, rfl⟩
      change u (τ a) ∈ B
      rw [hright (hAP ha)]
      exact hb

theorem IsPLHomeomorphInto.exists_second_trace_motion_of_model_motion
    {M ι : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P S : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsPolyhedron P)
    (hS : IsCompact S) (hSP : S ⊆ interior P)
    {A B : Set M} (hAP : A ⊆ u '' P) {Γ : ι → Set M}
    (hfull : A ∩ B = ⋃ i, Γ i) (I : Set ι)
    (H : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3))
    (hH : IsPLHomeomorphOn H univ univ) (hfix : EqOn H id Sᶜ)
    (hkeep : ∀ i : I, Disjoint S (Function.invFunOn u P '' Γ i.1))
    (htrace : H '' (P ∩ u ⁻¹' B) ∩ (Function.invFunOn u P '' A) =
      ⋃ i : I, Function.invFunOn u P '' Γ i.1) :
    ∃ ψ : M ≃ₜ M, IsCompact (u '' S) ∧ EqOn ψ id (u '' S)ᶜ ∧
      IsPLOn 3 3 ψ (interior (u '' P)) ∧
      (∀ i : I, Disjoint (u '' S) (Γ i.1)) ∧
      (∀ i : I, ∀ x ∈ Γ i.1, ψ =ᶠ[𝓝 x] id) ∧ A ∩ ψ '' B = ⋃ i : I, Γ i.1 := by
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hΓP (i : ι) : Γ i ⊆ u '' P :=
    (subset_iUnion Γ i).trans (hfull.symm.subset.trans (inter_subset_left.trans hAP))
  have hback (i : ι) : u '' (τ '' Γ i) = Γ i := by
    rw [image_image]
    exact (image_congr fun x hx => hright (hΓP i hx)).trans (image_id' (Γ i))
  obtain ⟨ψ, hoff, hconj, hψ⟩ := hu.exists_supported_model_motion hP hS hSP H hH hfix
  have hHP : H '' P = P :=
    image_eq_of_homeomorph_eqOn_compl_of_subset H hfix (hSP.trans interior_subset)
  have hK : IsCompact (u '' S) :=
    hS.image_of_continuousOn (hu.continuousOn.mono (hSP.trans interior_subset))
  have hdis (i : I) : Disjoint (u '' S) (Γ i.1) := by
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ hxΓ
    apply disjoint_left.mp (hkeep i) hx
    exact ⟨u x, hxΓ, hleft (interior_subset (hSP hx))⟩
  refine ⟨ψ, hK, hoff, hψ, hdis, ?_, ?_⟩
  · intro i x hx
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds (disjoint_right.mp (hdis i) hx)]
      with y hy
    exact hoff hy
  · rw [hu.inter_image_eq_of_model_conjugacy H ψ hHP hconj hAP, inter_comm,
      htrace, image_iUnion]
    congr 1
    funext i
    exact hback i.1

end DifferentialGeometry.Topology.PiecewiseLinear

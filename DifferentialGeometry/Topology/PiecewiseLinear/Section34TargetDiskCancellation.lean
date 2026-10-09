import DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelDiskFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelBoundaryDisk
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelTraceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PseudoCellCancellation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.exists_relative_second_disk_cancellation {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsPLBall 3 P) {A Ab B Bb C D F J Ω : Set M}
    (hA : IsPLCellOn 3 A Ab) (hAP : A ⊆ u '' P) (hB : IsPLCellOn 3 B Bb)
    (hC : IsPLCellOn 3 C (D ∪ F)) (hD : IsPLCellOn 2 D J) (hF : IsPLCellOn 2 F J)
    (hmeet : Ab ∩ C = F) (htrace : D ∩ Ab = J) (hDB : D ⊆ Bb)
    (hrest : IsClosed ((Ab \ C) ∩ Bb)) (hΩ : IsOpen Ω) (hCΩ : C ⊆ Ω)
    (hΩP : Ω ⊆ interior (u '' P)) :
    ∃ (K : Set M) (ψ : M ≃ₜ M), IsCompact K ∧ K ⊆ Ω ∧ EqOn ψ id Kᶜ ∧
      IsPLOn 3 3 ψ (interior (u '' P)) ∧
      Disjoint K ((Ab \ C) ∩ Bb) ∧
      (∀ x ∈ (Ab \ C) ∩ Bb, ψ =ᶠ[𝓝 x] id) ∧ Ab ∩ ψ '' Bb = (Ab \ C) ∩ Bb := by
  let τ := Function.invFunOn u P
  let S₂ := P ∩ u ⁻¹' Bb
  let R := (Ab \ C) ∩ Bb
  have hCPint : C ⊆ interior (u '' P) := hCΩ.trans hΩP
  have hCP : C ⊆ u '' P := hCPint.trans interior_subset
  have hAbP : Ab ⊆ u '' P := hA.boundary_subset.trans hAP
  have hDP : D ⊆ interior (u '' P) :=
    (subset_union_left.trans hC.boundary_subset).trans hCPint
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτmap : MapsTo τ (u '' P) P := hu.injOn.bijOn_image.surjOn.mapsTo_invFunOn
  have hτi : InjOn τ (u '' P) := by
    intro x hx y hy hxy
    rw [← hright hx, ← hright hy, hxy]
  have hτint : MapsTo τ (interior (u '' P)) (interior P) := by
    intro x hx
    rw [← hu.image_interior] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hleft (interior_subset hy)]
    exact hy
  obtain ⟨hAs, hCs, hFs, hFC, hcap⟩ :=
    hu.invFunOn_disk_filling_data hA hAP hC hCP hD hF hmeet htrace
  obtain ⟨E, Eint, Ebd, p, hpc, hE₂, -, hDE, hEg⟩ :=
    hu.exists_pseudo_cell_boundary_chart hB hD hDB hDP
  have hR : IsCompact R := hA.isCompact.of_isClosed_subset hrest
    (fun _ hx => hA.boundary_subset hx.1.1)
  have hRP : R ⊆ u '' P := fun _ hx => hAbP hx.1.1
  have hτR : IsCompact (τ '' R) := hR.image_of_continuousOn
    ((hu.isPLOn_inverse hleft).continuousOn.mono hRP)
  have hbackR : u '' (τ '' R) = R := by
    rw [image_image]
    exact (image_congr fun x hx => hright (hRP hx)).trans (image_id' R)
  have hRmodel : ((τ '' Ab) \ (τ '' C)) ∩ S₂ = τ '' R := by
    ext x
    constructor
    · rintro ⟨⟨⟨a, ha, hax⟩, hxC⟩, hxP, hxB⟩
      have hua : u x = a := hax ▸ hright (hAbP ha)
      exact ⟨a, ⟨⟨ha, fun haC => hxC ⟨a, haC, hax⟩⟩, hua ▸ hxB⟩, hax⟩
    · rintro ⟨a, ⟨⟨ha, haC⟩, haB⟩, rfl⟩
      refine ⟨⟨⟨a, ha, rfl⟩, ?_⟩, hτmap (hAbP ha), ?_⟩
      · rintro ⟨c, hc, hca⟩
        exact haC ((hτi (hCP hc) (hAbP ha) hca) ▸ hc)
      · change u (τ a) ∈ Bb
        rw [hright (hAbP ha)]
        exact haB
  let V := interior P ∩ u ⁻¹' Ω
  have hV : IsOpen V := (hu.continuousOn.mono interior_subset).isOpen_inter_preimage
    isOpen_interior hΩ
  have hCV : τ '' C ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hτint (hCPint hx), ?_⟩
    change u (τ x) ∈ Ω
    rw [hright (hCP hx)]
    exact hCΩ hx
  have hDE' : closure (frontier (τ '' C) \ (τ '' Ab)) ⊆ Eint \ {p} := by
    rwa [hcap]
  have hEg' : ∀ x ∈ closure (frontier (τ '' C) \ (τ '' Ab)),
      ∀ᶠ y in 𝓝 x, y ∈ E ↔ y ∈ S₂ := by
    rwa [hcap]
  have hRmclosed : IsClosed (((τ '' Ab) \ (τ '' C)) ∩ S₂) := hRmodel ▸ hτR.isClosed
  obtain ⟨O, Φ, -, -, hOV, hdis, hΦ, hfix, -, hcancel⟩ :=
    hCs.exists_relative_second_disk_cancellation_of_pseudo_cell hAs hpc hE₂ hDE' hEg'
      hFs hFC hRmclosed hV hCV
  let φ := ((Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 3))).symm.trans hΦ.homeomorph).trans
    (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 3)))
  have hφ : IsPLHomeomorphOn φ univ univ := hΦ
  have hφfix : EqOn φ id Oᶜ := hfix
  have hOPint : closure O ⊆ interior P := hOV.trans inter_subset_left
  have hOP : closure O ⊆ P := hOPint.trans interior_subset
  have hOcompact := hP.isPolyhedron.isCompact.of_isClosed_subset isClosed_closure hOP
  obtain ⟨ψ, hoff, hconj, hψ⟩ := hu.exists_supported_model_motion hP.isPolyhedron hOcompact hOPint
    φ hφ (hφfix.mono (compl_subset_compl.mpr subset_closure))
  have hφP : φ '' P = P := image_eq_of_homeomorph_eqOn_compl_of_subset φ hφfix
    (subset_closure.trans hOP)
  have hK : IsCompact (u '' closure O) :=
    hOcompact.image_of_continuousOn (hu.continuousOn.mono hOP)
  have hKR : Disjoint (u '' closure O) R := by
    refine disjoint_left.mpr ?_
    rintro x ⟨z, hz, rfl⟩ hxR
    apply disjoint_left.mp hdis hz
    rw [hRmodel]
    exact ⟨u z, hxR, hleft (hOP hz)⟩
  refine ⟨u '' closure O, ψ, hK, ?_, hoff, hψ, hKR, ?_, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    exact (hOV hz).2
  · intro x hx
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds (disjoint_right.mp hKR hx)] with y hy
    exact hoff hy
  · rw [hu.inter_image_eq_of_model_conjugacy φ ψ hφP hconj hAbP]
    change u '' ((τ '' Ab) ∩ Φ '' S₂) = R
    rw [hcancel, hRmodel, hbackR]

end DifferentialGeometry.Topology.PiecewiseLinear

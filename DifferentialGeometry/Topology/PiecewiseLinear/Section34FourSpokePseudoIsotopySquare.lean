import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeSquareWitness
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FourSpokePseudoIsotopy

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_PL_splice_square_pseudoisotopy_of_preserves_spokes
    {u : ℝ × ℝ → ℝ × ℝ} (hu : IsPLHomeomorphOn u spliceSquare spliceSquare)
    (huT : ∀ i, u '' segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) =
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i))
    (huv : ∀ i, u (fourSpokeModelLeaf i) = fourSpokeModelLeaf i) :
    ∃ Φ : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ,
      IsPLHomeomorphOn Φ (spliceSquare ×ˢ Icc (0 : ℝ) 1)
        (spliceSquare ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ spliceSquare, Φ (x, 0) = (x, 0)) ∧
      (∀ x ∈ spliceSquare, Φ (x, 1) = (u x, 1)) ∧
      (∀ i, Φ '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1) =
        segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (0, t) = (0, t)) ∧
      ∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
        Φ (fourSpokeModelLeaf i, t) = (fourSpokeModelLeaf i, t) := by
  let e := fourSpokePlaneEquiv
  have he : IsPLHomeomorphOn e spliceSquare fourSpokeSquare :=
    isPLHomeomorphOn_fourSpokePlaneEquiv isPLBall_spliceSquare.isPolyhedron
  have hei : IsPLHomeomorphOn e.symm fourSpokeSquare spliceSquare := by
    apply he.symm.congr
    intro x hx
    have h := congrArg e.symm (he.bijOn.invOn_invFunOn.2 hx)
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h.symm
  have hback (S : Set (ℝ × ℝ)) : e.symm '' (e '' S) = S := by
    ext x
    simp only [mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, hxy⟩
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hxy ▸ hz
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
  let v := e ∘ u ∘ e.symm
  have hv : IsPLHomeomorphOn v fourSpokeSquare fourSpokeSquare :=
    (hei.trans hu).trans he
  have hvT (i : Fin 4) : v '' fourSpokeArm i = fourSpokeArm i := by
    rw [fourSpokeArm_eq_image]
    change (e ∘ u ∘ e.symm) '' (e '' _) = e '' _
    rw [image_comp, image_comp, hback, huT]
  have hvv (i : Fin 4) : v (fourSpokeLeaf i) = fourSpokeLeaf i := by
    change e (u (e.symm (e (fourSpokeModelLeaf i)))) = e (fourSpokeModelLeaf i)
    rw [e.symm_apply_apply, huv]
  obtain ⟨A₁, A₂, hcut, hv1, hv3⟩ := exists_isCutPair_fourSpokeSquare
  obtain ⟨Ψ, hΨ, hΨ0, hΨ1, hΨT, hΨc, hΨv⟩ :=
    exists_PL_four_spoke_disk_pseudoisotopy isPLBall_fourSpokeSquare isPLBall_fourSpokeArm
      isArcBetween_fourSpokeArm fourSpokeArm_subset fourSpokeArm_inter_frontier
      (fun _ _ h => fourSpokeArm_inter h) hcut hv1 hv3 hv hvT hvv
  have hI : IsPLHomeomorphOn (id : ℝ → ℝ) (Icc 0 1) (Icc 0 1) :=
    isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
  let Φ := Prod.map e.symm id ∘ Ψ ∘ Prod.map e id
  have hΦ : IsPLHomeomorphOn Φ (spliceSquare ×ˢ Icc (0 : ℝ) 1)
      (spliceSquare ×ˢ Icc (0 : ℝ) 1) :=
    ((he.prodMap hI).trans hΨ).trans (hei.prodMap hI)
  refine ⟨Φ, hΦ, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change Prod.map e.symm id (Ψ (e x, 0)) = (x, 0)
    rw [hΨ0 (e x) (he.bijOn.mapsTo hx)]
    simp only [Prod.map_apply, id_eq, ContinuousLinearEquiv.symm_apply_apply]
  · intro x hx
    change Prod.map e.symm id (Ψ (e x, 1)) = (u x, 1)
    rw [hΨ1 (e x) (he.bijOn.mapsTo hx)]
    simp only [Prod.map_apply, id_eq, v, Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  · intro i
    change (Prod.map e.symm id ∘ Ψ ∘ Prod.map e id) '' _ = _
    rw [image_comp, image_comp, prodMap_image_prod, image_id]
    change Prod.map e.symm id '' (Ψ ''
      ((fourSpokePlaneEquiv '' segment ℝ 0 (fourSpokeModelLeaf i)) ×ˢ Icc 0 1)) = _
    rw [← fourSpokeArm_eq_image, hΨT, prodMap_image_prod, image_id, fourSpokeArm_eq_image]
    exact congrArg (· ×ˢ Icc (0 : ℝ) 1) (hback _)
  · intro t ht
    change Prod.map e.symm id (Ψ (fourSpokeCentre, t)) = (0, t)
    rw [hΨc t ht]
    simp only [Prod.map_apply, id_eq, fourSpokeCentre, e,
      ContinuousLinearEquiv.symm_apply_apply]
  · intro i t ht
    change Prod.map e.symm id (Ψ (fourSpokeLeaf i, t)) = (fourSpokeModelLeaf i, t)
    rw [hΨv i t ht]
    simp only [Prod.map_apply, id_eq, fourSpokeLeaf, e,
      ContinuousLinearEquiv.symm_apply_apply]

end DifferentialGeometry.Topology.PiecewiseLinear

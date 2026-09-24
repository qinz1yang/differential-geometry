import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ConnectingCylinderCover
import DifferentialGeometry.Topology.Attachment.TwoEndedCylinder.ClosedCover

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1

universe u v

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {N : ConnectedClosedOrientedManifold.{v} 3}
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment)

theorem exists_outer_caps_cylinder_homeomorph :
    let endMap : S2 ⊕ S2 → S2 × unitInterval :=
      Sum.elim (fun z => (z, 0)) (fun z => (z, 1))
    let attaching : S2 ⊕ S2 → outerPunctured c ⊕ outerPunctured d :=
      Sum.map (outerLeftBoundary c) (outerRightBoundary d a)
    ∃ H : AdjunctionSpace endMap attaching ≃ₜ
        (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier,
      (∀ q, H (adjunctionCell endMap attaching q) = connectingCylinder c d a q) ∧
      (∀ x, H (adjunctionLower (i := endMap) attaching (Sum.inl x)) = outerLeft c d a x) ∧
      (∀ x, H (adjunctionLower (i := endMap) attaching (Sum.inr x)) = outerRight c d a x) ∧
      (∀ q, H.symm (connectingCylinder c d a q) = adjunctionCell endMap attaching q) ∧
      (∀ x, H.symm (outerLeft c d a x) =
        adjunctionLower (i := endMap) attaching (Sum.inl x)) ∧
      ∀ x, H.symm (outerRight c d a x) =
        adjunctionLower (i := endMap) attaching (Sum.inr x) := by
  let f₀ : C(outerPunctured c,
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier) :=
    ⟨outerLeft c d a, (isClosedEmbedding_outerLeft c d a).continuous⟩
  let f₁ : C(outerPunctured d,
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier) :=
    ⟨outerRight c d a, (isClosedEmbedding_outerRight c d a).continuous⟩
  let T : C(S2 × unitInterval,
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier) :=
    ⟨connectingCylinder c d a, continuous_connectingCylinder c d a⟩
  have hcov : range T ∪ (range f₀ ∪ range f₁) = univ :=
    (union_comm _ _).trans (outer_caps_connectingCylinder_cover c d a)
  obtain ⟨H, hT, hL, hR⟩ := exists_adjunction_homeomorph_of_two_cap_cylinder_cover
    (outerLeftBoundary c) (outerRightBoundary d a) f₀ f₁ T
    (isClosedEmbedding_outerLeft c d a) (isClosedEmbedding_outerRight c d a)
    (isClosedEmbedding_connectingCylinder c d a) (disjoint_outer_caps c d a)
    (connectingCylinder_zero c d a) (connectingCylinder_one c d a)
    (fun q x h => (connectingCylinder_eq_outerLeft_iff c d a q x).mp h)
    (fun q x h => (connectingCylinder_eq_outerRight_iff c d a q x).mp h) hcov
  refine ⟨H, hT, hL, hR, ?_, ?_, ?_⟩
  · intro q
    exact H.symm_apply_eq.mpr (hT q).symm
  · intro x
    exact H.symm_apply_eq.mpr (hL x).symm
  · intro x
    exact H.symm_apply_eq.mpr (hR x).symm

theorem contMDiff_connectingCylinder_interior :
    let U : TopologicalSpace.Opens ℝ := ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩
    letI : ChartedSpace ℝ (Ioo (0 : ℝ) 1) := U.instChartedSpace
    ContMDiff ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) ∞
      (fun q : S2 × Ioo (0 : ℝ) 1 =>
        connectingCylinder c d a (q.1, ⟨q.2.val, q.2.property.1.le, q.2.property.2.le⟩)) := by
  let U : TopologicalSpace.Opens ℝ := ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩
  let : ChartedSpace ℝ (Ioo (0 : ℝ) 1) := U.instChartedSpace
  let phi : S2 × Ioo (0 : ℝ) 1 → connectingCylinderDomain := fun q =>
    ⟨(q.1, q.2.val), mem_univ _, by constructor <;> linarith [q.2.property.1, q.2.property.2]⟩
  have hphi : ContMDiff ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) ∞ phi := by
    apply (ContMDiff.subtypeVal_comp_iff connectingCylinderDomain _).mp
    exact contMDiff_fst.prodMk
      ((contMDiff_subtype_val (I := 𝓘(ℝ, ℝ)) (U := U)).comp contMDiff_snd)
  exact (isLocalDiffeomorph_connectingCylinderOpen c d a).contMDiff.comp hphi

variable {P : Type*} [TopologicalSpace P]

theorem exists_homeomorph_of_outer_caps_cylinder_cover
    (f₀ : C(outerPunctured c, P)) (f₁ : C(outerPunctured d, P))
    (T : C(S2 × unitInterval, P))
    (hf₀ : _root_.Topology.IsClosedEmbedding f₀)
    (hf₁ : _root_.Topology.IsClosedEmbedding f₁)
    (hT : _root_.Topology.IsClosedEmbedding T)
    (hdisj : Disjoint (range f₀) (range f₁))
    (hzero : ∀ z, T (z, 0) = f₀ (outerLeftBoundary c z))
    (hone : ∀ z, T (z, 1) = f₁ (outerRightBoundary d a z))
    (hcross₀ : ∀ q x, T q = f₀ x → q.2 = 0 ∧ outerLeftBoundary c q.1 = x)
    (hcross₁ : ∀ q x, T q = f₁ x → q.2 = 1 ∧ outerRightBoundary d a q.1 = x)
    (hcover : range T ∪ (range f₀ ∪ range f₁) = univ) :
    ∃ H : (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier ≃ₜ P,
      (∀ q, H (connectingCylinder c d a q) = T q) ∧
      (∀ x, H (outerLeft c d a x) = f₀ x) ∧
      (∀ x, H (outerRight c d a x) = f₁ x) ∧
      (∀ q, H.symm (T q) = connectingCylinder c d a q) ∧
      (∀ x, H.symm (f₀ x) = outerLeft c d a x) ∧
      ∀ x, H.symm (f₁ x) = outerRight c d a x := by
  obtain ⟨A,hAT,hAL,hAR,hATi,hALi,hARi⟩ := exists_outer_caps_cylinder_homeomorph c d a
  obtain ⟨B,hBT,hBL,hBR⟩ := exists_adjunction_homeomorph_of_two_cap_cylinder_cover
    (outerLeftBoundary c) (outerRightBoundary d a) f₀ f₁ T
    hf₀ hf₁ hT hdisj hzero hone hcross₀ hcross₁ hcover
  let H := A.symm.trans B
  have hHT (q) : H (connectingCylinder c d a q) = T q := by
    change B (A.symm (connectingCylinder c d a q)) = T q
    rw [hATi,hBT]
  have hHL (x) : H (outerLeft c d a x) = f₀ x := by
    change B (A.symm (outerLeft c d a x)) = f₀ x
    rw [hALi,hBL]
  have hHR (x) : H (outerRight c d a x) = f₁ x := by
    change B (A.symm (outerRight c d a x)) = f₁ x
    rw [hARi,hBR]
  exact ⟨H,hHT,hHL,hHR,
    fun q => H.symm_apply_eq.mpr (hHT q).symm,
    fun x => H.symm_apply_eq.mpr (hHL x).symm,
    fun x => H.symm_apply_eq.mpr (hHR x).symm⟩

end DifferentialGeometry.Topology.ConnectedSumQuotient

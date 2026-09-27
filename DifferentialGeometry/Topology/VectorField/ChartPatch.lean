import DifferentialGeometry.Topology.VectorField.OpenPatch
import DifferentialGeometry.Topology.VectorField.Pushforward

set_option autoImplicit false
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.VectorField
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  (c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
  (V : ∀ x : M, TangentSpace I x) (W : E → E)


def patchInCoordinates (x : M) : TangentSpace I x :=
  patchOnOpen ⟨c.source, c.open_source⟩ V
    (fun y => _root_.VectorField.mpullback I 𝓘(ℝ, E) c W y.val) x


theorem patchInCoordinates_of_mem {x : M} (hx : x ∈ c.source) :
    patchInCoordinates c V W x = _root_.VectorField.mpullback I 𝓘(ℝ, E) c W x :=
  patchOnOpen_of_mem _ _ _ hx


theorem patchInCoordinates_of_not_mem {x : M} (hx : x ∉ c.source) :
    patchInCoordinates c V W x = V x :=
  patchOnOpen_of_not_mem _ _ _ hx

theorem mpullback_patchInCoordinates {y : E} (hy : y ∈ c.target) :
    _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm (patchInCoordinates c V W) y = W y := by
  have hx := c.map_target hy
  have hh := mpullback_symm_partialDiffeomorph_apply c (by simp)
    (patchInCoordinates c V W) hx
  rw [c.right_inv hy] at hh
  rw [hh, patchInCoordinates_of_mem c V W hx]
  change (mfderiv I 𝓘(ℝ, E) c (c.symm y))
    ((mfderiv I 𝓘(ℝ, E) c (c.symm y)).inverse (W (c (c.symm y)))) = W y
  erw [c.right_inv hy]
  exact (isInvertible_mfderiv_partialDiffeomorph c (by simp) hx).self_apply_inverse _


theorem patchInCoordinates_eq_zero_iff {x : M} (hx : x ∈ c.source) :
    patchInCoordinates c V W x = 0 ↔ W (c x) = 0 := by
  rw [patchInCoordinates_of_mem c V W hx]
  exact mpullback_partialDiffeomorph_eq_zero_iff c (by simp) W hx


theorem patchInCoordinates_eventuallyEq_pullback {x : M} (hx : x ∈ c.source) :
    (fun y => (⟨y, patchInCoordinates c V W y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
      (fun y => (⟨y, _root_.VectorField.mpullback I 𝓘(ℝ, E) c W y⟩ : TangentBundle I M)) := by
  filter_upwards [c.open_source.mem_nhds hx] with y hy
  exact congrArg (fun v => (⟨y, v⟩ : TangentBundle I M))
    (patchInCoordinates_of_mem c V W hy)

theorem patchInCoordinates_eq_self_off {C : Set E}
    (hagree : ∀ y ∈ c.target \ C,
      W y = _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V y)
    {x : M} (hx : x ∉ c.symm '' C) : patchInCoordinates c V W x = V x := by
  by_cases hxc : x ∈ c.source
  · have hcx : c x ∉ C := fun h => hx ⟨c x, h, c.left_inv hxc⟩
    rw [patchInCoordinates_of_mem c V W hxc]
    change (mfderiv I 𝓘(ℝ, E) c x).inverse (W (c x)) = _
    rw [hagree (c x) ⟨c.map_source hxc, hcx⟩,
      mpullback_symm_partialDiffeomorph_apply c (by simp) V hxc]
    exact (isInvertible_mfderiv_partialDiffeomorph c (by simp) hxc).inverse_apply_self _
  · exact patchInCoordinates_of_not_mem c V W hxc

theorem patchInCoordinates_eventuallyEq_self [T2Space M] {C : Set E}
    (hC : IsCompact C) (hCt : C ⊆ c.target)
    (hagree : ∀ y ∈ c.target \ C,
      W y = _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V y)
    {x : M} (hx : x ∉ c.symm '' C) :
    (fun y => (⟨y, patchInCoordinates c V W y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) := by
  have hK := hC.image_of_continuousOn (c.symm.contMDiffOn.continuousOn.mono hCt)
  filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
  exact congrArg (fun v => (⟨y, v⟩ : TangentBundle I M))
    (patchInCoordinates_eq_self_off c V W hagree hy)

theorem contMDiff_patchInCoordinates [IsManifold I 1 M] [T2Space M]
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hW : ContDiffOn ℝ ∞ W c.target) {C : Set E}
    (hC : IsCompact C) (hCt : C ⊆ c.target)
    (hagree : ∀ y ∈ c.target \ C,
      W y = _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V y) :
    ContMDiff I I.tangent ∞
      (fun x => (⟨x, patchInCoordinates c V W x⟩ : TangentBundle I M)) := by
  intro x
  by_cases hx : x ∈ c.source
  · have hWx : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
        (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) E)) (c x) :=
      contMDiffAt_vectorSpace_iff_contDiffAt.mpr
        (hW.contDiffAt (c.open_target.mem_nhds (c.map_source hx)))
    exact (contMDiffAt_mpullback_partialDiffeomorph c (by simp) hx hWx).congr_of_eventuallyEq
      (patchInCoordinates_eventuallyEq_pullback c V W hx)
  · have hxK : x ∉ c.symm '' C := by
      rintro ⟨y,hy,rfl⟩
      exact hx (c.map_target (hCt hy))
    exact (hV x).congr_of_eventuallyEq
      (patchInCoordinates_eventuallyEq_self c V W hC hCt hagree hxK)

theorem tsupport_patchInCoordinates_sub_subset [T2Space M] {C : Set E}
    (hC : IsCompact C) (hCt : C ⊆ c.target)
    (hagree : ∀ y ∈ c.target \ C,
      W y = _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V y) :
    tsupport (fun x => patchInCoordinates c V W x - V x) ⊆ c.symm '' C := by
  apply closure_minimal _ (hC.image_of_continuousOn
    (c.symm.contMDiffOn.continuousOn.mono hCt)).isClosed
  intro x hx
  by_contra hn
  exact hx (sub_eq_zero.mpr (patchInCoordinates_eq_self_off c V W hagree hn))


theorem isCompact_tsupport_patchInCoordinates_sub [T2Space M] {C : Set E}
    (hC : IsCompact C) (hCt : C ⊆ c.target)
    (hagree : ∀ y ∈ c.target \ C,
      W y = _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V y) :
    IsCompact (tsupport (fun x => patchInCoordinates c V W x - V x)) :=
  (hC.image_of_continuousOn (c.symm.contMDiffOn.continuousOn.mono hCt)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_patchInCoordinates_sub_subset c V W hC hCt hagree)

theorem continuous_patchInCoordinates [IsManifold I 1 M] [T2Space M]
    (hV : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hW : ContinuousOn W c.target) {C : Set E}
    (hC : IsCompact C) (hCt : C ⊆ c.target)
    (hagree : ∀ y ∈ c.target \ C,
      W y = _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V y) :
    Continuous (fun x => (⟨x, patchInCoordinates c V W x⟩ : TangentBundle I M)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ c.source
  · have hWx : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 0
        (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) E)) (c x) :=
      contMDiffAt_vectorSpace_iff_contDiffAt.mpr
        (contDiffOn_zero.mpr hW |>.contDiffAt (c.open_target.mem_nhds (c.map_source hx)))
    exact (contMDiffAt_mpullback_partialDiffeomorph c (by simp) hx hWx).continuousAt.congr
      (patchInCoordinates_eventuallyEq_pullback c V W hx).symm
  · have hxK : x ∉ c.symm '' C := by
      rintro ⟨y,hy,rfl⟩
      exact hx (c.map_target (hCt hy))
    exact hV.continuousAt.congr
      (patchInCoordinates_eventuallyEq_self c V W hC hCt hagree hxK).symm

theorem patchInCoordinates_zeroSet :
    {x : M | patchInCoordinates c V W x = 0} =
      c.symm '' {y | y ∈ c.target ∧ W y = 0} ∪ ({x : M | V x = 0} \ c.source) := by
  ext x
  by_cases hx : x ∈ c.source
  · rw [mem_ofPred_eq, patchInCoordinates_of_mem c V W hx,
      mpullback_partialDiffeomorph_eq_zero_iff c (by simp) W hx]
    constructor
    · intro hz
      exact Or.inl ⟨c x, ⟨c.map_source hx,hz⟩, c.left_inv hx⟩
    · rintro (⟨y,hy,rfl⟩ | ⟨_,hh⟩)
      · change W (c (c.symm y)) = 0
        erw [c.right_inv hy.1]
        exact hy.2
      · exact (hh hx).elim
  · rw [mem_ofPred_eq, patchInCoordinates_of_not_mem c V W hx]
    constructor
    · exact fun hz => Or.inr ⟨hz,hx⟩
    · rintro (⟨y,hy,rfl⟩ | ⟨hz,_⟩)
      · exact (hx (c.map_target hy.1)).elim
      · exact hz

theorem finite_zeroSet_patchInCoordinates
    (hW : {y | y ∈ c.target ∧ W y = 0}.Finite)
    (hV : ({x : M | V x = 0} \ c.source).Finite) :
    {x : M | patchInCoordinates c V W x = 0}.Finite := by
  rw [patchInCoordinates_zeroSet c V W]
  exact (hW.image c.symm).union hV

end DifferentialGeometry.VectorField

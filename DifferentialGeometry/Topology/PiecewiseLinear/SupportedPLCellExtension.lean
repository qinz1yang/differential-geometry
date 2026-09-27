/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ControlledInwardPush

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private noncomputable def supportedPieceExtension {M : Type*} (W : Set M) (F : M → M) :
    M → M := by
  classical
  exact W.piecewise F id

private theorem isPL_supportedPieceExtension {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {W K : Set M} {F : M → M} (hK : IsClosed K) (hKW : K ⊆ interior W)
    (hF : IsPLOn n n F W) (hfix : EqOn F id (W \ K)) :
    IsPL n n (supportedPieceExtension W F) := by
  classical
  intro x
  by_cases hx : x ∈ interior W
  · apply piecewiseAffineProperty_localInvariantProp.liftPropAt_congr_of_eventuallyEq
      ((hF.mono_of_isOpen isOpen_interior interior_subset).isPLAt_of_isOpen
        isOpen_interior hx)
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact piecewise_eq_of_mem W F id (interior_subset hy)
  · have hxK : x ∉ K := fun hxK => hx (hKW hxK)
    apply piecewiseAffineProperty_localInvariantProp.liftPropAt_congr_of_eventuallyEq
      (isPL_id (M := M) x)
    filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
    by_cases hyW : y ∈ W
    · change W.piecewise F id y = id y
      rw [piecewise_eq_of_mem W F id hyW]
      exact hfix ⟨hyW, hy⟩
    · exact piecewise_eq_of_notMem W F id hyW

theorem exists_supported_isPL_homeomorph_extension {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {W K : Set M} {F G : M → M}
    (hK : IsClosed K) (hKW : K ⊆ interior W)
    (hF : IsPLOn n n F W) (hG : IsPLOn n n G W)
    (hFW : MapsTo F W W) (hGW : MapsTo G W W)
    (hGF : LeftInvOn G F W) (hFG : LeftInvOn F G W)
    (hfix : EqOn F id (W \ K)) :
    ∃ φ : M ≃ₜ M, IsPL n n φ ∧ IsPL n n φ.symm ∧
      EqOn φ F W ∧ EqOn φ.symm G W ∧ EqOn φ id Kᶜ := by
  classical
  have hGfix : EqOn G id (W \ K) := by
    intro x hx
    have ht := hGF hx.1
    rwa [hfix hx] at ht
  let f := supportedPieceExtension W F
  let g := supportedPieceExtension W G
  have hfp : IsPL n n f := isPL_supportedPieceExtension hK hKW hF hfix
  have hgp : IsPL n n g := isPL_supportedPieceExtension hK hKW hG hGfix
  have hgf : Function.LeftInverse g f := by
    intro x
    by_cases hx : x ∈ W
    · change W.piecewise G id (W.piecewise F id x) = x
      rw [piecewise_eq_of_mem W F id hx, piecewise_eq_of_mem W G id (hFW hx)]
      exact hGF hx
    · change W.piecewise G id (W.piecewise F id x) = x
      rw [piecewise_eq_of_notMem W F id hx]
      exact piecewise_eq_of_notMem W G id hx
  have hfg : Function.RightInverse g f := by
    intro x
    by_cases hx : x ∈ W
    · change W.piecewise F id (W.piecewise G id x) = x
      rw [piecewise_eq_of_mem W G id hx, piecewise_eq_of_mem W F id (hGW hx)]
      exact hFG hx
    · change W.piecewise F id (W.piecewise G id x) = x
      rw [piecewise_eq_of_notMem W G id hx]
      exact piecewise_eq_of_notMem W F id hx
  let φ : M ≃ₜ M :=
    { toEquiv := ⟨f, g, hgf, hfg⟩
      continuous_toFun := continuous_iff_continuousAt.mpr fun x => by
        simpa only [continuousWithinAt_univ] using (hfp x).continuousWithinAt
      continuous_invFun := continuous_iff_continuousAt.mpr fun x => by
        simpa only [continuousWithinAt_univ] using (hgp x).continuousWithinAt }
  refine ⟨φ, hfp, hgp, ?_, ?_, ?_⟩
  · intro x hx
    exact piecewise_eq_of_mem W F id hx
  · intro x hx
    exact piecewise_eq_of_mem W G id hx
  · intro x hx
    by_cases hxW : x ∈ W
    · change W.piecewise F id x = id x
      rw [piecewise_eq_of_mem W F id hxW]
      exact hfix ⟨hxW, hx⟩
    · exact piecewise_eq_of_notMem W F id hxW

end DifferentialGeometry.Topology.PiecewiseLinear

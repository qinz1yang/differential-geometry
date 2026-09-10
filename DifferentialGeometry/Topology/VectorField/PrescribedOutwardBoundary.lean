import DifferentialGeometry.Topology.VectorField.BoundarySectionExtension
import DifferentialGeometry.Topology.VectorField.OutwardPoincareHopf
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.NormalSign

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
namespace Poincare.VectorField

theorem exists_outward_with_prescribed_tangential_component
    {E H B : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    {J : ModelWithCorners ℝ E H} [IsManifold J 1 B]
    {n : ℕ} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [CompactSpace M]
    {ε δ : ℝ} [Fact ((0 : ℝ) < ε)] (hδ : 0 < δ) :
    let I := 𝓡∂ (n + 1)
    let S : Opens (B × Icc (0 : ℝ) ε) :=
      ⟨{q | q.2.val < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
    ∀ (Y : Opens M), I.boundary M ⊆ Y →
    ∀ e : Diffeomorph (J.prod (𝓡∂ 1)) I S Y ∞,
      (∀ q : S, 0 < q.val.2.val → I.IsInteriorPoint (e q).val) →
      (∀ q : S, q.val.2.val = 0 → I.IsBoundaryPoint (e q).val) →
    ∀ V : ∀ x : M, TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) →
      (∀ x, I.IsBoundaryPoint x → (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V x) < 0) →
    ∀ T : ∀ p : B, TangentSpace J p,
      ContMDiff J J.tangent ∞ (fun p => (⟨p, T p⟩ : TangentBundle J B)) →
    ∃ G : ∀ x : M, TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M)) ∧
      (∀ x, I.IsBoundaryPoint x → (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (G x) < 0) ∧
      {x | G x = 0} = {x | V x = 0} ∧
      (∀ x, V x = 0 → G =ᶠ[𝓝 x] V) ∧
      ∀ q : S, q.val.2.val = 0 →
        _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => G y.val) q =
          (T q.val.1, (Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2).symm (-1)) := by
  intro I S Y hY e hi hzero V hV hout T hT
  obtain ⟨U, hU, hUzero⟩ := exists_boundary_section_extension hδ Y e V hV T (fun _ => -1)
    hT contMDiff_const
  have hUout (x : M) (hx : I.IsBoundaryPoint x) :
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (U x) < 0 := by
    let y : Y := ⟨x, hY hx⟩
    let q := e.symm y
    have he : (e q).val = x := congrArg Subtype.val (e.apply_symm_apply y)
    have hqb : I.IsBoundaryPoint (e q).val := he.symm ▸ hx
    have hq0 : q.val.2.val = 0 := by
      apply le_antisymm _ q.val.2.property.1
      by_contra h
      exact (I.isBoundaryPoint_iff_not_isInteriorPoint (e q).val).mp hqb (hi q (lt_of_not_ge h))
    have hv := Poincare.Manifold.BoundaryCollar.proj_collar_pushforward_neg S Y e hq0 hqb
      (T q.val.1, (Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2).symm (-1))
      (by rw [ContinuousLinearEquiv.apply_symm_apply]; norm_num)
    rw [← hUzero q hq0] at hv
    erw [he] at hv
    exact hv
  obtain ⟨G, hG, hGU, hz, hgerm⟩ := exists_boundary_splice_preserving_zero_germs I V U hV hU
    (I.isClosed_boundary (n := ∞) (by simp))
    (fun x hx t => affineSection_ne_zero_of_outward V U (hout x hx) (hUout x hx) t)
  refine ⟨G, hG, (fun x hx => (hGU x hx).self_of_nhds.symm ▸ hUout x hx), hz, hgerm, ?_⟩
  intro q hq
  have hval : G (e q).val = mfderiv (J.prod (𝓡∂ 1)) I e q
      (T q.val.1, (Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2).symm (-1)) :=
    (hGU (e q).val (hzero q hq)).self_of_nhds.trans (hUzero q hq)
  change (mfderiv (J.prod (𝓡∂ 1)) I e q).inverse (G (e q).val) = _
  exact (congrArg (mfderiv (J.prod (𝓡∂ 1)) I e q).inverse hval).trans
    ((isInvertible_mfderiv_diffeomorph e (by simp) q).inverse_apply_self _)

end Poincare.VectorField

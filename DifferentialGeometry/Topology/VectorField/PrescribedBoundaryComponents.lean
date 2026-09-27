import DifferentialGeometry.Topology.VectorField.BoundarySectionExtension
import DifferentialGeometry.Topology.VectorField.OutwardPoincareHopf
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.NormalSign

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
namespace DifferentialGeometry.VectorField

theorem exists_with_prescribed_boundary_components
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
    ∀ (T : ∀ p : B, TangentSpace J p) (b : B → ℝ),
      ContMDiff J J.tangent ∞ (fun p => (⟨p, T p⟩ : TangentBundle J B)) →
      ContMDiff J 𝓘(ℝ, ℝ) ∞ b →
      (∀ q : S, q.val.2.val = 0 →
        0 < DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2
          (_root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val) q).2 * b q.val.1) →
    ∃ G : ∀ x : M, TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M)) ∧
      {x | G x = 0} = {x | V x = 0} ∧
      (∀ x, V x = 0 → G =ᶠ[𝓝 x] V) ∧
      ∀ q : S, q.val.2.val = 0 →
        _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => G y.val) q =
          (T q.val.1, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2).symm (b q.val.1)) := by
  intro I S Y hY e hi hzero V hV T b hT hb hsign
  obtain ⟨U, hU, hUzero⟩ := exists_boundary_section_extension hδ Y e V hV T b hT hb
  have haffine (x : M) (hx : I.IsBoundaryPoint x) (t : unitInterval) :
      affineSection I V U t x ≠ 0 := by
    let y : Y := ⟨x, hY hx⟩
    let q := e.symm y
    have he : (e q).val = x := congrArg Subtype.val (e.apply_symm_apply y)
    have hqb : I.IsBoundaryPoint (e q).val := he.symm ▸ hx
    have hq0 : q.val.2.val = 0 := by
      apply le_antisymm _ q.val.2.property.1
      by_contra h
      exact (I.isBoundaryPoint_iff_not_isInteriorPoint (e q).val).mp hqb (hi q (lt_of_not_ge h))
    let W := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val)
    obtain ⟨c, hc, hnormal⟩ := DifferentialGeometry.Manifold.BoundaryCollar.collar_normal_eq_pos_mul_proj S Y e hq0 hqb
    have hv := hnormal (W q)
    have hpush : mfderiv (J.prod (𝓡∂ 1)) I e q (W q) = V (e q).val :=
      (isInvertible_mfderiv_diffeomorph e (by simp) q).self_apply_inverse _
    rw [hpush] at hv
    have hu := hnormal (T q.val.1,
      (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2).symm (b q.val.1))
    rw [ContinuousLinearEquiv.apply_symm_apply, ← hUzero q hq0] at hu
    erw [he] at hv hu
    let L := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))
    have hs := hsign q hq0
    have hsame : 0 < L (V x) * L (U x) := by
      rw [hv, hu] at hs
      nlinarith [sq_nonneg c]
    intro hzeroV
    have heval := congrArg L hzeroV
    change (1 - (t : ℝ)) • L (V x) + (t : ℝ) • L (U x) = 0 at heval
    rcases mul_pos_iff.mp hsame with hp | hn
    · have hp' : (1 - (t : ℝ)) • L (V x) + (t : ℝ) • L (U x) ∈ Ioi (0 : ℝ) :=
        convex_Ioi 0 hp.1 hp.2 (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
      exact hp'.ne' heval
    · have hn' : (1 - (t : ℝ)) • L (V x) + (t : ℝ) • L (U x) ∈ Iio (0 : ℝ) :=
        convex_Iio 0 hn.1 hn.2 (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
      exact hn'.ne heval
  obtain ⟨G, hG, hGU, hz, hgerm⟩ := exists_boundary_splice_preserving_zero_germs I V U hV hU
    (I.isClosed_boundary (n := ∞) (by simp))
    haffine
  refine ⟨G, hG, hz, hgerm, ?_⟩
  intro q hq
  have hval : G (e q).val = mfderiv (J.prod (𝓡∂ 1)) I e q
      (T q.val.1, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2).symm (b q.val.1)) :=
    (hGU (e q).val (hzero q hq)).self_of_nhds.trans (hUzero q hq)
  change (mfderiv (J.prod (𝓡∂ 1)) I e q).inverse (G (e q).val) = _
  exact (congrArg (mfderiv (J.prod (𝓡∂ 1)) I e q).inverse hval).trans
    ((isInvertible_mfderiv_diffeomorph e (by simp) q).inverse_apply_self _)

end DifferentialGeometry.VectorField

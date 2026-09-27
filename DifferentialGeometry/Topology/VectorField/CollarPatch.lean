import DifferentialGeometry.Topology.VectorField.DiffeomorphPatch
import DifferentialGeometry.Topology.VectorField.InwardCollarZeros

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
namespace DifferentialGeometry.VectorField

private theorem isCompact_closed_collar_strip {B : Type*} [TopologicalSpace B] [CompactSpace B]
    {ε δ R : ℝ} (hR : R < δ)
    (S : Opens (B × Icc (0 : ℝ) ε))
    (hS : (S : Set (B × Icc (0 : ℝ) ε)) = {q | q.2.val < δ}) :
    IsCompact {q : S | q.val.2.val ≤ R} := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have he : Subtype.val '' {q : S | q.val.2.val ≤ R} =
      {q : B × Icc (0 : ℝ) ε | q.2.val ≤ R} := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hq
      exact ⟨⟨q, (Set.ext_iff.mp hS q).mpr (hq.trans_lt hR)⟩, hq, rfl⟩
  rw [he]
  exact (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).isCompact

variable {E F H H' B M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
  [TopologicalSpace M] [ChartedSpace H' M] [T2Space M]
  {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F H'}
  [IsManifold J 1 B] [IsManifold I 1 M]
  {ε δ R : ℝ} [Fact ((0 : ℝ) < ε)]
  (S : Opens (B × Icc (0 : ℝ) ε))
  (hS : (S : Set (B × Icc (0 : ℝ) ε)) = {q | q.2.val < δ})
  (Y : Opens M) (e : Diffeomorph (J.prod (𝓡∂ 1)) I S Y ∞)
  (V : ∀ x : M, TangentSpace I x) (G : ∀ q : S, TangentSpace (J.prod (𝓡∂ 1)) q)
  (hR : R < δ)
  (hmatch : ∀ q : S, R ≤ q.val.2.val → G q =
    _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val) q)

include hS hR hmatch


theorem contMDiff_patchThroughCollar
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hG : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, G q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S))) :
    ContMDiff I I.tangent ∞
      (fun x => (⟨x, patchThroughDiffeomorph Y e V G x⟩ : TangentBundle I M)) :=
  contMDiff_patchThroughDiffeomorph Y e V G hV hG
    (isCompact_closed_collar_strip hR S hS) (fun q hq => hmatch q (not_le.mp hq).le)

omit [IsManifold J 1 B] [IsManifold I 1 M] in
theorem patchThroughCollar_eventuallyEq_at_original_zero
    (hn : ∀ q : S, _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e
      (fun y : Y => V y.val) q ≠ 0)
    {x : M} (hx : V x = 0) :
    (fun y => (⟨y, patchThroughDiffeomorph Y e V G y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) := by
  apply patchThroughDiffeomorph_eventuallyEq_self Y e V G
    (isCompact_closed_collar_strip hR S hS) (fun q hq => hmatch q (not_le.mp hq).le)
  rintro ⟨q, _, hq⟩
  change (e q).val = x at hq
  exact hn q ((mpullback_diffeomorph_eq_zero_iff e (by simp) (fun y : Y => V y.val) q).mpr
    (by change (V (e q).val : F) = 0; erw [hq]; exact hx))

omit [CompactSpace B] [T2Space M] [IsManifold J 1 B] [IsManifold I 1 M] hS hR hmatch in
theorem patchThroughCollar_zeroSet
    (hn : ∀ q : S, _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e
      (fun y : Y => V y.val) q ≠ 0) :
    {x | patchThroughDiffeomorph Y e V G x = 0} =
      (fun q : S => (e q).val) '' {q | G q = 0} ∪ {x | V x = 0} ∧
    Disjoint ((fun q : S => (e q).val) '' {q | G q = 0}) {x | V x = 0} := by
  have hnY (y : Y) : V y.val ≠ 0 := by
    intro hy
    apply hn (e.symm y)
    apply (mpullback_diffeomorph_eq_zero_iff e (by simp) (fun y : Y => V y.val) (e.symm y)).mpr
    change (V (e (e.symm y)).val : F) = 0
    erw [e.apply_symm_apply]
    exact hy
  refine ⟨?_, ?_⟩
  · rw [patchThroughDiffeomorph_zeroSet]
    congr 1
    ext x
    exact ⟨And.left, fun hx => ⟨hx, fun hY => hnY ⟨x, hY⟩ hx⟩⟩
  · apply Set.disjoint_left.mpr
    rintro x ⟨q, _, rfl⟩ hx
    exact hnY (e q) hx

end DifferentialGeometry.VectorField

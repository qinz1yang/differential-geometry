import Mathlib.Geometry.Manifold.Instances.Icc
import DifferentialGeometry.Topology.VectorField.OpenRestriction
import DifferentialGeometry.Topology.VectorField.FiniteZeros
import DifferentialGeometry.Topology.Compactness.Strip

set_option autoImplicit false
open Set Function Bundle Manifold TopologicalSpace
open scoped ContDiff Topology
noncomputable section
namespace DifferentialGeometry.VectorField

theorem exists_nonvanishing_collar_pullback_strip
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    {F G M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace G M]
    {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F G}
    [IsManifold J 1 B] [IsManifold I 1 M]
    {ε : ℝ} [Fact ((0 : ℝ) < ε)]
    (c : C(B × Icc (0 : ℝ) ε, M))
    (S : Opens (B × Icc (0 : ℝ) ε)) (Y : Opens M)
    (e : Diffeomorph (J.prod (𝓡∂ 1)) I S Y ∞)
    (he : ∀ q : S, (e q : M) = c q.val)
    (hS : ∀ p : B, (p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩) ∈ S)
    (V : ∀ x : M, TangentSpace I x)
    (hV : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) Y)
    (hzero : ∀ p : B, V (c (p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩)) ≠ 0) :
    let W := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e
      (fun y : Y => V y.val)
    ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, W q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) ∧
      (∀ q : S, W q = 0 ↔ V (c q.val) = 0) ∧
      (∀ q : S, mfderiv (J.prod (𝓡∂ 1)) I e q (W q) = V (e q).val) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
        {q : B × Icc (0 : ℝ) ε | q.2.val < δ} ⊆ S ∧
        ∀ q : S, q.val.2.val < δ → W q ≠ 0 := by
  intro W
  have hVr := contMDiff_tangentSection_restrict_opens Y hV
  have hW : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, W q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) := by
    intro q
    exact contMDiffAt_mpullback_partialDiffeomorph e.toPartialDiffeomorph (by simp)
      (by trivial) (hVr (e q))
  have hz (q : S) : W q = 0 ↔ V (c q.val) = 0 := by
    refine (mpullback_diffeomorph_eq_zero_iff e (by simp) (fun y : Y => V y.val) q).trans ?_
    change (V ((e q).val) : F) = 0 ↔ (V (c q.val) : F) = 0
    rw [he q]
  have hnonzero : IsOpen {q : S | W q ≠ 0} :=
    (DifferentialGeometry.VectorBundle.isClosed_zeroSet ℝ hW.continuous).isOpen_compl
  obtain ⟨δ, hδ, hδε, hδS⟩ := DifferentialGeometry.Topology.exists_shorter_strip_image_subset
    (Fact.out : (0 : ℝ) < ε) continuous_id (S.isOpen.isOpenMap_subtype_val _ hnonzero)
    (fun p => ⟨⟨_, hS p⟩, fun hh => hzero p ((hz ⟨_, hS p⟩).mp hh), rfl⟩)
  refine ⟨hW, hz, ?_, δ, hδ, hδε, ?_, ?_⟩
  · intro q
    exact (isInvertible_mfderiv_diffeomorph e (by simp) q).self_apply_inverse (V (e q).val)
  · intro q hq
    obtain ⟨q', _, hq'⟩ := hδS ⟨q, hq, rfl⟩
    change q'.val = q at hq'
    exact hq' ▸ q'.property
  · intro q hq hWzero
    obtain ⟨q', hn, heq⟩ := hδS ⟨q.val, hq, rfl⟩
    have hh : q' = q := Subtype.ext heq
    exact hn (hh ▸ hWzero)

end DifferentialGeometry.VectorField

import DifferentialGeometry.Topology.Manifold.Interval.SignedCoordinate
import DifferentialGeometry.Topology.VectorField.InwardCollarOutwardization

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
namespace DifferentialGeometry.VectorField

theorem exists_inwardCollar_pullback_germ
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    {J : ModelWithCorners ℝ E H}
    {ε a : ℝ} [Fact ((0 : ℝ) < ε)] (ha : a ≠ 0)
    (S : Opens (B × Icc (0 : ℝ) ε))
    (T : ∀ p : B, TangentSpace J p) (b : B → ℝ)
    (L : ∀ q : S, TangentSpace (J.prod (𝓡∂ 1)) q)
    (hL : ∀ p : S, p.val.2.val ≤ a → L p =
      (T p.val.1, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc p.val.2).symm
        (-a * (collarExtension T b collarTransition (p.val.1, 1 - p.val.2.val / a)).2)))
    (q : S) (hq : 0 < q.val.2.val ∧ q.val.2.val < ε) (hqa : q.val.2.val < a) :
    ∃ f : PartialDiffeomorph (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ)) S (B × ℝ) ∞,
      q ∈ f.source ∧
      (∀ p ∈ f.source, f p = (p.val.1, 1 - p.val.2.val / a)) ∧
      L =ᶠ[𝓝 q] _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ)) f
        (collarExtension T b collarTransition) := by
  obtain ⟨f, hqf, hf⟩ := DifferentialGeometry.Manifold.Interval.exists_signedStrip_partialDiffeomorph J ha S q hq
  refine ⟨f, hqf, hf, ?_⟩
  have hnear : ∀ᶠ p : S in 𝓝 q, p.val.2.val < a :=
    (isOpen_lt (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))
      continuous_const).mem_nhds hqa
  filter_upwards [f.open_source.mem_nhds hqf, hnear] with p hpf hpa
  have hfg : f =ᶠ[𝓝 p] fun r : S => (r.val.1, 1 - r.val.2.val / a) := by
    filter_upwards [f.open_source.mem_nhds hpf] with r hr
    exact hf r hr
  have hd := hfg.mfderiv_eq (I := J.prod (𝓡∂ 1)) (I' := J.prod 𝓘(ℝ, ℝ))
  have hpush : mfderiv (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ)) f p (L p) =
      collarExtension T b collarTransition (f p) := by
    erw [hd, DifferentialGeometry.Manifold.Interval.mfderiv_signedStripCoordinate, hf p hpf, hL p hpa.le]
    apply Prod.ext
    · rfl
    · change -(DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc p.val.2
        ((DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc p.val.2).symm
          (-a * (collarExtension T b collarTransition (p.val.1, 1 - p.val.2.val / a)).2))) / a = _
      rw [ContinuousLinearEquiv.apply_symm_apply]
      field_simp
  change L p = (mfderiv (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ)) f p).inverse
    (collarExtension T b collarTransition (f p))
  rw [← hpush]
  exact ((isInvertible_mfderiv_partialDiffeomorph f (by simp) hpf).inverse_apply_self (L p)).symm

end DifferentialGeometry.VectorField

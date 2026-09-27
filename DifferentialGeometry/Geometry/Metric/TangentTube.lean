import DifferentialGeometry.Geometry.Metric.CompactTangentBall
import DifferentialGeometry.Geometry.Metric.InfinitesimalDistance



noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry Metric
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

set_option backward.isDefEq.respectTransparency false in



theorem exists_metric_tangent_pair_radius (g : SmoothRiemannianMetric I M)
    {W : Set (TangentBundle I M × TangentBundle I M)} (hW : IsOpen W)
    (hzero : ∀ x : M,
      ((TotalSpace.mk' E x 0 : TangentBundle I M), TotalSpace.mk' E x 0) ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u v : TangentBundle I M, u.proj = v.proj →
      Real.sqrt (g.inner u.proj u.2 u.2) ≤ ε →
      Real.sqrt (g.inner v.proj v.2 v.2) ≤ ε → (u, v) ∈ W := by
  let D : Set (TangentBundle I M × TangentBundle I M) :=
    {p | p.1.proj = p.2.proj ∧ Real.sqrt (g.inner p.1.proj p.1.2 p.1.2) ≤ 1 ∧
      Real.sqrt (g.inner p.2.proj p.2.2 p.2.2) ≤ 1}
  have hDc : IsCompact D := by
    have hp := FiberBundle.continuous_proj E (TangentSpace I : M → Type _)
    have hclosed : IsClosed {p : TangentBundle I M × TangentBundle I M | p.1.proj = p.2.proj} :=
      isClosed_eq (hp.comp continuous_fst) (hp.comp continuous_snd)
    exact ((isCompact_metric_tangent_closedBall g 1).prod
      (isCompact_metric_tangent_closedBall g 1)).inter_left hclosed
  let A : ℝ × D → TangentBundle I M × TangentBundle I M := fun p =>
    (TotalSpace.mk' E p.2.val.1.proj (p.1 • p.2.val.1.2),
      TotalSpace.mk' E p.2.val.2.proj (p.1 • p.2.val.2.2))
  have hA : Continuous A :=
    (continuous_tangent_smul continuous_fst
      (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))).prodMk
      (continuous_tangent_smul continuous_fst
        (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))
  have hzeroA : ({0} : Set ℝ) ×ˢ (univ : Set D) ⊆ A ⁻¹' W := by
    rintro ⟨t, p⟩ ⟨ht, _⟩
    obtain rfl : t = 0 := ht
    change (TotalSpace.mk' E p.val.1.proj ((0 : ℝ) • p.val.1.2),
      TotalSpace.mk' E p.val.2.proj ((0 : ℝ) • p.val.2.2)) ∈ W
    simp only [zero_smul]
    rw [← p.property.1]
    exact hzero _
  let : CompactSpace D := isCompact_iff_compactSpace.mp hDc
  obtain ⟨U, V, hU, _, h0U, hUV, hprod⟩ := generalized_tube_lemma isCompact_singleton
    isCompact_univ (hW.preimage hA) hzeroA
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (h0U (mem_singleton 0)))
  let ε : ℝ := δ / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, hε, fun u v huv hu hv => ?_⟩
  let u' : TangentBundle I M := TotalSpace.mk' E u.proj (ε⁻¹ • u.2)
  let v' : TangentBundle I M := TotalSpace.mk' E v.proj (ε⁻¹ • v.2)
  have hscale (p : TangentBundle I M) (hp : Real.sqrt (g.inner p.proj p.2 p.2) ≤ ε) :
      Real.sqrt (g.inner p.proj (ε⁻¹ • p.2) (ε⁻¹ • p.2)) ≤ 1 := by
    rw [sqrt_metric_smul, abs_of_pos (inv_pos.mpr hε)]
    exact (mul_le_mul_of_nonneg_left hp (inv_pos.mpr hε).le).trans_eq (inv_mul_cancel₀ hε.ne')
  let p : D := ⟨(u', v'), huv, hscale u hu, hscale v hv⟩
  have hεU : ε ∈ U := hδU (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hε]
    dsimp [ε]
    linarith)
  have h := hprod (show (ε, p) ∈ U ×ˢ V from ⟨hεU, hUV (mem_univ p)⟩)
  change (TotalSpace.mk' E u.proj (ε • (ε⁻¹ • u.2)),
    TotalSpace.mk' E v.proj (ε • (ε⁻¹ • v.2))) ∈ W at h
  simpa only [smul_smul, mul_inv_cancel₀ hε.ne', one_smul] using h

end DifferentialGeometry.Geometry

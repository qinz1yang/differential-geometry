import DifferentialGeometry.Geometry.Metric.TangentScaling
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit



noncomputable section

open Bundle Manifold Set DifferentialGeometry
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

set_option backward.isDefEq.respectTransparency false in


theorem isCompact_metric_tangent_closedBall (g : SmoothRiemannianMetric I M) (R : ℝ) :
    IsCompact {p : TangentBundle I M | Real.sqrt (g.inner p.proj p.2 p.2) ≤ R} := by
  by_cases hR : 0 ≤ R
  · let A : ℝ × MetricUnitTangent g → TangentBundle I M := fun p =>
      TotalSpace.mk' E (MetricUnitTangent.base p.2) (p.1 • MetricUnitTangent.vec p.2)
    have hA : Continuous A := continuous_tangent_smul continuous_fst
      (continuous_subtype_val.comp continuous_snd)
    have hAc : IsCompact (A '' (Icc 0 R ×ˢ univ)) :=
      (isCompact_Icc.prod (metricUnit_compact g)).image hA
    have hZ : IsCompact (range (fun x : M => (TotalSpace.mk' E x 0 : TangentBundle I M))) :=
      isCompact_range (continuous_zeroSection ℝ (F := E) (E := TangentSpace I))
    have heq : {p : TangentBundle I M | Real.sqrt (g.inner p.proj p.2 p.2) ≤ R} =
        range (fun x : M => (TotalSpace.mk' E x 0 : TangentBundle I M)) ∪
          A '' (Icc 0 R ×ˢ univ) := by
      ext p
      constructor
      · intro hp
        by_cases hv : p.2 = 0
        · exact Or.inl ⟨p.proj, by cases p; simp_all only [TotalSpace.mk']⟩
        · let s := Real.sqrt (g.inner p.proj p.2 p.2)
          have hs : 0 < s := Real.sqrt_pos.mpr (g.pos p.proj p.2 hv)
          have hsq : s * s = g.inner p.proj p.2 p.2 := Real.mul_self_sqrt (g.pos p.proj p.2 hv).le
          have hw : g.inner p.proj (s⁻¹ • p.2) (s⁻¹ • p.2) = 1 := by
            rw [metric_smul2, ← hsq]
            field_simp
          let u : MetricUnitTangent g := ⟨TotalSpace.mk' E p.proj (s⁻¹ • p.2), hw⟩
          refine Or.inr ⟨(s, u), ⟨⟨hs.le, hp⟩, mem_univ _⟩, ?_⟩
          change (TotalSpace.mk' E p.proj (s • (s⁻¹ • p.2)) : TangentBundle I M) = p
          rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
      · rintro (⟨x, rfl⟩ | ⟨⟨s, u⟩, ⟨hs, _⟩, rfl⟩)
        · change Real.sqrt (g.inner x 0 0) ≤ R
          simpa only [map_zero, Real.sqrt_zero] using hR
        · change Real.sqrt (g.inner (MetricUnitTangent.base u)
            (s • MetricUnitTangent.vec u) (s • MetricUnitTangent.vec u)) ≤ R
          rw [metric_smul2, MetricUnitTangent.unit, mul_one, ← pow_two, Real.sqrt_sq hs.1]
          exact hs.2
    rw [heq]
    exact hZ.union hAc
  · have hempty : {p : TangentBundle I M | Real.sqrt (g.inner p.proj p.2 p.2) ≤ R} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hR ((Real.sqrt_nonneg _).trans hp)
    rw [hempty]
    exact isCompact_empty

end DifferentialGeometry.Geometry

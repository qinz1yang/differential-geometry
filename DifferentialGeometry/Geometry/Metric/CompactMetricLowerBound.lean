import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Unit
import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Metric lower bound on a compact manifold (the per-pair "(A)" fact)

On a compact manifold, any smooth Riemannian metric `h` is bounded below by a
positive multiple of any other metric `gRef`: `∃ c > 0, c·gRef(v,v) ≤ h(v,v)`.
The proof takes the minimum of the `h`-quadratic form over the (compact) `gRef`
unit tangent bundle — reusing `metricUnit_compact` and `metricUnit_quadCont` —
and rescales by homogeneity. This is the "head term" input for extracting
`MetricUniformEquivalentOn` from Cheeger–Gromov convergence.
-/

noncomputable section

namespace DifferentialGeometry

open scoped Manifold ContDiff Topology
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M]

/-- One smooth Riemannian metric has a positive lower bound relative to another
on any compact base set. -/
theorem metric_lower_on
    {K : Set M} (hK : IsCompact K)
    (h gRef : SmoothRiemannianMetric I M) :
    ∃ c : Real, 0 < c ∧
      ∀ (x : M), x ∈ K → ∀ v : TangentSpace I x,
        c * gRef.inner x v v ≤ h.inner x v v := by
  classical
  set f : MetricUnitTangent (I := I) (M := M) gRef → Real :=
    fun p => quad02 (I := I) (M := M)
      (Tensor0SBundle.metricTensorField (I := I) h (MetricUnitTangent.base (I := I) (M := M) p))
      (MetricUnitTangent.vec (I := I) (M := M) p) with hf_def
  have hf_cont : Continuous f :=
    metricUnit_quadCont (I := I) (M := M) gRef (Tensor0SBundle.metricTensorField (I := I) h)
  have hcompact : IsCompact {p : MetricUnitTangent (I := I) (M := M) gRef |
      MetricUnitTangent.base (I := I) (M := M) p ∈ K} :=
    metricUnitOn_compact (I := I) (M := M) gRef hK
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M; infer_instance
  have hquad_eq : ∀ p : MetricUnitTangent (I := I) (M := M) gRef,
      f p = h.inner (MetricUnitTangent.base (I := I) (M := M) p)
        (MetricUnitTangent.vec (I := I) (M := M) p)
        (MetricUnitTangent.vec (I := I) (M := M) p) := by
    intro p
    simp [hf_def, quad02, Tensor0SBundle.metricTensorField_apply]
  by_cases hne : {p : MetricUnitTangent (I := I) (M := M) gRef |
      MetricUnitTangent.base (I := I) (M := M) p ∈ K}.Nonempty
  · obtain ⟨p0, _hp0, hmin⟩ := hcompact.exists_isMinOn hne hf_cont.continuousOn
    set c : Real := f p0 with hc_def
    have hc : 0 < c := by
      rw [hc_def, hquad_eq p0]
      apply h.pos
      intro hz
      have hu := MetricUnitTangent.unit (I := I) (M := M) p0
      rw [hz] at hu
      simp at hu
    refine ⟨c, hc, ?_⟩
    intro x hx v
    by_cases hv : v = 0
    · subst hv
      have h00 : h.inner x (0 : TangentSpace I x) 0 = 0 := by
        rw [(h.inner x).map_zero, ContinuousLinearMap.zero_apply]
      have hg00 : gRef.inner x (0 : TangentSpace I x) 0 = 0 := by
        rw [(gRef.inner x).map_zero, ContinuousLinearMap.zero_apply]
      rw [h00, hg00, mul_zero]
    · have hrpos : 0 < gRef.inner x v v := gRef.pos x v hv
      set s : Real := Real.sqrt (gRef.inner x v v) with hs_def
      have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
      have hsne : s ≠ 0 := ne_of_gt hspos
      have hss : s * s = gRef.inner x v v := by
        simpa [hs_def, sq] using Real.sq_sqrt hrpos.le
      set u : TangentSpace I x := s⁻¹ • v with hu_def
      have hunit : gRef.inner x u u = 1 := by
        rw [hu_def, metric_smul2]
        field_simp [hsne]
        linarith [hss]
      let p : MetricUnitTangent (I := I) (M := M) gRef :=
        ⟨(⟨x, u⟩ : TangentBundle I M), hunit⟩
      have hpK : MetricUnitTangent.base (I := I) (M := M) p ∈ K := by
        simpa [p, MetricUnitTangent.base] using hx
      have hfp : c ≤ f p := (isMinOn_iff.mp hmin) p hpK
      have hfp_eq : f p = s⁻¹ * s⁻¹ * h.inner x v v := by
        rw [hquad_eq p]
        change h.inner x u u = _
        rw [hu_def, metric_smul2]
      rw [hfp_eq] at hfp
      have hkey : c * (s * s) ≤ h.inner x v v := by
        have := mul_le_mul_of_nonneg_right hfp (by positivity : (0 : Real) ≤ s * s)
        calc c * (s * s) ≤ (s⁻¹ * s⁻¹ * h.inner x v v) * (s * s) := this
          _ = h.inner x v v := by field_simp
      rw [hss] at hkey
      exact hkey
  · refine ⟨1, one_pos, ?_⟩
    intro x hx v
    by_cases hv : v = 0
    · subst hv
      have h00 : h.inner x (0 : TangentSpace I x) 0 = 0 := by
        rw [(h.inner x).map_zero, ContinuousLinearMap.zero_apply]
      have hg00 : gRef.inner x (0 : TangentSpace I x) 0 = 0 := by
        rw [(gRef.inner x).map_zero, ContinuousLinearMap.zero_apply]
      rw [h00, hg00, mul_zero]
    · exfalso
      have hrpos : 0 < gRef.inner x v v := gRef.pos x v hv
      set s : Real := Real.sqrt (gRef.inner x v v)
      have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
      have hunit : gRef.inner x (s⁻¹ • v) (s⁻¹ • v) = 1 := by
        rw [metric_smul2]
        have hss : s * s = gRef.inner x v v := by simpa [sq] using Real.sq_sqrt hrpos.le
        field_simp [ne_of_gt hspos]
        linarith [hss]
      exact hne ⟨⟨(⟨x, s⁻¹ • v⟩ : TangentBundle I M), hunit⟩, by
        simpa [MetricUnitTangent.base] using hx⟩

/-- **Metric lower bound on a compact manifold.** For two smooth Riemannian
metrics `h`, `gRef`, there is `c > 0` with `c·gRef(v,v) ≤ h(v,v)` for all `v`. -/
theorem metric_lower_bound_of_compact [CompactSpace M]
    (h gRef : SmoothRiemannianMetric I M) :
    ∃ c : Real, 0 < c ∧
      ∀ (x : M) (v : TangentSpace I x), c * gRef.inner x v v ≤ h.inner x v v := by
  obtain ⟨c, hc, hbound⟩ :=
    metric_lower_on (I := I) (M := M) isCompact_univ h gRef
  exact ⟨c, hc, fun x v => hbound x (Set.mem_univ x) v⟩

end DifferentialGeometry

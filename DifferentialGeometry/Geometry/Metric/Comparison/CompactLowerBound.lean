import DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import DifferentialGeometry.Analysis.FunctionalAnalysis.BilinearCoercivity
import DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric

set_option autoImplicit false

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

omit [SigmaCompactSpace M] in
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
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
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
        rw [(h.inner x).map_zero, zero_apply]
      have hg00 : gRef.inner x (0 : TangentSpace I x) 0 = 0 := by
        rw [(gRef.inner x).map_zero, zero_apply]
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
        rw [(h.inner x).map_zero, zero_apply]
      have hg00 : gRef.inner x (0 : TangentSpace I x) 0 = 0 := by
        rw [(gRef.inner x).map_zero, zero_apply]
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
        change x ∈ K
        exact hx⟩

omit [SigmaCompactSpace M] in
theorem metric_lower_bound_of_compact [CompactSpace M]
    (h gRef : SmoothRiemannianMetric I M) :
    ∃ c : Real, 0 < c ∧
      ∀ (x : M) (v : TangentSpace I x), c * gRef.inner x v v ≤ h.inner x v v := by
  obtain ⟨c, hc, hbound⟩ :=
    metric_lower_on (I := I) (M := M) isCompact_univ h gRef
  exact ⟨c, hc, fun x v => hbound x (Set.mem_univ x) v⟩

namespace Geometry.Curvature

open Bundle

omit [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem MetricFamilySmoothOn.exists_pos_mul_norm_sq_le_chart_inner
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (hJc : IsCompact J)
    (α : M) {K : Set E} (hK : K ⊆ (extChartAt I α).target)
    (hKc : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ J ×ˢ K, ∀ v : E,
      c * ‖v‖ ^ 2 ≤ (g p.1).inner ((extChartAt I α).symm p.2)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm p.2) v)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm p.2) v) := by
  classical
  let e := trivializationAt E (TangentSpace I) α
  let b : ℝ × E → M := fun p => (extChartAt I α).symm p.2
  let A : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ := fun p =>
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] ℝ) α (b p) α (b p) ((g p.1).inner (b p))
  have hb (p : ℝ × E) (hp : p ∈ J ×ˢ K) : b p ∈ e.baseSet := by
    have hs := (extChartAt I α).map_target (hK hp.2)
    rwa [extChartAt_source] at hs
  have hAeval (p : ℝ × E) (hp : p ∈ J ×ˢ K) (v w : E) :
      A p v w = (g p.1).inner (b p) (e.symmL ℝ (b p) v) (e.symmL ℝ (b p) w) := by
    dsimp only [A]
    have hR : b p ∈ (trivializationAt ℝ (Bundle.Trivial M ℝ) α).baseSet := mem_univ _
    rw [inCoordinates_apply_eq₂ (𝕜 := ℝ)
      (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := TangentSpace I) (E₂ := TangentSpace I) (E₃ := Bundle.Trivial M ℝ)
      (x₀ := α) (x := b p) (ϕ := (g p.1).inner (b p)) (v := v) (w := w)
      (hb p hp) (hb p hp) hR]
    rw [(trivializationAt ℝ (Bundle.Trivial M ℝ) α).coe_linearMapAt_of_mem hR]
    simp only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
    rw [← Bundle.Trivialization.symmL_apply (R := ℝ) e (hb p hp) v,
      ← Bundle.Trivialization.symmL_apply (R := ℝ) e (hb p hp) w]
  have hA : ContinuousOn A (J ×ˢ K) := by
    intro p hp
    let em := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) α
    have hbc : ContinuousWithinAt b (J ×ˢ K) p :=
      ((continuousOn_extChartAt_symm (I := I) α).comp continuousOn_snd
        (fun _ hq => hK hq.2)) p hp
    have ht : D.regular ∈ 𝓝 p.1 := D.regular_isOpen.mem_nhds (hJ hp.1)
    have hmc := (hG.metricCLMSmoothAt (x := b p) ht).continuousAt.comp_continuousWithinAt
      (f := fun q : ℝ × E => (q.1, b q)) (continuousWithinAt_fst.prodMk hbc)
    have hsrc : (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (b p) ((g p.1).inner (b p))) ∈
        em.source := by
      simpa only [em, e, Trivialization.mem_source, hom_trivializationAt_baseSet,
        TangentBundle.trivializationAt_baseSet, Bundle.Trivial.fiberBundle_trivializationAt',
        Bundle.Trivial.trivialization_baseSet, mem_inter_iff, mem_univ, and_true, and_self]
        using hb p hp
    have hc := em.toOpenPartialHomeomorph.continuousAt hsrc
    have hcoord : ContinuousWithinAt (fun q : ℝ × E => em
        (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          (b q) ((g q.1).inner (b q)))) (J ×ˢ K) p :=
      hc.comp_continuousWithinAt (f := fun q : ℝ × E =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          (b q) ((g q.1).inner (b q))) hmc
    exact hcoord.snd
  have hpos : ∀ p ∈ J ×ˢ K, ∀ v : E, v ≠ 0 → 0 < A p v v := by
    intro p hp v hv
    rw [hAeval p hp]
    apply (g p.1).pos
    intro hz
    have hleft := e.continuousLinearMapAt_symmL (R := ℝ) (hb p hp) v
    rw [hz, map_zero] at hleft
    exact hv hleft.symm
  obtain ⟨c, hc, hbound⟩ := exists_pos_mul_norm_sq_le_bilinear_of_isCompact (hJc.prod hKc) A hA hpos
  refine ⟨c, hc, ?_⟩
  intro p hp v
  simpa only [hAeval p hp] using hbound p hp v

end Geometry.Curvature

end DifferentialGeometry

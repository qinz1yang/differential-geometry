import RicciFlower.MaximumPrinciple.TensorWeak
import RicciFlower.Realized.RicciFlow
import RicciFlower.Tensor.RSTensor.QuadraticBounds

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Metric variation bounds for tensor maximum-principle barriers

This file connects compact unit-tangent quadratic-form bounds to the metric
gain input consumed by Hamilton's tensor weak maximum principle.
-/

noncomputable section

namespace RicciFlower
namespace Realized

open Bundle Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]

/-- A uniform metric-relative bound on the metric variation gives the half
metric gain used by Hamilton's positive barrier. -/
private theorem metric_gain_of_quad_bound
    {epsilon delta c C g dg : Real}
    (hepsilon : 0 < epsilon)
    (hC : 0 ≤ C)
    (hdelta_le : delta ≤ 1 / (4 * C + 1))
    (hc_nonneg : 0 ≤ c)
    (hc_le : c ≤ 2 * delta)
    (hg : 0 ≤ g)
    (hdg : |dg| ≤ C * g) :
    (epsilon / 2) * g ≤ epsilon * (g + c * dg) := by
  have hden_pos : 0 < 4 * C + 1 := by nlinarith
  have hCdelta_le : C * delta ≤ C * (1 / (4 * C + 1)) :=
    mul_le_mul_of_nonneg_left hdelta_le hC
  have hCfrac_le : C * (1 / (4 * C + 1)) ≤ 1 / 4 := by
    field_simp [hden_pos.ne']
    nlinarith [hC]
  have hCdelta_quarter : C * delta ≤ 1 / 4 :=
    le_trans hCdelta_le hCfrac_le
  have hCc_le : C * c ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hc_le hC
    nlinarith [h, hCdelta_quarter]
  have hCc_g_le : (C * c) * g ≤ (1 / 2) * g :=
    mul_le_mul_of_nonneg_right hCc_le hg
  have hdg_lower : -(C * g) ≤ dg := (abs_le.mp hdg).1
  have hc_dg_lower : c * (-(C * g)) ≤ c * dg :=
    mul_le_mul_of_nonneg_left hdg_lower hc_nonneg
  have hinside : (1 / 2) * g ≤ g + c * dg := by
    nlinarith [hCc_g_le, hc_dg_lower]
  have hmul := mul_le_mul_of_nonneg_left hinside (le_of_lt hepsilon)
  nlinarith

/-- Fixed-start metric gain from a tensor-valued metric variation whose
quadratic form is compactly bounded on the full raw slab. -/
theorem metricGainAt_of_quadBound
    (G : Real -> SmoothRiemannianMetric I M)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {T t0 deltaRaw : Real}
    (hdeltaRaw : 0 < deltaRaw)
    (hdeltaRawT : t0 + deltaRaw ≤ T)
    (hderiv :
      ∀ delta : Real, 0 < delta -> delta ≤ deltaRaw ->
        ∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
          ∀ x, ∀ v : TangentSpace I x,
            HasDerivWithinAt (fun s : Real => (G s).inner x v v)
              (quad02 (I := I) (M := M) (A t x) v)
              (Set.Icc t0 (t0 + delta)) t)
    [TopologicalSpace (MetricUnitTangentSlab (I := I) (M := M) G t0 (t0 + deltaRaw))]
    (hcompact : IsCompact
      (Set.univ : Set
        (MetricUnitTangentSlab (I := I) (M := M) G t0 (t0 + deltaRaw))))
    (hcont : Continuous
      (fun p : MetricUnitTangentSlab (I := I) (M := M) G t0 (t0 + deltaRaw) =>
        |quad02 (I := I) (M := M)
          (A p.1.1 (MetricUnitTangent.base (I := I) (M := M) p.2))
          (MetricUnitTangent.vec (I := I) (M := M) p.2)|)) :
    ∃ delta0 : Real,
      0 < delta0 ∧ t0 + delta0 ≤ T ∧
        ∀ delta : Real,
          0 < delta ->
          delta ≤ delta0 ->
          ∀ epsilon : Real,
            SmallBarrierEps epsilon ->
            ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
              (∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  HasDerivWithinAt (fun s : Real => (G s).inner x v v)
                    (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
              (∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  (epsilon / 2) * (G t).inner x v v ≤
                    epsilon * ((G t).inner x v v +
                      (delta + t - t0) * metricDeriv t x v)) := by
  obtain ⟨C, hC, hbound⟩ :=
    compactUnitSlab_absBound (I := I) (M := M) G A t0 (t0 + deltaRaw)
      hcompact hcont
  let delta0 : Real := min deltaRaw (1 / (4 * C + 1))
  have hden_pos : 0 < 4 * C + 1 := by nlinarith
  have hrecip_pos : 0 < 1 / (4 * C + 1) := by positivity
  have hdelta0_pos : 0 < delta0 := by
    dsimp [delta0]
    exact lt_min hdeltaRaw hrecip_pos
  have hdelta0_le_raw : delta0 ≤ deltaRaw := by
    dsimp [delta0]
    exact min_le_left _ _
  have hdelta0_le_recip : delta0 ≤ 1 / (4 * C + 1) := by
    dsimp [delta0]
    exact min_le_right _ _
  have hdelta0T : t0 + delta0 ≤ T := by
    have hle : delta0 ≤ deltaRaw := hdelta0_le_raw
    linarith
  refine ⟨delta0, hdelta0_pos, hdelta0T, ?_⟩
  intro delta hdelta hdelta_le epsilon hepsilon
  have hdelta_le_raw : delta ≤ deltaRaw := le_trans hdelta_le hdelta0_le_raw
  have hdelta_le_recip : delta ≤ 1 / (4 * C + 1) :=
    le_trans hdelta_le hdelta0_le_recip
  let metricDeriv : TensorQuadraticFormFamily (I := I) (M := M) :=
    fun t x v => quad02 (I := I) (M := M) (A t x) v
  refine ⟨metricDeriv, ?_, ?_⟩
  · intro t ht x v
    exact hderiv delta hdelta hdelta_le_raw t ht x v
  · intro t ht x v
    have htime_nonneg : 0 ≤ delta + t - t0 := by
      have ht_sub : 0 ≤ t - t0 := sub_nonneg.mpr ht.1
      have hsum : 0 ≤ delta + (t - t0) :=
        add_nonneg (le_of_lt hdelta) ht_sub
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsum
    have htime_le : delta + t - t0 ≤ 2 * delta := by
      have ht_le : t - t0 ≤ delta := by linarith [ht.2]
      linarith
    have hmetric_nonneg : 0 ≤ (G t).inner x v v := by
      by_cases hv : v = 0
      · subst v
        simp
      · exact le_of_lt ((G t).pos x v hv)
    have ht_raw : t ∈ Set.Icc t0 (t0 + deltaRaw) := by
      exact ⟨ht.1, by linarith⟩
    exact metric_gain_of_quad_bound
      (epsilon := epsilon) (delta := delta) (c := delta + t - t0)
      (C := C) (g := (G t).inner x v v)
      (dg := metricDeriv t x v)
      hepsilon.1 hC hdelta_le_recip htime_nonneg htime_le hmetric_nonneg
      (hbound t ht_raw x v)

/-- Ricci-flow all-time derivative specialization of
`metricGainAt_of_quadBound`.

The interval `MetricVariationEquationOn` only gives regular-time derivatives,
so the closed-slab WMP input should use this all-time derivative predicate or a
separate regular-time WMP interface. -/
theorem metricGainAt_of_metricVariationDerivAt
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : RicciTensorField (I := I) (M := M) Real)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {T t0 deltaRaw : Real}
    (hdeltaRaw : 0 < deltaRaw)
    (hdeltaRawT : t0 + deltaRaw ≤ T)
    (hEq : ∀ t, t ∈ Set.Icc t0 (t0 + deltaRaw) ->
      MetricVariationEquationDerivAt (I := I) G Ric t)
    (hA :
      ∀ t, t ∈ Set.Icc t0 (t0 + deltaRaw) ->
        ∀ x, ∀ v : TangentSpace I x,
          quad02 (I := I) (M := M) (A t x) v =
            (-2 : Real) * Ric t x v v)
    [TopologicalSpace
      (MetricUnitTangentSlab (I := I) (M := M) (fun t => G.metric t)
        t0 (t0 + deltaRaw))]
    (hcompact : IsCompact
      (Set.univ : Set
        (MetricUnitTangentSlab (I := I) (M := M) (fun t => G.metric t)
          t0 (t0 + deltaRaw))))
    (hcont : Continuous
      (fun p :
        MetricUnitTangentSlab (I := I) (M := M) (fun t => G.metric t)
          t0 (t0 + deltaRaw) =>
        |quad02 (I := I) (M := M)
          (A p.1.1 (MetricUnitTangent.base (I := I) (M := M) p.2))
          (MetricUnitTangent.vec (I := I) (M := M) p.2)|)) :
    ∃ delta0 : Real,
      0 < delta0 ∧ t0 + delta0 ≤ T ∧
        ∀ delta : Real,
          0 < delta ->
          delta ≤ delta0 ->
          ∀ epsilon : Real,
            SmallBarrierEps epsilon ->
            ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
              (∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  HasDerivWithinAt
                    (fun s : Real => (G.metric s).inner x v v)
                    (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
              (∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  (epsilon / 2) * (G.metric t).inner x v v ≤
                    epsilon * ((G.metric t).inner x v v +
                      (delta + t - t0) * metricDeriv t x v)) := by
  apply metricGainAt_of_quadBound (I := I) (M := M)
    (G := fun t => G.metric t) (A := A)
    (T := T) (t0 := t0) (deltaRaw := deltaRaw)
    hdeltaRaw hdeltaRawT
  · intro delta hdelta hdelta_le t ht x v
    have ht_raw : t ∈ Set.Icc t0 (t0 + deltaRaw) := ⟨ht.1, by linarith [ht.2, hdelta_le]⟩
    have hderiv := hEq t ht_raw x v v
    have hval := hA t ht_raw x v
    rw [hval]
    exact hderiv.hasDerivWithinAt
  · exact hcompact
  · exact hcont

end Realized
end RicciFlower

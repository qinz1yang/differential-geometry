import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Unit

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle DifferentialGeometry.Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
variable [IsManifold I ∞ M]

theorem tensor02_lower_on_of_positive_definite
    {K : Set M} (hK : IsCompact K) (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := ∞) 2)
    (hA : ∀ x : M, x ∈ K → ∀ v : TangentSpace I x, v ≠ 0 →
      0 < quad02 (I := I) (M := M) (A x) v) :
    ∃ c : Real, 0 < c ∧
      ∀ (x : M), x ∈ K → ∀ v : TangentSpace I x,
        c * g.inner x v v ≤ quad02 (I := I) (M := M) (A x) v := by
  classical
  let q : MetricUnitTangent (I := I) (M := M) g → Real := fun p =>
    quad02 (I := I) (M := M)
      (A (MetricUnitTangent.base (I := I) (M := M) p))
      (MetricUnitTangent.vec (I := I) (M := M) p)
  have hq_cont : Continuous q :=
    metricUnit_quadCont (I := I) (M := M) g A
  have hcompact : IsCompact {p : MetricUnitTangent (I := I) (M := M) g |
      MetricUnitTangent.base (I := I) (M := M) p ∈ K} :=
    metricUnitOn_compact (I := I) (M := M) g hK
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  by_cases hne : {p : MetricUnitTangent (I := I) (M := M) g |
      MetricUnitTangent.base (I := I) (M := M) p ∈ K}.Nonempty
  · obtain ⟨p₀, hp₀, hmin⟩ :=
      hcompact.exists_isMinOn hne hq_cont.continuousOn
    let c : Real := q p₀
    have hc : 0 < c := by
      apply hA _ hp₀
      intro hz
      have hu := MetricUnitTangent.unit (I := I) (M := M) p₀
      rw [hz] at hu
      simp at hu
    refine ⟨c, hc, ?_⟩
    intro x hx v
    by_cases hv : v = 0
    · subst hv
      have hzero : quad02 (I := I) (M := M) (A x) (0 : TangentSpace I x) = 0 := by
        with_unfolding_all exact (A x).map_coord_zero (0 : Fin 2) rfl
      rw [hzero, (g.inner x).map_zero]
      simp
    · have hrpos : 0 < g.inner x v v := g.pos x v hv
      let s : Real := Real.sqrt (g.inner x v v)
      have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
      have hsne : s ≠ 0 := ne_of_gt hspos
      have hss : s * s = g.inner x v v := by
        simpa [s, sq] using Real.sq_sqrt hrpos.le
      set u : TangentSpace I x := s⁻¹ • v with hu_def
      have hunit : g.inner x u u = 1 := by
        rw [hu_def, metric_smul2]
        field_simp [hsne]
        linarith [hss]
      let p : MetricUnitTangent (I := I) (M := M) g :=
        ⟨(⟨x, u⟩ : TangentBundle I M), hunit⟩
      have hpK : MetricUnitTangent.base (I := I) (M := M) p ∈ K := by
        simpa [p, MetricUnitTangent.base] using hx
      have hqp : c ≤ q p := (isMinOn_iff.mp hmin) p hpK
      have hqp_eq : q p = s⁻¹ * s⁻¹ * quad02 (I := I) (M := M) (A x) v := by
        change quad02 (I := I) (M := M) (A x) u = _
        rw [hu_def, tensor02_smul2]
      rw [hqp_eq] at hqp
      have hkey : c * (s * s) ≤ quad02 (I := I) (M := M) (A x) v := by
        have hmul := mul_le_mul_of_nonneg_right hqp
          (by positivity : (0 : Real) ≤ s * s)
        calc
          c * (s * s) ≤
              (s⁻¹ * s⁻¹ * quad02 (I := I) (M := M) (A x) v) *
                (s * s) := hmul
          _ = quad02 (I := I) (M := M) (A x) v := by
            field_simp
      rw [hss] at hkey
      exact hkey
  · refine ⟨1, one_pos, ?_⟩
    intro x hx v
    by_cases hv : v = 0
    · subst hv
      have hzero : quad02 (I := I) (M := M) (A x) (0 : TangentSpace I x) = 0 := by
        with_unfolding_all exact (A x).map_coord_zero (0 : Fin 2) rfl
      rw [hzero, (g.inner x).map_zero]
      simp
    · exfalso
      have hrpos : 0 < g.inner x v v := g.pos x v hv
      let s : Real := Real.sqrt (g.inner x v v)
      have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
      have hunit : g.inner x (s⁻¹ • v) (s⁻¹ • v) = 1 := by
        rw [metric_smul2]
        have hss : s * s = g.inner x v v := by
          simpa [s, sq] using Real.sq_sqrt hrpos.le
        field_simp [ne_of_gt hspos]
        linarith [hss]
      exact hne ⟨⟨(⟨x, s⁻¹ • v⟩ : TangentBundle I M), hunit⟩, by
        change x ∈ K
        exact hx⟩

end DifferentialGeometry

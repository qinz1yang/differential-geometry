import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.AdaptedField
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] in
omit [SigmaCompactSpace M] in
theorem lRegIndex_trace_linear_cutoff
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M)
    (P : Fin (Module.finrank Real E) → ∀ s, TangentSpace I (alpha s))
    (a b : Real) (hab : a < b)
    (ht : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ Set.Icc a b,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha s)
    (hP : ∀ i s, s ∈ Set.Icc a b →
      DifferentiableAt Real (chartRepAt (I := I) alpha (P i) s) s)
    (hDP : ∀ i, IsLAdapted S T alpha (P i) (Set.Icc a b))
    (hON : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (alpha b) (P i b) (P j b) =
        if i = j then 1 else 0)
    (hIint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ ((s - a) / (b - a)) ^ 2 *
        lRegIndexIntegrand S T alpha (P i) (P i) s)
      MeasureTheory.volume a b)
    (hRint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (2 * s * (s - a) / (b - a) ^ 2) *
        S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s)))
      MeasureTheory.volume a b) :
    ∑ i : Fin (Module.finrank Real E),
        lRegIndex S T alpha (fun s ↦ ((s - a) / (b - a)) • P i s)
          (fun s ↦ ((s - a) / (b - a)) • P i s) a b =
      (Module.finrank Real E : Real) / (2 * (b - a)) +
        ∫ s in a..b,
          (((s - a) / (b - a)) ^ 2 *
              ∑ i : Fin (Module.finrank Real E),
                lRegIndexIntegrand S T alpha (P i) (P i) s) -
            (2 * s * (s - a) / (b - a) ^ 2) *
              S.scalar (T - s ^ 2) (alpha s) := by
  classical
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hONs (s : Real) (hs : s ∈ Set.Icc a b)
      (i j : Fin (Module.finrank Real E)) :
      (S.base.metric (T - s ^ 2)).inner (alpha s) (P i s) (P j s) =
        if i = j then 1 else 0 := by
    rw [metric_inner_eq_of_isLAdapted (I := I) S hS T alpha (P i) (P j) hs.2
      (fun r hr ↦ ht r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ halpha r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hP i r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hP j r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hDP i r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hDP j r ⟨le_trans hs.1 hr.1, hr.2⟩)]
    exact hON i j
  have hRic (s : Real) (hs : s ∈ Set.Icc a b) :
      ∑ i : Fin (Module.finrank Real E),
          S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s)) =
        S.scalar (T - s ^ 2) (alpha s) := by
    let g := S.base.metric (T - s ^ 2)
    let x := alpha s
    calc
      ∑ i : Fin (Module.finrank Real E),
          S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s)) =
          ∑ i : Fin (Module.finrank Real E),
            ricciTensor (I := I) g x (P i s) (P i s) := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              exact metricRicciAt_apply_eq_ricciTensor (I := I) g x (P i s) (P i s)
      _ = scalarCurv (I := I) g x :=
        (scalarCurv_eq_orthonormal_trace (I := I) g x (fun i ↦ P i s)
          (hONs s hs)).symm
      _ = metricScalarAt (I := I) g x :=
        (metricScalar_eq_scal (I := I) g x).symm
      _ = S.scalar (T - s ^ 2) (alpha s) := rfl
  have hidx (i : Fin (Module.finrank Real E)) :
      lRegIndex S T alpha (fun s ↦ ((s - a) / (b - a)) • P i s)
          (fun s ↦ ((s - a) / (b - a)) • P i s) a b =
        (1 / (2 * (b - a))) *
            (S.base.metric (T - b ^ 2)).inner (alpha b) (P i b) (P i b) +
          ∫ s in a..b,
            (((s - a) / (b - a)) ^ 2 *
                lRegIndexIntegrand S T alpha (P i) (P i) s -
              (2 * s * (s - a) / (b - a) ^ 2) *
                S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s))) := by
    let f : Real → Real := fun s ↦ (s - a) / (b - a)
    let F : Real → Real := fun s ↦
      ((s - a) / (b - a)) ^ 2 * lRegIndexIntegrand S T alpha (P i) (P i) s
    let N : Real → Real := fun s ↦
      (1 / (2 * (b - a) ^ 2)) *
        (S.base.metric (T - s ^ 2)).inner (alpha s) (P i s) (P i s)
    let R : Real → Real := fun s ↦
      (2 * s * (s - a) / (b - a) ^ 2) *
        S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s))
    have hpt : ∀ s ∈ Set.uIcc a b,
        lRegIndexIntegrand S T alpha (fun r ↦ f r • P i r)
            (fun r ↦ f r • P i r) s = F s + N s - R s := by
      intro s hs
      have hs' : s ∈ Set.Icc a b := by
        simpa only [Set.uIcc_of_le hab.le] using hs
      have hf : DifferentiableAt Real f s := by
        exact (((hasDerivAt_id s).sub_const a).div_const (b - a)).differentiableAt
      have hderiv : deriv f s = 1 / (b - a) := by
        exact (((hasDerivAt_id s).sub_const a).div_const (b - a)).deriv
      have hbase := lRegIndexIntegrand_smul_function_self_of_isLAdaptedAt (I := I) S T alpha (P i) f s hf
        (hP i s hs') (hDP i s hs')
      rw [hbase, hderiv]
      dsimp only [f, F, N, R]
      field_simp [hba]
    have hNconst : ∀ s ∈ Set.uIcc a b, N s = N b := by
      intro s hs
      have hs' : s ∈ Set.Icc a b := by
        simpa only [Set.uIcc_of_le hab.le] using hs
      have hpair := metric_inner_eq_of_isLAdapted (I := I) S hS T alpha (P i) (P i) hs'.2
        (fun r hr ↦ ht r ⟨le_trans hs'.1 hr.1, hr.2⟩)
        (fun r hr ↦ halpha r ⟨le_trans hs'.1 hr.1, hr.2⟩)
        (fun r hr ↦ hP i r ⟨le_trans hs'.1 hr.1, hr.2⟩)
        (fun r hr ↦ hP i r ⟨le_trans hs'.1 hr.1, hr.2⟩)
        (fun r hr ↦ hDP i r ⟨le_trans hs'.1 hr.1, hr.2⟩)
        (fun r hr ↦ hDP i r ⟨le_trans hs'.1 hr.1, hr.2⟩)
      dsimp only [N]
      rw [hpair]
    have hNint : IntervalIntegrable N MeasureTheory.volume a b := by
      rw [intervalIntegrable_congr (f := N) (g := fun _ : Real ↦ N b) (by
        intro s hs
        exact hNconst s (Set.uIoc_subset_uIcc hs))]
      exact intervalIntegrable_const
    have hNintegral :
        (∫ s in a..b, N s) =
          (1 / (2 * (b - a))) *
            (S.base.metric (T - b ^ 2)).inner (alpha b) (P i b) (P i b) := by
      calc
        (∫ s in a..b, N s) = ∫ _s in a..b, N b :=
          intervalIntegral.integral_congr hNconst
        _ = (1 / (2 * (b - a))) *
            (S.base.metric (T - b ^ 2)).inner (alpha b) (P i b) (P i b) := by
          simp only [intervalIntegral.integral_const, smul_eq_mul, N]
          field_simp [hba]
    unfold lRegIndex
    change (∫ s in a..b,
      lRegIndexIntegrand S T alpha (fun r ↦ f r • P i r)
        (fun r ↦ f r • P i r) s) = _
    rw [intervalIntegral.integral_congr hpt]
    rw [intervalIntegral.integral_sub ((hIint i).add hNint) (hRint i),
      intervalIntegral.integral_add (hIint i) hNint,
      intervalIntegral.integral_sub (hIint i) (hRint i), hNintegral]
    ring
  rw [Finset.sum_congr rfl (fun i _ ↦ hidx i)]
  rw [Finset.sum_add_distrib]
  have hint (i : Fin (Module.finrank Real E)) : IntervalIntegrable
      (fun s : Real ↦
        ((s - a) / (b - a)) ^ 2 * lRegIndexIntegrand S T alpha (P i) (P i) s -
          (2 * s * (s - a) / (b - a) ^ 2) *
            S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s)))
      MeasureTheory.volume a b :=
    (hIint i).sub (hRint i)
  rw [← intervalIntegral.integral_finsetSum
    (s := (Finset.univ : Finset (Fin (Module.finrank Real E))))
    (f := fun i s ↦
      ((s - a) / (b - a)) ^ 2 * lRegIndexIntegrand S T alpha (P i) (P i) s -
        (2 * s * (s - a) / (b - a) ^ 2) *
          S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s)))
    (fun i _ ↦ hint i)]
  apply congrArg₂ (· + ·)
  · simp_rw [hON, if_pos]
    rw [Finset.sum_const, Finset.card_fin]
    simp only [nsmul_eq_mul]
    field_simp [hba]
  · apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Set.Icc a b := by
      simpa only [Set.uIcc_of_le hab.le] using hs
    dsimp only
    calc
      ∑ i : Fin (Module.finrank Real E),
          (((s - a) / (b - a)) ^ 2 * lRegIndexIntegrand S T alpha (P i) (P i) s -
            (2 * s * (s - a) / (b - a) ^ 2) *
              S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s))) =
          ((s - a) / (b - a)) ^ 2 *
              ∑ i : Fin (Module.finrank Real E),
                lRegIndexIntegrand S T alpha (P i) (P i) s -
            (2 * s * (s - a) / (b - a) ^ 2) *
              ∑ i : Fin (Module.finrank Real E),
                S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s)) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = ((s - a) / (b - a)) ^ 2 *
              ∑ i : Fin (Module.finrank Real E),
                lRegIndexIntegrand S T alpha (P i) (P i) s -
            (2 * s * (s - a) / (b - a) ^ 2) *
              S.scalar (T - s ^ 2) (alpha s) := by
          rw [hRic s hs']

omit [InnerProductSpace Real E] in
omit [SigmaCompactSpace M] in
theorem lRegIndex_trace_linear_cutoff_zero
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M)
    (P : Fin (Module.finrank Real E) → ∀ s, TangentSpace I (alpha s))
    (b : Real) (hb : 0 < b)
    (ht : ∀ s ∈ Set.Icc (0 : Real) b, T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ Set.Icc (0 : Real) b,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha s)
    (hP : ∀ i s, s ∈ Set.Icc (0 : Real) b →
      DifferentiableAt Real (chartRepAt (I := I) alpha (P i) s) s)
    (hDP : ∀ i, IsLAdapted S T alpha (P i) (Set.Icc (0 : Real) b))
    (hON : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (alpha b) (P i b) (P j b) =
        if i = j then 1 else 0)
    (hIint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (s / b) ^ 2 * lRegIndexIntegrand S T alpha (P i) (P i) s)
      MeasureTheory.volume 0 b)
    (hRint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (2 * s ^ 2 / b ^ 2) *
        S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s)))
      MeasureTheory.volume 0 b) :
    ∑ i : Fin (Module.finrank Real E),
        lRegIndex S T alpha (fun s ↦ (s / b) • P i s)
          (fun s ↦ (s / b) • P i s) 0 b =
      (Module.finrank Real E : Real) / (2 * b) +
        ∫ s in (0 : Real)..b,
          ((s / b) ^ 2 *
              ∑ i : Fin (Module.finrank Real E),
                lRegIndexIntegrand S T alpha (P i) (P i) s) -
            (2 * s ^ 2 / b ^ 2) * S.scalar (T - s ^ 2) (alpha s) := by
  have hIint' : ∀ i, IntervalIntegrable
      (fun s : Real ↦ ((s - 0) / (b - 0)) ^ 2 *
        lRegIndexIntegrand S T alpha (P i) (P i) s)
      MeasureTheory.volume 0 b := by
    intro i
    simpa using hIint i
  have hRint' : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (2 * s * (s - 0) / (b - 0) ^ 2) *
        S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s)))
      MeasureTheory.volume 0 b := by
    intro i
    convert hRint i using 1
    funext s
    ring
  calc
    ∑ i : Fin (Module.finrank Real E),
          lRegIndex S T alpha (fun s ↦ (s / b) • P i s)
            (fun s ↦ (s / b) • P i s) 0 b =
        (Module.finrank Real E : Real) / (2 * b) +
          ∫ s in (0 : Real)..b,
            ((s / b) ^ 2 *
                ∑ i : Fin (Module.finrank Real E),
                  lRegIndexIntegrand S T alpha (P i) (P i) s) -
              (2 * s * s / b ^ 2) * S.scalar (T - s ^ 2) (alpha s) := by
        simpa only [sub_zero] using
          lRegIndex_trace_linear_cutoff (I := I) S hS T alpha P 0 b hb ht halpha hP
            hDP hON hIint' hRint'
    _ = (Module.finrank Real E : Real) / (2 * b) +
          ∫ s in (0 : Real)..b,
            ((s / b) ^ 2 *
                ∑ i : Fin (Module.finrank Real E),
                  lRegIndexIntegrand S T alpha (P i) (P i) s) -
              (2 * s ^ 2 / b ^ 2) * S.scalar (T - s ^ 2) (alpha s) := by
        apply congrArg ((Module.finrank Real E : Real) / (2 * b) + ·)
        apply intervalIntegral.integral_congr
        intro s _
        ring

end DifferentialGeometry.PDE.RicciFlow.Perelman

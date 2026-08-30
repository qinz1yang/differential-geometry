import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.AdaptedField
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Algebra
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentity
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile

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

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] in
omit [SigmaCompactSpace M] in
theorem lIndex_smul_pt
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (P : ∀ s, TangentSpace I (alpha s))
    (f : Real → Real) (s : Real)
    (hf : DifferentiableAt Real f s)
    (hP : DifferentiableAt Real (chartRepAt (I := I) alpha P s) s)
    (hDP : covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha P s =
      (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
        (alpha s) (P s)) :
    lRegIndexInt S T alpha (fun r ↦ f r • P r)
        (fun r ↦ f r • P r) s =
      (f s) ^ 2 * lRegIndexInt S T alpha P P s +
        (1 / 2 : Real) * (deriv f s) ^ 2 *
          (S.base.metric (T - s ^ 2)).inner (alpha s) (P s) (P s) -
        2 * s * f s * deriv f s *
          S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P s) (P s)) := by
  let g := S.base.metric (T - s ^ 2)
  let c : Real := f s
  let q : Real := deriv f s
  let W : ∀ r, TangentSpace I (alpha r) := fun r ↦ f r • P r
  let Q : ∀ r, TangentSpace I (alpha r) := fun r ↦ c • P r
  have hcovW : covDerivAlong (I := I) g alpha W s =
      q • P s + c • covDerivAlong (I := I) g alpha P s := by
    rw [covDerivAlong_smulFun (I := I) g alpha f P s hf hP]
  have hcovQ : covDerivAlong (I := I) g alpha Q s =
      c • covDerivAlong (I := I) g alpha P s := by
    exact covDerivAlong_smul (I := I) g alpha c P s
  have hQ : lRegIndexInt S T alpha Q Q s =
      c ^ 2 * lRegIndexInt S T alpha P P s := by
    calc
      lRegIndexInt S T alpha Q Q s =
          c * lRegIndexInt S T alpha P Q s :=
        lRegIndexInt_smul (I := I) S T c alpha P Q s
      _ = c * lRegIndexInt S T alpha Q P s := by
        rw [lRegIndexInt_symm (I := I) S T alpha P Q s]
      _ = c * (c * lRegIndexInt S T alpha P P s) := by
        rw [lRegIndexInt_smul (I := I) S T c alpha P P s]
      _ = c ^ 2 * lRegIndexInt S T alpha P P s := by ring
  have hWQ : lRegIndexInt S T alpha W W s =
      lRegIndexInt S T alpha Q Q s +
        (1 / 2 : Real) *
          (g.inner (alpha s)
              (q • P s + c • covDerivAlong (I := I) g alpha P s)
              (q • P s + c • covDerivAlong (I := I) g alpha P s) -
            g.inner (alpha s)
              (c • covDerivAlong (I := I) g alpha P s)
              (c • covDerivAlong (I := I) g alpha P s)) := by
    simp only [lRegIndexInt]
    rw [hcovW, hcovQ]
    have hWval : W s = Q s := by rfl
    rw [hWval]
    ring
  rw [hWQ, hQ, hDP]
  simp only [map_add, add_apply, map_smul,
    smul_apply, smul_eq_mul]
  rw [inner_ricciSharp, inner_ricciSharp_right]
  rw [← metricRicciAt_apply_eq_ricciTensor]
  dsimp only [c, q, g, W, Q, SolutionOn.ricciAt, SolutionFamily.ricciAt]
  ring

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] in
omit [SigmaCompactSpace M] in
theorem lIndex_adapted_pt
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (P : ∀ s, TangentSpace I (alpha s))
    (b s : Real) (hb : b ≠ 0)
    (hP : DifferentiableAt Real (chartRepAt (I := I) alpha P s) s)
    (hDP : covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha P s =
      (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
        (alpha s) (P s)) :
    lRegIndexInt S T alpha (fun r ↦ (r / b) • P r)
        (fun r ↦ (r / b) • P r) s =
      (s / b) ^ 2 * lRegIndexInt S T alpha P P s +
        (1 / (2 * b ^ 2)) *
          (S.base.metric (T - s ^ 2)).inner (alpha s) (P s) (P s) -
        (2 * s ^ 2 / b ^ 2) *
          S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P s) (P s)) := by
  let g := S.base.metric (T - s ^ 2)
  let c : Real := s / b
  let q : Real := 1 / b
  let W : ∀ r, TangentSpace I (alpha r) := fun r ↦ (r / b) • P r
  let Q : ∀ r, TangentSpace I (alpha r) := fun r ↦ c • P r
  have hf : DifferentiableAt Real (fun r : Real ↦ r / b) s := by
    fun_prop
  have hderiv : deriv (fun r : Real ↦ r / b) s = q := by
    simpa only [id_eq, q] using (hasDerivAt_id s).div_const b |>.deriv
  have hcovW : covDerivAlong (I := I) g alpha W s =
      q • P s + c • covDerivAlong (I := I) g alpha P s := by
    rw [covDerivAlong_smulFun (I := I) g alpha (fun r : Real ↦ r / b) P s hf hP]
    rw [hderiv]
  have hcovQ : covDerivAlong (I := I) g alpha Q s =
      c • covDerivAlong (I := I) g alpha P s := by
    exact covDerivAlong_smul (I := I) g alpha c P s
  have hQ : lRegIndexInt S T alpha Q Q s =
      c ^ 2 * lRegIndexInt S T alpha P P s := by
    calc
      lRegIndexInt S T alpha Q Q s =
          c * lRegIndexInt S T alpha P Q s :=
        lRegIndexInt_smul (I := I) S T c alpha P Q s
      _ = c * lRegIndexInt S T alpha Q P s := by
        rw [lRegIndexInt_symm (I := I) S T alpha P Q s]
      _ = c * (c * lRegIndexInt S T alpha P P s) := by
        rw [lRegIndexInt_smul (I := I) S T c alpha P P s]
      _ = c ^ 2 * lRegIndexInt S T alpha P P s := by ring
  have hWQ : lRegIndexInt S T alpha W W s =
      lRegIndexInt S T alpha Q Q s +
        (1 / 2 : Real) *
          (g.inner (alpha s)
              (q • P s + c • covDerivAlong (I := I) g alpha P s)
              (q • P s + c • covDerivAlong (I := I) g alpha P s) -
            g.inner (alpha s)
              (c • covDerivAlong (I := I) g alpha P s)
              (c • covDerivAlong (I := I) g alpha P s)) := by
    simp only [lRegIndexInt]
    rw [hcovW, hcovQ]
    have hWval : W s = Q s := by rfl
    rw [hWval]
    ring
  rw [hWQ, hQ, hDP]
  simp only [map_add, add_apply, map_smul,
    smul_apply, smul_eq_mul]
  rw [inner_ricciSharp, inner_ricciSharp_right]
  rw [← metricRicciAt_apply_eq_ricciTensor]
  dsimp only [c, q, g, W, Q, SolutionOn.ricciAt, SolutionFamily.ricciAt]
  field_simp [hb]
  ring

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)] in
omit [SigmaCompactSpace M] in
theorem lIndex_adapted
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (P : ∀ s, TangentSpace I (alpha s))
    (b : Real) (hb : 0 < b)
    (ht : ∀ s ∈ Set.Icc (0 : Real) b, T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ Set.Icc (0 : Real) b,
      MDifferentiableAt 𝓘(Real, Real) I alpha s)
    (hP : ∀ s ∈ Set.Icc (0 : Real) b,
      DifferentiableAt Real (chartRepAt (I := I) alpha P s) s)
    (hDP : ∀ s ∈ Set.Icc (0 : Real) b,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha P s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (alpha s) (P s))
    (hIint : IntervalIntegrable
      (fun s : Real ↦ (s / b) ^ 2 * lRegIndexInt S T alpha P P s)
      MeasureTheory.volume 0 b)
    (hRint : IntervalIntegrable
      (fun s : Real ↦ (2 * s ^ 2 / b ^ 2) *
        S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P s) (P s)))
      MeasureTheory.volume 0 b) :
    lRegIndex S T alpha (fun s ↦ (s / b) • P s)
        (fun s ↦ (s / b) • P s) 0 b =
      (1 / (2 * b)) *
          (S.base.metric (T - b ^ 2)).inner (alpha b) (P b) (P b) +
        ∫ s in (0 : Real)..b,
          ((s / b) ^ 2 * lRegIndexInt S T alpha P P s -
            (2 * s ^ 2 / b ^ 2) *
              S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P s) (P s))) := by
  let F : Real → Real := fun s ↦
    (s / b) ^ 2 * lRegIndexInt S T alpha P P s
  let N : Real → Real := fun s ↦
    (1 / (2 * b ^ 2)) *
      (S.base.metric (T - s ^ 2)).inner (alpha s) (P s) (P s)
  let R : Real → Real := fun s ↦
    (2 * s ^ 2 / b ^ 2) *
      S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P s) (P s))
  have hpt : ∀ s ∈ Set.uIcc (0 : Real) b,
      lRegIndexInt S T alpha (fun r ↦ (r / b) • P r)
          (fun r ↦ (r / b) • P r) s = F s + N s - R s := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : Real) b := by
      simpa only [Set.uIcc_of_le hb.le] using hs
    simpa only [F, N, R] using
      lIndex_adapted_pt (I := I) S T alpha P b s hb.ne' (hP s hs') (hDP s hs')
  have hNconst : ∀ s ∈ Set.uIcc (0 : Real) b, N s = N b := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : Real) b := by
      simpa only [Set.uIcc_of_le hb.le] using hs
    have hpair := lAdapted_inner_eq (I := I) S hS T alpha P P hs'.2
      (fun r hr ↦ ht r ⟨le_trans hs'.1 hr.1, hr.2⟩)
      (fun r hr ↦ halpha r ⟨le_trans hs'.1 hr.1, hr.2⟩)
      (fun r hr ↦ hP r ⟨le_trans hs'.1 hr.1, hr.2⟩)
      (fun r hr ↦ hP r ⟨le_trans hs'.1 hr.1, hr.2⟩)
      (fun r hr ↦ hDP r ⟨le_trans hs'.1 hr.1, hr.2⟩)
      (fun r hr ↦ hDP r ⟨le_trans hs'.1 hr.1, hr.2⟩)
    dsimp only [N]
    rw [hpair]
  have hNint : IntervalIntegrable N MeasureTheory.volume 0 b := by
    rw [intervalIntegrable_congr (f := N) (g := fun _ : Real ↦ N b) (by
      intro s hs
      exact hNconst s (Set.uIoc_subset_uIcc hs))]
    exact intervalIntegrable_const
  have hNintegral :
      (∫ s in (0 : Real)..b, N s) =
        (1 / (2 * b)) *
          (S.base.metric (T - b ^ 2)).inner (alpha b) (P b) (P b) := by
    calc
      (∫ s in (0 : Real)..b, N s) = ∫ _s in (0 : Real)..b, N b :=
        intervalIntegral.integral_congr hNconst
      _ = (1 / (2 * b)) *
          (S.base.metric (T - b ^ 2)).inner (alpha b) (P b) (P b) := by
        simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, N]
        field_simp [hb.ne']
  unfold lRegIndex
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_sub (hIint.add hNint) hRint,
    intervalIntegral.integral_add hIint hNint,
    intervalIntegral.integral_sub hIint hRint, hNintegral]
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman

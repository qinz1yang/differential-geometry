import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
private theorem metricRicciAt_le_half_scalar_of_unit
    (g : SmoothRiemannianMetric I M) (x : M)
    (hR : metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (u : TangentSpace I x) (hu : g.inner x u u = 1) :
    0 ≤ metricRicciAt (I := I) (M := M) g x (vec2 u u) ∧
      metricRicciAt (I := I) (M := M) g x (vec2 u u) ≤
        metricScalarAt (I := I) (M := M) g x / 2 := by
  classical
  let D := (tangentMetricData (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x)
      _ _ _ D.toCore
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  have huInner : Inner.inner Real u u = 1 := by
    calc
      Inner.inner Real u u = D.inner u u :=
        MetricFiberData.toCore_inner D u u
      _ = g.inner x u u :=
        TangentMetricData.inner_eq
          (tangentMetricData (I := I) g x) u u
      _ = 1 := hu
  have huON : Orthonormal Real ((↑) : ({u} : Set (TangentSpace I x)) →
      TangentSpace I x) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (i : TangentSpace I x) = u := i.2
    have hj : (j : TangentSpace I x) = u := j.2
    have hij : i = j := Subtype.ext (hi.trans hj.symm)
    rw [hi, hj, huInner, if_pos hij]
  obtain ⟨s, orthBasis, hus, horthBasis⟩ := huON.exists_orthonormalBasis_extension
  let basis := orthBasis.toBasis
  let iu : s := ⟨u, hus (Set.mem_singleton u)⟩
  have hbasis (i : s) : basis i = (i : TangentSpace I x) := by
    exact congrFun horthBasis i
  have hbu : basis iu = u := by rw [hbasis]
  have hON : ∀ i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0 := by
    intro i j
    rw [← TangentMetricData.inner_eq (tangentMetricData (I := I) g x)]
    change D.inner (basis i) (basis j) = _
    rw [← MetricFiberData.toCore_inner D]
    exact orthonormal_iff_ite.mp orthBasis.orthonormal i j
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := s)) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  let K := metricCurvatureSections (I := I) (M := M) g
  have hLower : Rm04LowersRm13At (I := I) g x
      (metricRm13 (I := I) (M := M) g x)
      (metricRm04 (I := I) (M := M) g x) :=
    rm04LowersRm13At_of_realizes (I := I) g
      (metricCov (I := I) (M := M) g)
      (metricRm13 (I := I) (M := M) g)
      (metricRm04 (I := I) (M := M) g)
      K.rm13Realizes K.rm04Realizes x
  have hRicTrace : ∀ i j,
      metricRicciAt (I := I) (M := M) g x
          (vec2 (basis i) (basis j)) =
        ∑ a, metricRm04At (I := I) (M := M) g x
          (vec4 (basis a) (basis i) (basis j) (basis a)) := by
    intro i j
    simpa using ricci_diag_eq_sum_rm04_diag_of_orthonormal
      (I := I) (M := M) g basis
      (metricRicci (I := I) (M := M) g)
      (metricRm13 (I := I) (M := M) g)
      (metricRm04 (I := I) (M := M) g)
      K.ricciRealizes hLower hON i j
  have hsec : ∀ i j : s, 0 ≤
      metricRm04At (I := I) (M := M) g x
        (vec4 (basis j) (basis i) (basis i) (basis j)) := by
    intro i j
    have h :=
      (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (I := I) (M := M) g x).mp hR 1 (fun _ => 1)
        (fun _ => basis j) (fun _ => basis i)
    simpa [metricRm04StandardAt_apply, vec4] using h
  have hscalar : metricScalarAt (I := I) (M := M) g x =
      ∑ i, metricRicciAt (I := I) (M := M) g x
        (vec2 (basis i) (basis i)) := by
    calc
      metricScalarAt (I := I) (M := M) g x =
          DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I) g
            (metricRicciAt (I := I) (M := M) g x) :=
        metricScalarAt_def (I := I) g x
      _ = ∑ i, metricRicciAt (I := I) (M := M) g x
          (vec2 (basis i) (basis i)) := by
        rw [DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis
          (I := I) g basis (identityInvMetric (Idx := s)) hinv]
        simp [identityInvMetric, diagonalInvMetric]
  have hrowLower : ∀ i : s,
      metricRm04At (I := I) (M := M) g x
          (vec4 (basis iu) (basis i) (basis i) (basis iu)) ≤
        metricRicciAt (I := I) (M := M) g x
          (vec2 (basis i) (basis i)) := by
    intro i
    rw [hRicTrace i i]
    exact Finset.single_le_sum (fun j _ => hsec i j) (Finset.mem_univ iu)
  have hpair : ∀ i : s,
      metricRm04At (I := I) (M := M) g x
          (vec4 (basis iu) (basis i) (basis i) (basis iu)) =
        metricRm04At (I := I) (M := M) g x
          (vec4 (basis i) (basis iu) (basis iu) (basis i)) := by
    intro i
    exact (mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (M := M) g x)).pair_swap _ _ _ _
  have hdiag : metricRm04At (I := I) (M := M) g x
      (vec4 (basis iu) (basis iu) (basis iu) (basis iu)) = 0 := by
    have hanti := (mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (M := M) g x)).anti_first
        (basis iu) (basis iu) (basis iu) (basis iu)
    have hanti' : metricRm04At (I := I) (M := M) g x
        (vec4 (basis iu) (basis iu) (basis iu) (basis iu)) =
        -metricRm04At (I := I) (M := M) g x
          (vec4 (basis iu) (basis iu) (basis iu) (basis iu)) := by
      simpa [tensor04StandardAt, vec4] using hanti
    linarith
  have hcomplement : metricRicciAt (I := I) (M := M) g x
        (vec2 u u) ≤
      ∑ i ∈ (Finset.univ.erase iu),
        metricRicciAt (I := I) (M := M) g x
          (vec2 (basis i) (basis i)) := by
    have hsum := Finset.sum_le_sum (s := Finset.univ.erase iu)
      (fun i _ => hrowLower i)
    have hricu : metricRicciAt (I := I) (M := M) g x (vec2 u u) =
        ∑ i ∈ (Finset.univ.erase iu),
          metricRm04At (I := I) (M := M) g x
            (vec4 (basis iu) (basis i) (basis i) (basis iu)) := by
      rw [← hbu, hRicTrace iu iu]
      have hsplit := Finset.sum_erase_add (Finset.univ : Finset s)
        (fun i => metricRm04At (I := I) (M := M) g x
          (vec4 (basis i) (basis iu) (basis iu) (basis i)))
        (Finset.mem_univ iu)
      rw [hdiag, add_zero] at hsplit
      rw [← hsplit]
      apply Finset.sum_congr rfl
      intro i _
      exact (hpair i).symm
    rw [← hricu] at hsum
    exact hsum
  constructor
  · rw [← hbu, hRicTrace iu iu]
    exact Finset.sum_nonneg fun i _ => hsec iu i
  · rw [hscalar]
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset s)
      (fun i => metricRicciAt (I := I) (M := M) g x
        (vec2 (basis i) (basis i))) (Finset.mem_univ iu)
    rw [hbu] at hsplit
    rw [← hsplit]
    linarith

omit [SigmaCompactSpace M] in
theorem metricRicciAt_le_half_scalar_mul_inner_of_curvatureOperator_nonnegative
    (g : SmoothRiemannianMetric I M) (x : M)
    (hR : metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (v : TangentSpace I x) :
    metricRicciAt (I := I) (M := M) g x (vec2 v v) ≤
      (metricScalarAt (I := I) (M := M) g x / 2) * g.inner x v v := by
  by_cases hv : v = 0
  · subst v
    have hzero : metricRicciAt (I := I) (M := M) g x
        (vec2 (0 : TangentSpace I x) 0) = 0 := by
      exact (metricRicciAt (I := I) (M := M) g x).map_coord_zero
        (i := 0) (by simp [vec2])
    rw [hzero, (g.inner x).map_zero, zero_apply, mul_zero]
  · have hpos : 0 < g.inner x v v := g.pos x v hv
    let r := Real.sqrt (g.inner x v v)
    let u := r⁻¹ • v
    have hr : 0 < r := Real.sqrt_pos.mpr hpos
    have hu : g.inner x u u = 1 := by
      dsimp [u]
      rw [(g.inner x).map_smul]
      change r⁻¹ * ((g.inner x v) (r⁻¹ • v)) = 1
      rw [(g.inner x v).map_smul]
      simp only [smul_eq_mul]
      have hrSq : r ^ 2 = g.inner x v v := by
        dsimp [r]
        exact Real.sq_sqrt hpos.le
      rw [← hrSq]
      field_simp [ne_of_gt hr]
    have hunit := (metricRicciAt_le_half_scalar_of_unit
      (I := I) (M := M) g x hR u hu).2
    have hvEq : v = r • u := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
    rw [hvEq]
    have hricScale := tensor02_smul2 (I := I) (M := M)
      (metricRicciAt (I := I) (M := M) g x) r u
    have hricScale' : metricRicciAt (I := I) (M := M) g x
        (vec2 (r • u) (r • u)) =
        r * r * metricRicciAt (I := I) (M := M) g x (vec2 u u) := by
      have hru : vec2 (I := I) (r • u) (r • u) =
          fun _ : Fin 2 => r • u := by
        funext i
        fin_cases i <;> rfl
      have hu' : vec2 (I := I) u u = fun _ : Fin 2 => u := by
        funext i
        fin_cases i <;> rfl
      rw [hru, hu']
      simpa [quad02] using hricScale
    rw [hricScale']
    have hinnerScale : g.inner x (r • u) (r • u) = r ^ 2 := by
      rw [(g.inner x).map_smul]
      change r * ((g.inner x u) (r • u)) = r ^ 2
      rw [(g.inner x u).map_smul]
      simp [smul_eq_mul, hu, pow_two]
    rw [hinnerScale]
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hunit (sq_nonneg r)

omit [SigmaCompactSpace M] in
theorem metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    (g : SmoothRiemannianMetric I M) (x : M)
    (hR : metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (v : TangentSpace I x) :
    0 ≤ metricRicciAt (I := I) (M := M) g x (vec2 v v) := by
  by_cases hv : v = 0
  · subst v
    exact le_of_eq ((metricRicciAt (I := I) (M := M) g x).map_coord_zero
      (i := 0) (by simp [vec2])).symm
  · have hpos : 0 < g.inner x v v := g.pos x v hv
    let r := Real.sqrt (g.inner x v v)
    let u := r⁻¹ • v
    have hr : 0 < r := Real.sqrt_pos.mpr hpos
    have hu : g.inner x u u = 1 := by
      dsimp [u]
      rw [(g.inner x).map_smul]
      change r⁻¹ * ((g.inner x v) (r⁻¹ • v)) = 1
      rw [(g.inner x v).map_smul]
      simp only [smul_eq_mul]
      have hrSq : r ^ 2 = g.inner x v v := by
        dsimp [r]
        exact Real.sq_sqrt hpos.le
      rw [← hrSq]
      field_simp [ne_of_gt hr]
    have hunit := (metricRicciAt_le_half_scalar_of_unit
      (I := I) (M := M) g x hR u hu).1
    have hvEq : v = r • u := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
    rw [hvEq]
    have hscale := tensor02_smul2 (I := I) (M := M)
      (metricRicciAt (I := I) (M := M) g x) r u
    have hscale' : metricRicciAt (I := I) (M := M) g x
        (vec2 (r • u) (r • u)) =
        r * r * metricRicciAt (I := I) (M := M) g x (vec2 u u) := by
      have hru : vec2 (I := I) (r • u) (r • u) =
          fun _ : Fin 2 => r • u := by
        funext i
        fin_cases i <;> rfl
      have hu' : vec2 (I := I) u u = fun _ : Fin 2 => u := by
        funext i
        fin_cases i <;> rfl
      rw [hru, hu']
      simpa [quad02] using hscale
    rw [hscale']
    exact mul_nonneg (mul_nonneg hr.le hr.le) hunit

omit [SigmaCompactSpace M] in
theorem metricScalarAt_nonnegative_of_curvatureOperator_nonnegative
    (g : SmoothRiemannianMetric I M) (x : M)
    (hR : metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    0 ≤ metricScalarAt (I := I) (M := M) g x := by
  classical
  let D := (tangentMetricData (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x)
      _ _ _ D.toCore
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let orthBasis := stdOrthonormalBasis Real (TangentSpace I x)
  let basis := orthBasis.toBasis
  have hON : ∀ i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0 := by
    intro i j
    rw [← TangentMetricData.inner_eq (tangentMetricData (I := I) g x)]
    change D.inner (orthBasis i) (orthBasis j) = if i = j then (1 : Real) else 0
    rw [← MetricFiberData.toCore_inner D]
    exact orthBasis.inner_eq_ite i j
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) :=
    metricInverseInBasis_of_orthonormal (I := I) g basis hON
  calc
    metricScalarAt (I := I) (M := M) g x =
        DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I) g
          (metricRicciAt (I := I) (M := M) g x) :=
      metricScalarAt_def (I := I) g x
    _ = ∑ i, metricRicciAt (I := I) (M := M) g x
        (vec2 (basis i) (basis i)) := by
      rw [DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis
        (I := I) g basis
        (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x))))
        hinv]
      simp [identityInvMetric, diagonalInvMetric]
    _ ≥ 0 := Finset.sum_nonneg fun i _ =>
      metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
        (I := I) (M := M) g x hR (basis i)

end DifferentialGeometry.Geometry.Curvature

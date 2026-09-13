import DifferentialGeometry.Geometry.Curvature.RoundCylinder
import DifferentialGeometry.Geometry.Curvature.PositiveSectional
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Geometry.Curvature

theorem metricRm04StandardAt_prodEuclidean_axis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (x : M × ℝ)
    (u : TangentSpace (I.prod 𝓘(ℝ, ℝ)) x) :
    metricRm04StandardAt (g.prod (euclideanMetric (E := ℝ))) x u
      ((0 : TangentSpace I x.1), (1 : ℝ))
      ((0 : TangentSpace I x.1), (1 : ℝ)) u = 0 := by
  let T : TangentSpace (I.prod 𝓘(ℝ, ℝ)) x := ((0 : TangentSpace I x.1), (1 : ℝ))
  change metricRm04StandardAt (g.prod (euclideanMetric (E := ℝ))) x u T T u = 0
  have hinner := rm04_eq_inner_riem (g.prod (euclideanMetric (E := ℝ))) x u T T u
  have hzero : riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita
        (g.prod (euclideanMetric (E := ℝ)))) x u T T = 0 :=
    riemannOp_productReal_vertical_eq_zero g x u T 1
  rw [hzero] at hinner
  simpa only [map_zero, add_zero] using hinner

theorem metricRm04StandardAt_roundCylinder_axis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (x : Metric.sphere (0 : E) 1 × ℝ) (v : TangentSpace (𝓡 n) x.1) :
    metricRm04StandardAt (roundCylinderMetric (E := E) (n := n)) x
      ((v, 0) : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) x)
      ((0, 1) : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) x)
      ((0, 1) : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) x)
      ((v, 0) : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) x) = 0 := by
  rw [show roundCylinderMetric (E := E) (n := n) =
      (scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := n))).prod
        (euclideanMetric (E := ℝ)) from by
    unfold roundCylinderMetric cylinderMetric
    rfl]
  exact metricRm04StandardAt_prodEuclidean_axis
    (g := scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := n))) x
    ((v, 0) : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) x)

theorem metricScalarAt_roundCylinder_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] (hn : 2 ≤ n)
    (x : Metric.sphere (0 : E) 1 × ℝ) :
    0 < metricScalarAt (roundCylinderMetric (E := E) (n := n)) x := by
  have hlt : (1 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) hn
  have hpos : (0 : ℝ) < (n : ℝ) := by linarith
  rw [metricScalarAt_roundCylinder]
  exact div_pos (mul_pos hpos (sub_pos.mpr hlt)) (by norm_num)

section Countermodel

private local instance factFinrankEuclideanSpaceThree :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem metricScalarAt_roundCylinderModel_pos
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
    0 < metricScalarAt
      (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) x :=
  metricScalarAt_roundCylinder_pos (by norm_num) x

theorem not_hasPositiveSectionalCurvature_roundCylinder :
    ¬ DifferentialGeometry.Geometry.HasPositiveSectionalCurvature
      (I := (𝓡 2).prod 𝓘(ℝ, ℝ))
      (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) := by
  intro hsec
  let x₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by
      simp [PiLp.norm_single]⟩
  let z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ := (x₀, 0)
  let v : EuclideanSpace ℝ (Fin 2) := (PiLp.basisFun 2 ℝ (Fin 2)) (0 : Fin 2)
  let W : EuclideanSpace ℝ (Fin 2) × ℝ := (v, 0)
  let T : EuclideanSpace ℝ (Fin 2) × ℝ := (0, 1)
  have hv : v ≠ 0 := (PiLp.basisFun 2 ℝ (Fin 2)).ne_zero (0 : Fin 2)
  have hli : LinearIndependent ℝ ![W, T] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hb : b = 0 := by
      have h2 := congrArg Prod.snd hab
      simpa [W, T] using h2
    refine ⟨?_, hb⟩
    have h1 : a • v = 0 := by
      have h1 := congrArg Prod.fst hab
      simpa [W, T, hb] using h1
    exact (smul_eq_zero.mp h1).resolve_right hv
  have hpos := hsec z W T hli
  have hzero : metricRm04StandardAt
      (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) z W T T W = 0 :=
    metricRm04StandardAt_roundCylinder_axis (x := z) (v := v)
  exact (ne_of_lt hpos) hzero.symm

theorem roundCylinder_scalarPos_not_positiveSectional :
    (∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ,
        0 < metricScalarAt
          (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) x) ∧
      ¬ DifferentialGeometry.Geometry.HasPositiveSectionalCurvature
        (I := (𝓡 2).prod 𝓘(ℝ, ℝ))
        (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) :=
  ⟨metricScalarAt_roundCylinderModel_pos, not_hasPositiveSectionalCurvature_roundCylinder⟩

end Countermodel

end DifferentialGeometry.Geometry.Curvature

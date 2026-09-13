import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistenceFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Evolution
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval} {a b : ℝ}

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem eq_zero_of_metric_inner_eq_zero_of_finrank_eq_one
    {p : M} (hE : Module.finrank ℝ (TangentSpace I p) = 1)
    (g : SmoothRiemannianMetric I M) {v w : TangentSpace I p}
    (hvw : g.inner p v w = 0) (hw : w ≠ 0) : v = 0 := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℝ) w hw).mp hE v
  have h1 : g.inner p v w = c * g.inner p w w := by
    rw [← hc, ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul]
  have hpos : 0 < g.inner p w w := g.pos p w hw
  have h2 : c = 0 := by
    have h3 : c * g.inner p w w = 0 := by rw [← h1, hvw]
    exact (mul_eq_zero.mp h3).resolve_right (ne_of_gt hpos)
  rw [← hc, h2, zero_smul]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [TopologicalSpace M] in
def staticCurve (c₀ : AddCircle (1 : ℝ) → M) : CurveMap M := fun z _ => c₀ z

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [TopologicalSpace M] in
@[simp] theorem staticCurve_apply (c₀ : AddCircle (1 : ℝ) → M) (z : AddCircle (1 : ℝ)) (t : ℝ) :
    staticCurve c₀ z t = c₀ z := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [TopologicalSpace M] in
@[simp] theorem staticCurve_lift (c₀ : AddCircle (1 : ℝ) → M) (x t : ℝ) :
    (staticCurve c₀).lift x t = c₀ (x : AddCircle (1 : ℝ)) := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [IsManifold I ∞ M] in
theorem staticCurve_smoothOn (c₀ : AddCircle (1 : ℝ) → M)
    (h : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x : ℝ => c₀ (x : AddCircle (1 : ℝ)))) (J : Set ℝ) :
    (staticCurve c₀).SmoothOn (I := I) J := by
  have hfst : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × ℝ => p.1) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiff_fst
  have hcomp : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => c₀ ((p.1 : ℝ) : AddCircle (1 : ℝ))) := h.comp hfst
  exact hcomp.contMDiffOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [IsManifold I ∞ M] in
theorem staticCurve_immersedOn (c₀ : AddCircle (1 : ℝ) → M) (J : Set ℝ)
    (him : ∀ x : ℝ, mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => c₀ (y : AddCircle (1 : ℝ))) x (1 : ℝ) ≠ 0) :
    (staticCurve c₀).ImmersedOn (I := I) J := by
  intro x t _
  exact him x

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [IsManifold I ∞ M] in
theorem staticCurve_velocity (c₀ : AddCircle (1 : ℝ) → M) (J : Set ℝ) (x t : ℝ) :
    (staticCurve c₀).velocity (I := I) J x t = 0 := by
  rw [CurveMap.velocity]
  change mfderivWithin 𝓘(ℝ, ℝ) I (fun _ : ℝ => c₀ (x : AddCircle (1 : ℝ))) J t (1 : ℝ) = 0
  rw [mfderivWithin_const]
  rfl

theorem curvatureVector_eq_zero_of_finrank_eq_one [I.Boundaryless]
    (hE : Module.finrank ℝ E = 1) (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    {c : CurveMap M} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    {x t : ℝ} (ht : t ∈ J) : c.curvatureVector g x t = 0 := by
  obtain ⟨hunit, horth, -⟩ := tangent_curvature_geometry g c J hc hi x t ht
  refine eq_zero_of_metric_inner_eq_zero_of_finrank_eq_one (p := c.lift x t) ?_ (g t) horth ?_
  · rw [show Module.finrank ℝ (TangentSpace I (c.lift x t)) = Module.finrank ℝ E from rfl]
    exact hE
  · intro hzero
    rw [hzero] at hunit
    simp at hunit

theorem curveShorteningLocalExistence_of_finrank_eq_one [I.Boundaryless]
    (hE : Module.finrank ℝ E = 1)
    (B : SmoothMetricWindow (I := I) (M := M) D a b) :
    curveShorteningLocalExistence (I := I) (M := M) B := by
  intro t₀ ht₀ c₀
  refine ⟨b - t₀, sub_pos.mpr ht₀.2, le_of_eq (by ring), staticCurve c₀.map, ?_, ?_⟩
  · refine ⟨staticCurve_smoothOn c₀.map c₀.smooth _, ?_, ?_⟩
    · exact staticCurve_immersedOn c₀.map _ c₀.immersed
    · intro x t ht
      rw [staticCurve_velocity]
      exact (curvatureVector_eq_zero_of_finrank_eq_one hE B.family.metric
        (staticCurve_smoothOn c₀.map c₀.smooth _)
        (staticCurve_immersedOn c₀.map _ c₀.immersed) ht).symm
  · intro z
    rfl

noncomputable def euclideanLineWindow (a b : ℝ) (hab : a < b) :
    SmoothMetricWindow (I := 𝓘(ℝ, ℝ)) (M := ℝ) (RealTimeInterval.univ 0) a b where
  family := ⟨fun _ => euclideanMetric (E := ℝ)⟩
  smooth := metricFamilySmoothOn_stationary (euclideanMetric (E := ℝ)) (RealTimeInterval.univ 0)
  lt := hab
  regular := fun _ _ => trivial

theorem exists_curveShorteningLocalExistence :
    ∃ B : SmoothMetricWindow (I := 𝓘(ℝ, ℝ)) (M := ℝ) (RealTimeInterval.univ 0) 0 1,
      curveShorteningLocalExistence (I := 𝓘(ℝ, ℝ)) (M := ℝ) B :=
  ⟨euclideanLineWindow 0 1 zero_lt_one,
    curveShorteningLocalExistence_of_finrank_eq_one (by simp) _⟩

noncomputable def roundCircleWindow (a b : ℝ) (hab : a < b) :
    SmoothMetricWindow (I := 𝓡 1) (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
      (RealTimeInterval.univ 0) a b :=
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) := ⟨by simp⟩
  { family := ⟨fun _ => DifferentialGeometry.Geometry.roundMetric
        (E := EuclideanSpace ℝ (Fin 2)) (n := 1)⟩
    smooth := metricFamilySmoothOn_stationary _ _
    lt := hab
    regular := fun _ _ => trivial }

theorem exists_curveShorteningLocalExistence_compact :
    ∃ B : SmoothMetricWindow (I := 𝓡 1)
        (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (RealTimeInterval.univ 0) 0 1,
      curveShorteningLocalExistence (I := 𝓡 1)
        (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) B :=
  ⟨roundCircleWindow 0 1 zero_lt_one,
    curveShorteningLocalExistence_of_finrank_eq_one (by simp) _⟩

theorem CurveShorteningSmoothSolution.of_finrank_eq_one [I.Boundaryless]
    (hE : Module.finrank ℝ E = 1)
    (B : SmoothMetricWindow (I := I) (M := M) D a b) :
    CurveShorteningSmoothSolution (I := I) (M := M) B := by
  intro t₀ ht₀ c₀
  obtain ⟨τ, hτ, hb, c, hsol, hinit⟩ :=
    curveShorteningLocalExistence_of_finrank_eq_one hE B t₀ ht₀ c₀
  exact ⟨τ, hτ, hb, c, hsol.smooth, hinit, hsol.equation⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

import DifferentialGeometry.Geometry.Connection.Product
import DifferentialGeometry.Geometry.Connection.LeviCivita.AlongCurve
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.Euclidean

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Connection

open Riemannian.Geodesic

variable {E H M F K N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

set_option backward.isDefEq.respectTransparency false in
theorem chartChristoffelContraction_prod
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (p : M × N) {q : M × N}
    (hq₁ : q.1 ∈ chartLeviCivitaGoodSet (I := I) p.1)
    (hq₂ : q.2 ∈ chartLeviCivitaGoodSet (I := J) p.2) (u w : E × F) :
    chartChristoffelContraction (g.prod h) p u w (extChartAt (I.prod J) p q) =
      (chartChristoffelContraction g p.1 u.1 w.1 (extChartAt I p.1 q.1),
       chartChristoffelContraction h p.2 u.2 w.2 (extChartAt J p.2 q.2)) := by
  have h₁ := mem_chartLeviCivitaGoodSet_iff.mp hq₁
  have h₂ := mem_chartLeviCivitaGoodSet_iff.mp hq₂
  have hq : q ∈ chartLeviCivitaGoodSet (I := I.prod J) p := by
    apply mem_chartLeviCivitaGoodSet_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · simpa only [extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod] using And.intro h₁.1 h₂.1
    · simpa only [TangentBundle.trivializationAt_baseSet, prodChartedSpace_chartAt,
        OpenPartialHomeomorph.prod_source, Set.mem_prod] using And.intro h₁.2.1 h₂.2.1
    · simpa only [extChartAt_prod, PartialEquiv.prod_target, PartialEquiv.prod_coe,
        interior_prod_eq, Set.mem_prod] using And.intro h₁.2.2 h₂.2.2
  have hb := chartLeviCivitaGoodSet_mem_baseSet hq
  let X := (trivializationAt (E × F) (TangentSpace (I.prod J)) p).symmL ℝ q u
  have heq := connectionForm_leviCivita_prod_of_mem g h p hb X w
  rw [connectionForm_leviCivita_apply (g.prod h) p hq,
    connectionForm_leviCivita_apply g p.1 hq₁,
    connectionForm_leviCivita_apply h p.2 hq₂] at heq
  dsimp only [X, trivToE] at heq
  rw [Trivialization.continuousLinearMapAt_symmL _ hb,
    trivializationAt_symmL_prod p q hb] at heq
  dsimp only at heq
  rw [Trivialization.continuousLinearMapAt_symmL _ h₁.2.1,
    Trivialization.continuousLinearMapAt_symmL _ h₂.2.1] at heq
  exact heq


theorem chartChristoffelContraction_prod_euclideanMetric
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (g : SmoothRiemannianMetric I M) (p : M) {q : M}
    (hq : q ∈ chartLeviCivitaGoodSet (I := I) p) (z₀ z : V) (u v : E × V) :
    chartChristoffelContraction (g.prod (euclideanMetric (E := V))) (p, z₀) u v
      (extChartAt I p q, z) =
        (chartChristoffelContraction g p u.1 v.1 (extChartAt I p q), 0) := by
  have hz : z ∈ chartLeviCivitaGoodSet (I := 𝓘(ℝ, V)) z₀ := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source, extChartAt_model_space_eq_id]
    exact Set.mem_univ z
  have h := chartChristoffelContraction_prod g (euclideanMetric (E := V)) (p, z₀)
    (q := (q, z)) hq hz u v
  rw [chartChristoffelContraction_euclideanMetric] at h
  simpa only [extChartAt_prod, PartialEquiv.prod_coe, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, Prod.map_apply, id_eq] using h

end DifferentialGeometry.Geometry.Connection

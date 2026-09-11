import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Regularized

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegularizedIndex_cross_pos_of_isLRegularizedJacobi
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (Y W : ∀ r, TangentSpace I (alpha r))
    (c b : Real) (hc0 : 0 < c) (hcb : c < b)
    (ht : ∀ s ∈ Set.uIcc (0 : Real) c, T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ Set.uIcc (0 : Real) c, ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : ∀ s ∈ Set.uIcc (0 : Real) c, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hjac : IsLRegularizedJacobi S T alpha Y (Set.uIcc (0 : Real) c))
    (hW : ∀ s ∈ Set.uIcc (0 : Real) c, DifferentiableAt Real
      (chartRepAt (I := I) alpha W s) s)
    (hIint : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y W)
      MeasureTheory.volume 0 c)
    (hW0 : W 0 = 0)
    (hWc : W c = (c * (b - c)) •
      covDerivAlong (I := I) (S.base.metric (T - c ^ 2)) alpha Y c)
    (hDne : covDerivAlong (I := I)
      (S.base.metric (T - c ^ 2)) alpha Y c ≠ 0) :
    0 < lRegularizedIndex S T alpha Y W 0 c := by
  let P : TangentSpace I (alpha c) :=
    covDerivAlong (I := I) (S.base.metric (T - c ^ 2)) alpha Y c
  have hPc : 0 < (S.base.metric (T - c ^ 2)).inner (alpha c) P P :=
    (S.base.metric (T - c ^ 2)).pos (alpha c) P (by
      simpa only [P] using hDne)
  have hscale : 0 < c * (b - c) := mul_pos hc0 (sub_pos.mpr hcb)
  have hgreen := lRegularizedIndex_eq_half_boundary_of_isLRegularizedJacobi (I := I) S hS T alpha Y W 0 c ht
    halpha hA hjac hW hIint
  rw [hgreen, hW0, hWc]
  simp only [map_zero, sub_zero]
  change 0 < (1 / 2 : Real) *
    ((S.base.metric (T - c ^ 2)).inner (alpha c) P
      ((c * (b - c)) • P))
  rw [((S.base.metric (T - c ^ 2)).inner (alpha c) P).map_smul]
  positivity

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegularizedIndex_cross_neg_of_isLRegularizedJacobi
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (Y W : ∀ r, TangentSpace I (alpha r))
    (c b : Real) (hc0 : 0 < c) (hcb : c < b)
    (ht : ∀ s ∈ uIcc c b, T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ uIcc c b, ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : ∀ s ∈ uIcc c b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hjac : IsLRegularizedJacobi S T alpha Y (uIcc c b))
    (hW : ∀ s ∈ uIcc c b, DifferentiableAt Real
      (chartRepAt (I := I) alpha W s) s)
    (hIint : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y W)
      MeasureTheory.volume c b)
    (hWb : W b = 0)
    (hWc : W c = (c * (b - c)) •
      covDerivAlong (I := I) (S.base.metric (T - c ^ 2)) alpha Y c)
    (hDne : covDerivAlong (I := I)
      (S.base.metric (T - c ^ 2)) alpha Y c ≠ 0) :
    lRegularizedIndex S T alpha Y W c b < 0 := by
  let P : TangentSpace I (alpha c) :=
    covDerivAlong (I := I) (S.base.metric (T - c ^ 2)) alpha Y c
  have hPc : 0 < (S.base.metric (T - c ^ 2)).inner (alpha c) P P :=
    (S.base.metric (T - c ^ 2)).pos (alpha c) P (by
      simpa only [P] using hDne)
  have hscale : 0 < c * (b - c) := mul_pos hc0 (sub_pos.mpr hcb)
  have hgreen := lRegularizedIndex_eq_half_boundary_of_isLRegularizedJacobi (I := I) S hS T alpha Y W c b ht
    halpha hA hjac hW hIint
  rw [hWb, hWc] at hgreen
  simp only [map_zero, zero_sub] at hgreen
  rw [hgreen]
  change (1 / 2 : Real) *
    (-((S.base.metric (T - c ^ 2)).inner (alpha c) P
      ((c * (b - c)) • P))) < 0
  rw [((S.base.metric (T - c ^ 2)).inner (alpha c) P).map_smul]
  rw [smul_eq_mul]
  have hprod : 0 < (c * (b - c)) *
      (S.base.metric (T - c ^ 2)).inner (alpha c) P P :=
    mul_pos hscale hPc
  nlinarith [hprod]

end DifferentialGeometry.PDE.RicciFlow.Perelman

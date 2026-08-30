import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.NegativeDirection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private theorem exists_pos_scale {h Q : Real} (hh : h < 0) :
    ∃ k : Real, 2 * k * h + k ^ 2 * Q < 0 := by
  have hden : 0 < |Q| + 1 := by positivity
  let k : Real := -h / (|Q| + 1)
  have hkpos : 0 < k := div_pos (neg_pos.mpr hh) hden
  have hkQ : |k * Q| < -h := by
    simp only [k]
    rw [abs_mul, abs_div, abs_neg, abs_of_neg hh,
      abs_of_pos hden, div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [abs_nonneg Q]
  have hsum : 2 * h + k * Q < 0 := by
    linarith [(abs_lt.mp hkQ).2]
  refine ⟨k, ?_⟩
  calc
    2 * k * h + k ^ 2 * Q = k * (2 * h + k * Q) := by ring
    _ < 0 := mul_neg_of_pos_of_neg hkpos hsum

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem exists_lSplit_left
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (Y W : ∀ s, TangentSpace I (alpha s))
    (a c b : Real)
    (hY : ∀ s ∈ uIcc c b,
      DifferentiableAt Real (chartRepAt (I := I) alpha Y s) s)
    (hW : ∀ s ∈ uIcc c b,
      DifferentiableAt Real (chartRepAt (I := I) alpha W s) s)
    (hYYint : IntervalIntegrable (lRegIndexInt S T alpha Y Y)
      MeasureTheory.volume c b)
    (hYWint : IntervalIntegrable (lRegIndexInt S T alpha Y W)
      MeasureTheory.volume c b)
    (hWWac : IntervalIntegrable (lRegIndexInt S T alpha W W)
      MeasureTheory.volume a c)
    (hWWcb : IntervalIntegrable (lRegIndexInt S T alpha W W)
      MeasureTheory.volume c b)
    (hYY : lRegIndex S T alpha Y Y c b = 0)
    (hYW : lRegIndex S T alpha Y W c b < 0) :
    ∃ k : Real,
      lRegIndex S T alpha (fun s ↦ k • W s)
          (fun s ↦ k • W s) a c +
        lRegIndex S T alpha (fun s ↦ Y s + k • W s)
          (fun s ↦ Y s + k • W s) c b < 0 := by
  let Q := lRegIndex S T alpha W W a b
  obtain ⟨k, hk⟩ := exists_pos_scale hYW (Q := Q)
  refine ⟨k, ?_⟩
  have htail := lIndex_sq_add (I := I) S T k alpha Y W c b hY hW
    hYYint hYWint hWWcb
  have hprefix : lRegIndex S T alpha (fun s ↦ k • W s)
      (fun s ↦ k • W s) a c =
      k ^ 2 * lRegIndex S T alpha W W a c := by
    rw [lRegIndex_smul (I := I) S T k alpha W
        (fun s ↦ k • W s) a c,
      lRegIndex_smul_r (I := I) S T k alpha W W a c]
    ring
  have hjoin := lIndex_adj (I := I) S T alpha W W a c b hWWac hWWcb
  rw [hprefix, htail, hYY, zero_add]
  dsimp only [Q] at hk
  rw [← hjoin] at hk
  nlinarith

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lIndex_cross_neg
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
    (hjac : IsLRegJacobi S T alpha Y (uIcc c b))
    (hW : ∀ s ∈ uIcc c b, DifferentiableAt Real
      (chartRepAt (I := I) alpha W s) s)
    (hIint : IntervalIntegrable (lRegIndexInt S T alpha Y W)
      MeasureTheory.volume c b)
    (hWb : W b = 0)
    (hWc : W c = (c * (b - c)) •
      covDerivAlong (I := I) (S.base.metric (T - c ^ 2)) alpha Y c)
    (hDne : covDerivAlong (I := I)
      (S.base.metric (T - c ^ 2)) alpha Y c ≠ 0) :
    lRegIndex S T alpha Y W c b < 0 := by
  let P : TangentSpace I (alpha c) :=
    covDerivAlong (I := I) (S.base.metric (T - c ^ 2)) alpha Y c
  have hPc : 0 < (S.base.metric (T - c ^ 2)).inner (alpha c) P P :=
    (S.base.metric (T - c ^ 2)).pos (alpha c) P (by
      simpa only [P] using hDne)
  have hscale : 0 < c * (b - c) := mul_pos hc0 (sub_pos.mpr hcb)
  have hgreen := lRegIndex_jacobi (I := I) S hS T alpha Y W c b ht
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

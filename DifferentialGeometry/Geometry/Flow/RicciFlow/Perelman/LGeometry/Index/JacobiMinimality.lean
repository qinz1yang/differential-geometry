import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Algebra

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open scoped Manifold ContDiff

open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

omit [I.Boundaryless] in
private theorem sub_field_regular
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (J V : ∀ r, TangentSpace I (alpha r)) (a b : Real)
    (hJd : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real (chartRepAt (I := I) alpha J s) s)
    (hV : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real (chartRepAt (I := I) alpha V s) s)
    (hJJ : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha J J)
      MeasureTheory.volume a b)
    (hJV : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha J V)
      MeasureTheory.volume a b)
    (hVV : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha V V)
      MeasureTheory.volume a b) :
    (∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha (fun r ↦ V r - J r) s) s) ∧
    IntervalIntegrable (lRegularizedIndexIntegrand S T alpha J (fun r ↦ V r - J r))
      MeasureTheory.volume a b ∧
    IntervalIntegrable
      (lRegularizedIndexIntegrand S T alpha (fun r ↦ V r - J r) (fun r ↦ V r - J r))
      MeasureTheory.volume a b := by
  let N : ∀ r, TangentSpace I (alpha r) := fun r ↦ (-1 : Real) • J r
  let W : ∀ r, TangentSpace I (alpha r) := fun r ↦ V r + N r
  have hWsub : (fun s ↦ V s - J s) = W := by
    funext s
    simp only [W, N, neg_one_smul, sub_eq_add_neg]
  rw [hWsub]
  have hNd : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha N s) s := by
    intro s hs
    simp only [N]
    rw [chartRepAt_smul]
    exact (hJd s hs).const_smul _
  have hWd : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha W s) s := by
    intro s hs
    simp only [W]
    rw [chartRepAt_add]
    exact (hV s hs).add (hNd s hs)
  have hJW : ∀ s ∈ Set.uIcc a b,
      lRegularizedIndexIntegrand S T alpha J W s =
        lRegularizedIndexIntegrand S T alpha J V s +
          (-1 : Real) * lRegularizedIndexIntegrand S T alpha J J s := by
    intro s hs
    rw [lRegularizedIndexIntegrand_add_right (I := I) S T alpha J V N s (hV s hs) (hNd s hs),
      lRegularizedIndexIntegrand_smul_right (I := I) S T (-1) alpha J J s]
  have hVW : ∀ s ∈ Set.uIcc a b,
      lRegularizedIndexIntegrand S T alpha V W s =
        lRegularizedIndexIntegrand S T alpha V V s +
          (-1 : Real) * lRegularizedIndexIntegrand S T alpha J V s := by
    intro s hs
    rw [lRegularizedIndexIntegrand_add_right (I := I) S T alpha V V N s (hV s hs) (hNd s hs),
      lRegularizedIndexIntegrand_smul_right (I := I) S T (-1) alpha V J s,
      lRegularizedIndexIntegrand_symm (I := I) S T alpha V J s]
  have hWW : ∀ s ∈ Set.uIcc a b,
      lRegularizedIndexIntegrand S T alpha W W s =
        lRegularizedIndexIntegrand S T alpha V V s -
          2 * lRegularizedIndexIntegrand S T alpha J V s +
          lRegularizedIndexIntegrand S T alpha J J s := by
    intro s hs
    rw [lRegularizedIndexIntegrand_add (I := I) S T alpha V N W s (hV s hs) (hNd s hs),
      lRegularizedIndexIntegrand_smul (I := I) S T (-1) alpha J W s,
      hVW s hs, hJW s hs]
    ring
  refine ⟨hWd, ?_, ?_⟩
  · exact (intervalIntegrable_congr
      (fun s hs ↦ (hJW s (Set.uIoc_subset_uIcc hs)).symm)).mp
      (hJV.add (hJJ.const_mul (-1)))
  · exact (intervalIntegrable_congr
      (fun s hs ↦ (hWW s (Set.uIoc_subset_uIcc hs)).symm)).mp
      ((hVV.sub (hJV.const_mul 2)).add hJJ)

theorem lRegularizedIndex_self_eq_add_boundary_add_sub_of_isLRegularizedJacobi
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (J V : ∀ r, TangentSpace I (alpha r))
    (a b : Real)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ Set.uIcc a b, ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hjac : IsLRegularizedJacobi S T alpha J (Set.uIcc a b))
    (hV : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha V s) s)
    (hJJ : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha J J)
      MeasureTheory.volume a b)
    (hJV : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha J V)
      MeasureTheory.volume a b)
    (hVV : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha V V)
      MeasureTheory.volume a b) :
    lRegularizedIndex S T alpha V V a b =
      lRegularizedIndex S T alpha J J a b +
        ((S.base.metric (T - b ^ 2)).inner (alpha b)
            (covDerivAlong (I := I) (S.base.metric (T - b ^ 2)) alpha J b)
            (V b - J b) -
          (S.base.metric (T - a ^ 2)).inner (alpha a)
            (covDerivAlong (I := I) (S.base.metric (T - a ^ 2)) alpha J a)
            (V a - J a)) +
        lRegularizedIndex S T alpha (fun s ↦ V s - J s) (fun s ↦ V s - J s) a b := by
  have hJd : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha J s) s := fun s hs ↦ (hjac s hs).2.1
  obtain ⟨hWd, hJWint, hWWint⟩ :=
    sub_field_regular (I := I) S T alpha J V a b hJd hV hJJ hJV hVV
  have hexp := lRegularizedIndex_add_smul_self (I := I) S T 1 alpha J
    (fun r ↦ V r - J r) a b hJd hWd hJJ hJWint hWWint
  have hsum : (fun s ↦ J s + (1 : Real) • (V s - J s)) = V := by
    funext s
    simp only [one_smul, add_sub_cancel]
  rw [hsum] at hexp
  have hgreen := lRegularizedIndex_eq_half_boundary_of_isLRegularizedJacobi (I := I) S hS T
    alpha J (fun r ↦ V r - J r) a b ht halpha hA hjac hWd hJWint
  rw [hexp, hgreen]
  ring

theorem lRegularizedIndex_self_eq_add_sub_of_isLRegularizedJacobi
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (J V : ∀ r, TangentSpace I (alpha r))
    (a b : Real)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ Set.uIcc a b, ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hjac : IsLRegularizedJacobi S T alpha J (Set.uIcc a b))
    (hV : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha V s) s)
    (hJJ : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha J J)
      MeasureTheory.volume a b)
    (hJV : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha J V)
      MeasureTheory.volume a b)
    (hVV : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha V V)
      MeasureTheory.volume a b)
    (hVa : V a = J a) (hVb : V b = J b) :
    lRegularizedIndex S T alpha V V a b =
      lRegularizedIndex S T alpha J J a b +
        lRegularizedIndex S T alpha (fun s ↦ V s - J s) (fun s ↦ V s - J s) a b := by
  rw [lRegularizedIndex_self_eq_add_boundary_add_sub_of_isLRegularizedJacobi (I := I) S hS T
    alpha J V a b ht halpha hA hjac hV hJJ hJV hVV, hVa, hVb]
  simp only [sub_self, map_zero, add_zero]

theorem lRegularizedIndex_le_of_isLRegularizedJacobi
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (J V : ∀ r, TangentSpace I (alpha r))
    (a b : Real)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ Set.uIcc a b, ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hnonneg : ∀ W : ∀ r, TangentSpace I (alpha r),
      (∀ s ∈ Set.uIcc a b, DifferentiableAt Real (chartRepAt (I := I) alpha W s) s) →
      IntervalIntegrable (lRegularizedIndexIntegrand S T alpha W W) MeasureTheory.volume a b →
      W a = 0 → W b = 0 → 0 ≤ lRegularizedIndex S T alpha W W a b)
    (hjac : IsLRegularizedJacobi S T alpha J (Set.uIcc a b))
    (hV : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha V s) s)
    (hJJ : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha J J)
      MeasureTheory.volume a b)
    (hJV : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha J V)
      MeasureTheory.volume a b)
    (hVV : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha V V)
      MeasureTheory.volume a b)
    (hVa : V a = J a) (hVb : V b = J b) :
    lRegularizedIndex S T alpha J J a b ≤ lRegularizedIndex S T alpha V V a b := by
  obtain ⟨hWd, -, hWWint⟩ :=
    sub_field_regular (I := I) S T alpha J V a b (fun s hs ↦ (hjac s hs).2.1) hV hJJ hJV hVV
  have hW := hnonneg (fun r ↦ V r - J r) hWd hWWint (by simp only [hVa, sub_self])
    (by simp only [hVb, sub_self])
  rw [lRegularizedIndex_self_eq_add_sub_of_isLRegularizedJacobi (I := I) S hS T alpha J V a b ht
    halpha hA hjac hV hJJ hJV hVV hVa hVb]
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman

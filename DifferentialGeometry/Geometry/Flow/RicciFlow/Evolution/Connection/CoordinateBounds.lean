import DifferentialGeometry.Geometry.Metric.Coordinates.FrameBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Tower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.CoordinateEvolution

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Matrix
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [T2Space M] in
private theorem coordInv_eq_gramInv
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : ℝ) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    coordInv S x₀ t x =
      (gramE (coordinateTrivializationAt (I := I) x₀) (S.family.metric t)
        (Module.finBasis ℝ E) x)⁻¹ := by
  classical
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hinv := metricInverseInBasis_of_local S (coordInv S x₀)
    (coordinateFrameAt (I := I) x₀) hframe (coordInvLocal S x₀) t hx
  let A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    coordInv S x₀ t x
  have hmul : A * gramE (coordinateTrivializationAt (I := I) x₀)
      (S.family.metric t) (Module.finBasis ℝ E) x = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa only [A, gramE, Matrix.of_apply, hframe, coordinateFrameAt,
      IsLocalFrameOn.toBasisAt_coe] using (hinv i j).1
  exact (Matrix.inv_eq_left_inv hmul).symm

private theorem nablaRicComp_eq_ricCovTower
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (frame : Fin (Module.finrank ℝ E) → (x : M) → TangentSpace I x)
    (t : ℝ) (x : M) (i j k : Fin (Module.finrank ℝ E)) :
    nablaRicComp S frame t x i j k =
      ricCovTower (S.family.metric t) (S.family.metric t) 1 x
        (vec3 (frame i x) (frame j x) (frame k x)) := by
  rfl

theorem exists_bound_christoffel_evolution_rhs_on_compact
    (R : SmoothRiemannianMetric I M) (x₀ : M)
    {K : Set M} (hK : IsCompact K) (hchart : K ⊆ coordinateFrameSet (I := I) x₀)
    (a b B KShi : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D),
      (∀ t ∈ Icc a b, MetricUniformEquivalentOn K R (S.family.metric t) B) →
      MovingShiBoundOn K a b (fun _ t => S.family.metric t) 1 KShi →
      ∀ t ∈ Icc a b, ∀ x ∈ K, ∀ i j k : CoordinateIdx (𝕜 := ℝ) E,
        ‖-(∑ l : CoordinateIdx (𝕜 := ℝ) E,
          coordInv S x₀ t x k l *
            (nablaRicComp S (coordinateFrameAt (I := I) x₀) t x i j l +
              nablaRicComp S (coordinateFrameAt (I := I) x₀) t x j i l -
              nablaRicComp S (coordinateFrameAt (I := I) x₀) t x l i j))‖ ≤ C := by
  classical
  by_cases hB : 0 < B
  · obtain ⟨Rf, hRf, hframe⟩ := exists_pos_bound_localFrame_on_compact
      (coordinateTrivializationAt (I := I) x₀) R (Module.finBasis ℝ E) hK hchart
    obtain ⟨Ci, hCi, hinv⟩ := exists_abs_gramInv_le_of_lower_bound
      (coordinateTrivializationAt (I := I) x₀) R (Module.finBasis ℝ E) hK hchart
      B⁻¹ (inv_pos.mpr hB)
    let V := Real.sqrt B * Rf
    let A := max KShi 0 * V ^ 3
    have hV : 0 ≤ V := mul_nonneg (Real.sqrt_nonneg _) hRf.le
    have hA : 0 ≤ A := mul_nonneg (le_max_right _ _) (pow_nonneg hV _)
    refine ⟨(Module.finrank ℝ E : ℝ) * (Ci * (3 * A)), by positivity, ?_⟩
    intro D S hmetric hShi t ht x hx i j k
    have hF (r : CoordinateIdx (𝕜 := ℝ) E) :
        Real.sqrt ((S.family.metric t).inner x (coordinateFrameAt (I := I) x₀ r x)
          (coordinateFrameAt (I := I) x₀ r x)) ≤ V := by
      calc
        _ ≤ Real.sqrt (B * R.inner x (coordinateFrameAt (I := I) x₀ r x)
            (coordinateFrameAt (I := I) x₀ r x)) :=
          Real.sqrt_le_sqrt ((hmetric t ht).2 x hx _).2
        _ = Real.sqrt B * Real.sqrt (R.inner x (coordinateFrameAt (I := I) x₀ r x)
            (coordinateFrameAt (I := I) x₀ r x)) := Real.sqrt_mul hB.le _
        _ ≤ Real.sqrt B * Rf :=
          mul_le_mul_of_nonneg_left (hframe x hx r) (Real.sqrt_nonneg _)
    have hN (r s u : CoordinateIdx (𝕜 := ℝ) E) :
        |nablaRicComp S (coordinateFrameAt (I := I) x₀) t x r s u| ≤ A := by
      rw [nablaRicComp_eq_ricCovTower]
      refine (abs_apply_le_norm0S (S.family.metric t) x 3
        (ricCovTower (S.family.metric t) (S.family.metric t) 1 x)
        (vec3 (coordinateFrameAt (I := I) x₀ r x) (coordinateFrameAt (I := I) x₀ s x)
          (coordinateFrameAt (I := I) x₀ u x))).trans ?_
      have hprod : (∏ q : Fin 3, Real.sqrt ((S.family.metric t).inner x
          (vec3 (coordinateFrameAt (I := I) x₀ r x) (coordinateFrameAt (I := I) x₀ s x)
            (coordinateFrameAt (I := I) x₀ u x) q)
          (vec3 (coordinateFrameAt (I := I) x₀ r x) (coordinateFrameAt (I := I) x₀ s x)
            (coordinateFrameAt (I := I) x₀ u x) q))) ≤ V ^ 3 := by
        calc
          _ ≤ ∏ _q : Fin 3, V := by
            apply Finset.prod_le_prod
            · intro q _; exact Real.sqrt_nonneg _
            · intro q _; fin_cases q <;> exact hF _
          _ = V ^ 3 := by simp
      exact mul_le_mul ((hShi 1 le_rfl 0 t ht x hx).trans (le_max_left KShi 0)) hprod
        (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _) (le_max_right KShi 0)
    have hI (l : CoordinateIdx (𝕜 := ℝ) E) : |coordInv S x₀ t x k l| ≤ Ci := by
      rw [coordInv_eq_gramInv S x₀ t (hchart hx)]
      exact hinv x hx (S.family.metric t) (fun v => ((hmetric t ht).2 x hx v).1) k l
    rw [norm_neg, Real.norm_eq_abs]
    calc
      _ ≤ ∑ l : CoordinateIdx (𝕜 := ℝ) E,
          |coordInv S x₀ t x k l *
            (nablaRicComp S (coordinateFrameAt (I := I) x₀) t x i j l +
              nablaRicComp S (coordinateFrameAt (I := I) x₀) t x j i l -
              nablaRicComp S (coordinateFrameAt (I := I) x₀) t x l i j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : CoordinateIdx (𝕜 := ℝ) E, Ci * (3 * A) := by
        apply Finset.sum_le_sum
        intro l _
        rw [abs_mul]
        apply mul_le_mul (hI l) _ (abs_nonneg _) hCi
        calc
          _ ≤ |nablaRicComp S (coordinateFrameAt (I := I) x₀) t x i j l +
              nablaRicComp S (coordinateFrameAt (I := I) x₀) t x j i l| +
              |nablaRicComp S (coordinateFrameAt (I := I) x₀) t x l i j| := abs_sub _ _
          _ ≤ (|nablaRicComp S (coordinateFrameAt (I := I) x₀) t x i j l| +
              |nablaRicComp S (coordinateFrameAt (I := I) x₀) t x j i l|) +
              |nablaRicComp S (coordinateFrameAt (I := I) x₀) t x l i j| :=
            by
              linarith [abs_add_le
                (nablaRicComp S (coordinateFrameAt (I := I) x₀) t x i j l)
                (nablaRicComp S (coordinateFrameAt (I := I) x₀) t x j i l)]
          _ ≤ 3 * A := by linarith [hN i j l, hN j i l, hN l i j]
      _ = _ := by simp [CoordinateIdx]
  · refine ⟨0, le_rfl, ?_⟩
    intro D S hmetric _ t ht x _ i j k
    exact False.elim (hB (zero_lt_one.trans_le (hmetric t ht).1))

end DifferentialGeometry.PDE.RicciFlow

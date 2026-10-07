import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.DifferenceKoszulDerivative
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Bounds

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Connection

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem connectionDifference_inner_metricCovDeriv
    (h g : SmoothRiemannianMetric I M) (x : M) (v w z : TangentSpace I x) :
    h.inner x (CovariantDerivative.difference (LeviCivita h) (LeviCivita g) x w v) z =
      (1 / 2 : ℝ) * metricCovDeriv h g 1 x ![v, w, z] +
        (1 / 2 : ℝ) * metricCovDeriv h g 1 x ![w, v, z] -
        (1 / 2 : ℝ) * metricCovDeriv h g 1 x ![z, v, w] := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x w
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x z
  have hvec (a b : TangentSpace I x) :
      (fun q : Fin 2 => if q = 0 then a else b) = ![a, b] := by
    funext q
    fin_cases q <;> rfl
  have hk := connectionDifference_koszul_nabla h g X Y Z (x := x)
  simp only [hvec] at hk
  have hD (W : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I))
      (a b : TangentSpace I x) :
      Tensor0SBundle.nabla0SFun 2 (LeviCivita g) W
          (Tensor0SBundle.metricTensorField h) x ![a, b] =
        metricCovDeriv h g 1 x ![W x, a, b] := by
    change Tensor0SBundle.nabla0SFun 2 (leviCivitaConnectionOfMetric g) W
      (metricCovDeriv h g 0) x ![a, b] = _
    exact (metricCovDeriv_one_apply_section h g W x ![a, b]).symm
  rw [hD, hD, hD] at hk
  simpa only [hX, hY, hZ] using hk

theorem connectionDifference_norm_le_of_metric_lower_bound
    (h g : SmoothRiemannianMetric I M) (x : M) {c : ℝ} (hc : 0 < c)
    (hcg : ∀ z : TangentSpace I x, c * g.inner x z z ≤ h.inner x z z)
    (v w : TangentSpace I x) :
    let A := CovariantDerivative.difference (LeviCivita h) (LeviCivita g) x w v
    Real.sqrt (g.inner x A A) ≤
      (3 / (2 * c)) * metricCovDerivNorm 1 h g x *
        Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let A := CovariantDerivative.difference (LeviCivita h) (LeviCivita g) x w v
  let N := metricCovDerivNorm 1 h g x
  let S (z : TangentSpace I x) := Real.sqrt (g.inner x z z)
  have hg (z : TangentSpace I x) : 0 ≤ g.inner x z z := by
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · exact (g.pos x z hz).le
  have hbound (a b d : TangentSpace I x) :
      |metricCovDeriv h g 1 x ![a, b, d]| ≤ N * S a * S b * S d := by
    have ht := Tensor0SBundle.abs_apply_le_norm0S g x 3 (metricCovDeriv h g 1 x) ![a, b, d]
    simpa [N, S, metricCovDerivNorm, Fin.prod_univ_three, mul_assoc] using ht
  have h1 := (le_abs_self _).trans (hbound v w A)
  have h2 := (le_abs_self _).trans (hbound w v A)
  have h3 := (neg_le_abs _).trans (hbound A v w)
  have heq := connectionDifference_inner_metricCovDeriv h g x v w A
  have hs : S A ^ 2 = g.inner x A A := Real.sq_sqrt (hg A)
  have hineq : c * (S A * S A) ≤ (3 / 2 : ℝ) * N * S v * S w * S A := by
    have hl := hcg A
    change c * g.inner x A A ≤ h.inner x A A at hl
    change h.inner x A A = _ at heq
    calc
      c * (S A * S A) = c * g.inner x A A := by rw [← hs]; ring
      _ ≤ h.inner x A A := hl
      _ ≤ _ := by rw [heq]; nlinarith only [h1, h2, h3]
  change S A ≤ _
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (g.inner x A A)) with hzero | hpos
  · change 0 = S A at hzero
    rw [← hzero]
    dsimp [N, S, metricCovDerivNorm]
    positivity
  · have hcancel : c * S A ≤ (3 / 2 : ℝ) * N * S v * S w :=
      (mul_le_mul_iff_left₀ hpos).mp (by nlinarith only [hineq])
    calc
      S A = (c * S A) / c := by field_simp
      _ ≤ ((3 / 2 : ℝ) * N * S v * S w) / c := div_le_div_of_nonneg_right hcancel hc.le
      _ = _ := by dsimp only [N, S]; ring

end DifferentialGeometry.Geometry.Connection

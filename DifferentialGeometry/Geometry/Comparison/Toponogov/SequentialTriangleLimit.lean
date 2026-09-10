import DifferentialGeometry.Geometry.Comparison.Toponogov.MetricComparisonAngle

open Filter Topology

noncomputable section

namespace Poincare.Toponogov

theorem comparisonTriangleLimit {a b c : ℕ → ℝ}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hreverse : ∀ i, |a i - b i| ≤ c i) (htriangle : ∀ i, c i ≤ a i + b i)
    (hu : Tendsto (fun i ↦ a i / b i) atTop (nhds 0))
    (htheta : Tendsto (fun i ↦ comparisonAngle (a i) (b i) (c i)) atTop (nhds 0)) :
    Tendsto (fun i ↦ comparisonAngle (a i) (c i) (b i)) atTop (nhds Real.pi) := by
  let u : ℕ → ℝ := fun i ↦ a i / b i
  let w : ℕ → ℝ := fun i ↦ c i / b i
  let theta : ℕ → ℝ := fun i ↦ comparisonAngle (a i) (b i) (c i)
  have hu' : Tendsto u atTop (nhds 0) := by simpa only [u] using hu
  have htheta' : Tendsto theta atTop (nhds 0) := by simpa only [theta] using htheta
  have hcosTheta : Tendsto (fun i ↦ Real.cos (theta i)) atTop (nhds 1) := by
    change Tendsto (Real.cos ∘ theta) atTop (nhds 1)
    simpa only [Real.cos_zero] using (Real.continuous_cos.tendsto 0).comp htheta'
  have hw_nonneg (i : ℕ) : 0 ≤ w i := by
    exact div_nonneg (hc i).le (hb i).le
  have hw_sq_formula (i : ℕ) :
      w i ^ 2 = u i ^ 2 + 1 - 2 * u i * Real.cos (theta i) := by
    dsimp only [u, w, theta]
    rw [cos_comparisonAngle (ha i) (hb i) (hreverse i) (htriangle i)]
    unfold comparisonCosine
    field_simp [(ha i).ne', (hb i).ne']
    ring
  have hrhs :
      Tendsto (fun i ↦ u i ^ 2 + 1 - 2 * u i * Real.cos (theta i)) atTop (nhds 1) := by
    (convert (((hu'.pow 2).add tendsto_const_nhds).sub
      ((tendsto_const_nhds.mul hu').mul hcosTheta)) using 1; norm_num)
  have hw_sq : Tendsto (fun i ↦ w i ^ 2) atTop (nhds 1) :=
    hrhs.congr' (Eventually.of_forall fun i ↦ (hw_sq_formula i).symm)
  have hw : Tendsto w atTop (nhds 1) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 1).comp hw_sq
    convert hsqrt using 1
    · funext i
      exact (Real.sqrt_sq (hw_nonneg i)).symm
    · simp
  have hphi_formula (i : ℕ) :
      comparisonCosine (a i) (c i) (b i) =
        (u i - Real.cos (theta i)) / w i := by
    dsimp only [u, w, theta]
    rw [cos_comparisonAngle (ha i) (hb i) (hreverse i) (htriangle i)]
    unfold comparisonCosine
    field_simp [(ha i).ne', (hb i).ne', (hc i).ne']
    ring
  have hratio :
      Tendsto ((fun i ↦ u i - Real.cos (theta i)) / w) atTop (nhds (-1)) := by
    (convert (hu'.sub hcosTheta).div hw (by norm_num) using 1; norm_num)
  have hphi_cosine :
      Tendsto (fun i ↦ comparisonCosine (a i) (c i) (b i)) atTop (nhds (-1)) :=
    hratio.congr' (Eventually.of_forall fun i ↦ by
      change (u i - Real.cos (theta i)) / w i = comparisonCosine (a i) (c i) (b i)
      exact (hphi_formula i).symm)
  change Tendsto (Real.arccos ∘ fun i ↦ comparisonCosine (a i) (c i) (b i)) atTop
    (nhds Real.pi)
  simpa only [Real.arccos_neg_one] using
    (Real.continuous_arccos.tendsto (-1)).comp hphi_cosine

end Poincare.Toponogov

import DifferentialGeometry.Geometry.Neck.SignedCollarGraph
import DifferentialGeometry.Geometry.Neck.ScaleComparison
import DifferentialGeometry.Analysis.ODE.Flow.Planar.CollarScaleEstimate

noncomputable section
open Set DifferentialGeometry
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Operator

namespace Poincare.Geometry.Neck

private abbrev S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private theorem sign_product (τ : Fin 2 → ℝ) (hτ : ∀ i, τ i = 1 ∨ τ i = -1)
    (s : ℝ) (hcompat : τ 1 = τ 0 * s) (k i : Fin 2) :
    τ k * τ i = if k = i then 1 else s := by
  have hsq (j : Fin 2) : τ j * τ j = 1 := by rcases hτ j with h | h <;> rw [h] <;> norm_num
  have hcross : τ 0 * τ 1 = s := by rw [hcompat, ← mul_assoc, hsq, one_mul]
  fin_cases k <;> fin_cases i <;> norm_num [Fin.ext_iff]
  · exact hsq 0
  · exact hcross
  · simpa only [mul_comm] using hcross
  · exact hsq 1

private def recordedTranslation (s c : ℝ) (k i : Fin 2) : ℝ :=
  if k = i then 0 else if k = 1 then c else -s * c

private theorem recorded_value_error (u τ : Fin 2 → ℝ)
    (hτ : ∀ i, τ i = 1 ∨ τ i = -1) (s c : ℝ) (hs : s = 1 ∨ s = -1)
    (hcompat : τ 1 = τ 0 * s) (k i : Fin 2) :
    |u k - (τ k * τ i) * u i - recordedTranslation s c k i| ≤ |u 1 - (s * u 0 + c)| := by
  rw [sign_product τ hτ s hcompat]
  fin_cases k <;> fin_cases i <;> norm_num [Fin.ext_iff, recordedTranslation]
  · have he : u 0 - s * u 1 + s * c = -s * (u 1 - (s * u 0 + c)) := by
      rcases hs with rfl | rfl <;> ring
    rw [he, abs_mul]
    rcases hs with rfl | rfl <;> norm_num
  · exact le_of_eq (congrArg abs (by ring))

private theorem recorded_gradient_error
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M]
    (g : SmoothRiemannianMetric J M) (y : M) (X : Fin 2 → TangentSpace J y)
    (τ : Fin 2 → ℝ) (hτ : ∀ i, τ i = 1 ∨ τ i = -1)
    (s : ℝ) (hs : s = 1 ∨ s = -1) (hcompat : τ 1 = τ 0 * s) (k i : Fin 2) :
    Real.sqrt (g.inner y (X k - (τ k * τ i) • X i) (X k - (τ k * τ i) • X i)) ≤
      Real.sqrt (g.inner y (X 1 - s • X 0) (X 1 - s • X 0)) := by
  rw [sign_product τ hτ s hcompat]
  fin_cases k <;> fin_cases i <;> norm_num [Fin.ext_iff]
  apply le_of_eq
  congr 1
  rcases hs with rfl | rfl <;> ring

theorem exists_uniform_graphs_of_recorded_collar_estimates (Cₒ : ℝ) (hCₒ : 0 < Cₒ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] (J : ModelWithCorners ℝ F H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M],
    ∀ (g : SmoothRiemannianMetric J M) (C : Fin 2 → cylindricalChart J (M := M))
      (U : ∀ j, Set (C j).domain) (ε : ℝ), 0 ≤ ε → ε < ε₀ →
    (∀ j, (C j).metricCloseOn g ε (U j)) →
    ∀ (s c : ℝ), (s = 1 ∨ s = -1) →
    ∀ (τ : Fin 2 → ℝ), (∀ j, τ j = 1 ∨ τ j = -1) → τ 1 = τ 0 * s →
    ∀ (k i : Fin 2) (l r : ℝ) (hwidth : 1 ≤ r - l),
    ∀ hcollar : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc l r,
      (x.1, τ k * (x.2 : ℝ)) ∈ (C k).domain,
    let e := fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc l r ↦
      ((C k).chart ⟨(x.1, τ k * (x.2 : ℝ)), hcollar x⟩ : M)
    (∀ j x, e x ∈ (C j).region (U j)) →
    (∀ x, |(C 1).axial (e x) - (s * (C 0).axial (e x) + c)| ≤
      Cₒ * ε / Real.sqrt (C 0).scale) →
    (∀ x, Real.sqrt (g.inner (e x)
      (gradFun g (C 1).axial (e x) - s • gradFun g (C 0).axial (e x))
      (gradFun g (C 1).axial (e x) - s • gradFun g (C 0).axial (e x))) ≤ Cₒ * ε) →
    ∃ a b : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ,
      Continuous a ∧ Continuous b ∧ (∀ p, a p < b p) ∧
      ∃ ha : ∀ p, (p, τ i * a p) ∈ (C i).domain,
      ∃ hb : ∀ p, (p, τ i * b p) ∈ (C i).domain,
        range (fun p ↦ ((C i).chart ⟨(p, τ i * a p), ha p⟩ : M)) =
          range (fun p ↦ e (p, ⟨l, le_rfl, by linarith only [hwidth]⟩)) ∧
        range (fun p ↦ ((C i).chart ⟨(p, τ i * b p), hb p⟩ : M)) =
          range (fun p ↦ e (p, ⟨r, by linarith only [hwidth], le_rfl⟩)) ∧
        let A := {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ |
          a x.1 ≤ τ i * x.2 ∧ τ i * x.2 ≤ b x.1}
        A ⊆ (C i).domain ∧
        range e = (C i).region ((Subtype.val : (C i).domain →
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) ⁻¹' A) := by
  let C' : ℝ := max Cₒ 17292
  have hC' : 0 < C' := hCₒ.trans_le (le_max_left _ _)
  obtain ⟨ε₀, hε₀, hthreshold⟩ :=
    Poincare.Analysis.exists_uniform_collar_error_threshold 1 C' zero_lt_one hC'
  refine ⟨ε₀, hε₀, ?_⟩
  intro F H M _ _ _ _ J _ _ _ _ _ g C U ε hεnonneg hε hmetric s c hs τ hτ hcompat
    k i l r hwidth hcollar e hboth hvalue hgradient
  have hlr : l < r := by linarith only [hwidth]
  obtain ⟨heps, _, htrans, B, _, _, hscale⟩ := hthreshold ε hεnonneg hε
  have herror : Cₒ * ε ≤ C' * ε := mul_le_mul_of_nonneg_right (le_max_left _ _) hεnonneg
  have hratio : |(C 0).scale / (C 1).scale - 1| ≤ C' * ε := by
    let p : S := ⟨EuclideanSpace.single 0 1, by simp⟩
    let x : S × Icc l r := (p, ⟨l, le_rfl, hlr.le⟩)
    exact ((C 0).scale_ratio_of_metricCloseOn (C 1) g ε heps (hmetric 0) (hmetric 1)
      (e x) (hboth 0 x) (hboth 1 x)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hεnonneg)
  have hwhich : (C k).scale = (C 0).scale ∨ (C k).scale = (C 1).scale := by
    fin_cases k <;> simp
  have hsep : 2 * (C' * ε / Real.sqrt (C 0).scale) <
      (Real.sqrt (C k).scale)⁻¹ * (r - l) := by
    have h := (hscale (C 0).scale (C 1).scale (C 0).scale_pos (C 1).scale_pos
      hratio (C k).scale hwhich).1
    exact h.trans_le (by
      have he := mul_le_mul_of_nonneg_left hwidth (inv_nonneg.mpr (Real.sqrt_nonneg (C k).scale))
      simpa only [mul_one] using he)
  have ht (x : S × Icc l r) : e x ∈ (C i).target := by
    obtain ⟨z, _, hz⟩ := hboth i x
    exact hz ▸ z.property
  have hU (x : S × Icc l r) : (C i).chart.symm ⟨e x, ht x⟩ ∈ U i := by
    obtain ⟨z, ⟨w, hw, rfl⟩, hz⟩ := hboth i x
    have he : (⟨e x, ht x⟩ : (C i).target) = (C i).chart w := Subtype.ext hz.symm
    rw [he, (C i).chart.symm_apply_apply]
    exact hw
  exact (C k).exists_signed_graph_band_of_gradient_close (C i) g
    (τ k) (τ i) (hτ k) (hτ i) l r hlr hcollar ht ε (by linarith only [heps])
    (hmetric i) hU (recordedTranslation s c k i) (C' * ε)
    (C' * ε / Real.sqrt (C 0).scale) htrans
    (fun x ↦ (recorded_gradient_error g (e x) (fun j ↦ gradFun g (C j).axial (e x))
      τ hτ s hs hcompat k i).trans ((hgradient x).trans herror))
    (fun x ↦ (recorded_value_error (fun j ↦ (C j).axial (e x)) τ hτ s c hs hcompat k i).trans
      ((hvalue x).trans (div_le_div_of_nonneg_right herror (Real.sqrt_nonneg _)))) hsep

end Poincare.Geometry.Neck

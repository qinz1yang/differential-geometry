import DifferentialGeometry.Geometry.Collapse.EdgeInterpolationTransversality

/-!
# Consumer: a shifted parabola model on the plane

The model map `u₀(p) = (p.1, p.2²)` on the plane has, at level `c = 0` and sublevel value `e = 1`,
the model fibre `{0} × [-1, 1]` with boundary `{(0, ±1)}`. A source map `w = u₀ + (a, b)` with
`|a|, |b| ≤ 1/10` has the same differential; `exists_edgeInterp_fibre_isotopy` gives a compactly
supported `C¹` isotopy of the plane carrying `{p.1 = 0, p.2² ≤ 1}` onto
`{p.1 + a = 0, p.2² + b ≤ 1}` and the two boundary points onto the two boundary points
(`shiftedParabola_fibre_isotopy`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- The differential of the parabola model `(p.1, p.2²) + (a, b)` on the plane. -/
theorem hasMFDerivAt_shiftedParabola (a b : ℝ) (p : ℝ × ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun q : ℝ × ℝ => (q.1 + a, q.2 * q.2 + b)) p
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ + p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)) :=
  ((hasFDerivAt_fst.add_const a).prodMk
    ((hasFDerivAt_snd.mul hasFDerivAt_snd).add_const b)).hasMFDerivAt

theorem contMDiff_shiftedParabola (a b : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (2 : ℕ) (fun q : ℝ × ℝ => (q.1 + a, q.2 * q.2 + b)) :=
  ((contDiff_fst.add contDiff_const).prodMk
    ((contDiff_snd.mul contDiff_snd).add contDiff_const)).contMDiff

theorem mfderiv_shiftedParabola_apply (a b : ℝ) (p X : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun q : ℝ × ℝ => (q.1 + a, q.2 * q.2 + b)) p X =
      (X.1, p.2 * X.2 + p.2 * X.2) := by
  rw [(hasMFDerivAt_shiftedParabola a b p).mfderiv]
  rfl

/-- **Concrete consumer.** For `|a|, |b| ≤ 1/10` the segment `{0} × [-1, 1]` is isotopic, by a
compactly supported `C¹` isotopy of the plane, to `{-a} × {p.2² ≤ 1 - b}`, boundary to boundary. -/
theorem shiftedParabola_fibre_isotopy {a b : ℝ} (ha : |a| ≤ 1 / 10) (hb : |b| ≤ 1 / 10) :
    ∃ (K : Set (ℝ × ℝ)) (Φ : ℝ → (ℝ × ℝ) ≃ₘ^((2 - 1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯
        (ℝ × ℝ)),
      IsCompact K ∧ (∀ t x, x ∉ K → Φ t x = x) ∧
      Φ 1 '' {p | p.1 = 0 ∧ p.2 * p.2 ≤ 1} = {p | p.1 + a = 0 ∧ p.2 * p.2 + b ≤ 1} ∧
      Φ 1 '' {p | p.1 = 0 ∧ p.2 * p.2 = 1} = {p | p.1 + a = 0 ∧ p.2 * p.2 + b = 1} := by
  have h0 := contMDiff_shiftedParabola 0 0
  have hw := contMDiff_shiftedParabola a b
  have hd0 := mfderiv_shiftedParabola_apply 0 0
  have hdw := mfderiv_shiftedParabola_apply a b
  obtain ⟨K, Φ, hK, -, -, hoff, h1, h1b⟩ := exists_edgeInterp_fibre_isotopy (le_refl 2) h0 hw
    (c := 0) (e := 1) (δ := 1 / 10)
    (fun x => ⟨by simpa using ha, by simpa using hb⟩)
    (fun x _ _ => ⟨((1 : ℝ), (0 : ℝ)), by rw [hd0], by rw [hdw]; norm_num⟩)
    (fun x _ hx2 => by
      have hx : x.2 ≠ 0 := by
        intro h
        rw [h] at hx2
        norm_num at hx2
      refine ⟨((1 : ℝ), (0 : ℝ)), ((0 : ℝ), 1 / (2 * x.2)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hd0]
      · rw [hd0]
      · rw [hd0]; simp
      · rw [hd0]; field_simp; norm_num
      · rw [hdw]; norm_num
      · rw [hdw]; norm_num
      · rw [hdw]; simp
      · rw [hdw, hd0]; simp)
    (isCompact_closedBall (0 : ℝ × ℝ) 3) (fun x hx1 hx2 => by
      simp only [add_zero, sub_zero] at hx1 hx2
      rw [mem_closedBall, dist_zero_right, Prod.norm_def]
      refine max_le ?_ ?_
      · rw [Real.norm_eq_abs]; linarith
      · rw [Real.norm_eq_abs]
        nlinarith [abs_mul_abs_self x.2, abs_nonneg x.2])
  refine ⟨K, Φ, hK, hoff, ?_, ?_⟩
  · simpa using h1
  · simpa using h1b

end DifferentialGeometry.Geometry.Collapse

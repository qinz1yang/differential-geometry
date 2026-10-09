import DifferentialGeometry.Geometry.Collapse.EdgeValueComparison
import DifferentialGeometry.Geometry.Collapse.EdgeInterpolationDiskBundleApplications

/-!
# A quotient-controlled shifted parabola consumes the LFR28 value kernel

Primitive small smoothing error and a small scale perturbation determine the actual second
shift a / (1 + l). The new quotient bound supplies the global interpolation value hypothesis;
the accepted G1 theorem then yields a compactly supported isotopy, including its boundary.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

theorem shiftedParabola_edgeValue_hval {a l : ℝ} (ha : |a| ≤ 1 / 100000)
    (hl : 0 ≤ l) (hlmax : l ≤ 1 / 100000) :
    ∀ x : ℝ × ℝ, |(x.1 + a, x.2 * x.2 + a / (1 + l)).1 - (x.1, x.2 * x.2).1| ≤ 1 / 10 ∧
      |(x.1 + a, x.2 * x.2 + a / (1 + l)).2 - (x.1, x.2 * x.2).2| ≤ 1 / 10
 := by
  have hb := abs_edgeValueQuotient_sub_model_le
    (Δ := 1) (μ := 1 / 100000) (τ := 0) (h := 0) (l := l)
    (d := 0) (b := 0) (r := 0) (F := a) (G := 0) (ρ := 1 + l)
    (by norm_num) hl (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by simpa using ha) (by norm_num) (by norm_num) (by norm_num)
    (by simp [abs_of_nonneg hl])
  have hquot : |a / (1 + l)| ≤ 1 / 10 := by
    simp only [sub_zero, mul_one] at hb
    linarith
  intro x
  simp only [add_sub_cancel_left]
  exact ⟨ha.trans (by norm_num), hquot⟩

theorem shiftedParabola_edgeValue_fibre_isotopy {a l : ℝ} (ha : |a| ≤ 1 / 100000)
    (hl : 0 ≤ l) (hlmax : l ≤ 1 / 100000) :
    ∃ (K : Set (ℝ × ℝ))
      (Φ : ℝ → (ℝ × ℝ) ≃ₘ^((1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ (ℝ × ℝ)),
      IsCompact K ∧ (∀ t x, x ∉ K → Φ t x = x) ∧
      Φ 1 '' {p | p.1 = 0 ∧ p.2 * p.2 ≤ 1} =
        {p | p.1 + a = 0 ∧ p.2 * p.2 + a / (1 + l) ≤ 1} ∧
      Φ 1 '' {p | p.1 = 0 ∧ p.2 * p.2 = 1} =
        {p | p.1 + a = 0 ∧ p.2 * p.2 + a / (1 + l) = 1}
 := by
  let u₀ : ℝ × ℝ → ℝ × ℝ := fun x => (x.1, x.2 * x.2)
  let w : ℝ × ℝ → ℝ × ℝ := fun x => (x.1 + a, x.2 * x.2 + a / (1 + l))
  have hmodel : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (2 : ℕ) u₀ := by
    simpa [u₀] using contMDiff_shiftedParabola 0 0
  have hsource := contMDiff_shiftedParabola a (a / (1 + l))
  have hval : ∀ x, |(w x).1 - (u₀ x).1| ≤ 1 / 10 ∧
      |(w x).2 - (u₀ x).2| ≤ 1 / 10 := shiftedParabola_edgeValue_hval ha hl hlmax
  have hmodelDerivative := mfderiv_parabolaModel_apply
  have hsourceDerivative := mfderiv_shiftedParabola_apply a (a / (1 + l))
  have hrow : ∀ x, |(u₀ x).1 - 0| ≤ 1 / 10 → (u₀ x).2 ≤ 1 + 1 / 10 →
      ∃ v : ℝ × ℝ, (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) u₀ x v).1 = 1 ∧
        |(mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) w x v).1 - 1| ≤ 1 / 1000 := by
    intro x hfirst hsecond
    clear hfirst hsecond
    refine ⟨(1, 0), ?_, ?_⟩
    · exact congrArg Prod.fst (hmodelDerivative x (1, 0))
    · rw [hsourceDerivative]
      norm_num
  have hpair : ∀ x, |(u₀ x).1 - 0| ≤ 1 / 10 → |(u₀ x).2 - 1| ≤ 1 / 10 →
      ∃ v₁ v₂ : ℝ × ℝ,
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) u₀ x v₁).1 = 1 ∧
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) u₀ x v₂).1 = 0 ∧
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) u₀ x v₁).2 = 0 ∧
        1 / 2 ≤ (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) u₀ x v₂).2 ∧
        |(mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) w x v₁).1 - 1| ≤ 1 / 1000 ∧
        |(mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) w x v₂).1| ≤ 1 / 1000 ∧
        |(mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) w x v₁).2| ≤ 1 / 1000 ∧
        |(mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) w x v₂).2 -
          (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) u₀ x v₂).2| ≤ 1 / 1000 := by
    intro x hfirst hsecond
    clear hfirst
    have hx2 : x.2 ≠ 0 := by
      intro hx
      change |x.2 * x.2 - 1| ≤ 1 / 10 at hsecond
      rw [hx] at hsecond
      norm_num at hsecond
    refine ⟨(1, 0), (0, 1 / (2 * x.2)), ?_⟩
    simp only [u₀, w, hmodelDerivative, hsourceDerivative]
    have hc : x.2 * (1 / (2 * x.2)) + x.2 * (1 / (2 * x.2)) = 1 := by
      field_simp
      ring
    rw [hc]
    norm_num
  have hcompact : IsCompact (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) :=
    isCompact_Icc.prod isCompact_Icc
  have henclose : ∀ x, |(u₀ x).1 - 0| ≤ 1 / 10 → (u₀ x).2 ≤ 1 + 1 / 10 →
      x ∈ Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2 := by
    intro x hfirst hsecond
    change |x.1 - 0| ≤ 1 / 10 at hfirst
    change x.2 * x.2 ≤ 1 + 1 / 10 at hsecond
    have hf := abs_le.mp hfirst
    exact ⟨⟨by linarith, by linarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
  obtain ⟨K, Φ, hK, hzero, hsmooth, hoff, hlevel, hboundary⟩ :=
    exists_edgeInterp_fibre_isotopy (r := 2) (by norm_num) hmodel hsource
      (c := 0) (e := 1) (δ := 1 / 10) hval hrow hpair hcompact henclose
  clear hzero hsmooth
  exact ⟨K, Φ, hK, hoff, hlevel, hboundary⟩

end DifferentialGeometry.Geometry.Collapse

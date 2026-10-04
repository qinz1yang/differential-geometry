import DifferentialGeometry.Geometry.Collapse.EdgeInterpolationDiskBundle
import DifferentialGeometry.Geometry.Collapse.EdgeInterpolationTransversalityApplications

/-!
# Consumer: the shifted parabola strip is a trivial bundle over `(-1/2, 1/2)`

Model `u₀(p) = (p.1, p.2²)` and source `u(p) = (p.1 + a, p.2² + b)` on the plane, `j = id`,
`|a|, |b| ≤ 1/10`, sublevel value `e = 1`, level range `(-1, 1)`. `edgeInterp_disk_bundle` gives:
the source fibre `{p.1 + a = 0, p.2² + b ≤ 1}` is (smoothly, hence topologically) the model segment
`{p.1 = 0, p.2² ≤ 1}`, and the source strip over `(-1/2, 1/2)` is the product of that fibre with the
interval (`shiftedParabola_disk_bundle`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- The differential of the parabola model `(p.1, p.2²)`. -/
theorem hasMFDerivAt_parabolaModel (p : ℝ × ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun q : ℝ × ℝ => (q.1, q.2 * q.2)) p
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ + p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)) :=
  (hasFDerivAt_fst.prodMk (hasFDerivAt_snd.mul hasFDerivAt_snd)).hasMFDerivAt

theorem mfderiv_parabolaModel_apply (p X : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun q : ℝ × ℝ => (q.1, q.2 * q.2)) p X =
      (X.1, p.2 * X.2 + p.2 * X.2) := by
  rw [(hasMFDerivAt_parabolaModel p).mfderiv]
  rfl

private theorem plane_finrank : Module.finrank ℝ (ℝ × ℝ) = 0 + 1 + Module.finrank ℝ ℝ := by
  simp

/-- **Concrete consumer.** For `|a|, |b| ≤ 1/10` the source segment `{p.1 + a = 0, p.2² + b ≤ 1}` is
homeomorphic to the model segment `{p.1 = 0, p.2² ≤ 1}`, and the source strip
`{-1/2 < p.1 + a < 1/2, p.2² + b ≤ 1}` is the continuous injective image of (fibre) × (interval) over
the identity of the interval. -/
theorem shiftedParabola_disk_bundle {a b : ℝ} (ha : |a| ≤ 1 / 10) (hb : |b| ≤ 1 / 10) :
    Nonempty ({x : ℝ × ℝ // x.1 = 0 ∧ 0 ≤ 1 - x.2 * x.2} ≃ₜ
      {y : ℝ × ℝ // y.1 + a = 0 ∧ 0 ≤ 1 - (y.2 * y.2 + b)}) ∧
    ∃ Θ : {y : ℝ × ℝ // y.1 + a = 0 ∧ 0 ≤ 1 - (y.2 * y.2 + b)} × Ioo (-(1 / 2) : ℝ) (1 / 2) →
        ℝ × ℝ,
      Continuous Θ ∧ Injective Θ ∧ (∀ p, (Θ p).1 + a = p.2) ∧
      ∀ y : ℝ × ℝ, y.1 + a ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) → 0 ≤ 1 - (y.2 * y.2 + b) →
        ∃ p, Θ p = y := by
  let j : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ((3 : ℕ) : WithTop ℕ∞) :=
    (Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ((3 : ℕ) : WithTop ℕ∞)).toPartialDiffeomorph
  have hj : j.source = univ := rfl
  have hjt : j.target = univ := rfl
  have hu₀ : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun q : ℝ × ℝ => (q.1, q.2 * q.2)) :=
    (contDiff_fst.prodMk (contDiff_snd.mul contDiff_snd)).contMDiff
  have hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun q : ℝ × ℝ => (q.1 + a, q.2 * q.2 + b)) :=
    ((contDiff_fst.add contDiff_const).prodMk
      ((contDiff_snd.mul contDiff_snd).add contDiff_const)).contMDiff
  have hd0 := mfderiv_parabolaModel_apply
  have hdw : ∀ p X : ℝ × ℝ, mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun z => (fun q : ℝ × ℝ => (q.1 + a, q.2 * q.2 + b)) (j z)) p X =
      (X.1, p.2 * X.2 + p.2 * X.2) := mfderiv_shiftedParabola_apply a b
  have hK : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (-1) 1 →
      IsCompact ((fun y : ℝ × ℝ => (fun q : ℝ × ℝ => (q.1 + a, q.2 * q.2 + b)) y |>.1) ⁻¹' K ∩
        {y | 0 ≤ 1 - ((fun q : ℝ × ℝ => (q.1 + a, q.2 * q.2 + b)) y).2}) := by
    intro K hKc _
    have hK' : IsCompact ((fun t : ℝ => t + a) ⁻¹' K) :=
      (Homeomorph.addRight a).isCompact_preimage.mpr hKc
    refine (hK'.prod (isCompact_Icc (a := (-2 : ℝ)) (b := 2))).of_isClosed_subset ?_ ?_
    · exact (hKc.isClosed.preimage (continuous_fst.add continuous_const)).inter
        (isClosed_le continuous_const
          (continuous_const.sub ((continuous_snd.mul continuous_snd).add continuous_const)))
    · rintro y ⟨hy1, hy2⟩
      refine ⟨hy1, ?_, ?_⟩
      · change 0 ≤ 1 - (y.2 * y.2 + b) at hy2
        have := (abs_le.mp hb).1
        nlinarith
      · change 0 ≤ 1 - (y.2 * y.2 + b) at hy2
        have := (abs_le.mp hb).1
        nlinarith
  set u₀ : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, q.2 * q.2) with hu₀def
  set u : ℝ × ℝ → ℝ × ℝ := fun q => (q.1 + a, q.2 * q.2 + b) with hudef
  have hval : ∀ x, |(u (j x)).1 - (u₀ x).1| ≤ 1 / 10 ∧ |(u (j x)).2 - (u₀ x).2| ≤ 1 / 10 :=
    fun x => ⟨by change |x.1 + a - x.1| ≤ 1 / 10; simpa using ha,
      by change |x.2 * x.2 + b - x.2 * x.2| ≤ 1 / 10; simpa using hb⟩
  have hrow : ∀ x, |(u₀ x).1| ≤ 1 + 1 / 10 → (u₀ x).2 ≤ 1 + 1 / 10 → ∃ X : ℝ × ℝ,
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) u₀ x X).1 = 1 ∧
      |(mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X).1 - 1| ≤ 1 / 1000 :=
    fun x _ _ => ⟨((1 : ℝ), (0 : ℝ)), by rw [hd0], by rw [hdw]; norm_num⟩
  have hpair : ∀ x, |(u₀ x).1| ≤ 1 + 1 / 10 → |(u₀ x).2 - 1| ≤ 1 / 10 → ∃ X₁ X₂ : ℝ × ℝ,
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) u₀ x X₁).1 = 1 ∧
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).1 = 0 ∧
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) u₀ x X₁).2 = 0 ∧
      1 / 2 ≤ (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).2 ∧
      |(mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₁).1 - 1| ≤ 1 / 1000 ∧
      |(mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₂).1| ≤ 1 / 1000 ∧
      |(mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₁).2| ≤ 1 / 1000 ∧
      |(mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₂).2 -
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).2| ≤ 1 / 1000 := by
    intro x _ hx2
    have hx : x.2 ≠ 0 := by
      intro h
      change |x.2 * x.2 - 1| ≤ 1 / 10 at hx2
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
    · rw [hdw, hd0]; simp
  have hb1 : (0 : ℝ) < 1 := one_pos
  let _ := DifferentialGeometry.Manifold.RegularLevel.regularSublevelChartedSpace
    (Ψ := fun x : ℝ × ℝ => (u₀ x).1) (B := fun x => 1 - (u₀ x).2) plane_finrank
    (contDiff_fst.contMDiff.comp hu₀) ((contDiff_const.sub contDiff_snd).contMDiff.comp hu₀)
    (edgeInterp_model_regular j hu₀ hb1 hval hrow)
    (edgeInterp_model_regular_boundary j hu₀ hb1 hval hpair)
  let _ := DifferentialGeometry.Manifold.RegularLevel.regularSublevelChartedSpace
    (Ψ := fun y : ℝ × ℝ => (u y).1) (B := fun y => 1 - (u y).2) plane_finrank
    (contDiff_fst.contMDiff.comp hu) ((contDiff_const.sub contDiff_snd).contMDiff.comp hu)
    (fun y hy hB => edgeInterp_source_regular (by norm_num) j hj hu hval hrow
      (fun y _ _ => by rw [hjt]; exact mem_univ y) y
      (by rw [hy]; exact ⟨by norm_num, by norm_num⟩) hB)
    (fun y hy hB => edgeInterp_source_regular_boundary (by norm_num) j hj hu hval hpair
      (fun y _ _ => by rw [hjt]; exact mem_univ y) y
      (by rw [hy]; exact ⟨by norm_num, by norm_num⟩) hB)
  have hbund := edgeInterp_disk_bundle (le_refl 3) plane_finrank j hj hu₀ hu (b := 1) (e := 1)
    (δ := 1 / 10) hval hrow hpair
    (isCompact_closedBall (0 : ℝ × ℝ) 3)
    (fun x hx1 hx2 => by
      change |x.1| ≤ 1 / 10 at hx1
      change x.2 * x.2 ≤ 1 + 1 / 10 at hx2
      rw [mem_closedBall, dist_zero_right, Prod.norm_def]
      refine max_le ?_ ?_
      · rw [Real.norm_eq_abs]; linarith
      · rw [Real.norm_eq_abs]
        nlinarith [abs_mul_abs_self x.2, abs_nonneg x.2])
    (fun y _ _ => by rw [hjt]; exact mem_univ y) hK
    (a₀ := -(1 / 2)) (b₀ := 1 / 2) (by norm_num) ⟨by norm_num, by norm_num⟩ (by norm_num)
  obtain ⟨⟨e₀⟩, ⟨Θ, hΘs, hΘP, -, hΘi, O, -, -, R, -, hR⟩, -⟩ := hbund
  refine ⟨⟨e₀.toHomeomorph⟩, fun p => Θ (p.1, ⟨p.2.1, p.2.2⟩), ?_, ?_, fun p => (hΘP _).1, ?_⟩
  · exact hΘs.continuous.comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk fun x => x.2.2))
  · intro p q hpq
    have h := hΘi hpq
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun z => (z.2 : ℝ)) h
    exact Prod.ext h1 (Subtype.ext h2)
  · intro y hy hB
    obtain ⟨hR1, hR2⟩ := hR y hy hB
    exact ⟨(⟨R y, hR1⟩, ⟨y.1 + a, hy⟩), hR2⟩

end DifferentialGeometry.Geometry.Collapse

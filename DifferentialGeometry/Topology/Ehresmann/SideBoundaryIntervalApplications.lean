import DifferentialGeometry.Topology.Ehresmann.SideBoundaryInterval

/-!
# Consumer: the closed strip is trivial over intervals

The map `P(x, y) = x` on the plane, restricted to the closed strip `{1 - y² ≥ 0}`, is a proper
submersion, also on the side boundary `{y = ±1}`. Its fibre over `0` is the segment
`{0} × [-1, 1]` with its two boundary points, and `exists_sideBoundary_interval_trivialization`
trivializes the strip over `(-1, 1)` (`strip_sideBoundary_trivialization`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Manifold.RegularLevel

private theorem strip_finrank : Module.finrank ℝ (ℝ × ℝ) = 0 + 1 + Module.finrank ℝ ℝ := by
  simp

/-- The strip derivative: `(x, y) ↦ (x, 1 - y·y)` is a submersion where `y ≠ 0`. -/
theorem surjective_mfderiv_strip {y : ℝ × ℝ} (hy : y.2 ≠ 0) :
    Surjective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun z : ℝ × ℝ => (z.1, 1 - z.2 * z.2)) y) := by
  have hd : HasFDerivAt (fun z : ℝ × ℝ => (z.1, 1 - z.2 * z.2))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (-(y.2 • ContinuousLinearMap.snd ℝ ℝ ℝ + y.2 • ContinuousLinearMap.snd ℝ ℝ ℝ))) y :=
    (hasFDerivAt_fst).prodMk
      (((hasFDerivAt_snd).mul (hasFDerivAt_snd)).const_sub 1)
  rw [mfderiv_eq_fderiv, hd.fderiv]
  intro w
  refine ⟨(w.1, -w.2 / (2 * y.2)), ?_⟩
  apply Prod.ext
  · rfl
  · change -(y.2 * (-w.2 / (2 * y.2)) + y.2 * (-w.2 / (2 * y.2))) = w.2
    field_simp
    ring

/-- **The closed strip is trivial over `(-1, 1)`.** The segment `{0} × [-1, 1]` (a manifold with
boundary) times `(-1, 1)` maps smoothly and injectively onto `(-1, 1) × [-1, 1]` over the first
coordinate, with smooth inverse data. -/
theorem strip_sideBoundary_trivialization :
    letI := regularSublevelChartedSpace (Ψ := fun z : ℝ × ℝ => z.1)
      (B := fun z : ℝ × ℝ => 1 - z.2 * z.2) (I := 𝓘(ℝ, ℝ × ℝ)) strip_finrank
      (contDiff_fst.contMDiff) ((contDiff_const.sub (contDiff_snd.mul contDiff_snd)).contMDiff)
      (fun z _ _ => by
        rw [mfderiv_eq_fderiv, fderiv_fst]
        exact fun v => ⟨(v, 0), rfl⟩)
      (fun z _ hz => surjective_mfderiv_strip (by
        intro h
        rw [h, mul_zero, sub_zero] at hz
        exact one_ne_zero hz))
    let Q : TopologicalSpace.Opens ℝ := ⟨Ioo (-1) 1, isOpen_Ioo⟩
    ∃ Θ : {z : ℝ × ℝ // z.1 = 0 ∧ 0 ≤ 1 - z.2 * z.2} × Q → ℝ × ℝ,
      ContMDiff ((𝓡∂ (0 + 1)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ Θ ∧
      (∀ p, (Θ p).1 = p.2 ∧ 0 ≤ 1 - (Θ p).2 * (Θ p).2) ∧ Injective Θ ∧
      ∀ z : ℝ × ℝ, z.1 ∈ Ioo (-1) 1 → 0 ≤ 1 - z.2 * z.2 → ∃ p, Θ p = z := by
  have hP : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ (fun z : ℝ × ℝ => z.1) := contDiff_fst.contMDiff
  have hB : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ (fun z : ℝ × ℝ => 1 - z.2 * z.2) :=
    (contDiff_const.sub (contDiff_snd.mul contDiff_snd)).contMDiff
  have hreg : ∀ z : ℝ × ℝ, z.1 ∈ Ioo (-2 : ℝ) 2 → 0 ≤ 1 - z.2 * z.2 →
      Surjective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (fun z : ℝ × ℝ => z.1) z) := by
    intro z _ _
    rw [mfderiv_eq_fderiv, fderiv_fst]
    exact fun v => ⟨(v, 0), rfl⟩
  have hregb : ∀ z : ℝ × ℝ, z.1 ∈ Ioo (-2 : ℝ) 2 → 1 - z.2 * z.2 = 0 →
      Surjective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun z : ℝ × ℝ => (z.1, 1 - z.2 * z.2)) z) := by
    intro z _ hz
    apply surjective_mfderiv_strip
    intro h
    rw [h, mul_zero, sub_zero] at hz
    exact one_ne_zero hz
  have hprop : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (-2) 2 →
      IsCompact ((fun z : ℝ × ℝ => z.1) ⁻¹' K ∩ {z | 0 ≤ 1 - z.2 * z.2}) := by
    intro K hK _
    apply (hK.prod (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).of_isClosed_subset
    · exact (hK.isClosed.preimage continuous_fst).inter
        (isClosed_le continuous_const (continuous_const.sub (continuous_snd.mul continuous_snd)))
    · rintro z ⟨hz1, hz2⟩
      change 0 ≤ 1 - z.2 * z.2 at hz2
      refine ⟨hz1, ?_, ?_⟩ <;> nlinarith
  obtain ⟨Θ, hΘs, hΘP, -, hΘi, O, -, -, R, -, hR⟩ :=
    exists_sideBoundary_interval_trivialization (I := 𝓘(ℝ, ℝ × ℝ)) (d := 0) strip_finrank hP hB
      hreg hregb hprop (by norm_num : (-2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1) (by norm_num : (1 : ℝ) < 2)
  exact ⟨Θ, hΘs, hΘP, hΘi, fun z hz hBz => ⟨_, (hR z hz hBz).2⟩⟩

end DifferentialGeometry.Topology.Ehresmann

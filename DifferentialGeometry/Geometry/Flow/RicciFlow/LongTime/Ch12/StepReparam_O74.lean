import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StepThick_O50
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

set_option autoImplicit false

/-! # CH12-O74 G2a: bounded-window thickness for P2 (`[FROZEN] CH12-O74`)

S143 FINDING F1: the window binder `hthickW` (`thickW_shape_O40`, `∀ y ∈ B(4R'')`) is unsatisfiable for
cusped `H`.  The repaired binder `hthickW'` (`thickWB_shape_O74` body) only asks for thickness on the
bounded window `B(a + 1)` and gives `InjOn q` as an extra premise.  P2's thickness conjunct (`∀ μ : ℝ`,
`∀ y ∈ B(a)`) is then produced at the reparametrised isotopy `E' (μ, p) := E (smoothTransition μ, p)`:
`smoothTransition μ ∈ [0,1]`, where hCX3ext's displacement bound keeps `E (·, y)` within distance `1`.

* `speed_reparam_O74`: smoothness and the speed bound survive the reparametrisation (with a universal
  shrink factor `c` of the speed).
* `step_thick_O74`: P2's thickness conjunct at `E'`, from `hthickW'` and displacement `≤ 1` on `[0,1]`.
* `thickWB_of_thickW_O74`: the old window binder implies the new one. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

section CX3
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- Reparametrisation by `Real.smoothTransition` (values in `[0,1]`, `0 ↦ 0`, `1 ↦ 1`): smoothness and
the speed bound (shrunk by the universal factor `c`) survive. -/
theorem speed_reparam_O74 (H : FiniteVolumeHyperbolicModel.{u}) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (E : ℝ × H.Carrier → H.Carrier) (ε : ℝ), 0 ≤ ε →
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ E →
      (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
        let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E (r, p)) μ
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
        H.metric.inner (E (μ, p)) v v ≤ (c * ε) ^ 2) →
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
          (fun q : ℝ × H.Carrier => E (Real.smoothTransition q.1, q.2)) ∧
        ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
          let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E (Real.smoothTransition r, p)) μ
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
          H.metric.inner (E (Real.smoothTransition μ, p)) v v ≤ ε ^ 2 := by
  have hσ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont.continuousOn (s := Icc (0 : ℝ) 1))
  have hC1 : 0 < |C| + 1 := by positivity
  refine ⟨1 / (|C| + 1), by positivity, ?_, fun E ε _ hE hspeed => ⟨?_, ?_⟩⟩
  · rw [div_le_one hC1]; linarith [abs_nonneg C]
  · exact hE.comp ((hσ.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  · intro μ hμ p
    have hσμ : Real.smoothTransition μ ∈ Icc (0 : ℝ) 1 :=
      ⟨Real.smoothTransition.nonneg μ, Real.smoothTransition.le_one μ⟩
    have hg : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E (r, p)) (Real.smoothTransition μ) :=
      (hE.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp)
    have hσd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition μ :=
      mdifferentiableAt_iff_differentiableAt.2 (hσ.differentiable (by simp) μ)
    have hv : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E (Real.smoothTransition r, p)) μ
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ)) =
        deriv Real.smoothTransition μ • mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E (r, p))
          (Real.smoothTransition μ)
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (Real.smoothTransition μ)).symm (1 : ℝ)) := by
      change mfderiv 𝓘(ℝ, ℝ) (𝓡 3) ((fun r => E (r, p)) ∘ Real.smoothTransition) μ _ = _
      rw [mfderiv_comp μ hg hσd, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
        ← map_smul (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E (r, p)) (Real.smoothTransition μ))]
      congr 1
      change fderiv ℝ Real.smoothTransition μ 1 = deriv Real.smoothTransition μ * 1
      rw [mul_one]; rfl
    have hw := hspeed (Real.smoothTransition μ) hσμ p
    have hd : |deriv Real.smoothTransition μ| ≤ |C| + 1 := by
      have := hC μ hμ
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self C]
    have key : ∀ d I : ℝ, I ≤ (1 / (|C| + 1) * ε) ^ 2 → |d| ≤ |C| + 1 → d * (d * I) ≤ ε ^ 2 := by
      intro d I hI hd'
      have hdc : (d * (1 / (|C| + 1))) ^ 2 ≤ 1 := by
        rw [sq_le_one_iff_abs_le_one, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 1 / (|C| + 1)), mul_one_div, div_le_one hC1]
        exact hd'
      calc d * (d * I) = d ^ 2 * I := by ring
        _ ≤ d ^ 2 * (1 / (|C| + 1) * ε) ^ 2 := mul_le_mul_of_nonneg_left hI (sq_nonneg d)
        _ = (d * (1 / (|C| + 1))) ^ 2 * ε ^ 2 := by ring
        _ ≤ 1 * ε ^ 2 := mul_le_mul_of_nonneg_right hdc (sq_nonneg ε)
        _ = ε ^ 2 := one_mul _
    dsimp only
    rw [hv, map_smul, map_smul, smul_apply, smul_eq_mul, smul_eq_mul]
    exact key _ _ hw hd

end CX3

/-- P2's thickness conjunct at the reparametrised isotopy `E (smoothTransition μ, ·)`, from `hthickW'`
(`thickWB_shape_O74` body, inline) and displacement `≤ 1` of `E` on `[0,1]`. -/
theorem step_thick_O74 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (wstar a : ℝ)
    (hthickW' :
      ∃ (ε₀ R₀ T₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ ∃ hT₀ : 0 < T₀,
        ∀ (s : ℝ) (hs : T₀ ≤ s) (q : H.Carrier → (postStage F.observation s).Carrier) (R'' : ℝ),
          R₀ ≤ R'' →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (a + 1), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT₀ hs))
              (postMetric F.observation s)) (q y) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le hT₀ hs)) (postMetric F.observation s)) (q y) r) :
    ∃ (ε₀ R₀ T₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ 0 < T₀ ∧
      ∀ (t t₂ : ℝ) (ht : 0 < t), T₀ ≤ t → ∀ (R' ε' : ℝ) (k' : ℕ), R₀ ≤ R' → ε' ≤ ε₀ → k₀ ≤ k' →
      ∀ f : (s : ℝ) → s ∈ Icc t t₂ → H.Carrier → (postStage F.observation s).Carrier,
        (∀ s (hs : s ∈ Icc t t₂),
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
          Set.InjOn (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
          ∀ k'' : ℕ, k'' ≤ k' → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R'),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ (f s hs) k'' p < ε') →
      ∀ E : ℝ × H.Carrier → H.Carrier,
        (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
          riemannianEDistOf H.metric p (E (μ, p)) ≤ ENNReal.ofReal 1) →
        (∀ s (hs : s ∈ Icc t t₂) (μ : ℝ), ∀ y ∈ riemannianBallOf H.metric H.basepoint (a), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le ht hs.1))
              (postMetric F.observation s)) (f s hs (E (Real.smoothTransition μ, y))) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le ht hs.1)) (postMetric F.observation s))
              (f s hs (E (Real.smoothTransition μ, y))) r) := by
  obtain ⟨ε₀, R₀, T₀, k₀, hε₀, hT₀, hth⟩ := hthickW'
  refine ⟨ε₀, R₀, T₀, k₀, hε₀, hT₀, fun t t₂ ht hTt R' ε' k' hR₀ hε' hk' f hf E hdisp => ?_⟩
  intro s hs μ y hy
  have hσ : Real.smoothTransition μ ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg μ, Real.smoothTransition.le_one μ⟩
  have hy' : riemannianEDistOf H.metric H.basepoint y < ENNReal.ofReal a := hy
  have ha : 0 < a := ENNReal.ofReal_pos.1 (lt_of_le_of_lt zero_le hy')
  have hmem : E (Real.smoothTransition μ, y) ∈ riemannianBallOf H.metric H.basepoint (a + 1) := by
    change riemannianEDistOf H.metric H.basepoint (E (Real.smoothTransition μ, y)) <
      ENNReal.ofReal (a + 1)
    calc riemannianEDistOf H.metric H.basepoint (E (Real.smoothTransition μ, y))
        ≤ riemannianEDistOf H.metric H.basepoint y +
            riemannianEDistOf H.metric y (E (Real.smoothTransition μ, y)) :=
          riemannianEDistOf_triangle _ _ _ _
      _ ≤ riemannianEDistOf H.metric H.basepoint y + ENNReal.ofReal 1 :=
          add_le_add le_rfl (hdisp _ hσ y)
      _ < ENNReal.ofReal a + ENNReal.ofReal 1 := ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hy'
      _ = ENNReal.ofReal (a + 1) := (ENNReal.ofReal_add ha.le zero_le_one).symm
  obtain ⟨hsm, hinj, herr⟩ := hf s hs
  exact hth s (le_trans hTt hs.1) (f s hs) R' hR₀ hsm hinj
    (fun k'' hk'' p hp => lt_of_lt_of_le (herr k'' (le_trans hk'' hk') p hp) hε') _ hmem

/-- The old window binder (`thickW_shape_O40` body) implies `hthickW'` (`thickWB_shape_O74` body). -/
theorem thickWB_of_thickW_O74 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (wstar a : ℝ)
    (hthickW :
      ∃ (ε₀ R₀ T₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ ∃ hT₀ : 0 < T₀,
        ∀ (s : ℝ) (hs : T₀ ≤ s) (q : H.Carrier → (postStage F.observation s).Carrier) (R'' : ℝ),
          R₀ ≤ R'' →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (4 * R''), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT₀ hs))
              (postMetric F.observation s)) (q y) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le hT₀ hs)) (postMetric F.observation s)) (q y) r) :
      ∃ (ε₀ R₀ T₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ ∃ hT₀ : 0 < T₀,
        ∀ (s : ℝ) (hs : T₀ ≤ s) (q : H.Carrier → (postStage F.observation s).Carrier) (R'' : ℝ),
          R₀ ≤ R'' →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (a + 1), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT₀ hs))
              (postMetric F.observation s)) (q y) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le hT₀ hs)) (postMetric F.observation s)) (q y) r := by
  obtain ⟨ε₀, R₀, T₀, k₀, hε₀, hT₀, hth⟩ := hthickW
  refine ⟨ε₀, max R₀ ((a + 1) / 4), T₀, k₀, hε₀, hT₀,
    fun s hs q R'' hR'' hsm _ herr y hy => ?_⟩
  have hR := (le_max_right R₀ ((a + 1) / 4)).trans hR''
  exact hth s hs q R'' ((le_max_left _ _).trans hR'') hsm herr y
    (riemannianBallOf_mono _ _ (by linarith) hy)

end GC.LongTime.Ch12

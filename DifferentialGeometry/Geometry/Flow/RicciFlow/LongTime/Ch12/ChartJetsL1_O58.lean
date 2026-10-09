import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ChartJetBound_O52
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ChartCovNorm_O43
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HModel_S112
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrDef_O19
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.InterpolationIter_O26

/-!
# CH12-O58 G1: L1 R-A (atlas-chart jets of the displacement from `ckErr`) + R-C (small jets)

`[FROZEN] CH12-O58 G1`.  In an atlas chart at `c` with Gram matrix `P` of `H.metric`, the model of
the pullback-error field of `Ψ` is `β (pullbackForm (P ∘ Ψ̃, DΨ̃) − P)` (`errModel_eq_O43`,
`Ψ̃ = id + u_Ψ`), `β = bilinearTensor02_O43` has a continuous linear left inverse, `chartCov_O43`
bounds the model jets by `ckErr`, and `chart_jet_bound_O52` turns small jets of
`pullbackForm (P ∘ Ψ̃, DΨ̃) − P` into bounded jets of `Ψ̃`.  The interpolation lemma
`small_iteratedFDeriv_of_C0_O26` then makes the jets small once `u_Ψ` is `C⁰`-small.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.TensorLieDeriv
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Manifold
open DifferentialGeometry.Geometry DifferentialGeometry.CheegerGromovCompactness
open Bundle Set Metric Filter
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `bilinearTensor02_O43` has a continuous linear left inverse. -/
theorem exists_leftInv_bilinearTensor02_O58 :
    ∃ γ : Tensor0SModel 2 ℝ E3 →L[ℝ] (E3 →L[ℝ] E3 →L[ℝ] ℝ),
      ∀ B : E3 →L[ℝ] E3 →L[ℝ] ℝ, γ (bilinearTensor02_O43 B) = B := by
  refine ⟨(ContinuousLinearMap.compL ℝ E3 _ _
      (continuousMultilinearCurryFin1 ℝ E3 ℝ).toContinuousLinearMap).comp
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E3) ℝ).toContinuousLinearMap,
    fun B => ?_⟩
  ext v w
  simp [bilinearTensor02_O43]

/-- The chart Gram matrix of `H.metric` is smooth, symmetric and positive on the chart target. -/
theorem chartGram_facts_O58 (H : FiniteVolumeHyperbolicModel.{u}) (c : H.Carrier) :
    ContDiffOn ℝ ∞ (pullbackMetricCoefficients H.metric (interiorChart (𝓡 3) ∞ c).symm)
      (extChartAt (𝓡 3) c).target ∧
    (∀ z ∈ (extChartAt (𝓡 3) c).target, ∀ v w : E3,
      pullbackMetricCoefficients H.metric (interiorChart (𝓡 3) ∞ c).symm z v w =
        pullbackMetricCoefficients H.metric (interiorChart (𝓡 3) ∞ c).symm z w v) ∧
    (∀ z ∈ (extChartAt (𝓡 3) c).target, ∀ v : E3, v ≠ 0 →
      0 < pullbackMetricCoefficients H.metric (interiorChart (𝓡 3) ∞ c).symm z v v) := by
  have hdt : (interiorChart (𝓡 3) ∞ c).target = (extChartAt (𝓡 3) c).target := by
    rw [interiorChart_target, (isOpen_extChartAt_target c).interior_eq]
  refine ⟨?_, fun z _ v w => ?_, fun z hz v hv => ?_⟩
  · rw [← hdt]
    exact contDiffOn_pullback_metric_coefficients H.metric (interiorChart (𝓡 3) ∞ c).open_target
      (interiorChart (𝓡 3) ∞ c).contMDiffOn_invFun
  · simp only [pullbackMetricCoefficients_apply]
    exact H.metric.symm _ _ _
  · have hz' : z ∈ (interiorChart (𝓡 3) ∞ c).symm.source := by
      change z ∈ (interiorChart (𝓡 3) ∞ c).target
      rw [hdt]; exact hz
    exact pullbackMetricCoefficients_pos H.metric
      (((interiorChart (𝓡 3) ∞ c).symm.isLocalDiffeomorphAt 𝓘(ℝ, E3) (𝓡 3) ∞ hz'
        ).mfderivToContinuousLinearEquiv (by simp)).injective hv

/-- The displacement is smooth on chart points whose image stays in the chart. -/
theorem displacement_contDiffOn_O58 {H : FiniteVolumeHyperbolicModel.{u}} (c : H.Carrier)
    {Ψ : H.Carrier → H.Carrier} {W : Set H.Carrier} (hW : IsOpen W)
    (hΨ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Ψ W) {V : Set E3}
    (hVW : V ⊆ (extChartAt (𝓡 3) c).target ∩ (extChartAt (𝓡 3) c).symm ⁻¹' W)
    (hVs : ∀ y ∈ V, Ψ ((extChartAt (𝓡 3) c).symm y) ∈ (extChartAt (𝓡 3) c).source) :
    ContDiffOn ℝ ∞ (chartDisplacement_CX3 (I := 𝓡 3) c Ψ) V := fun x hx =>
  (chartDisplacement_contDiffAt_CX3 c hW hΨ (hVW hx).1 (hVW hx).2 (hVs x hx)).contDiffWithinAt

/-- The chart model of the pullback-error field is `β (pullbackForm (P ∘ Ψ̃, DΨ̃) − P)`. -/
theorem model_eq_pullbackForm_O58 (H : FiniteVolumeHyperbolicModel.{u}) (c : H.Carrier)
    {Ψ : H.Carrier → H.Carrier} {W : Set H.Carrier} (hW : IsOpen W)
    (hΨ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Ψ W) {y : E3}
    (hy : y ∈ (extChartAt (𝓡 3) c).target) (hyW : (extChartAt (𝓡 3) c).symm y ∈ W)
    (hs : Ψ ((extChartAt (𝓡 3) c).symm y) ∈ (extChartAt (𝓡 3) c).source) :
    tensor0SModelInChart (I := 𝓡 3) 2 c (fun q : H.Carrier =>
        ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
          ((1 : ℝ) • localPullInner H.metric Ψ q - H.metric.inner q)).uncurryLeft) y =
      bilinearTensor02_O43 (pullbackForm
        (pullbackMetricCoefficients H.metric (interiorChart (𝓡 3) ∞ c).symm
          (y + chartDisplacement_CX3 (I := 𝓡 3) c Ψ y),
          fderiv ℝ (fun z => z + chartDisplacement_CX3 (I := 𝓡 3) c Ψ z) y) -
        pullbackMetricCoefficients H.metric (interiorChart (𝓡 3) ∞ c).symm y) := by
  have hF' : MDifferentiableAt (𝓡 3) (𝓡 3) Ψ ((extChartAt (𝓡 3) c).symm y) :=
    (hΨ.contMDiffAt (hW.mem_nhds hyW)).mdifferentiableAt (by simp)
  rw [errModel_eq_O43 H c hy hF' hs]
  have : (extChartAt (𝓡 3) c ∘ Ψ ∘ (extChartAt (𝓡 3) c).symm) =
      fun z => z + chartDisplacement_CX3 (I := 𝓡 3) c Ψ z := by
    funext z; simp [chartDisplacement_CX3]
  rw [this]
  rfl

/-- **R-A** (`[FROZEN] CH12-O58 G1`): small `ckErr` through order `n + 1` on `W` bounds the chart
jets of the displacement through order `n + 2` on every open `V ⊆ Kz` with `Ψ̃ V ⊆ Kz`. -/
theorem chart_bounded_jets_O58 (H : FiniteVolumeHyperbolicModel.{u}) (c : H.Carrier)
    {W : Set H.Carrier} (hW : IsOpen W) {Kz : Set E3} (hKz : IsCompact Kz)
    (hKzW : Kz ⊆ (extChartAt (𝓡 3) c).target ∩ (extChartAt (𝓡 3) c).symm ⁻¹' W) (n : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ Ψ : H.Carrier → H.Carrier, ContMDiffOn (𝓡 3) (𝓡 3) ∞ Ψ W →
      (∀ j : ℕ, j ≤ n + 1 → ∀ p ∈ W, ckErr_O19 H H.metric 1 Ψ j p < δ) →
      ∀ V : Set E3, IsOpen V → V ⊆ Kz →
      (∀ y ∈ V, Ψ ((extChartAt (𝓡 3) c).symm y) ∈ (extChartAt (𝓡 3) c).source ∧
        y + chartDisplacement_CX3 (I := 𝓡 3) c Ψ y ∈ Kz) →
      ∀ i : ℕ, i ≤ n + 2 → ∀ y ∈ V,
        ‖iteratedFDeriv ℝ i (chartDisplacement_CX3 (I := 𝓡 3) c Ψ) y‖ ≤ C := by
  obtain ⟨hP, hsym, hpos⟩ := chartGram_facts_O58 H c
  set P := pullbackMetricCoefficients H.metric (interiorChart (𝓡 3) ∞ c).symm with hPdef
  have hT : IsOpen (extChartAt (𝓡 3) c).target := isOpen_extChartAt_target c
  have hKzT : Kz ⊆ (extChartAt (𝓡 3) c).target := fun y hy => (hKzW hy).1
  obtain ⟨η, hη, C, hC⟩ := chart_jet_bound_O52 hT hP hsym hpos hKz hKzT n
  obtain ⟨C₁, hC₁, hcov⟩ := chartCov_O43 H.metric c hW hKz hKzW 2 (n + 1)
  obtain ⟨γ, hγ⟩ := exists_leftInv_bilinearTensor02_O58
  obtain ⟨R₀, hR₀⟩ := hKz.isBounded.exists_norm_le
  have hden : 0 < (‖γ‖ + 1) * (C₁ + 1) * ((n : ℝ) + 2) := by positivity
  refine ⟨η / ((‖γ‖ + 1) * (C₁ + 1) * ((n : ℝ) + 2)), div_pos hη hden, C + (1 + |R₀|), ?_⟩
  intro Ψ hΨ herr V hV hVK hVs i hi y hy
  set δ := η / ((‖γ‖ + 1) * (C₁ + 1) * ((n : ℝ) + 2)) with hδ
  set u := chartDisplacement_CX3 (I := 𝓡 3) c Ψ with hu_def
  have hVW : V ⊆ (extChartAt (𝓡 3) c).target ∩ (extChartAt (𝓡 3) c).symm ⁻¹' W :=
    fun x hx => hKzW (hVK hx)
  have hu : ContDiffOn ℝ ∞ u V := displacement_contDiffOn_O58 c hW hΨ hVW (fun x hx => (hVs x hx).1)
  have hΨt : ContDiffOn ℝ ∞ (fun z => z + u z) V := contDiffOn_id.add hu
  have hmaps : MapsTo (fun z => z + u z) V Kz := fun x hx => (hVs x hx).2
  have hX : (‖γ‖ + 1) * ((C₁ + 1) * (((n : ℝ) + 2) * δ)) = η := by
    rw [hδ]; field_simp
  have hjet : ∀ i : ℕ, i ≤ n + 1 → ∀ y ∈ V,
      ‖iteratedFDeriv ℝ i (fun x => pullbackForm (P (x + u x), fderiv ℝ (fun z => z + u z) x) -
        P x) y‖ ≤ η := by
    intro i' hi' y' hy'
    have hf : ContDiffAt ℝ ∞ (fun x => pullbackForm (P (x + u x), fderiv ℝ (fun z => z + u z) x) -
        P x) y' := by
      have h1 : ContDiffOn ℝ ∞ (fun x => P (x + u x)) V :=
        hP.comp hΨt (fun x hx => hKzT (hmaps hx))
      have h2 : ContDiffOn ℝ ∞ (fderiv ℝ (fun z => z + u z)) V :=
        hΨt.fderiv_of_isOpen hV (by exact_mod_cast le_top)
      have h3 := (pullbackForm.contDiff.comp_contDiffOn (h1.prodMk h2)).sub
        (hP.mono (fun x hx => hKzT (hVK hx)))
      exact h3.contDiffAt (hV.mem_nhds hy')
    have hβf : ContDiffAt ℝ ∞ (fun x => bilinearTensor02_O43 (pullbackForm (P (x + u x),
        fderiv ℝ (fun z => z + u z) x) - P x)) y' :=
      bilinearTensor02_contDiff_O43.contDiffAt.comp y' hf
    have hmodel : (tensor0SModelInChart (I := 𝓡 3) 2 c (fun q : H.Carrier =>
        ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
          ((1 : ℝ) • localPullInner H.metric Ψ q - H.metric.inner q)).uncurryLeft)) =ᶠ[𝓝 y']
        (fun x => bilinearTensor02_O43 (pullbackForm (P (x + u x),
          fderiv ℝ (fun z => z + u z) x) - P x)) :=
      Filter.eventually_of_mem (hV.mem_nhds hy') fun x hx =>
        model_eq_pullbackForm_O58 H c hW hΨ (hVW hx).1 (hVW hx).2 (hVs x hx).1
    have hEq : (fun x => pullbackForm (P (x + u x), fderiv ℝ (fun z => z + u z) x) - P x) =
        γ ∘ (fun x => bilinearTensor02_O43 (pullbackForm (P (x + u x),
          fderiv ℝ (fun z => z + u z) x) - P x)) := funext fun x => (hγ _).symm
    have hsum : ∑ l ∈ Finset.range (n + 1 + 1), tensor0SFiberNorm H.metric
        ((extChartAt (𝓡 3) c).symm y') (2 + l) (iteratedMetricCovariantDerivative H.metric 2
          (fun q : H.Carrier =>
            ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
              ((1 : ℝ) • localPullInner H.metric Ψ q - H.metric.inner q)).uncurryLeft) l
          ((extChartAt (𝓡 3) c).symm y')) ≤ ((n : ℝ) + 2) * δ := by
      calc _ ≤ ∑ _l ∈ Finset.range (n + 1 + 1), δ := Finset.sum_le_sum fun l hl =>
            (herr l (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)) _ (hVW hy').2).le
        _ = ((n : ℝ) + 2) * δ := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    have hcov' := hcov _ (errField_contMDiffOn_O43 H hW hΨ) y' (hVK hy') i' hi'
    have hγ0 : 0 ≤ ‖γ‖ := norm_nonneg _
    have hδ0 : 0 ≤ ((n : ℝ) + 2) * δ := by positivity
    calc _ = ‖iteratedFDeriv ℝ i' (γ ∘ (fun x => bilinearTensor02_O43 (pullbackForm (P (x + u x),
          fderiv ℝ (fun z => z + u z) x) - P x))) y'‖ := by rw [← hEq]
      _ ≤ ‖γ‖ * ‖iteratedFDeriv ℝ i' (fun x => bilinearTensor02_O43 (pullbackForm (P (x + u x),
          fderiv ℝ (fun z => z + u z) x) - P x)) y'‖ :=
          γ.norm_iteratedFDeriv_comp_left hβf (by exact_mod_cast le_top)
      _ = ‖γ‖ * ‖iteratedFDeriv ℝ i' (tensor0SModelInChart (I := 𝓡 3) 2 c (fun q : H.Carrier =>
        ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
          ((1 : ℝ) • localPullInner H.metric Ψ q - H.metric.inner q)).uncurryLeft)) y'‖ := by
          rw [(hmodel.iteratedFDeriv ℝ i').eq_of_nhds]
      _ ≤ ‖γ‖ * (C₁ * (((n : ℝ) + 2) * δ)) :=
          mul_le_mul_of_nonneg_left (hcov'.trans (mul_le_mul_of_nonneg_left hsum hC₁)) hγ0
      _ ≤ (‖γ‖ + 1) * ((C₁ + 1) * (((n : ℝ) + 2) * δ)) := by
          gcongr <;> linarith
      _ = η := hX
  have hbd := hC (fun z => z + u z) V hV hVK hΨt hmaps hjet i hi y hy
  have hyK : ‖y‖ ≤ |R₀| := (hR₀ y (hVK hy)).trans (le_abs_self _)
  have hid : ‖iteratedFDeriv ℝ i (id : E3 → E3) y‖ ≤ 1 + |R₀| := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos'
    · subst h0; rw [norm_iteratedFDeriv_zero]; simp only [id]; linarith [abs_nonneg R₀]
    · exact (norm_iteratedFDeriv_id_le_S112 y hpos').trans (by linarith [abs_nonneg R₀])
  have hsplit : u = (fun z => z + u z) - id := by funext z; simp
  have hyV : y ∈ V := hy
  rw [hsplit, iteratedFDeriv_sub_apply ((hΨt.contDiffAt (hV.mem_nhds hyV)).of_le
    (by exact_mod_cast le_top)) (contDiffAt_id.of_le (by exact_mod_cast le_top))]
  exact (norm_sub_le _ _).trans (add_le_add hbd hid)

/-- `θ := min_{j ≤ k} η j` for a positive family indexed by `j ≤ k`. -/
theorem exists_pos_le_forall_le_O58 (k : ℕ) (η : (j : ℕ) → j ≤ k → ℝ)
    (hη : ∀ j hj, 0 < η j hj) : ∃ θ : ℝ, 0 < θ ∧ ∀ j (hj : j ≤ k), θ ≤ η j hj := by
  have key : ∀ m, m ≤ k → ∃ θ : ℝ, 0 < θ ∧ ∀ j (hj : j ≤ k), j ≤ m → θ ≤ η j hj := by
    intro m
    induction m with
    | zero =>
      intro h0
      refine ⟨η 0 h0, hη 0 h0, fun j hj hjm => ?_⟩
      obtain rfl : j = 0 := by omega
      exact le_rfl
    | succ m ih =>
      intro hm
      obtain ⟨θ, hθ, h⟩ := ih (by omega)
      refine ⟨min θ (η (m + 1) hm), lt_min hθ (hη _ _), fun j hj hjm => ?_⟩
      rcases Nat.lt_or_ge j (m + 1) with h1 | h1
      · exact (min_le_left _ _).trans (h j hj (by omega))
      · obtain rfl : j = m + 1 := by omega
        exact min_le_right _ _
  obtain ⟨θ, hθ, h⟩ := key k le_rfl
  exact ⟨θ, hθ, fun j hj => h j hj hj⟩

/-- **R-C** (`[FROZEN] CH12-O58 G1`): with `ckErr` small through order `k + 1` and the displacement
`C⁰`-small (`≤ θ₀`) on `V`, its jets through order `k` are `< ε` at every `y` with
`closedBall y r ⊆ V`. -/
theorem chart_small_jets_O58 (H : FiniteVolumeHyperbolicModel.{u}) (c : H.Carrier)
    {W : Set H.Carrier} (hW : IsOpen W) {Kz : Set E3} (hKz : IsCompact Kz)
    (hKzW : Kz ⊆ (extChartAt (𝓡 3) c).target ∩ (extChartAt (𝓡 3) c).symm ⁻¹' W) (k : ℕ)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ Ψ : H.Carrier → H.Carrier,
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ Ψ W →
      (∀ j : ℕ, j ≤ k + 1 → ∀ p ∈ W, ckErr_O19 H H.metric 1 Ψ j p < δ) →
      ∀ V : Set E3, IsOpen V → V ⊆ Kz →
      (∀ y ∈ V, Ψ ((extChartAt (𝓡 3) c).symm y) ∈ (extChartAt (𝓡 3) c).source ∧
        y + chartDisplacement_CX3 (I := 𝓡 3) c Ψ y ∈ Kz ∧
        ‖chartDisplacement_CX3 (I := 𝓡 3) c Ψ y‖ ≤ θ₀) →
      ∀ j : ℕ, j ≤ k → ∀ y : E3, closedBall y r ⊆ V →
        ‖iteratedFDeriv ℝ j (chartDisplacement_CX3 (I := 𝓡 3) c Ψ) y‖ < ε := by
  obtain ⟨δ, hδ, C, hC⟩ := chart_bounded_jets_O58 H c hW hKz hKzW k
  have hc : 0 < r / ((k : ℝ) + 1) := by positivity
  choose η hη hsmall using fun j (hj : j ≤ k) =>
    small_iteratedFDeriv_of_C0_O26 (E := E3) (F := E3) k hc (le_max_right C 0) j hj ε hε
  obtain ⟨θ₀, hθ₀, hθle⟩ := exists_pos_le_forall_le_O58 k η hη
  refine ⟨δ, hδ, θ₀, hθ₀, ?_⟩
  intro Ψ hΨ herr V hV hVK hVs j hj y hy
  have hVW : V ⊆ (extChartAt (𝓡 3) c).target ∩ (extChartAt (𝓡 3) c).symm ⁻¹' W :=
    fun x hx => hKzW (hVK hx)
  have hu := displacement_contDiffOn_O58 c hW hΨ hVW (fun x hx => (hVs x hx).1)
  have hB : ∀ i : ℕ, i ≤ k + 1 → ∀ z ∈ V,
      ‖iteratedFDeriv ℝ i (chartDisplacement_CX3 (I := 𝓡 3) c Ψ) z‖ ≤ max C 0 :=
    fun i hi z hz => (hC Ψ hΨ herr V hV hVK (fun x hx => ⟨(hVs x hx).1, (hVs x hx).2.1⟩) i
      (by omega) z hz).trans (le_max_left _ _)
  refine hsmall j hj _ V hV hu hB (fun z hz => (hVs z hz).2.2.trans (hθle j hj)) y ?_
  refine (closedBall_subset_closedBall ?_).trans hy
  have hjk : (j : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (by omega : j ≤ k + 1)
  calc (j : ℝ) * (r / ((k : ℝ) + 1)) ≤ ((k : ℝ) + 1) * (r / ((k : ℝ) + 1)) := by gcongr
    _ = r := by field_simp

end GC.LongTime.Ch12

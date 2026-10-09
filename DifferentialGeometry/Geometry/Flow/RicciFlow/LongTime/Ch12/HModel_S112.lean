import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThetaModel_S112

/-!
# CH12-S112 G1b: `hmodel_S112` (single-chart bound (c) of `[FROZEN] CH12-O43 G2`)

For `K` compact in the chart target at `c`, `δ ≤ r/2` small and `F` with chart-displacement `u` whose
jets at `x ∈ K` are `< δ`: near `x` the model of the pullback-error field is
`y ↦ Θ (y, (u y, Du y))` with `Θ` the globally smooth map of `ThetaModel_S112` (cutoff of the chart
Gram matrix `P`, `Θ (y, 0) = 0`), so `hadamard_jets_S112` gives
`‖D^l model x‖ ≤ C_l * ∑_{i ≤ l} ‖D^i (u, Du) x‖ ≤ 2 C_l * ∑_{l' ≤ k+1} ‖D^{l'} u x‖`.
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

/-- Near a good chart point the model of the error field is `Θ (y, (u y, Du y))`. -/
theorem model_eq_theta_S112 (H : FiniteVolumeHyperbolicModel.{u}) (c : H.Carrier)
    {F : H.Carrier → H.Carrier} {O : Set H.Carrier} (hO : IsOpen O)
    (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ F O) {y : E3}
    (hy : y ∈ (extChartAt (𝓡 3) c).target) (hyO : (extChartAt (𝓡 3) c).symm y ∈ O)
    (hFy : F ((extChartAt (𝓡 3) c).symm y) ∈ (extChartAt (𝓡 3) c).source)
    (hu : DifferentiableAt ℝ (chartDisplacement_CX3 (I := 𝓡 3) c F) y)
    (P' : E3 → (E3 →L[ℝ] E3 →L[ℝ] ℝ))
    (h1 : P' y = pullbackMetricCoefficients H.metric (interiorChart (𝓡 3) ∞ c).symm y)
    (h2 : P' (y + chartDisplacement_CX3 (I := 𝓡 3) c F y) =
      pullbackMetricCoefficients H.metric (interiorChart (𝓡 3) ∞ c).symm
        (y + chartDisplacement_CX3 (I := 𝓡 3) c F y)) :
    tensor0SModelInChart (I := 𝓡 3) 2 c (fun q : H.Carrier =>
        ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
          ((1 : ℝ) • localPullInner H.metric F q - H.metric.inner q)).uncurryLeft) y =
      thetaS112 P' (y, (chartDisplacement_CX3 (I := 𝓡 3) c F y,
        fderiv ℝ (chartDisplacement_CX3 (I := 𝓡 3) c F) y)) := by
  have hF' : MDifferentiableAt (𝓡 3) (𝓡 3) F ((extChartAt (𝓡 3) c).symm y) :=
    (hF.contMDiffAt (hO.mem_nhds hyO)).mdifferentiableAt (by simp)
  rw [errModel_eq_O43 H c hy hF' hFy]
  have hfd : fderiv ℝ (extChartAt (𝓡 3) c ∘ F ∘ (extChartAt (𝓡 3) c).symm) y =
      ContinuousLinearMap.id ℝ E3 + fderiv ℝ (chartDisplacement_CX3 (I := 𝓡 3) c F) y := by
    have : (extChartAt (𝓡 3) c ∘ F ∘ (extChartAt (𝓡 3) c).symm) =
        fun z => z + chartDisplacement_CX3 (I := 𝓡 3) c F z := by
      funext z; simp [chartDisplacement_CX3]
    rw [this]
    exact ((hasFDerivAt_id y).add hu.hasFDerivAt).fderiv
  rw [hfd]
  change bilinearTensor02_O43 (pullbackForm (pullbackMetricCoefficients H.metric
      (interiorChart (𝓡 3) ∞ c).symm (y + chartDisplacement_CX3 (I := 𝓡 3) c F y),
      ContinuousLinearMap.id ℝ E3 + fderiv ℝ (chartDisplacement_CX3 (I := 𝓡 3) c F) y) -
      pullbackMetricCoefficients H.metric (interiorChart (𝓡 3) ∞ c).symm y) =
    bilinearTensor02_O43 (pullbackForm (P' (y + chartDisplacement_CX3 (I := 𝓡 3) c F y),
      ContinuousLinearMap.id ℝ E3 + fderiv ℝ (chartDisplacement_CX3 (I := 𝓡 3) c F) y) - P' y)
  rw [h1, h2]

/-- Jets of the pair `(u, Du)`. -/
theorem norm_iteratedFDeriv_pair_le_S112 {u : E3 → E3} {x : E3} (hu : ContDiffAt ℝ ∞ u x)
    (hdu : ContDiffAt ℝ ∞ (fderiv ℝ u) x) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun y => (u y, fderiv ℝ u y)) x‖ ≤
      ‖iteratedFDeriv ℝ i u x‖ + ‖iteratedFDeriv ℝ (i + 1) u x‖ := by
  refine (norm_iteratedFDeriv_prodMk_le_S112 hu hdu i).trans ?_
  rw [norm_iteratedFDeriv_fderiv]

/-- Sum estimate: `∑_{i ≤ l} (a_i + a_{i+1}) ≤ 2 ∑_{j < k+2} a_j` for `l ≤ k`. -/
theorem sum_pair_le_S112 (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) {l k : ℕ} (hl : l ≤ k) :
    ∑ i ∈ Finset.range (l + 1), (a i + a (i + 1)) ≤ 2 * ∑ j ∈ Finset.range (k + 2), a j := by
  rw [Finset.sum_add_distrib]
  have h1 : ∑ i ∈ Finset.range (l + 1), a i ≤ ∑ j ∈ Finset.range (k + 2), a j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun j _ _ => ha j)
  have h2 : ∑ i ∈ Finset.range (l + 1), a (i + 1) ≤ ∑ j ∈ Finset.range (k + 2), a j := by
    have h3 : ∑ j ∈ Finset.range (l + 2), a j = ∑ i ∈ Finset.range (l + 1), a (i + 1) + a 0 :=
      Finset.sum_range_succ' a (l + 1)
    have h4 : ∑ j ∈ Finset.range (l + 2), a j ≤ ∑ j ∈ Finset.range (k + 2), a j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun j _ _ => ha j)
    linarith [ha 0]
  linarith

/-- **G1b.** Single-chart bound (c): `[FROZEN] CH12-O43 G2` `hmodel`, verbatim. -/
theorem hmodel_S112 (H : FiniteVolumeHyperbolicModel.{u}) :
    ∀ (c : H.Carrier) (K : Set (EuclideanSpace ℝ (Fin 3))) (k : ℕ), IsCompact K →
      K ⊆ (extChartAt (𝓡 3) c).target → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
        ∀ (F : H.Carrier → H.Carrier) (O : Set H.Carrier), IsOpen O →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ F O → ∀ x ∈ K, (extChartAt (𝓡 3) c).symm x ∈ O →
          F ((extChartAt (𝓡 3) c).symm x) ∈ (extChartAt (𝓡 3) c).source →
          (∀ l ≤ k + 1, ‖iteratedFDeriv ℝ l (chartDisplacement_CX3 (I := 𝓡 3) c F) x‖ < δ) →
          ∀ l ≤ k, ‖iteratedFDeriv ℝ l (tensor0SModelInChart (I := 𝓡 3) 2 c (fun q : H.Carrier =>
            ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
              ((1 : ℝ) • localPullInner H.metric F q - H.metric.inner q)).uncurryLeft)) x‖ ≤
            C * ∑ l' ∈ Finset.range (k + 2),
              ‖iteratedFDeriv ℝ l' (chartDisplacement_CX3 (I := 𝓡 3) c F) x‖ := by
  intro c K k hK hKt
  have hdt : (interiorChart (𝓡 3) ∞ c).target = (extChartAt (𝓡 3) c).target := by
    rw [interiorChart_target, (isOpen_extChartAt_target c).interior_eq]
  have hKU : K ⊆ (interiorChart (𝓡 3) ∞ c).target := hdt ▸ hKt
  have hP : ContDiffOn ℝ ∞ (pullbackMetricCoefficients H.metric (interiorChart (𝓡 3) ∞ c).symm)
      (interiorChart (𝓡 3) ∞ c).target :=
    contDiffOn_pullback_metric_coefficients H.metric (interiorChart (𝓡 3) ∞ c).open_target
      (interiorChart (𝓡 3) ∞ c).contMDiffOn_invFun
  obtain ⟨r, P', hr, hrU, hP'c, hP'eq⟩ :=
    exists_cutoff_S112 hK (interiorChart (𝓡 3) ∞ c).open_target hKU hP
  have hΘ := thetaS112_contDiff hP'c
  obtain ⟨M, hM0, hM⟩ := exists_jet_bound_S112 (Z := E3 × (E3 →L[ℝ] E3)) hΘ hK k
  choose Cl hCl0 hCl using fun l =>
    hadamard_jets_S112 (E := E3) (Z := E3 × (E3 →L[ℝ] E3)) K M hM0 l
  refine ⟨min (r / 2) (1 / 2), 2 * ∑ l ∈ Finset.range (k + 1), Cl l,
    lt_min (by positivity) (by norm_num),
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun l _ => hCl0 l), ?_⟩
  intro F O hO hF x hxK hxO hxs hjet l hl
  set u := chartDisplacement_CX3 (I := 𝓡 3) c F with hu_def
  have hxt : x ∈ (extChartAt (𝓡 3) c).target := hKt hxK
  have hO' : IsOpen (O ∩ F ⁻¹' (extChartAt (𝓡 3) c).source) :=
    hF.continuousOn.isOpen_inter_preimage hO (isOpen_extChartAt_source c)
  have hV₀ : IsOpen ((extChartAt (𝓡 3) c).target ∩
      (extChartAt (𝓡 3) c).symm ⁻¹' (O ∩ F ⁻¹' (extChartAt (𝓡 3) c).source)) :=
    (continuousOn_extChartAt_symm c).isOpen_inter_preimage (isOpen_extChartAt_target c) hO'
  set V₀ := (extChartAt (𝓡 3) c).target ∩
      (extChartAt (𝓡 3) c).symm ⁻¹' (O ∩ F ⁻¹' (extChartAt (𝓡 3) c).source) with hV₀def
  have hxV₀ : x ∈ V₀ := ⟨hxt, hxO, hxs⟩
  have hu : ContDiffOn ℝ ∞ u V₀ := fun y hy =>
    (chartDisplacement_contDiffAt_CX3 c hO hF hy.1 hy.2.1 hy.2.2).contDiffWithinAt
  have hdu : ContDiffOn ℝ ∞ (fderiv ℝ u) V₀ := hu.fderiv_of_isOpen hV₀ (by simp)
  have hu0 : ‖u x‖ < min (r / 2) (1 / 2) := by
    simpa [norm_iteratedFDeriv_zero] using hjet 0 (Nat.zero_le _)
  have hδr : min (r / 2) (1 / 2) ≤ r / 2 := min_le_left _ _
  have hδ1 : min (r / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hV₁ : IsOpen (V₀ ∩ (fun y => y + u y) ⁻¹' ball (x + u x) (r / 2)) :=
    (continuousOn_id.add hu.continuousOn).isOpen_inter_preimage hV₀ isOpen_ball
  set V := (V₀ ∩ (fun y => y + u y) ⁻¹' ball (x + u x) (r / 2)) ∩ ball x r with hVdef
  have hV : IsOpen V := hV₁.inter isOpen_ball
  have hxV : x ∈ V := ⟨⟨hxV₀, by simpa using half_pos hr⟩, mem_ball_self hr⟩
  have hVV₀ : V ⊆ V₀ := fun y hy => hy.1.1
  have huAt : ContDiffAt ℝ ∞ u x := (hu x hxV₀).contDiffAt (hV₀.mem_nhds hxV₀)
  have hduAt : ContDiffAt ℝ ∞ (fderiv ℝ u) x := (hdu x hxV₀).contDiffAt (hV₀.mem_nhds hxV₀)
  let ζ : E3 → E3 × (E3 →L[ℝ] E3) := fun y => (u y, fderiv ℝ u y)
  have hζ : ContDiffOn ℝ ∞ ζ V := (hu.mono hVV₀).prodMk (hdu.mono hVV₀)
  have hζ1 : ∀ i ≤ l, ‖iteratedFDeriv ℝ i ζ x‖ ≤ 1 := by
    intro i hi
    refine (norm_iteratedFDeriv_pair_le_S112 huAt hduAt i).trans ?_
    have h1 := hjet i (by omega)
    have h2 := hjet (i + 1) (by omega)
    linarith
  have heq : tensor0SModelInChart (I := 𝓡 3) 2 c (fun q : H.Carrier =>
        ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
          ((1 : ℝ) • localPullInner H.metric F q - H.metric.inner q)).uncurryLeft) =ᶠ[𝓝 x]
      fun y => thetaS112 P' (y, ζ y) := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    have hycth : y ∈ cthickening r K :=
      mem_cthickening_of_dist_le y x r K hxK (mem_ball.1 hy.2).le
    have hΨcth : y + u y ∈ cthickening r K := by
      refine mem_cthickening_of_dist_le _ x r K hxK ?_
      have h1 : dist (y + u y) (x + u x) < r / 2 := hy.1.2
      have h2 : dist (x + u x) x = ‖u x‖ := by rw [dist_eq_norm]; congr 1; abel
      calc dist (y + u y) x ≤ dist (y + u y) (x + u x) + dist (x + u x) x := dist_triangle _ _ _
        _ ≤ r := by linarith
    exact model_eq_theta_S112 H c hO hF hy.1.1.1 hy.1.1.2.1 hy.1.1.2.2
      ((hu.differentiableOn (by simp)).differentiableAt (hV₀.mem_nhds hy.1.1)) P'
      (hP'eq y hycth) (hP'eq _ hΨcth)
  rw [(heq.iteratedFDeriv ℝ l).eq_of_nhds]
  have hmain := hCl l (Tensor0SModel 2 ℝ E3) (thetaS112 P') hΘ (thetaS112_zero P')
    (fun i hi y hy z hz => hM i (by omega) y hy z hz) ζ V hV hζ x hxV hxK hζ1
  refine hmain.trans ?_
  set A : ℝ := ∑ j ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ j u x‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsum : ∑ i ∈ Finset.range (l + 1), ‖iteratedFDeriv ℝ i ζ x‖ ≤ 2 * A :=
    (Finset.sum_le_sum fun i _ => norm_iteratedFDeriv_pair_le_S112 huAt hduAt i).trans
      (sum_pair_le_S112 (fun j => ‖iteratedFDeriv ℝ j u x‖) (fun _ => norm_nonneg _) hl)
  have hCle : Cl l ≤ ∑ l' ∈ Finset.range (k + 1), Cl l' :=
    Finset.single_le_sum (f := Cl) (fun _ _ => hCl0 _) (Finset.mem_range.2 (by omega))
  calc Cl l * ∑ i ∈ Finset.range (l + 1), ‖iteratedFDeriv ℝ i ζ x‖ ≤ Cl l * (2 * A) :=
        mul_le_mul_of_nonneg_left hsum (hCl0 l)
    _ ≤ (∑ l' ∈ Finset.range (k + 1), Cl l') * (2 * A) :=
        mul_le_mul_of_nonneg_right hCle (by positivity)
    _ = 2 * (∑ l' ∈ Finset.range (k + 1), Cl l') * A := by ring

end GC.LongTime.Ch12

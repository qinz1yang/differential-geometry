import DifferentialGeometry.Geometry.HarmonicMap.ConformalSource
import DifferentialGeometry.Geometry.Operator.Hessian.Basic
import DifferentialGeometry.Analysis.Elliptic.Euclidean.MaximumPrinciple

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter InnerProductSpace
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Operator
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [I.Boundaryless] in
private theorem hessFun_eq_chart_fderiv
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (p : M)
    (hf : ContDiffAt ℝ 2 (scalarOnE (I := I) p f) (extChartAt I p p))
    (v w : TangentSpace I p) :
    hessFun g f p v w =
      fderiv ℝ (fderiv ℝ (scalarOnE (I := I) p f)) (extChartAt I p p) v w -
        fderiv ℝ (scalarOnE (I := I) p f) (extChartAt I p p)
          (chartChristoffelContraction g p v w (extChartAt I p p)) := by
  classical
  let b := chartModelBasis E
  let φ := scalarOnE (I := I) p f
  let y := extChartAt I p p
  let L := fderiv ℝ (fderiv ℝ φ) y
  have he (v w : E) : L v w =
      ∑ i, ∑ j, b.repr v i * b.repr w j * L (b i) (b j) := by
    conv_lhs => rw [← b.sum_repr v, ← b.sum_repr w]
    simp only [map_sum, map_smul, sum_apply,
      smul_apply, Finset.mul_sum, smul_eq_mul, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsecond (i j : Fin (Module.finrank ℝ E)) :
      chartIteratedPartialDeriv (I := I) p f i j y = L (b i) (b j) := by
    change fderiv ℝ (fun x => fderiv ℝ φ x (b j)) y (b i) = _
    rw [fderiv_clm_apply
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      (differentiableAt_const (b j))]
    simp [L, φ, y]
  have hΓ : fderiv ℝ φ y (chartChristoffelContraction g p v w y) =
      ∑ i, ∑ j, b.repr v i * b.repr w j *
        ∑ k, chartChristoffel g p i j k y * partialDeriv k φ y := by
    simp only [chartChristoffelContraction, map_sum, map_smul, smul_eq_mul,
      Finset.sum_mul, chartCoord, partialDeriv]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [b]
    ring
  have hrepr (v : TangentSpace I p) :
      (centeredChartTangentBasis (I := I) p).repr v = b.repr v := by
    rw [centeredChartTangentBasis_repr, centeredChartTangentEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
  change hessFun g f p v w = L v w - fderiv ℝ φ y _
  rw [hessFun_apply, he v w, hΓ]
  dsimp only [y] at hsecond
  simp only [hrepr, chartHessianTensor_def, hsecond, mul_sub,
    Finset.sum_sub_distrib]
  rfl

omit [FiniteDimensional ℝ E] in
private theorem second_fderiv_comp
    {X : ℂ → E} {φ : E → ℝ} {z : ℂ}
    (hX : ContDiffAt ℝ 2 X z) (hφ : ContDiffAt ℝ 2 φ (X z)) (v w : ℂ) :
    fderiv ℝ (fderiv ℝ (φ ∘ X)) z v w =
      fderiv ℝ φ (X z) (fderiv ℝ (fderiv ℝ X) z v w) +
        fderiv ℝ (fderiv ℝ φ) (X z) (fderiv ℝ X z v) (fderiv ℝ X z w) := by
  have hdX := hX.differentiableAt (by norm_num)
  have hddX := (hX.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hddφ := (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hnear : fderiv ℝ (φ ∘ X) =ᶠ[𝓝 z]
      fun q => (fderiv ℝ φ (X q)).comp (fderiv ℝ X q) := by
    filter_upwards [hX.eventually (by norm_num),
      hdX.continuousAt (hφ.eventually (by norm_num))] with q hq hφq
    change ContDiffAt ℝ 2 φ (X q) at hφq
    exact fderiv_comp q (hφq.differentiableAt (by norm_num))
      (hq.differentiableAt (by norm_num))
  rw [hnear.fderiv_eq, fderiv_clm_comp (c := fun q => fderiv ℝ φ (X q))
    (d := fderiv ℝ X) (hddφ.comp z hdX) hddX,
    fderiv_fun_comp z hddφ hdX]
  rfl

theorem laplacian_comp_of_planarTension_eq_zero
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {U : ℂ → M} {z : ℂ}
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) I 2 U z)
    (hτ : planarTension g U z = 0) :
    Laplacian.laplacian (f ∘ U) z =
      hessFun g f (U z) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))
        (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ)) +
      hessFun g f (U z) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I)
        (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) := by
  let p := U z
  let X := (extChartAt I p) ∘ U
  let φ := scalarOnE (I := I) p f
  have hp : U z ∈ (chartAt H p).source := mem_chart_source H p
  have hX : ContDiffAt ℝ 2 X z :=
    ((contMDiffAt_extChartAt' (I := I) (n := 2) hp).comp z hU).contDiffAt
  have hφ : ContDiffAt ℝ 2 φ (X z) :=
    ((scalarOnE_contDiffOn p hf).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds
        ((extChartAt I p).map_source (mem_extChartAt_source p)))).of_le (by simp)
  have hnear : f ∘ U =ᶠ[𝓝 z] φ ∘ X := by
    filter_upwards [hU.continuousAt.preimage_mem_nhds
      ((chartAt H p).open_source.mem_nhds hp)] with q hq
    have hq' : U q ∈ (extChartAt I p).source := by
      change U q ∈ (chartAt H p).source at hq
      simpa only [extChartAt_source] using hq
    exact (scalarOnE_extChartAt p f hq').symm
  have hDX (v : ℂ) : fderiv ℝ X z v = mfderiv 𝓘(ℝ, ℂ) I U z v := by
    have hc := mfderiv_comp (I := 𝓘(ℝ, ℂ)) (I' := I) (I'' := 𝓘(ℝ, E)) z
      (mdifferentiableAt_extChartAt hp) (hU.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv, mfderiv_extChartAt_self] at hc
    exact congrArg (fun L => L v) hc
  have hzero := chart_planarTension g hU hp
  rw [hτ, map_zero] at hzero
  have hΔ : Laplacian.laplacian X z =
      -(chartChristoffelContraction g p (fderiv ℝ X z 1) (fderiv ℝ X z 1) (X z) +
        chartChristoffelContraction g p (fderiv ℝ X z Complex.I)
          (fderiv ℝ X z Complex.I) (X z)) := by
    exact eq_neg_iff_add_eq_zero.mpr (by simpa only [add_assoc] using hzero.symm)
  rw [(laplacian_congr_nhds hnear).eq_of_nhds]
  have hc : Laplacian.laplacian (φ ∘ X) z =
      fderiv ℝ φ (X z) (Laplacian.laplacian X z) +
        fderiv ℝ (fderiv ℝ φ) (X z) (fderiv ℝ X z 1) (fderiv ℝ X z 1) +
        fderiv ℝ (fderiv ℝ φ) (X z) (fderiv ℝ X z Complex.I)
          (fderiv ℝ X z Complex.I) := by
    simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [second_fderiv_comp hX hφ, second_fderiv_comp hX hφ, map_add]
    ring
  rw [hc, hΔ, map_neg, map_add]
  rw [hessFun_eq_chart_fderiv g f p hφ, hessFun_eq_chart_fderiv g f p hφ]
  simp only [hDX]
  dsimp [φ, X, p]
  ring

private theorem le_of_laplacian_nonneg_above_boundary
    {q : ℂ → ℝ} {s : Set ℂ} {C : ℝ}
    (hs : IsCompact (closure s)) (hq : ContinuousOn q (closure s))
    (hd : ∀ z ∈ interior s, C < q z → ContDiffAt ℝ 2 q z)
    (hΔ : ∀ z ∈ interior s, C < q z → 0 ≤ Laplacian.laplacian q z)
    (hb : ∀ z ∈ frontier s, q z ≤ C) : ∀ z ∈ closure s, q z ≤ C := by
  intro x hx
  by_contra! hbad
  obtain ⟨R, hR, hbound⟩ := hs.isBounded.exists_pos_norm_le
  let δ := (q x - C) / (2 * (R ^ 2 + 1))
  have hδ : 0 < δ := div_pos (sub_pos.mpr hbad) (by positivity)
  have hδeq : δ * (2 * (R ^ 2 + 1)) = q x - C :=
    div_mul_cancel₀ _ (by positivity)
  have hn (y : ℂ) : ContDiffAt ℝ 2 (fun z : ℂ => ‖z‖ ^ 2) y :=
    contDiffAt_id.norm_sq ℝ
  have hcont : ContinuousOn (fun z => q z + δ * ‖z‖ ^ 2) (closure s) :=
    hq.add (continuousOn_const.mul (continuous_norm.pow 2).continuousOn)
  obtain ⟨y, hy, hmax⟩ := hs.exists_isMaxOn ⟨x, hx⟩ hcont
  have hyC : C < q y := by
    have hnorm : ‖y‖ ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hR.le).mpr (hbound y hy)
    have hvalue := hmax hx
    change q x + δ * ‖x‖ ^ 2 ≤ q y + δ * ‖y‖ ^ 2 at hvalue
    have hxnon : 0 ≤ δ * ‖x‖ ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
    have hRnon : 0 ≤ δ * R ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
    have hybound := mul_le_mul_of_nonneg_left hnorm hδ.le
    nlinarith
  have hyi : y ∈ interior s := by
    by_contra hyi
    exact (not_lt_of_ge (hb y ⟨hy, hyi⟩)) hyC
  have hlmax := hmax.isLocalMax
    (mem_of_superset (isOpen_interior.mem_nhds hyi)
      (interior_subset.trans subset_closure))
  have hnon := DifferentialGeometry.Analysis.laplacian_nonpos_of_localMax
    ((hd y hyi hyC).add (contDiffAt_const.mul (hn y))) hlmax
  change Laplacian.laplacian (q + fun z : ℂ => δ * ‖z‖ ^ 2) y ≤ 0 at hnon
  rw [(hd y hyi hyC).laplacian_add (contDiffAt_const.mul (hn y))] at hnon
  have hscale : Laplacian.laplacian (fun z : ℂ => δ * ‖z‖ ^ 2) y =
      δ * Laplacian.laplacian (fun z : ℂ => ‖z‖ ^ 2) y :=
    laplacian_smul δ (hn y)
  rw [hscale, InnerProductSpace.laplacian_norm_sq] at hnon
  have hdim : (0 : ℝ) < Module.finrank ℝ ℂ := by
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := ℂ))
  have hstrict : 0 < δ * (2 * (Module.finrank ℝ ℂ : ℝ)) := by positivity
  linarith [hΔ y hyi hyC]

theorem le_boundary_of_planarTension_eq_zero_of_hessian_nonneg
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {U : ℂ → M} {s : Set ℂ} {C : ℝ}
    (hs : IsCompact (closure s)) (hU : ContinuousOn U (closure s))
    (hd : ∀ z ∈ interior s, ContMDiffAt 𝓘(ℝ, ℂ) I 2 U z)
    (hτ : ∀ z ∈ interior s, planarTension g U z = 0)
    (hH : ∀ z ∈ interior s, C < f (U z) →
      ∀ v : TangentSpace I (U z), 0 ≤ hessFun g f (U z) v v)
    (hb : ∀ z ∈ frontier s, f (U z) ≤ C) :
    ∀ z ∈ closure s, f (U z) ≤ C := by
  apply le_of_laplacian_nonneg_above_boundary hs
    (hf.continuous.comp_continuousOn hU)
  · intro z hz _
    exact ((hf.contMDiffAt.of_le (by simp)).comp z (hd z hz)).contDiffAt
  · intro z hz hC
    rw [laplacian_comp_of_planarTension_eq_zero g hf (hd z hz) (hτ z hz)]
    exact add_nonneg (hH z hz hC _) (hH z hz hC _)
  · exact hb

end DifferentialGeometry.Geometry

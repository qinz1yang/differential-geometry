import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates.TransitionBounds
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Buffered C1 convergence of local metric isometries

The coefficient fields and maps are the supplied ones on their original open
coordinate domains. Uniform coercivity and first coefficient derivative bounds
bound the Hessian through the differentiated metric law. Two mean value estimates
then upgrade uniform C0 convergence to C1 on a fixed inner buffer. No convergence
of derivatives, all-order regularity, or choice of a new map is an input.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem norm_le_of_metric_pairing
    (B C : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E)
    {mu J : ℝ} (hmu : 0 < mu) (hJ : 0 ≤ J)
    (hB : ∀ v, B v v ≤ J * ‖v‖ ^ 2)
    (hC : ∀ v, mu * ‖v‖ ^ 2 ≤ C v v)
    (hmetric : ∀ v, C (A v) (A v) = B v v) :
    ‖A‖ ≤ Real.sqrt (J / mu) := by
  apply A.opNorm_le_bound (Real.sqrt_nonneg _)
  intro v
  have henergy : mu * ‖A v‖ ^ 2 ≤ J * ‖v‖ ^ 2 :=
    (hC (A v)).trans ((hmetric v).trans_le (hB v))
  have hscale : mu * (Real.sqrt (J / mu) * ‖v‖) ^ 2 = J * ‖v‖ ^ 2 := by
    calc
      _ = (mu * (J / mu)) * ‖v‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (div_nonneg hJ hmu.le)]
        ring
      _ = J * ‖v‖ ^ 2 := by rw [mul_div_cancel₀ _ hmu.ne']
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  exact le_of_mul_le_mul_left (henergy.trans_eq hscale.symm) hmu

private theorem trilinear_norm_le
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) {C : ℝ} (hD : ‖D‖ ≤ C)
    (u v w : E) : ‖D u v w‖ ≤ C * ‖u‖ * ‖v‖ * ‖w‖ := by
  calc
    ‖D u v w‖ ≤ ‖D u‖ * ‖v‖ * ‖w‖ := (D u).le_opNorm₂ v w
    _ ≤ (‖D‖ * ‖u‖) * ‖v‖ * ‖w‖ := by
      gcongr
      exact D.le_opNorm u
    _ ≤ C * ‖u‖ * ‖v‖ * ‖w‖ := by gcongr

private theorem hessian_bound_of_metric_isometry
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (B C : E → E →L[ℝ] E →L[ℝ] ℝ) (f : E → E) {x : E}
    {mu J DB DC : ℝ} (hmu : 0 < mu) (hJ : 0 ≤ J)
    (hDB : 0 ≤ DB) (hDC : 0 ≤ DC)
    (hB : ContDiffAt ℝ 1 B x) (hC : ContDiffAt ℝ 1 C (f x))
    (hf : ContDiffAt ℝ 2 f x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v,
      B y u v = C (f y) (fderiv ℝ f y u) (fderiv ℝ f y v))
    (hCsym : ∀ u v, C (f x) u v = C (f x) v u)
    (hBlower : ∀ v, mu * ‖v‖ ^ 2 ≤ B x v v)
    (hBupper : ∀ v, B x v v ≤ J * ‖v‖ ^ 2)
    (hClower : ∀ v, mu * ‖v‖ ^ 2 ≤ C (f x) v v)
    (hdB : ‖fderiv ℝ B x‖ ≤ DB) (hdC : ‖fderiv ℝ C (f x)‖ ≤ DC) :
    let L := Real.sqrt (J / mu)
    ‖fderiv ℝ (fderiv ℝ f) x‖ ≤
      L * (mu⁻¹ * ((3 / 2 : ℝ) * DB)) +
        (mu⁻¹ * ((3 / 2 : ℝ) * DC)) * L ^ 2 := by
  let L := Real.sqrt (J / mu)
  let A := fderiv ℝ f x
  have hxmetric : ∀ u v, B x u v = C (f x) (A u) (A v) :=
    mem_of_mem_nhds hmetric
  have hAnorm : ‖A‖ ≤ L := norm_le_of_metric_pairing (B x) (C (f x)) A
    hmu hJ hBupper hClower (fun v => (hxmetric v v).symm)
  have hAvec (v : E) : ‖A v‖ ≤ L * ‖v‖ :=
    (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hAnorm (norm_nonneg v))
  have hAinj : Function.Injective A := by
    intro u v huv
    have hzero : A (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have hz := hxmetric (u - v) (u - v)
    rw [hzero, map_zero] at hz
    have hb := hBlower (u - v)
    rw [hz] at hb
    have hn : ‖u - v‖ ^ 2 ≤ 0 :=
      le_of_mul_le_mul_left (by simpa only [mul_zero] using hb) hmu
    exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (u - v)]))
  have hAsurj : Function.Surjective A := LinearMap.surjective_of_injective hAinj
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hAinj) (LinearMap.range_eq_top.mpr hAsurj)
  have he : (e : E →L[ℝ] E) = A :=
    ContinuousLinearEquiv.coe_ofBijective A
      (LinearMap.ker_eq_bot.mpr hAinj) (LinearMap.range_eq_top.mpr hAsurj)
  have hBco : IsCoercive (B x) := ⟨mu, hmu, fun v => by
    simpa only [pow_two, mul_assoc] using hBlower v⟩
  have hCco : IsCoercive (C (f x)) := ⟨mu, hmu, fun v => by
    simpa only [pow_two, mul_assoc] using hClower v⟩
  have hfd : HasFDerivAt f (e : E →L[ℝ] E) x := by
    rw [he]
    exact (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hfdd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt
      one_ne_zero).hasFDerivAt
  have hEq (u v : E) :
      fderiv ℝ (fderiv ℝ f) x u v =
        A (MetricKoszul.koszulVec hBco (fderiv ℝ B x) u v) -
          MetricKoszul.koszulVec hCco (fderiv ℝ C (f x)) (A u) (A v) := by
    have hh := MetricIsometry.isom_second_eq B C f (fderiv ℝ f)
      (fderiv ℝ B x) (fderiv ℝ C (f x)) e (fderiv ℝ (fderiv ℝ f) x)
      (hB.differentiableAt one_ne_zero).hasFDerivAt
      (hC.differentiableAt one_ne_zero).hasFDerivAt hfd hfdd hmetric he.symm
      hCsym (hf.isSymmSndFDerivAt (by norm_num)) hBco hCco u v
    have he_apply (w : E) : e w = A w :=
      congrArg (fun T : E →L[ℝ] E => T w) he
    simpa only [he_apply] using hh
  have hKB (u v : E) : ‖MetricKoszul.koszulVec hBco (fderiv ℝ B x) u v‖ ≤
      (mu⁻¹ * ((3 / 2 : ℝ) * DB)) * ‖u‖ * ‖v‖ := by
    simpa only [mul_assoc] using MetricKoszul.koszul_vec_norm_le hBco hmu
      (fun w => by simpa only [pow_two, mul_assoc] using hBlower w)
      (fderiv ℝ B x) hDB (trilinear_norm_le _ hdB) u v
  have hKC (u v : E) : ‖MetricKoszul.koszulVec hCco (fderiv ℝ C (f x)) u v‖ ≤
      (mu⁻¹ * ((3 / 2 : ℝ) * DC)) * ‖u‖ * ‖v‖ := by
    simpa only [mul_assoc] using MetricKoszul.koszul_vec_norm_le hCco hmu
      (fun w => by simpa only [pow_two, mul_assoc] using hClower w)
      (fderiv ℝ C (f x)) hDC (trilinear_norm_le _ hdC) u v
  change ‖fderiv ℝ (fderiv ℝ f) x‖ ≤
    L * (mu⁻¹ * ((3 / 2 : ℝ) * DB)) + (mu⁻¹ * ((3 / 2 : ℝ) * DC)) * L ^ 2
  apply MetricIsometry.op_norm₂_le _ (by dsimp [L]; positivity)
  intro u v
  rw [hEq]
  calc
    _ ≤ ‖A (MetricKoszul.koszulVec hBco (fderiv ℝ B x) u v)‖ +
        ‖MetricKoszul.koszulVec hCco (fderiv ℝ C (f x)) (A u) (A v)‖ :=
      norm_sub_le _ _
    _ ≤ L * ((mu⁻¹ * ((3 / 2 : ℝ) * DB)) * ‖u‖ * ‖v‖) +
        (mu⁻¹ * ((3 / 2 : ℝ) * DC)) * (L * ‖u‖) * (L * ‖v‖) := by
      apply add_le_add
      · exact (hAvec _).trans (mul_le_mul_of_nonneg_left (hKB u v) (Real.sqrt_nonneg _))
      · exact (hKC _ _).trans (by gcongr; exacts [hAvec u, hAvec v])
    _ = (L * (mu⁻¹ * ((3 / 2 : ℝ) * DB)) +
        (mu⁻¹ * ((3 / 2 : ℝ) * DC)) * L ^ 2) * ‖u‖ * ‖v‖ := by ring

private theorem fderiv_sub_id_bound_of_hessian
    (f : E → E) {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    {x : E} {rho delta M t : ℝ} (ht : 0 < t) (htrho : t ≤ rho)
    (hdelta : 0 ≤ delta) (hM : 0 ≤ M) (hfit : closedBall x rho ⊆ U)
    (hzero : ∀ y ∈ closedBall x rho, ‖f y - y‖ ≤ delta)
    (hsecond : ∀ y ∈ closedBall x rho, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M) :
    ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ 2 * delta / t + M * t := by
  have hsub : closedBall x t ⊆ closedBall x rho := closedBall_subset_closedBall htrho
  have hx : x ∈ closedBall x t := mem_closedBall_self ht.le
  have hdiff (y : E) (hy : y ∈ closedBall x t) : DifferentiableAt ℝ f y :=
    (hf.contDiffAt (hU.mem_nhds (hfit (hsub hy)))).differentiableAt (by norm_num)
  have hdiff' (y : E) (hy : y ∈ closedBall x t) :
      DifferentiableAt ℝ (fderiv ℝ f) y :=
    (((hf.contDiffAt (hU.mem_nhds (hfit (hsub hy)))).fderiv_right
      (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt one_ne_zero)
  have hvar (y : E) (hy : y ∈ closedBall x t) :
      ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ M * t := by
    have hh := (convex_closedBall x t).norm_image_sub_le_of_norm_fderiv_le
      hdiff' (fun z hz => hsecond z (hsub hz)) hx hy
    exact hh.trans (mul_le_mul_of_nonneg_left (by
      simpa only [mem_closedBall, dist_eq_norm] using hy) hM)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let y := x + t • v
  have hyNorm : ‖y - x‖ = t := by
    simp only [y, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hv,
      mul_one]
  have hy : y ∈ closedBall x t := by
    rw [mem_closedBall, dist_eq_norm, hyNorm]
  have hrem := (convex_closedBall x t).norm_image_sub_le_of_norm_fderiv_le'
    hdiff hvar hx hy
  have hrem' : ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ M * t * t := by
    simpa only [hyNorm] using hrem
  have hdisp : ‖(f y - y) - (f x - x)‖ ≤ 2 * delta :=
    (norm_sub_le _ _).trans (by linarith [hzero y (hsub hy), hzero x (hsub hx)])
  have hsec : ‖(fderiv ℝ f x - ContinuousLinearMap.id ℝ E) (y - x)‖ ≤
      2 * delta + M * t * t := by
    have heq : (fderiv ℝ f x - ContinuousLinearMap.id ℝ E) (y - x) =
        ((f y - y) - (f x - x)) - (f y - f x - fderiv ℝ f x (y - x)) := by
      simp only [sub_apply, ContinuousLinearMap.id_apply]
      abel
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add hdisp hrem')
  have hmul : t * ‖(fderiv ℝ f x - ContinuousLinearMap.id ℝ E) v‖ ≤
      2 * delta + M * t * t := by
    simpa only [y, add_sub_cancel_left, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht] using hsec
  have hdiv : ‖(fderiv ℝ f x - ContinuousLinearMap.id ℝ E) v‖ ≤
      (2 * delta + M * t * t) / t :=
    (le_div_iff₀ ht).2 (by simpa only [mul_comm] using hmul)
  calc
    ‖(fderiv ℝ f x - ContinuousLinearMap.id ℝ E) v‖ ≤
        (2 * delta + M * t * t) / t := hdiv
    _ = 2 * delta / t + M * t := by
      rw [add_div, mul_div_cancel_right₀ _ ht.ne']

section FiniteDimensional

variable [FiniteDimensional ℝ E] [CompleteSpace E]

/-- The same C2 local metric isometry satisfies a quantitative C1 identity
estimate on any genuine closed-ball buffer. The Hessian constant is derived
from the actual coefficient fields, not assumed as an input. -/
theorem norm_fderiv_sub_id_le_of_metric_isometry
    (B C : E → E →L[ℝ] E →L[ℝ] ℝ) (f : E → E)
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hB : ContDiffOn ℝ 1 B U) (hC : ContDiffOn ℝ 1 C V)
    (hf : ContDiffOn ℝ 2 f U) (hmap : MapsTo f U V)
    {mu J DB DC : ℝ} (hmu : 0 < mu) (hJ : 0 ≤ J)
    (hDB : 0 ≤ DB) (hDC : 0 ≤ DC)
    (hmetric : ∀ y ∈ U, ∀ u v,
      B y u v = C (f y) (fderiv ℝ f y u) (fderiv ℝ f y v))
    (hCsym : ∀ y ∈ V, ∀ u v, C y u v = C y v u)
    (hBlower : ∀ y ∈ U, ∀ v, mu * ‖v‖ ^ 2 ≤ B y v v)
    (hBupper : ∀ y ∈ U, ∀ v, B y v v ≤ J * ‖v‖ ^ 2)
    (hClower : ∀ y ∈ V, ∀ v, mu * ‖v‖ ^ 2 ≤ C y v v)
    (hdB : ∀ y ∈ U, ‖fderiv ℝ B y‖ ≤ DB)
    (hdC : ∀ y ∈ V, ‖fderiv ℝ C y‖ ≤ DC)
    {x : E} {rho delta t : ℝ} (ht : 0 < t) (htrho : t ≤ rho)
    (hdelta : 0 ≤ delta) (hfit : closedBall x rho ⊆ U)
    (hzero : ∀ y ∈ closedBall x rho, ‖f y - y‖ ≤ delta) :
    let L := Real.sqrt (J / mu)
    let M := L * (mu⁻¹ * ((3 / 2 : ℝ) * DB)) +
      (mu⁻¹ * ((3 / 2 : ℝ) * DC)) * L ^ 2
    ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ 2 * delta / t + M * t := by
  apply fderiv_sub_id_bound_of_hessian f hU hf ht htrho hdelta
    (by positivity) hfit hzero
  intro y hy
  exact hessian_bound_of_metric_isometry B C f hmu hJ hDB hDC
    (hB.contDiffAt (hU.mem_nhds (hfit hy)))
    (hC.contDiffAt (hV.mem_nhds (hmap (hfit hy))))
    (hf.contDiffAt (hU.mem_nhds (hfit hy)))
    (Filter.Eventually.mono (hU.mem_nhds (hfit hy)) (fun z hz => hmetric z hz))
    (hCsym (f y) (hmap (hfit hy))) (hBlower y (hfit hy)) (hBupper y (hfit hy))
    (hClower (f y) (hmap (hfit hy))) (hdB y (hfit hy)) (hdC (f y) (hmap (hfit hy)))

/-- Uniform C0 convergence of the original metric isometries, with eventual
uniform first coefficient bounds and a fixed source buffer, implies order-one
convergence of that same entire sequence. No subsequence is selected. -/
theorem mapCPConvergenceOn_one_of_metric_isometries
    (B C : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ) (f : ℕ → E → E)
    {U V K : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {rho mu J DB DC : ℝ} (hrho : 0 < rho) (hmu : 0 < mu) (hJ : 0 ≤ J)
    (hDB : 0 ≤ DB) (hDC : 0 ≤ DC)
    (hfit : ∀ x ∈ K, closedBall x rho ⊆ U)
    (hdata : ∀ᶠ n in atTop,
      ContDiffOn ℝ 1 (B n) U ∧ ContDiffOn ℝ 1 (C n) V ∧
      ContDiffOn ℝ 2 (f n) U ∧ MapsTo (f n) U V ∧
      (∀ x ∈ U, ∀ u v,
        B n x u v = C n (f n x) (fderiv ℝ (f n) x u) (fderiv ℝ (f n) x v)) ∧
      (∀ y ∈ V, ∀ u v, C n y u v = C n y v u) ∧
      (∀ x ∈ U, ∀ v, mu * ‖v‖ ^ 2 ≤ B n x v v) ∧
      (∀ x ∈ U, ∀ v, B n x v v ≤ J * ‖v‖ ^ 2) ∧
      (∀ y ∈ V, ∀ v, mu * ‖v‖ ^ 2 ≤ C n y v v) ∧
      (∀ x ∈ U, ‖fderiv ℝ (B n) x‖ ≤ DB) ∧
      (∀ y ∈ V, ‖fderiv ℝ (C n) y‖ ≤ DC))
    (hzero : TendstoUniformlyOn f (fun x => x) atTop U) :
    MapCPConvergenceOn K 1 f (fun x => x) := by
  let L := Real.sqrt (J / mu)
  let M := L * (mu⁻¹ * ((3 / 2 : ℝ) * DB)) +
    (mu⁻¹ * ((3 / 2 : ℝ) * DC)) * L ^ 2
  have hM : 0 ≤ M := by dsimp [M, L]; positivity
  intro epsilon hepsilon
  let t := min rho (epsilon / (2 * (M + 1)))
  have ht : 0 < t := lt_min hrho (by positivity)
  have htrho : t ≤ rho := min_le_left _ _
  have htbudget : t * (2 * (M + 1)) ≤ epsilon :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hMt : M * t ≤ epsilon / 2 := by nlinarith
  let delta := min (epsilon / 2) (epsilon * t / 4)
  have hdelta : 0 < delta := lt_min (by positivity) (by positivity)
  have hdeltaeps : delta ≤ epsilon / 2 := min_le_left _ _
  have hdeltat : delta ≤ epsilon * t / 4 := min_le_right _ _
  have hquot : 2 * delta / t ≤ epsilon / 2 :=
    (div_le_iff₀ ht).mpr (by nlinarith)
  have hz := (Metric.tendstoUniformlyOn_iff.mp hzero) delta hdelta
  have hevent : ∀ᶠ n in atTop, ∀ r : ℕ, r ≤ 1 → ∀ x ∈ K,
      mapDerivNorm r (f n) (fun y => y) x ≤ epsilon := by
    filter_upwards [hdata, hz] with n hn hnzero
    rcases hn with ⟨hB, hC, hf, hmap, hmetric, hCsym, hBlower, hBupper, hClower,
      hdB, hdC⟩
    have hnzero' (y : E) (hy : y ∈ U) : ‖f n y - y‖ ≤ delta := by
      have hh := hnzero y hy
      rw [dist_eq_norm, norm_sub_rev] at hh
      exact hh.le
    intro r hr x hx
    have hxU : x ∈ U := hfit x hx (mem_closedBall_self hrho.le)
    interval_cases r
    · rw [mapDerivNorm, norm_iteratedFDeriv_zero]
      exact (hnzero' x hxU).trans (hdeltaeps.trans (by linarith))
    · rw [mapDerivNorm, norm_iteratedFDeriv_one]
      have hdsub : HasFDerivAt (fun y : E => f n y - y)
          (fderiv ℝ (f n) x - ContinuousLinearMap.id ℝ E) x := by
        change HasFDerivAt (f n - id)
          (fderiv ℝ (f n) x - ContinuousLinearMap.id ℝ E) x
        exact (((hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt
          (by norm_num)).hasFDerivAt).sub (hasFDerivAt_id x)
      rw [hdsub.fderiv]
      have hh := norm_fderiv_sub_id_le_of_metric_isometry (B n) (C n) (f n)
        hU hV hB hC hf hmap hmu hJ hDB hDC hmetric hCsym hBlower hBupper hClower
        hdB hdC ht htrho hdelta.le (hfit x hx)
        (fun y hy => hnzero' y (hfit x hx hy))
      exact hh.trans (by change 2 * delta / t + M * t ≤ epsilon; linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  exact ⟨N, fun n hn r hr x hx => hN n hn r hr x hx⟩

end FiniteDimensional
end DifferentialGeometry.CheegerGromovCompactness

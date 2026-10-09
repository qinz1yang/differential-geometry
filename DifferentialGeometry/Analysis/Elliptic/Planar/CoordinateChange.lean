import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- The full scalar nondivergence operator in the real basis `1, I` of the plane. -/
def planarScalarOperator (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (beta : ℂ → Fin 2 → ℝ) (c w : ℂ → ℝ) (x : ℂ) : ℝ :=
  (∑ i : Fin 2, ∑ j : Fin 2, A x i j * fderiv ℝ (fderiv ℝ w) x
    ((![1, Complex.I] : Fin 2 → ℂ) i) ((![1, Complex.I] : Fin 2 → ℂ) j)) +
  (∑ i : Fin 2, beta x i * fderiv ℝ w x ((![1, Complex.I] : Fin 2 → ℂ) i)) +
  c x * w x

/-- The coordinate Hessian correction and the original drift, before division
by the scalar principal factor. Both are evaluated in the original coordinates. -/
def planarCoordinateDrift (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (beta : ℂ → Fin 2 → ℝ) (e : ℂ → ℂ) (x : ℂ) : ℂ :=
  (∑ i : Fin 2, ∑ j : Fin 2, A x i j • fderiv ℝ (fderiv ℝ e) x
    ((![1, Complex.I] : Fin 2 → ℂ) i) ((![1, Complex.I] : Fin 2 → ℂ) j)) +
  ∑ i : Fin 2, beta x i • fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) i)

private theorem second_derivative_comp_apply
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} {e : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (e x)) (he : ContDiffAt ℝ 2 e x) (u v : E) :
    fderiv ℝ (fderiv ℝ (fun z => f (e z))) x u v =
      fderiv ℝ (fderiv ℝ f) (e x) (fderiv ℝ e x u) (fderiv ℝ e x v) +
      fderiv ℝ f (e x) (fderiv ℝ (fderiv ℝ e) x u v) := by
  have hfd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hed := he.differentiableAt (by norm_num)
  have hedd := (he.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hnear : fderiv ℝ (fun z => f (e z)) =ᶠ[𝓝 x]
      fun z => (fderiv ℝ f (e z)).comp (fderiv ℝ e z) := by
    filter_upwards [he.eventually (by norm_num),
      he.continuousAt (hf.eventually (by norm_num))] with z hez hfz
    change ContDiffAt ℝ 2 f (e z) at hfz
    exact fderiv_fun_comp z (hfz.differentiableAt (by norm_num))
      (hez.differentiableAt (by norm_num))
  have hsecond := ((hfd.hasFDerivAt.comp x hed.hasFDerivAt).clm_comp
    hedd.hasFDerivAt).fderiv
  simp only [Function.comp_def] at hsecond
  rw [hnear.fderiv_eq, hsecond]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

/-- The complete chain rule retains the coordinate Hessian correction, original
drift, and potential. No differential of the solution is inverted. -/
theorem planarScalarOperator_comp
    (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ)
    {v : ℂ → ℝ} {e : ℂ → ℂ} {x : ℂ}
    (hv : ContDiffAt ℝ 2 v (e x)) (he : ContDiffAt ℝ 2 e x) :
    planarScalarOperator A beta c (fun z => v (e z)) x =
      (∑ i : Fin 2, ∑ j : Fin 2, A x i j * fderiv ℝ (fderiv ℝ v) (e x)
        (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) i))
        (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) j))) +
      fderiv ℝ v (e x) (planarCoordinateDrift A beta e x) + c x * v (e x) := by
  have hfirst := fderiv_fun_comp x (hv.differentiableAt (by norm_num))
    (he.differentiableAt (by norm_num))
  simp only [planarScalarOperator, second_derivative_comp_apply hv he, hfirst,
    ContinuousLinearMap.comp_apply, planarCoordinateDrift, map_add, map_sum, map_smul,
    smul_eq_mul, mul_add, Finset.sum_add_distrib]
  ring

/-- Exact pushforward through an actual smooth inverse chart, before any
principal normalization. The transformed solution is literally `w ∘ e.symm`. -/
theorem planarScalarOperator_pushforward
    (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ)
    {w : ℂ → ℝ} (e : OpenPartialHomeomorph ℂ ℂ)
    (hw : ContDiffOn ℝ 2 w e.source) (he : ContDiffOn ℝ 2 e e.source)
    (hei : ContDiffOn ℝ 2 e.symm e.target) {y : ℂ} (hy : y ∈ e.target) :
    let x := e.symm y
    let v : ℂ → ℝ := fun z => w (e.symm z)
    planarScalarOperator A beta c w x =
      (∑ i : Fin 2, ∑ j : Fin 2, A x i j * fderiv ℝ (fderiv ℝ v) y
        (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) i))
        (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) j))) +
      fderiv ℝ v y (planarCoordinateDrift A beta e x) + c x * v y := by
  intro x v
  have hx : x ∈ e.source := e.map_target hy
  have hex : e x = y := e.right_inv hy
  have hv : ContDiffOn ℝ 2 v e.target := hw.comp hei (fun z hz => e.map_target hz)
  have hnear : (fun z => v (e z)) =ᶠ[𝓝 x] w := by
    filter_upwards [e.open_source.mem_nhds hx] with z hz
    exact congrArg w (e.left_inv hz)
  have hvalue : v (e x) = w x := hnear.eq_of_nhds
  have hoperator : planarScalarOperator A beta c (fun z => v (e z)) x =
      planarScalarOperator A beta c w x := by
    simp only [planarScalarOperator, hnear.fderiv_eq, hnear.fderiv.fderiv_eq, hvalue]
  rw [← hoperator, planarScalarOperator_comp A beta c
    (hv.contDiffAt (e.open_target.mem_nhds (e.map_source hx)))
    (he.contDiffAt (e.open_source.mem_nhds hx)), hex]

/-- Coordinate change preserves the actual scalar map and exactly its zero set. -/
theorem planarCoordinateChange_map_zero_set (w : ℂ → ℝ) (e : OpenPartialHomeomorph ℂ ℂ) :
    (∀ x ∈ e.source, w (e.symm (e x)) = w x) ∧
      e.target ∩ (fun y => w (e.symm y)) ⁻¹' ({0} : Set ℝ) =
        e '' (e.source ∩ w ⁻¹' ({0} : Set ℝ)) := by
  refine ⟨fun x hx => congrArg w (e.left_inv hx), ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hw⟩
    exact ⟨e.symm y, ⟨e.map_target hy, hw⟩, e.right_inv hy⟩
  · rintro ⟨x, ⟨hx, hw⟩, rfl⟩
    exact ⟨e.map_source hx, by simpa only [mem_preimage, e.left_inv hx] using hw⟩

/-- Once the supplied coordinate derivative has a scalar principal contraction,
the full equation becomes a Laplacian equation with explicit drift and potential.
The only divisor is the strictly positive principal factor. -/
theorem planarScalarOperator_eq_zero_in_isothermal_coordinates
    (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ → Fin 2 → ℝ) (c w : ℂ → ℝ)
    (e : OpenPartialHomeomorph ℂ ℂ) (lam : ℂ → ℝ)
    (hw : ContDiffOn ℝ 2 w e.source) (he : ContDiffOn ℝ 2 e e.source)
    (hei : ContDiffOn ℝ 2 e.symm e.target)
    (hlam : ∀ x ∈ e.source, 0 < lam x)
    (hprincipal : ∀ x ∈ e.source, ∀ H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
      (∑ i : Fin 2, ∑ j : Fin 2, A x i j *
        H (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) i))
          (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) j))) =
        lam x * (H 1 1 + H Complex.I Complex.I))
    (hpde : ∀ x ∈ e.source, planarScalarOperator A beta c w x = 0) :
    let v : ℂ → ℝ := fun y => w (e.symm y)
    let drift : ℂ → ℂ := fun y => (lam (e.symm y))⁻¹ •
      planarCoordinateDrift A beta e (e.symm y)
    let potential : ℂ → ℝ := fun y => c (e.symm y) / lam (e.symm y)
    ContDiffOn ℝ 2 v e.target ∧
      (∀ y ∈ e.target,
        Laplacian.laplacian v y + fderiv ℝ v y (drift y) + potential y * v y = 0) ∧
      (∀ x ∈ e.source, v (e x) = w x) ∧
      e.target ∩ v ⁻¹' ({0} : Set ℝ) = e '' (e.source ∩ w ⁻¹' ({0} : Set ℝ)) := by
  intro v drift potential
  have hv : ContDiffOn ℝ 2 v e.target := hw.comp hei (fun z hz => e.map_target hz)
  refine ⟨hv, ?_, planarCoordinateChange_map_zero_set w e⟩
  intro y hy
  have hx := e.map_target hy
  have hpush := planarScalarOperator_pushforward A beta c e hw he hei hy
  change planarScalarOperator A beta c w (e.symm y) = _ at hpush
  rw [hpde _ hx, hprincipal _ hx] at hpush
  have hlap : Laplacian.laplacian v y =
      fderiv ℝ (fderiv ℝ v) y 1 1 +
        fderiv ℝ (fderiv ℝ v) y Complex.I Complex.I := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hlap]
  change _ + fderiv ℝ v y ((lam (e.symm y))⁻¹ •
    planarCoordinateDrift A beta e (e.symm y)) +
      (c (e.symm y) / lam (e.symm y)) * v y = 0
  rw [map_smul, smul_eq_mul]
  have hn : lam (e.symm y) ≠ 0 := (hlam _ hx).ne'
  apply (mul_left_cancel₀ hn)
  rw [mul_zero]
  calc
    _ = lam (e.symm y) *
        (fderiv ℝ (fderiv ℝ v) y 1 1 +
          fderiv ℝ (fderiv ℝ v) y Complex.I Complex.I) +
        fderiv ℝ v y (planarCoordinateDrift A beta e (e.symm y)) +
        c (e.symm y) * v y := by field_simp [hn]
    _ = 0 := hpush.symm

/-- The full coordinate drift is smooth for smooth original coefficients and chart. -/
theorem contDiffOn_planarCoordinateDrift
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {A : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {beta : ℂ → Fin 2 → ℝ} {e : ℂ → ℂ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) Ω)
    (hbeta : ∀ i, ContDiffOn ℝ ∞ (fun x => beta x i) Ω)
    (he : ContDiffOn ℝ ∞ e Ω) :
    ContDiffOn ℝ ∞ (planarCoordinateDrift A beta e) Ω := by
  have hd := he.fderiv_of_isOpen (m := ∞) hΩ (by simp)
  have hdd := hd.fderiv_of_isOpen (m := ∞) hΩ (by simp)
  apply ContDiffOn.add
  · apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact (hA i j).smul ((hdd.clm_apply
      (contDiffOn_const (c := (![1, Complex.I] : Fin 2 → ℂ) i))).clm_apply
        (contDiffOn_const (c := (![1, Complex.I] : Fin 2 → ℂ) j)))
  · apply ContDiffOn.sum
    intro i _
    exact (hbeta i).smul (hd.clm_apply
      (contDiffOn_const (c := (![1, Complex.I] : Fin 2 → ℂ) i)))

end DifferentialGeometry.Analysis

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MetricWindow_S49
import DifferentialGeometry.Geometry.Curvature.RiemannRicciNorm

set_option autoImplicit false

/-!
# CH12-S70 / G2b: order-zero `ckErr_S45` from a quadratic-form bound

Converse of `pullback_inner_le_of_ckErr_S49`: if `|c f^*g'(w,w) - h(w,w)| ≤ e h(w,w)` for all `w` at `p`,
then `ckErr_S45 H g' c f 0 p ≤ 3 e` (polarisation over an `h`-orthonormal basis, `3 = √(card Fin 3 ^ 2)`).
This turns the bi-Lipschitz-type output of `metric_variation_S45` into the `ckErr` clause of `hLTF04_lift_k0`.
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.Geometry.Curvature
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

theorem abs_pullbackErr_basis_le_S70 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (p : H.Carrier) {e : ℝ}
    (hq : ∀ w : TangentSpace (𝓡 3) p,
      |c * g'.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w) -
          H.metric.inner p w w| ≤ e * H.metric.inner p w w)
    {ι : Type} [DecidableEq ι] (b : Module.Basis ι ℝ (TangentSpace (𝓡 3) p))
    (hON : ∀ i j : ι, H.metric.inner p (b i) (b j) = if i = j then (1 : ℝ) else 0) (i j : ι) :
    |c * g'.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p (b i)) (mfderiv (𝓡 3) (𝓡 3) f p (b j)) -
        H.metric.inner p (b i) (b j)| ≤ e := by
  set L := mfderiv (𝓡 3) (𝓡 3) f p with hL
  let B : TangentSpace (𝓡 3) p → TangentSpace (𝓡 3) p → ℝ := fun v w =>
    c * g'.inner (f p) (L v) (L w) - H.metric.inner p v w
  have hBs : ∀ v w, B v w = B w v := fun v w => by
    simp only [B]; rw [g'.symm (f p) (L v) (L w), H.metric.symm p v w]
  have hBpp : ∀ u v, B (u + v) (u + v) = B u u + 2 * B u v + B v v := fun u v => by
    simp only [B, map_add, add_apply]; rw [g'.symm (f p) (L v) (L u), H.metric.symm p v u]; ring
  have hBmm : ∀ u v, B (u - v) (u - v) = B u u - 2 * B u v + B v v := fun u v => by
    simp only [B, map_sub, sub_apply]; rw [g'.symm (f p) (L v) (L u), H.metric.symm p v u]; ring
  change |B (b i) (b j)| ≤ e
  by_cases hij : i = j
  · subst hij
    have h := hq (b i)
    have gii : H.metric.inner p (b i) (b i) = 1 := by simp [hON]
    change |B (b i) (b i)| ≤ e * H.metric.inner p (b i) (b i) at h
    rw [gii, mul_one] at h
    exact h
  · have gij : H.metric.inner p (b i) (b j) = 0 := by simp [hON, hij]
    have gji : H.metric.inner p (b j) (b i) = 0 := by rw [H.metric.symm p, gij]
    have gii : H.metric.inner p (b i) (b i) = 1 := by simp [hON]
    have gjj : H.metric.inner p (b j) (b j) = 1 := by simp [hON]
    have gp : H.metric.inner p (b i + b j) (b i + b j) = 2 := by
      simp [gij, gji, gii, gjj]; norm_num
    have gm : H.metric.inner p (b i - b j) (b i - b j) = 2 := by
      simp [gij, gji, gii, gjj]; norm_num
    have h1 := hq (b i + b j)
    have h2 := hq (b i - b j)
    change |B (b i + b j) (b i + b j)| ≤ e * H.metric.inner p (b i + b j) (b i + b j) at h1
    change |B (b i - b j) (b i - b j)| ≤ e * H.metric.inner p (b i - b j) (b i - b j) at h2
    rw [gp, hBpp] at h1
    rw [gm, hBmm] at h2
    have h3 := hq (b i)
    have h4 := hq (b j)
    change |B (b i) (b i)| ≤ e * H.metric.inner p (b i) (b i) at h3
    change |B (b j) (b j)| ≤ e * H.metric.inner p (b j) (b j) at h4
    rw [gii] at h3
    rw [gjj] at h4
    rw [abs_le] at h1 h2 h3 h4 ⊢
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

theorem ckErr_zero_le_of_quad_S70 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (p : H.Carrier) {e : ℝ}
    (he : 0 ≤ e)
    (hq : ∀ w : TangentSpace (𝓡 3) p,
      |c * g'.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w) -
          H.metric.inner p w w| ≤ e * H.metric.inner p w w) :
    ckErr_S45 H g' c f 0 p ≤ 3 * e := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := 𝓡 3) H.metric p
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) p) = 3 := finrank_euclideanSpace_fin
  have hinv : MetricInverseInBasis (I := 𝓡 3) H.metric p basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace (𝓡 3) p)))) := by
    intro i j
    constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  have h := sqrt_normSq0S_le_card_of_component_bound (I := 𝓡 3) H.metric p 2 basis hinv
    (scaledMetricError_S49 H g' c f p) e he (fun slots => by
      rw [component0S_apply]
      have e1 : (fun a : Fin 2 => basis (slots a)) = vec2 (basis (slots 0)) (basis (slots 1)) := by
        funext a; fin_cases a <;> rfl
      rw [e1, scaledMetricError_apply_vec2_S49]
      exact abs_pullbackErr_basis_le_S70 H g' c f p hq basis hON _ _)
  have hcard : (Fintype.card (Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 3) p))) : ℝ) = 9 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hdim]; norm_num
  rw [hcard] at h
  have h9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h9] at h
  exact h

end GC.LongTime.Ch12

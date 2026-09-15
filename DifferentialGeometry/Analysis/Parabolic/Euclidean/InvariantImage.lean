import DifferentialGeometry.Analysis.Parabolic.Euclidean.Composition
import DifferentialGeometry.Analysis.Parabolic.Euclidean.Uniqueness
import DifferentialGeometry.Analysis.Parabolic.Euclidean.RetractionResidual

open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem periodic_comp_eq_of_parabolic_residual_bound
    {u : ℝ → ℝ → E} {P : E → E} {a : ℝ → ℝ → ℝ} {δ L s v : ℝ}
    (hsv : s < v) (hδ : 0 < δ)
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc s v))
    (hPcont : ContinuousOn P ((Function.uncurry u) '' (Icc 0 1 ×ˢ Icc s v)))
    (hinit : ∀ x, P (u x s) = u x s)
    (hx : ∀ x t, t ∈ Ioo s v → ContDiffAt ℝ 2 (fun y => u y t) x)
    (ht : ∀ x t, t ∈ Ioo s v → DifferentiableAt ℝ (fun τ => u x τ) t)
    (hP : ∀ x t, t ∈ Ioo s v → ContDiffAt ℝ 2 P (u x t))
    (ha : ∀ x t, t ∈ Ioo s v → δ ≤ a x t)
    (hres : ∀ x t, t ∈ Ioo s v →
      ‖(deriv (fun τ => u x τ) t - a x t • deriv (deriv (fun y => u y t)) x) -
        fderiv ℝ P (u x t)
          (deriv (fun τ => u x τ) t - a x t • deriv (deriv (fun y => u y t)) x) +
        a x t • fderiv ℝ (fderiv ℝ P) (u x t)
          (deriv (fun y => u y t) x) (deriv (fun y => u y t) x)‖ ≤
        L * (‖u x t - P (u x t)‖ +
          ‖deriv (fun y => u y t) x - fderiv ℝ P (u x t) (deriv (fun y => u y t) x)‖)) :
    ∀ x t, t ∈ Icc s v → P (u x t) = u x t := by
  have hz := periodic_eq_zero_of_parabolic_residual_bound
    (u := fun x t => u x t - P (u x t)) (a := a) (L := L) hsv hδ
    (fun x t => by rw [hper]) (hcont.sub (hPcont.comp hcont (mapsTo_image _ _)))
    (fun x => sub_eq_zero.mpr (hinit x).symm)
    (fun x t ht' => (hx x t ht').sub ((hP x t ht').comp x (hx x t ht')))
    (fun x t ht' => (ht x t ht').sub
      ((hP x t ht').differentiableAt (by norm_num) |>.comp t (ht x t ht')))
    ha ?_
  · intro x t ht'
    exact (sub_eq_zero.mp (hz x t ht')).symm
  · intro x t ht'
    rw [normal_defect_parabolic_residual (hP x t ht') (hx x t ht') (ht x t ht')]
    have hdx := (hx x t ht').differentiableAt (by norm_num)
    have hcomp := ((hP x t ht').differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x
      hdx.hasDerivAt
    have hdiff : DifferentiableAt ℝ (fun y => P (u y t)) x := hcomp.differentiableAt
    rw [deriv_fun_sub hdx hdiff]
    change HasDerivAt (fun y => P (u y t)) _ x at hcomp
    rw [hcomp.deriv]
    exact hres x t ht'


theorem periodic_comp_eq_of_retractionParabolicResidual_eq_zero
    {u : ℝ → ℝ → E} {P : E → E}
    {A : ℝ × E × E → E} {a : ℝ × E × E → ℝ}
    {U K : Set (ℝ × E × E)} {V : Set E} {δ s v : ℝ}
    (hsv : s < v) (hδ : 0 < δ)
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hKU : K ⊆ U)
    (hP : ContDiffOn ℝ 3 P V) (hA : ContDiffOn ℝ 1 A U) (ha : ContDiffOn ℝ 1 a U)
    (hUV : ∀ q ∈ U, q.2.1 ∈ V)
    (hPU : ∀ q ∈ K, (q.1, P q.2.1, fderiv ℝ P q.2.1 q.2.2) ∈ U)
    (hzero : ∀ q ∈ K,
      retractionParabolicResidual P A a (q.1, P q.2.1, fderiv ℝ P q.2.1 q.2.2) = 0)
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc s v))
    (himage : ∀ x t, t ∈ Icc s v → u x t ∈ V)
    (hinit : ∀ x, P (u x s) = u x s)
    (hx : ∀ x t, t ∈ Ioo s v → ContDiffAt ℝ 2 (fun y => u y t) x)
    (ht : ∀ x t, t ∈ Ioo s v → DifferentiableAt ℝ (fun τ => u x τ) t)
    (hjet : ∀ x t, t ∈ Ioo s v → (t, u x t, deriv (fun y => u y t) x) ∈ K)
    (hell : ∀ q ∈ K, δ ≤ a q)
    (heq : ∀ x t, t ∈ Ioo s v →
      deriv (fun τ => u x τ) t -
          a (t, u x t, deriv (fun y => u y t) x) • deriv (deriv (fun y => u y t)) x =
        A (t, u x t, deriv (fun y => u y t) x)) :
    ∀ x t, t ∈ Icc s v → P (u x t) = u x t := by
  obtain ⟨L, hL⟩ := exists_retractionParabolicResidual_bound
    hU hV hK hKU hP hA ha hUV hPU hzero
  apply periodic_comp_eq_of_parabolic_residual_bound (L := L) hsv hδ hper hcont
  · apply hP.continuousOn.mono
    rintro _ ⟨⟨x, t⟩, hxt, rfl⟩
    exact himage x t hxt.2
  · exact hinit
  · exact hx
  · exact ht
  · intro x t ht'
    exact (hP.contDiffAt (hV.mem_nhds (himage x t ⟨ht'.1.le, ht'.2.le⟩))).of_le
      (by norm_num)
  · intro x t ht'
    exact hell _ (hjet x t ht')
  · intro x t ht'
    rw [heq x t ht']
    exact hL _ (hjet x t ht')

end DifferentialGeometry.Analysis.Parabolic

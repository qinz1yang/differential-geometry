import DifferentialGeometry.Topology.Manifold.Sard
import DifferentialGeometry.Topology.SphereSeparation.ManifoldInverseFunction
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Regular values of smooth circle maps

For a smooth map `f : Circle → Circle`, regular values are dense, and the fibre over a regular
value is finite. The circle has no global real angle coordinate, so the density statement goes
through the imaginary part after a rotation of the target: a value whose imaginary part is a
regular value of `im ∘ f` is a regular value of `f`, by the chain rule. Finiteness: a nonzero
derivative between one-dimensional spaces is bijective, so `f` is injective near each point of
the fibre, and a closed discrete subset of the compact circle is finite.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace GC.Seifert

attribute [local instance] finrank_real_complex_fact'

theorem circle_contMDiff_im_mul (c : Circle) :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun w : Circle => ((c * w : Circle) : ℂ).im) := by
  have hmul : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun w : Circle => c * w) :=
    contMDiff_const.mul contMDiff_id
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun w : Circle => (w : ℂ)) :=
    contMDiff_coe_sphere
  exact Complex.imCLM.contDiff.contMDiff.comp (hcoe.comp hmul)

theorem circle_mfderiv_bijective {f : Circle → Circle} {z : Circle}
    (h : mfderiv (𝓡 1) (𝓡 1) f z ≠ 0) :
    Function.Bijective (mfderiv (𝓡 1) (𝓡 1) f z) := by
  set L := mfderiv (𝓡 1) (𝓡 1) f z
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1 := by simp
  let L' : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1) := L.toLinearMap
  obtain ⟨v, hv⟩ : ∃ v, L' v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h (ContinuousLinearMap.ext hcon)
  have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0, map_zero])
  have hinj : Function.Injective L' := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv0).mp hrank u
    have hu' : c • L' v = 0 := by
      rw [← map_smul]
      exact hu
    rcases smul_eq_zero.mp hu' with hc | hc
    · rw [hc, zero_smul]
    · exact absurd hc hv
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩

theorem circle_eventually_ne_of_mfderiv_ne_zero {f : Circle → Circle}
    (hf : ContMDiff (𝓡 1) (𝓡 1) ∞ f) {z : Circle} (h : mfderiv (𝓡 1) (𝓡 1) f z ≠ 0) :
    ∃ U ∈ 𝓝 z, InjOn f U := by
  open DifferentialGeometry.Topology.SphereSeparation in
  exact exists_nhds_injOn_of_contMDiffAt_of_bijective_mfderiv
    (𝓡 1) (𝓡 1) (by simp) hf.contMDiffAt (circle_mfderiv_bijective h)

theorem circle_finite_fiber_of_regular {f : Circle → Circle}
    (hf : ContMDiff (𝓡 1) (𝓡 1) ∞ f) {s : Circle}
    (hs : ∀ z, f z = s → mfderiv (𝓡 1) (𝓡 1) f z ≠ 0) :
    {z | f z = s}.Finite := by
  have hK : IsCompact {z | f z = s} :=
    (isClosed_eq hf.continuous continuous_const).isCompact
  choose! U hU hinj using fun z (hz : f z = s) =>
    circle_eventually_ne_of_mfderiv_ne_zero hf (hs z hz)
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover U (fun z hz => hU z hz)
  apply t.finite_toSet.subset
  intro y hy
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hcover hy)
  have hxK : f x = s := htK x hx
  have hxy : y = x := hinj x hxK hyx (mem_of_mem_nhds (hU x hxK)) (hy.trans hxK.symm)
  rw [hxy]
  exact hx

theorem circle_mfderiv_ne_zero_of_im {f : Circle → Circle}
    (hf : ContMDiff (𝓡 1) (𝓡 1) ∞ f) (c : Circle) {z : Circle}
    (h : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun w => ((c * f w : Circle) : ℂ).im) z ≠ 0) :
    mfderiv (𝓡 1) (𝓡 1) f z ≠ 0 := by
  intro h0
  apply h
  have hH := (circle_contMDiff_im_mul c).mdifferentiableAt (x := f z) (by simp)
  have hF := hf.mdifferentiableAt (x := z) (by simp)
  have hcomp := mfderiv_comp z hH hF
  change mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ((fun w : Circle => ((c * w : Circle) : ℂ).im) ∘ f) z = 0
  rw [hcomp, h0, ContinuousLinearMap.comp_zero]

theorem circle_exists_regular_mem {f : Circle → Circle} (hf : ContMDiff (𝓡 1) (𝓡 1) ∞ f)
    {U : Set Circle} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ s ∈ U, ∀ z, f z = s → mfderiv (𝓡 1) (𝓡 1) f z ≠ 0 := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨θp, rfl⟩ := Circle.exp_surjective p
  have hcont : Continuous (fun t : ℝ => Circle.exp (θp + t)) :=
    Circle.exp.continuous.comp (continuous_const.add continuous_id)
  have hpre : IsOpen ((fun t : ℝ => Circle.exp (θp + t)) ⁻¹' U) := hU.preimage hcont
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => Circle.exp (θp + t)) ⁻¹' U := by
    simpa only [mem_preimage, add_zero] using hp
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.mp hpre 0 h0
  set δ := min δ₀ 1 with hδdef
  have hδ : 0 < δ := lt_min hδ₀ one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδπ : δ < Real.pi / 2 := lt_of_le_of_lt hδ1 (by linarith [Real.pi_gt_three])
  let g : Circle → ℝ := fun w => ((Circle.exp (-θp) * f w : Circle) : ℂ).im
  have hg : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ g := (circle_contMDiff_im_mul _).comp hf
  have hgc : HasCompactSupport g := isClosed_tsupport g |>.isCompact
  have hsin : Real.sin (-δ) < Real.sin δ := by
    rw [Real.sin_neg]
    have := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_gt_three])
    linarith
  obtain ⟨r, hr, hreg⟩ := hg.exists_regular_value_of_hasCompactSupport hgc hsin
  have hr1 : r ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · have := Real.neg_one_le_sin (-δ)
      linarith [hr.1]
    · have := Real.sin_le_one δ
      linarith [hr.2]
  set θ := Real.arcsin r with hθdef
  have hθ : θ ∈ Ioo (-δ) δ := by
    constructor
    · rw [hθdef, Real.lt_arcsin_iff_sin_lt ⟨by linarith, by linarith⟩ hr1]
      exact hr.1
    · rw [hθdef, Real.arcsin_lt_iff_lt_sin hr1 ⟨by linarith, by linarith⟩]
      exact hr.2
  refine ⟨Circle.exp (θp + θ), ?_, ?_⟩
  · apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hθ.1, hθ.2, min_le_left δ₀ 1]
  · intro z hz
    apply circle_mfderiv_ne_zero_of_im hf (Circle.exp (-θp))
    apply hreg
    change ((Circle.exp (-θp) * f z : Circle) : ℂ).im = r
    rw [hz, ← Circle.exp_add, show -θp + (θp + θ) = θ by ring, Circle.coe_exp]
    rw [Complex.exp_ofReal_mul_I_im, hθdef, Real.sin_arcsin hr1.1 hr1.2]

end GC.Seifert

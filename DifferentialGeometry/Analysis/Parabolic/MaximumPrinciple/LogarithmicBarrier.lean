import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak
import DifferentialGeometry.Analysis.Parabolic.Operator.Logarithmic
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.FirstContact
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity

noncomputable section

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem cutoff_logarithmic_reaction_bound_at_time_and_space_min
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    (r q φ : ℝ → M → ℝ) (c : ℝ → ℝ)
    {t : ℝ} (ht : 0 < t) (x : M) (hx : I.IsInteriorPoint x)
    (hrtime : DifferentiableWithinAt ℝ (fun s => r s x) (Icc 0 t) t)
    (hqtime : DifferentiableWithinAt ℝ (fun s => q s x) (Icc 0 t) t)
    (hφtime : DifferentiableWithinAt ℝ (fun s => φ s x) (Icc 0 t) t)
    (hctime : DifferentiableWithinAt ℝ c (Icc 0 t) t)
    (hrspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (r t) y)
    (hqspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (q t) y)
    (hφspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y)
    (hrgrad : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (r t) y) x)
    (hqgrad : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (q t) y) x)
    (hφgrad : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (φ t) y) x)
    (hφpos : 0 < φ t x) (hqpos : 0 < q t x)
    (hboundary : r t x = q t x * (Real.log (φ t x * q t x) + c t))
    (htimemin : IsLocalMinOn
      (fun s => φ s x * r s x - (φ s x * q s x) * (Real.log (φ s x * q s x) + c s))
      (Icc 0 t) t)
    (hspacemin : IsLocalMin
      (fun y => φ t y * r t y - (φ t y * q t y) * (Real.log (φ t y * q t y) + c t)) x)
    {κ δ ε : ℝ}
    (hreaction : κ * q t x ^ 2 ≤ parabolicOperatorWithDrift (I := I) G t X r t x -
      (Real.log (φ t x * q t x) + c t + 1) * parabolicOperatorWithDrift (I := I) G t X q t x)
    (hφpar : parabolicOperatorWithDrift (I := I) G t X φ t x ≤ δ)
    (hφsq : (G.metric t).inner x
      (gradientAt (I := I) G t (φ t) x) (gradientAt (I := I) G t (φ t) x) ≤ ε * φ t x) :
    κ * φ t x * q t x ≤ δ + 2 * ε + φ t x * derivWithin c (Icc 0 t) t := by
  let u : ℝ → M → ℝ := fun s y => φ s y * r s y
  let v : ℝ → M → ℝ := fun s y => φ s y * q s y
  let ψ : ℝ → M → ℝ := fun s y => u s y - v s y * (Real.log (v s y) + c s)
  have hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 t) t := hφtime.mul hrtime
  have hv_time : DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 t) t := hφtime.mul hqtime
  have hu_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y := by
    filter_upwards [hφspace, hrspace] with y hφy hry
    exact hφy.mul hry
  have hv_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) y := by
    filter_upwards [hφspace, hqspace] with y hφy hqy
    exact hφy.mul hqy
  have hu_grad : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (u t) y) x :=
    mdifferentiableAt_gradientFun_mul (G.metric t) hφspace hrspace hφgrad hrgrad
  have hv_grad : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (v t) y) x :=
    mdifferentiableAt_gradientFun_mul (G.metric t) hφspace hqspace hφgrad hqgrad
  have hvpos : 0 < v t x := mul_pos hφpos hqpos
  have hvnear : ∀ᶠ y in 𝓝 x, v t y ≠ 0 :=
    hv_space.self_of_nhds.continuousAt.eventually_ne hvpos.ne'
  let l : M → ℝ := fun y => v t y * (Real.log (v t y) + c t)
  let b : ℝ := Real.log (v t x) + c t + 1
  have hldiff : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) l y := by
    filter_upwards [hv_space, hvnear] with y hyv hyne
    exact hyv.mul (((Real.differentiableAt_log hyne).mdifferentiableAt.comp y hyv).add
      mdifferentiableAt_const)
  have hderiv (z : ℝ) (hz : z ≠ 0) : HasDerivAt (fun w : ℝ => w * (Real.log w + c t))
      (Real.log z + c t + 1) z := by
    simpa only [id_eq, one_mul, mul_inv_cancel₀ hz] using!
      (hasDerivAt_id z).mul ((Real.hasDerivAt_log hz).add_const (c t))
  have hlgrad : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) l y) x := by
    have hcoeff : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => Real.log (v t y) + c t + 1) x :=
      ((Real.differentiableAt_log hvpos.ne').mdifferentiableAt.comp x
        hv_space.self_of_nhds).add mdifferentiableAt_const |>.add mdifferentiableAt_const
    refine (hcoeff.smul_section hv_grad).congr_of_eventuallyEq ?_
    filter_upwards [hv_space, hvnear] with y hyv hyne
    apply congrArg (fun w => (⟨y, w⟩ : TotalSpace E (TangentSpace I : M → Type _)))
    rw [gradientFun_comp (G.metric t) (hderiv _ hyne).differentiableAt hyv,
      (hderiv _ hyne).deriv]
    rfl
  have hψspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (ψ t) y := by
    filter_upwards [hu_space, hldiff] with y huy hly
    exact huy.sub hly
  have hψgrad : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (ψ t) y) x := by
    refine (mdifferentiableAt_sub_section hu_grad hlgrad).congr_of_eventuallyEq ?_
    filter_upwards [hu_space, hldiff] with y huy hly
    exact congrArg (fun w => (⟨y, w⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      (gradientFun_sub (G.metric t) huy hly)
  have hP : parabolicOperatorWithDrift (I := I) G t X ψ t x ≤ 0 :=
    derivWithin_sub_heatOperatorWithDrift_nonpos_at_time_and_space_min G X ht
      htimemin hspacemin hx hψspace hψgrad
  have hPeq := parabolic_sub_mul_log_add_time_at G t X u v c t x hvpos.ne'
    hu_time hv_time hctime hu_space hv_space hu_grad hv_grad
  change parabolicOperatorWithDrift (I := I) G t X ψ t x = _ at hPeq
  rw [parabolic_mul_nhds (G := G) t X φ r t x hφtime hrtime hφspace hrspace hφgrad hrgrad,
    parabolic_mul_nhds (G := G) t X φ q t x hφtime hqtime hφspace hqspace hφgrad hqgrad] at hPeq
  have hzero := gradientFun_eq_zero_at_spatial_min_of_isInteriorPoint
    (G.metric t) hspacemin hx hψspace.self_of_nhds
  rw [gradientFun_sub (G.metric t) hu_space.self_of_nhds hldiff.self_of_nhds,
    gradientFun_comp (G.metric t) (hderiv _ hvpos.ne').differentiableAt hv_space.self_of_nhds,
    (hderiv _ hvpos.ne').deriv,
    gradientFun_mul (G.metric t) hφspace.self_of_nhds hrspace.self_of_nhds,
    gradientFun_mul (G.metric t) hφspace.self_of_nhds hqspace.self_of_nhds] at hzero
  have hcross := congrArg (fun w => (G.metric t).inner x
    (gradientAt (I := I) G t (φ t) x) w) hzero
  simp only [map_sub, map_add, map_smul, map_zero, smul_eq_mul] at hcross
  let D := (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
    (gradientAt (I := I) G t (φ t) x)
  let N := (G.metric t).inner x (gradientAt (I := I) G t (v t) x)
    (gradientAt (I := I) G t (v t) x)
  have hN : 0 ≤ N := by
    rcases eq_or_ne (gradientAt (I := I) G t (v t) x) 0 with hzero | hne
    · dsimp only [N]
      rw [hzero]
      simp
    · exact ((G.metric t).pos x _ hne).le
  have hNscale : 0 ≤ φ t x * ((v t x)⁻¹ * N) :=
    mul_nonneg hφpos.le (mul_nonneg (inv_nonneg.mpr hvpos.le) hN)
  have hscaled := mul_le_mul_of_nonneg_left hreaction (sq_nonneg (φ t x))
  have hPscaled := mul_nonpos_of_nonneg_of_nonpos hφpos.le hP
  have hδ := mul_le_mul_of_nonneg_left hφpar (mul_pos hφpos hqpos).le
  have hε := mul_le_mul_of_nonneg_left hφsq (mul_pos (by norm_num : (0 : ℝ) < 2) hqpos).le
  have hbd : r t x = q t x * (b - 1) := by dsimp only [b, v]; linarith [hboundary]
  have hcross' : φ t x * (G.metric t).inner x
      (gradientAt (I := I) G t (φ t) x) (gradientAt (I := I) G t (r t) x) -
      b * φ t x * (G.metric t).inner x
        (gradientAt (I := I) G t (φ t) x) (gradientAt (I := I) G t (q t) x) = q t x * D := by
    change φ t x * _ + r t x * D - b * (φ t x * _ + q t x * D) = 0 at hcross
    simp only [gradientAt] at *
    rw [hbd] at hcross
    nlinarith only [hcross]
  have hcore : φ t x * q t x *
      (κ * φ t x * q t x - δ - 2 * ε - φ t x * derivWithin c (Icc 0 t) t) ≤ 0 := by
    change parabolicOperatorWithDrift (I := I) G t X ψ t x =
      φ t x * _ + r t x * _ - 2 * _ - b * (φ t x * _ + q t x * _ - 2 * _) -
      derivWithin c (Icc 0 t) t * (φ t x * q t x) + (v t x)⁻¹ * N at hPeq
    rw [hbd] at hPeq
    nlinarith [hscaled, hPscaled, hNscale, hδ, hε, hcross']
  have hcore' := nonpos_of_mul_nonpos_right hcore (mul_pos hφpos hqpos)
  linarith


end DifferentialGeometry.Analysis.Parabolic

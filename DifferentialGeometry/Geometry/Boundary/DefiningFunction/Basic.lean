import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity

set_option autoImplicit false

noncomputable section

open Bundle
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Boundary

theorem frontier_levelSet_annulus_subset
    {X : Type*} [TopologicalSpace X]
    {rho : X → Real} (hrho : Continuous rho) {r R : Real} :
    frontier {x | r ≤ rho x ∧ rho x ≤ R} ⊆
      {x | rho x = r ∨ rho x = R} := by
  intro x hx
  let K : Set X := {y | r ≤ rho y ∧ rho y ≤ R}
  have hKclosed : IsClosed K :=
    (isClosed_le continuous_const hrho).inter
      (isClosed_le hrho continuous_const)
  have hxK : x ∈ K := by
    have hxcl : x ∈ closure K := frontier_subset_closure hx
    rwa [hKclosed.closure_eq] at hxcl
  by_contra hboundary
  change ¬ (rho x = r ∨ rho x = R) at hboundary
  rw [not_or] at hboundary
  have hrx : r < rho x :=
    lt_of_le_of_ne hxK.1 (Ne.symm hboundary.1)
  have hxR : rho x < R :=
    lt_of_le_of_ne hxK.2 hboundary.2
  let U : Set X := {y | r < rho y} ∩ {y | rho y < R}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const hrho).inter
      (isOpen_lt hrho continuous_const)
  have hUK : U ⊆ K := by
    intro y hy
    exact ⟨hy.1.le, hy.2.le⟩
  have hxU : x ∈ U := ⟨hrx, hxR⟩
  have hxint : x ∈ interior K := interior_maximal hUK hUopen hxU
  exact (mem_frontier_iff_notMem_interior hxK).mp hx hxint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

def levelSetOutwardNormal
    (g : SmoothRiemannianMetric I M) (rho : M → Real) (x : M) :
    TangentSpace I x :=
  if 0 < g.inner x (gradientFun (I := I) g rho x)
      (gradientFun (I := I) g rho x) then
    (Real.sqrt (g.inner x (gradientFun (I := I) g rho x)
      (gradientFun (I := I) g rho x)))⁻¹ •
        gradientFun (I := I) g rho x
  else
    0

theorem levelSetOutwardNormal_eq
    (g : SmoothRiemannianMetric I M) (rho : M → Real) (x : M)
    (hgrad : 0 < g.inner x (gradientFun (I := I) g rho x)
      (gradientFun (I := I) g rho x)) :
    levelSetOutwardNormal (I := I) g rho x =
      (Real.sqrt (g.inner x (gradientFun (I := I) g rho x)
        (gradientFun (I := I) g rho x)))⁻¹ •
          gradientFun (I := I) g rho x := by
  unfold levelSetOutwardNormal
  rw [if_pos hgrad]

theorem levelSetOutwardNormal_unit
    (g : SmoothRiemannianMetric I M) (rho : M → Real) (x : M)
    (hgrad : 0 < g.inner x (gradientFun (I := I) g rho x)
      (gradientFun (I := I) g rho x)) :
    g.inner x (levelSetOutwardNormal (I := I) g rho x)
      (levelSetOutwardNormal (I := I) g rho x) = 1 := by
  let q := g.inner x (gradientFun (I := I) g rho x)
    (gradientFun (I := I) g rho x)
  have hq : 0 < q := hgrad
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsqrt_ne : Real.sqrt q ≠ 0 := ne_of_gt hsqrt
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
  rw [levelSetOutwardNormal_eq (I := I) g rho x hgrad]
  change g.inner x ((Real.sqrt q)⁻¹ • gradientFun (I := I) g rho x)
      ((Real.sqrt q)⁻¹ • gradientFun (I := I) g rho x) = 1
  rw [map_smul, ContinuousLinearMap.map_smul]
  change (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) = 1
  rw [show (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) =
    q / (Real.sqrt q * Real.sqrt q) by field_simp]
  rw [hsq]
  exact div_self (ne_of_gt hq)

theorem inner_levelSetOutwardNormal_neg
    (g : SmoothRiemannianMetric I M) (rho f : M → Real) (x : M)
    (hgrad : 0 < g.inner x (gradientFun (I := I) g rho x)
      (gradientFun (I := I) g rho x))
    (hneg : g.inner x (gradientFun (I := I) g f x)
      (gradientFun (I := I) g rho x) < 0) :
    g.inner x (gradientFun (I := I) g f x)
      (levelSetOutwardNormal (I := I) g rho x) < 0 := by
  rw [levelSetOutwardNormal_eq (I := I) g rho x hgrad,
    ContinuousLinearMap.map_smul]
  change (Real.sqrt (g.inner x (gradientFun (I := I) g rho x)
    (gradientFun (I := I) g rho x)))⁻¹ *
      g.inner x (gradientFun (I := I) g f x)
        (gradientFun (I := I) g rho x) < 0
  exact mul_neg_of_pos_of_neg (inv_pos.mpr (Real.sqrt_pos.mpr hgrad)) hneg

theorem levelSetOutwardNormal_inner
    (g : SmoothRiemannianMetric I M) (f : M → Real) (x : M)
    (v : TangentSpace I x) :
    g.inner x (levelSetOutwardNormal (I := I) g f x) v =
      (Real.sqrt (normGradSqFun (I := I) g f x))⁻¹ * mvfderiv (I := I) f x v := by
  by_cases hpos : 0 < normGradSqFun (I := I) g f x
  · rw [levelSetOutwardNormal_eq (I := I) g f x hpos, map_smul, smul_apply, smul_eq_mul]
    change (Real.sqrt (normGradSqFun (I := I) g f x))⁻¹ *
      g.inner x (gradientFun (I := I) g f x) v = _
    rw [inner_gradientFun]
  · have hzero : normGradSqFun (I := I) g f x = 0 :=
      le_antisymm (le_of_not_gt hpos) (normGradSqFun_nonneg g f x)
    have hnormal : levelSetOutwardNormal (I := I) g f x = 0 := by
      unfold levelSetOutwardNormal
      exact if_neg hpos
    simp only [hnormal, hzero, Real.sqrt_zero, inv_zero, zero_mul, map_zero,
      _root_.zero_apply]

theorem inner_gradientFun_levelSetOutwardNormal
    (g : SmoothRiemannianMetric I M) (f : M → Real) (x : M) :
    g.inner x (gradientFun (I := I) g f x) (levelSetOutwardNormal (I := I) g f x) =
      Real.sqrt (normGradSqFun (I := I) g f x) := by
  rw [g.symm, levelSetOutwardNormal_inner]
  have hgrad : mvfderiv (I := I) f x (gradientFun (I := I) g f x) =
      normGradSqFun (I := I) g f x := by
    rw [← inner_gradientFun]
    rfl
  rw [hgrad]
  by_cases hz : normGradSqFun (I := I) g f x = 0
  · simp only [hz, mul_zero, Real.sqrt_zero]
  · have hpos := lt_of_le_of_ne (normGradSqFun_nonneg g f x) (Ne.symm hz)
    rw [inv_mul_eq_div]
    exact (div_eq_iff (Real.sqrt_pos.mpr hpos).ne').mpr
      (Real.mul_self_sqrt (normGradSqFun_nonneg g f x)).symm

theorem mvfderiv_levelSetOutwardNormal
    (g : SmoothRiemannianMetric I M) (f : M → Real) (x : M) :
    mvfderiv (I := I) f x (levelSetOutwardNormal (I := I) g f x) =
      Real.sqrt (normGradSqFun (I := I) g f x) := by
  rw [← inner_gradientFun, inner_gradientFun_levelSetOutwardNormal]

theorem levelSetOutwardNormal_inner_eq_zero_of_mem_ker
    (g : SmoothRiemannianMetric I M) (f : M → Real) (x : M)
    (v : TangentSpace I x) (hv : v ∈ (mvfderiv (I := I) f x).ker) :
    g.inner x (levelSetOutwardNormal (I := I) g f x) v = 0 := by
  change mvfderiv (I := I) f x v = 0 at hv
  rw [levelSetOutwardNormal_inner, hv, mul_zero]

theorem levelSetOutwardNormal_contMDiffAt
    (g : SmoothRiemannianMetric I M) {f : M → Real} {x : M}
    (hf : ContMDiffAt I 𝓘(Real, Real) ∞ f x)
    (hreg : mfderiv I 𝓘(Real, Real) f x ≠ 0) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
      (fun y : M => TotalSpace.mk' E y (levelSetOutwardNormal (I := I) g f y)) x := by
  have hgrad := gradientFun_contMDiffAt g hf
  have htotal := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun y : M => TangentSpace I y)
    (E₂ := fun y : M => TangentSpace I y)
    (E₃ := fun _ : M => Real) (g.contMDiff x) hgrad hgrad
  have hnorm : ContMDiffAt I 𝓘(Real, Real) ∞ (normGradSqFun (I := I) g f) x := by
    rw [Bundle.contMDiffAt_totalSpace] at htotal
    exact htotal.2
  have hpos : 0 < normGradSqFun (I := I) g f x :=
    lt_of_le_of_ne (normGradSqFun_nonneg g f x)
      (Ne.symm (mt normGradSqFun_eq_zero_iff.mp hreg))
  have hsqrt : ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y => Real.sqrt (normGradSqFun (I := I) g f y)) x :=
    (Real.contDiffAt_sqrt hpos.ne').contMDiffAt.comp x hnorm
  have hcoeff := hsqrt.inv₀ (Real.sqrt_pos.mpr hpos).ne'
  have hscaled := hcoeff.smul_section hgrad
  apply hscaled.congr_of_eventuallyEq
  filter_upwards [hnorm.continuousAt.eventually (isOpen_Ioi.mem_nhds hpos)] with y hy
  congr 1
  exact levelSetOutwardNormal_eq (I := I) g f y hy

theorem levelSetOutwardNormal_contMDiffOn
    (g : SmoothRiemannianMetric I M) {f : M → Real} {s : Set M}
    (hf : ContMDiffOn I 𝓘(Real, Real) ∞ f s) (hs : IsOpen s)
    (hreg : ∀ x ∈ s, mfderiv I 𝓘(Real, Real) f x ≠ 0) :
    ContMDiffOn I (I.prod 𝓘(Real, E)) ∞
      (fun y : M => TotalSpace.mk' E y (levelSetOutwardNormal (I := I) g f y)) s := by
  intro x hx
  exact (levelSetOutwardNormal_contMDiffAt g
    (hf.contMDiffAt (hs.mem_nhds hx)) (hreg x hx)).contMDiffWithinAt

end DifferentialGeometry.Geometry.Boundary

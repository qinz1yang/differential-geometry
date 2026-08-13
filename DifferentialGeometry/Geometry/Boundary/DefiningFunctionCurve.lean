import DifferentialGeometry.Geometry.Boundary.DefiningFunction
import DifferentialGeometry.Geometry.Comparison.Variation.SmoothCurveGerm
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Geometry.Manifold.Instances.Icc

set_option autoImplicit false

noncomputable section

open Bundle Filter Set SignType
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Boundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

omit [FiniteDimensional Real E] [IsManifold I ∞ M] in
private theorem hasDerivAt_comp_mfderiv
    (f : M → Real) (gamma : Real → M) (t : Real)
    (hf : MDifferentiableAt I (modelWithCornersSelf Real Real) f (gamma t))
    (hgamma : MDifferentiableAt (modelWithCornersSelf Real Real) I gamma t) :
    HasDerivAt (fun s => f (gamma s))
      (NormedSpace.fromTangentSpace (f (gamma t))
        (mfderiv I (modelWithCornersSelf Real Real) f (gamma t)
          (mfderiv (modelWithCornersSelf Real Real) I gamma t 1))) t := by
  rw [hasDerivAt_iff_hasFDerivAt]
  have hcomp := hf.hasMFDerivAt.comp t hgamma.hasMFDerivAt
  have hcomp' := hcomp.hasFDerivAt
  convert hcomp' using 1
  change ContinuousLinearMap.toSpanSingleton Real
      (((mfderiv I (modelWithCornersSelf Real Real) f (gamma t)).comp
        (mfderiv (modelWithCornersSelf Real Real) I gamma t)) 1) = _
  exact ContinuousLinearMap.toSpanSingleton_apply_map_one
    (R₁ := Real) (M₂ := Real) _

private theorem hasDerivAt_comp_neg_gradient
    (g : SmoothRiemannianMetric I M)
    (f rho : M → Real) (p : M) (gamma : Real → M)
    (hgamma0 : gamma 0 = p)
    (hf : MDifferentiableAt I (modelWithCornersSelf Real Real) f p)
    (hgamma : MDifferentiableAt (modelWithCornersSelf Real Real) I gamma 0)
    (hvelocity : mfderiv (modelWithCornersSelf Real Real) I gamma 0 1 =
      -gradientFun (I := I) g rho p) :
    HasDerivAt (fun s => f (gamma s))
      (-g.inner p (gradientFun (I := I) g f p)
        (gradientFun (I := I) g rho p)) 0 := by
  have hcurve := hasDerivAt_comp_mfderiv (I := I) f gamma 0
    (by simpa [hgamma0] using hf) hgamma
  rw [hgamma0] at hcurve
  convert hcurve using 1
  change -g.inner p (gradientFun (I := I) g f p)
      (gradientFun (I := I) g rho p) =
    mfderiv I (modelWithCornersSelf Real Real) f p
      (mfderiv (modelWithCornersSelf Real Real) I gamma 0 1)
  rw [hvelocity, map_neg]
  rw [inner_gradientFun]
  rfl

theorem exists_levelSet_inward_curve_of_gradient_ne_zero
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (rho : M → Real) {p : M}
    (hrho : MDifferentiableAt I (modelWithCornersSelf Real Real) rho p)
    {r R : Real} (hrR : r < R) (hp : rho p = R)
    (hgrad : gradientFun (I := I) g rho p ≠ 0) :
    ∃ a : Real, 0 < a ∧ ∃ gamma : Real → M,
      gamma 0 = p ∧
      Set.MapsTo gamma (Set.Icc 0 a) {x | r ≤ rho x ∧ rho x ≤ R} ∧
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma 0 ∧
      mfderiv (modelWithCornersSelf Real Real) I gamma 0 1 =
        -gradientFun (I := I) g rho p := by
  let v : TangentSpace I p := -gradientFun (I := I) g rho p
  obtain ⟨gamma, hgamma_smooth, hgamma0, hgamma_deriv⟩ :=
    DifferentialGeometry.Geometry.Riemannian.Variation.exists_contMDiffAt_hasMFDerivAt_of_tangent
      (I := I) p v
  have hgamma_mdiff :
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma 0 :=
    hgamma_deriv.mdifferentiableAt
  have hvelocity :
      mfderiv (modelWithCornersSelf Real Real) I gamma 0 1 =
        -gradientFun (I := I) g rho p := by
    rw [hgamma_deriv.mfderiv]
    change (1 : Real) • v = -gradientFun (I := I) g rho p
    simp [v]
  let q : Real := g.inner p (gradientFun (I := I) g rho p)
    (gradientFun (I := I) g rho p)
  have hq : 0 < q := g.pos p _ hgrad
  have hrho_gamma : HasDerivAt (fun s => rho (gamma s)) (-q) 0 := by
    simpa [q] using hasDerivAt_comp_neg_gradient (I := I)
      g rho rho p gamma hgamma0 hrho hgamma_mdiff hvelocity
  let f : Real → Real := fun s => rho (gamma s) - R
  have hf : HasDerivAt f (-q) 0 := by
    simpa [f] using hrho_gamma.sub_const R
  have hf0 : f 0 = 0 := by
    simp [f, hgamma0, hp]
  have hsign : ∀ᶠ s in nhds 0, sign (f s) = sign (0 - s) := by
    exact eventually_nhdsWithin_sign_eq_of_deriv_neg
      (by rw [hf.deriv]; exact neg_neg_of_pos hq) hf0
  have hupper : ∀ᶠ s in nhds 0, 0 ≤ s → rho (gamma s) ≤ R := by
    filter_upwards [hsign] with s hs hsnonneg
    by_cases hs0 : s = 0
    · subst s
      simp [hgamma0, hp]
    · have hspos : 0 < s := lt_of_le_of_ne hsnonneg (Ne.symm hs0)
      have hfsign : sign (f s) = -1 := by
        rw [hs]
        exact sign_neg (sub_neg.mpr hspos)
      have hfneg : f s < 0 := sign_eq_neg_one_iff.mp hfsign
      simpa [f] using hfneg.le
  have hrho_cont : ContinuousAt (fun s => rho (gamma s)) 0 := by
    exact hrho.continuousAt.comp_of_eq hgamma_mdiff.continuousAt hgamma0
  have hlower : ∀ᶠ s in nhds 0, r < rho (gamma s) := by
    have htendsto : Tendsto (fun s => rho (gamma s)) (nhds 0) (nhds R) := by
      simpa [hgamma0, hp] using hrho_cont.tendsto
    exact htendsto.eventually (Ioi_mem_nhds hrR)
  have hgood : ∀ᶠ s in nhds 0, 0 ≤ s →
      r ≤ rho (gamma s) ∧ rho (gamma s) ≤ R := by
    filter_upwards [hlower, hupper] with s hs_lower hs_upper hsnonneg
    exact ⟨hs_lower.le, hs_upper hsnonneg⟩
  obtain ⟨b, hb, hbsub⟩ := exists_Ico_subset_of_mem_nhds
    hgood ⟨1, zero_lt_one⟩
  let a : Real := b / 2
  have ha : 0 < a := half_pos hb
  refine ⟨a, ha, gamma, hgamma0, ?_, hgamma_mdiff, hvelocity⟩
  intro s hs
  have hsa : s < b := hs.2.trans_lt (half_lt_self hb)
  exact hbsub ⟨hs.1, hsa⟩ hs.1

end DifferentialGeometry.Geometry.Boundary

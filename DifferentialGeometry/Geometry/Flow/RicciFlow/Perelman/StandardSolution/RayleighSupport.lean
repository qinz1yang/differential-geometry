import DifferentialGeometry.Geometry.Operator.RayleighLaplacian
import DifferentialGeometry.Analysis.Parabolic.Scaling.ParabolicNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RicciUpperReaction
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.SlotPermutation

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private theorem upper_second_eq_iterCov
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) :
    ricciUpperBoundNab2ModelSec S t =
      iterCov (S.base.metric t) 2 (ricciUpperBoundSec S t) 2 := by
  have hfirst :
      TotalNabla0SRealizes (I := I) 2
        (leviCivitaConnectionOfMetric (S.base.metric t))
        (ricciUpperBoundSec S t)
        (ricciUpperBoundNablaModel S t) := by
    have hh := TotalNabla0SRealizes.smul (I := I) (M := M)
      (-1 : ℝ) ((pinchSpatialModel (I := I) S (1 / 2)).first t)
    simpa [ricciUpperBoundSec, ricciUpperBoundNablaModel,
      pinchNablaModel, SolutionFamily.connection] using hh
  have hsecond :
      TotalNabla0SRealizes (I := I) 3
        (leviCivitaConnectionOfMetric (S.base.metric t))
        (ricciUpperBoundNablaModel S t)
        (ricciUpperBoundNab2ModelSec S t) := by
    have hh := TotalNabla0SRealizes.smul (I := I) (M := M)
      (-1 : ℝ) ((pinchSpatialModel (I := I) S (1 / 2)).second t)
    simpa [ricciUpperBoundNablaModel, ricciUpperBoundNab2ModelSec,
      pinchNab2ModelSec, pinchNab2Model, pinchNablaModel,
      SolutionFamily.connection] using hh
  have hfirstEq :
      ricciUpperBoundNablaModel S t =
        iterCov (S.base.metric t) 2 (ricciUpperBoundSec S t) 1 :=
    Tensor0SBundle.totalNabla0SRealizes_unique hfirst
      (iterCov_realizes (S.base.metric t) (ricciUpperBoundSec S t) 0)
  rw [hfirstEq] at hsecond
  exact Tensor0SBundle.totalNabla0SRealizes_unique hsecond
    (iterCov_realizes (S.base.metric t) (ricciUpperBoundSec S t) 1)

private theorem metric_section_square_gradient_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (V : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hcovV :
      ∀ W : ContMDiffSection I E ∞ (TangentSpace I : M → Type _),
        (leviCivitaConnectionOfMetric g (fun y => V y) x) (W x) = 0) :
    gradientFun (I := I) g
      (fun y => g.inner y (V y) (V y)) x = 0 := by
  apply gradientFun_eq_zero_of_mfderiv_eq_zero
  ext z
  change mfderiv I 𝓘(ℝ, ℝ)
    (fun y => g.inner y (V y) (V y)) x z = 0
  obtain ⟨W, hW, _⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply
      (I := I) (leviCivitaConnectionOfMetric g) x z
  have hm := IsMetricCompatible.mvfderiv_inner
    (leviCivitaConnectionOfMetric_isMetricCompatible g) (x := x) (W x)
    (V.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    (V.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  rw [hcovV W] at hm
  apply (NormedSpace.fromTangentSpace (g.inner x (V x) (V x))).injective
  simpa only [mvfderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, hW, map_zero, zero_apply, add_zero] using hm

omit [CompleteSpace E] [T2Space M] in
private theorem normalized_local_operator
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T t : ℝ) (hT : 0 < T) (ht : t ∈ Icc 0 T)
    (b d : ℝ → M → ℝ) (x : M) (ell : ℝ)
    (hbtime : DifferentiableWithinAt ℝ
      (fun s => b s x) (Icc 0 T) t)
    (hdtime : DifferentiableWithinAt ℝ
      (fun s => d s x) (Icc 0 T) t)
    (hbspace : ContMDiff I 𝓘(ℝ, ℝ) ∞ (b t))
    (hdspace : ContMDiff I 𝓘(ℝ, ℝ) ∞ (d t))
    (hbzero : b t x = 0) (hdone : d t x = 1)
    (hdgrad : gradientFun (I := I) (G.metric t) (d t) x = 0) :
    let ψ := fun s y => ell + b s y / d s y
    ψ t x = ell ∧
      DifferentiableWithinAt ℝ (fun s => ψ s x) (Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (ψ t) y) ∧
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (T% (gradientFun (I := I) (G.metric t) (ψ t))) x ∧
      parabolicOperatorWithDrift G T (fun _ _ => 0) ψ t x =
        parabolicOperatorWithDrift G T (fun _ _ => 0) b t x ∧
      parabolicOperatorWithDrift G T (fun _ _ => 0)
          (fun s y => -ψ s y) t x =
        -parabolicOperatorWithDrift G T (fun _ _ => 0) b t x := by
  let q := fun s y => b s y / d s y
  let ψ := fun s y => ell + q s y
  have huniq := (uniqueDiffOn_Icc hT) t ht
  have hdne : d t x ≠ 0 := by rw [hdone]; norm_num
  have hnear : ∀ᶠ y in 𝓝 x, d t y ≠ 0 :=
    hdspace.continuous.continuousAt.eventually_ne hdne
  have hqtime :
      DifferentiableWithinAt ℝ (fun s => q s x) (Icc 0 T) t :=
    hbtime.div hdtime hdne
  have hqspace :
      ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (q t) y := by
    filter_upwards [hnear] with y hy
    have hh := (hbspace.mdifferentiableAt (x := y) (by simp)).mul
      ((hdspace.mdifferentiableAt (x := y) (by simp)).inv hy)
    convert hh using 1 <;> rfl
  have hqAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (q t) x :=
    hbspace.contMDiffAt.div₀ hdspace.contMDiffAt hdne
  have hqgrad :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (T% (gradientFun (I := I) (G.metric t) (q t))) x :=
    (gradientFun_contMDiffAt (G.metric t) hqAt).mdifferentiableAt
      (by simp)
  have hψtime :
      DifferentiableWithinAt ℝ (fun s => ψ s x) (Icc 0 T) t :=
    (differentiableWithinAt_const ell).add hqtime
  have hψspace :
      ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (ψ t) y :=
    hqspace.mono fun y hy => mdifferentiableAt_const.add hy
  have hψAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (ψ t) x :=
    contMDiffAt_const.add hqAt
  have hψgrad :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (T% (gradientFun (I := I) (G.metric t) (ψ t))) x :=
    (gradientFun_contMDiffAt (G.metric t) hψAt).mdifferentiableAt
      (by simp)
  have hcspace :
      ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun _ : M => ell) y :=
    Eventually.of_forall fun _ => mdifferentiableAt_const
  have hcgrad :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (T% (gradientFun (I := I) (G.metric t) (fun _ : M => ell))) x := by
    simp only [gradientFun_const]
    exact mdifferentiableAt_zeroSection
      (𝕜 := ℝ) (F := E) (E := TangentSpace I)
  have hPconst :
      parabolicOperatorWithDrift G T (fun _ _ => 0)
        (fun _ _ => ell) t x = 0 := by
    unfold parabolicOperatorWithDrift heatOperatorWithDrift laplacianAt
    rw [(hasDerivWithinAt_const t (Icc 0 T) ell).derivWithin huniq,
      laplacian_const]
    simp only [driftTerm, gradientAt, gradientFun_const,
      map_zero, add_zero, sub_zero]
  have hadd := parabolic_add_local G T (fun _ _ => 0)
    (fun _ _ => ell) q t x
    (differentiableWithinAt_const ell) hqtime
    hcspace hqspace hcgrad hqgrad
  have hPadd :
      parabolicOperatorWithDrift G T (fun _ _ => 0) ψ t x =
        parabolicOperatorWithDrift G T (fun _ _ => 0) q t x := by
    change parabolicOperatorWithDrift G T (fun _ _ => 0)
      (fun s y => ell + q s y) t x = _
    rw [hadd, hPconst, zero_add]
  have hquot := parabolic_div_at_zero_unit_denominator
    G T t b d x hbtime hdtime hbspace hdspace hbzero hdone hdgrad
  have hPψ :
      parabolicOperatorWithDrift G T (fun _ _ => 0) ψ t x =
        parabolicOperatorWithDrift G T (fun _ _ => 0) b t x :=
    hPadd.trans hquot
  have hneg :
      parabolicOperatorWithDrift G T (fun _ _ => 0)
          (fun s y => -ψ s y) t x =
        -parabolicOperatorWithDrift G T (fun _ _ => 0) ψ t x := by
    have hh := parabolic_time_mul_local G T (fun _ _ => 0)
      ψ t x hψtime hψspace hψgrad
      (fun _ => (-1 : ℝ)) 0
      (hasDerivWithinAt_const t (Icc 0 T) (-1)) huniq
    simpa only [neg_one_mul, zero_mul, add_zero] using hh
  refine ⟨?_, hψtime, hψspace, hψgrad, hPψ, ?_⟩
  · simp only [hbzero, zero_div, add_zero]
  · rw [hneg, hPψ]

theorem exists_rayleigh_support_operator_in_ordered_frame
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (T : ℝ) (hT : 0 < T)
    (hdim : ∀ y : M, Module.finrank ℝ (TangentSpace I y) = 3)
    (hTsub : Icc 0 T ⊆ D.carrier)
    (hTreg : Ioc 0 T ⊆ D.regular)
    (t : ℝ) (ht : t ∈ Ioc 0 T) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (r1 r2 r3 : ℝ)
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (h21 : r2 ≤ r1) (h32 : r3 ≤ r2)
    (hdiag : ∀ i j : Fin 3,
      S.ricciAt t x (vec2 (I := I) (basis i) (basis j)) =
        ricciDiag3 r1 r2 r3 i j)
    (hleft : ∀ z : TangentSpace I x,
      ricciUpperBoundSec S t x (vec2 (I := I) (basis 0) z) =
        ((1 / 2 : ℝ) * S.scalar t x - r1) *
          (S.base.metric t).inner x (basis 0) z)
    (hright : ∀ z : TangentSpace I x,
      ricciUpperBoundSec S t x (vec2 (I := I) z (basis 0)) =
        ((1 / 2 : ℝ) * S.scalar t x - r1) *
          (S.base.metric t).inner x z (basis 0)) :
    let ell := (1 / 2 : ℝ) * S.scalar t x - r1
    ∃ V : ContMDiffSection I E ∞ (TangentSpace I : M → Type _),
      V x = basis 0 ∧
      (∀ W : ContMDiffSection I E ∞ (TangentSpace I : M → Type _),
        (leviCivitaConnectionOfMetric (S.base.metric t)
          (fun y => V y) x) (W x) = 0) ∧
      let d := fun s y => (S.base.metric s).inner y (V y) (V y)
      let b := fun s y =>
        ricciUpperBoundSec S s y (vec2 (I := I) (V y) (V y)) - ell * d s y
      let ψ := fun s y => ell + b s y / d s y
      ψ t x = ell ∧
        DifferentiableWithinAt ℝ (fun s => ψ s x) (Icc 0 T) t ∧
        (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (ψ t) y) ∧
        MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (T% (gradientFun (I := I) (S.base.metric t) (ψ t))) x ∧
        2 * r1 * ell ≤
          parabolicOperatorWithDrift (flowG S) T (fun _ _ => 0) ψ t x ∧
        ∀ K : ℝ, ell < 0 → r1 ≤ 3 * K →
          parabolicOperatorWithDrift (flowG S) T (fun _ _ => 0)
              (fun s y => -ψ s y) t x ≤
            6 * K * (-ell) := by
  let ell := (1 / 2 : ℝ) * S.scalar t x - r1
  let g := S.base.metric t
  obtain ⟨V, hV, hcovV⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply
      (I := I) (leviCivitaConnectionOfMetric g) x (basis 0)
  let a := fun s y =>
    ricciUpperBoundSec S s y (vec2 (I := I) (V y) (V y))
  let d := fun s y => (S.base.metric s).inner y (V y) (V y)
  let b := fun s y => a s y - ell * d s y
  let ψ := fun s y => ell + b s y / d s y
  have htcc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
  have huniq := (uniqueDiffOn_Icc hT) t htcc
  have hunit : g.inner x (basis 0) (basis 0) = 1 := by
    simpa only [delta3, ite_true] using horth 0 0
  have hr1 :
      S.ricciAt t x (vec2 (I := I) (basis 0) (basis 0)) = r1 := by
    simpa only [ricciDiag3, ite_true] using hdiag 0 0
  have hquad
      (B : Tensor0SField (I := I) (M := M) ∞ 2) :
      ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun y => B y (vec2 (I := I) (V y) (V y))) := by
    simpa only [vec2_self_eq_const] using
      TensorMultilinear.contMDiff_tensor0SField_apply B (fun _ => V)
  have haspace : ContMDiff I 𝓘(ℝ, ℝ) ∞ (a t) :=
    hquad (ricciUpperBoundSec S t)
  have hdspace : ContMDiff I 𝓘(ℝ, ℝ) ∞ (d t) := by
    simpa only [metricTensorField_apply, vec2_self_eq_const] using
      hquad (metricTensorField g)
  have hbspace : ContMDiff I 𝓘(ℝ, ℝ) ∞ (b t) :=
    haspace.sub (contMDiff_const.mul hdspace)
  have hdone : d t x = 1 := by
    change g.inner x (V x) (V x) = 1
    rw [hV]
    exact hunit
  have hbzero : b t x = 0 := by
    change ricciUpperBoundSec S t x
      (vec2 (I := I) (V x) (V x)) -
        ell * g.inner x (V x) (V x) = 0
    rw [hV, hleft]
    dsimp only [ell]
    ring
  have hdgrad :
      gradientFun (I := I) (S.base.metric t) (d t) x = 0 :=
    metric_section_square_gradient_zero g x V hcovV
  obtain ⟨μ, hμtime, hμineq⟩ :=
    (ricci_upper_bound_parabolic
      S hS hdim hTsub hTreg).evaluatedInequality
  have hatime :
      HasDerivWithinAt (fun s => a s x)
        (μ t x (basis 0)) (Icc 0 T) t := by
    simpa only [a, hV, twoTensorSecToFamily] using
      hμtime t ht x (basis 0)
  have hdtime :
      HasDerivWithinAt (fun s => d s x)
        (-2 * r1) (Icc 0 T) t := by
    have hh := (metric_derivWithin_eq_neg_two_ricci
      S hS.isSolution ⟨t, hTreg ht⟩
      x (basis 0) (basis 0)).mono hTsub
    simpa only [d, hV, SolutionOn.family_metric, hr1] using hh
  have hbtime :
      HasDerivWithinAt (fun s => b s x)
        (μ t x (basis 0) - ell * (-2 * r1)) (Icc 0 T) t :=
    hatime.sub (hdtime.const_mul ell)
  let heat :=
    tensorHeatWithDrift2QuadMetricAt (I := I) g
      (fun _ : M => 0)
      (ricciUpperBoundNab2ModelSec S t x)
      (ricciUpperBoundNablaModel S t x)
      (basis 0)
  have hbfun :
      b t = fun y =>
        (ricciUpperBoundSec S t + (-ell) • metricTensorField g) y
          (vec2 (I := I) (V y) (V y)) := by
    funext y
    change ricciUpperBoundSec S t y
        (vec2 (I := I) (V y) (V y)) -
          ell * g.inner y (V y) (V y) =
      ricciUpperBoundSec S t y
        (vec2 (I := I) (V y) (V y)) +
          (-ell) * metricTensorField g y
            (vec2 (I := I) (V y) (V y))
    simp only [metricTensorField_apply, vec2_self_eq_const]
    ring
  have hlap :
      laplacianAt (flowG S) t (b t) x = heat := by
    have hh := laplacian_shifted_tensor_at_eigenvector
      g (ricciUpperBoundSec S t) x (basis 0) ell V
      hV hcovV hleft hright
    rw [← upper_second_eq_iterCov S t] at hh
    change laplacian (leviCivitaConnectionOfMetric g) g (b t) x = heat
    rw [hbfun]
    simpa only [heat, tensorHeatWithDrift2QuadMetricAt_zero_drift,
      tensorHeat0SMetricAt_apply] using hh
  let reaction :=
    ricciUpperBoundReact (I := I) (M := M)
      t g
      (twoTensorSecToFamily (I := I) (M := M)
        (ricciUpperBoundSec S) t)
      x (basis 0) (basis 0)
  have hreaction : 0 ≤ reaction := by
    change 0 ≤ ricciUpperBoundReact (I := I) (M := M) t (S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t)
      x (basis 0) (basis 0)
    rw [ricci_upper_bound_reaction_in_eigenframe
      S t x basis horth r1 r2 r3 hdiag]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (sub_nonneg.mpr h21))
      (sub_nonneg.mpr (h32.trans h21))
  have hPb :
      reaction + 2 * r1 * ell ≤
        parabolicOperatorWithDrift (flowG S) T
          (fun _ _ => 0) b t x := by
    have hh := hμineq t ht x (basis 0)
    change heat + reaction ≤ μ t x (basis 0) at hh
    unfold parabolicOperatorWithDrift heatOperatorWithDrift
    rw [hbtime.derivWithin huniq, hlap]
    simp only [driftTerm, map_zero, zero_apply, add_zero]
    nlinarith only [hh]
  obtain ⟨hψvalue, hψtime, hψspace, hψgrad, hPψ, hPneg⟩ :=
    normalized_local_operator (flowG S) T t hT htcc
      b d x ell hbtime.differentiableWithinAt hdtime.differentiableWithinAt
      hbspace hdspace hbzero hdone hdgrad
  refine ⟨V, hV, hcovV, hψvalue, hψtime, hψspace, hψgrad, ?_, ?_⟩
  · change 2 * r1 * ell ≤ parabolicOperatorWithDrift (flowG S) T (fun _ _ => 0) ψ t x
    rw [hPψ]
    exact (le_add_of_nonneg_left hreaction).trans hPb
  · intro K hell hK
    change ell < 0 at hell
    change parabolicOperatorWithDrift (flowG S) T (fun _ _ => 0)
      (fun s y => -ψ s y) t x ≤ 6 * K * (-ell)
    rw [hPneg]
    have hm := mul_le_mul_of_nonneg_right hK
      (neg_nonneg.mpr hell.le)
    nlinarith only [hPb, hreaction, hm]

end DifferentialGeometry.PDE.RicciFlow

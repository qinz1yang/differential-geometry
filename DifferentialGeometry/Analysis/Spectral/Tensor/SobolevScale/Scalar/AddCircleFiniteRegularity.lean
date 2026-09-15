import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleClassicalDerivative
import Mathlib.Topology.UniformSpace.UniformApproximation

noncomputable section
open scoped Manifold ContDiff Topology
namespace AddCircle
open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem hasDerivAt_scalarH1ToContinuous_of_order
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n)
    (u : TensorHs g 0 0 ((n : ℝ) + 1)) (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ (n : ℝ) + 1) u)
        (t : AddCircle (1 : ℝ)))
      (scalarH1ToContinuous g
        (tensorHsInclusion (by exact_mod_cast hn)
          (parameterDerivativeHs g n u)) (x : AddCircle (1 : ℝ))) x := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := hasDerivAt_scalarH1ToContinuous g
    (tensorHsInclusion (by norm_num; linarith : ((1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 1) u) x
  have hder := parameterDerivativeHs_tensorHsInclusion g (n := 1) (m := n)
    hn u
  rw [hder, ← tensorHsInclusion_trans_apply] at h
  simpa only [← tensorHsInclusion_trans_apply] using h

theorem contDiff_scalarH1ToContinuous
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (n : ℕ) (u : TensorHs g 0 0 ((n : ℝ) + 1)) :
    ContDiff ℝ n (fun t : ℝ => scalarH1ToContinuous g
      (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ (n : ℝ) + 1) u)
      (t : AddCircle (1 : ℝ))) := by
  induction n with
  | zero =>
      apply contDiff_zero.mpr
      exact (scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num) u)).continuous.comp
        (AddCircle.continuous_mk' 1)
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨?_, ?_, ?_⟩
      · intro x
        exact (hasDerivAt_scalarH1ToContinuous_of_order g (by omega) u x).differentiableAt
      · norm_num
      · have hderiv : deriv (fun t : ℝ => scalarH1ToContinuous g
          (tensorHsInclusion (by norm_num; positivity : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1) u)
          (t : AddCircle (1 : ℝ))) =
          (fun t : ℝ => scalarH1ToContinuous g
            (tensorHsInclusion (by exact_mod_cast (show 1 ≤ n + 1 by omega))
              (parameterDerivativeHs g (n + 1) u))
            (t : AddCircle (1 : ℝ))) := by
            funext x
            exact (hasDerivAt_scalarH1ToContinuous_of_order g (by omega) u x).deriv
        rw [hderiv]
        have h := ih (tensorHsInclusion
          (by norm_num : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ))
          (parameterDerivativeHs g (n + 1) u))
        simpa only [← tensorHsInclusion_trans_apply] using h

theorem deriv_scalarH1ToContinuous
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n) (u : TensorHs g 0 0 ((n : ℝ) + 1)) :
    deriv (fun t : ℝ => scalarH1ToContinuous g
      (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ (n : ℝ) + 1) u)
      (t : AddCircle (1 : ℝ))) =
      (fun t : ℝ => scalarH1ToContinuous g
        (tensorHsInclusion (by exact_mod_cast hn)
          (parameterDerivativeHs g n u)) (t : AddCircle (1 : ℝ))) := by
  funext x
  exact (hasDerivAt_scalarH1ToContinuous_of_order g hn u x).deriv

theorem contDiff_scalarH1PiToContinuous {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (n : ℕ) (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1))) :
    ContDiff ℝ n (fun t : ℝ => scalarH1PiToContinuous g
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ (n : ℝ) + 1)) u)
      (t : AddCircle (1 : ℝ))) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_scalarH1ToContinuous g n (u i)

theorem deriv_scalarH1PiToContinuous {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n)
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1))) :
    deriv (fun t : ℝ => scalarH1PiToContinuous g
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ (n : ℝ) + 1)) u)
      (t : AddCircle (1 : ℝ))) =
      (fun t : ℝ => scalarH1PiToContinuous g
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by exact_mod_cast hn)) (parameterDerivativeHsPi g n u))
        (t : AddCircle (1 : ℝ))) := by
  funext x
  apply HasDerivAt.deriv
  apply hasDerivAt_pi.mpr
  intro i
  exact hasDerivAt_scalarH1ToContinuous_of_order g hn (u i) x

theorem tendstoUniformly_iteratedDeriv_scalarH1ToContinuous
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (n : ℕ) {α : Type*} {l : Filter α}
    {U : α → TensorHs g 0 0 ((n : ℝ) + 1)}
    {u : TensorHs g 0 0 ((n : ℝ) + 1)} (h : Filter.Tendsto U l (𝓝 u)) :
    TendstoUniformly
      (fun a => iteratedDeriv n (fun t : ℝ => scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ (n : ℝ) + 1) (U a))
        (t : AddCircle (1 : ℝ))))
      (iteratedDeriv n (fun t : ℝ => scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ (n : ℝ) + 1) u)
        (t : AddCircle (1 : ℝ)))) l := by
  induction n with
  | zero =>
      simp only [iteratedDeriv_zero]
      exact (ContinuousMap.tendsto_iff_tendstoUniformly.mp
        (((scalarH1ToContinuous g).continuous.comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by norm_num : (1 : ℝ) ≤ (0 : ℕ) + 1)).continuous).tendsto u |>.comp h)).comp
          (fun t : ℝ => (t : AddCircle (1 : ℝ)))
  | succ n ih =>
      simp only [iteratedDeriv_succ', deriv_scalarH1ToContinuous g (show 1 ≤ n + 1 by omega)]
      let L := (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ))).comp
          (parameterDerivativeHs g (n + 1))
      have hL := (L.continuous.tendsto u).comp h
      have hrec := ih hL
      simpa only [Function.comp_apply, L, ContinuousLinearMap.comp_apply,
        ← tensorHsInclusion_trans_apply] using hrec

theorem tendstoUniformly_iteratedDeriv_scalarH1PiToContinuous {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (n : ℕ) {α : Type*} {l : Filter α}
    {U : α → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1))}
    {u : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1))}
    (h : Filter.Tendsto U l (𝓝 u)) :
    TendstoUniformly
      (fun a => iteratedDeriv n (fun t : ℝ => scalarH1PiToContinuous g
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by norm_num : (1 : ℝ) ≤ (n : ℝ) + 1)) (U a))
        (t : AddCircle (1 : ℝ))))
      (iteratedDeriv n (fun t : ℝ => scalarH1PiToContinuous g
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by norm_num : (1 : ℝ) ≤ (n : ℝ) + 1)) u)
        (t : AddCircle (1 : ℝ)))) l := by
  induction n with
  | zero =>
      simp only [iteratedDeriv_zero]
      exact (ContinuousMap.tendsto_iff_tendstoUniformly.mp
        (((scalarH1PiToContinuous g).continuous.comp
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by norm_num : (1 : ℝ) ≤ (0 : ℕ) + 1))).continuous).tendsto u |>.comp h)).comp
          (fun t : ℝ => (t : AddCircle (1 : ℝ)))
  | succ n ih =>
      simp only [iteratedDeriv_succ', deriv_scalarH1PiToContinuous g (show 1 ≤ n + 1 by omega)]
      let L := (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ)))).comp
            (parameterDerivativeHsPi g (n + 1))
      have hL := (L.continuous.tendsto u).comp h
      have hrec := ih hL
      have heq (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 1))) :
          ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by norm_num : (1 : ℝ) ≤ (n : ℝ) + 1)) (L v) =
          ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by exact_mod_cast (show 1 ≤ n + 1 by omega)))
            (parameterDerivativeHsPi g (n + 1) v) := by
        apply PiLp.ext
        intro i
        simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.piLpMap_apply]
        exact (tensorHsInclusion_trans_apply (by norm_num) (by norm_num) _).symm
      simpa only [Function.comp_apply, heq] using hrec

theorem continuous_iteratedDeriv_scalarH1ToContinuous
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    Continuous (fun p : TensorHs g 0 0 ((n : ℝ) + 1) × ℝ =>
      iteratedDeriv n (fun t : ℝ => scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ (n : ℝ) + 1) p.1)
        (t : AddCircle (1 : ℝ))) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (tendstoUniformly_iteratedDeriv_scalarH1ToContinuous g n
    (continuous_fst.tendsto p)).tendsto_comp
      ((contDiff_scalarH1ToContinuous g n p.1).continuous_iteratedDeriv' n).continuousAt
      (continuous_snd.tendsto p)

theorem continuous_iteratedDeriv_scalarH1PiToContinuous {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    Continuous (fun p : (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1))) × ℝ =>
      iteratedDeriv n (fun t : ℝ => scalarH1PiToContinuous g
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by norm_num : (1 : ℝ) ≤ (n : ℝ) + 1)) p.1)
        (t : AddCircle (1 : ℝ))) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (tendstoUniformly_iteratedDeriv_scalarH1PiToContinuous g n
    (continuous_fst.tendsto p)).tendsto_comp
      ((contDiff_scalarH1PiToContinuous g n p.1).continuous_iteratedDeriv' n).continuousAt
      (continuous_snd.tendsto p)

end AddCircle

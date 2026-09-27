import DifferentialGeometry.Analysis.Parabolic.Energy.ParabolicLocalAlgebra

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Analysis
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem gradient_affine_local (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (x : M) (A c : ℝ)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y)
    (hg : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (gradientFun (I := I) g f)) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g (fun y => A + c * f y))) x := by
  apply (hg.smul_const_section (a := c)).congr_of_eventuallyEq
  filter_upwards [hf] with y hy
  apply congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I)))
  have hc : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => c * f z) y := mdifferentiableAt_const.mul hy
  rw [gradientFun_add g (f := fun _ => A) (h := fun z => c * f z) mdifferentiableAt_const hc,
    gradientFun_const]
  rw [zero_add]
  exact gradientFun_const_smul g c hy

private theorem affine_sub_local (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T : ℝ) (X : ℝ → (x : M) → TangentSpace I x) (u : ℝ → M → ℝ)
    (t : ℝ) (x : M) (A b : ℝ) (huniq : UniqueDiffWithinAt ℝ (Icc 0 T) t)
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hu_grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) (G.metric t) (u t))) x) :
    parabolicOperatorWithDrift G T X (fun s y => A + b * s - u s y) t x =
      b - parabolicOperatorWithDrift G T X u t x := by
  have hnegspace := hu_space.mono fun y hy => (mdifferentiableAt_const (c := (-1 : ℝ))).mul hy
  have hneggrad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) (G.metric t) (fun y => (-1 : ℝ) * u t y))) x := by
    simpa only [zero_add] using gradient_affine_local (G.metric t) (u t) x 0 (-1) hu_space hu_grad
  have hneg := parabolic_time_mul_local G T X u t x hu_time hu_space hu_grad
    (fun _ => (-1 : ℝ)) 0 (hasDerivWithinAt_const t (Icc 0 T) (-1)) huniq
  have haff : HasDerivWithinAt (fun s : ℝ => A + b * s) b (Icc 0 T) t := by
    have hh := (((hasDerivAt_id t).const_mul b).const_add A).hasDerivWithinAt (s := Icc 0 T)
    simp only [mul_one, id_eq] at hh
    exact hh
  have haffspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun _ : M => A + b * t) y :=
    Eventually.of_forall fun _ => mdifferentiableAt_const
  have haffgrad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) (G.metric t) (fun _ : M => A + b * t))) x := by
    simp only [gradientFun_const]
    exact mdifferentiableAt_zeroSection (𝕜 := ℝ) (F := E) (E := TangentSpace I)
  have hadd := parabolic_add_local G T X (fun s _ => A + b * s) (fun s y => (-1 : ℝ) * u s y)
    t x haff.differentiableWithinAt (hu_time.const_mul (-1)) haffspace hnegspace haffgrad hneggrad
  have hp : parabolicOperatorWithDrift G T X (fun s _ => A + b * s) t x = b := by
    unfold parabolicOperatorWithDrift heatOperatorWithDrift laplacianAt
    rw [haff.derivWithin huniq, laplacian_const]
    simp only [driftTerm, gradientAt, gradientFun_const, map_zero, zero_add, sub_zero]
  rw [hp, hneg] at hadd
  simpa only [neg_one_mul, zero_mul, add_zero, sub_eq_add_neg] using hadd

theorem scalar_linear_reaction_bound_support [I.Boundaryless]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) (T : ℝ) (hT : 0 < T)
    (X : ℝ → (x : M) → TangentSpace I x) (u : ℝ → M → ℝ)
    (K : Set M) (hK : IsCompact K) (a b A : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hcont : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (Icc 0 T ×ˢ K))
    (hout : ∀ t ∈ Icc 0 T, ∀ x ∉ K, u t x ≤ 0)
    (hinit : ∀ x : M, u 0 x ≤ A)
    (hsupport : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < u t x →
      ∃ v : ℝ → M → ℝ, v t x = u t x ∧
        (∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x), v p.1 p.2 ≤ u p.1 p.2) ∧
        DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t ∧
        (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) y) ∧
        MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (gradientFun (I := I) (G.metric t) (v t))) x ∧
        parabolicOperatorWithDrift G T X v t x ≤ a * v t x + b) :
    ∀ t ∈ Icc 0 T, ∀ x : M, u t x ≤ Real.exp (a * t) * (A + b * t) := by
  let w := fun s y => A + b * s - Real.exp (-a * s) * u s y
  have hscale : ContDiff ℝ ∞ (fun s : ℝ => Real.exp (-a * s)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hnonneg := strict_barrier_compact_of_upperSupport G T X w K hK
    (fun s hs y hy => by
      have hp := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-a * s)).le (hout s hs y hy)
      dsimp only [w]
      linarith [mul_nonneg hb hs.1])
    (((continuous_const.add (continuous_const.mul continuous_fst)).continuousOn).sub
      (((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).continuousOn).mul hcont))
    (fun y => by simpa only [w, mul_zero, add_zero, Real.exp_zero, one_mul] using sub_nonneg.mpr (hinit y))
    (fun s hs hspos y hneg => by
      have hpositive : 0 < u s y := by
        have hb0 : 0 ≤ A + b * s := add_nonneg hA (mul_nonneg hb hs.1)
        have hexp := Real.exp_pos (-a * s)
        dsimp only [w] at hneg
        nlinarith
      let v := Classical.choose (hsupport s hs hspos y hpositive)
      have hv := Classical.choose_spec (hsupport s hs hspos y hpositive)
      rcases hv with ⟨heq, hle, htime, hspace, hgrad, hP⟩
      change v s y = u s y at heq
      let V := fun r z => Real.exp (-a * r) * v r z
      have hVtime : DifferentiableWithinAt ℝ (fun r => V r y) (Icc 0 T) s :=
        (((hscale.differentiable (by simp)) s).differentiableWithinAt).mul htime
      have hVspace : ∀ᶠ z in 𝓝 y, MDifferentiableAt I 𝓘(ℝ, ℝ) (V s) z :=
        hspace.mono fun z hz => mdifferentiableAt_const.mul hz
      have hVgrad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (T% (gradientFun (I := I) (G.metric s) (V s))) y := by
        simpa only [zero_add] using gradient_affine_local (G.metric s) (v s) y 0 (Real.exp (-a * s)) hspace hgrad
      have hPV : parabolicOperatorWithDrift G T X V s y ≤ b := by
        rw [parabolic_exp_rescale_local G T X v s y htime hspace hgrad a ((uniqueDiffOn_Icc hT) s hs)]
        have hh := mul_le_mul_of_nonneg_left (show parabolicOperatorWithDrift G T X v s y - a * v s y ≤ b by linarith)
          (Real.exp_pos (-a * s)).le
        have he : Real.exp (-a * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [ha, hs.1])
        exact hh.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right he hb)
      refine { upperSupport := fun r z => A + b * r - V r z
               eq_at := by simp only [V, w, heq]
               upper_nhds := ?_
               time_diff := ?_
               space_diff_nhds := ?_
               grad_diff := ?_
               operator_nonneg := ?_ }
      · filter_upwards [hle] with p hp
        dsimp only [w, V]
        exact sub_le_sub_left (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le) _
      · exact ((differentiableWithinAt_const A).add (differentiableWithinAt_id.const_mul b)).sub hVtime
      · exact hVspace.mono fun z hz => mdifferentiableAt_const.sub hz
      · have hh := gradient_affine_local (G.metric s) (V s) y (A + b * s) (-1) hVspace hVgrad
        simpa only [neg_one_mul, sub_eq_add_neg] using hh
      · rw [affine_sub_local G T X V s y A b ((uniqueDiffOn_Icc hT) s hs) hVtime hVspace hVgrad]
        exact sub_nonneg.mpr hPV)
  intro t ht x
  have hh := mul_le_mul_of_nonneg_left (show Real.exp (-a * t) * u t x ≤ A + b * t by
    have hw := hnonneg t ht x
    dsimp only [w] at hw
    linarith) (Real.exp_pos (a * t)).le
  have he : Real.exp (a * t) * (Real.exp (-a * t) * u t x) = u t x := by
    rw [← mul_assoc, ← Real.exp_add]
    simp only [neg_mul, add_neg_cancel, Real.exp_zero, one_mul]
  rwa [he] at hh
end DifferentialGeometry.Analysis

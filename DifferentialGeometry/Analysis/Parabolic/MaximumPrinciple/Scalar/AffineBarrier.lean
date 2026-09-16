import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak

set_option autoImplicit false
noncomputable section

open Set Filter Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Parabolic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace E] in
theorem scalar_lower_affine_barrier
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T K : ℝ) (X : ℝ → (x : M) → TangentSpace I x)
    (v : ℝ → M → ℝ)
    (hv_cont : ContinuousOn (fun p : ℝ × M => v p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hv_time : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t)
    (hv_mdiff : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) x)
    (hv_grad : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (v t) y) x)
    (hv0 : ∀ x : M, 1 ≤ v 0 x)
    (hP : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      -K ≤ parabolicOperatorWithDrift (I := I) G T X v t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M, 1 - K * t ≤ v t x := by
  let c : ℝ → ℝ := fun t => 1 - K * t
  let w : ℝ → M → ℝ := fun t x => v t x - c t
  have hw_cont : ContinuousOn (fun p : ℝ × M => w p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    dsimp [w, c]
    exact hv_cont.sub ((continuous_const.sub (continuous_const.mul continuous_fst)).continuousOn)
  have hw0 : ∀ x : M, 0 ≤ w 0 x := by
    intro x
    dsimp [w, c]
    simpa using hv0 x
  have hw_time : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt ℝ (fun s => w s x) (Icc 0 T) t := by
    intro t ht htpos x
    dsimp [w, c]
    exact (hv_time t ht htpos x).sub
      ((differentiableWithinAt_const (1 : ℝ)).sub
        ((differentiableWithinAt_fun_id (𝕜 := ℝ)).const_mul K))
  have hw_mdiff : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (w t) x := by
    intro t ht htpos x
    dsimp [w, c]
    exact (hv_mdiff t ht htpos x).sub mdifferentiableAt_const
  have hw_grad : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (w t) y) x := by
    intro t ht htpos x
    have hfun : (fun y : M => gradientFun (I := I) (G.metric t) (w t) y) =
        (fun y : M => gradientFun (I := I) (G.metric t) (v t) y) := by
      funext y
      dsimp [w, c]
      rw [gradientFun_sub (I := I) (G.metric t) (hv_mdiff t ht htpos y)
        mdifferentiableAt_const, gradientFun_const]
      simp
    have hsection :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (w t) y) =
          (T% fun y : M => gradientFun (I := I) (G.metric t) (v t) y) := by
      funext y
      exact congrArg (fun q => (⟨y, q⟩ : TotalSpace E (TangentSpace I)))
        (congrFun hfun y)
    rw [hsection]
    exact hv_grad t ht htpos x
  have hneg : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, w t x < 0 →
      0 ≤ parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht htpos x hwneg
    have hc : DifferentiableWithinAt ℝ c (Icc 0 T) t := by
      dsimp [c]
      exact (differentiableWithinAt_const (1 : ℝ)).sub
        ((differentiableWithinAt_fun_id (𝕜 := ℝ)).const_mul K)
    have hp := parabolic_sub_time_curve_identity (I := I) G T X v c t
      (fun y => hv_mdiff t ht htpos y) x (hv_time t ht htpos x) hc
    rw [hp]
    have hcderiv : derivWithin c (Icc 0 T) t = -K := by
      have hconst : HasDerivWithinAt (fun _ : ℝ => (1 : ℝ)) 0
          (Icc 0 T) t := hasDerivWithinAt_const t (Icc 0 T) 1
      have hid : HasDerivWithinAt (fun s : ℝ => s) 1
          (Icc 0 T) t := hasDerivWithinAt_id t (Icc 0 T)
      have h := hconst.sub (hid.const_mul K)
      dsimp [c]
      have hTpos : 0 < T := lt_of_lt_of_le htpos ht.2
      have hu := h.derivWithin ((uniqueDiffOn_Icc hTpos) t ht)
      have hfun : (fun s : ℝ => 1 - K * s) =
          (fun s : ℝ => (1 : ℝ)) - (fun s : ℝ => K * s) := by
        funext s
        simp only [Pi.sub_apply]
      rw [hfun]
      simpa using hu
    rw [hcderiv]
    have := hP t ht htpos x
    linarith
  have hw := strict_barrier_nonnegative_of_positive_time (I := I) G T X w
    hw_cont hw0 hw_time hw_mdiff hw_grad hneg
  intro t ht x
  have := hw t ht x
  dsimp [w, c] at this
  linarith

omit [CompleteSpace E] in
theorem scalar_two_sided_affine_barrier
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T K : ℝ) (X : ℝ → (x : M) → TangentSpace I x)
    (v : ℝ → M → ℝ)
    (hv_cont : ContinuousOn (fun p : ℝ × M => v p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hv_time : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t)
    (hv_mdiff : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) x)
    (hv_grad : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (v t) y) x)
    (hv0 : ∀ x : M, v 0 x = 1)
    (hP : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      |parabolicOperatorWithDrift (I := I) G T X v t x| ≤ K) :
    ∀ t ∈ Icc 0 T, ∀ x : M, 1 - K * t ≤ v t x ∧ v t x ≤ 1 + K * t := by
  have hlow : ∀ t ∈ Icc 0 T, ∀ x : M, 1 - K * t ≤ v t x := by
    apply scalar_lower_affine_barrier G T K X v hv_cont hv_time hv_mdiff hv_grad
      (fun x => le_of_eq (hv0 x).symm)
    intro t ht htpos x
    exact (abs_le.mp (hP t ht htpos x)).1
  let z : ℝ → M → ℝ := fun t x => 2 - v t x
  have hz_cont : ContinuousOn (fun p : ℝ × M => z p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    dsimp [z]
    exact continuousOn_const.sub hv_cont
  have hz_time : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt ℝ (fun s => z s x) (Icc 0 T) t := by
    intro t ht htpos x
    dsimp [z]
    exact (differentiableWithinAt_const (c := (2 : ℝ))).sub (hv_time t ht htpos x)
  have hz_mdiff : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (z t) x := by
    intro t ht htpos x
    dsimp [z]
    exact mdifferentiableAt_const.sub (hv_mdiff t ht htpos x)
  have hz_grad : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (z t) y) x := by
    intro t ht htpos x
    have hsection :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (z t) y) =
          (T% fun y : M => -gradientFun (I := I) (G.metric t) (v t) y) := by
      funext y
      apply congrArg (fun q => (⟨y, q⟩ : TotalSpace E (TangentSpace I)))
      dsimp [z]
      rw [gradientFun_sub (I := I) (G.metric t) mdifferentiableAt_const
        (hv_mdiff t ht htpos y), gradientFun_const]
      simp
    rw [hsection]
    exact mdifferentiableAt_neg_section (hv_grad t ht htpos x)
  have hz0 : ∀ x : M, 1 ≤ z 0 x := by
    intro x
    dsimp [z]
    rw [hv0 x]
    norm_num
  have hzP : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      -K ≤ parabolicOperatorWithDrift (I := I) G T X z t x := by
    intro t ht htpos x
    have hTpos : 0 < T := lt_of_lt_of_le htpos ht.2
    have hconst := parabolic_const_sub (I := I) G T X v 2 t x
      ((uniqueDiffOn_Icc hTpos) t ht) (hv_time t ht htpos x)
      (fun y => hv_mdiff t ht htpos y) (hv_grad t ht htpos x)
    dsimp [z]
    rw [hconst]
    have hupper := (abs_le.mp (hP t ht htpos x)).2
    linarith
  have hzlow := scalar_lower_affine_barrier G T K X z hz_cont hz_time hz_mdiff hz_grad hz0 hzP
  intro t ht x
  constructor
  · exact hlow t ht x
  · have := hzlow t ht x
    dsimp [z] at this
    linarith

end DifferentialGeometry.Analysis.Parabolic

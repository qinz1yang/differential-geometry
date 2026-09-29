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

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [T2Space M]

omit [CompleteSpace E] [T2Space M] in
theorem scalar_subsolution_affine_bound
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real -> (x : M) -> TangentSpace I x)
    (F : Real -> M -> Real) (a b : Real)
    (hw_cont : ContinuousOn
      (fun p : Real × M => (a + b * p.1) - F p.1 p.2)
      (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T))
    (hF_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => F s x) (Set.Icc 0 T) t)
    (hF_space : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (F t) y)
    (hF_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) (F t) y) x)
    (hinit : forall x : M, F 0 x <= a)
    (hsub : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      DifferentialGeometry.Analysis.Parabolic.parabolicOperatorWithDrift (I := I) G T X F t x <=
        b) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, F t x <= a + b * t := by
  let w : Real -> M -> Real := fun t x => (a + b * t) - F t x
  have hw0 : forall x : M, 0 <= w 0 x := by
    intro x
    have : F 0 x <= a := hinit x
    simp only [w]
    nlinarith [this]
  have hw_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, DifferentiableWithinAt Real (fun s : Real => w s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    have hbarrier : DifferentiableWithinAt Real
        (fun s : Real => a + b * s) (Set.Icc 0 T) t := by
      have hlin : DifferentiableWithinAt Real (fun s : Real => b * s) (Set.Icc 0 T) t := by
        simpa using
          (differentiableWithinAt_fun_id (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul b
      exact (differentiableWithinAt_const a).add hlin
    exact hbarrier.sub (hF_time t ht htpos x)
  have hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real) (w t) x := by
    intro t ht htpos x
    have : MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (a + b * t) - F t y) x :=
      mdifferentiableAt_const.sub (hF_space t ht htpos x)
    simpa [w] using this
  have hw_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) (w t) y) x := by
    intro t ht htpos x
    have hplain :
        (fun y : M =>
          DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) (w t) y) =
        (fun y : M =>
          - DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) (F t)
            y) := by
      funext y
      have hwt : w t = (fun z : M => (a + b * t) - F t z) := rfl
      rw [hwt]
      calc
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t)
            (fun z : M => (a + b * t) - F t z) y =
          DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t)
              (fun _ : M => (a + b * t)) y -
            DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) (F t) y := by
            exact DifferentialGeometry.Geometry.Operator.gradientFun_sub (I := I) (G.metric t)
              mdifferentiableAt_const (hF_space t ht htpos y)
        _ = - DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) (F t)
          y := by
            rw [DifferentialGeometry.Geometry.Operator.gradientFun_const]
            simp
    have hsection :
        (T% fun y : M =>
          DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) (w t) y) =
        (T% fun y : M =>
          - DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) (F t)
            y) := by
      funext y
      simpa using congrFun hplain y
    rw [hsection]
    have hneg :
        (T% fun y : M =>
          - DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) (F t) y) =
        (T% ((-1 : Real) • fun y : M =>
          DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric t) (F t) y)) := by
      funext y
      simp
    rw [hneg]
    exact (hF_grad t ht htpos x).smul_const_section (a := (-1 : Real))
  have hnegative : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, w t x < 0 ->
        0 <= DifferentialGeometry.Analysis.Parabolic.parabolicOperatorWithDrift (I := I) G T X w t
          x := by
    intro t ht htpos x _hwneg
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
      (uniqueDiffOn_Icc (lt_of_lt_of_le htpos ht.2)).uniqueDiffWithinAt ht
    have hident :
        DifferentialGeometry.Analysis.Parabolic.parabolicOperatorWithDrift (I := I) G T X w t x =
          b - DifferentialGeometry.Analysis.Parabolic.parabolicOperatorWithDrift (I := I) G T X F t
            x := by
      simpa [w] using
        parabolic_affine_sub_nhds (I := I) (G := G) T X F a b t x huniq
          (hF_time t ht htpos x)
          (Filter.Eventually.of_forall (hF_space t ht htpos)) (hF_grad t ht htpos x)
    rw [hident]
    have := hsub t ht htpos x
    linarith
  have hw_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
    DifferentialGeometry.Analysis.Parabolic.strict_barrier_positive_region (I := I) G T X w
      hw_cont hw0 hw_time hw_mdiff hw_grad hnegative
  intro t ht x
  have := hw_nonneg t ht x
  simp only [w] at this
  linarith

end

end DifferentialGeometry.Analysis.Parabolic

import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem heat_pot_comparison_with_drift
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (X : Real → (x : M) → TangentSpace I x)
    (V u v : Real → M → Real) (C : Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hv_cont : ContinuousOn (fun p : Real × M => v p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hv_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => v s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hv_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (v t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (u t) y) x)
    (hv_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (v t) y) x)
    (hu_sub : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      parabolicOperatorWithDrift (I := I) G T X u t x - V t x * u t x ≤ 0)
    (hv_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X v t x - V t x * v t x)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, V t x ≤ C)
    (hinit : ∀ x : M, u 0 x ≤ v 0 x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x ≤ v t x := by
  let w : Real → M → Real := fun t x => v t x - u t x
  have hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (spacetimeSlab (M := M) T) :=
    hv_cont.sub hu_cont
  have hw0 : ∀ x : M, 0 ≤ w 0 x := fun x => sub_nonneg.mpr (hinit x)
  have hw_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => w s x) (Set.Icc 0 T) t :=
    fun t ht htpos x => (hv_time t ht htpos x).sub (hu_time t ht htpos x)
  have hw_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (w t) x :=
    fun t ht htpos x => (hv_mdiff t ht htpos x).sub (hu_mdiff t ht htpos x)
  have hw_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (w t) y) x := by
    intro t ht htpos x
    have heq : (T% fun y : M => gradientFun (I := I) (G.metric t) (w t) y) =
        (T% fun y : M =>
          gradientFun (I := I) (G.metric t) (v t) y -
            gradientFun (I := I) (G.metric t) (u t) y) := by
      funext y
      apply congrArg (fun q =>
        (⟨y, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      exact gradientFun_sub (I := I) (G.metric t)
        (hv_mdiff t ht htpos y) (hu_mdiff t ht htpos y)
    rw [heq]
    exact mdifferentiableAt_sub_section
      (hv_grad t ht htpos x) (hu_grad t ht htpos x)
  have hPw : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      V t x * w t x ≤ parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht htpos x
    have hsub := parabolic_sub (I := I) G T X v u t x
      (hv_time t ht htpos x) (hu_time t ht htpos x)
      (fun y => hv_mdiff t ht htpos y) (fun y => hu_mdiff t ht htpos y)
      (hv_grad t ht htpos x) (hu_grad t ht htpos x)
    have h1 : V t x * v t x ≤ parabolicOperatorWithDrift (I := I) G T X v t x := by
      linarith [hv_super t ht htpos x]
    have h2 : parabolicOperatorWithDrift (I := I) G T X u t x ≤ V t x * u t x := by
      linarith [hu_sub t ht htpos x]
    have hkey : V t x * w t x = V t x * v t x - V t x * u t x := by
      dsimp only [w]
      ring
    rw [hsub]
    linarith
  let z : Real → M → Real := fun s y => Real.exp (-C * s) * w s y
  have hz_eq : ∀ t : Real, z t = Real.exp (-C * t) • w t := by
    intro t
    funext y
    simp only [z, Pi.smul_apply, smul_eq_mul]
  have hz_cont : ContinuousOn (fun p : Real × M => z p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    have hscale : ContinuousOn (fun p : Real × M => Real.exp (-C * p.1))
        (spacetimeSlab (M := M) T) :=
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_fst)).continuousOn
    exact hscale.mul hw_cont
  have hz0 : ∀ x : M, 0 ≤ z 0 x := by
    intro x
    simpa [z] using hw0 x
  have hz_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => z s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    have hscale : DifferentiableWithinAt Real
        (fun s : Real => Real.exp (-C * s)) (Set.Icc 0 T) t :=
      (((differentiableAt_const (-C)).mul differentiableAt_id).exp
        (x := t)).differentiableWithinAt
    have hEv : (fun s : Real => z s x) =ᶠ[𝓝[Set.Icc 0 T] t]
        ((fun s : Real => Real.exp (-C * s)) * fun s : Real => w s x) :=
      Filter.EventuallyEq.of_eq (by
        funext s
        simp only [z, Pi.mul_apply])
    exact (Filter.EventuallyEq.differentiableWithinAt_iff hEv
      (by simp only [z, Pi.mul_apply])).mpr
        (hscale.mul (hw_time t ht htpos x))
  have hz_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (z t) x := by
    intro t ht htpos x
    have hEv : (z t) =ᶠ[𝓝 x]
        (fun y : M => Real.exp (-C * t) • w t y) :=
      Filter.EventuallyEq.of_eq (by
        funext y
        simp only [z, smul_eq_mul])
    exact hEv.mdifferentiableAt_iff.mpr
      ((hw_mdiff t ht htpos x).const_smul (Real.exp (-C * t)))
  have hz_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (z t) y) x := by
    intro t ht htpos x
    have hgrad_eq : (fun y : M =>
          gradientFun (I := I) (G.metric t) (z t) y) =
        (fun y : M => Real.exp (-C * t) •
          gradientFun (I := I) (G.metric t) (w t) y) := by
      funext y
      rw [hz_eq t, gradientFun_const_smul (I := I) (G.metric t)
        (Real.exp (-C * t)) (hw_mdiff t ht htpos y)]
    have hsec : (T% fun y : M => gradientFun (I := I) (G.metric t) (z t) y) =
        (T% fun y : M => Real.exp (-C * t) •
          gradientFun (I := I) (G.metric t) (w t) y) := by
      funext y
      apply congrArg (fun q =>
        (⟨y, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      exact congrFun hgrad_eq y
    rw [hsec]
    exact (hw_grad t ht htpos x).smul_const_section (a := Real.exp (-C * t))
  have hz_neg : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M, z t x < 0 →
      0 ≤ parabolicOperatorWithDrift (I := I) G T X z t x := by
    intro t ht htpos x hzneg
    have hTpos : 0 < T := lt_of_lt_of_le htpos ht.2
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
      (uniqueDiffOn_Icc hTpos).uniqueDiffWithinAt ht
    have hscale : DifferentiableWithinAt Real
        (fun s : Real => Real.exp (-C * s)) (Set.Icc 0 T) t :=
      (((differentiableAt_const (-C)).mul differentiableAt_id).exp
        (x := t)).differentiableWithinAt
    have hw_neg : w t x < 0 := by
      have hz' := hzneg
      rw [hz_eq t, Pi.smul_apply, smul_eq_mul] at hz'
      have h : Real.exp (-C * t) * w t x < Real.exp (-C * t) * 0 := by
        simpa using hz'
      exact lt_of_mul_lt_mul_left h (Real.exp_pos (-C * t)).le
    have hPw' : C * w t x ≤ parabolicOperatorWithDrift (I := I) G T X w t x := by
      have hle := hPw t ht htpos x
      have hVC : V t x - C ≤ 0 := sub_nonpos.mpr (hV t ht x)
      have hkey : V t x * w t x - C * w t x = (V t x - C) * w t x := by ring
      have hnonneg : 0 ≤ V t x * w t x - C * w t x := by
        rw [hkey]
        exact mul_nonneg_of_nonpos_of_nonpos hVC hw_neg.le
      linarith
    have hrescale := parabolic_exp_rescale_identity (I := I) G T C X w t huniq
      (fun y => hw_mdiff t ht htpos y) x (hw_grad t ht htpos x)
      (hw_time t ht htpos x) hscale
    change 0 ≤ parabolicOperatorWithDrift (I := I) G T X
      (fun s y => Real.exp (-C * s) * w s y) t x
    rw [hrescale]
    exact mul_nonneg (Real.exp_pos (-C * t)).le (sub_nonneg.mpr hPw')
  have hz_nonneg := strict_barrier_positive_region (I := I) G T X z
    hz_cont hz0 hz_time hz_mdiff hz_grad hz_neg
  intro t ht x
  have h := hz_nonneg t ht x
  rw [hz_eq t, Pi.smul_apply, smul_eq_mul] at h
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (Real.exp_pos (-C * t))).mp h)

theorem heat_pot_subsolution_nonpos_with_drift
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (X : Real → (x : M) → TangentSpace I x)
    (V u : Real → M → Real) (C : Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_sub : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      parabolicOperatorWithDrift (I := I) G T X u t x - V t x * u t x ≤ 0)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, V t x ≤ C)
    (hinit : ∀ x : M, u 0 x ≤ 0) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x ≤ 0 := by
  have hcmp := heat_pot_comparison_with_drift (I := I) G X V u
    (fun _ _ => (0 : Real)) C hu_cont continuousOn_const hu_time
    (fun _ _ _ _ => differentiableWithinAt_const 0) hu_mdiff
    (fun t ht htpos x => mdifferentiableAt_const) hu_grad
    (fun t ht htpos x =>
      gradientFun_mdiffAt (I := I) (G.metric t) contMDiff_const x)
    hu_sub
    (fun t ht htpos x => by
      rw [parabolic_const (I := I) (G := G) T X 0 t x]
      simp)
    hV hinit
  intro t ht x
  simpa using hcmp t ht x

theorem heatOperatorWithDrift_const
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (t : Real) (X : (x : M) → TangentSpace I x) (a : Real) (x : M) :
    heatOperatorWithDrift (I := I) G t X (fun _ : M => a) x = 0 := by
  have hlap : laplacianAt (I := I) G t (fun _ : M => a) x = 0 := by
    unfold laplacianAt
    exact DifferentialGeometry.Geometry.Operator.laplacian_const
      (G.connection t) (G.metric t) a x
  have hdrift : driftTerm (I := I) G t X (fun _ : M => a) x = 0 := by
    unfold driftTerm gradientAt
    rw [gradientFun_const]
    simp
  unfold heatOperatorWithDrift
  rw [hlap, hdrift, add_zero]

theorem heat_pot_comparison_with_drift_const
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T c d : Real} (X : Real → (x : M) → TangentSpace I x) (hcd : c ≤ d) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      (fun (_ : Real) (_ : M) => c) t x ≤ (fun (_ : Real) (_ : M) => d) t x := by
  have hcmp := heat_pot_comparison_with_drift (I := I) G X (fun _ _ => (0 : Real))
    (fun _ _ => c) (fun _ _ => d) 0 continuousOn_const continuousOn_const
    (fun _ _ _ _ => differentiableWithinAt_const c)
    (fun _ _ _ _ => differentiableWithinAt_const d)
    (fun _ _ _ _ => mdifferentiableAt_const) (fun _ _ _ _ => mdifferentiableAt_const)
    (fun t _ _ x => gradientFun_mdiffAt (I := I) (G.metric t) contMDiff_const x)
    (fun t _ _ x => gradientFun_mdiffAt (I := I) (G.metric t) contMDiff_const x)
    (fun t _ _ x => by
      rw [parabolic_const (I := I) (G := G) T X c t x]
      simp)
    (fun t _ _ x => by
      rw [parabolic_const (I := I) (G := G) T X d t x]
      simp)
    (fun _ _ _ => le_rfl) (fun _ => hcd)
  intro t ht x
  simpa using hcmp t ht x

theorem exists_heat_pot_subsolution_with_drift_of_initial_positive
    [VectorBundle Real E (TangentSpace I : M → Type _)] [Nonempty M]
    (G : MetricConnectionFamily (I := I) (M := M) Real) {T : Real} (hT : 0 ≤ T) :
    ∃ (X : Real → (x : M) → TangentSpace I x) (V u : Real → M → Real),
      (∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
        parabolicOperatorWithDrift (I := I) G T X u t x - V t x * u t x ≤ 0) ∧
      (∀ t ∈ Set.Icc 0 T, ∀ x : M, V t x ≤ 0) ∧
      (0 : Real) ∈ Set.Icc 0 T ∧
      (∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 < u t x) := by
  refine ⟨fun _ x => 0, fun _ _ => 0, fun _ _ => 1, ?_, fun _ _ _ => le_rfl,
    ⟨le_rfl, hT⟩, fun _ _ _ => zero_lt_one⟩
  intro t _ _ x
  rw [parabolic_const (I := I) (G := G) T (fun _ x => 0) 1 t x]
  simp

theorem exists_heat_pot_subsolution_with_drift_of_unbounded_potential
    [VectorBundle Real E (TangentSpace I : M → Type _)] [Nonempty M]
    (G : MetricConnectionFamily (I := I) (M := M) Real) :
    ∃ (X : Real → (x : M) → TangentSpace I x) (V u : Real → M → Real),
      (∀ t ∈ Set.Icc 0 1, 0 < t → ∀ x : M,
        parabolicOperatorWithDrift (I := I) G 1 X u t x - V t x * u t x ≤ 0) ∧
      (∀ x : M, u 0 x ≤ 0) ∧
      (∀ C : Real, ∃ t ∈ Set.Icc 0 1, ∃ x : M, C < V t x) ∧
      (∀ x : M, 0 < u 1 x) := by
  classical
  refine ⟨fun _ x => 0, fun t _ => if t = 0 then 0 else t⁻¹, fun t _ => t, ?_, ?_, ?_, ?_⟩
  · intro t ht htpos x
    have htne : t ≠ 0 := ne_of_gt htpos
    have hderiv : derivWithin (fun s : Real => s) (Set.Icc 0 1) t = 1 :=
      derivWithin_id' (𝕜 := Real) (s := Set.Icc 0 1) (x := t)
        ((uniqueDiffOn_Icc zero_lt_one).uniqueDiffWithinAt ht)
    have hheat : heatOperatorWithDrift (I := I) G t
        ((fun _ x => (0 : TangentSpace I x)) t) (fun _ : M => t) x = 0 :=
      heatOperatorWithDrift_const (I := I) G t _ t x
    have hP : parabolicOperatorWithDrift (I := I) G 1
        (fun _ x => (0 : TangentSpace I x)) (fun s _ => s) t x = 1 := by
      simp only [parabolicOperatorWithDrift, hheat, hderiv, sub_zero]
    have hV : (if t = 0 then (0 : Real) else t⁻¹) * t = 1 := by
      rw [if_neg htne, inv_mul_cancel₀ htne]
    rw [hP, hV]
    norm_num
  · intro x
    norm_num
  · intro C
    have hone : (1 : Real) ≤ max C 0 + 1 := by
      linarith [le_max_right C 0]
    have hC : C < max C 0 + 1 :=
      lt_of_le_of_lt (le_max_left C 0) (lt_add_one _)
    have hpos : (0 : Real) < max C 0 + 1 := lt_of_lt_of_le zero_lt_one hone
    have hne : (max C 0 + 1)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hpos)
    exact ⟨(max C 0 + 1)⁻¹, ⟨(inv_pos.mpr hpos).le, inv_le_one_of_one_le₀ hone⟩,
      Classical.choice inferInstance, by
        change C < (if (max C 0 + 1)⁻¹ = 0 then (0 : Real)
          else ((max C 0 + 1)⁻¹)⁻¹)
        rw [if_neg hne, inv_inv]
        exact hC⟩
  · intro x
    norm_num

end

end DifferentialGeometry.Analysis.Parabolic

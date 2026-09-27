import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Hopf.ManifoldBoundary
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Strong

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem scalar_heat_positive_of_initial_point
    [I.Boundaryless]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        ΔG (I := I) g ⟨u t, hu_space t ht htpos⟩ x)
    {c : M} (hc : 0 < u 0 c) :
    ∀ y : M, 0 < u T y := by
  let τ : Real := T / 2
  have hτ : 0 < τ := by
    dsimp [τ]
    linarith
  have hτT : τ ≤ T := by
    dsimp [τ]
    linarith
  have hτmem : τ ∈ Set.Icc (0 : Real) T := ⟨hτ.le, hτT⟩
  have hu_contτ : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) τ) := by
    apply hu_cont.mono
    intro p hp
    rw [spacetimeSlab] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hτT⟩, hp.2⟩
  have hu_nonnegτ : ∀ t ∈ Set.Icc 0 τ, ∀ x : M, 0 ≤ u t x := by
    intro t ht x
    exact hu_nonneg t ⟨ht.1, ht.2.trans hτT⟩ x
  have hu_timeτ : ∀ t ∈ Set.Icc 0 τ, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 τ) t := by
    intro t ht htpos x
    exact (hu_time t ⟨ht.1, ht.2.trans hτT⟩ htpos x).mono
      (Set.Icc_subset_Icc_right hτT)
  have hu_spaceτ : ∀ t ∈ Set.Icc 0 τ, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t) := by
    intro t ht htpos
    exact hu_space t ⟨ht.1, ht.2.trans hτT⟩ htpos
  have hu_superτ : ∀ (t : Real) (ht : t ∈ Set.Icc 0 τ) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 τ) t -
        ΔG (I := I) g ⟨u t, hu_spaceτ t ht htpos⟩ x := by
    intro t ht htpos x
    have htT : t ∈ Set.Icc (0 : Real) T := ⟨ht.1, ht.2.trans hτT⟩
    have hderiv : derivWithin (fun s => u s x) (Set.Icc 0 τ) t =
        derivWithin (fun s => u s x) (Set.Icc 0 T) t := by
      exact derivWithin_subset (Set.Icc_subset_Icc le_rfl hτT)
        ((uniqueDiffOn_Icc hτ).uniqueDiffWithinAt ht)
        (hu_time t htT htpos x)
    rw [hderiv]
    simpa using hu_super t htT htpos x
  have hτzero : ∃ x : M, 0 < u τ x := by
    by_contra hnot
    have hzero : ∀ x : M, u τ x = 0 := by
      intro x
      have hle : u τ x ≤ 0 := le_of_not_gt (fun hx => hnot ⟨x, hx⟩)
      exact le_antisymm hle (hu_nonnegτ τ ⟨hτ.le, le_rfl⟩ x)
    have hpast := scalar_strong_maximum_principle_fixed_metric (I := I)
      g hτ u hu_contτ hu_nonnegτ hu_timeτ hu_spaceτ hu_superτ
      (y := c) (hzero c)
    have hczero : u 0 c = 0 := hpast 0 ⟨le_rfl, hτ.le⟩ c
    linarith
  obtain ⟨xτ, hxτ⟩ := hτzero
  intro y
  exact scalar_strong_maximum_principle_fixed_metric_positive (I := I)
    g hT u hu_cont hu_nonneg hu_time hu_space hu_super hτmem hxτ y

section Dirichlet

theorem scalar_dirichlet_solution_nonnegative
    [CompactSpace M]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real → (x : M) → TangentSpace I x)
    (a : Real) (ha : 0 ≤ a)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_initial : ∀ x : M, 0 ≤ u 0 x)
    (hu_boundary : ∀ t ∈ Set.Icc 0 T, ∀ p : BoundaryManifold I M,
      u t (p : M) = 0)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_equation : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      parabolicOperatorWithDrift (I := I) G T X u t x = -a * u t x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x := by
  apply strict_barrier_on_compact_manifold_with_boundary
    (I := I) G T X u hu_cont hu_initial
  · intro t ht p
    rw [hu_boundary t ht p]
  · exact hu_time
  · exact hu_mdiff
  · exact hu_grad
  · intro t ht htpos x hx hneg
    rw [hu_equation t ht htpos x hx]
    simpa only [mul_neg, neg_mul] using
      mul_nonneg ha (neg_nonneg.mpr hneg.le)

theorem scalar_dirichlet_solution_lower_bound_of_spatial_barrier
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (a : Real) (ha : 0 ≤ a)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_boundary : ∀ t ∈ Set.Icc 0 T, ∀ p : BoundaryManifold I M,
      u t (p : M) = 0)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_equation : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      parabolicOperatorWithDrift (I := I) G T X u t x = -a * u t x)
    (b : M → Real) (hb : ContMDiff I 𝓘(Real, Real) ∞ b)
    (hb_initial : ∀ x : M, b x ≤ u 0 x)
    (hb_boundary : ∀ p : BoundaryManifold I M, b (p : M) ≤ 0)
    (C : Real)
    (hb_heat : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ I.interior M, 0 < b x →
      -C * b x ≤ heatOperatorWithDrift (I := I) G t (X t) b x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      Real.exp (-(a + C) * t) * b x ≤ u t x := by
  let v : Real → M → Real := fun t x => Real.exp (-(a + C) * t) * b x
  let w : Real → M → Real := fun t x => u t x - v t x
  have hv_cont : ContinuousOn (fun p : Real × M => v p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    have hexp : Continuous (fun p : Real × M => Real.exp (-(a + C) * p.1)) := by
      fun_prop
    have hbcomp : Continuous (fun p : Real × M => b p.2) :=
      hb.continuous.comp continuous_snd
    change ContinuousOn
      ((fun p : Real × M => Real.exp (-(a + C) * p.1)) * fun p => b p.2)
        (spacetimeSlab (M := M) T)
    exact (hexp.mul hbcomp).continuousOn
  have hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (spacetimeSlab (M := M) T) := hu_cont.sub hv_cont
  have hw0 : ∀ x : M, 0 ≤ w 0 x := by
    intro x
    simpa [w, v] using sub_nonneg.mpr (hb_initial x)
  have hw_boundary : ∀ t ∈ Set.Icc 0 T, ∀ p : BoundaryManifold I M,
      0 ≤ w t (p : M) := by
    intro t ht p
    change 0 ≤ u t (p : M) - Real.exp (-(a + C) * t) * b (p : M)
    rw [hu_boundary t ht p, zero_sub]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
      (Real.exp_pos _).le (hb_boundary p))
  have hv_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => v s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    exact (by fun_prop : DifferentiableAt Real (fun s => v s x) t).differentiableWithinAt
  have hv_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (v t) x := by
    intro t ht htpos x
    exact (contMDiff_const.mul hb).mdifferentiable (by simp) x
  have hv_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (v t) y) x := by
    intro t ht htpos x
    exact gradientFun_mdiffAt (I := I) (G.metric t) (contMDiff_const.mul hb) x
  have hv_operator : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      0 < b x →
        parabolicOperatorWithDrift (I := I) G T X v t x ≤ -a * v t x := by
    intro t ht htpos x hx hbx
    let btime : Real → M → Real := fun _ y => b y
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
      (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
    have hbtime_time : DifferentiableWithinAt Real
        (fun s => btime s x) (Set.Icc 0 T) t := differentiableWithinAt_const _
    have hbtime_space : ∀ y : M,
        MDifferentiableAt I 𝓘(Real, Real) (btime t) y := by
      intro y
      exact hb.mdifferentiable (by simp) y
    have hbtime_grad : MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (btime t) y) x :=
      gradientFun_mdiffAt (I := I) (G.metric t) hb x
    have hscale : DifferentiableWithinAt Real
        (fun s => Real.exp (-(a + C) * s)) (Set.Icc 0 T) t := by
      fun_prop
    have hbase : parabolicOperatorWithDrift (I := I) G T X btime t x =
        -heatOperatorWithDrift (I := I) G t (X t) b x := by
      unfold parabolicOperatorWithDrift
      have hderiv : derivWithin (fun _s : Real => b x) (Set.Icc 0 T) t = 0 :=
        (hasDerivWithinAt_const (x := t) (s := Set.Icc 0 T) (c := b x)).derivWithin huniq
      rw [hderiv, zero_sub]
    have hrescale := parabolic_exp_rescale_identity (I := I)
      G T (a + C) X btime t huniq hbtime_space x hbtime_grad hbtime_time hscale
    change parabolicOperatorWithDrift (I := I) G T X v t x ≤ -a * v t x
    change parabolicOperatorWithDrift (I := I) G T X
        (fun s y => Real.exp (-(a + C) * s) * btime s y) t x ≤
      -a * (Real.exp (-(a + C) * t) * b x)
    rw [hrescale, hbase]
    have hheat := hb_heat t ht x hx hbx
    nlinarith [Real.exp_pos (-(a + C) * t)]
  have hw_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      DifferentiableWithinAt Real (fun s => w s x) (Set.Icc 0 T) t := by
    intro t ht htpos x hx
    exact (hu_time t ht htpos x hx).sub (hv_time t ht htpos x)
  have hw_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDifferentiableAt I 𝓘(Real, Real) (w t) x := by
    intro t ht htpos x hx
    exact (hu_mdiff t ht htpos x hx).sub (hv_mdiff t ht htpos x)
  have hw_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x := by
    intro t ht htpos x hx
    have hgrad_eq :
        (fun y : M => gradientFun (I := I) (G.metric t) (w t) y) =ᶠ[nhds x]
          fun y : M => gradientFun (I := I) (G.metric t) (u t) y -
            gradientFun (I := I) (G.metric t) (v t) y := by
      filter_upwards [
        (I.isOpen_interior (M := M) (n := ∞) (by simp)).mem_nhds hx] with y hy
      exact gradientFun_sub (I := I) (G.metric t)
        (hu_mdiff t ht htpos y hy) (hv_mdiff t ht htpos y)
    have hgrad_total :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (w t) y) =ᶠ[nhds x]
          (T% fun y : M => gradientFun (I := I) (G.metric t) (u t) y -
            gradientFun (I := I) (G.metric t) (v t) y) := by
      filter_upwards [hgrad_eq] with y hy
      rw [hy]
    exact (mdifferentiableAt_sub_section
      (hu_grad t ht htpos x hx) (hv_grad t ht htpos x)).congr_of_eventuallyEq hgrad_total
  have hnegative : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      w t x < 0 → 0 ≤ parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht htpos x hx hwneg
    have hu_space : ∀ᶠ y in nhds x,
        MDifferentiableAt I 𝓘(Real, Real) (u t) y := by
      filter_upwards [
        (I.isOpen_interior (M := M) (n := ∞) (by simp)).mem_nhds hx] with y hy
      exact hu_mdiff t ht htpos y hy
    have hv_space : ∀ᶠ y in nhds x,
        MDifferentiableAt I 𝓘(Real, Real) (v t) y :=
      Filter.Eventually.of_forall (hv_mdiff t ht htpos)
    have hsub := parabolic_sub_nhds (I := I) (G := G) T X u v t x
      (hu_time t ht htpos x hx) (hv_time t ht htpos x)
      hu_space hv_space (hu_grad t ht htpos x hx) (hv_grad t ht htpos x)
    change parabolicOperatorWithDrift (I := I) G T X w t x = _ at hsub
    rw [hsub, hu_equation t ht htpos x hx]
    have hbx : 0 < b x := by
      have hu0 := hu_nonneg t ht x
      change u t x - Real.exp (-(a + C) * t) * b x < 0 at hwneg
      by_contra hnot
      have hb0 : b x ≤ 0 := le_of_not_gt hnot
      have hscaled : Real.exp (-(a + C) * t) * b x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hb0
      linarith
    have hvP := hv_operator t ht htpos x hx hbx
    have hnonneg : 0 ≤ -a * w t x :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr ha) hwneg.le
    change 0 ≤ -a * (u t x - v t x) at hnonneg
    linarith
  have hw_nonneg := strict_barrier_on_compact_manifold_with_boundary
    (I := I) G T X w hw_cont hw0 hw_boundary hw_time hw_mdiff hw_grad hnegative
  intro t ht x
  have h := hw_nonneg t ht x
  change 0 ≤ u t x - Real.exp (-(a + C) * t) * b x at h
  exact sub_nonneg.mp h

private theorem parabolic_exp_rescale_identity_at
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T L : Real) (X : Real → (x : M) → TangentSpace I x)
    (v : Real → M → Real) (t : Real) {x : M}
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t)
    (hv_space : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) (v t) y)
    (hv_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (v t) y) x)
    (hv_time : DifferentiableWithinAt Real (fun s => v s x)
      (Set.Icc 0 T) t)
    (hscale : DifferentiableWithinAt Real
      (fun s : Real => Real.exp (-L * s)) (Set.Icc 0 T) t) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => Real.exp (-L * s) * v s y) t x =
      Real.exp (-L * t) *
        (parabolicOperatorWithDrift (I := I) G T X v t x - L * v t x) := by
  have hlinear_diff : DifferentiableWithinAt Real
      (fun s : Real => -L * s) (Set.Icc 0 T) t := by
    simpa using
      (differentiableWithinAt_fun_id (𝕜 := Real)
        (s := Set.Icc 0 T) (x := t)).const_mul (-L)
  have hlinear_deriv :
      derivWithin (fun s : Real => -L * s) (Set.Icc 0 T) t = -L := by
    have hid : derivWithin (fun s : Real => s) (Set.Icc 0 T) t = 1 :=
      derivWithin_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t) huniq
    rw [derivWithin_const_mul (-L)
      (d := fun s : Real => s) (s := Set.Icc 0 T) (x := t)
      differentiableWithinAt_id, hid]
    ring
  have hscale_deriv :
      derivWithin (fun s : Real => Real.exp (-L * s)) (Set.Icc 0 T) t =
        -L * Real.exp (-L * t) := by
    rw [derivWithin_exp hlinear_diff huniq, hlinear_deriv]
    ring
  have htime :
      derivWithin (fun s : Real => Real.exp (-L * s) * v s x)
          (Set.Icc 0 T) t =
        (-L * Real.exp (-L * t)) * v t x +
          Real.exp (-L * t) *
            derivWithin (fun s : Real => v s x) (Set.Icc 0 T) t := by
    rw [derivWithin_fun_mul hscale hv_time, hscale_deriv]
  have hheat :
      heatOperatorWithDrift (I := I) G t (X t)
          (fun y : M => Real.exp (-L * t) * v t y) x =
        Real.exp (-L * t) *
          heatOperatorWithDrift (I := I) G t (X t) (v t) x := by
    have hlap := laplacian_smul_at (I := I) (G.connection t) (G.metric t)
      (Real.exp (-L * t)) hv_space hv_grad
    change laplacian (I := I) (G.connection t) (G.metric t)
        (fun y : M => Real.exp (-L * t) * v t y) x =
      Real.exp (-L * t) *
        laplacian (I := I) (G.connection t) (G.metric t) (v t) x at hlap
    have hdrift := driftTerm_const_smul (I := I) G t (X t)
      (Real.exp (-L * t)) hv_space.self_of_nhds
    change driftTerm (I := I) G t (X t)
        (fun y : M => Real.exp (-L * t) * v t y) x =
      Real.exp (-L * t) * driftTerm (I := I) G t (X t) (v t) x at hdrift
    unfold heatOperatorWithDrift laplacianAt
    rw [hlap, hdrift]
    ring
  unfold parabolicOperatorWithDrift
  rw [htime, hheat]
  ring

private theorem scalar_dirichlet_solution_positive_at_terminal_time_of_positive_point
    [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hheat_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (a : Real) (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_equation : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      parabolicOperatorWithDrift (I := I) G T X u t x = -a * u t x)
    (hinterior_conn : IsPreconnected (I.interior M))
    {c : M} (hcint : c ∈ I.interior M) (hc : 0 < u T c)
    (y : M) (hyint : y ∈ I.interior M) :
    0 < u T y := by
  let z : Real → M → Real := fun t x => Real.exp (-(-a) * t) * u t x
  have hz_cont : ContinuousOn (fun p : Real × M => z p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_fst)).continuousOn.mul hu_cont
  have hz_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ z t x := by
    intro t ht x
    exact mul_nonneg (Real.exp_pos _).le (hu_nonneg t ht x)
  have hz_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      DifferentiableWithinAt Real (fun s => z s x) (Set.Icc 0 T) t := by
    intro t ht htpos x hx
    have hscale : DifferentiableWithinAt Real
        (fun s : Real => Real.exp (-(-a) * s)) (Set.Icc 0 T) t :=
      (((differentiableAt_const (-(-a))).mul differentiableAt_id).exp
        (x := t)).differentiableWithinAt
    exact hscale.mul (hu_time t ht htpos x hx)
  have hz_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDifferentiableAt I 𝓘(Real, Real) (z t) x := by
    intro t ht htpos x hx
    exact (hu_mdiff t ht htpos x hx).const_smul (Real.exp (-(-a) * t))
  have hz_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (z t) y) x := by
    intro t ht htpos x hx
    have hu_space : ∀ᶠ y in nhds x,
        MDifferentiableAt I 𝓘(Real, Real) (u t) y := by
      filter_upwards [
        (I.isOpen_interior (M := M) (n := ∞) (by simp)).mem_nhds hx] with y hy
      exact hu_mdiff t ht htpos y hy
    have hgrad_eq :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (z t) y) =ᶠ[nhds x]
          (T% fun y : M => Real.exp (-(-a) * t) •
            gradientFun (I := I) (G.metric t) (u t) y) := by
      filter_upwards [hu_space] with y hy
      apply congrArg (fun q =>
        (⟨y, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      change gradientFun (I := I) (G.metric t)
        (Real.exp (-(-a) * t) • u t) y = _
      exact gradientFun_const_smul (I := I) (G.metric t)
        (Real.exp (-(-a) * t)) hy
    exact (mdifferentiableAt_const.smul_section
      (hu_grad t ht htpos x hx)).congr_of_eventuallyEq hgrad_eq
  have hz_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X z t x := by
    intro t ht htpos x hx
    have hu_space : ∀ᶠ y in nhds x,
        MDifferentiableAt I 𝓘(Real, Real) (u t) y := by
      filter_upwards [
        (I.isOpen_interior (M := M) (n := ∞) (by simp)).mem_nhds hx] with y hy
      exact hu_mdiff t ht htpos y hy
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
      (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
    have hscale : DifferentiableWithinAt Real
        (fun s : Real => Real.exp (-(-a) * s)) (Set.Icc 0 T) t :=
      (((differentiableAt_const (-(-a))).mul differentiableAt_id).exp
        (x := t)).differentiableWithinAt
    have hrescale :
        parabolicOperatorWithDrift (I := I) G T X z t x =
          Real.exp (-(-a) * t) *
            (parabolicOperatorWithDrift (I := I) G T X u t x - (-a) * u t x) := by
      simpa only [z] using parabolic_exp_rescale_identity_at (I := I)
        G T (-a) X u t huniq hu_space (hu_grad t ht htpos x hx)
          (hu_time t ht htpos x hx) hscale
    rw [hrescale, hu_equation t ht htpos x hx]
    ring_nf
    exact le_rfl
  have hzc : 0 < z T c := mul_pos (Real.exp_pos _) hc
  have hzy :=
    scalar_strong_maximum_principle_time_dependent_metric_with_drift_spatial_interior_region
      (I := I) G hT X hgrad_cont hheat_cont z (I.interior M)
      (I.isOpen_interior (M := M) (n := ∞) (by simp)) (fun _ h => h)
      hinterior_conn hz_cont hz_nonneg hz_time hz_mdiff hz_grad hz_super
      hcint hzc y hyint
  change 0 < Real.exp (-(-a) * T) * u T y at hzy
  rcases mul_pos_iff.mp hzy with h | h
  · exact h.2
  · exact (not_lt_of_ge (Real.exp_pos _).le h.1).elim

private theorem scalar_dirichlet_solution_positive_at_terminal_time_of_initial_point
    [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hheat_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (a : Real) (ha : 0 ≤ a)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_initial : ∀ x : M, 0 ≤ u 0 x)
    (hu_boundary : ∀ t ∈ Set.Icc 0 T, ∀ p : BoundaryManifold I M,
      u t (p : M) = 0)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_equation : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      parabolicOperatorWithDrift (I := I) G T X u t x = -a * u t x)
    (hinterior_conn : IsPreconnected (I.interior M))
    {c : M} (hcint : c ∈ I.interior M) (hc : 0 < u 0 c)
    (y : M) (hyint : y ∈ I.interior M) :
    0 < u T y := by
  have hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x :=
    scalar_dirichlet_solution_nonnegative (I := I) G T X a ha u hu_cont
      hu_initial hu_boundary hu_time hu_mdiff hu_grad hu_equation
  have hu0_cont : Continuous (u 0) := by
    rw [← continuousOn_univ]
    have hmap : Set.MapsTo (fun x : M => (0, x)) Set.univ
        (spacetimeSlab (M := M) T) := by
      intro x hx
      exact ⟨⟨le_rfl, hT.le⟩, Set.mem_univ x⟩
    change ContinuousOn
      ((fun p : Real × M => u p.1 p.2) ∘ fun x : M => (0, x)) Set.univ
    exact hu_cont.comp (by fun_prop) hmap
  let epsilon : Real := u 0 c / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  let V : Set M := {x : M | epsilon < u 0 x} ∩ I.interior M
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_const hu0_cont).inter
      (I.isOpen_interior (M := M) (n := ∞) (by simp))
  have hV : V ∈ nhds c := by
    apply hVopen.mem_nhds
    exact ⟨by dsimp [epsilon]; linarith, hcint⟩
  obtain ⟨b, C, hb, hbc, hb_lt, hb_pos_mem, -, hb_heat⟩ :=
    exists_spatial_barrier_positive_at (I := I) G hT X hgrad_cont hheat_cont
      hV hepsilon
  have hb_initial : ∀ x : M, b x ≤ u 0 x := by
    intro x
    by_cases hbx : 0 < b x
    · have hxV := hb_pos_mem x hbx
      have hblt := hb_lt x
      exact hblt.le.trans hxV.1.le
    · exact (le_of_not_gt hbx).trans (hu_initial x)
  have hb_boundary : ∀ p : BoundaryManifold I M, b (p : M) ≤ 0 := by
    intro p
    by_contra hnot
    have hbp : 0 < b (p : M) := lt_of_not_ge hnot
    have hpV := hb_pos_mem (p : M) hbp
    exact (Set.disjoint_left.1 I.disjoint_interior_boundary) hpV.2 p.2
  have hlower := scalar_dirichlet_solution_lower_bound_of_spatial_barrier
    (I := I) G hT X a ha u hu_cont hu_nonneg hu_boundary hu_time hu_mdiff
      hu_grad hu_equation b hb hb_initial hb_boundary C
      (fun t ht x hx hbx => hb_heat t ht x hbx)
  have hcT : 0 < u T c := by
    exact (mul_pos (Real.exp_pos _) hbc).trans_le
      (hlower T ⟨hT.le, le_rfl⟩ c)
  exact scalar_dirichlet_solution_positive_at_terminal_time_of_positive_point
    (I := I) G hT X hgrad_cont hheat_cont a u hu_cont hu_nonneg hu_time
      hu_mdiff hu_grad hu_equation hinterior_conn hcint hcT y hyint

theorem scalar_dirichlet_solution_positive_of_initial_point
    [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real → (x : M) → TangentSpace I x)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hheat_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (a : Real) (ha : 0 ≤ a)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_initial : ∀ x : M, 0 ≤ u 0 x)
    (hu_boundary : ∀ t ∈ Set.Icc 0 T, ∀ p : BoundaryManifold I M,
      u t (p : M) = 0)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_equation : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      parabolicOperatorWithDrift (I := I) G T X u t x = -a * u t x)
    (hinterior_conn : IsPreconnected (I.interior M))
    {c : M} (hcint : c ∈ I.interior M) (hc : 0 < u 0 c) :
    ∀ t ∈ Set.Ioc 0 T, ∀ y ∈ I.interior M, 0 < u t y := by
  intro t ht y hyint
  have hsub : Set.Icc (0 : Real) t ⊆ Set.Icc 0 T :=
    Set.Icc_subset_Icc_right ht.2
  have hgrad_cont_t : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) t) := by
    intro rho hrho
    exact (hgrad_cont rho hrho).mono fun p hp =>
      ⟨hsub hp.1, hp.2⟩
  have hheat_cont_t : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) t) := by
    intro rho hrho
    exact (hheat_cont rho hrho).mono fun p hp =>
      ⟨hsub hp.1, hp.2⟩
  have hu_cont_t : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) t) :=
    hu_cont.mono fun p hp => ⟨hsub hp.1, hp.2⟩
  have hu_boundary_t : ∀ s ∈ Set.Icc 0 t, ∀ p : BoundaryManifold I M,
      u s (p : M) = 0 := by
    intro s hs p
    exact hu_boundary s (hsub hs) p
  have hu_time_t : ∀ s ∈ Set.Icc 0 t, 0 < s → ∀ x ∈ I.interior M,
      DifferentiableWithinAt Real (fun r => u r x) (Set.Icc 0 t) s := by
    intro s hs hspos x hx
    exact (hu_time s (hsub hs) hspos x hx).mono hsub
  have hu_mdiff_t : ∀ s ∈ Set.Icc 0 t, 0 < s → ∀ x ∈ I.interior M,
      MDifferentiableAt I 𝓘(Real, Real) (u s) x := by
    intro s hs hspos x hx
    exact hu_mdiff s (hsub hs) hspos x hx
  have hu_grad_t : ∀ s ∈ Set.Icc 0 t, 0 < s → ∀ x ∈ I.interior M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric s) (u s) y) x := by
    intro s hs hspos x hx
    exact hu_grad s (hsub hs) hspos x hx
  have hu_equation_t : ∀ s ∈ Set.Icc 0 t, 0 < s → ∀ x ∈ I.interior M,
      parabolicOperatorWithDrift (I := I) G t X u s x = -a * u s x := by
    intro s hs hspos x hx
    have hderiv : derivWithin (fun r => u r x) (Set.Icc 0 t) s =
        derivWithin (fun r => u r x) (Set.Icc 0 T) s :=
      derivWithin_subset hsub
        ((uniqueDiffOn_Icc ht.1).uniqueDiffWithinAt hs)
        (hu_time s (hsub hs) hspos x hx)
    unfold parabolicOperatorWithDrift
    rw [hderiv]
    exact hu_equation s (hsub hs) hspos x hx
  exact scalar_dirichlet_solution_positive_at_terminal_time_of_initial_point
    (I := I) G ht.1 X hgrad_cont_t hheat_cont_t a ha u hu_cont_t
      hu_initial hu_boundary_t hu_time_t hu_mdiff_t hu_grad_t hu_equation_t
      hinterior_conn hcint hc y hyint

def IsLocalScalarDirichletSolution
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real → (x : M) → TangentSpace I x)
    (s t c : Real) (Kset : Set M) (f₀ : M → Real) (f : Real → M → Real) : Prop :=
  ContinuousOn (fun p : Real × M ↦ f p.1 p.2) (Set.Icc s t ×ˢ Kset) ∧
    (∀ z ∈ Kset, f s z = f₀ z) ∧
    (∀ q ∈ Set.Icc s t, ∀ z ∈ frontier Kset, f q z = 0) ∧
    (∀ q ∈ Set.Ioc s t, ∀ z ∈ interior Kset, 0 < f q z) ∧
    (∀ q ∈ Set.Ioc s t, ∀ z ∈ interior Kset,
      DifferentiableAt Real (fun r ↦ f r z) q) ∧
    (∀ q ∈ Set.Ioc s t, ∀ z ∈ interior Kset,
      MDifferentiableAt I 𝓘(Real, Real) (f q) z) ∧
    (∀ q ∈ Set.Ioc s t, ∀ z ∈ interior Kset,
      MDiffAt (T% fun w : M ↦ gradientFun (I := I) (G.metric q) (f q) w) z) ∧
    ∀ q ∈ Set.Ioc s t, ∀ z ∈ interior Kset,
      parabolicOperatorWithDrift (I := I) G T X f q z = -c * f q z

theorem IsLocalScalarDirichletSolution.nonnegative
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {T s t c : Real} {X : Real → (x : M) → TangentSpace I x}
    {Kset : Set M} {f₀ : M → Real} {f : Real → M → Real}
    (h : IsLocalScalarDirichletSolution (I := I) G T X s t c Kset f₀ f)
    (hf₀ : ∀ x ∈ Kset, 0 ≤ f₀ x) :
    ∀ q ∈ Set.Icc s t, ∀ x ∈ Kset, 0 ≤ f q x := by
  intro q hq x hx
  by_cases hqs : q = s
  · subst q
    rw [h.2.1 x hx]
    exact hf₀ x hx
  · by_cases hxi : x ∈ interior Kset
    · exact (h.2.2.2.1 q ⟨lt_of_le_of_ne hq.1 (Ne.symm hqs), hq.2⟩ x hxi).le
    · have hxf : x ∈ frontier Kset := ⟨subset_closure hx, hxi⟩
      rw [h.2.2.1 q hq x hxf]

theorem IsLocalScalarDirichletSolution.nonnegative_of_closure_interior
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T s t c : Real}
    (X : Real → (x : M) → TangentSpace I x)
    (Kset : Set M) (f₀ : M → Real) (f : Real → M → Real)
    (h : IsLocalScalarDirichletSolution (I := I) G T X s t c Kset f₀ f)
    (hK : Kset ⊆ closure (interior Kset)) :
    ∀ q ∈ Set.Ioc s t, ∀ x ∈ Kset, 0 ≤ f q x := by
  intro q hq x hx
  have hqIcc : q ∈ Set.Icc s t := ⟨le_of_lt hq.1, hq.2⟩
  have hcont_sp : ContinuousWithinAt
      (fun p : Real × M => f p.1 p.2)
      (Set.Icc s t ×ˢ Kset) (q, x) :=
    h.1.continuousWithinAt ⟨hqIcc, hx⟩
  have hphi : ContinuousAt (fun y : M => (q, y)) x :=
    continuousAt_const.prodMk continuousAt_id
  have hmap : Set.MapsTo (fun y : M => (q, y)) (interior Kset)
      (Set.Icc s t ×ˢ Kset) := by
    intro y hy
    exact ⟨hqIcc, interior_subset hy⟩
  have hcont_q : ContinuousWithinAt (fun y : M => f q y)
      (interior Kset) x := by
    have hc := hcont_sp.comp hphi.continuousWithinAt hmap
    change ContinuousWithinAt (fun y : M => f q y) (interior Kset) x at hc
    exact hc
  have hle := ContinuousWithinAt.closure_le (x := x) (hK hx)
    (continuousWithinAt_const : ContinuousWithinAt (fun _ : M => (0 : Real))
      (interior Kset) x) hcont_q
    (fun y hy => (h.2.2.2.1 q hq y hy).le)
  simpa using hle

theorem IsLocalScalarDirichletSolution.time_restrict
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T s t c : Real}
    (X : Real → (x : M) → TangentSpace I x)
    (Kset : Set M) (f₀ : M → Real) (f : Real → M → Real)
    (h : IsLocalScalarDirichletSolution (I := I) G T X s t c Kset f₀ f)
    {u : Real} (hu : u ∈ Set.Icc s t) :
    IsLocalScalarDirichletSolution (I := I) G T X s u c Kset f₀ f := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply h.1.mono
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans hu.2⟩, hp.2⟩
  · intro z hz
    exact h.2.1 z hz
  · intro q hq z hz
    exact h.2.2.1 q ⟨hq.1, hq.2.trans hu.2⟩ z hz
  · intro q hq z hz
    exact h.2.2.2.1 q ⟨hq.1, hq.2.trans hu.2⟩ z hz
  · intro q hq z hz
    exact h.2.2.2.2.1 q ⟨hq.1, hq.2.trans hu.2⟩ z hz
  · intro q hq z hz
    exact h.2.2.2.2.2.1 q ⟨hq.1, hq.2.trans hu.2⟩ z hz
  · intro q hq z hz
    exact h.2.2.2.2.2.2.1 q ⟨hq.1, hq.2.trans hu.2⟩ z hz
  · intro q hq z hz
    exact h.2.2.2.2.2.2.2 q ⟨hq.1, hq.2.trans hu.2⟩ z hz

structure IsGlobalScalarDirichletSolution
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real → (x : M) → TangentSpace I x)
    (a : Real) (u : Real → M → Real) : Prop where
  continuous : ContinuousOn (fun p : Real × M ↦ u p.1 p.2)
    (Set.Icc 0 T ×ˢ Set.univ)
  boundary : ∀ q ∈ Set.Icc 0 T, ∀ p : BoundaryManifold I M,
    u q (p : M) = 0
  time : ∀ q ∈ Set.Icc 0 T, 0 < q → ∀ x : M,
    DifferentiableWithinAt Real (fun r ↦ u r x) (Set.Icc 0 T) q
  space : ∀ q ∈ Set.Icc 0 T, 0 < q → ∀ x : M,
    MDifferentiableAt I 𝓘(Real, Real) (u q) x
  gradient : ∀ q ∈ Set.Icc 0 T, 0 < q → ∀ x : M,
    MDiffAt (T% fun y : M ↦ gradientFun (I := I) (G.metric q) (u q) y) x
  equation : ∀ q ∈ Set.Icc 0 T, 0 < q → ∀ x : M,
    parabolicOperatorWithDrift (I := I) G T X u q x = -a * u q x

theorem global_scalar_dirichlet_solution_unique
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real}
    (X : Real → (x : M) → TangentSpace I x)
    {a : Real} (ha : 0 ≤ a)
    {u v : Real → M → Real}
    (hu : IsGlobalScalarDirichletSolution (I := I) G T X a u)
    (hv : IsGlobalScalarDirichletSolution (I := I) G T X a v)
    (hinit : ∀ x : M, u 0 x = v 0 x) :
    ∀ q ∈ Set.Icc 0 T, ∀ x : M, u q x = v q x := by
  let w : Real → M → Real := fun q x => u q x - v q x
  have hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.univ) := by
    exact hu.continuous.sub hv.continuous
  have hw0 : ∀ x : M, 0 ≤ w 0 x := by
    intro x
    simp [w, hinit x]
  have hw_boundary : ∀ q ∈ Set.Icc 0 T, ∀ p : BoundaryManifold I M,
      0 ≤ w q (p : M) := by
    intro q hq p
    change 0 ≤ u q (p : M) - v q (p : M)
    rw [hu.boundary q hq p, hv.boundary q hq p]
    norm_num
  have hw_time : ∀ q ∈ Set.Icc 0 T, 0 < q → ∀ x ∈ I.interior M,
      DifferentiableWithinAt Real (fun r => w r x) (Set.Icc 0 T) q := by
    intro q hq hqpos x _
    exact (hu.time q hq hqpos x).sub (hv.time q hq hqpos x)
  have hw_mdiff : ∀ q ∈ Set.Icc 0 T, 0 < q → ∀ x ∈ I.interior M,
      MDifferentiableAt I 𝓘(Real, Real) (w q) x := by
    intro q hq hqpos x _
    exact (hu.space q hq hqpos x).sub (hv.space q hq hqpos x)
  have hw_grad : ∀ q ∈ Set.Icc 0 T, 0 < q → ∀ x ∈ I.interior M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric q) (w q) y) x := by
    intro q hq hqpos x _
    have hgrad_eq : (fun y : M => gradientFun (I := I) (G.metric q) (w q) y) =
        (fun y : M => gradientFun (I := I) (G.metric q) (u q) y -
          gradientFun (I := I) (G.metric q) (v q) y) := by
      funext y
      exact gradientFun_sub (I := I) (G.metric q)
        (hu.space q hq hqpos y) (hv.space q hq hqpos y)
    have hgrad_total :
        (T% fun y : M => gradientFun (I := I) (G.metric q) (w q) y) =
          (T% fun y : M => gradientFun (I := I) (G.metric q) (u q) y -
            gradientFun (I := I) (G.metric q) (v q) y) := by
      funext y
      exact congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I : M → Type _)))
        (congrFun hgrad_eq y)
    rw [hgrad_total]
    exact mdifferentiableAt_sub_section
      (hu.gradient q hq hqpos x) (hv.gradient q hq hqpos x)
  have hnegative : ∀ q ∈ Set.Icc 0 T, 0 < q → ∀ x ∈ I.interior M,
      w q x < 0 →
        0 ≤ parabolicOperatorWithDrift (I := I) G T X w q x := by
    intro q hq hqpos x hx hneg
    have hsub := parabolic_sub (I := I) G T X u v q x
      (hu.time q hq hqpos x) (hv.time q hq hqpos x)
      (fun y => hu.space q hq hqpos y) (fun y => hv.space q hq hqpos y)
      (hu.gradient q hq hqpos x)
      (hv.gradient q hq hqpos x)
    rw [hsub, hu.equation q hq hqpos x, hv.equation q hq hqpos x]
    have hnonneg : 0 ≤ (-a) * (u q x - v q x) :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr ha) hneg.le
    dsimp [w] at hneg ⊢
    nlinarith
  have hw_nonneg := strict_barrier_on_compact_manifold_with_boundary
    (I := I) G T X w hw_cont hw0 hw_boundary hw_time hw_mdiff hw_grad hnegative
  let w' : Real → M → Real := fun q x => v q x - u q x
  have hw'_cont : ContinuousOn (fun p : Real × M => w' p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.univ) := by
    exact hv.continuous.sub hu.continuous
  have hw'0 : ∀ x : M, 0 ≤ w' 0 x := by
    intro x
    simp [w', hinit x]
  have hw'_boundary : ∀ q ∈ Set.Icc 0 T, ∀ p : BoundaryManifold I M,
      0 ≤ w' q (p : M) := by
    intro q hq p
    change 0 ≤ v q (p : M) - u q (p : M)
    rw [hv.boundary q hq p, hu.boundary q hq p]
    norm_num
  have hw'_time : ∀ q ∈ Set.Icc 0 T, 0 < q → ∀ x ∈ I.interior M,
      DifferentiableWithinAt Real (fun r => w' r x) (Set.Icc 0 T) q := by
    intro q hq hqpos x _
    exact (hv.time q hq hqpos x).sub (hu.time q hq hqpos x)
  have hw'_mdiff : ∀ q ∈ Set.Icc 0 T, 0 < q → ∀ x ∈ I.interior M,
      MDifferentiableAt I 𝓘(Real, Real) (w' q) x := by
    intro q hq hqpos x _
    exact (hv.space q hq hqpos x).sub (hu.space q hq hqpos x)
  have hw'_grad : ∀ q ∈ Set.Icc 0 T, 0 < q → ∀ x ∈ I.interior M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric q) (w' q) y) x := by
    intro q hq hqpos x _
    have hgrad_eq : (fun y : M => gradientFun (I := I) (G.metric q) (w' q) y) =
        (fun y : M => gradientFun (I := I) (G.metric q) (v q) y -
          gradientFun (I := I) (G.metric q) (u q) y) := by
      funext y
      exact gradientFun_sub (I := I) (G.metric q)
        (hv.space q hq hqpos y) (hu.space q hq hqpos y)
    have hgrad_total :
        (T% fun y : M => gradientFun (I := I) (G.metric q) (w' q) y) =
          (T% fun y : M => gradientFun (I := I) (G.metric q) (v q) y -
            gradientFun (I := I) (G.metric q) (u q) y) := by
      funext y
      exact congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I : M → Type _)))
        (congrFun hgrad_eq y)
    rw [hgrad_total]
    exact mdifferentiableAt_sub_section
      (hv.gradient q hq hqpos x) (hu.gradient q hq hqpos x)
  have h'negative : ∀ q ∈ Set.Icc 0 T, 0 < q → ∀ x ∈ I.interior M,
      w' q x < 0 →
        0 ≤ parabolicOperatorWithDrift (I := I) G T X w' q x := by
    intro q hq hqpos x hx hneg
    have hsub := parabolic_sub (I := I) G T X v u q x
      (hv.time q hq hqpos x) (hu.time q hq hqpos x)
      (fun y => hv.space q hq hqpos y) (fun y => hu.space q hq hqpos y)
      (hv.gradient q hq hqpos x)
      (hu.gradient q hq hqpos x)
    rw [hsub, hv.equation q hq hqpos x, hu.equation q hq hqpos x]
    have hnonneg : 0 ≤ (-a) * (v q x - u q x) :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr ha) hneg.le
    dsimp [w'] at hneg ⊢
    nlinarith
  have hw'_nonneg := strict_barrier_on_compact_manifold_with_boundary
    (I := I) G T X w' hw'_cont hw'0 hw'_boundary hw'_time hw'_mdiff hw'_grad
      h'negative
  intro q hq x
  have hleft := hw_nonneg q hq x
  have hright := hw'_nonneg q hq x
  dsimp [w, w'] at hleft hright
  linarith

def HasLocalScalarDirichletSolution
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real → (x : M) → TangentSpace I x)
    (s t : Real) (Kset : Set M) : Prop :=
  IsCompact Kset ∧ (interior Kset).Nonempty ∧ IsPreconnected (interior Kset) ∧
    ∀ (c : Real), 0 ≤ c → ∀ f₀ : M → Real,
      ContMDiff I 𝓘(Real, Real) ∞ f₀ →
      (∀ z, 0 ≤ f₀ z) → HasCompactSupport f₀ →
      tsupport f₀ ⊆ interior Kset →
      (∃ z ∈ interior Kset, 0 < f₀ z) →
      ∃ f : Real → M → Real, IsLocalScalarDirichletSolution
        (I := I) G T X s t c Kset f₀ f

theorem HasLocalScalarDirichletSolution.exists_solution
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {T : Real} {X : Real → (x : M) → TangentSpace I x}
    {s t : Real} {Kset : Set M}
    (h : HasLocalScalarDirichletSolution (I := I) G T X s t Kset)
    {c : Real} (hc : 0 ≤ c) {f₀ : M → Real}
    (hf₀ : ContMDiff I 𝓘(Real, Real) ∞ f₀)
    (hf₀_nonneg : ∀ z, 0 ≤ f₀ z) (hf₀_compact : HasCompactSupport f₀)
    (hf₀_support : tsupport f₀ ⊆ interior Kset)
    (hf₀_pos : ∃ z ∈ interior Kset, 0 < f₀ z) :
    ∃ f : Real → M → Real, IsLocalScalarDirichletSolution
      (I := I) G T X s t c Kset f₀ f :=
  h.2.2.2 c hc f₀ hf₀ hf₀_nonneg hf₀_compact hf₀_support hf₀_pos

theorem scalar_dirichlet_solution_nonnegative_and_positive_of_initial_point
    [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (X : Real → (x : M) → TangentSpace I x)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hheat_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (a : Real) (ha : 0 ≤ a)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_initial : ∀ x : M, 0 ≤ u 0 x)
    (hu_boundary : ∀ t ∈ Set.Icc 0 T, ∀ p : BoundaryManifold I M,
      u t (p : M) = 0)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_equation : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ I.interior M,
      parabolicOperatorWithDrift (I := I) G T X u t x = -a * u t x)
    (hinterior_conn : IsPreconnected (I.interior M))
    {c : M} (hcint : c ∈ I.interior M) (hc : 0 < u 0 c) :
    (∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x) ∧
      (∀ t ∈ Set.Ioc 0 T, ∀ y ∈ I.interior M, 0 < u t y) := by
  refine ⟨?_, ?_⟩
  · exact scalar_dirichlet_solution_nonnegative (I := I) G T X a ha u
      hu_cont hu_initial hu_boundary hu_time hu_mdiff hu_grad hu_equation
  · exact scalar_dirichlet_solution_positive_of_initial_point (I := I) G T X
      hgrad_cont hheat_cont a ha u hu_cont hu_initial hu_boundary hu_time
      hu_mdiff hu_grad hu_equation hinterior_conn hcint hc

end Dirichlet

end

end DifferentialGeometry.Analysis.Parabolic

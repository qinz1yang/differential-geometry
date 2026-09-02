import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.BoundaryHopf
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ScalarStrong

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
    [VectorBundle Real E (TangentSpace I : M → Type _)]
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

theorem scalar_dirichlet_solution_lower_bound_of_spatial_subsolution
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (a : Real) (ha : 0 ≤ a)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
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
    (hb_boundary : ∀ p : BoundaryManifold I M, b (p : M) = 0)
    (C : Real)
    (hb_heat : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ I.interior M,
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
    simp [w, v, hu_boundary t ht p, hb_boundary p]
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
      parabolicOperatorWithDrift (I := I) G T X v t x ≤ -a * v t x := by
    intro t ht htpos x hx
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
    have hheat := hb_heat t ht x hx
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
    have hsub := parabolic_sub_at (I := I) G T X u v t x
      (hu_time t ht htpos x hx) (hv_time t ht htpos x)
      hu_space hv_space (hu_grad t ht htpos x hx) (hv_grad t ht htpos x)
    change parabolicOperatorWithDrift (I := I) G T X w t x = _ at hsub
    rw [hsub, hu_equation t ht htpos x hx]
    have hvP := hv_operator t ht htpos x hx
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

end Dirichlet

end

end DifferentialGeometry.Analysis.Parabolic

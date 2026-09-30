import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace DifferentialGeometry.Analysis.Parabolic

structure ParabolicCutoffLowerSupportAt
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T ε : Real)
    (χ : Real → M → Real)
    (t : Real) (x : M) where
  phi : Real → M → Real
  eq_at : phi t x = χ t x
  lower_nhds :
    ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
      0 ≤ phi p.1 p.2 ∧ phi p.1 p.2 ≤ χ p.1 p.2
  time_diff :
    DifferentiableWithinAt Real (fun s => phi s x) (Set.Icc 0 T) t
  space_diff_nhds :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) (phi t) y
  grad_diff :
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (phi t) y) x
  grad_sq_le :
    (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) (phi t) x)
        (gradientFun (I := I) (G.metric t) (phi t) x) ≤
      ε * phi t x
  parabolic_le :
    parabolicOperatorWithDrift (I := I) G T
      (fun _ y => (0 : TangentSpace I y)) phi t x ≤ ε

structure ParabolicCutoff
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T ε : Real) where
  chi : Real → M → Real
  support : Set M
  err_nonneg : 0 ≤ ε
  support_compact : IsCompact support
  support_zero :
    ∀ t, t ∈ Set.Icc 0 T → ∀ x, x ∉ support → chi t x = 0
  range :
    ∀ t, t ∈ Set.Icc 0 T → ∀ x, chi t x ∈ Set.Icc (0 : Real) 1
  joint_cont :
    ContinuousOn (fun p : Real × M ↦ chi p.1 p.2)
      (Set.Icc 0 T ×ˢ support)
  lowerSupport :
    ∀ t, t ∈ Set.Icc 0 T → 0 < t → ∀ x, 0 < chi t x →
      Nonempty (ParabolicCutoffLowerSupportAt (I := I) G T ε chi t x)

theorem ParabolicCutoff.isCompact_slab
    {G : MetricConnectionFamily (I := I) (M := M) Real} {T ε : Real}
    (cut : ParabolicCutoff (I := I) G T ε) :
    IsCompact (Set.Icc 0 T ×ˢ cut.support) :=
  isCompact_Icc.prod cut.support_compact

theorem ParabolicCutoff.mem_support_of_pos
    {G : MetricConnectionFamily (I := I) (M := M) Real} {T ε t : Real}
    (cut : ParabolicCutoff (I := I) G T ε)
    (ht : t ∈ Set.Icc 0 T) {x : M} (hx : 0 < cut.chi t x) :
    x ∈ cut.support := by
  by_contra hmem
  rw [cut.support_zero t ht x hmem] at hx
  exact lt_irrefl 0 hx

structure ParabolicCutoffSequence
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) where
  chi : Nat → Real → M → Real
  err : Nat → Real
  support : Nat → Set M
  err_nonneg : ∀ n, 0 ≤ err n
  err_tendsto : Tendsto err atTop (nhds 0)
  support_compact : ∀ n, IsCompact (support n)
  support_zero :
    ∀ n t, t ∈ Set.Icc 0 T → ∀ x, x ∉ support n → chi n t x = 0
  range :
    ∀ n t x, t ∈ Set.Icc 0 T → chi n t x ∈ Set.Icc (0 : Real) 1
  exhausts :
    ∀ t x, t ∈ Set.Icc 0 T →
      ∃ n₀, ∀ n, n₀ ≤ n → chi n t x = 1
  joint_cont :
    ∀ n, ContinuousOn
      (fun p : Real × M => chi n p.1 p.2) (spacetimeSlab (M := M) T)
  time_diff :
    ∀ n t, t ∈ Set.Icc 0 T → 0 < t → ∀ x,
      DifferentiableWithinAt Real (fun s => chi n s x) (Set.Icc 0 T) t
  space_smooth :
    ∀ n t, t ∈ Set.Icc 0 T →
      ContMDiff I 𝓘(Real, Real) ∞ (chi n t)
  grad_sq_le :
    ∀ n t, t ∈ Set.Icc 0 T → 0 < t → ∀ x,
      (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) (chi n t) x)
          (gradientFun (I := I) (G.metric t) (chi n t) x) ≤
        err n * chi n t x
  parabolic_le :
    ∀ n t, t ∈ Set.Icc 0 T → 0 < t → ∀ x,
      parabolicOperatorWithDrift (I := I) G T
        (fun _ y => (0 : TangentSpace I y)) (chi n) t x ≤ err n

structure ParabolicBarrierCutoffSequence
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (O : M) where
  chi : Nat → Real → M → Real
  err : Nat → Real
  support : Nat → Set M
  err_nonneg : ∀ n, 0 ≤ err n
  err_tendsto : Tendsto err atTop (nhds 0)
  support_compact : ∀ n, IsCompact (support n)
  support_zero :
    ∀ n t, t ∈ Set.Icc 0 T →
      ∀ x, x ∉ support n → chi n t x = 0
  range :
    ∀ n t x, t ∈ Set.Icc 0 T →
      chi n t x ∈ Set.Icc (0 : Real) 1
  center_exhausts :
    ∀ t, t ∈ Set.Icc 0 T →
      ∀ᶠ n in atTop, chi n t O = 1
  joint_cont :
    ∀ n, ContinuousOn
      (fun p : Real × M => chi n p.1 p.2)
      (Set.Icc 0 T ×ˢ support n)
  lowerSupport :
    ∀ n t, t ∈ Set.Icc 0 T → 0 < t → ∀ x,
      0 < chi n t x →
        ParabolicCutoffLowerSupportAt
          (I := I) G T (err n) (chi n) t x

namespace ParabolicCutoffSequence

theorem support_slab
    {G : MetricConnectionFamily (I := I) (M := M) Real} {T : Real}
    (cut : ParabolicCutoffSequence (I := I) G T) (n : Nat) :
    IsCompact (Set.Icc 0 T ×ˢ cut.support n) :=
  isCompact_Icc.prod (cut.support_compact n)

theorem space_diff
    {G : MetricConnectionFamily (I := I) (M := M) Real} {T : Real}
    (cut : ParabolicCutoffSequence (I := I) G T) {n : Nat} {t : Real}
    (ht : t ∈ Set.Icc 0 T) (x : M) :
    MDifferentiableAt I 𝓘(Real, Real) (cut.chi n t) x :=
  (cut.space_smooth n t ht).mdifferentiableAt (by simp)

theorem grad_diff
    {G : MetricConnectionFamily (I := I) (M := M) Real} {T : Real}
    (cut : ParabolicCutoffSequence (I := I) G T) {n : Nat} {t : Real}
    (ht : t ∈ Set.Icc 0 T) (x : M) :
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (cut.chi n t) y) x :=
  gradientFun_mdiffAt (I := I) (G.metric t) (cut.space_smooth n t ht) x

def toBarrierAt
    {G : MetricConnectionFamily (I := I) (M := M) Real} {T : Real}
    (cut : ParabolicCutoffSequence (I := I) G T) (O : M) :
    ParabolicBarrierCutoffSequence (I := I) G T O where
  chi := cut.chi
  err := cut.err
  support := cut.support
  err_nonneg := cut.err_nonneg
  err_tendsto := cut.err_tendsto
  support_compact := cut.support_compact
  support_zero := cut.support_zero
  range := cut.range
  center_exhausts := by
    intro t ht
    obtain ⟨n₀, hn₀⟩ := cut.exhausts t O ht
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact hn₀ n hn
  joint_cont := by
    intro n
    exact (cut.joint_cont n).mono fun p hp =>
      ⟨hp.1, Set.mem_univ p.2⟩
  lowerSupport := by
    intro n t ht htpos x _hx
    refine
      { phi := cut.chi n
        eq_at := rfl
        lower_nhds := ?_
        time_diff := cut.time_diff n t ht htpos x
        space_diff_nhds := ?_
        grad_diff := cut.grad_diff ht x
        grad_sq_le := cut.grad_sq_le n t ht htpos x
        parabolic_le := cut.parabolic_le n t ht htpos x }
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact ⟨(cut.range n p.1 p.2 hp.1).1, le_rfl⟩
    · exact Filter.Eventually.of_forall fun y => cut.space_diff ht y

end ParabolicCutoffSequence

end DifferentialGeometry.Analysis.Parabolic

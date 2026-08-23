import DifferentialGeometry.Geometry.Metric.Convergence.WindowBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.FixedDomainBounds

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry

attribute [local instance] Fintype.ofFinite
namespace HCGCompactness

open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedDomain

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)
structure MetricAllTimesFirstOrderInput
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (K u : Set M) (β ψ t0 : Real)
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (SSeq : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M)
    (T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x)
    (A : Real) where
  base :
    MetricAllTimesBoundsInput (I := I) K β ψ t0
      (fun i t => (SSeq i).family.metric t) gRef
  log_input :
    MetricLogDerivativeInput (I := I) K β ψ t0
      (fun i t => (SSeq i).family.metric t) T A
  frame : Idx -> (x : M) -> TangentSpace I x
  hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u
  hu : IsOpen u
  K_subset_u : K ⊆ u
  subset_carrier : Set.Icc β ψ ⊆ D.carrier
  regular_on_window : forall s : Real, s ∈ Set.Icc β ψ -> s ∈ D.regular
  gInv : Nat -> Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx
  nablaRic : Nat -> Real -> M -> Idx -> Idx -> Idx -> Real
  hinv_id :
    forall i : Nat, forall s : Real, s ∈ Set.Icc β ψ ->
      forall x : M, x ∈ K ->
        forall e l : Idx, gInv i s x e l = if e = l then 1 else 0
  hinv_frame :
    forall i : Nat, forall s : Real, s ∈ Set.Icc β ψ ->
      DifferentialGeometry.Geometry.Curvature.InverseMetricComponentsInFrame
        (I := I) ((SSeq i).family.metric s) (gInv i s) frame
  hevol :
    forall i : Nat,
      DifferentialGeometry.PDE.RicciFlow.ChristoffelEvolutionEquationInFrameOn
        (I := I) (SSeq i) (gInv i) frame
        (localFrameOneOfInf (I := I) frame hframe) (nablaRic i)
  R : Real
  R_nonneg : 0 <= R
  nablaRic_bound :
    forall i : Nat, forall s : Real, s ∈ Set.Icc β ψ ->
      forall x : M, x ∈ K ->
        Real.sqrt
          (DifferentialGeometry.Geometry.Connection.componentL2Sq3
            (fun a b c : Idx => nablaRic i s x a b c)) <= R
  initialOneC : Real
  initial_one_bound :
    forall i : Nat, forall x : M, x ∈ K ->
      metricCovDerivNorm (I := I) 1 ((SSeq i).family.metric t0) gRef x <=
        initialOneC
  Bmax : Real
  B_le_Bmax :
    forall t : Real, t ∈ Set.Icc β ψ ->
      metricEquivalenceFactor base.equivC A t t0 <= Bmax
  timeRadius : Real
  time_abs_le :
    forall t : Real, t ∈ Set.Icc β ψ -> |t - t0| <= timeRadius

structure MetricAllTimesFirstOrderConclusion
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (K : Set M) (β ψ : Real)
    (SSeq : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef
      (fun i t => (SSeq i).family.metric t) B
  C1 : Real
  order_one_bound :
    MetricCovDerivOrderBoundOnWindow (I := I) K β ψ
      (fun i t => (SSeq i).family.metric t) gRef 1 C1

omit [SigmaCompactSpace M] in
theorem metricCovOrderOneWindow_of_christoffel
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {K u : Set M} {β ψ t0 : Real} {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {SSeq : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D}
    {gRef : SmoothRiemannianMetric I M}
    {T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x}
    {A : Real}
    (H :
      MetricAllTimesFirstOrderInput (I := I) (Idx := Idx) K u β ψ t0
        (D := D) SSeq gRef T A) :
    MetricCovDerivOrderBoundOnWindow (I := I) K β ψ
      (fun i t => (SSeq i).family.metric t) gRef 1
      (metricFirstOrderConstant
        H.base.equivC H.Bmax H.R H.timeRadius H.initialOneC) := by
  have hEquivC : 1 <= H.base.equivC := (H.base.equiv_at_t0 0).1
  have hequiv_window :
      MetricUniformEquivalentOnWindow (I := I) K β ψ gRef
        (fun i t => (SSeq i).family.metric t)
        (fun t : Real => metricEquivalenceFactor H.base.equivC A t t0) :=
    metricUniformEquivalentOnWindow_of_logDerivativeInput
      (I := I) K β ψ t0 H.base.equivC A gRef
      (fun i t => (SSeq i).family.metric t) T
      H.base.t0_mem hEquivC H.base.equiv_at_t0 H.log_input
  refine
    metricCovOrderWindow_of_pointwise (I := I) K β ψ
      (fun i t => (SSeq i).family.metric t) gRef 1
      (metricFirstOrderConstant
        H.base.equivC H.Bmax H.R H.timeRadius H.initialOneC) ?_
  intro i t ht x hxK
  have hsegment : Set.uIcc t0 t ⊆ Set.Icc β ψ :=
    Set.uIcc_subset_Icc H.base.t0_mem ht
  have hsub : Set.uIcc t0 t ⊆ D.carrier := fun s hs =>
    H.subset_carrier (hsegment hs)
  have hregular :
      forall s : Real, s ∈ Set.uIcc t0 t -> s ∈ D.regular := fun s hs =>
    H.regular_on_window s (hsegment hs)
  have hEq_t :
      MetricUniformEquivalentOn
        (I := I) K gRef ((SSeq i).family.metric t) H.Bmax :=
    metricUniformEquivalentOn_of_le
      (I := I) (hequiv_window i t ht) (H.B_le_Bmax t ht)
  have hraw :
      metricCovDerivNorm (I := I) 1 ((SSeq i).family.metric t) gRef x <=
        Real.sqrt (H.Bmax ^ 3) *
          (2 *
            (3 * H.R * |t - t0| +
              (3 / 2 : Real) *
                (Real.sqrt (H.base.equivC ^ 3) * H.initialOneC))) :=
    covOne_le_init
      (I := I) (K := K) (u := u) (SSeq i) gRef (H.gInv i)
      H.frame H.hframe H.hu (H.K_subset_u hxK) hxK (H.nablaRic i)
      hsub hregular
      (fun s hs e l => H.hinv_id i s (hsegment hs) x hxK e l)
      (H.hevol i)
      (fun s hs => H.nablaRic_bound i s (hsegment hs) x hxK)
      hEq_t (H.hinv_frame i t ht) (H.base.equiv_at_t0 i)
      (H.hinv_frame i t0 H.base.t0_mem)
      (H.initial_one_bound i x hxK)
  have htime :
      3 * H.R * |t - t0| <= 3 * H.R * H.timeRadius := by
    nlinarith [H.R_nonneg, H.time_abs_le t ht]
  have hinside :
      3 * H.R * |t - t0| +
          (3 / 2 : Real) *
            (Real.sqrt (H.base.equivC ^ 3) * H.initialOneC) <=
        3 * H.R * H.timeRadius +
          (3 / 2 : Real) *
            (Real.sqrt (H.base.equivC ^ 3) * H.initialOneC) :=
    by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right htime
          ((3 / 2 : Real) *
            (Real.sqrt (H.base.equivC ^ 3) * H.initialOneC))
  have hconst :
      Real.sqrt (H.Bmax ^ 3) *
          (2 *
            (3 * H.R * |t - t0| +
              (3 / 2 : Real) *
                (Real.sqrt (H.base.equivC ^ 3) * H.initialOneC))) <=
        metricFirstOrderConstant
          H.base.equivC H.Bmax H.R H.timeRadius H.initialOneC := by
    unfold metricFirstOrderConstant
    exact
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinside (by norm_num : (0 : Real) <= 2))
        (Real.sqrt_nonneg _)
  exact le_trans hraw hconst

def metricAllTimes_firstOrder
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {K u : Set M} {β ψ t0 : Real} {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {SSeq : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D}
    {gRef : SmoothRiemannianMetric I M}
    {T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x}
    {A : Real}
    (H :
      MetricAllTimesFirstOrderInput (I := I) (Idx := Idx) K u β ψ t0
        (D := D) SSeq gRef T A) :
    MetricAllTimesFirstOrderConclusion (I := I) K β ψ SSeq gRef where
  B := fun t : Real => metricEquivalenceFactor H.base.equivC A t t0
  equiv_on_window := by
    have hEquivC : 1 <= H.base.equivC := (H.base.equiv_at_t0 0).1
    exact
      metricUniformEquivalentOnWindow_of_logDerivativeInput
        (I := I) K β ψ t0 H.base.equivC A gRef
        (fun i t => (SSeq i).family.metric t) T
        H.base.t0_mem hEquivC H.base.equiv_at_t0 H.log_input
  C1 :=
    metricFirstOrderConstant
      H.base.equivC H.Bmax H.R H.timeRadius H.initialOneC
  order_one_bound :=
    metricCovOrderOneWindow_of_christoffel (I := I) (Idx := Idx) H

def metricCovOrderEvolutionAlpha (Cpp : Real) : Real :=
  1 + 8 * Cpp ^ 2

def metricCovOrderEvolutionBeta (Cppp : Real) : Real :=
  8 * Cppp ^ 2 + 1

def metricCovOrderEvolutionConstant
    (Cpp Cppp timeRadius initC : Real) : Real :=
  Real.sqrt
    (Real.exp (metricCovOrderEvolutionAlpha Cpp * timeRadius) *
      (initC ^ 2 +
        metricCovOrderEvolutionBeta Cppp /
          metricCovOrderEvolutionAlpha Cpp))

def MetricCovOrderEvolutionOn
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p : Nat)
    (nablaRic :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x) :
    Prop :=
  forall i : Nat, forall x : M, x ∈ K -> forall s : Real, s ∈ Set.Icc β ψ ->
      HasDerivAt
        (fun r : Real => metricCovDeriv (I := I) (gSeq i r) gRef p x)
        ((-2 : Real) • nablaRic i s x) s

def MetricCovOrderNormSqEvolutionOn
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p : Nat)
    (nablaRic :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x) :
    Prop :=
  forall i : Nat, forall x : M, x ∈ K -> forall s : Real, s ∈ Set.Icc β ψ ->
    exists d : Real,
      HasDerivAt
        (fun r : Real =>
          metricCovDerivNorm (I := I) p (gSeq i r) gRef x ^ 2) d s ∧
        |d| <=
          metricCovDerivNorm (I := I) p (gSeq i s) gRef x ^ 2 +
            (2 *
              Real.sqrt
                (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
                  (nablaRic i s x))) ^ 2

structure MetricCovOrderEvolutionInput
    (K : Set M) (β ψ t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p : Nat) where
  t0_mem : t0 ∈ Set.Icc β ψ
  nablaRic :
    Nat -> Real -> (x : M) ->
      Tensor0SBundle.Tensor0SSpace
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x
  normsq_evol :
    MetricCovOrderNormSqEvolutionOn (I := I) K β ψ gSeq gRef p nablaRic
  Cpp : Real
  Cppp : Real
  Cpp_nonneg : 0 <= Cpp
  Cppp_nonneg : 0 <= Cppp
  ric_bound :
    forall i : Nat, forall s : Real, s ∈ Set.Icc β ψ ->
      forall x : M, x ∈ K ->
        Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
            (nablaRic i s x)) <=
          Cpp * metricCovDerivNorm (I := I) p (gSeq i s) gRef x + Cppp
  initC : Real
  initC_nonneg : 0 <= initC
  init_bound :
    forall i : Nat, forall x : M, x ∈ K ->
      metricCovDerivNorm (I := I) p (gSeq i t0) gRef x <= initC
  timeRadius : Real
  time_abs_le :
    forall t : Real, t ∈ Set.Icc β ψ -> |t - t0| <= timeRadius

omit [SigmaCompactSpace M] in
theorem metricCovOrderWindow_of_evolution
    {K : Set M} {β ψ t0 : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p : Nat}
    (Hin :
      MetricCovOrderEvolutionInput (I := I) K β ψ t0 gSeq gRef p) :
    MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef p
      (metricCovOrderEvolutionConstant
        Hin.Cpp Hin.Cppp Hin.timeRadius Hin.initC) := by
  refine
    metricCovOrderWindow_of_pointwise (I := I) K β ψ gSeq gRef p
      (metricCovOrderEvolutionConstant
        Hin.Cpp Hin.Cppp Hin.timeRadius Hin.initC) ?_
  intro i t ht x hxK
  let U : Real -> Real := fun s =>
    metricCovDerivNorm (I := I) p (gSeq i s) gRef x ^ 2
  have hsegment : Set.uIcc t0 t ⊆ Set.Icc β ψ :=
    Set.uIcc_subset_Icc Hin.t0_mem ht
  let derivData :
      forall s : Real, s ∈ Set.Icc β ψ ->
        exists d : Real, HasDerivAt U d s ∧
          |d| <= U s +
            (2 *
              Real.sqrt
                (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
                  (Hin.nablaRic i s x))) ^ 2 := fun s hs =>
    by
      simpa [U] using Hin.normsq_evol i x hxK s hs
  let U' : Real -> Real := fun s =>
    if hs : s ∈ Set.Icc β ψ then Classical.choose (derivData s hs) else 0
  have hU_nonneg : forall s : Real, s ∈ Set.uIcc t0 t -> 0 <= U s := by
    intro s hs
    exact sq_nonneg _
  have hU_deriv :
      forall s : Real, s ∈ Set.uIcc t0 t -> HasDerivAt U (U' s) s := by
    intro s hs
    have hswin : s ∈ Set.Icc β ψ := hsegment hs
    have hspec := Classical.choose_spec (derivData s hswin)
    have hchoose : U' s = Classical.choose (derivData s hswin) := by
      dsimp [U']
      exact dif_pos hswin
    simpa [hchoose] using hspec.1
  have halpha_pos : 0 < metricCovOrderEvolutionAlpha Hin.Cpp := by
    unfold metricCovOrderEvolutionAlpha
    nlinarith [sq_nonneg Hin.Cpp]
  have hbeta_pos : 0 < metricCovOrderEvolutionBeta Hin.Cppp := by
    unfold metricCovOrderEvolutionBeta
    nlinarith [sq_nonneg Hin.Cppp]
  have hbound :
      forall s : Real, s ∈ Set.uIcc t0 t ->
        |U' s| <=
          metricCovOrderEvolutionAlpha Hin.Cpp * U s +
            metricCovOrderEvolutionBeta Hin.Cppp := by
    intro s hs
    have hswin : s ∈ Set.Icc β ψ := hsegment hs
    have hspec := Classical.choose_spec (derivData s hswin)
    have hchoose : U' s = Classical.choose (derivData s hswin) := by
      dsimp [U']
      exact dif_pos hswin
    have hbase :
        |U' s| <=
          U s +
            (2 *
              Real.sqrt
                (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
                  (Hin.nablaRic i s x))) ^ 2 := by
      simpa [hchoose] using hspec.2
    let q : Real :=
      Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
          (Hin.nablaRic i s x))
    let y : Real := metricCovDerivNorm (I := I) p (gSeq i s) gRef x
    have hq_nonneg : 0 <= q := by
      exact Real.sqrt_nonneg _
    have hy_nonneg : 0 <= y := by
      exact Real.sqrt_nonneg _
    have hRic_le :
        q <= Hin.Cpp * y + Hin.Cppp := by
      simpa [q, y] using Hin.ric_bound i s hswin x hxK
    have hRhs_nonneg : 0 <= Hin.Cpp * y + Hin.Cppp := by
      exact add_nonneg (mul_nonneg Hin.Cpp_nonneg hy_nonneg) Hin.Cppp_nonneg
    have hRic_sq :
        q ^ 2 <= (Hin.Cpp * y + Hin.Cppp) ^ 2 := by
      exact (sq_le_sq₀ hq_nonneg hRhs_nonneg).2 hRic_le
    have hYoung :
        (Hin.Cpp * y + Hin.Cppp) ^ 2 <=
          2 * (Hin.Cpp * y) ^ 2 + 2 * Hin.Cppp ^ 2 := by
      nlinarith [sq_nonneg (Hin.Cpp * y - Hin.Cppp)]
    have htwo_sq :
        (2 * q) ^ 2 <=
          8 * Hin.Cpp ^ 2 * U s + 8 * Hin.Cppp ^ 2 := by
      have hmain :
          (2 * q) ^ 2 <=
            8 * Hin.Cpp ^ 2 * y ^ 2 + 8 * Hin.Cppp ^ 2 := by
        nlinarith [hRic_sq, hYoung]
      simpa [U, y, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmain
    have hbase' :
        |U' s| <= U s + (2 * q) ^ 2 := by
      simpa [q] using hbase
    calc
      |U' s| <= U s + (2 * q) ^ 2 := hbase'
      _ <= U s + (8 * Hin.Cpp ^ 2 * U s + 8 * Hin.Cppp ^ 2) := by
            simpa [U, add_comm, add_left_comm, add_assoc] using
              add_le_add_left htwo_sq (U s)
      _ <= metricCovOrderEvolutionAlpha Hin.Cpp * U s +
            metricCovOrderEvolutionBeta Hin.Cppp := by
            unfold metricCovOrderEvolutionAlpha metricCovOrderEvolutionBeta U
            ring_nf
            nlinarith [sq_nonneg y]
  have hgronwall :
      U t <=
        Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * |t - t0|) *
          (U t0 +
            metricCovOrderEvolutionBeta Hin.Cppp /
              metricCovOrderEvolutionAlpha Hin.Cpp) :=
    affineGronwall_of_abs_deriv_le U U'
      halpha_pos hbeta_pos hU_nonneg hU_deriv hbound
  have hU0 :
      U t0 <= Hin.initC ^ 2 := by
    have hinit := Hin.init_bound i x hxK
    have hnorm_nonneg :
        0 <= metricCovDerivNorm (I := I) p (gSeq i t0) gRef x :=
      Real.sqrt_nonneg _
    have hsquare :
        (metricCovDerivNorm (I := I) p (gSeq i t0) gRef x) ^ 2 <=
          Hin.initC ^ 2 :=
      (sq_le_sq₀ hnorm_nonneg Hin.initC_nonneg).2 hinit
    simpa [U] using hsquare
  have hshift_nonneg :
      0 <=
        metricCovOrderEvolutionBeta Hin.Cppp /
          metricCovOrderEvolutionAlpha Hin.Cpp :=
    le_of_lt (div_pos hbeta_pos halpha_pos)
  have hbracket :
      U t0 +
          metricCovOrderEvolutionBeta Hin.Cppp /
            metricCovOrderEvolutionAlpha Hin.Cpp <=
        Hin.initC ^ 2 +
          metricCovOrderEvolutionBeta Hin.Cppp /
            metricCovOrderEvolutionAlpha Hin.Cpp := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right hU0
        (metricCovOrderEvolutionBeta Hin.Cppp /
          metricCovOrderEvolutionAlpha Hin.Cpp)
  have hafter_init :
      U t <=
        Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * |t - t0|) *
          (Hin.initC ^ 2 +
            metricCovOrderEvolutionBeta Hin.Cppp /
              metricCovOrderEvolutionAlpha Hin.Cpp) :=
    le_trans hgronwall
      (mul_le_mul_of_nonneg_left hbracket
        (le_of_lt (Real.exp_pos _)))
  have htime_exp :
      Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * |t - t0|) <=
        Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * Hin.timeRadius) :=
    Real.exp_le_exp.mpr (by
      nlinarith [le_of_lt halpha_pos, Hin.time_abs_le t ht])
  have hbracket_nonneg :
      0 <=
        Hin.initC ^ 2 +
          metricCovOrderEvolutionBeta Hin.Cppp /
            metricCovOrderEvolutionAlpha Hin.Cpp :=
    add_nonneg (sq_nonneg Hin.initC) hshift_nonneg
  have hfinal_sq :
      U t <=
        Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * Hin.timeRadius) *
          (Hin.initC ^ 2 +
            metricCovOrderEvolutionBeta Hin.Cppp /
              metricCovOrderEvolutionAlpha Hin.Cpp) :=
    le_trans hafter_init
      (mul_le_mul_of_nonneg_right htime_exp hbracket_nonneg)
  have htarget_nonneg :
      0 <=
        Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * Hin.timeRadius) *
          (Hin.initC ^ 2 +
            metricCovOrderEvolutionBeta Hin.Cppp /
              metricCovOrderEvolutionAlpha Hin.Cpp) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) hbracket_nonneg
  have hnorm_le :
      metricCovDerivNorm (I := I) p (gSeq i t) gRef x <=
        metricCovOrderEvolutionConstant Hin.Cpp Hin.Cppp Hin.timeRadius Hin.initC := by
    unfold metricCovOrderEvolutionConstant
    refine
      (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).1 ?_
    rw [Real.sq_sqrt htarget_nonneg]
    simpa [U] using hfinal_sq
  exact hnorm_le

omit [SigmaCompactSpace M] in
theorem metricMixedOneWindow_of_evolution
    {K : Set M} {β ψ t0 : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p : Nat} {Csp0 : Real}
    (Hin :
      MetricCovOrderEvolutionInput (I := I) K β ψ t0 gSeq gRef p)
    (hmixed :
      MetricMixedDerivOneEvolutionOn (I := I) K β ψ gSeq gRef p Hin.nablaRic)
    (hspatial :
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef p Csp0) :
    MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef p 1
      (metricMixedOneConstant Hin.Cpp Csp0 Hin.Cppp) := by
  exact
    metricMixedOneWindow_of_ric_bound (I := I)
      (K := K) (β := β) (ψ := ψ) (gSeq := gSeq) (gRef := gRef)
      (p := p) (Csp0 := Csp0) (nablaRic := Hin.nablaRic)
      Hin.Cpp Hin.Cppp Hin.Cpp_nonneg Hin.ric_bound hmixed hspatial

def MetricMixedDerivLayerEvolutionOn
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p q : Nat)
    (layer :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x) :
    Prop :=
  forall i : Nat, forall x : M, x ∈ K -> forall t : Real, t ∈ Set.Icc β ψ ->
    metricMixedDeriv (I := I) p q (gSeq i) gRef x t =
      (-2 : Real) • layer i t x

def metricMixedQConstant (Cpq : Real) : Real :=
  2 * Cpq

omit [SigmaCompactSpace M] in
theorem metricMixedQWindow_of_evolution
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p q : Nat}
    {layer :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x}
    (Cpq : Real)
    (hmixed :
      MetricMixedDerivLayerEvolutionOn (I := I) K β ψ gSeq gRef p q layer)
    (layer_bound :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall x : M, x ∈ K ->
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (layer i t x)) <= Cpq) :
    MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef p q
      (metricMixedQConstant Cpq) := by
  refine
    metricMixedWindow_of_pointwise (I := I) K β ψ gSeq gRef p q
      (metricMixedQConstant Cpq) ?_
  intro i t ht x hx
  have heq :
      metricMixedDeriv (I := I) p q (gSeq i) gRef x t =
        (-2 : Real) • layer i t x :=
    hmixed i x hx t ht
  have hnorm :
      metricMixedDerivNorm (I := I) p q (gSeq i) gRef x t =
        2 *
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (layer i t x)) := by
    unfold metricMixedDerivNorm
    rw [heq, Tensor0SBundle.sqrt_normSq0S_smul]
    norm_num
  have hlayer :=
    layer_bound i t ht x hx
  have hscaled :
      2 *
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (layer i t x)) <=
        2 * Cpq :=
    mul_le_mul_of_nonneg_left hlayer (by norm_num : (0 : Real) <= 2)
  simpa [hnorm, metricMixedQConstant] using hscaled

omit [SigmaCompactSpace M] in
theorem metricMixedZeroWindow_of_spatial
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (a : Nat) (C : Real)
    (h :
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef a C) :
    MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef a 0 C := by
  refine metricMixedWindow_of_pointwise (I := I) K β ψ gSeq gRef a 0 C ?_
  intro i t ht x hx
  simpa using h i t ht x hx

noncomputable def metricMixedCumulativeConstant
    (D : Nat -> Nat -> Real) (p q : Nat) : Real :=
  (Finset.range (p + 1) ×ˢ Finset.range (q + 1)).sup' (by
    refine ⟨(0, 0), ?_⟩
    exact Finset.mem_product.mpr ⟨by simp, by simp⟩)
    (fun ab : Nat × Nat => D ab.1 ab.2)

omit [SigmaCompactSpace M] in
theorem metricMixedBoundsWindow_of_layerBounds
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (D : Nat -> Nat -> Real)
    (hD : forall a b : Nat, 0 <= D a b)
    (hlayer :
      forall a b : Nat,
        MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef a b
          (D a b)) :
    MetricMixedDerivBoundsOnWindow (I := I) K β ψ gSeq gRef
      (metricMixedCumulativeConstant D) := by
  refine
    metricMixedBoundsWindow_of_pointwise (I := I) K β ψ gSeq gRef
      (metricMixedCumulativeConstant D) ?_
  intro i t ht p q a ha b hb x hx
  have hmem :
      (a, b) ∈ Finset.range (p + 1) ×ˢ Finset.range (q + 1) := by
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ha),
        Finset.mem_range.mpr (Nat.lt_succ_of_le hb)⟩
  have hsup : D a b <= metricMixedCumulativeConstant D p q := by
    unfold metricMixedCumulativeConstant
    exact Finset.le_sup' (fun ab : Nat × Nat => D ab.1 ab.2) hmem
  have _hcum_nonneg : 0 <= metricMixedCumulativeConstant D p q :=
    le_trans (hD a b) hsup
  exact le_trans (hlayer a b i t ht x hx) hsup

structure MetricAllTimesInput
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B
  layerC : Nat -> Nat -> Real
  layerC_nonneg : forall a b : Nat, 0 <= layerC a b
  layer_on_window :
    forall a b : Nat,
      MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef a b
        (layerC a b)

noncomputable def metricAllTimes
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (H : MetricAllTimesInput (I := I) K β ψ gSeq gRef) :
    MetricAllTimesConclusion (I := I) K β ψ gSeq gRef where
  B := H.B
  equiv_on_window := H.equiv_on_window
  metricC := metricMixedCumulativeConstant H.layerC
  mixed_on_window :=
    metricMixedBoundsWindow_of_layerBounds (I := I)
      H.layerC H.layerC_nonneg H.layer_on_window

end FixedDomain

end HCGCompactness
end DifferentialGeometry

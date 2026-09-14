import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Endomorphism
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness

universe uHF

theorem finrank_range_le_of_continuousWithinAt_of_forall_lt_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (A : ℝ → V →L[ℝ] W) (hA : ContinuousWithinAt A (Iio 0) 0) {q : ℕ}
    (hbound : ∀ t < (0 : ℝ),
      Module.finrank ℝ (LinearMap.range (A t : V →ₗ[ℝ] W)) ≤ q) :
    Module.finrank ℝ (LinearMap.range (A 0 : V →ₗ[ℝ] W)) ≤ q := by
  by_contra hle
  rw [not_le] at hle
  have hopen : IsOpen {f : V →L[ℝ] W |
      ((q + 1 : ℕ) : Cardinal) ≤ (f : V →ₗ[ℝ] W).rank} :=
    isOpen_setOfPred_nat_le_rank (𝕜 := ℝ) (E := V) (F := W) (q + 1)
  have hev : ∀ᶠ t in 𝓝[<] (0 : ℝ),
      A t ∈ {f : V →L[ℝ] W |
        ((q + 1 : ℕ) : Cardinal) ≤ (f : V →ₗ[ℝ] W).rank}ᶜ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_compl_iff, Set.mem_ofPred_eq, not_le]
    have hrank : (A t : V →ₗ[ℝ] W).rank ≤ ((q : ℕ) : Cardinal) := by
      rw [LinearMap.rank, ← Module.finrank_eq_rank]
      exact Nat.cast_le.mpr (hbound t ht)
    rw [Nat.cast_add, Nat.cast_one]
    exact Cardinal.lt_natCast_add_one_iff.mpr hrank
  have hmem := hopen.isClosed_compl.mem_of_tendsto hA hev
  have hlt : (A 0 : V →ₗ[ℝ] W).rank < ((q + 1 : ℕ) : Cardinal) := by
    simpa only [mem_compl_iff, Set.mem_ofPred_eq, not_le] using hmem
  have hrank0 : (A 0 : V →ₗ[ℝ] W).rank =
      ((Module.finrank ℝ (LinearMap.range (A 0 : V →ₗ[ℝ] W)) : ℕ) : Cardinal) := by
    rw [LinearMap.rank, Module.finrank_eq_rank]
  rw [hrank0] at hlt
  have : Module.finrank ℝ (LinearMap.range (A 0 : V →ₗ[ℝ] W)) < q + 1 := Nat.cast_lt.mp hlt
  omega

theorem finrank_range_le_of_continuousWithinAt_of_forall_lt_eq
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (A : ℝ → V →L[ℝ] W) (hA : ContinuousWithinAt A (Iio 0) 0) {q : ℕ}
    (hq : ∀ t < (0 : ℝ), Module.finrank ℝ (LinearMap.range (A t : V →ₗ[ℝ] W)) = q) :
    Module.finrank ℝ (LinearMap.range (A 0 : V →ₗ[ℝ] W)) ≤ q :=
  finrank_range_le_of_continuousWithinAt_of_forall_lt_le A hA fun t ht => (hq t ht).le

theorem finrank_range_le_of_ker_le
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W]
    {A B : V →ₗ[ℝ] W} (hker : A.ker ≤ B.ker) :
    Module.finrank ℝ B.range ≤ Module.finrank ℝ A.range := by
  have h1 : Module.finrank ℝ A.range + Module.finrank ℝ A.ker = Module.finrank ℝ V :=
    LinearMap.finrank_range_add_finrank_ker A
  have h2 : Module.finrank ℝ B.range + Module.finrank ℝ B.ker = Module.finrank ℝ V :=
    LinearMap.finrank_range_add_finrank_ker B
  have h3 : Module.finrank ℝ A.ker ≤ Module.finrank ℝ B.ker := Submodule.finrank_mono hker
  have h5 : Module.finrank ℝ V - Module.finrank ℝ B.ker ≤
      Module.finrank ℝ V - Module.finrank ℝ A.ker := Nat.sub_le_sub_left h3 _
  have h6 : Module.finrank ℝ V - Module.finrank ℝ B.ker = Module.finrank ℝ B.range := by
    rw [← h2, Nat.add_sub_cancel]
  have h7 : Module.finrank ℝ V - Module.finrank ℝ A.ker = Module.finrank ℝ A.range := by
    rw [← h1, Nat.add_sub_cancel]
  rwa [h6, h7] at h5

theorem finrank_range_le_of_range_le
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W]
    {A B : V →ₗ[ℝ] W} (h : A.range ≤ B.range) :
    Module.finrank ℝ A.range ≤ Module.finrank ℝ B.range :=
  Submodule.finrank_mono h

theorem finrank_range_eq_of_continuousWithinAt_of_forall_lt_eq_of_ker_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (A : ℝ → V →L[ℝ] W) (hA : ContinuousWithinAt A (Iio 0) 0) {q : ℕ}
    (hq : ∀ t < (0 : ℝ), Module.finrank ℝ (LinearMap.range (A t : V →ₗ[ℝ] W)) = q)
    (hker : ∀ t < (0 : ℝ), (A 0 : V →ₗ[ℝ] W).ker ≤ (A t : V →ₗ[ℝ] W).ker) :
    Module.finrank ℝ (LinearMap.range (A 0 : V →ₗ[ℝ] W)) = q := by
  refine le_antisymm (finrank_range_le_of_continuousWithinAt_of_forall_lt_eq A hA hq) ?_
  rw [← hq (-1) (by norm_num)]
  exact finrank_range_le_of_ker_le (hker (-1) (by norm_num))

theorem finrank_range_eq_of_continuousWithinAt_of_forall_lt_eq_of_range_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (A : ℝ → V →L[ℝ] W) (hA : ContinuousWithinAt A (Iio 0) 0) {q : ℕ}
    (hq : ∀ t < (0 : ℝ), Module.finrank ℝ (LinearMap.range (A t : V →ₗ[ℝ] W)) = q)
    (hnest : ∀ t < (0 : ℝ), (A t : V →ₗ[ℝ] W).range ≤ (A 0 : V →ₗ[ℝ] W).range) :
    Module.finrank ℝ (LinearMap.range (A 0 : V →ₗ[ℝ] W)) = q := by
  refine le_antisymm (finrank_range_le_of_continuousWithinAt_of_forall_lt_eq A hA hq) ?_
  rw [← hq (-1) (by norm_num)]
  exact finrank_range_le_of_range_le (hnest (-1) (by norm_num))

theorem exists_continuousWithinAt_forall_lt_finrank_range_eq :
    ∃ A : ℝ → ℝ →L[ℝ] ℝ, Continuous A ∧
      (∀ t < (0 : ℝ), Module.finrank ℝ (LinearMap.range (A t : ℝ →ₗ[ℝ] ℝ)) = 1) ∧
      Module.finrank ℝ (LinearMap.range (A 0 : ℝ →ₗ[ℝ] ℝ)) = 1 := by
  have hfin : ∀ f : ℝ →L[ℝ] ℝ, f = 1 →
      Module.finrank ℝ (LinearMap.range (f : ℝ →ₗ[ℝ] ℝ)) = 1 := by
    rintro f rfl
    rw [show ((1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = 1 from rfl]
    rw [LinearMap.finrank_range_of_inj (f := (1 : ℝ →ₗ[ℝ] ℝ)) fun x y h => h]
    exact Module.finrank_self ℝ
  exact ⟨fun _ => 1, continuous_const, fun t _ => hfin 1 rfl, hfin 1 rfl⟩

theorem not_forall_lt_ker_le_of_continuousWithinAt_countermodel :
    ∃ A : ℝ → ℝ →L[ℝ] ℝ, Continuous A ∧
      (∀ t < (0 : ℝ), Module.finrank ℝ (LinearMap.range (A t : ℝ →ₗ[ℝ] ℝ)) = 1) ∧
      ¬ (∀ t < (0 : ℝ),
        (A 0 : ℝ →ₗ[ℝ] ℝ).ker ≤ (A t : ℝ →ₗ[ℝ] ℝ).ker) ∧
      Module.finrank ℝ (LinearMap.range (A 0 : ℝ →ₗ[ℝ] ℝ)) = 0 := by
  let f : ℝ → (ℝ →L[ℝ] ℝ) := fun t => t • (1 : ℝ →L[ℝ] ℝ)
  have hcoe : ∀ t : ℝ, ((f t : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) =
      t • (1 : ℝ →ₗ[ℝ] ℝ) := fun t => rfl
  have hrank : ∀ t : ℝ, t ≠ 0 → Module.finrank ℝ
      (LinearMap.range ((f t : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ)) = 1 := by
    intro t ht
    rw [hcoe t, LinearMap.range_smul (1 : ℝ →ₗ[ℝ] ℝ) t ht]
    rw [LinearMap.finrank_range_of_inj (f := (1 : ℝ →ₗ[ℝ] ℝ)) fun x y h => h]
    exact Module.finrank_self ℝ
  have hzero : ((f 0 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = 0 := by
    rw [show f 0 = (0 : ℝ) • (1 : ℝ →L[ℝ] ℝ) from rfl, zero_smul]
    rfl
  have htop : ((f 0 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ).ker = ⊤ := by
    rw [hzero, LinearMap.ker_zero]
  have hbot : ((f (-1) : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ).ker = ⊥ := by
    rw [hcoe (-1), LinearMap.ker_smul (1 : ℝ →ₗ[ℝ] ℝ) (-1) (by norm_num),
      LinearMap.ker_eq_bot]
    intro x y hxy
    simpa using hxy
  refine ⟨f, continuous_id.smul continuous_const, fun t ht => hrank t (ne_of_lt ht), ?_, ?_⟩
  · intro h
    have hle : (⊤ : Submodule ℝ ℝ) ≤ ⊥ := by
      rw [← htop, ← hbot]
      exact h (-1) (by norm_num)
    exact one_ne_zero (by simpa using hle Submodule.mem_top)
  · rw [hzero, LinearMap.range_zero]
    exact Submodule.finrank_eq_zero.mpr rfl

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type uHF} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
  (F : PointedFlowData.{0, 0, uHF} (I := I) D)

local instance terminalRankBoundaryLimitProducerTopology : TopologicalSpace F.M := F.topology
local instance terminalRankBoundaryLimitProducerCharted : ChartedSpace H F.M := F.charted
local instance terminalRankBoundaryLimitProducerSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalRankBoundaryLimitProducerC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalRankBoundaryLimitProducerC2 : IsManifold I 2 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalRankBoundaryLimitProducerC3 : IsManifold I 3 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalRankBoundaryLimitProducerT2 : T2Space F.M := F.t2
local instance terminalRankBoundaryLimitProducerSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance terminalRankBoundaryLimitProducerInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance terminalRankBoundaryLimitProducerFiniteDimensional (x : F.M) :
    FiniteDimensional ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis ℝ (TangentSpace I x))).finiteDimensional_of_finite

noncomputable abbrev terminalSliceCurvatureOperatorAt (t : ℝ) (x : F.M) :
    (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ]
      (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
  curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric t) x
    ⟨metricRm04At (I := I) (F.S.base.metric t) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric t) x⟩

noncomputable abbrev terminalSliceCurvatureImageAt (t : ℝ) (x : F.M) :
    Submodule ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
  curvatureOperatorImageAt (I := I) (F.S.base.metric t) x
    ⟨metricRm04At (I := I) (F.S.base.metric t) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric t) x⟩

noncomputable def TerminalSliceCurvatureOperatorContinuousWithinAt : Prop :=
  ∀ x : F.M, ContinuousWithinAt (fun t : ℝ => terminalSliceCurvatureOperatorAt F t x) (Iio 0) 0

noncomputable def TerminalCurvatureKernelMonotoneAtTerminal : Prop :=
  ∀ t < (0 : ℝ), ∀ x : F.M,
    (terminalSliceCurvatureOperatorAt F 0 x).ker ≤ (terminalSliceCurvatureOperatorAt F t x).ker

omit [I.Boundaryless] in
theorem terminalSliceCurvatureOperatorAt_congr {t t' : ℝ}
    (h : F.S.base.metric t = F.S.base.metric t') (x : F.M) :
    terminalSliceCurvatureOperatorAt F t x = terminalSliceCurvatureOperatorAt F t' x := by
  exact congrArg (fun g : SmoothRiemannianMetric I F.M =>
    curvatureOperatorEndomorphismAt (I := I) g x
      ⟨metricRm04At (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩) h

omit [I.Boundaryless] in
theorem terminalSliceCurvatureOperatorContinuousWithinAt_of_metric_eq
    (h : ∀ t < (0 : ℝ), F.S.base.metric t = F.S.base.metric 0) :
    TerminalSliceCurvatureOperatorContinuousWithinAt F := by
  intro x
  refine ContinuousWithinAt.congr_of_eventuallyEq continuousWithinAt_const ?_ rfl
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact terminalSliceCurvatureOperatorAt_congr F (h t ht) x

omit [I.Boundaryless] in
theorem terminalCurvatureKernelMonotoneAtTerminal_of_metric_eq
    (h : ∀ t < (0 : ℝ), F.S.base.metric t = F.S.base.metric 0) :
    TerminalCurvatureKernelMonotoneAtTerminal F := by
  intro t ht x
  rw [terminalSliceCurvatureOperatorAt_congr F (h t ht) x]

omit [I.Boundaryless] in
theorem terminalSliceCurvatureKernel_le_of_operatorKernel_le
    (h : ∀ t < (0 : ℝ), ∀ x : F.M,
      (terminalSliceCurvatureOperatorAt F 0 x).ker ≤
        (terminalSliceCurvatureOperatorAt F t x).ker) :
    ∀ t < (0 : ℝ), ∀ x : F.M,
      curvatureOperatorKernelAt (I := I) (F.S.base.metric 0) x
          ⟨metricRm04At (I := I) (F.S.base.metric 0) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.base.metric 0) x⟩ ≤
        curvatureOperatorKernelAt (I := I) (F.S.base.metric t) x
          ⟨metricRm04At (I := I) (F.S.base.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.base.metric t) x⟩ := by
  intro t ht x
  rw [← curvatureOperatorEndomorphismAt_ker (I := I) (F.S.base.metric 0) x
      ⟨metricRm04At (I := I) (F.S.base.metric 0) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric 0) x⟩,
    ← curvatureOperatorEndomorphismAt_ker (I := I) (F.S.base.metric t) x
      ⟨metricRm04At (I := I) (F.S.base.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric t) x⟩]
  exact h t ht x

omit [I.Boundaryless] in
theorem terminalSliceCurvatureRank_eq_of_continuousWithinAt_of_forall_lt_eq_of_image_le
    (hcont : TerminalSliceCurvatureOperatorContinuousWithinAt F) {q : ℕ}
    (hq : ∀ t < (0 : ℝ), ∀ x : F.M,
      Module.finrank ℝ (terminalSliceCurvatureImageAt F t x) = q)
    (hnest : ∀ t < (0 : ℝ), ∀ x : F.M,
      terminalSliceCurvatureImageAt F t x ≤ terminalSliceCurvatureImageAt F 0 x) (x : F.M) :
    Module.finrank ℝ (terminalSliceCurvatureImageAt F 0 x) = q :=
  finrank_range_eq_of_continuousWithinAt_of_forall_lt_eq_of_range_le
    (fun t : ℝ => terminalSliceCurvatureOperatorAt F t x) (hcont x)
    (fun t ht => hq t ht x) (fun t ht => hnest t ht x)

omit [I.Boundaryless] in
theorem terminalSliceCurvatureRank_eq_of_continuousWithinAt_of_forall_lt_eq_of_kernel_le
    (hcont : TerminalSliceCurvatureOperatorContinuousWithinAt F) {q : ℕ}
    (hq : ∀ t < (0 : ℝ), ∀ x : F.M,
      Module.finrank ℝ (terminalSliceCurvatureImageAt F t x) = q)
    (hker : TerminalCurvatureKernelMonotoneAtTerminal F) (x : F.M) :
    Module.finrank ℝ (terminalSliceCurvatureImageAt F 0 x) = q :=
  finrank_range_eq_of_continuousWithinAt_of_forall_lt_eq_of_ker_le
    (fun t : ℝ => terminalSliceCurvatureOperatorAt F t x) (hcont x)
    (fun t ht => hq t ht x) (fun t ht => hker t ht x)

omit [I.Boundaryless] in
theorem exists_terminalSliceCurvatureRank_eq_of_continuousWithinAt_of_forall_lt_eq
    (hcont : TerminalSliceCurvatureOperatorContinuousWithinAt F) {q : ℕ}
    (hq : ∀ t < (0 : ℝ), ∀ x : F.M,
      Module.finrank ℝ (terminalSliceCurvatureImageAt F t x) = q)
    (hkernel : TerminalCurvatureKernelMonotoneAtTerminal F) :
    ∃ q' : ℕ, ∀ x : F.M, Module.finrank ℝ (terminalSliceCurvatureImageAt F 0 x) = q' :=
  ⟨q, fun x =>
    terminalSliceCurvatureRank_eq_of_continuousWithinAt_of_forall_lt_eq_of_kernel_le
      F hcont hq hkernel x⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.NullSectionalRicciReactionRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.NullSectionalRankRigidity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankRigidity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.SurfaceProductRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.AncientCurvatureRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureKernel

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor0SBundle

universe uHF

variable {H : Type uHF} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{0, 0, uHF} (I := I) D)

local instance terminalRankPersistenceTopology : TopologicalSpace F.M := F.topology
local instance terminalRankPersistenceCharted : ChartedSpace H F.M := F.charted
local instance terminalRankPersistenceSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalRankPersistenceC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalRankPersistenceC2 : IsManifold I 2 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalRankPersistenceT2 : T2Space F.M := F.t2

local instance terminalReductionTwoForm (x : F.M) :
    FiniteDimensional ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis ℝ (TangentSpace I x))).finiteDimensional_of_finite

omit [I.Boundaryless] in
theorem terminal_mem_nonnegativeCone
    {kappa : ℝ} (hK : KLim (I := I) kappa F) :
    ∀ x : F.M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := F.M) (F.S.base.metric 0) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
  intro x
  apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
  intro n c v w
  have h0 : (0 : ℝ) ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  have h := hK.nonnegativeCurvatureOperator 0 h0 x n c v w
  simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
    tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h

omit [I.Boundaryless] in
theorem slice_mem_nonnegativeCone
    {kappa : ℝ} (hK : KLim (I := I) kappa F) {t : ℝ} (ht : t ∈ D.carrier) :
    ∀ x : F.M,
      (⟨metricRm04At (I := I) (F.S.base.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.base.metric t) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := F.M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
  intro x
  apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
  intro n c v w
  have h := hK.nonnegativeCurvatureOperator t ht x n c v w
  simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
    tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h

theorem terminalConstantRankParallelKernel_of_null_plane_rank_ne_two
    {kappa : ℝ} (hK : KLim (I := I) kappa F)
    (hnotpos : ¬ DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
      (F.S.base.metric 0))
    (hne_two : ∀ x : F.M, ∀ a b : TangentSpace I x,
      0 < (F.S.base.metric 0).inner x a a * (F.S.base.metric 0).inner x b b -
          ((F.S.base.metric 0).inner x a b) ^ 2 →
        metricRm04StandardAt (I := I) (M := F.M) (F.S.base.metric 0) x a b b a = 0 →
          Module.finrank ℝ
            (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
              ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
                metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) (F.S.base.metric 0) x⟩) ≠ 2)
    (hrank : ∃ q : ℕ, ∀ x : F.M, Module.finrank ℝ
      (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
        ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (F.S.base.metric 0) x⟩) = q)
    (hkernel : IsParallelContinuousAlternatingSubmoduleFamily (F.S.base.metric 0)
      (fun x => curvatureOperatorKernelAt (I := I) (F.S.base.metric 0) x
        ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (F.S.base.metric 0) x⟩)) :
    TerminalConstantRankParallelKernel (I := I) F := by
  let A : ∀ x : F.M,
      algebraicCurvatureTensorSubmodule (I := I) (M := F.M) x :=
    fun x => ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (F.S.base.metric 0) x⟩
  have hdimE : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hdimx (x : F.M) : Module.finrank ℝ (TangentSpace I x) = 3 :=
    (show Module.finrank ℝ (TangentSpace I x) =
      Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) from rfl).trans hdimE
  have hcone := terminal_mem_nonnegativeCone F hK
  have hnotAll : ¬ ∀ x : F.M,
      CurvatureOperatorPositiveAt (I := I) (M := F.M) (F.S.base.metric 0) x :=
    fun h => hnotpos
      ((hasPositiveSectionalCurvature_iff_forall_curvatureOperatorPositiveAt
        (I := I) (M := F.M) (F.S.base.metric 0) hdimE).mpr h)
  obtain ⟨x₀, a, b, hgram, hsec⟩ :=
    exists_nullPlane_of_not_forall_curvatureOperatorPositiveAt (I := I) (M := F.M)
      (F.S.base.metric 0) hdimE hcone hnotAll
  have hmin_le : leastCurvatureOperatorEigenvalueAt (I := I) (F.S.base.metric 0) x₀
      (A x₀) ≤ 0 := by
    obtain ⟨basis, horth⟩ :=
      exists_orthonormalBasisAt (I := I) (F.S.base.metric 0) x₀ (hdimx x₀)
    have hbound : curvatureOperatorLowerBoundAt (I := I) (F.S.base.metric 0) x₀ (A x₀)
        (-(leastCurvatureOperatorEigenvalueAt (I := I) (F.S.base.metric 0) x₀
          (A x₀))) :=
      (curvatureOperatorLowerBoundAt_iff_neg_leastCurvatureOperatorEigenvalueAt_le
        (I := I) (g := F.S.base.metric 0) (x := x₀) (A := A x₀)
        basis horth).mpr le_rfl
    have hquad := hbound 1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b)
    have hquad0 : algebraicCurvatureOperatorQuadraticEval (I := I) (M := F.M) (A x₀)
        (fun _ : Fin 1 => 1) (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) = 0 := by
      simpa only [A, metricRm04_apply, algebraicCurvatureOperatorQuadraticEval,
        Fin.sum_univ_one, one_mul, metricRm04StandardAt] using hsec
    have hidpos : 0 < algebraicCurvatureIdentityQuadraticEval (I := I)
        (F.S.base.metric 0) (fun _ : Fin 1 => 1) (fun _ : Fin 1 => a)
        (fun _ : Fin 1 => b) := by
      simpa only [algebraicCurvatureIdentityQuadraticEval, Fin.sum_univ_one, one_mul,
        (F.S.base.metric 0).symm x₀ b a, ← pow_two, one_pow] using hgram
    rw [hquad0, zero_add] at hquad
    nlinarith [hquad, hidpos]
  have hne_three : Module.finrank ℝ
      (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x₀ (A x₀)) ≠ 3 := by
    intro hthree
    have hpos := leastCurvatureOperatorEigenvalueAt_pos_of_image_finrank_eq_three
      (I := I) (M := F.M) (F.S.base.metric 0) x₀ (hdimx x₀) (A x₀)
      (by simpa only [A, metricRm04_apply, metricAlgebraicCurvatureTensorAt] using hcone x₀) hthree
    linarith
  have hle_three : Module.finrank ℝ
      (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x₀ (A x₀)) ≤ 3 := by
    have hfiber : Module.finrank ℝ
        (TangentSpace I x₀ [⋀^Fin 2]→L[ℝ] ℝ) = 3 := by
      rw [ContinuousAlternatingMap.finrank_continuousAlternatingMap, hdimx x₀]
      norm_num
    exact (Submodule.finrank_le _).trans_eq hfiber
  have hne_two_x₀ : Module.finrank ℝ
      (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x₀ (A x₀)) ≠ 2 := by
    simpa only [A, metricRm04_apply] using hne_two x₀ a b hgram hsec
  obtain ⟨q, hq⟩ := hrank
  have hq01 : q = 0 ∨ q = 1 := by
    have hqx : Module.finrank ℝ
        (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x₀ (A x₀)) = q := by
      simpa only [A] using hq x₀
    omega
  refine ⟨q, ?_, ?_, hkernel⟩
  · rcases hq01 with h | h <;> simp [h]
  · simpa only [A] using hq

theorem terminalConstantRankParallelKernel_of_reaction_annihilation_on_kernel
    {kappa : ℝ} (hK : KLim (I := I) kappa F)
    (hnotpos : ¬ DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
      (F.S.base.metric 0))
    (hnull : ∀ x : F.M, ∀ v : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
      curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric 0) x
          ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.base.metric 0) x⟩ v = 0 →
        curvatureOperatorReactionEndomorphism3
          (curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric 0) x
            ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (F.S.base.metric 0) x⟩).toLinearMap v = 0)
    (hrank : ∃ q : ℕ, ∀ x : F.M, Module.finrank ℝ
      (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
        ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (F.S.base.metric 0) x⟩) = q)
    (hkernel : IsParallelContinuousAlternatingSubmoduleFamily (F.S.base.metric 0)
      (fun x => curvatureOperatorKernelAt (I := I) (F.S.base.metric 0) x
        ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (F.S.base.metric 0) x⟩)) :
    TerminalConstantRankParallelKernel (I := I) F := by
  refine terminalConstantRankParallelKernel_of_kernelParallel F hK hnotpos ?_ hrank hkernel
  intro x
  have hdimE : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hdimx : Module.finrank ℝ (TangentSpace I x) = 3 :=
    (show Module.finrank ℝ (TangentSpace I x) =
      Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) from rfl).trans hdimE
  have htwo : Module.finrank ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) = 3 := by
    rw [ContinuousAlternatingMap.finrank_continuousAlternatingMap, hdimx]
    norm_num
  have hne := curvatureOperatorEndomorphism_finrank_range_ne_two_of_metric
    (D := twoFormMetricData (I := I) (F.S.base.metric 0) x) htwo
    (curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric 0) x
      ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.base.metric 0) x⟩).toLinearMap
    (curvatureOperatorEndomorphismAt_isSymmetric (I := I) (F.S.base.metric 0) x _)
    (fun v => curvatureOperatorEndomorphismAt_inner_nonneg_of_mem_nonnegativeCone
      hdimE (F.S.base.metric 0) x _ (terminal_mem_nonnegativeCone F hK x) v)
    (hnull x)
  exact hne

theorem exists_terminal_slice_constant_rank_and_parallel_kernel
    [ConnectedSpace F.M]
    {kappa : ℝ} (hK : KLim (I := I) kappa F)
    (hreg : Set.Iio (0 : ℝ) ⊆ D.regular) :
    ∃ t₀ < (0 : ℝ), ∃ q : ℕ, (q = 0 ∨ q = 1 ∨ q = 3) ∧
      (∀ t ≤ t₀, ∀ x : F.M, Module.finrank ℝ
        (curvatureOperatorImageAt (I := I) (F.S.base.metric t) x
          ⟨metricRm04At (I := I) (F.S.base.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.base.metric t) x⟩) = q) ∧
      (∀ t < t₀, IsParallelContinuousAlternatingSubmoduleFamily (F.S.base.metric t)
        (fun x => curvatureOperatorKernelAt (I := I) (F.S.base.metric t) x
          ⟨metricRm04At (I := I) (F.S.base.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.base.metric t) x⟩)) := by
  have hdimE : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hR : ∀ t < (0 : ℝ), ∀ x : F.M,
      (⟨metricRm04At (I := I) (F.S.base.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.base.metric t) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := F.M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) :=
    fun t ht => slice_mem_nonnegativeCone F hK
      (by simpa only [hK.carrier_eq, Set.mem_Iic] using ht.le)
  obtain ⟨t₀, ht₀, q, hq, hconst⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_curvatureOperatorImageAt_finrank_eq_on_past_interval
      F.S F.isSolution hdimE hreg hR
  refine ⟨t₀, ht₀, q, hq, ?_, ?_⟩
  · intro t ht x
    exact hconst t ht x
  · intro t htt₀
    have hmid : t < (t + t₀) / 2 := by linarith
    have hle : (t + t₀) / 2 ≤ t₀ := by linarith
    refine DifferentialGeometry.PDE.RicciFlow.curvatureOperatorKernelAt_parallel_of_constant_rank
      F.S F.isSolution hdimE (a := t - 1) (b := (t + t₀) / 2) (t := t)
      ⟨by linarith, hmid⟩ ?_ ?_ q ?_
    · intro r hr
      have hr0 : r < 0 := by linarith [hr.2, hle, ht₀]
      exact hreg hr0
    · intro r hr
      have hr0 : r < 0 := by linarith [hr.2, hle, ht₀]
      exact hR r hr0
    · intro r hr
      have hrt : r ≤ t₀ := by linarith [hr.2, hle]
      exact hconst r hrt

section TerminalProductRankWitness

variable {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
variable {H₂ : Type*} [TopologicalSpace H₂]
variable {I₂ : ModelWithCorners ℝ E₂ H₂} [I₂.Boundaryless]
variable {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂] [T2Space M₂]

theorem curvatureOperatorImageAt_finrank_prod_real_eq_one
    (g₂ : SmoothRiemannianMetric I₂ M₂) (hdim : Module.finrank ℝ E₂ = 2) (x : M₂ × ℝ)
    (hscalar : metricScalarAt (I := I₂) g₂ x.1 ≠ 0) :
    Module.finrank ℝ
      (curvatureOperatorImageAt (g₂.prod (euclideanMetric (E := ℝ))) x
        ⟨metricRm04At (g₂.prod (euclideanMetric (E := ℝ))) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (g₂.prod (euclideanMetric (E := ℝ))) x⟩) = 1 :=
  curvatureOperatorImageAt_finrank_prod_real_eq_one_of_scalar_ne_zero g₂ hdim x hscalar

theorem curvatureOperatorImageAt_finrank_prod_real_ne_two
    (g₂ : SmoothRiemannianMetric I₂ M₂) (hdim : Module.finrank ℝ E₂ = 2) (x : M₂ × ℝ)
    (hscalar : metricScalarAt (I := I₂) g₂ x.1 ≠ 0) :
    Module.finrank ℝ
      (curvatureOperatorImageAt (g₂.prod (euclideanMetric (E := ℝ))) x
        ⟨metricRm04At (g₂.prod (euclideanMetric (E := ℝ))) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (g₂.prod (euclideanMetric (E := ℝ))) x⟩) ≠ 2 := by
  rw [curvatureOperatorImageAt_finrank_prod_real_eq_one g₂ hdim x hscalar]
  omega

end TerminalProductRankWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

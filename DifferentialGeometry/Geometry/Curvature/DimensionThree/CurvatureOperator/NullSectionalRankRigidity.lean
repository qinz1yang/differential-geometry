import DifferentialGeometry.Geometry.Connection.ParallelTransport.Kernel
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorPositiveSectional
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalConstantRankFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalCurvatureTrichotomy

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open DifferentialGeometry.Tensor0SBundle

theorem map_eq_zero_of_inner_map_self_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (D : MetricFiberData V) (A : V →ₗ[ℝ] V)
    (hsymm : D.IsSymmetric A) (hnonneg : ∀ v : V, 0 ≤ D.inner (A v) v)
    {v : V} (hzero : D.inner (A v) v = 0) : A v = 0 := by
  let addV : AddCommGroup V := inferInstance
  let modV : Module ℝ V := inferInstance
  let : InnerProductSpace.Core ℝ V := D.toCore
  let : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ V _ addV modV D.toCore
  let : AddCommGroup V := addV
  let : Module ℝ V := modV
  let : InnerProductSpace ℝ V := @InnerProductSpace.ofCore ℝ V _ _ _ D.toCore.toCore
  have hsymm' : A.IsSymmetric := by
    intro x y
    rw [MetricFiberData.toCore_inner D, MetricFiberData.toCore_inner D]
    exact hsymm x y
  have hnonneg' : ∀ x : V, 0 ≤ ⟪A x, x⟫ := by
    intro x
    rw [MetricFiberData.toCore_inner D]
    exact hnonneg x
  have hzero' : ⟪A v, v⟫ = 0 := by
    rw [MetricFiberData.toCore_inner D]
    exact hzero
  have hkey : ∀ w : V, ⟪A v, w⟫ = 0 := by
    intro w
    have hsym : ⟪A w, v⟫ = ⟪A v, w⟫ :=
      (hsymm' w v).trans (real_inner_comm _ _)
    have hquad : ∀ t : ℝ, 0 ≤ 2 * t * ⟪A v, w⟫ + t ^ 2 * ⟪A w, w⟫ := by
      intro t
      have h := hnonneg' (v + t • w)
      have hexp : ⟪A (v + t • w), v + t • w⟫ =
          2 * t * ⟪A v, w⟫ + t ^ 2 * ⟪A w, w⟫ := by
        simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
          real_inner_smul_right, hsym, hzero', zero_add]
        ring
      rwa [hexp] at h
    set x : ℝ := ⟪A v, w⟫ with hx
    set c : ℝ := ⟪A w, w⟫ with hc
    have hcnonneg : 0 ≤ c := by
      rw [hc]
      exact hnonneg' w
    have hden : (0 : ℝ) < (c + 1) ^ 2 := by nlinarith
    have htwo : 0 < c + 2 := by linarith
    have hexp2 : 2 * (-(x) / (c + 1)) * x + (-(x) / (c + 1)) ^ 2 * c =
        -(x ^ 2 * (c + 2)) / (c + 1) ^ 2 := by
      field_simp
      ring
    have hw := hquad (-(x) / (c + 1))
    rw [hexp2] at hw
    have hnum_nonpos : -(x ^ 2 * (c + 2)) ≤ 0 := by nlinarith [sq_nonneg x, htwo]
    have hquot_nonpos : -(x ^ 2 * (c + 2)) / (c + 1) ^ 2 ≤ 0 := by
      rw [div_le_iff₀ hden]
      simpa using hnum_nonpos
    have hquot_zero : -(x ^ 2 * (c + 2)) / (c + 1) ^ 2 = 0 :=
      le_antisymm hquot_nonpos hw
    have hnum_zero : -(x ^ 2 * (c + 2)) = 0 := by
      rcases (div_eq_zero_iff).mp hquot_zero with h | h
      · exact h
      · exact absurd h (ne_of_gt hden)
    have hprod : x ^ 2 * (c + 2) = 0 := by linarith
    have hx2 : x ^ 2 = 0 := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt htwo)
    have hxzero : x = 0 := by
      have : x * x = 0 := by simpa [pow_two] using hx2
      exact mul_self_eq_zero.mp this
    exact hxzero
  exact ext_inner_right ℝ (fun w => by simpa using hkey w)

theorem finrank_range_lt_of_metric_inner_map_self_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (D : MetricFiberData V) (A : V →ₗ[ℝ] V)
    (hsymm : D.IsSymmetric A) (hnonneg : ∀ v : V, 0 ≤ D.inner (A v) v)
    {v : V} (hv : v ≠ 0) (hzero : D.inner (A v) v = 0) :
    Module.finrank ℝ A.range < Module.finrank ℝ V := by
  have hker : v ∈ A.ker := LinearMap.mem_ker.mpr (map_eq_zero_of_inner_map_self_eq_zero D A hsymm hnonneg hzero)
  have hkerne : A.ker ≠ ⊥ := by
    intro hbot
    have : v ∈ (⊥ : Submodule ℝ V) := by rw [← hbot]; exact hker
    exact hv (by simpa using this)
  have hkerpos : 0 < Module.finrank ℝ A.ker := by
    refine Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hker⟩, ?_⟩
    simpa using hv
  have hsum := A.finrank_range_add_finrank_ker
  omega


section NullSectionalRank

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M]

theorem metricCurvatureOperatorRankAt_eq_zero_or_one_of_null_sectional
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3)
    (hcone : metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hdefect : ricciReactionDefectAt (I := I) g x = 0)
    {a b : TangentSpace I x}
    (hgram : 0 < g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2)
    (hsec : metricRm04StandardAt (I := I) (M := M) g x a b b a = 0) :
    metricCurvatureOperatorRankAt (I := I) g x hdim = 0 ∨
      metricCurvatureOperatorRankAt (I := I) g x hdim = 1 := by
  have hlin : LinearIndependent ℝ (vec2 a b) := by
    have hvec : vec2 a b = ![a, b] := by
      funext i
      fin_cases i <;> simp [vec2]
    rw [hvec]
    exact Geometry.Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos
      (I := I) g x a b
      (by simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using hgram)
  have hne : metricCurvatureOperatorRankAt (I := I) g x hdim ≠ 3 := by
    intro hthree
    have hpos := metricRm04StdAt_pos_of_metricCurvatureOperatorRankAt_eq_three_of_nonnegative
      (I := I) (M := M) g x hdim hthree hcone a b hlin
    rw [hsec] at hpos
    exact lt_irrefl 0 hpos
  have htri :=
    metricCurvatureOperatorRankAt_eq_zero_or_one_or_three_of_nonnegative_of_ricciReactionDefectAt_eq_zero
      (I := I) (M := M) g x hdim hcone hdefect
  omega

end NullSectionalRank

end DifferentialGeometry.Geometry.Curvature.DimensionThree

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Riemannian

universe uHF

variable {H : Type uHF} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{0, 0, uHF} (I := I) D)

local instance terminalRankKernelTopology : TopologicalSpace F.M := F.topology
local instance terminalRankKernelCharted : ChartedSpace H F.M := F.charted
local instance terminalRankKernelSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalRankKernelC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalRankKernelC2 : IsManifold I 2 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalRankKernelT2 : T2Space F.M := F.t2

theorem terminalConstantRankParallelKernel_of_kernelParallel
    {kappa : ℝ} (hK : KLim (I := I) kappa F)
    (hnotpos : ¬ DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
      (F.S.base.metric 0))
    (hne_two : ∀ x : F.M, Module.finrank ℝ
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
  have hcone : ∀ x : F.M,
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
  obtain ⟨q, hq⟩ := hrank
  have hq01 : q = 0 ∨ q = 1 := by
    have hqx : Module.finrank ℝ
        (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x₀ (A x₀)) = q := by
      simpa only [A] using hq x₀
    have hne2 : Module.finrank ℝ
        (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x₀ (A x₀)) ≠ 2 := by
      simpa only [A] using hne_two x₀
    omega
  refine ⟨q, ?_, ?_, hkernel⟩
  · rcases hq01 with h | h <;> simp [h]
  · simpa only [A] using hq

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

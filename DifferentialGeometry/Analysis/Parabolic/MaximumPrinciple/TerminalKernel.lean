import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Reaction
import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle
import DifferentialGeometry.Bundle.SmoothSubbundle.Kernel
import DifferentialGeometry.Geometry.Connection.ParallelTransport.SubbundleInvariance
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped Manifold ContDiff Topology InnerProductSpace BigOperators

namespace PositiveSystem

open DifferentialGeometry DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

private theorem terminal_derivative_inner_nonpos
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {A : ℝ → W →L[ℝ] W} {B : W →L[ℝ] W} {a b : ℝ}
    (hab : a < b) (hd : HasDerivWithinAt A B (Iic b) b)
    (hpos : ∀ t ∈ Icc a b, (A t).IsPositive)
    (v : W) (hv : A b v = 0) : inner ℝ (B v) v ≤ 0 := by
  have heval := hd.clm_apply (hasDerivWithinAt_const b (Iic b) v)
  simp only [map_zero, add_zero] at heval
  have hscalar := heval.inner ℝ (hasDerivWithinAt_const b (Iic b) v)
  simp only [inner_zero_right, zero_add] at hscalar
  have hlim : Tendsto (slope (fun t => inner ℝ (A t v) v) b)
      (𝓝[<] b) (𝓝 (inner ℝ (B v) v)) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : b ∉ Iio b)).mp
      (hscalar.mono Iio_subset_Iic_self)
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hab] with t ht
  rw [slope_def_field, hv, inner_zero_left, sub_zero]
  exact div_nonpos_of_nonneg_of_nonpos
    ((hpos t ⟨ht.1.le, ht.2.le⟩).inner_nonneg_left v) (sub_nonpos.mpr ht.2.le)

private theorem local_kernel_covariantDerivatives_mem_of_nonpos
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (A : Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    {x : M} (hA : ∀ y, (A y).toLinearMap.IsSymmetric)
    (hApos : (A x).IsPositive) (Z : TangentSpace I x)
    (B : V x →L[ℝ] V x) (w : Cₛ^∞⟮I; F, V⟯)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U)
    (hw : ∀ y ∈ U, A y (w y) = 0)
    (hB : 0 ≤ inner ℝ (B (w x)) (w x))
    (hL : inner ℝ
      ((rawBundleEndomorphismConnLap (I := I) g cov (fun y => A y) x +
        HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov (fun y => A y) x Z + B) (w x)) (w x) ≤ 0) :
    (∀ Y : TangentSpace I x, cov (fun y => w y) x Y ∈ (A x).ker) ∧
      inner ℝ (B (w x)) (w x) = 0 := by
  have hdrift :=
    HomConnectionGen.inner_homBundleCovariantDerivativeGen_apply_of_eventually_mem_ker
      cov A hA w hU hxU hw Z
  have hlap := inner_rawBundleEndomorphismConnLap_apply_of_eventually_mem_ker
    g cov hcov A hA w hU hxU hw
  simp only [add_apply, inner_add_left, hlap, hdrift, add_zero] at hL
  have hnonneg : 0 ≤ ∑ i : Fin (Module.finrank ℝ E),
      inner ℝ (A x (cov (fun y => w y) x (smoothOrthoFrame g x i x)))
        (cov (fun y => w y) x (smoothOrthoFrame g x i x)) :=
    Finset.sum_nonneg fun i _ => hApos.inner_nonneg_left _
  have hidentity : 2 * ∑ i : Fin (Module.finrank ℝ E),
      inner ℝ (A x (cov (fun y => w y) x (smoothOrthoFrame g x i x)))
        (cov (fun y => w y) x (smoothOrthoFrame g x i x)) +
      inner ℝ (B (w x)) (w x) = 0 := by linarith
  have hmain := kernel_derivatives_mem_and_reaction_inner_eq_zero hApos
    (fun i => cov (fun y => w y) x (smoothOrthoFrame g x i x)) (w x) hB hidentity
  refine ⟨?_, hmain.2⟩
  intro Y
  by_cases hdim : Module.finrank ℝ E = 0
  · have hY : Y = 0 :=
      (finrank_zero_iff_forall_zero.mp (show
        Module.finrank ℝ (TangentSpace I x) = 0 from hdim)) Y
    rw [hY, map_zero]
    exact Submodule.zero_mem _
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame g x i x
  let P : Submodule ℝ (TangentSpace I x) :=
    (A x).ker.comap (cov (fun y => w y) x).toLinearMap
  have he : ⊤ ≤ Submodule.span ℝ (range e) :=
    (smoothOrtho_isLocal g x).generating
      (mem_smoothOrthoFrameNeighborhood_self (I := I) (M := M) x)
  have hrange : range e ⊆ P := by
    rintro Z ⟨i, rfl⟩
    exact hmain.1 i
  exact (Submodule.span_le.mpr hrange) (he Submodule.mem_top)

theorem local_kernel_section_covariantDerivative_mem_and_reaction_inner_eq_zero_at_right_endpoint
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    {a b : ℝ} (hab : a < b) {x : M}
    (hA : ∀ y, (A b y).toLinearMap.IsSymmetric)
    (hApos : ∀ t ∈ Icc a b, (A t x).IsPositive)
    (Z : TangentSpace I x) (B : V x →L[ℝ] V x)
    (w : Cₛ^∞⟮I; F, V⟯) {U : Set M} (hU : IsOpen U) (hxU : x ∈ U)
    (hw : ∀ y ∈ U, A b y (w y) = 0)
    (hB : 0 ≤ inner ℝ (B (w x)) (w x))
    (hevolution : HasDerivWithinAt (fun t => A t x)
      (rawBundleEndomorphismConnLap (I := I) g cov (fun y => A b y) x +
        HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov (fun y => A b y) x Z + B) (Iic b) b) :
    (∀ Y : TangentSpace I x, cov (fun y => w y) x Y ∈ (A b x).ker) ∧
      inner ℝ (B (w x)) (w x) = 0 := by
  exact local_kernel_covariantDerivatives_mem_of_nonpos g cov hcov (A b) hA
    (hApos b ⟨hab.le, le_rfl⟩) Z B w hU hxU hw hB
    (terminal_derivative_inner_nonpos hab hevolution hApos (w x) (hw x hxU))

theorem kernel_isCovariantlyInvariant_at_right_endpoint
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    {a b : ℝ} (hab : a < b)
    (hApos : ∀ t ∈ Icc a b, ∀ x, (A t x).IsPositive)
    (Z : ∀ x, TangentSpace I x) (B : ∀ x, V x →L[ℝ] V x)
    (hB : ∀ x v, A b x v = 0 → 0 ≤ inner ℝ (B x v) v)
    (hevolution : ∀ x, HasDerivWithinAt (fun t => A t x)
      (rawBundleEndomorphismConnLap (I := I) g cov (fun y => A b y) x +
        HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov (fun y => A b y) x (Z x) + B x) (Iic b) b) :
    IsCovariantlyInvariantSubmoduleFamily cov (fun x => (A b x).ker) := by
  intro w U hU hw x hx Y
  have hwzero : ∀ y ∈ U, A b y (w y) = 0 :=
    fun y hy => LinearMap.mem_ker.mp (hw y hy)
  exact (local_kernel_section_covariantDerivative_mem_and_reaction_inner_eq_zero_at_right_endpoint
    g cov hcov A hab
    (fun y => (hApos b ⟨hab.le, le_rfl⟩ y).toLinearMap.isSymmetric)
    (fun t ht => hApos t ht x) (Z x) (B x) w hU hx hwzero
    (hB x _ (hwzero x hx)) (hevolution x)).1 Y


theorem exists_parallel_kernel_at_right_endpoint_of_constant_rank
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    {a b : ℝ} (hab : a < b)
    (hApos : ∀ t ∈ Icc a b, ∀ x, (A t x).IsPositive)
    (Z : ∀ x, TangentSpace I x) (B : ∀ x, V x →L[ℝ] V x)
    (hB : ∀ x v, A b x v = 0 → 0 ≤ inner ℝ (B x v) v)
    (hevolution : ∀ x, HasDerivWithinAt (fun t => A t x)
      (rawBundleEndomorphismConnLap (I := I) g cov (fun y => A b y) x +
        HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov (fun y => A b y) x (Z x) + B x) (Iic b) b)
    (k : ℕ) (hker : ∀ x, Module.finrank ℝ (A b x).ker = k) :
    ∃ K : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞),
      K.rank = k ∧ (∀ x, K.fiber x = (A b x).ker) ∧
      IsCovariantlyInvariantSubmoduleFamily cov K.fiber ∧
      cov.IsParallelSet {p : TotalSpace F V | p.2 ∈ K.fiber p.1} ∧
      ∀ x v, A b x v = 0 → inner ℝ (B x v) v = 0 := by
  let _ : ∀ x, FiniteDimensional ℝ (V x) := fun x =>
    VectorBundle.finiteDimensional ℝ F V x
  obtain ⟨K, hKrank, hK⟩ := ContMDiffVectorSubbundle.exists_smooth_kernel
    (fun x => A b x) (A b).contMDiff k hker
  have hinv : IsCovariantlyInvariantSubmoduleFamily cov K.fiber := by
    rw [show K.fiber = fun x => (A b x).ker from funext hK]
    exact kernel_isCovariantlyInvariant_at_right_endpoint g cov hcov A hab hApos
      Z B hB hevolution
  refine ⟨K, hKrank, hK, hinv,
    K.isParallelSet_of_covariantly_invariant cov hinv inferInstance, ?_⟩
  intro x v hv
  let _ := K.totalSpaceTopology
  let _ := K.fiberBundle
  let _ := K.vector_bundle
  let _ := K.contMDiffVectorBundle
  have hvK : v ∈ K.fiber x := by
    rw [hK x]
    exact LinearMap.mem_ker.mpr hv
  obtain ⟨σ, hσ⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Fin K.rank → ℝ) (V := fun y => K.fiber y) (n := (⊤ : ℕ∞)) x ⟨v, hvK⟩
  let w : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y => (σ y : V y), K.contMDiff_subtypeVal.comp σ.contMDiff⟩
  have hw : ∀ y ∈ (univ : Set M), A b y (w y) = 0 := by
    intro y _
    exact LinearMap.mem_ker.mp ((hK y) ▸ (σ y).property)
  have hwx : w x = v := congrArg Subtype.val hσ
  have h := (local_kernel_section_covariantDerivative_mem_and_reaction_inner_eq_zero_at_right_endpoint
    g cov hcov A hab
    (fun y => (hApos b ⟨hab.le, le_rfl⟩ y).toLinearMap.isSymmetric)
    (fun t ht => hApos t ht x) (Z x) (B x) w isOpen_univ (mem_univ x) hw
    (hB x _ (hw x (mem_univ x))) (hevolution x)).2
  simpa only [hwx] using h

end PositiveSystem

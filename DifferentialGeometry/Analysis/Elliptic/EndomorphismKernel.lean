import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle
import DifferentialGeometry.Analysis.Spectral.LowerKyFan

noncomputable section

open Bundle CovariantDerivative
open scoped Manifold ContDiff BigOperators Topology InnerProductSpace

namespace DifferentialGeometry.Analysis.Elliptic

open DifferentialGeometry.Geometry.Connection

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

theorem kernel_isCovariantlyInvariant_of_laplacian_add_drift_nonpos_on_kernel
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (A : Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (hA : ∀ x, (A x).IsPositive) (Z : ∀ x, TangentSpace I x)
    (hlap : ∀ x v, A x v = 0 →
      inner ℝ ((rawBundleEndomorphismConnLap g cov (fun y => A y) x +
        HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov (fun y => A y) x (Z x)) v) v ≤ 0) :
    IsCovariantlyInvariantSubmoduleFamily cov (fun x => (A x).ker) := by
  let _ : ∀ x, FiniteDimensional ℝ (V x) :=
    fun x => VectorBundle.finiteDimensional ℝ F V x
  intro w U hU hw x hx Y
  have hwzero : ∀ y ∈ U, A y (w y) = 0 :=
    fun y hy => LinearMap.mem_ker.mp (hw y hy)
  have hidentity := inner_rawBundleEndomorphismConnLap_apply_of_eventually_mem_ker
    g cov hcov A (fun y => (hA y).toLinearMap.isSymmetric) w hU hx hwzero
  have hnonpos := hlap x (w x) (hwzero x hx)
  have hdrift :=
    HomConnectionGen.inner_homBundleCovariantDerivativeGen_apply_of_eventually_mem_ker
      cov A (fun y => (hA y).toLinearMap.isSymmetric) w hU hx hwzero (Z x)
  simp only [add_apply, inner_add_left, hidentity, hdrift, add_zero] at hnonpos
  let e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  have hterm (i : Fin (Module.finrank ℝ E)) :
      0 ≤ inner ℝ (A x (cov (fun y => w y) x (e i))) (cov (fun y => w y) x (e i)) :=
    (hA x).inner_nonneg_left _
  have hsum : ∑ i, inner ℝ (A x (cov (fun y => w y) x (e i)))
      (cov (fun y => w y) x (e i)) = 0 := by
    apply le_antisymm
    · dsimp only [e]
      linarith
    · exact Finset.sum_nonneg fun i _ => hterm i
  have hall := (Fintype.sum_eq_zero_iff_of_nonneg hterm).mp hsum
  have hmain (i : Fin (Module.finrank ℝ E)) : cov (fun y => w y) x (e i) ∈ (A x).ker :=
    LinearMap.mem_ker.mpr (((hA x).toLinearMap.inner_apply_self_eq_zero_iff _).mp
      (congrFun hall i))
  by_cases hdim : Module.finrank ℝ E = 0
  · have hY : Y = 0 :=
      (finrank_zero_iff_forall_zero.mp (show
        Module.finrank ℝ (TangentSpace I x) = 0 by exact hdim)) Y
    rw [hY, map_zero]
    exact Submodule.zero_mem _
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let P : Submodule ℝ (TangentSpace I x) :=
    (A x).ker.comap (cov (fun y => w y) x).toLinearMap
  have he : ⊤ ≤ Submodule.span ℝ (Set.range e) :=
    (smoothOrtho_isLocal (I := I) g x).generating
      (mem_smoothOrthoFrameNeighborhood_self (I := I) (M := M) x)
  have hrange : Set.range e ⊆ P := by
    rintro Z ⟨i, rfl⟩
    exact hmain i
  exact (Submodule.span_le.mpr hrange) (he Submodule.mem_top)

end DifferentialGeometry.Analysis.Elliptic

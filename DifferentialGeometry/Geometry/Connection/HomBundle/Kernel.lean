import DifferentialGeometry.Geometry.Connection.HomBundle.Basic

noncomputable section

open Bundle DifferentialGeometry
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

theorem hom_apply_of_eventually_mem_ker
    (cov : CovariantDerivative I F V)
    (A : Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (w : Cₛ^∞⟮I; F, V⟯) {x : M} {U : Set M}
    (hU : IsOpen U) (hxU : x ∈ U) (hw : ∀ y ∈ U, A y (w y) = 0)
    (v : TangentSpace I x) :
    (hom I M F V F V cov cov A x v) (w x) =
      -A x (cov w x v) := by
  let Aw : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y => A y (w y),
      ContMDiff.clm_bundle_apply (b := id) A.contMDiff w.contMDiff⟩
  have hcovAw : cov (fun y => Aw y) x = 0 := by
    have hzeroDiff : MDiffAt (T% fun y : M => (0 : V y)) x :=
      mdifferentiableAt_zeroSection (𝕜 := ℝ) (F := F) (E := V) (IB := I)
    have hEq : ∀ᶠ y in 𝓝 x, Aw y = (0 : V y) :=
      Filter.eventually_of_mem (hU.mem_nhds hxU) hw
    have hcovEq := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      Aw.mdifferentiableAt hzeroDiff Filter.univ_mem hEq
    rw [hcovEq]
    exact congrArg (fun phi => phi x) cov.zero
  have happly := hom_apply
    I M F V F V cov cov A w x v
  change
    (hom I M F V F V cov cov
        (fun y => A y) x v) (w x) =
      cov (fun y => Aw y) x v - A x (cov (fun y => w y) x v) at happly
  rw [hcovAw] at happly
  simpa using happly

end CovariantDerivative

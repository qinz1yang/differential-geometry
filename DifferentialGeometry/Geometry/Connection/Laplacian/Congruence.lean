import DifferentialGeometry.Geometry.Connection.Laplacian.Map

noncomputable section

open Bundle CovariantDerivative
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

theorem rawBundleConnLap_congr
    (D C : CovariantDerivative I F V) (hD : ContMDiffCovariantDerivative D ∞)
    (hDC : ∀ (σ : Cₛ^∞⟮I; F, V⟯) (y : M), D σ y = C σ y)
    (g : SmoothRiemannianMetric I M) (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    rawBundleConnLap g D σ x = rawBundleConnLap g C σ x := by
  unfold rawBundleConnLap
  apply Finset.sum_congr rfl
  intro i _
  let _ : NeZero (Module.finrank ℝ E) :=
    ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
  let Z : Cₛ^∞⟮I; E, TangentSpace I⟯ := ⟨smoothOrthoFrame g x i, smoothOrthoFrame_smooth g x i⟩
  have hDσ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun y => (⟨y, D σ y⟩ : TotalSpace (E →L[ℝ] F)
        (fun y => TangentSpace I y →L[ℝ] V y))) := by
    rw [← contMDiffOn_univ]
    exact hD.contMDiff.contMDiff (by simpa using σ.contMDiff.contMDiffOn)
  let τ : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y => D σ y (Z y), hDσ.clm_bundle_apply Z.contMDiff⟩
  have hfirst : (fun y => D σ y (Z y)) = (fun y => C σ y (Z y)) := by
    funext y
    rw [hDC σ y]
  change D τ x (Z x) - D σ x (LeviCivita g Z x (Z x)) = _
  rw [hDC τ x, hDC σ x]
  congr 1
  exact congrArg (fun s => C s x (Z x)) hfirst

end DifferentialGeometry.Geometry.Connection

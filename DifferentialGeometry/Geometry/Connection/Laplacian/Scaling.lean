import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundleTrace
import DifferentialGeometry.Geometry.Connection.Laplacian.Map
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling

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
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

theorem rawBundleConnLap_scaleMetric
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (D : CovariantDerivative I F V) {σ : ∀ x, V x} {x : M}
    (hDσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] F))
      (fun y => (⟨y, D σ y⟩ : TotalSpace (E →L[ℝ] F)
        (fun y => TangentSpace I y →L[ℝ] V y))) x) :
    rawBundleConnLap (scaleMetric c hc g) D σ x = c⁻¹ • rawBundleConnLap g D σ x := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : IsEmpty (Fin (Module.finrank ℝ E)) := by
      simpa [hdim] using (Fin.isEmpty : IsEmpty (Fin 0))
    simp [rawBundleConnLap]
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let e := fun i => smoothOrthoFrame g x i x
  have he : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0 :=
    smoothOrthoFrame_orthonormal_at_center g x
  have hes : ∀ i j, (scaleMetric c hc g).inner x
      ((Real.sqrt c)⁻¹ • e i) ((Real.sqrt c)⁻¹ • e j) = if i = j then 1 else 0 := by
    intro i j
    rw [scaleMetric_inner_inv_sqrt_smul, he]
  rw [rawBundleConnLap_eq_sum_hessian_of_orthonormal (scaleMetric c hc g) D hDσ
    (fun i => (Real.sqrt c)⁻¹ • e i) hes,
    rawBundleConnLap_eq_sum_hessian_of_orthonormal g D hDσ e he, Finset.smul_sum]
  have hconn : LeviCivita (scaleMetric c hc g) = LeviCivita g := lcConn_scaleMetric c hc g
  rw [hconn]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_smul, smul_apply, smul_smul]
  rw [← pow_two, inv_pow, Real.sq_sqrt hc.le]

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]

theorem rawBundleConnLap_scaleMetric_const_smul
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (D : CovariantDerivative I F V) (hD : ContMDiffCovariantDerivative D ∞)
    (σ : ∀ x, V x)
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (T% σ)) (a : ℝ) (x : M) :
    rawBundleConnLap (scaleMetric c hc g) D (fun y => a • σ y) x =
      (c⁻¹ * a) • rawBundleConnLap g D σ x := by
  rw [rawBundleConnLap_const_smul _ D hD σ hσ a x,
    rawBundleConnLap_scaleMetric c hc g D
      ((hD.contMDiffAt (m := 1) (hσ x) (by norm_num)).mdifferentiableAt (by simp)),
    smul_smul, mul_comm]

end DifferentialGeometry.Geometry.Connection

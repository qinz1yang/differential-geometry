import DifferentialGeometry.Geometry.Connection.ParallelTransport.Frame
import DifferentialGeometry.Geometry.Exponential.Smoothness.Domain
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

open CovariantDerivativeAlong Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_parallel_orthonormal_frame_expMap_smul
    [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {L : ℝ} (hL : 0 ≤ L) (hdom : L • v ∈ expDomain g p) :
    let γ : ℝ → M := fun t => expMap g p (t • v)
    ∃ F : Fin (Module.finrank ℝ E) → ∀ t : ℝ, TangentSpace I (γ t),
      (∀ i, ∀ t ∈ Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (F i) t) t) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) L, covDerivAlong (I := I) g γ (F i) t = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) (F i t) (F j t) = if i = j then (1 : ℝ) else 0) := by
  classical
  let γ : ℝ → M := fun t => expMap g p (t • v)
  let U : Set ℝ := {t | t • v ∈ expDomain g p}
  have hU : IsOpen U :=
    (isOpen_expDomain g p).preimage (continuous_id.smul continuous_const)
  obtain ⟨η, J, hJ, hconn, h0, hLJ, hη⟩ := smul_mem_expDomain_iff.mp hdom
  have hseg : Icc (0 : ℝ) L ⊆ U := by
    intro t ht
    exact smul_mem_expDomain_iff.mpr
      ⟨η, J, hJ, hconn, h0, hconn.ordConnected.out h0 hLJ ht, hη⟩
  let vE : E := v
  have hline : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => t • vE) := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_id.smul contDiff_const
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) I (⊤ : ℕ∞)
      (fun t => expMap g p (t • v)) U :=
    (contMDiffOn_expMap g p).comp hline.contMDiffOn (fun _ ht => ht)
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ U :=
    hcurve.of_le (by exact_mod_cast le_top)
  obtain ⟨basis, hON⟩ := Tensor0SBundle.exists_orthonormal_basis (I := I) g (γ 0)
  obtain ⟨F, _, hdiff, hpar, horth⟩ :=
    exists_parallel_frame_on_Icc (I := I) g γ hγ hU hL hseg basis hON
  exact ⟨F, hdiff, hpar, horth⟩

end DifferentialGeometry.Geometry.Riemannian

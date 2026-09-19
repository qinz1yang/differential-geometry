import DifferentialGeometry.Geometry.Connection.ChartFrame.OrthonormalBasis
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Metric
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Expansion
import DifferentialGeometry.Analysis.Convex.MatrixRayleigh


noncomputable section

open Bundle Manifold Filter Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Convex
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem tensor04_tendsto_apply {ι : Type*} {l : Filter ι} {x : M}
    {A : ι → Tensor04At (I := I) (M := M) x} {A₀ : Tensor04At (I := I) (M := M) x}
    (hA : ∀ v w u z, Tendsto (fun k => tensor04StandardAt (A k) v w u z) l
      (𝓝 (tensor04StandardAt A₀ v w u z)))
    {v : ι → Fin 4 → TangentSpace I x} {v₀ : Fin 4 → TangentSpace I x}
    (hv : ∀ j, Tendsto (fun k => v k j) l (𝓝 (v₀ j))) :
    Tendsto (fun k => A k (v k)) l (𝓝 (A₀ v₀)) := by
  classical
  let B := Module.finBasis ℝ (TangentSpace I x)
  simp only [tensor0S_apply_eq_sum B]
  apply tendsto_finsetSum
  intro slots hslots
  have hc : Tendsto (fun k => component0S B (A k) slots) l (𝓝 (component0S B A₀ slots)) := by
    have hh := hA (B (slots 0)) (B (slots 1)) (B (slots 2)) (B (slots 3))
    have heq : vec4 (B (slots 0)) (B (slots 1)) (B (slots 2)) (B (slots 3)) = fun j => B (slots j) := by
      ext j; fin_cases j <;> rfl
    simpa only [tensor04StandardAt, component0S, heq] using hh
  apply hc.mul
  apply tendsto_finsetProd
  intro j hj
  exact (B.coord (slots j)).continuous_of_finiteDimensional.continuousAt.tendsto.comp (hv j)

theorem leastCurvatureOperatorEigenvalueAt_tendsto_of_components
    (hdim : Module.finrank ℝ E = 3)
    {ι : Type*} {l : Filter ι} {g : ι → SmoothRiemannianMetric I M}
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    {A : (k : ι) → algebraicCurvatureTensorSubmodule (I := I) (M := M) x}
    (A₀ : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hg : ∀ v w : TangentSpace I x, Tendsto (fun k => (g k).inner x v w) l
      (𝓝 (g₀.inner x v w)))
    (hA : ∀ v w u z, Tendsto (fun k => tensor04StandardAt (A k).1 v w u z) l
      (𝓝 (tensor04StandardAt A₀.1 v w u z))) :
    Tendsto (fun k => leastCurvatureOperatorEigenvalueAt (g k) x (A k)) l
      (𝓝 (leastCurvatureOperatorEigenvalueAt g₀ x A₀)) := by
  let : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  let B (h : SmoothRiemannianMetric I M) : Module.Basis (Fin 3) ℝ (TangentSpace I x) :=
    (smoothOrthoFrameBasis h x).reindex (finCongr hdim)
  have hBeq (h : SmoothRiemannianMetric I M) (i : Fin 3) :
      B h i = chartFrameNorm h x ((finCongr hdim).symm i) x := by
    simp only [B, Module.Basis.reindex_apply, smoothOrthoFrameBasis_apply]
    exact smoothOrthoFrame_eq_on_neighborhood h x _ (mem_smoothOrthoFrameNeighborhood_self x)
  have horth (h : SmoothRiemannianMetric I M) : OrthonormalBasisAt h x (B h) := by
    intro i j
    rw [hBeq, hBeq]
    have hh := chartFrameNorm_orthonormal h x (mem_baseSet_trivializationAt E (TangentSpace I) x)
      ((finCongr hdim).symm i) ((finCongr hdim).symm j)
    simpa only [Equiv.apply_eq_iff_eq, delta3] using hh
  have hB (i : Fin 3) : Tendsto (fun k => B (g k) i) l (𝓝 (B g₀ i)) := by
    simp only [hBeq]
    exact chartFrameNorm_tendsto_of_inner_tendsto g₀ x hg _
  have hmatrix : Tendsto (fun k => curvatureOperatorMatrixAt x (B (g k)) (A k)) l
      (𝓝 (curvatureOperatorMatrixAt x (B g₀) A₀)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact tensor04_tendsto_apply hA (by
      intro k
      fin_cases k
      · exact hB _
      · exact hB _
      · exact hB _
      · exact hB _)
  have hmin := continuous_minimumRayleighQuotient3.continuousAt.tendsto.comp hmatrix
  have heq (h : SmoothRiemannianMetric I M)
      (T : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
      minimumRayleighQuotient3 (curvatureOperatorMatrixAt x (B h) T) =
        leastCurvatureOperatorEigenvalueAt h x T := by
    rw [leastCurvatureOperatorEigenvalueAt_eq_sectionalMin h x (B h) (horth h)]
    exact minimumRayleighQuotient3_eq_min_eigenvalue (curvatureOperatorMatrixAt_isHermitian x (B h) T)
  simpa only [Function.comp_def, heq] using hmin

end DifferentialGeometry.Geometry.Curvature.DimensionThree

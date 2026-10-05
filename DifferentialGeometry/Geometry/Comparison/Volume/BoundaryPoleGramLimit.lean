import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleJacobiSlope
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Gram

/-!
The rescaled Gram matrix of the actual pole Jacobi derivative converges to its initial Gram.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]

omit ambientFinite in
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem boundaryPole_inner_continuous
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) :
    Continuous (fun q : E × (E × E) => G.inner q.1 q.2.1 q.2.2) := by
  let metricBundle : RiemannianBundle (fun x : E => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨G.toRiemannianMetric⟩
  let metricContinuous : IsContinuousRiemannianBundle E
      (fun x : E => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨⟨G.inner, G.contMDiff.continuous, by intro x v w; rfl⟩⟩
  have hleft : Continuous (fun q : E × (E × E) =>
      (⟨q.1, q.2.1⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm.continuous.comp
      (continuous_fst.prodMk continuous_snd.fst)
  have hright : Continuous (fun q : E × (E × E) =>
      (⟨q.1, q.2.2⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm.continuous.comp
      (continuous_fst.prodMk continuous_snd.snd)
  exact hleft.inner_bundle hright

noncomputable def boundaryPoleScaledJacobi
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (y v w : E) (t : ℝ) : E :=
  t⁻¹ • boundaryPoleJacobiLinear (E := E) G y v t w

theorem boundaryPoleScaledJacobi_tendsto
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (y v w : E) :
    Tendsto (boundaryPoleScaledJacobi (E := E) G y v w) (𝓝[>] (0 : ℝ)) (𝓝 w) :=
  boundaryPoleJacobiLinear_div_tendsto G y v w

theorem boundaryPoleJacobiLinear_inner_tendsto
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (y v w z : E) :
    Tendsto (fun t : ℝ =>
      G.inner (boundaryPoleFlowFamily G y v t)
        (boundaryPoleScaledJacobi (E := E) G y v w t)
        (boundaryPoleScaledJacobi (E := E) G y v z t))
      (𝓝[>] (0 : ℝ)) (𝓝 (G.inner y w z)) := by
  have hpoint : Tendsto (boundaryPoleFlowFamily G y v)
      (𝓝[>] (0 : ℝ)) (𝓝 y) := by
    have hh := (boundaryPoleFlowFamily_initial G y v).2.continuousAt.tendsto
    rw [(boundaryPoleFlowFamily_initial G y v).1] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  have hscaledLeft := boundaryPoleScaledJacobi_tendsto (E := E) G y v w
  have hscaledRight := boundaryPoleScaledJacobi_tendsto (E := E) G y v z
  have hpair := hscaledLeft.prodMk_nhds hscaledRight
  have htriple := hpoint.prodMk_nhds hpair
  have hinner := (boundaryPole_inner_continuous (E := E) G).tendsto (y, (w, z))
  have hcomposed := hinner.comp htriple
  change Tendsto (fun t : ℝ => G.inner (boundaryPoleFlowFamily G y v t)
    (boundaryPoleScaledJacobi (E := E) G y v w t)
    (boundaryPoleScaledJacobi (E := E) G y v z t))
    (𝓝[>] (0 : ℝ)) (𝓝 (G.inner y w z)) at hcomposed
  exact hcomposed

theorem boundaryPoleJacobiLinear_gram_tendsto
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (y v : E) (e : Fin 2 → E) :
    Tendsto (fun t : ℝ => fun i j : Fin 2 =>
      G.inner (boundaryPoleFlowFamily G y v t)
        (boundaryPoleScaledJacobi (E := E) G y v (e i) t)
        (boundaryPoleScaledJacobi (E := E) G y v (e j) t))
      (𝓝[>] (0 : ℝ)) (𝓝 (fun i j : Fin 2 => G.inner y (e i) (e j))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact boundaryPoleJacobiLinear_inner_tendsto (E := E) G y v (e i) (e j)

theorem boundaryPoleJacobiLinear_scaled_density_tendsto
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (y v : E) (e : Fin 2 → E)
    (hON : ∀ i j, G.inner y (e i) (e j) = if i = j then 1 else 0) :
    Tendsto (fun t : ℝ => curveDensity G (boundaryPoleFlowFamily G y v)
      (fun i s => boundaryPoleScaledJacobi (E := E) G y v (e i) s) t)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  have hgram := boundaryPoleJacobiLinear_gram_tendsto (E := E) G y v e
  have hid : (fun i j : Fin 2 => G.inner y (e i) (e j)) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    simp only [hON, Matrix.one_apply]
  rw [hid] at hgram
  have hdet := (continuous_id.matrix_det.tendsto
    (1 : Matrix (Fin 2) (Fin 2) ℝ)).comp hgram
  have hsqrt := (Real.continuous_sqrt.tendsto
    (Matrix.det (1 : Matrix (Fin 2) (Fin 2) ℝ))).comp hdet
  change Tendsto (fun t : ℝ => curveDensity G (boundaryPoleFlowFamily G y v)
    (fun i s => boundaryPoleScaledJacobi (E := E) G y v (e i) s) t)
    (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt (Matrix.det
      (1 : Matrix (Fin 2) (Fin 2) ℝ)))) at hsqrt
  simpa only [Matrix.det_one, Real.sqrt_one] using hsqrt

theorem boundaryPoleJacobiLinear_density_div_sq_tendsto
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (y v : E) (e : Fin 2 → E)
    (hON : ∀ i j, G.inner y (e i) (e j) = if i = j then 1 else 0) :
    Tendsto (fun t : ℝ => curveDensity G (boundaryPoleFlowFamily G y v)
      (fun i s => boundaryPoleJacobiLinear (E := E) G y v s (e i)) t / t ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  have hs := boundaryPoleJacobiLinear_scaled_density_tendsto (E := E) G y v e hON
  have heq : (fun t : ℝ => curveDensity G (boundaryPoleFlowFamily G y v)
      (fun i s => boundaryPoleScaledJacobi (E := E) G y v (e i) s) t) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => curveDensity G (boundaryPoleFlowFamily G y v)
        (fun i s => boundaryPoleJacobiLinear (E := E) G y v s (e i)) t / t ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htp : (0 : ℝ) < t := ht
    have habs : |t⁻¹| = t⁻¹ := abs_of_pos (inv_pos.mpr htp)
    have hscale := curveDensity_smul G (boundaryPoleFlowFamily G y v)
      (fun i s => boundaryPoleJacobiLinear (E := E) G y v s (e i)) t t⁻¹
    have hliteral : curveDensity G (boundaryPoleFlowFamily G y v)
        (fun i s => boundaryPoleScaledJacobi (E := E) G y v (e i) s) t =
        curveDensity G (boundaryPoleFlowFamily G y v)
          (fun i => t⁻¹ • (fun s => boundaryPoleJacobiLinear (E := E) G y v s (e i))) t := by
      rfl
    have hcombined := hliteral.trans hscale
    calc
      _ = |t⁻¹| ^ Fintype.card (Fin 2) * curveDensity G
          (boundaryPoleFlowFamily G y v)
          (fun i s => boundaryPoleJacobiLinear (E := E) G y v s (e i)) t := hcombined
      _ = _ := by
        simp only [Fintype.card_fin, habs, inv_pow, div_eq_mul_inv]
        exact mul_comm _ _
  exact hs.congr' heq

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Radial
import DifferentialGeometry.Geometry.Exponential.VolumeDensity
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint.MinimizingGeodesic

noncomputable section

open Filter Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open Exponential Variation CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem paramDensity_expMap_le_mul_hyperbolicDensity
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (hx : (show TangentSpace I p from x) ∈ expDomain (I := I) g p)
    (q : ℝ) (hq : 0 ≤ q)
    (hinj : ∀ t ∈ Ioo (0 : ℝ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, E) I
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) (t • x)))
    (hRic : ∀ t ∈ Ioo (0 : ℝ) 1,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
          g.inner (radialCurve (I := I) g p x t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t) ≤
        ricciTensor (I := I) g (radialCurve (I := I) g p x t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) :
    paramDensity (I := I) g
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) x ≤
      paramDensity (I := I) g
          (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) 0 *
        hyperbolicDensity (q * Real.sqrt (g.inner p x x)) (Module.finrank ℝ E - 1) 1 := by
  classical
  by_cases hx0 : x = 0
  · subst x
    have hmetric : g.inner p (0 : E) (0 : E) = 0 := by
      let A : E →L[ℝ] ℝ := g.inner p (0 : E)
      exact A.map_zero
    simp [hmetric, hyperbolicDensity, hyperbolicSn]
  obtain ⟨w₀, hON₀, hperp₀⟩ := exists_perp_pos (I := I) g p x (g.pos p x hx0)
  let w : Fin (Module.finrank ℝ E - 1) → E := fun i => w₀ i
  have hON i j : g.inner p (w i) (w j) = if i = j then 1 else 0 := hON₀ i j
  have hperp i : g.inner p x (w i) = 0 := (g.symm p x (w i)).trans (hperp₀ i)
  have hLI : LinearIndependent ℝ (fun i => (w i : E)) := by
    let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner p
    let Q : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
      (ContinuousLinearMap.coeLM ℝ).comp G.toLinearMap
    apply LinearMap.linearIndependent_of_isOrthoᵢ (B := Q)
    · rw [LinearMap.isOrthoᵢ_def]
      intro i j hij
      change g.inner p (w i) (w j) = 0
      rw [hON, if_neg hij]
    · intro i
      change g.inner p (w i) (w i) ≠ 0
      rw [hON, if_pos rfl]
      exact one_ne_zero
  have hdom t (ht : t ∈ Ioo (0 : ℝ) 1) :
      (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p :=
    smul_mem_expDomain hx ⟨ht.1.le, ht.2.le⟩
  let γ := radialCurve (I := I) g p x
  let V := fun i => radialJacobiField (I := I) g p x (w i)
  have hG0 : curveGram (I := I) g (fun _ : ℝ => p)
      (fun i (_ : ℝ) => show TangentSpace I p from w i) 0 = 1 := by
    ext i j
    exact hON i j
  have hD0 : curveDensity (I := I) g (fun _ : ℝ => p)
      (fun i (_ : ℝ) => show TangentSpace I p from w i) 0 = 1 := by
    unfold curveDensity
    rw [hG0, Matrix.det_one, Real.sqrt_one]
  have hbound := curveDensity_radialJacobiField_le_mul_hyperbolicDensity
    (I := I) g p x hx0 (fun i => (w i : E)) hLI hperp (Fintype.card_fin _)
    q 1 hq hdom hinj hRic
  simp only [hD0, one_mul] at hbound
  have hx1 : (show TangentSpace I p from (1 : ℝ) • x) ∈ expDomain (I := I) g p := by
    simpa only [one_smul] using! hx
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ 1 :=
    ((contMDiffAt_expMap (I := I) g p hx1).comp 1
      (contMDiff_id.smul (contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun _ : ℝ => x))).contMDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
  have hVdiff i : DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) 1) 1 :=
    differentiableAt_chartRep_radialJacobiField (I := I) g p x (w i)
      hx1
  have hDcont := curveDensity_cont (I := I) (n := 1) le_rfl g γ V 1 hγ hVdiff
  have hmodel := (hyperbolicDen_continuous
    (q * Real.sqrt (g.inner p x x)) (Module.finrank ℝ E - 1)).continuousAt (x := 1)
  have hendpoint : curveDensity (I := I) g γ V 1 ≤
      hyperbolicDensity (q * Real.sqrt (g.inner p x x)) (Module.finrank ℝ E - 1) 1 := by
    apply le_of_tendsto_of_tendsto
      (hDcont.tendsto.mono_left (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from inf_le_left))
      (hmodel.tendsto.mono_left (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from inf_le_left))
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
    exact hbound t ht
  rw [paramDensity_expMap_eq_mul_curveDensity_of_orthonormal
    (I := I) g p x hx (fun i => (w i : E)) hON hperp]
  exact mul_le_mul_of_nonneg_left hendpoint (Real.sqrt_nonneg _)

theorem paramDensity_expMap_le_of_ricci_nonneg
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (hx : (show TangentSpace I p from x) ∈ expDomain (I := I) g p)
    (hinj : ∀ t ∈ Ioo (0 : ℝ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, E) I
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) (t • x)))
    (hRic : ∀ t ∈ Ioo (0 : ℝ) 1,
      0 ≤ ricciTensor (I := I) g (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) :
    paramDensity (I := I) g
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) x ≤
      paramDensity (I := I) g
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) 0 := by
  have h := paramDensity_expMap_le_mul_hyperbolicDensity
    (I := I) g p x hx 0 le_rfl hinj (fun t ht => by simpa using! hRic t ht)
  simpa [hyperbolicDensity, hyperbolicSn] using! h

section ENorm

variable [(y : M) → ENorm (TangentSpace I y)]

theorem paramDensity_expMap_le_mul_hyperbolicDensity_of_le_riemannianEDist
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (x : E)
    (hx : (show TangentSpace I p from x) ∈ expDomain (I := I) g p)
    (hmin : ENNReal.ofReal (Real.sqrt (g.inner p x x)) ≤
      Manifold.riemannianEDist I p (expMap (I := I) g p (show TangentSpace I p from x)))
    (q : ℝ) (hq : 0 ≤ q)
    (hRic : ∀ t ∈ Ioo (0 : ℝ) 1,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
          g.inner (radialCurve (I := I) g p x t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t) ≤
        ricciTensor (I := I) g (radialCurve (I := I) g p x t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) :
    paramDensity (I := I) g
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) x ≤
      paramDensity (I := I) g
          (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) 0 *
        hyperbolicDensity (q * Real.sqrt (g.inner p x x)) (Module.finrank ℝ E - 1) 1 := by
  exact paramDensity_expMap_le_mul_hyperbolicDensity (I := I) g p x hx q hq
    (fun _ ht => injective_mfderiv_expMap_of_le_riemannianEDist
      (I := I) g hEnorm p x hx hmin ⟨ht.1.le, ht.2⟩) hRic

theorem paramDensity_expMap_le_of_ricci_nonneg_of_le_riemannianEDist
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (x : E)
    (hx : (show TangentSpace I p from x) ∈ expDomain (I := I) g p)
    (hmin : ENNReal.ofReal (Real.sqrt (g.inner p x x)) ≤
      Manifold.riemannianEDist I p (expMap (I := I) g p (show TangentSpace I p from x)))
    (hRic : ∀ t ∈ Ioo (0 : ℝ) 1,
      0 ≤ ricciTensor (I := I) g (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) :
    paramDensity (I := I) g
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) x ≤
      paramDensity (I := I) g
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) 0 := by
  have h := paramDensity_expMap_le_mul_hyperbolicDensity_of_le_riemannianEDist
    (I := I) g hEnorm p x hx hmin 0 le_rfl (fun t ht => by simpa using! hRic t ht)
  simpa [hyperbolicDensity, hyperbolicSn] using! h

end ENorm

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

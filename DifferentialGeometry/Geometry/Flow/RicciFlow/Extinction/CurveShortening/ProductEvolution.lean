import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductBackground
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Ramps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Projection
import DifferentialGeometry.Analysis.Calculus.TimeJet.SpatialDerivatives

section

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    {D : RealTimeInterval} {a b s u : ℝ}

omit [SigmaCompactSpace M] in
theorem map_ricciTangent_eq (c : ProductCurve M) (A : QuotientProductAtlas I M)
    (G : SolutionFamily (I := I) (M := M)) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.ricciTangent (quotientProductFamily A G lambda hlambda) x t =
      c.ricciTangent G lambda x t := by
  let _ := A.charts
  let _ := A.smoothManifold
  have hricci := quotientProduct_iterCov_ricci_apply A (G.metric t) lambda hlambda 0
    (c.coverLift x t) (fun _ => c.unitTangent G.metric lambda x t)
  dsimp only [CurveMap.ricciTangent, ProductCurve.ricciTangent, quotientProductFamily,
    SolutionFamily.ricciAt]
  rw [c.map_unitTangent_eq A G.metric lambda hlambda hc x t ht]
  have hricci' :
      (metricRicciAt (quotientProductMetric A (G.metric t) lambda hlambda)
        (productCoverProjection (M := M) (c.coverLift x t)))
          (fun _ => mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
            (productCoverProjection (M := M)) (c.coverLift x t)
            (c.unitTangent G.metric lambda x t)) =
      (metricRicciAt (G.metric t) (c.projection.lift x t))
        (fun _ => (c.unitTangent G.metric lambda x t).1) := by
    simpa only [iterCov, Nat.rec_zero, Nat.add_zero, metricRicci_apply,
      ProductCurve.coverLift] using! hricci
  have he (v : E × ℝ) :
      (metricRicciAt (quotientProductMetric A (G.metric t) lambda hlambda)
        (productCoverProjection (M := M) (c.coverLift x t))) (fun _ => v) =
      (metricRicciAt (quotientProductMetric A (G.metric t) lambda hlambda)
        (c.map.lift x t)) (fun _ => v) :=
    congrArg (fun q => (metricRicciAt
      (quotientProductMetric A (G.metric t) lambda hlambda) q) (fun _ => v))
      (c.coverProjection_lift x t)
  convert (he _).symm.trans hricci' using 1 <;>
    congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem hasDerivWithinAt_speed
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    HasDerivWithinAt (c.speed B.family.metric lambda x)
      (-(c.curvatureSq B.family.metric lambda x t + c.ricciTangent B.family lambda x t) *
        c.speed B.family.metric lambda x t) (Icc s u) t := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  let _ := A.charts
  let _ := A.smoothManifold
  obtain ⟨D', _, _, hB⟩ := exists_quotientProduct_ricciBackground_on_regular A B
  obtain ⟨Bhat, hf, _, _, _, _⟩ := hB lambda hlambda
  have hm : Bhat.family.metric =
      fun τ => quotientProductMetric A (B.family.metric τ) lambda hlambda :=
    congrArg (fun F => F.metric) hf
  have hsol : c.map.IsSolutionOn Bhat.family.metric (Icc s u) := by
    rw [hm]
    exact c.isSolutionOn_map A B.family.metric lambda hlambda (uniqueDiffOn_Icc hsu) hc
  have hs := CurveMap.speedEvolution_of_pairingEvolution Bhat c.map hsol.immersed
    (CurveMap.pairingEvolution Bhat hsu hwindow c.map hsol) x t ht
  have he (τ : ℝ) (hτ : τ ∈ Icc s u) :
      c.map.speed Bhat.family.metric x τ = c.speed B.family.metric lambda x τ := by
    rw [hm]
    exact c.map_speed_eq A B.family.metric lambda hlambda hc.smooth x τ hτ
  have hk : c.map.curvatureSq Bhat.family.metric x t =
      c.curvatureSq B.family.metric lambda x t := by
    rw [hm]
    exact c.map_curvatureSq_eq A B.family.metric lambda hlambda hc.smooth hc.immersed x t ht
  have hr : c.map.ricciTangent Bhat.family x t = c.ricciTangent B.family lambda x t := by
    rw [hf]
    exact c.map_ricciTangent_eq A B.family lambda hlambda hc.smooth x t ht
  rw [CurveMap.q, hk, hr, he t ht] at hs
  exact hs.congr_of_mem (fun τ hτ => (he τ hτ).symm) ht

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

end
end

section

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem height_evolution (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (x t : ℝ) (ht : t ∈ J) :
    derivWithin (c.y x) J t = (c.speed g lambda x t)⁻¹ *
      deriv (fun z => (c.speed g lambda z t)⁻¹ * deriv (fun w => c.y w t) z) x := by
  simpa only [velocity, curvatureVector, Ds, Dx, unitTangent, X,
    Prod.smul_snd, smul_eq_mul] using congrArg Prod.snd (hc.equation x t ht)

private theorem ds_angle_eq_height_derivative (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (x t : ℝ) (ht : t ∈ J) :
    c.ds g lambda (c.angle g lambda) x t = lambda * derivWithin (c.y x) J t := by
  have hangle : (fun z => c.angle g lambda z t) =
      (fun z => lambda * ((c.speed g lambda z t)⁻¹ * deriv (fun w => c.y w t) z)) := by
    funext z
    rw [c.angle_eq]
    ring
  rw [ds, hangle, deriv_const_mul_field, height_evolution c g lambda hc x t ht]
  ring

private theorem hasDerivWithinAt_angle_of_speed (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) {J : Set ℝ}
    (hJ : UniqueDiffOn ℝ J) (hacc : J ⊆ closure (interior J))
    (hc : c.IsSolutionOn g lambda J) (x t q : ℝ) (ht : t ∈ J)
    (hv : c.speed g lambda x t ≠ 0)
    (hspeed : HasDerivWithinAt (c.speed g lambda x)
      (-q * c.speed g lambda x t) J t) :
    HasDerivWithinAt (c.angle g lambda x)
      (c.ds g lambda (c.ds g lambda (c.angle g lambda)) x t +
        q * c.angle g lambda x t) J t := by
  have hdy : HasDerivWithinAt (fun s => deriv (fun z => c.y z s) x)
      (deriv (fun z => derivWithin (c.y z) J t) x) J t := by
    simpa only [iteratedDeriv_one] using
      DifferentialGeometry.Analysis.hasDerivWithinAt_iteratedDeriv_fst
        (G := c.y) isOpen_univ hJ hacc hc.smooth.2 1 (mem_univ x) ht
  have hds : c.ds g lambda (c.ds g lambda (c.angle g lambda)) x t =
      lambda * (c.speed g lambda x t)⁻¹ *
        deriv (fun z => derivWithin (c.y z) J t) x := by
    have heq : (fun z => c.ds g lambda (c.angle g lambda) z t) =
        fun z => lambda * derivWithin (c.y z) J t :=
      funext (fun z => ds_angle_eq_height_derivative c g lambda hc z t ht)
    change (c.speed g lambda x t)⁻¹ *
      deriv (fun z => c.ds g lambda (c.angle g lambda) z t) x = _
    rw [heq, deriv_const_mul_field]
    ring
  have hprod := ((hspeed.inv hv).const_mul lambda).mul hdy
  have hprod' : HasDerivWithinAt (c.angle g lambda x)
      ((lambda * (-(-q * c.speed g lambda x t) / c.speed g lambda x t ^ 2)) *
          deriv (fun z => c.y z t) x +
        (lambda * (c.speed g lambda x t)⁻¹) *
          deriv (fun z => derivWithin (c.y z) J t) x) J t :=
    hprod.congr_of_mem (fun s _ => c.angle_eq g lambda x s) ht
  apply hprod'.congr_deriv
  rw [hds, c.angle_eq]
  field_simp [hv]
  ring


variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    {D : RealTimeInterval} {a b s u : ℝ}

theorem hasDerivWithinAt_angle
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    HasDerivWithinAt (c.angle B.family.metric lambda x)
      (c.ds B.family.metric lambda (c.ds B.family.metric lambda
          (c.angle B.family.metric lambda)) x t +
        (c.curvatureSq B.family.metric lambda x t + c.ricciTangent B.family lambda x t) *
          c.angle B.family.metric lambda x t) (Icc s u) t := by
  have hacc : Icc s u ⊆ closure (interior (Icc s u)) := by
    simpa only [interior_Icc, closure_Ioo hsu.ne] using (Subset.refl (Icc s u))
  exact hasDerivWithinAt_angle_of_speed c B.family.metric lambda
    (uniqueDiffOn_Icc hsu) hacc hc x t
    (c.curvatureSq B.family.metric lambda x t + c.ricciTangent B.family lambda x t) ht
    (c.speed_pos_of_immersedOn B.family.metric lambda hlambda hc.immersed x t ht).ne'
    (hasDerivWithinAt_speed B c lambda hlambda hsu hwindow hc x t ht)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

end
end

section

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def regularizedCurvature (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda ε x t : ℝ) : ℝ :=
  Real.sqrt (c.curvatureSq g lambda x t + ε ^ 2)

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
  {D : RealTimeInterval} {a b s u : ℝ}

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem ds_congr (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (f h : ℝ → ℝ → ℝ) (x t : ℝ) (heq : ∀ y, f y t = h y t) :
    c.ds g lambda f x t = c.ds g lambda h x t := by
  unfold ds
  rw [funext heq]

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem regularized_curvature_periodic (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (ε t : ℝ) (ht : t ∈ J) :
    Function.Periodic (fun x => c.regularizedCurvature g ε x t) 1 := by
  intro x
  have hperiod := c.curvatureSq_speed_periodic g J hc hi t ht x
  dsimp only at hperiod
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun z => c.lift z t) (x + 1) :=
    (contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc t ht)).mdifferentiableAt (by simp)
  have hs := c.speed_add_period g t x hγ
  have heq : c.curvatureSq g (x + 1) t = c.curvatureSq g x t := by
    rw [hs] at hperiod
    exact mul_right_cancel₀ (c.speed_pos g hi x t ht).ne' hperiod
  simp only [CurveMap.regularizedCurvature, heq]

theorem regularized_curvature_evolution
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc s u))
    (ε : ℝ) (hε : 0 < ε) :
    ContDiffOn ℝ ∞
        (fun p : ℝ × ℝ => c.regularizedCurvature B.family.metric lambda ε p.1 p.2)
        (univ ×ˢ Icc s u) ∧
      (∀ t ∈ Icc s u, Function.Periodic
        (fun x => c.regularizedCurvature B.family.metric lambda ε x t) 1) ∧
      (∀ x t, t ∈ Icc s u →
        0 ≤ c.regularizedCurvature B.family.metric lambda ε x t -
          c.curvature B.family.metric lambda x t ∧
        c.regularizedCurvature B.family.metric lambda ε x t -
          c.curvature B.family.metric lambda x t ≤ ε) ∧
      ∀ x t, t ∈ Icc s u →
        derivWithin (c.regularizedCurvature B.family.metric lambda ε x) (Icc s u) t ≤
          c.ds B.family.metric lambda
            (c.ds B.family.metric lambda (c.regularizedCurvature B.family.metric lambda ε)) x t +
          c.curvatureSq B.family.metric lambda x t *
            c.regularizedCurvature B.family.metric lambda ε x t +
          B.C * (c.regularizedCurvature B.family.metric lambda ε x t + 1) := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  let _ := A.charts
  let _ := A.smoothManifold
  obtain ⟨D', _, _, hB⟩ := exists_quotientProduct_ricciBackground_on_regular A B
  obtain ⟨Bhat, hf, _, _, _, hC⟩ := hB lambda hlambda
  have hm : Bhat.family.metric =
      fun τ => quotientProductMetric A (B.family.metric τ) lambda hlambda :=
    congrArg (fun F => F.metric) hf
  have hsol : c.map.IsSolutionOn Bhat.family.metric (Icc s u) := by
    rw [hm]
    exact c.isSolutionOn_map A B.family.metric lambda hlambda (uniqueDiffOn_Icc hsu) hc
  have hk (x t : ℝ) (ht : t ∈ Icc s u) :
      c.map.curvatureSq Bhat.family.metric x t = c.curvatureSq B.family.metric lambda x t := by
    rw [hm]
    exact c.map_curvatureSq_eq A B.family.metric lambda hlambda hc.smooth hc.immersed x t ht
  have he (x t : ℝ) (ht : t ∈ Icc s u) :
      c.map.regularizedCurvature Bhat.family.metric ε x t =
        c.regularizedCurvature B.family.metric lambda ε x t := by
    simp only [CurveMap.regularizedCurvature, regularizedCurvature, hk x t ht]
  have hds (f : ℝ → ℝ → ℝ) (x t : ℝ) (ht : t ∈ Icc s u) :
      c.map.ds Bhat.family.metric f x t = c.ds B.family.metric lambda f x t := by
    rw [hm]
    exact map_ds_eq c A B.family.metric lambda hlambda hc.smooth f x t ht
  obtain ⟨hreg, herr, hpde⟩ := rfs_csf_regularized_curvature Bhat hsu hwindow c.map hsol ε hε
  refine ⟨hreg.congr (fun p hp => (he p.1 p.2 hp.2).symm), ?_, ?_, ?_⟩
  · intro t ht x
    change c.regularizedCurvature B.family.metric lambda ε (x + 1) t =
      c.regularizedCurvature B.family.metric lambda ε x t
    rw [← he (x + 1) t ht, ← he x t ht]
    exact regularized_curvature_periodic c.map Bhat.family.metric hsol.smooth
      hsol.immersed ε t ht x
  · intro x t ht
    simpa only [he x t ht, CurveMap.curvature, hk x t ht, ProductCurve.curvature]
      using herr x t ht
  · intro x t ht
    have hd : derivWithin (c.map.regularizedCurvature Bhat.family.metric ε x) (Icc s u) t =
        derivWithin (c.regularizedCurvature B.family.metric lambda ε x) (Icc s u) t :=
      derivWithin_congr (fun τ hτ => he x τ hτ) (he x t ht)
    have hss : c.map.ds Bhat.family.metric
        (c.map.ds Bhat.family.metric (c.map.regularizedCurvature Bhat.family.metric ε)) x t =
        c.ds B.family.metric lambda
          (c.ds B.family.metric lambda (c.regularizedCurvature B.family.metric lambda ε)) x t := by
      rw [hds _ x t ht]
      apply ds_congr
      intro y
      rw [hds _ y t ht]
      exact ds_congr c B.family.metric lambda _ _ y t (fun z => he z t ht)
    simpa only [hd, hss, hk x t ht, he x t ht, hC] using hpde x t ht

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

end
end

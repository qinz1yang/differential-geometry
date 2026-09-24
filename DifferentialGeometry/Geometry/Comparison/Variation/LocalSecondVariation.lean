import DifferentialGeometry.Geometry.Comparison.Variation.GeodesicEndpoints
import DifferentialGeometry.Geometry.Comparison.Variation.LocalEnergyDerivatives
import DifferentialGeometry.Geometry.Exponential.Variation.Jacobi

noncomputable section
open Bundle Manifold Set Filter MeasureTheory
open scoped Topology Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] in
lemma centralVariationField_eventuallyEq {d f : ℝ × ℝ → M} {t : ℝ}
    (h : d =ᶠ[𝓝 (0, t)] f) :
    ∀ᶠ u in 𝓝 t,
      (centralVariationField (I := I) (Function.curry d) u : E) =
        (centralVariationField (I := I) (Function.curry f) u : E) := by
  have hh : ∀ᶠ u in 𝓝 t, d =ᶠ[𝓝 (0, u)] f :=
    (continuous_const.prodMk continuous_id).continuousAt.eventually h.eventuallyEq_nhds
  filter_upwards [hh] with u hu
  have hs := hu.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  exact congrArg (fun A => A (1 : ℝ)) (hs.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I))


lemma centralCurvatureDensity_eq_of_eventuallyEq (g : SmoothRiemannianMetric I M)
    {d f : ℝ × ℝ → M} {t : ℝ} (h : d =ᶠ[𝓝 (0, t)] f) :
    centralCurvatureDensity (I := I) g (Function.curry d) t =
      centralCurvatureDensity (I := I) g (Function.curry f) t := by
  have hvel : centralVelocity (I := I) (Function.curry d) t =
      centralVelocity (I := I) (Function.curry f) t := by
    unfold centralVelocity
    have hpath : (fun u : ℝ => Function.curry d 0 u) =ᶠ[𝓝 t]
        (fun u : ℝ => Function.curry f 0 u) := by
      filter_upwards
        [h.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt]
        with u hu using hu
    exact congrArg (fun A => A (1 : ℝ))
      (hpath.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I))
  have hv : centralVariationField (I := I) (Function.curry d) t =
      centralVariationField (I := I) (Function.curry f) t :=
    (centralVariationField_eventuallyEq (I := I) h).self_of_nhds
  have hbase : Function.curry d 0 t = Function.curry f 0 t := h.self_of_nhds
  unfold centralCurvatureDensity
  rw [hbase, hv, hvel]

theorem secondVariation_curveEnergy_neg_of_parallel_geodesicEndpoints_local
    (g : SmoothRiemannianMetric I M) (f : ℝ × ℝ → M) {L : ℝ} (hL : 0 < L)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hsub : ({0} ×ˢ Icc 0 L) ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f U)
    (hcentral : IsGeodesicOn (I := I) g (fun t => f (0, t)) (Icc 0 L))
    (hinitial : HasGeodesicEquationAt (I := I) g (fun s => f (s, 0)) 0)
    (hterminal : HasGeodesicEquationAt (I := I) g (fun s => f (s, L)) 0)
    (hparallel : ∀ t ∈ Icc (0 : ℝ) L,
      covDerivAlong (I := I) g (fun u => f (0, u))
        (centralVariationField (I := I) (Function.curry f)) t = 0)
    (hpositive : ∀ t ∈ Icc (0 : ℝ) L,
      0 < centralCurvatureDensity (I := I) g (Function.curry f) t) :
    deriv (deriv (fun s => curveEnergy (I := I) g (fun t => f (s, t)) 0 L)) 0 < 0 := by
  obtain ⟨d, hd, heq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_global_smooth_variation_eq_jointly_near_slice hL.le hU hsub hf
  have hjoint : ∀ t ∈ Icc (0 : ℝ) L, d =ᶠ[𝓝 (0, t)] f := heq.self_of_nhds
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      (fun u => d (0, u)) =ᶠ[𝓝 t] (fun u => f (0, u)) :=
    (hjoint t ht).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have hd8 : IsSmoothVariation (I := I) (Function.curry d) := by
    unfold IsSmoothVariation
    have hh : ContMDiff 𝓘(ℝ, ℝ × ℝ) I (8 : ℕ) d := hd.of_le (by decide)
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hh
    exact hh
  have hg : IsGeodesicOn (I := I) g (fun t => d (0, t)) (Icc 0 L) := by
    intro t ht
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
      (hpath t ht).eq_of_nhds (hpath t ht) (hcentral t ht)
  have hend (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L)
      (hgt : HasGeodesicEquationAt (I := I) g (fun s => f (s, t)) 0) :
      HasGeodesicEquationAt (I := I) g (fun s => d (s, t)) 0 := by
    have hs := (hjoint t ht).comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at hs.eq_of_nhds hs hgt
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      covDerivAlong (I := I) g (fun u => d (0, u))
        (centralVariationField (I := I) (Function.curry d)) t = 0 := by
    have hc := covDerivAlong_congr_curve g
      (centralVariationField (I := I) (Function.curry d))
      (centralVariationField (I := I) (Function.curry f))
      (hpath t ht) (centralVariationField_eventuallyEq (hjoint t ht))
    exact hc.trans (hparallel t ht)
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      0 < centralCurvatureDensity (I := I) g (Function.curry d) t := by
    rw [centralCurvatureDensity_eq_of_eventuallyEq g (hjoint t ht)]
    exact hpositive t ht
  have hE : (fun s => curveEnergy (I := I) g (fun t => d (s, t)) 0 L) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => curveEnergy (I := I) g (fun t => f (s, t)) 0 L) := by
    filter_upwards [heq] with s hs
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    exact (speedSq_eventuallyEq g (hs t ht)).eq_of_nhds
  rw [← hE.deriv.deriv_eq]
  exact secondVariation_curveEnergy_neg_of_parallel_geodesicEndpoints g (Function.curry d) L hd8 hL
    hg (hend 0 ⟨le_rfl, hL.le⟩ hinitial) (hend L ⟨hL.le, le_rfl⟩ hterminal) hp hpos

theorem secondVariation_curveEnergy_parallel_geodesicEndpoints_local
    (g : SmoothRiemannianMetric I M) (f : ℝ × ℝ → M) {L : ℝ} (hL : 0 < L)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hsub : ({0} ×ˢ Icc 0 L) ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f U)
    (hcentral : IsGeodesicOn (I := I) g (fun t => f (0, t)) (Icc 0 L))
    (hinitial : HasGeodesicEquationAt (I := I) g (fun s => f (s, 0)) 0)
    (hterminal : HasGeodesicEquationAt (I := I) g (fun s => f (s, L)) 0)
    (hparallel : ∀ t ∈ Icc (0 : ℝ) L,
      covDerivAlong (I := I) g (fun u => f (0, u))
        (centralVariationField (I := I) (Function.curry f)) t = 0) :
    HasDerivAt (deriv (fun s => curveEnergy (I := I) g (fun t => f (s, t)) 0 L))
      (-2 * ∫ t in (0 : ℝ)..L, centralCurvatureDensity (I := I) g (Function.curry f) t) 0 := by
  obtain ⟨d, hd, heq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_global_smooth_variation_eq_jointly_near_slice hL.le hU hsub hf
  have hjoint : ∀ t ∈ Icc (0 : ℝ) L, d =ᶠ[𝓝 (0, t)] f := heq.self_of_nhds
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      (fun u => d (0, u)) =ᶠ[𝓝 t] (fun u => f (0, u)) :=
    (hjoint t ht).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have hd8 : IsSmoothVariation (I := I) (Function.curry d) := by
    unfold IsSmoothVariation
    have hh : ContMDiff 𝓘(ℝ, ℝ × ℝ) I (8 : ℕ) d := hd.of_le (by decide)
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hh
    exact hh
  have hg : IsGeodesicOn (I := I) g (fun t => d (0, t)) (Icc 0 L) := by
    intro t ht
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
      (hpath t ht).eq_of_nhds (hpath t ht) (hcentral t ht)
  have hend (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L)
      (hgt : HasGeodesicEquationAt (I := I) g (fun s => f (s, t)) 0) :
      HasGeodesicEquationAt (I := I) g (fun s => d (s, t)) 0 := by
    have hs := (hjoint t ht).comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at hs.eq_of_nhds hs hgt
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      covDerivAlong (I := I) g (fun u => d (0, u))
        (centralVariationField (I := I) (Function.curry d)) t = 0 := by
    have hc := covDerivAlong_congr_curve g
      (centralVariationField (I := I) (Function.curry d))
      (centralVariationField (I := I) (Function.curry f))
      (hpath t ht) (centralVariationField_eventuallyEq (hjoint t ht))
    exact hc.trans (hparallel t ht)
  have hE : (fun s => curveEnergy (I := I) g (fun t => d (s, t)) 0 L) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => curveEnergy (I := I) g (fun t => f (s, t)) 0 L) := by
    filter_upwards [heq] with s hs
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    exact (speedSq_eventuallyEq g (hs t ht)).eq_of_nhds
  have hsecond := secondVariation_curveEnergy_parallel_geodesicEndpoints
    g (Function.curry d) L hd8 hL hg
    (hend 0 ⟨le_rfl, hL.le⟩ hinitial) (hend L ⟨hL.le, le_rfl⟩ hterminal) hp
  have hi : (∫ t in (0 : ℝ)..L, centralCurvatureDensity (I := I) g (Function.curry d) t) =
      ∫ t in (0 : ℝ)..L, centralCurvatureDensity (I := I) g (Function.curry f) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    exact centralCurvatureDensity_eq_of_eventuallyEq g (hjoint t ht)
  rw [hi] at hsecond
  exact hsecond.congr_of_eventuallyEq hE.deriv.symm

end DifferentialGeometry.Geometry.Riemannian.Variation

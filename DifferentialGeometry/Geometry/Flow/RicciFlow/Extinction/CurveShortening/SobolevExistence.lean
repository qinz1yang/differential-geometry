import DifferentialGeometry.Topology.Manifold.Embedding.ProductRetraction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.Uniqueness
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.Regularity

open private ScalarVectorTimeCoefficients.radius from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState

open private CircleHsPi circleHsPiInclusion from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private ambientSobolev ScalarVectorTimeCoefficients ambientCoefficients from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
open private parameterDerivativeForcingFieldLift ambientSobolevSolutionFacts ambient_retraction_contMDiff_two_and_immersed_of_parameterDerivative_lift ambient_retraction_parametric_equation_of_parameterDerivative_lift ambient_retraction_smooth_of_contDiffOn ambient_retraction_exists_reparametrization_of_contDiffOn from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity
open private ambient_sobolev_solution_exists_with_smooth_chart from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.Regularity

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
open AddCircle (parameterPrincipalOperatorHsPi parameterPrincipalOperatorH0Pi)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

variable (c₀ : SmoothImmersion (I := I) (M := M))
variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

private theorem ambient_sobolev_solution_exists_with_reparametrization [I.Boundaryless]
    (hg : MetricFamilySmoothOn D g) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ScalarVectorTimeCoefficients.radius C ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
            parameterDerivativeForcingFieldLift g₀ hT gforce ∧
            let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
              (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
            let c : CurveMap M := fun z t => r (d z t)
            (∀ z, c z 0 = c₀.map z) ∧
              (∀ z t, t ∈ Icc 0 T → e (c z t) = d z t) ∧
              c.SmoothOn (I := I) (Icc 0 T) ∧
              c.ImmersedOn (I := I) (Icc 0 T) ∧
              ∃ φ : CircleReparametrization (Icc 0 T),
                (∀ z, φ.map 0 z = z) ∧
                CurveMap.IsSolutionOn (I := I) (fun z t => c (φ.map t z) t) g (Icc 0 T) ∧
                (∀ z, c (φ.map 0 z) 0 = c₀.map z) ∧
                (∀ z t, t ∈ Icc 0 T → e (c (φ.map t z) t) = d (φ.map t z) t) ∧
                ∀ t, t ∈ Icc 0 T →
                  range (fun z => e (c (φ.map t z) t)) = range (fun z => d z t) := by
  intro C g₀ f₀ P S
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, hsmooth⟩ :=
    ambient_sobolev_solution_exists_with_smooth_chart c₀ g ht he hr hEU hleft β hG
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, ?_⟩
  exact ambient_retraction_exists_reparametrization_of_contDiffOn
    c₀ g ht he hr hEU hleft β hG hg hT hTρ hρC u gforce hfacts hlift hsmooth

include ht he hr hEU hleft β hG in
private theorem exists_solution_of_smooth_retraction [I.Boundaryless]
    (hg : MetricFamilySmoothOn D g) :
    ∃ T : ℝ, 0 < T ∧ ∃ c : CurveMap M,
      c.IsSolutionOn (I := I) g (Icc 0 T) ∧ ∀ z, c z 0 = c₀.map z := by
  obtain ⟨ρ, _, _, _, T, hT, _, u, gforce, _, _,
      _, _, _, _, φ, _, hsol, hinit, _, _⟩ :=
    ambient_sobolev_solution_exists_with_reparametrization
      c₀ g ht he hr hEU hleft β hG hg
  exact ⟨T, hT, _, hsol, hinit⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}

private theorem curve_shortening_local_existence_of_retraction [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {e : M → EuclideanSpace ℝ (Fin n)}
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M}
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : range e ⊆ U) (hleft : ∀ p, r (e p) = p) :
    curveShorteningLocalExistence (I := I) (M := M) B := by
  intro t₀ ht₀ c₀
  let gshift : ℝ → SmoothRiemannianMetric I M := fun s => B.family.metric (s + t₀)
  have hgshift : MetricFamilySmoothOn (D.timeShift t₀) gshift := B.smooth.timeShift t₀
  have hzero : (0 : ℝ) ∈ (D.timeShift t₀).regular := by
    change 0 + t₀ ∈ D.regular
    simpa only [zero_add] using B.regular ⟨ht₀.1, ht₀.2.le⟩
  let β : U := ⟨e (c₀.map 0), hEU (mem_range_self _)⟩
  have hG := metricFamilySmoothOn_retractionMetric gshift hgshift he hr
  obtain ⟨T, hT, c, hc, hinit⟩ :=
    SmoothImmersion.exists_solution_of_smooth_retraction
      c₀ gshift hzero he hr hEU hleft β hG hgshift
  let τ := min T (b - t₀)
  have hτ : 0 < τ := lt_min hT (sub_pos.mpr ht₀.2)
  have hτT : τ ≤ T := min_le_left _ _
  have hτb : t₀ + τ ≤ b := by
    have hle : τ ≤ b - t₀ := min_le_right _ _
    linarith
  have hmap : MapsTo (fun t : ℝ => t + -t₀) (Icc t₀ (t₀ + τ)) (Icc 0 T) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hshifted := hc.time_translate (-t₀) hmap
    (uniqueDiffOn_Icc (by linarith : t₀ < t₀ + τ))
  let d : CurveMap M := fun z t => c z (t + -t₀)
  have hd : d.IsSolutionOn (I := I) B.family.metric (Icc t₀ (t₀ + τ)) := by
    simpa only [gshift, neg_add_cancel_right] using hshifted
  refine ⟨τ, hτ, hτb, d, hd, ?_⟩
  intro z
  change c z (t₀ + -t₀) = c₀.map z
  rw [add_neg_cancel]
  exact hinit z

theorem curveShorteningLocalExistence_of_compact
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b) :
    curveShorteningLocalExistence (I := I) (M := M) B := by
  intro t₀ ht₀ c₀
  let : Nonempty M := ⟨c₀.map 0⟩
  obtain ⟨n, e, he, hemb, hi⟩ :=
    exists_embedding_euclidean_of_compact (I := I) (M := M)
  obtain ⟨r, V, hV, heV, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction
      he hemb.isEmbedding hi
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨V, hV⟩
  have hrU : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U := hr
  exact curve_shortening_local_existence_of_retraction
    (I := I) (M := M) (n := n) B he hrU heV hleft t₀ ht₀ c₀

theorem curveShorteningParabolicGaugeLocalExistence_of_compact
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b) :
    curveShorteningParabolicGaugeLocalExistence (I := I) (M := M) B := by
  intro t₀ ht₀ c₀
  obtain ⟨τ, hτ, hτb, c, hc, hinit⟩ :=
    curveShorteningLocalExistence_of_compact B t₀ ht₀ c₀
  refine ⟨τ, hτ, hτb, c, hc.smooth, hinit, ?_⟩
  intro x t ht
  have hpar := parabolic_gauge_velocity (I := I) B.family.metric c
    hc.smooth hc.immersed x t ht
  rw [hc.equation x t ht, hpar.2, add_sub_cancel_right]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
open AddCircle (parameterPrincipalOperatorHsPi parameterPrincipalOperatorH0Pi)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

variable (c₀ : SmoothImmersion (I := I) (M := M))
variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

include ht he hr hEU hleft β hG in
private theorem exists_parametric_solution_of_smooth_retraction [I.Boundaryless] :
    ∃ T : ℝ, 0 < T ∧ ∃ c : CurveMap M,
      c.SmoothOn (I := I) (Icc 0 T) ∧ c.ImmersedOn (I := I) (Icc 0 T) ∧
      (∀ z, c z 0 = c₀.map z) ∧
      ∀ x t, t ∈ Icc 0 T → c.velocity (I := I) (Icc 0 T) x t =
        c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, hsmooth⟩ :=
    ambient_sobolev_solution_exists_with_smooth_chart c₀ g ht he hr hEU hleft β hG
  let g₀ := c₀.pullbackMetric (g 0)
  let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
  let P := circleHsPiInclusion g₀ (Fin n)
    (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
  let S := circleHsPiInclusion g₀ (Fin n)
    (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
  let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
    (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
  let c : CurveMap M := fun z t => r (d z t)
  have hfinite := ambient_retraction_contMDiff_two_and_immersed_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hcsm : c.SmoothOn (I := I) (Icc 0 T) :=
    ambient_retraction_smooth_of_contDiffOn
      c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hsmooth
  have hparam := ambient_retraction_parametric_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  exact ⟨T, hT, c, hcsm, hfinite.2.2.2, hfinite.1, hparam⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Geometry.Curvature

theorem exists_parametric_solution_of_compact
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    (ht : 0 ∈ D.regular) (hg : MetricFamilySmoothOn D g) :
    ∃ T : ℝ, 0 < T ∧ ∃ c : CurveMap M,
      c.SmoothOn (I := I) (Icc 0 T) ∧ c.ImmersedOn (I := I) (Icc 0 T) ∧
      (∀ z, c z 0 = c₀.map z) ∧
      ∀ x t, t ∈ Icc 0 T → c.velocity (I := I) (Icc 0 T) x t =
        c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  let : Nonempty M := ⟨c₀.map 0⟩
  obtain ⟨n, e, he, hemb, hi⟩ :=
    exists_embedding_euclidean_of_compact (I := I) (M := M)
  obtain ⟨r, V, hV, heV, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction
      he hemb.isEmbedding hi
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨V, hV⟩
  have hrU : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U := hr
  let β : U := ⟨e (c₀.map 0), heV (mem_range_self _)⟩
  have hG := metricFamilySmoothOn_retractionMetric g hg he hrU
  exact exists_parametric_solution_of_smooth_retraction c₀ g ht he hrU heV hleft β hG

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

section

open private
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.exists_initial_interval_eq_of_parametric_curves_of_retraction from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.Uniqueness

noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open DifferentialGeometry.Geometry.Curvature

theorem exists_initial_interval_eq_of_parametric_curves_of_compact
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} {T : ℝ}
    (hT : 0 < T) (hG : MetricFamilySmoothOn D g) (hJD : Icc (0 : ℝ) T ⊆ D.regular)
    {c₁ c₂ : CurveMap M}
    (hc₁ : c₁.SmoothOn (I := I) (Icc 0 T))
    (hc₂ : c₂.SmoothOn (I := I) (Icc 0 T))
    (hi₁ : c₁.ImmersedOn (I := I) (Icc 0 T))
    (hi₂ : c₂.ImmersedOn (I := I) (Icc 0 T))
    (heq₁ : ∀ x t, t ∈ Icc 0 T → c₁.velocity (I := I) (Icc 0 T) x t =
      c₁.speed g x t ^ (-2 : ℤ) • c₁.Dx g c₁.X x t)
    (heq₂ : ∀ x t, t ∈ Icc 0 T → c₂.velocity (I := I) (Icc 0 T) x t =
      c₂.speed g x t ^ (-2 : ℤ) • c₂.Dx g c₂.X x t)
    (hinit : ∀ z, c₁ z 0 = c₂ z 0) :
    ∃ δ > 0, δ ≤ T ∧ ∀ z t, t ∈ Icc 0 δ → c₁ z t = c₂ z t := by
  classical
  let c₀ := SmoothImmersion.slice c₁ hc₁ hi₁ 0 ⟨le_rfl, hT.le⟩
  let : Nonempty M := ⟨c₀.map 0⟩
  obtain ⟨n, e, he, hemb, hi⟩ :=
    exists_embedding_euclidean_of_compact (I := I) (M := M)
  let emb : Width.SmoothLoopEmbedding (I := I) (Q := M) n := ⟨e, he, hemb, hi⟩
  obtain ⟨ret, V, hV, heV, hret, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction
      he hemb.isEmbedding hi
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨V, hV⟩
  have hretU : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ ret U := hret
  let β : U := ⟨e (c₀.map 0), heV (mem_range_self _)⟩
  have hGret := metricFamilySmoothOn_retractionMetric g hG he hretU
  exact DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.exists_initial_interval_eq_of_parametric_curves_of_retraction
    c₀ g (hJD ⟨le_rfl, hT.le⟩) emb hretU heV hleft β hGret hT
    hc₁ hc₂ hi₁ hi₂ (fun _ => rfl) (fun z => (hinit z).symm) heq₁ heq₂

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
end

end

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Geometry.Curvature

theorem exists_parametric_solution_prod_of_compact
    {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    (c₀ : SmoothImmersion (I := I.prod 𝓘(ℝ, F)) (M := M × F))
    (g : ℝ → SmoothRiemannianMetric (I.prod 𝓘(ℝ, F)) (M × F)) {D : RealTimeInterval}
    (ht : 0 ∈ D.regular) (hg : MetricFamilySmoothOn D g) :
    ∃ T : ℝ, 0 < T ∧ ∃ c : CurveMap (M × F),
      c.SmoothOn (I := I.prod 𝓘(ℝ, F)) (Icc 0 T) ∧
      c.ImmersedOn (I := I.prod 𝓘(ℝ, F)) (Icc 0 T) ∧
      (∀ z, c z 0 = c₀.map z) ∧
      ∀ x t, t ∈ Icc 0 T → c.velocity (I := I.prod 𝓘(ℝ, F)) (Icc 0 T) x t =
        c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  let : Nonempty M := ⟨(c₀.map 0).1⟩
  obtain ⟨n, e, r, V, he, hV, heV, hr, hleft⟩ :=
    DifferentialGeometry.Topology.exists_smooth_neighborhood_retraction_prod_of_compact
      (I := I) (M := M) (F := F)
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨V, hV⟩
  have hrU : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (I.prod 𝓘(ℝ, F)) ∞ r U := hr
  let β : U := ⟨e (c₀.map 0), heV (mem_range_self _)⟩
  have hG := metricFamilySmoothOn_retractionMetric g hg he hrU
  exact DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.exists_parametric_solution_of_smooth_retraction
    c₀ g ht he hrU heV hleft β hG

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

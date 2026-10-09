import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryLaunchFlow

/-!
An actual original interior launch is glued to all future existing native maximal-flow times.
The resulting original curve is smooth, geodesic and interior on its actual open time domain.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem continuation_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundary_original_launch_continuation (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      continuation_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ (γ : ℝ → M) (T : ℝ), 0 < T → ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo 0 T) →
      (∀ t ∈ Ioo 0 T, HasGeodesicEquationAt g γ t) →
      (∀ t ∈ Ioo 0 T, I.IsInteriorPoint (γ t)) →
      ∃ seed : TangentBundle 𝓘(ℝ, E) U, ∃ R : ℝ → M,
        (seed.proj : M) = γ (T / 2) ∧ R 0 = γ 0 ∧
        (∀ t ≤ T / 2, R t = γ t) ∧
        (∀ t > T / 2, R t = ((k.geodesicFlow seed (t - T / 2)).proj : M)) ∧
        IsOpen {t : ℝ | 0 < t ∧ (t < T / 2 ∨ (seed, t - T / 2) ∈ k.geodesicFlowDomain)} ∧
        ∀ t : ℝ, 0 < t → (t < T / 2 ∨ (seed, t - T / 2) ∈ k.geodesicFlowDomain) →
          ContMDiffAt 𝓘(ℝ) I ∞ R t ∧ HasGeodesicEquationAt g R t ∧ I.IsInteriorPoint (R t) := by
  classical
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    continuation_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro γ T hT hγ hgeo henter
  obtain ⟨seed, ε, hε, heT, hbase, hmatch, hfull⟩ :=
    boundary_original_launch_flow g γ T hT hγ hgeo henter
  let a := T / 2
  let η : ℝ → M := fun t => ((k.geodesicFlow seed (t - a)).proj : M)
  let R : ℝ → M := fun t => if t ≤ a then γ t else η t
  have ha : 0 < a := by dsimp only [a]; positivity
  have haT : a < T := by dsimp only [a]; linarith
  have hηsmooth (t : ℝ) (ht : (seed, t - a) ∈ k.geodesicFlowDomain) :
      ContMDiffAt 𝓘(ℝ) I ∞ η t := by
    have htime : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => s - a) t :=
      contMDiffAt_id.sub contMDiffAt_const
    have houter : ContMDiffAt 𝓘(ℝ) I ∞
        (fun s : ℝ => ((k.geodesicFlow seed s).proj : M)) (t - a) :=
      (hfull (t - a) ht).1
    exact houter.comp (f := fun s : ℝ => s - a) t htime
  have hηgeo (t : ℝ) (ht : (seed, t - a) ∈ k.geodesicFlowDomain) :
      HasGeodesicEquationAt g η t := by
    simpa only [η, one_mul, sub_eq_add_neg] using hasGeodesicEquationAt_comp_affine
      (c := 1) (d := -a) (t := t)
      (by simpa only [one_mul, sub_eq_add_neg] using (hfull (t - a) ht).2.1)
  have hηinterior (t : ℝ) (ht : (seed, t - a) ∈ k.geodesicFlowDomain) :
      I.IsInteriorPoint (η t) := (hfull (t - a) ht).2.2
  have hjoin : R =ᶠ[𝓝 a] η := by
    filter_upwards [Metric.ball_mem_nhds a hε] with t ht
    by_cases hta : t ≤ a
    · have hs : t - a ∈ Metric.ball (0 : ℝ) ε := by
        simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
      have heq := (hmatch (t - a) hs).2.symm
      change (if t ≤ a then γ t else η t) = η t
      rw [ite_eq_left hta]
      simpa only [a, sub_add_cancel] using heq
    · simp only [R, ite_eq_right hta]
  have hopen : IsOpen {t : ℝ | 0 < t ∧ (t < a ∨
      (seed, t - a) ∈ k.geodesicFlowDomain)} := by
    change IsOpen (Ioi (0 : ℝ) ∩ (Iio a ∪
      (fun t : ℝ => (seed, t - a)) ⁻¹' k.geodesicFlowDomain))
    exact isOpen_Ioi.inter (isOpen_Iio.union
      ((k.isOpen_geodesicFlowDomain (r := ⊤) le_top).preimage
        (continuous_const.prodMk (continuous_id.sub continuous_const))))
  refine ⟨seed, R, hbase, ?_, ?_, ?_, hopen, ?_⟩
  · simp only [R, ite_eq_left ha.le]
  · intro t ht
    exact ite_eq_left ht
  · intro t ht
    exact ite_eq_right (not_le.mpr ht)
  · intro t ht hdomain
    by_cases hta : t < a
    · have htT : t ∈ Ioo 0 T := ⟨ht, hta.trans haT⟩
      have hev : R =ᶠ[𝓝 t] γ := by
        filter_upwards [isOpen_Iio.mem_nhds hta] with s hs
        exact ite_eq_left hs.le
      have hsmooth := (hγ.contMDiffAt (isOpen_Ioo.mem_nhds htT)).congr_of_eventuallyEq hev
      have hequation := HasGeodesicEquationAt.congr_of_eventuallyEq_at
        hev.eq_of_nhds hev (hgeo t htT)
      have hinterior : I.IsInteriorPoint (R t) := by
        rw [hev.eq_of_nhds]
        exact henter t htT
      exact ⟨hsmooth, hequation, hinterior⟩
    · have hflow : (seed, t - a) ∈ k.geodesicFlowDomain := hdomain.resolve_left hta
      have hev : R =ᶠ[𝓝 t] η := by
        by_cases hat : a < t
        · filter_upwards [isOpen_Ioi.mem_nhds hat] with s hs
          exact ite_eq_right (not_le.mpr hs)
        · have htaeq : t = a := le_antisymm (le_of_not_gt hat) (le_of_not_gt hta)
          rw [htaeq]
          exact hjoin
      have hsmooth := (hηsmooth t hflow).congr_of_eventuallyEq hev
      have hequation := HasGeodesicEquationAt.congr_of_eventuallyEq_at
        hev.eq_of_nhds hev (hηgeo t hflow)
      have hinterior : I.IsInteriorPoint (R t) := by
        rw [hev.eq_of_nhds]
        exact hηinterior t hflow
      exact ⟨hsmooth, hequation, hinterior⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

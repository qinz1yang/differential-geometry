import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Variation.Monotonicity
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

set_option autoImplicit false

open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Bundle Filter MeasureTheory DifferentialGeometry.Tensor0SBundle

open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology

universe u uE uH

variable {M : Type u}

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [T2Space M] in
private theorem eq_zero_of_integral_mul_pos_weight_eq_zero
    (μ : Measure M) [μ.IsOpenPosMeasure]
    (ρ Sq : M -> Real)
    (hρc : Continuous ρ) (hρpos : ∀ x : M, 0 < ρ x)
    (hSqc : Continuous Sq) (hSq0 : ∀ x : M, 0 ≤ Sq x)
    (hint : Integrable (fun x : M => ρ x * Sq x) μ)
    (hzero : (∫ x, ρ x * Sq x ∂μ) = 0) :
    ∀ x : M, Sq x = 0 := by
  have hprod : Continuous (fun x : M => ρ x * Sq x) := hρc.mul hSqc
  have hae : (fun x : M => ρ x * Sq x) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun x : M => mul_nonneg (hρpos x).le (hSq0 x)) hint).mp hzero
  intro x
  have hall : ρ x * Sq x = 0 :=
    congrFun (Measure.eq_of_ae_eq hae hprod continuous_const) x
  rcases mul_eq_zero.mp hall with h | h
  · exact absurd h (hρpos x).ne'
  · exact h

theorem wEntropyFirstVariation_eq_neg_two_mul_tau_integral_square
    [I.Boundaryless] [CompactSpace M]
    {D Dr : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (u : Real -> M -> Real)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn Dr
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) T)
      (fun r x =>
        (conjCoeff (I := I) (M := M) S (T - r) : M -> Real) x) u)
    (hpos : ∀ r : Real, r ∈ Dr.regular ∩ Set.Ioi (0 : Real) ->
      ∀ x : M, 0 < u r x)
    {s : Real} (hs : s ∈ Dr.regular) (hspos : 0 < s)
    (hTs : T - s ∈ D.regular) :
    let n := Module.finrank Real E
    let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
    let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
    let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
    let q : Real -> M -> Real := fun r x =>
      (G.metric r).inner x
        (gradientFun (I := I) (G.metric r) (f r) x)
        (gradientFun (I := I) (G.metric r) (f r) x)
    let hf : ContMDiff I 𝓘(Real, Real) ∞ (f s) := by
      simpa only [f] using
        potential_slice (I := I) Dr G
          (fun r x =>
            (conjCoeff (I := I) (M := M) S (T - r) : M -> Real) x)
          u n hu hs hspos (hpos s ⟨hs, hspos⟩)
    let Sq : M -> Real := fun x =>
      normSq0S (I := I) (G.metric s) x 2
        (metricRicciAt (I := I) (M := M) (G.metric s) x +
          hessianSec (I := I)
            (metricCov (I := I) (M := M) (G.metric s))
            (metricCov_smooth (I := I) (M := M) (G.metric s))
            (f s) hf x -
          (1 / (2 * s)) • metricTensor0S (I := I) (G.metric s) x)
    wEntropyFirstVariation
      (volumeMeasureFamily (I := I) (M := M) G)
      n (fun r : Real => r) R q f s =
      -2 * s *
        ∫ x, perelmanDensity n s (f s) x * Sq x
          ∂(volumeMeasureFamily (I := I) (M := M) G s) := by
  classical
  dsimp only
  exact wEntropyFirstVariation_eq_of_hasFirstVariationAt
    (w_rev_square (I := I) S hS T u hu hpos hs hspos hTs)

theorem wEntropyFirstVariation_eq_zero_iff_soliton_equation
    [I.Boundaryless] [CompactSpace M]
    {D Dr : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (u : Real -> M -> Real)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn Dr
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) T)
      (fun r x =>
        (conjCoeff (I := I) (M := M) S (T - r) : M -> Real) x) u)
    (hpos : ∀ r : Real, r ∈ Dr.regular ∩ Set.Ioi (0 : Real) ->
      ∀ x : M, 0 < u r x)
    {s : Real} (hs : s ∈ Dr.regular) (hspos : 0 < s)
    (hTs : T - s ∈ D.regular) :
    let n := Module.finrank Real E
    let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
    let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
    let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
    let q : Real -> M -> Real := fun r x =>
      (G.metric r).inner x
        (gradientFun (I := I) (G.metric r) (f r) x)
        (gradientFun (I := I) (G.metric r) (f r) x)
    let hf : ContMDiff I 𝓘(Real, Real) ∞ (f s) := by
      simpa only [f] using
        potential_slice (I := I) Dr G
          (fun r x =>
            (conjCoeff (I := I) (M := M) S (T - r) : M -> Real) x)
          u n hu hs hspos (hpos s ⟨hs, hspos⟩)
    wEntropyFirstVariation
      (volumeMeasureFamily (I := I) (M := M) G)
      n (fun r : Real => r) R q f s = 0 ↔
      ∀ x : M,
        metricRicciAt (I := I) (M := M) (G.metric s) x +
          hessianSec (I := I)
            (metricCov (I := I) (M := M) (G.metric s))
            (metricCov_smooth (I := I) (M := M) (G.metric s))
            (f s) hf x =
          (1 / (2 * s)) • metricTensor0S (I := I) (G.metric s) x := by
  classical
  dsimp only
  let n := Module.finrank Real E
  let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
  let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
  let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
  let q : Real -> M -> Real := fun r x =>
    (G.metric r).inner x
      (gradientFun (I := I) (G.metric r) (f r) x)
      (gradientFun (I := I) (G.metric r) (f r) x)
  let g := G.metric s
  let hf : ContMDiff I 𝓘(Real, Real) ∞ (f s) := by
    simpa only [f] using
      potential_slice (I := I) Dr G
        (fun r x =>
          (conjCoeff (I := I) (M := M) S (T - r) : M -> Real) x)
        u n hu hs hspos (hpos s ⟨hs, hspos⟩)
  let μ := volumeMeasureFamily (I := I) (M := M) G s
  let ρ : M -> Real := perelmanDensity n s (f s)
  let A : (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x := fun x =>
    metricRicciAt (I := I) (M := M) g x +
      hessianSec (I := I)
        (metricCov (I := I) (M := M) g)
        (metricCov_smooth (I := I) (M := M) g)
        (f s) hf x -
      (1 / (2 * s)) • metricTensor0S (I := I) g x
  let Sq : M -> Real := fun x => normSq0S (I := I) g x 2 (A x)
  have hident :
      wEntropyFirstVariation
        (volumeMeasureFamily (I := I) (M := M) G)
        n (fun r : Real => r) R q f s =
        -2 * s * ∫ x, ρ x * Sq x ∂μ := by
    simpa only [n, G, f, R, q, g, μ, ρ, A, Sq] using
      wEntropyFirstVariation_eq_neg_two_mul_tau_integral_square
        (I := I) S hS T u hu hpos hs hspos hTs
  have hρpos : ∀ x : M, 0 < ρ x := by
    intro x
    have hd : ρ = u s := by
      simpa only [ρ, f] using
        density_potential n (u s) hspos (hpos s ⟨hs, hspos⟩)
    rw [hd]
    exact hpos s ⟨hs, hspos⟩ x
  have hρc : Continuous ρ := by
    have hd : ρ = u s := by
      simpa only [ρ, f] using
        density_potential n (u s) hspos (hpos s ⟨hs, hspos⟩)
    rw [hd]
    exact (hu.sliceSmooth s (Dr.regular_subset hs)).continuous
  have hSqc : Continuous Sq := by
    let Ric := metricRicci (I := I) (M := M) g
    let Hess := hessianSec (I := I) (metricCov (I := I) (M := M) g)
      (metricCov_smooth (I := I) (M := M) g) (f s) hf
    let K : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2 :=
      Ric + Hess - (1 / (2 * s)) • metricTensorField (I := I) g
    have hK := normSq02_smooth (I := I) g K
    refine hK.continuous.congr (fun x => ?_)
    have hmetric : metricTensorField (I := I) g x =
        metricTensor0S (I := I) g x := by
      ext v
      rw [metricTensorField_apply, metricTensor0S_apply]
    change
      normSq0S (I := I) g x 2
          (Ric x + Hess x - (1 / (2 * s)) • metricTensorField (I := I) g x) =
        normSq0S (I := I) g x 2 (A x)
    rw [hmetric]
    simp only [A, Ric, Hess, metricRicci_apply]
  have hSq0 : ∀ x : M, 0 ≤ Sq x := fun x =>
    normSq0S_nonneg (I := I) g x 2 _
  have hcontprod : Continuous (fun x : M => ρ x * Sq x) := hρc.mul hSqc
  let : IsFiniteMeasureOnCompacts μ := by
    change IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I) (M := M) g)
    exact riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have hint : Integrable (fun x : M => ρ x * Sq x) μ :=
    hcontprod.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  constructor
  · intro hzero
    rw [hident] at hzero
    have hI : (∫ x, ρ x * Sq x ∂μ) = 0 := by
      have hne : (-2 : Real) * s ≠ 0 := mul_ne_zero (by norm_num) hspos.ne'
      exact (mul_eq_zero.mp hzero).resolve_left hne
    let : μ.IsOpenPosMeasure :=
      riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
    have hall := eq_zero_of_integral_mul_pos_weight_eq_zero μ ρ Sq hρc hρpos hSqc hSq0 hint hI
    intro x
    have hallx : Sq x = 0 := hall x
    change normSq0S (I := I) g x 2 (A x) = 0 at hallx
    have hAx : A x = 0 := (normSq0S_eq_zero_iff (I := I) g x 2 (A x)).mp hallx
    change metricRicciAt (I := I) (M := M) g x +
        hessianSec (I := I) (metricCov (I := I) (M := M) g)
          (metricCov_smooth (I := I) (M := M) g) (f s) hf x -
        (1 / (2 * s)) • metricTensor0S (I := I) g x = 0 at hAx
    exact sub_eq_zero.mp hAx
  · intro hsol
    have hSqzero : ∀ x : M, Sq x = 0 := by
      intro x
      change normSq0S (I := I) g x 2 (A x) = 0
      refine (normSq0S_eq_zero_iff (I := I) g x 2 (A x)).mpr ?_
      have hg : g = (reverseFamily (I := I) (M := M) (flowG (I := I) S) T).metric s :=
        rfl
      have hsol' : metricRicciAt (I := I) (M := M) g x +
          hessianSec (I := I) (metricCov (I := I) (M := M) g)
            (metricCov_smooth (I := I) (M := M) g) (f s) hf x =
          (1 / (2 * s)) • metricTensor0S (I := I) g x := by
        simpa only [hg] using hsol x
      exact sub_eq_zero.mpr hsol'
    have hI0 : (∫ x, ρ x * Sq x ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with x
      exact mul_eq_zero_of_right (ρ x) (hSqzero x)
    rw [hident, hI0]
    ring

section Sharpness

theorem exists_pos_density_ae_zero_not_eq_zero :
    ∃ ρ Sq : Real -> Real,
      (∀ x : Real, 0 < ρ x) ∧ (∀ x : Real, 0 ≤ Sq x) ∧
        (∀ᵐ x ∂(volume : Measure Real), ρ x * Sq x = 0) ∧
        (¬ ∀ x : Real, Sq x = 0) ∧ ¬ Continuous Sq := by
  refine ⟨fun _ => 1, Set.indicator ({0} : Set Real) (fun _ => (1 : Real)),
    fun _ => zero_lt_one, fun x => ?_, ?_, ?_, ?_⟩
  · by_cases hx : x = 0 <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  · rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_
      (show (volume : Measure Real) ({0} : Set Real) = 0 from Real.volume_singleton)
    intro x hx
    by_contra hx0
    exact hx (by simp [Set.indicator_of_notMem, hx0])
  · intro hone
    have h0 : ({0} : Set Real).indicator (fun _ => (1 : Real)) 0 = 0 := hone 0
    have h1 : ({0} : Set Real).indicator (fun _ => (1 : Real)) 0 = 1 := by simp
    rw [h1] at h0
    exact one_ne_zero h0
  · intro hc
    have hlim1 : Tendsto (Set.indicator ({0} : Set Real) (fun _ => (1 : Real)))
        (𝓝[≠] (0 : Real))
        (𝓝 (Set.indicator ({0} : Set Real) (fun _ => (1 : Real)) 0)) :=
      hc.continuousAt.tendsto.mono_left inf_le_left
    have hlim0 : Tendsto (Set.indicator ({0} : Set Real) (fun _ => (1 : Real)))
        (𝓝[≠] (0 : Real)) (𝓝 (0 : Real)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (Set.indicator_of_notMem hx (fun _ => (1 : Real))).symm
    have hz := tendsto_nhds_unique hlim1 hlim0
    have h1 : ({0} : Set Real).indicator (fun _ => (1 : Real)) 0 = 1 := by simp
    rw [h1] at hz
    exact one_ne_zero hz

theorem exists_zero_density_integral_zero_not_eq_zero :
    ∃ ρ Sq : Real -> Real,
      (∀ x : Real, 0 ≤ ρ x) ∧ (∀ x : Real, 0 ≤ Sq x) ∧
        Continuous ρ ∧ Continuous Sq ∧
        (∫ x, ρ x * Sq x ∂(volume : Measure Real)) = 0 ∧
        ¬ ∀ x : Real, Sq x = 0 := by
  refine ⟨fun _ => 0, fun _ => 1, fun _ => le_refl 0, fun _ => zero_le_one,
    continuous_const, continuous_const, ?_, ?_⟩
  · simp
  · intro h
    exact one_ne_zero (h 0)

end Sharpness

end

end DifferentialGeometry.PDE.RicciFlow.Entropy

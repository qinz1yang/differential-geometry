import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.UrysohnsLemma

noncomputable section

open Filter MeasureTheory Set
open scoped CompactlySupported Topology

namespace DifferentialGeometry.Analysis.Measure

theorem tendsto_mass_of_integral_tendsto_of_tight
    {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [T2Space X] [LocallyCompactSpace X]
    {F : Filter ι} {mus : ι → FiniteMeasure X} {mu : FiniteMeasure X}
    (hlocal : ∀ f : C_c(X, ℝ),
      Tendsto (fun i ↦ ∫ x, f x ∂(mus i : Measure X)) F
        (𝓝 (∫ x, f x ∂(mu : Measure X))))
    (htail : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set X, IsCompact K ∧
        (∀ᶠ i in F, ((mus i) Kᶜ : ℝ) ≤ ε) ∧
        (mu Kᶜ : ℝ) ≤ ε) :
    Tendsto (fun i ↦ (mus i).mass) F (𝓝 mu.mass) := by
  rw [← NNReal.tendsto_coe, Metric.tendsto_nhds]
  intro ε hε
  have hεhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨K, hK, htail_mus, htail_mu⟩ := htail (ε / 2) hεhalf
  obtain ⟨f, hfK, hfrange⟩ :
      ∃ f : C_c(X, ℝ), EqOn (⇑f) 1 K ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨f, hfK, hfsupp, -, hfrange⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen
        hK isOpen_univ K.subset_univ
    exact ⟨⟨f, hasCompactSupport_def.mpr hfsupp⟩, hfK, hfrange⟩
  have hKle (x : X) : K.indicator 1 x ≤ f x := by
    by_cases hx : x ∈ K
    · simp [hx, hfK hx]
    · simp [hx, (hfrange x).1]
  have hlow (nu : FiniteMeasure X) :
      (nu K : ℝ) ≤ ∫ x, f x ∂(nu : Measure X) := by
    calc
      (nu K : ℝ) = (nu : Measure X).real K := by simp
      _ = ∫ x, K.indicator 1 x ∂(nu : Measure X) :=
        (integral_indicator_one hK.measurableSet).symm
      _ ≤ ∫ x, f x ∂(nu : Measure X) := by
        refine integral_mono ?_ f.integrable hKle
        exact (continuousOn_const.integrableOn_compact hK).integrable_indicator
          hK.measurableSet
  have hhigh (nu : FiniteMeasure X) :
      ∫ x, f x ∂(nu : Measure X) ≤ (nu.mass : ℝ) := by
    calc
      (∫ x, f x ∂(nu : Measure X)) ≤ ∫ _ : X, (1 : ℝ) ∂(nu : Measure X) := by
        exact integral_mono f.integrable (integrable_const 1) fun x ↦ (hfrange x).2
      _ = (nu.mass : ℝ) := by simp [FiniteMeasure.mass]
  have hmass_le (nu : FiniteMeasure X) :
      (nu.mass : ℝ) ≤ ∫ x, f x ∂(nu : Measure X) + (nu Kᶜ : ℝ) := by
    have hsplit : (nu.mass : ℝ) = (nu K : ℝ) + (nu Kᶜ : ℝ) := by
      simpa [FiniteMeasure.mass] using
        (measureReal_add_measureReal_compl
          (μ := (nu : Measure X)) hK.measurableSet).symm
    rw [hsplit]
    exact add_le_add (hlow nu) le_rfl
  have hlocal_f :
      ∀ᶠ i in F,
        dist (∫ x, f x ∂(mus i : Measure X))
          (∫ x, f x ∂(mu : Measure X)) < ε / 2 :=
    (Metric.tendsto_nhds.1 (hlocal f)) (ε / 2) hεhalf
  filter_upwards [htail_mus, hlocal_f] with i htail_i hlocal_i
  rw [Real.dist_eq] at hlocal_i ⊢
  apply abs_lt.2
  constructor
  · have hlocal_lower := (abs_lt.1 hlocal_i).1
    linarith [hmass_le mu, hhigh (mus i), htail_mu]
  · have hlocal_upper := (abs_lt.1 hlocal_i).2
    linarith [hmass_le (mus i), hhigh mu, htail_i]

end DifferentialGeometry.Analysis.Measure

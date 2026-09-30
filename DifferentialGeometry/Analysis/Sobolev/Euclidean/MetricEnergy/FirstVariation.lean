import DifferentialGeometry.Analysis.Sobolev.Euclidean.Variation
import DifferentialGeometry.Analysis.Integration.Lp.QuadraticBounds
import DifferentialGeometry.Analysis.Calculus.Variation.Quadratic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Locality
import Mathlib.Topology.MetricSpace.Thickening

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

section Measurability

private theorem aestronglyMeasurable_clm_apply
    {α X Y : Type*} [MeasurableSpace α] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {μ : Measure α}
    {f : α → X →L[ℝ] Y} {u : α → X}
    (hf : AEStronglyMeasurable f μ) (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x => f x (u x)) μ :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hf.prodMk hu)

private theorem aestronglyMeasurable_comp_of_continuousOn
    {α X Y : Type*} [MeasurableSpace α] [NormedAddCommGroup X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    {μ : Measure α} {f : X → Y} {V : Set X} (hV : MeasurableSet V)
    (hf : ContinuousOn f V) {u : α → X} (hu : AEStronglyMeasurable u μ)
    (huV : ∀ᵐ x ∂μ, u x ∈ V) : AEStronglyMeasurable (fun x => f (u x)) μ := by
  classical
  have hm : Measurable (V.piecewise f (fun _ => 0)) :=
    hf.measurable_piecewise continuousOn_const hV
  exact (hm.comp_aemeasurable hu.aemeasurable).aestronglyMeasurable.congr
    (huV.mono fun x hx => Set.piecewise_eq_of_mem V f (fun _ => 0) hx)

end Measurability

section Integral

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
local instance metricFormNormedAdd : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance metricFormNormedSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance metricDerivNormedAdd : NormedAddCommGroup (F →L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance metricDerivNormedSpace : NormedSpace ℝ (F →L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedSpace

private theorem hasDerivAt_integral_metric_energy
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {u φ : α → F} (hu : AEStronglyMeasurable u μ) (hφm : AEStronglyMeasurable φ μ)
    {v w : ι → α → F} (hv : ∀ j, MemLp (v j) 2 μ) (hw : ∀ j, MemLp (w j) 2 μ)
    {A : F → F →L[ℝ] F →L[ℝ] ℝ} {V K : Set F}
    (hV : IsOpen V) (hA : ContDiffOn ℝ 1 A V) (hK : IsCompact K) (hKV : K ⊆ V)
    (huK : ∀ᵐ x ∂μ, u x ∈ K) (P : ℝ) (hP : 0 ≤ P) (hφ : ∀ x, ‖φ x‖ ≤ P) :
    Integrable (fun x => (∑ j : ι,
      ((fderiv ℝ A (u x) (φ x)) (v j x) (v j x) +
        A (u x) (w j x) (v j x) + A (u x) (v j x) (w j x)))) μ ∧
    HasDerivAt (fun t : ℝ => ∫ x, ∑ j : ι,
      A (u x + t • φ x) (v j x + t • w j x) (v j x + t • w j x) ∂μ)
      (∫ x, (∑ j : ι, ((fderiv ℝ A (u x) (φ x)) (v j x) (v j x) +
        A (u x) (w j x) (v j x) + A (u x) (v j x) (w j x))) ∂μ) 0 := by
  classical
  borelize F (F →L[ℝ] F →L[ℝ] ℝ) (F →L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ))
  obtain ⟨δ₀, hδ₀, C, hC, hbounds⟩ := exists_compact_metric_range_bounds hV hA hK hKV P hP
  let δ := min δ₀ 1
  have hδ : 0 < δ := lt_min hδ₀ zero_lt_one
  have hδ₀le : δ ≤ δ₀ := min_le_left _ _
  have hδone : δ ≤ 1 := min_le_right _ _
  let U := fun (t : ℝ) (x : α) => u x + t • φ x
  let W := fun (t : ℝ) (j : ι) (x : α) => v j x + t • w j x
  let f := fun (t : ℝ) (x : α) => ∑ j : ι, A (U t x) (W t j x) (W t j x)
  let f' := fun (t : ℝ) (x : α) => ∑ j : ι, ((fderiv ℝ A (U t x) (φ x)) (W t j x) (W t j x) +
      A (U t x) (w j x) (W t j x) + A (U t x) (W t j x) (w j x))
  have hbu (x : α) (hx : u x ∈ K) (t : ℝ) (ht : |t| < δ) :
      U t x ∈ V ∧ ‖A (U t x)‖ ≤ C ∧ ‖fderiv ℝ A (U t x)‖ ≤ C :=
    hbounds (u x) hx (φ x) (hφ x) t (ht.trans_le hδ₀le)
  have hUm (t : ℝ) : AEStronglyMeasurable (U t) μ := hu.add (hφm.const_smul t)
  have hWm (t : ℝ) (j : ι) : AEStronglyMeasurable (W t j) μ :=
    (hv j).aestronglyMeasurable.add ((hw j).aestronglyMeasurable.const_smul t)
  have hAm (t : ℝ) (ht : |t| < δ) : AEStronglyMeasurable (fun x => A (U t x)) μ :=
    aestronglyMeasurable_comp_of_continuousOn hV.measurableSet hA.continuousOn (hUm t)
      (huK.mono fun x hx => (hbu x hx t ht).1)
  have hDAm (t : ℝ) (ht : |t| < δ) : AEStronglyMeasurable (fun x => fderiv ℝ A (U t x)) μ :=
    aestronglyMeasurable_comp_of_continuousOn hV.measurableSet
      (hA.continuousOn_fderiv_of_isOpen hV le_rfl) (hUm t)
      (huK.mono fun x hx => (hbu x hx t ht).1)
  have hfm (t : ℝ) (ht : |t| < δ) : AEStronglyMeasurable (f t) μ := by
    have hh := Finset.aestronglyMeasurable_sum Finset.univ (fun (j : ι) _ =>
      aestronglyMeasurable_clm_apply
        (aestronglyMeasurable_clm_apply (hAm t ht) (hWm t j)) (hWm t j))
    convert hh using 1
    funext x
    simp only [f, Finset.sum_apply]
  have hf'm (t : ℝ) (ht : |t| < δ) : AEStronglyMeasurable (f' t) μ := by
    have hh := Finset.aestronglyMeasurable_sum Finset.univ (fun (j : ι) _ =>
      ((aestronglyMeasurable_clm_apply
        (aestronglyMeasurable_clm_apply (aestronglyMeasurable_clm_apply (hDAm t ht) hφm)
          (hWm t j)) (hWm t j)).add
        (aestronglyMeasurable_clm_apply
          (aestronglyMeasurable_clm_apply (hAm t ht) (hw j).aestronglyMeasurable) (hWm t j))).add
        (aestronglyMeasurable_clm_apply
          (aestronglyMeasurable_clm_apply (hAm t ht) (hWm t j)) (hw j).aestronglyMeasurable))
    convert hh using 1
    funext x
    simp only [f', Finset.sum_apply, Pi.add_apply]
  have hf0 : Integrable (f 0) μ := by
    refine (integrable_sum_norm_sq hv C).mono' (hfm 0 (by simpa using hδ)) ?_
    filter_upwards [huK] with x hx
    simp only [f, U, W, zero_smul, add_zero]
    calc
      ‖∑ j : ι, A (u x) (v j x) (v j x)‖ ≤ ∑ j : ι, ‖A (u x) (v j x) (v j x)‖ := norm_sum_le _ _
      _ ≤ ∑ j : ι, C * ‖v j x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hAy : ‖A (u x)‖ ≤ C := by simpa only [U, zero_smul, add_zero] using
          (hbu x hx 0 (by simpa using hδ)).2.1
        calc
          _ ≤ ‖A (u x)‖ * ‖v j x‖ * ‖v j x‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
          _ ≤ C * ‖v j x‖ * ‖v j x‖ := by gcongr
          _ = C * ‖v j x‖ ^ 2 := by ring
      _ = C * ∑ j : ι, ‖v j x‖ ^ 2 := (Finset.mul_sum ..).symm
  have hdiff (x : α) (hx : u x ∈ K) (t : ℝ) (ht : |t| < δ) :
      HasDerivAt (fun s => f s x) (f' t x) t := by
    have hh := HasDerivAt.sum (u := Finset.univ) (fun (j : ι) _ =>
      hasDerivAt_quadraticVariation A (u x) (φ x) (v j x) (w j x) t
        ((hA.contDiffAt (hV.mem_nhds (hbu x hx t ht).1)).differentiableAt (by norm_num)))
    convert hh using 1; try rfl
    funext s
    simp only [f, U, W, Finset.sum_apply]
  have hnear : Metric.ball (0 : ℝ) δ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hδ
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := f) (F' := f') (bound := fun x => C * ∑ j : ι,
      (P * (‖v j x‖ + ‖w j x‖) ^ 2 + 2 * ‖w j x‖ * (‖v j x‖ + ‖w j x‖))) hnear
    (by
      filter_upwards [hnear] with t ht
      exact hfm t (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht))
    hf0 (hf'm 0 (by simpa using hδ)) ?_
    (integrable_sum_quadratic_bound hv hw C P) ?_
  · simpa only [f, f', U, W, zero_smul, add_zero] using hresult
  · filter_upwards [huK] with x hx t ht
    have ht' : |t| < δ := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    dsimp only [f']
    calc
      ‖∑ j : ι, ((fderiv ℝ A (U t x) (φ x)) (W t j x) (W t j x) +
          A (U t x) (w j x) (W t j x) + A (U t x) (W t j x) (w j x))‖ ≤
        ∑ j : ι, ‖(fderiv ℝ A (U t x) (φ x)) (W t j x) (W t j x) +
          A (U t x) (w j x) (W t j x) + A (U t x) (W t j x) (w j x)‖ := norm_sum_le _ _
      _ ≤ ∑ j : ι, C * (P * (‖v j x‖ + ‖w j x‖) ^ 2 + 2 * ‖w j x‖ * (‖v j x‖ + ‖w j x‖)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hAt := (hA.contDiffAt (hV.mem_nhds (hbu x hx t ht').1)).differentiableAt (by norm_num)
        rw [← (hasDerivAt_quadraticVariation A (u x) (φ x) (v j x) (w j x) t hAt).deriv]
        exact norm_deriv_quadraticVariation_le A (u x) (φ x) (v j x) (w j x) t C P hAt
          (ht'.le.trans hδone) (hφ x) (hbu x hx t ht').2.1 (hbu x hx t ht').2.2
      _ = C * ∑ j : ι,
          (P * (‖v j x‖ + ‖w j x‖) ^ 2 + 2 * ‖w j x‖ * (‖v j x‖ + ‖w j x‖)) :=
        (Finset.mul_sum ..).symm
  · exact huK.mono fun x hx t ht => hdiff x hx t
      (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht)

end Integral

section SobolevCoordinates

variable {d n : ℕ}

local instance energyFormNormedAdd :
    NormedAddCommGroup ((EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance energyFormNormedSpace :
    NormedSpace ℝ ((EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable {Ω : Set (EuclideanSpace ℝ (Fin d))}
  {u : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin n))}

def metricDirichletEnergy
    (A : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)
    (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω) : ℝ :=
  ∫ x in Ω, ∑ j : Fin d,
    A (u x) (DeGiorgi.weakGradientColumn hu x j) (DeGiorgi.weakGradientColumn hu x j)

theorem metricDirichletEnergy_affine_variation_zero
    (hΩ : IsOpen Ω) (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω)
    (A : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)
    {φ : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin n))}
    (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ) :
    metricDirichletEnergy A (DeGiorgi.componentAffineVariationWitness hΩ hu hφ hφs 0) =
      metricDirichletEnergy A hu := by
  unfold metricDirichletEnergy
  simp only [DeGiorgi.weakGradientColumn_componentAffineVariationWitness, zero_smul, add_zero]


theorem hasDerivAt_metricDirichletEnergy_affine_variation
    (hΩ : IsOpen Ω) (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω)
    {A : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ} {V K : Set (EuclideanSpace ℝ (Fin n))}
    (hV : IsOpen V) (hA : ContDiffOn ℝ 1 A V) (hK : IsCompact K) (hKV : K ⊆ V)
    (huK : ∀ᵐ x ∂volume.restrict Ω, u x ∈ K)
    (hsym : ∀ y ∈ K, ∀ v w : (EuclideanSpace ℝ (Fin n)), A y v w = A y w v)
    {φ : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin n))}
    (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ) :
    IntegrableOn (fun x => ∑ j : Fin d,
      ((fderiv ℝ A (u x) (φ x)) (DeGiorgi.weakGradientColumn hu x j)
          (DeGiorgi.weakGradientColumn hu x j) +
        2 * A (u x) (DeGiorgi.weakGradientColumn hu x j)
          (fderiv ℝ φ x (EuclideanSpace.single j 1)))) Ω ∧
    HasDerivAt (fun t : ℝ => metricDirichletEnergy A
      (DeGiorgi.componentAffineVariationWitness hΩ hu hφ hφs t))
      (∫ x in Ω, (∑ j : Fin d,
        ((fderiv ℝ A (u x) (φ x)) (DeGiorgi.weakGradientColumn hu x j)
            (DeGiorgi.weakGradientColumn hu x j) +
          2 * A (u x) (DeGiorgi.weakGradientColumn hu x j)
            (fderiv ℝ φ x (EuclideanSpace.single j 1))))) 0 := by
  classical
  have hum : AEStronglyMeasurable u (volume.restrict Ω) :=
    (MemLp.of_eval_piLp fun i => (hu i).memLp).aestronglyMeasurable
  have hφm : AEStronglyMeasurable φ (volume.restrict Ω) := hφ.continuous.aestronglyMeasurable
  have hv (j : Fin d) : MemLp (fun x => DeGiorgi.weakGradientColumn hu x j) 2
      (volume.restrict Ω) := DeGiorgi.weakGrad_column_memLp hu j
  have hw (j : Fin d) : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) 2
      (volume.restrict Ω) := by
    have hc : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hc.memLp_of_hasCompactSupport (μ := volume) (p := 2)
      (hφs.fderiv_apply (𝕜 := ℝ) _)).restrict Ω
  obtain ⟨P₀, hP₀⟩ := hφ.continuous.bounded_above_of_compact_support hφs
  let P := max P₀ 0
  have hP : 0 ≤ P := le_max_right _ _
  have hPφ : ∀ x, ‖φ x‖ ≤ P := fun x => (hP₀ x).trans (le_max_left _ _)
  obtain ⟨hint, hderiv⟩ := hasDerivAt_integral_metric_energy hum hφm hv hw hV hA hK hKV huK P hP hPφ
  have heq : (fun x => ∑ j : Fin d,
        ((fderiv ℝ A (u x) (φ x)) (DeGiorgi.weakGradientColumn hu x j)
            (DeGiorgi.weakGradientColumn hu x j) +
          A (u x) (fderiv ℝ φ x (EuclideanSpace.single j 1)) (DeGiorgi.weakGradientColumn hu x j) +
          A (u x) (DeGiorgi.weakGradientColumn hu x j)
            (fderiv ℝ φ x (EuclideanSpace.single j 1)))) =ᵐ[volume.restrict Ω]
      (fun x => ∑ j : Fin d,
        ((fderiv ℝ A (u x) (φ x)) (DeGiorgi.weakGradientColumn hu x j)
            (DeGiorgi.weakGradientColumn hu x j) +
          2 * A (u x) (DeGiorgi.weakGradientColumn hu x j)
            (fderiv ℝ φ x (EuclideanSpace.single j 1)))) := by
    filter_upwards [huK] with x hx
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym (u x) hx (fderiv ℝ φ x (EuclideanSpace.single j 1))
      (DeGiorgi.weakGradientColumn hu x j)]
    ring
  refine ⟨hint.congr heq, ?_⟩
  have hfunc : (fun t : ℝ => metricDirichletEnergy A
      (DeGiorgi.componentAffineVariationWitness hΩ hu hφ hφs t)) =
      (fun t : ℝ => ∫ x in Ω, ∑ j : Fin d,
        A (u x + t • φ x)
          (DeGiorgi.weakGradientColumn hu x j + t • fderiv ℝ φ x (EuclideanSpace.single j 1))
          (DeGiorgi.weakGradientColumn hu x j + t • fderiv ℝ φ x (EuclideanSpace.single j 1))) := by
    funext t
    unfold metricDirichletEnergy
    simp only [DeGiorgi.weakGradientColumn_componentAffineVariationWitness]
  rw [hfunc]
  exact hderiv.congr_deriv (integral_congr_ae heq)

theorem integral_metric_energy_variation_eq_zero_of_isLocalMin
    (hΩ : IsOpen Ω) (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω)
    {A : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ} {V K : Set (EuclideanSpace ℝ (Fin n))}
    (hV : IsOpen V) (hA : ContDiffOn ℝ 1 A V) (hK : IsCompact K) (hKV : K ⊆ V)
    (huK : ∀ᵐ x ∂volume.restrict Ω, u x ∈ K)
    (hsym : ∀ y ∈ K, ∀ v w : (EuclideanSpace ℝ (Fin n)), A y v w = A y w v)
    {φ : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin n))}
    (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (hmin : IsLocalMin (fun t : ℝ => metricDirichletEnergy A
      (DeGiorgi.componentAffineVariationWitness hΩ hu hφ hφs t)) 0) :
    (∫ x in Ω, (∑ j : Fin d,
      ((fderiv ℝ A (u x) (φ x)) (DeGiorgi.weakGradientColumn hu x j)
          (DeGiorgi.weakGradientColumn hu x j) +
        2 * A (u x) (DeGiorgi.weakGradientColumn hu x j)
          (fderiv ℝ φ x (EuclideanSpace.single j 1))))) = 0 :=
  hmin.hasDerivAt_eq_zero
    (hasDerivAt_metricDirichletEnergy_affine_variation hΩ hu hV hA hK hKV huK hsym hφ hφs).2

theorem integral_metric_energy_variation_eq_zero_of_eventually_energy_le
    (hΩ : IsOpen Ω) (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω)
    {A : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ} {V K : Set (EuclideanSpace ℝ (Fin n))}
    (hV : IsOpen V) (hA : ContDiffOn ℝ 1 A V) (hK : IsCompact K) (hKV : K ⊆ V)
    (huK : ∀ᵐ x ∂volume.restrict Ω, u x ∈ K)
    (hsym : ∀ y ∈ K, ∀ v w : (EuclideanSpace ℝ (Fin n)), A y v w = A y w v)
    {φ : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin n))}
    (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (hmin : ∀ᶠ t in 𝓝 (0 : ℝ), metricDirichletEnergy A hu ≤ metricDirichletEnergy A
      (DeGiorgi.componentAffineVariationWitness hΩ hu hφ hφs t)) :
    (∫ x in Ω, (∑ j : Fin d,
      ((fderiv ℝ A (u x) (φ x)) (DeGiorgi.weakGradientColumn hu x j)
          (DeGiorgi.weakGradientColumn hu x j) +
        2 * A (u x) (DeGiorgi.weakGradientColumn hu x j)
          (fderiv ℝ φ x (EuclideanSpace.single j 1))))) = 0 := by
  apply integral_metric_energy_variation_eq_zero_of_isLocalMin hΩ hu hV hA hK hKV huK hsym hφ hφs
  change ∀ᶠ t in 𝓝 (0 : ℝ),
    metricDirichletEnergy A (DeGiorgi.componentAffineVariationWitness hΩ hu hφ hφs 0) ≤
      metricDirichletEnergy A (DeGiorgi.componentAffineVariationWitness hΩ hu hφ hφs t)
  rwa [metricDirichletEnergy_affine_variation_zero hΩ hu A hφ hφs]


end SobolevCoordinates

end DifferentialGeometry.Analysis.Sobolev

end

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

variable {d n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin n)

theorem integrable_quadratic_weakGradientColumn
    {Ω : Set V} {f : V → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (A : V → F →L[ℝ] F →L[ℝ] ℝ)
    (hA : AEStronglyMeasurable A (volume.restrict Ω))
    {C : ℝ} (hC : ∀ᵐ x ∂volume.restrict Ω, ‖A x‖ ≤ C) (j : Fin d) :
    IntegrableOn (fun x => A x (DeGiorgi.weakGradientColumn hf x j)
      (DeGiorgi.weakGradientColumn hf x j)) Ω := by
  have hG : MemLp (fun x => DeGiorgi.weakGradientColumn hf x j) 2 (volume.restrict Ω) :=
    MemLp.of_eval_piLp fun i => (hf i).weakGrad_component_memLp j
  exact integrable_bilinear_of_apply_aestronglyMeasurable A
    (fun v w => (hA.apply_continuousLinearMap v).apply_continuousLinearMap w) hC hG hG

theorem integrable_metric_weakGradientColumn_of_compact_range
    {Ω : Set V} {f : V → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    {K : Set F} (hK : IsCompact K) (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K) (j : Fin d) :
    IntegrableOn (fun x => A (f x) (DeGiorgi.weakGradientColumn hf x j)
      (DeGiorgi.weakGradientColumn hf x j)) Ω := by
  classical
  have hfm : MemLp f 2 (volume.restrict Ω) := MemLp.of_eval_piLp fun i => (hf i).memLp
  have hAm : Measurable (K.piecewise A 0) :=
    hA.measurable_piecewise continuous_zero.continuousOn hK.measurableSet
  have hB : ∀ v w, AEStronglyMeasurable (fun x => A (f x) v w)
      (volume.restrict Ω) := by
    intro v w
    have hAmf : AEMeasurable (fun x => A (f x)) (volume.restrict Ω) := by
      refine hAm.comp_aemeasurable hfm.aemeasurable |>.congr ?_
      filter_upwards [hfK] with x hx
      exact Set.piecewise_eq_of_mem K A 0 hx
    have hAv : AEMeasurable (fun x => A (f x) v) (volume.restrict Ω) :=
      (ContinuousLinearMap.apply ℝ (F →L[ℝ] ℝ) v).continuous.measurable.comp_aemeasurable hAmf
    exact ((ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp_aemeasurable hAv).aestronglyMeasurable
  have hn : ContinuousOn (fun y => ‖A y‖) K :=
    (@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA
  obtain ⟨C, hC⟩ := hK.bddAbove_image hn
  exact integrable_bilinear_of_apply_aestronglyMeasurable (fun x => A (f x)) hB
    (hfK.mono fun x hx => hC (mem_image_of_mem _ hx))
    (MemLp.of_eval_piLp fun i => (hf i).weakGrad_component_memLp j)
    (MemLp.of_eval_piLp fun i => (hf i).weakGrad_component_memLp j)

end DifferentialGeometry.Analysis.Sobolev

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {d m : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin m)

theorem integral_metric_energy_variation_eq_zero_of_ball_minimality
    {z : E → F} {R a : ℝ}
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball (0 : E) R))
    (hzc : ContinuousOn z (ball (0 : E) R)) (hzrange : MapsTo z (ball (0 : E) R) (ball 0 a))
    {U : Set F} (hU : IsOpen U) (hKU : closedBall (0 : F) a ⊆ U)
    (B : F → F →L[ℝ] F →L[ℝ] ℝ) (hB : ContDiffOn ℝ 1 B U)
    (hsym : ∀ y ∈ closedBall (0 : F) a, ∀ v w, B y v w = B y w v)
    (hmin : ∀ s : ℝ, 0 < s → s < R → ∀ q : E → F,
      ∀ hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (ball (0 : E) s),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - z x i) (ball (0 : E) s)) →
      (∀ᵐ x ∂volume.restrict (ball (0 : E) s), q x ∈ closedBall (0 : F) a) →
      (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in ball (0 : E) s,
        B (z x) (DeGiorgi.weakGradientColumn hz x j) (DeGiorgi.weakGradientColumn hz x j)) ≤
        (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in ball (0 : E) s,
          B (q x) (DeGiorgi.weakGradientColumn hq x j) (DeGiorgi.weakGradientColumn hq x j)))
    {s : ℝ} (hs : 0 < s) (hsR : s < R) {φ : E → F}
    (hφ : ContDiff ℝ ∞ φ) (hφsupp : tsupport φ ⊆ ball (0 : E) s) :
    (∫ x in ball (0 : E) s, ∑ j : Fin d,
      ((fderiv ℝ B (z x) (φ x))
          (DeGiorgi.weakGradientColumn hz x j) (DeGiorgi.weakGradientColumn hz x j) +
        2 * B (z x) (DeGiorgi.weakGradientColumn hz x j)
          (fderiv ℝ φ x (EuclideanSpace.single j 1)))) = 0 := by
  classical
  have hsub : ball (0 : E) s ⊆ ball (0 : E) R := ball_subset_ball hsR.le
  have hclosed : closedBall (0 : E) s ⊆ ball (0 : E) R := closedBall_subset_ball hsR
  let hzs (i : Fin m) := (hz i).restrict isOpen_ball hsub
  have hφcompact : HasCompactSupport φ :=
    (isCompact_closedBall (0 : E) s).of_isClosed_subset (isClosed_tsupport φ)
      (hφsupp.trans ball_subset_closedBall)
  let Kz := z '' closedBall (0 : E) s
  have hKz : IsCompact Kz := (isCompact_closedBall (0 : E) s).image_of_continuousOn
    (hzc.mono hclosed)
  have hKzball : Kz ⊆ ball (0 : F) a := by
    rintro y ⟨x, hx, rfl⟩
    exact hzrange (hclosed hx)
  obtain ⟨δ, hδ, hδK⟩ := hKz.exists_thickening_subset_open isOpen_ball hKzball
  obtain ⟨C₀, hC₀⟩ := hφ.continuous.bounded_above_of_compact_support hφcompact
  let C : ℝ := max C₀ 0 + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hφbound (x : E) : ‖φ x‖ ≤ C := (hC₀ x).trans (by dsimp only [C]; linarith [le_max_left C₀ 0])
  have hqrange : ∀ᶠ t in 𝓝 (0 : ℝ),
      MapsTo (fun x => z x + t • φ x) (ball (0 : E) s) (closedBall (0 : F) a) := by
    filter_upwards [ball_mem_nhds (0 : ℝ) (div_pos hδ hC)] with t ht x hx
    apply ball_subset_closedBall
    apply hδK
    apply mem_thickening_iff.mpr
    refine ⟨z x, mem_image_of_mem z (ball_subset_closedBall hx), ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have ht' : |t| < δ / C := by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
    exact (mul_le_mul_of_nonneg_left (hφbound x) (abs_nonneg t)).trans_lt
      ((lt_div_iff₀ hC).mp ht')
  have hzK : ∀ᵐ x ∂volume.restrict (ball (0 : E) s), z x ∈ closedBall (0 : F) a := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact ball_subset_closedBall (hzrange (hsub hx))
  have hbaseInt (j : Fin d) : IntegrableOn (fun x => B (z x)
      (DeGiorgi.weakGradientColumn hzs x j) (DeGiorgi.weakGradientColumn hzs x j))
        (ball (0 : E) s) :=
    Euclidean.integrable_quadratic_weakGrad_column_of_compact_range hzs
      (isCompact_closedBall (0 : F) a) hzK B (hB.continuousOn.mono hKU) j
  have hminvar : ∀ᶠ t in 𝓝 (0 : ℝ), metricDirichletEnergy B hzs ≤
      metricDirichletEnergy B (DeGiorgi.componentAffineVariationWitness
        isOpen_ball hzs hφ hφcompact t) := by
    filter_upwards [hqrange] with t htrange
    let ht := DeGiorgi.componentAffineVariationWitness isOpen_ball hzs hφ hφcompact t
    have htrace (i : Fin m) : DeGiorgi.MemW01p 2
        (fun x => (z x + t • φ x) i - z x i) (ball (0 : E) s) := by
      have hh := (DeGiorgi.memW01p_of_contDiffComponentHasCompactSupport_subset
        (p := 2) isOpen_ball hφ hφcompact hφsupp i).smul t
      convert hh using 1
      funext x
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_sub_cancel_left]
    have hqK : ∀ᵐ x ∂volume.restrict (ball (0 : E) s), z x + t • φ x ∈ closedBall (0 : F) a := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact htrange hx
    have hvarInt (j : Fin d) : IntegrableOn (fun x => B (z x + t • φ x)
        (DeGiorgi.weakGradientColumn ht x j) (DeGiorgi.weakGradientColumn ht x j))
          (ball (0 : E) s) :=
      Euclidean.integrable_quadratic_weakGrad_column_of_compact_range ht
        (isCompact_closedBall (0 : F) a) hqK B (hB.continuousOn.mono hKU) j
    have hle := hmin s hs hsR (fun x => z x + t • φ x) ht htrace hqK
    unfold metricDirichletEnergy
    rw [integral_finsetSum _ (fun j _ => hbaseInt j),
      integral_finsetSum _ (fun j _ => hvarInt j)]
    have hgrad : DeGiorgi.weakGradientColumn hzs = DeGiorgi.weakGradientColumn hz := rfl
    rw [hgrad]
    linarith [hle]
  exact integral_metric_energy_variation_eq_zero_of_eventually_energy_le isOpen_ball hzs
    hU hB (isCompact_closedBall (0 : F) a) hKU hzK hsym hφ hφcompact hminvar

end DifferentialGeometry.Analysis.Sobolev

end

end

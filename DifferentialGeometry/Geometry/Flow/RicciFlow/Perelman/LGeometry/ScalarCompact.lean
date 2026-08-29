import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RegAction
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [UniformSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [CompactSpace M] in
theorem lScalar_cont
    (S : SolutionOn (I := I) (M := M) D)
    (hS : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (alpha : Real → M)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.carrier)
    (halpha : ContinuousOn alpha (Set.uIcc a b)) :
    ContinuousOn
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
      (Set.uIcc a b) := by
  have hpair : ContinuousOn (fun s : Real ↦ (T - s ^ 2, alpha s))
      (Set.uIcc a b) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn.prodMk halpha
  have hmaps : Set.MapsTo (fun s : Real ↦ (T - s ^ 2, alpha s))
      (Set.uIcc a b) (D.carrier ×ˢ (Set.univ : Set M)) := by
    intro s hs
    exact ⟨ht s hs, Set.mem_univ _⟩
  have hscalar : ContinuousOn
      (fun s : Real ↦ S.scalar (T - s ^ 2) (alpha s))
      (Set.uIcc a b) := by
    simpa only [Function.comp_def] using
      hS.scalar_continuousOn.comp hpair hmaps
  exact ((continuous_const.mul (continuous_id.pow 2)).continuousOn.mul hscalar)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [CompactSpace M] in
theorem lScalar_int
    (S : SolutionOn (I := I) (M := M) D)
    (hS : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (alpha : Real → M)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.carrier)
    (halpha : ContinuousOn alpha (Set.uIcc a b)) :
    IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
      volume a b :=
  (lScalar_cont (I := I) S hS T a b alpha ht halpha).intervalIntegrable

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [CompactSpace M] in
theorem lScalar_lower_cpt
    (S : SolutionOn (I := I) (M := M) D)
    (hS : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.carrier)
    (K : Set M) (hK : IsCompact K) :
    ∃ C : Real, ∀ s ∈ Set.uIcc a b, ∀ x ∈ K,
      C ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) x := by
  let Q : Set (Real × M) := Set.uIcc a b ×ˢ K
  let f : Real × M → Real := fun q =>
    2 * q.1 ^ 2 * S.scalar (T - q.1 ^ 2) q.2
  let phi : Real × M → Real × M := fun q => (T - q.1 ^ 2, q.2)
  have hphi : Continuous phi :=
    (continuous_const.sub (continuous_fst.pow 2)).prodMk continuous_snd
  have hmaps : Set.MapsTo phi Q
      (D.carrier ×ˢ (Set.univ : Set M)) := by
    intro q hq
    exact ⟨ht q.1 hq.1, Set.mem_univ q.2⟩
  have hscalar : ContinuousOn
      (fun q : Real × M => S.scalar (T - q.1 ^ 2) q.2) Q := by
    simpa only [phi, Function.comp_def] using
      hS.scalar_continuousOn.comp hphi.continuousOn hmaps
  have hf : ContinuousOn f Q := by
    exact ((continuous_const.mul (continuous_fst.pow 2)).continuousOn.mul hscalar)
  have hQ : IsCompact Q := by
    simpa only [Q] using isCompact_uIcc.prod hK
  obtain ⟨C, hC⟩ := bddBelow_def.mp (hQ.bddBelow_image hf)
  refine ⟨C, ?_⟩
  intro s hs x hx
  exact hC (f (s, x)) ⟨(s, x), ⟨hs, hx⟩, rfl⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [CompactSpace M] in
theorem lScalar_tendsto_cpt
    (S : SolutionOn (I := I) (M := M) D)
    (hS : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (hab : a ≤ b)
    (ht : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ D.carrier)
    (K : Set M) (hK : IsCompact K)
    (alpha : Nat → Real → M) (alphaLim : Real → M)
    (halpha : ∀ n, ContinuousOn (alpha n) (Set.Icc a b))
    (hval : ∀ n s, s ∈ Set.Icc a b → alpha n s ∈ K)
    (hconv : TendstoUniformly
      (fun n (s : Set.Icc a b) ↦ alpha n s.1)
      (fun s : Set.Icc a b ↦ alphaLim s.1) atTop) :
    Tendsto
      (fun n ↦ ∫ s in a..b,
        2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s))
      atTop
      (𝓝 (∫ s in a..b,
        2 * s ^ 2 * S.scalar (T - s ^ 2) (alphaLim s))) := by
  let P : Real → M → Real := fun s x ↦
    2 * s ^ 2 * S.scalar (T - s ^ 2) x
  have hpair : ContinuousOn
      (fun q : Real × M ↦ (T - q.1 ^ 2, q.2))
      (Set.Icc a b ×ˢ K) :=
    (continuous_const.sub (continuous_fst.pow 2)).continuousOn.prodMk
      continuous_snd.continuousOn
  have hmaps : Set.MapsTo
      (fun q : Real × M ↦ (T - q.1 ^ 2, q.2))
      (Set.Icc a b ×ˢ K)
      (D.carrier ×ˢ (Set.univ : Set M)) := by
    intro q hq
    exact ⟨ht q.1 hq.1, Set.mem_univ _⟩
  have hscalar : ContinuousOn
      (fun q : Real × M ↦ S.scalar (T - q.1 ^ 2) q.2)
      (Set.Icc a b ×ˢ K) := by
    simpa only [Function.comp_def] using
      hS.scalar_continuousOn.comp hpair hmaps
  have hP : ContinuousOn (fun q : Real × M ↦ P q.1 q.2)
      (Set.Icc a b ×ˢ K) := by
    exact ((continuous_const.mul (continuous_fst.pow 2)).continuousOn.mul hscalar)
  have hQ : IsCompact (Set.Icc a b ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hP
  let C₀ : Real := max C 0
  have htimeU : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.carrier := by
    simpa only [Set.uIcc_of_le hab] using ht
  have halphaU : ∀ n, ContinuousOn (alpha n) (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using halpha
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (fun _ : Real ↦ C₀) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards with n
    exact ((lScalar_cont (I := I) S hS T a b (alpha n) htimeU
      (halphaU n)).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc
  · filter_upwards with n
    exact ae_of_all _ fun s hs ↦ by
      have hsIcc : s ∈ Set.Icc a b := by
        simpa only [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hs
      exact (hC (s, alpha n s) ⟨hsIcc, hval n s hsIcc⟩).trans
        (le_max_left C 0)
  · exact ae_of_all _ fun s hs ↦ by
      have hsIcc : s ∈ Set.Icc a b := by
        simpa only [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hs
      have halphaAt : Tendsto (fun n ↦ alpha n s) atTop
          (𝓝 (alphaLim s)) := by
        simpa only using hconv.tendsto_at ⟨s, hsIcc⟩
      let tD : {t : Real // t ∈ D.carrier} := ⟨T - s ^ 2, ht s hsIcc⟩
      have hpairAt : Tendsto (fun n ↦ (tD, alpha n s)) atTop
          (𝓝 (tD, alphaLim s)) :=
        tendsto_const_nhds.prodMk_nhds halphaAt
      have hscalarAt : Tendsto
          (fun n ↦ S.scalar (T - s ^ 2) (alpha n s)) atTop
          (𝓝 (S.scalar (T - s ^ 2) (alphaLim s))) := by
        have h := hS.continuous_subtype.continuousAt.tendsto.comp hpairAt
        change Tendsto (fun n ↦ S.scalar (T - s ^ 2) (alpha n s)) atTop
          (𝓝 (S.scalar (T - s ^ 2) (alphaLim s))) at h
        exact h
      simpa only [P] using tendsto_const_nhds.mul hscalarAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
theorem lScalar_tendsto
    (S : SolutionOn (I := I) (M := M) D)
    (hS : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (hab : a ≤ b)
    (ht : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ D.carrier)
    (alpha : Nat → Real → M) (alphaLim : Real → M)
    (halpha : ∀ n, ContinuousOn (alpha n) (Set.Icc a b))
    (hconv : TendstoUniformly
      (fun n (s : Set.Icc a b) ↦ alpha n s.1)
      (fun s : Set.Icc a b ↦ alphaLim s.1) atTop) :
    Tendsto
      (fun n ↦ ∫ s in a..b,
        2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s))
      atTop
      (𝓝 (∫ s in a..b,
        2 * s ^ 2 * S.scalar (T - s ^ 2) (alphaLim s))) := by
  let P : Real → M → Real := fun s x ↦
    2 * s ^ 2 * S.scalar (T - s ^ 2) x
  have hpair : ContinuousOn
      (fun q : Real × M ↦ (T - q.1 ^ 2, q.2))
      (Set.Icc a b ×ˢ (Set.univ : Set M)) :=
    (continuous_const.sub (continuous_fst.pow 2)).continuousOn.prodMk
      continuous_snd.continuousOn
  have hmaps : Set.MapsTo
      (fun q : Real × M ↦ (T - q.1 ^ 2, q.2))
      (Set.Icc a b ×ˢ (Set.univ : Set M))
      (D.carrier ×ˢ (Set.univ : Set M)) := by
    intro q hq
    exact ⟨ht q.1 hq.1, Set.mem_univ _⟩
  have hscalar : ContinuousOn
      (fun q : Real × M ↦ S.scalar (T - q.1 ^ 2) q.2)
      (Set.Icc a b ×ˢ (Set.univ : Set M)) := by
    simpa only [Function.comp_def] using
      hS.scalar_continuousOn.comp hpair hmaps
  have hP : ContinuousOn (fun q : Real × M ↦ P q.1 q.2)
      (Set.Icc a b ×ˢ (Set.univ : Set M)) := by
    exact ((continuous_const.mul (continuous_fst.pow 2)).continuousOn.mul hscalar)
  have hK : IsCompact (Set.Icc a b ×ˢ (Set.univ : Set M)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hP
  let C₀ : Real := max C 0
  have htimeU : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.carrier := by
    simpa only [Set.uIcc_of_le hab] using ht
  have halphaU : ∀ n, ContinuousOn (alpha n) (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using halpha
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (fun _ : Real ↦ C₀) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards with n
    exact ((lScalar_cont (I := I) S hS T a b (alpha n) htimeU
      (halphaU n)).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc
  · filter_upwards with n
    exact ae_of_all _ fun s hs ↦ by
      have hsIcc : s ∈ Set.Icc a b := by
        simpa only [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hs
      exact (hC (s, alpha n s) ⟨hsIcc, Set.mem_univ _⟩).trans
        (le_max_left C 0)
  · exact ae_of_all _ fun s hs ↦ by
      have hsIcc : s ∈ Set.Icc a b := by
        simpa only [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hs
      have halphaAt : Tendsto (fun n ↦ alpha n s) atTop
          (𝓝 (alphaLim s)) := by
        simpa only using hconv.tendsto_at ⟨s, hsIcc⟩
      let tD : {t : Real // t ∈ D.carrier} := ⟨T - s ^ 2, ht s hsIcc⟩
      have hpairAt : Tendsto (fun n ↦ (tD, alpha n s)) atTop
          (𝓝 (tD, alphaLim s)) :=
        tendsto_const_nhds.prodMk_nhds halphaAt
      have hscalarAt : Tendsto
          (fun n ↦ S.scalar (T - s ^ 2) (alpha n s)) atTop
          (𝓝 (S.scalar (T - s ^ 2) (alphaLim s))) := by
        have h := hS.continuous_subtype.continuousAt.tendsto.comp hpairAt
        change Tendsto (fun n ↦ S.scalar (T - s ^ 2) (alpha n s)) atTop
          (𝓝 (S.scalar (T - s ^ 2) (alphaLim s))) at h
        exact h
      simpa only [P] using tendsto_const_nhds.mul hscalarAt

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

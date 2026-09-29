import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientConnectionContinuity
import Mathlib.Topology.UniformSpace.UniformApproximation


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood.FiniteHorn
open Bundle Filter Set
open DifferentialGeometry.Analysis DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

private theorem continuousOn_of_uniform_time_sequences
    {E F : Type*} [NormedAddCommGroup E] [LocallyCompactSpace E]
    [NormedAddCommGroup F] {U : Set E} (hU : IsOpen U) {J : Set ℝ}
    {f : ℝ → E → F}
    (hspace : ∀ t ∈ J, ContinuousOn (f t) U)
    (htime : ∀ t ∈ J, ∀ τ : ℕ → ℝ, (∀ n, τ n ∈ J) → Tendsto τ atTop (𝓝 t) →
      ∀ K : Set E, IsCompact K → K ⊆ U →
        TendstoUniformlyOn (fun n => f (τ n)) (f t) atTop K) :
    ContinuousOn (fun q : ℝ × E => f q.1 q.2) (J ×ˢ U) := by
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ (s := J ×ˢ U)
    (x := (t, y)) ⟨ht, hy⟩]
  apply tendsto_iff_seq_tendsto.mpr
  intro q hq
  have hval := continuous_subtype_val.continuousAt.tendsto.comp hq
  have hτ : Tendsto (fun n => (q n).val.1) atTop (𝓝 t) :=
    continuous_fst.continuousAt.tendsto.comp hval
  have hyseq : Tendsto (fun n => (q n).val.2) atTop (𝓝 y) :=
    continuous_snd.continuousAt.tendsto.comp hval
  obtain ⟨K, hK, hyK, hKU⟩ := exists_compact_between isCompact_singleton hU
    (singleton_subset_iff.mpr hy)
  have hKnhds : K ∈ 𝓝 y := mem_of_superset
    (isOpen_interior.mem_nhds (hyK (mem_singleton y))) interior_subset
  have hunif := htime t ht (fun n => (q n).val.1)
    (fun n => (q n).property.1) hτ K hK hKU
  exact hunif.tendsto_comp ((hspace t ht y hy).mono hKU)
    (tendsto_nhdsWithin_iff.mpr ⟨hyseq, hyseq.eventually hKnhds⟩)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]


theorem solution_chartChristoffel_jets_continuousOn_carrier
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (p : M) (i j k : Fin (Module.finrank ℝ E)) (r : ℕ) :
    ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ r
      (chartChristoffel (I := I) (S.base.metric q.1) p i j k) q.2)
      (Iic b ×ˢ (extChartAt I p).target) := by
  have hW := isOpen_extChartAt_target (I := I) p
  have hs (t : ℝ) : ContDiffOn ℝ ∞
      (chartChristoffel (I := I) (S.base.metric t) p i j k) (extChartAt I p).target := by
    simpa only [hW.interior_eq] using
      chartChristoffel_contDiffOn_interior (I := I) (S.base.metric t) p i j k
  apply continuousOn_of_uniform_time_sequences hW (J := Iic b)
    (f := fun t y => iteratedFDeriv ℝ r
      (chartChristoffel (I := I) (S.base.metric t) p i j k) y)
  · intro t _ y hy
    exact ((hs t).contDiffAt (hW.mem_nhds hy)).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top) |>.continuousWithinAt
  · intro t ht τ hτ hτt K hK hKW
    have hgram := solution_chartGram_mapCInf_of_carrier_time_sequence S hS
      hcarrier hregular ht p τ hτ hτt
    have hchr := mapCInfConvergence_chartChristoffel_of_gram
      (fun n => S.base.metric (τ n)) (S.base.metric t) p hW (fun _ hx => hx) hgram i j k
    exact MapCInfConvergenceOnCompacts.tendstoUniformlyOn_iteratedFDeriv hW hK hKW hchr
      (fun n => hs (τ n)) (hs t) r


theorem exists_uniform_chartChristoffel_jet_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (p : M) (K : Set E) (hK : IsCompact K) (hKW : K ⊆ (extChartAt I p).target)
    (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ y ∈ K,
      ∀ i j k : Fin (Module.finrank ℝ E),
        ‖iteratedFDeriv ℝ r (chartChristoffel (I := I) (S.base.metric t) p i j k) y‖ ≤ C := by
  let F := fun q : ℝ × E => fun i j k : Fin (Module.finrank ℝ E) =>
    iteratedFDeriv ℝ r (chartChristoffel (I := I) (S.base.metric q.1) p i j k) q.2
  have hF : ContinuousOn F (Icc a b ×ˢ K) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro k
    exact (solution_chartChristoffel_jets_continuousOn_carrier S hS hcarrier hregular
      p i j k r).mono (fun _ hq => ⟨hq.1.2, hKW hq.2⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).bddAbove_image hF.norm
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht y hy i j k
  calc
    _ ≤ ‖F (t, y) i j‖ := norm_le_pi_norm (F (t, y) i j) k
    _ ≤ ‖F (t, y) i‖ := norm_le_pi_norm (F (t, y) i) j
    _ ≤ ‖F (t, y)‖ := norm_le_pi_norm (F (t, y)) i
    _ ≤ C := hC ⟨(t, y), ⟨ht, hy⟩, rfl⟩
    _ ≤ max C 0 := le_max_left _ _


theorem solution_chartInvGram_jets_continuousOn_carrier
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (p : M) (i j : Fin (Module.finrank ℝ E)) (r : ℕ) :
    ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ r
      (chartInvGramOnE (I := I) (S.base.metric q.1) p i j) q.2)
      (Iic b ×ˢ (extChartAt I p).target) := by
  have hW := isOpen_extChartAt_target (I := I) p
  have hs (t : ℝ) : ContDiffOn ℝ ∞
      (chartInvGramOnE (I := I) (S.base.metric t) p i j) (extChartAt I p).target :=
    DifferentialGeometry.Geometry.Operator.chartInvGramOnE_contDiffOn
      (I := I) (S.base.metric t) p i j
  apply continuousOn_of_uniform_time_sequences hW (J := Iic b)
    (f := fun t y => iteratedFDeriv ℝ r
      (chartInvGramOnE (I := I) (S.base.metric t) p i j) y)
  · intro t _ y hy
    exact ((hs t).contDiffAt (hW.mem_nhds hy)).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top) |>.continuousWithinAt
  · intro t ht τ hτ hτt K hK hKW
    have hgram := solution_chartGram_mapCInf_of_carrier_time_sequence S hS
      hcarrier hregular ht p τ hτ hτt
    have hop := mapCInfConvergence_chartJetOperator
      (fun n => S.base.metric (τ n)) (S.base.metric t) p hW (fun _ hx => hx) hgram
      (fun J => (Matrix.of J.1)⁻¹ i j) (fun _ hJ => contDiffAt_jetInvGram hJ i j)
    have hconv : MapCInfConvergenceOnCompacts (extChartAt I p).target
        (fun n => chartInvGramOnE (I := I) (S.base.metric (τ n)) p i j)
        (chartInvGramOnE (I := I) (S.base.metric t) p i j) := by
      exact hop.congr hW
        (fun n y _ => (jet2_chartGram_invGram (S.base.metric (τ n)) p y i j).symm)
        (fun y _ => (jet2_chartGram_invGram (S.base.metric t) p y i j).symm)
    exact MapCInfConvergenceOnCompacts.tendstoUniformlyOn_iteratedFDeriv hW hK hKW hconv
      (fun n => hs (τ n)) (hs t) r


theorem exists_uniform_chartInvGram_jet_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (p : M) (K : Set E) (hK : IsCompact K) (hKW : K ⊆ (extChartAt I p).target)
    (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ y ∈ K,
      ∀ i j : Fin (Module.finrank ℝ E),
        ‖iteratedFDeriv ℝ r (chartInvGramOnE (I := I) (S.base.metric t) p i j) y‖ ≤ C := by
  let F := fun q : ℝ × E => fun i j : Fin (Module.finrank ℝ E) =>
    iteratedFDeriv ℝ r (chartInvGramOnE (I := I) (S.base.metric q.1) p i j) q.2
  have hF : ContinuousOn F (Icc a b ×ˢ K) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (solution_chartInvGram_jets_continuousOn_carrier S hS hcarrier hregular
      p i j r).mono (fun _ hq => ⟨hq.1.2, hKW hq.2⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).bddAbove_image hF.norm
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht y hy i j
  calc
    _ ≤ ‖F (t, y) i‖ := norm_le_pi_norm (F (t, y) i) j
    _ ≤ ‖F (t, y)‖ := norm_le_pi_norm (F (t, y)) i
    _ ≤ C := hC ⟨(t, y), ⟨ht, hy⟩, rfl⟩
    _ ≤ max C 0 := le_max_left _ _

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

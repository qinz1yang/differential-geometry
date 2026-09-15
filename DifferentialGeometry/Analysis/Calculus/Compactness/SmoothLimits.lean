import DifferentialGeometry.Analysis.Calculus.Compactness.SmoothMap
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import Mathlib.Topology.Sequences

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set Topology
open scoped ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem mapCInfConvergenceOnCompacts_of_pointwise_of_local_jet_bounds
    {U : Set E} (hU : IsOpen U) (f : ℕ → E → F) (f₀ : E → F)
    (hf : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (f k) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (f k) x‖ ≤ C)
    (hpoint : ∀ x ∈ U, Tendsto (fun k => f k x) atTop (𝓝 (f₀ x))) :
    MapCInfConvergenceOnCompacts U f f₀ := by
  classical
  intro K hK hKU p ε hε
  by_contra hbad
  push Not at hbad
  choose k hk hbad using hbad
  choose r hr hbad using hbad
  choose x hx hbad using hbad
  have hkTop : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  obtain ⟨σ, fLimit, hσ, _, hconv⟩ := exists_cInf_subseq_on hU
    (fun n => f (k n)) (fun n => hf (k n)) (by
      intro j C hC hCU
      obtain ⟨B, hB⟩ := hbdd j C hC hCU
      exact ⟨B, fun n y hy => hB (k n) y hy⟩)
  have heq : Set.EqOn f₀ fLimit U := by
    intro y hy
    have hto₀ := (hpoint y hy).comp (hkTop.comp hσ.tendsto_atTop)
    have htoLimit := (tendstoUniformlyOn_of_cPConvergence
      (hconv {y} isCompact_singleton (Set.singleton_subset_iff.mpr hy) 0)).tendsto_at
        (Set.mem_singleton y)
    exact tendsto_nhds_unique hto₀ htoLimit
  have hconv₀ : MapCInfConvergenceOnCompacts U (fun n => f (k (σ n))) f₀ :=
    hconv.congr hU (fun _ _ _ => rfl) heq
  obtain ⟨N, hN⟩ := hconv₀ K hK hKU p ε hε
  exact not_lt_of_ge
    (hN N le_rfl (r (σ N)) (hr (σ N)) (x (σ N)) (hx (σ N))) (hbad (σ N))

theorem iteratedFDeriv_norm_le_of_pointwise_of_local_jet_bounds
    {U : Set E} (hU : IsOpen U) (f : ℕ → E → F) (f₀ : E → F)
    (hf : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (f k) U)
    (hf₀ : ContDiffOn ℝ (∞ : WithTop ℕ∞) f₀ U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (f k) x‖ ≤ C)
    (hpoint : ∀ x ∈ U, Tendsto (fun k => f k x) atTop (𝓝 (f₀ x)))
    (r : ℕ) {x : E} (hx : x ∈ U) {C : ℝ}
    (hC : ∀ᶠ k in atTop, ‖iteratedFDeriv ℝ r (f k) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ r f₀ x‖ ≤ C := by
  have hconv := mapCInfConvergenceOnCompacts_of_pointwise_of_local_jet_bounds
    hU f f₀ hf hbdd hpoint
  have hjet := (hconv.tendstoUniformlyOn_iteratedFDeriv hU isCompact_singleton
    (Set.singleton_subset_iff.mpr hx) hf hf₀ r).tendsto_at (Set.mem_singleton x)
  exact le_of_tendsto hjet.norm hC


variable {A : Type*} [TopologicalSpace A] [FirstCountableTopology A]

theorem continuousOn_spatial_iteratedFDeriv_of_local_jet_bounds
    {S : Set A} {U : Set E} (hU : IsOpen U)
    (G : A → E → F) (hG : ∀ x ∈ U, ContinuousOn (fun t => G t x) S)
    (hGs : ∀ t ∈ S, ContDiffOn ℝ (∞ : WithTop ℕ∞) (G t) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ t ∈ S, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ r (G t) x‖ ≤ C) (r : ℕ) :
    ContinuousOn (fun p : A × E => iteratedFDeriv ℝ r (G p.1) p.2) (S ×ˢ U) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_seqContinuous]
  intro z p hz
  have hzval := (continuous_subtype_val.tendsto p).comp hz
  have hzt : Tendsto (fun n => (z n).val.1) atTop (𝓝 p.val.1) :=
    (continuous_fst.tendsto p.val).comp hzval
  have hzx : Tendsto (fun n => (z n).val.2) atTop (𝓝 p.val.2) :=
    (continuous_snd.tendsto p.val).comp hzval
  let K : Set E := insert p.val.2 (Set.range (fun n => (z n).val.2))
  have hK : IsCompact K := hzx.isCompact_insert_range
  have hKU : K ⊆ U := by
    intro y hy
    rcases hy with rfl | ⟨n, rfl⟩
    · exact p.property.2
    · exact (z n).property.2
  have hconv : MapCInfConvergenceOnCompacts U
      (fun n => G (z n).val.1) (G p.val.1) := by
    apply mapCInfConvergenceOnCompacts_of_pointwise_of_local_jet_bounds hU
      (fun n => G (z n).val.1) (G p.val.1)
      (fun n => hGs _ (z n).property.1)
    · intro q L hL hLU
      obtain ⟨C, hC⟩ := hbdd q L hL hLU
      exact ⟨C, fun n y hy => hC _ (z n).property.1 y hy⟩
    · intro y hy
      exact (hG y hy p.val.1 p.property.1).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr
          ⟨hzt, Eventually.of_forall fun n => (z n).property.1⟩)
  have hjet := hconv.tendstoUniformlyOn_iteratedFDeriv hU hK hKU
    (fun n => hGs _ (z n).property.1) (hGs p.val.1 p.property.1) r
  exact hjet.tendsto_comp
    ((ContinuousOn.continuousOn_iteratedFDeriv (hGs p.val.1 p.property.1) hU
      (by exact_mod_cast le_top)).mono hKU p.val.2 (mem_insert _ _))
    (tendsto_nhdsWithin_iff.mpr
      ⟨hzx, Eventually.of_forall fun n => mem_insert_of_mem _ ⟨n, rfl⟩⟩)

theorem contDiffOn_and_continuousOn_spatial_iteratedFDeriv_closure
    {S : Set A} {U : Set E} (hU : IsOpen U)
    (G : A → E → F) (hG : ∀ x ∈ U, ContinuousOn (fun t => G t x) (closure S))
    (hGs : ∀ t ∈ S, ContDiffOn ℝ (∞ : WithTop ℕ∞) (G t) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ t ∈ S, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ r (G t) x‖ ≤ C) :
    (∀ t ∈ closure S, ContDiffOn ℝ (∞ : WithTop ℕ∞) (G t) U) ∧
      ∀ r : ℕ, ContinuousOn
        (fun p : A × E => iteratedFDeriv ℝ r (G p.1) p.2) (closure S ×ˢ U) := by
  have hpoint {t : A} (ht : t ∈ closure S)
      (u : ℕ → A) (hu : ∀ k, u k ∈ S) (hut : Tendsto u atTop (𝓝 t)) :
      ∀ x ∈ U, Tendsto (fun k => G (u k) x) atTop (𝓝 (G t x)) := by
    intro x hx
    exact (hG x hx t ht).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr
        ⟨hut, Eventually.of_forall fun k => subset_closure (hu k)⟩)
  have hseqbdd (u : ℕ → A) (hu : ∀ k, u k ∈ S) :
      ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
        ∃ C : ℝ, ∀ k : ℕ, ∀ x ∈ K,
          ‖iteratedFDeriv ℝ r (G (u k)) x‖ ≤ C := by
    intro r K hK hKU
    obtain ⟨C, hC⟩ := hbdd r K hK hKU
    exact ⟨C, fun k x hx => hC _ (hu k) x hx⟩
  have hsmooth : ∀ t ∈ closure S, ContDiffOn ℝ (∞ : WithTop ℕ∞) (G t) U := by
    intro t ht
    obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.mp ht
    obtain ⟨φ, flim, hφ, hflim, hconv⟩ := exists_cInf_subseq_on hU
      (fun k => G (u k)) (fun k => hGs _ (hu k)) (hseqbdd u hu)
    apply hflim.congr
    intro x hx
    exact tendsto_nhds_unique ((hpoint ht u hu hut x hx).comp hφ.tendsto_atTop)
      (tendsto_of_cInf hconv hx)
  refine ⟨hsmooth, fun r =>
    continuousOn_spatial_iteratedFDeriv_of_local_jet_bounds hU G hG hsmooth ?_ r⟩
  intro q K hK hKU
  obtain ⟨C, hC⟩ := hbdd q K hK hKU
  refine ⟨C, ?_⟩
  intro t ht x hx
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.mp ht
  exact iteratedFDeriv_norm_le_of_pointwise_of_local_jet_bounds hU
    (fun k => G (u k)) (G t) (fun k => hGs _ (hu k)) (hsmooth t ht)
    (hseqbdd u hu) (hpoint ht u hu hut) q (hKU hx)
    (Eventually.of_forall fun k => hC _ (hu k) x hx)

theorem contDiffOn_and_continuousOn_spatial_iteratedFDeriv_Icc
    {a b : ℝ} (hab : a < b) {U : Set E} (hU : IsOpen U)
    (G : ℝ → E → F) (hG : ∀ x ∈ U, ContinuousOn (fun t => G t x) (Ico a b))
    (hlimit : ∀ x ∈ U, Tendsto (fun t => G t x) (𝓝[Ico a b] b) (𝓝 (G b x)))
    (hGs : ∀ t ∈ Ico a b, ContDiffOn ℝ (∞ : WithTop ℕ∞) (G t) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ t ∈ Ico a b, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ r (G t) x‖ ≤ C) :
    (∀ t ∈ Icc a b, ContDiffOn ℝ (∞ : WithTop ℕ∞) (G t) U) ∧
      ∀ r : ℕ, ContinuousOn
        (fun p : ℝ × E => iteratedFDeriv ℝ r (G p.1) p.2) (Icc a b ×ˢ U) := by
  have hGc : ∀ x ∈ U, ContinuousOn (fun t => G t x) (closure (Ico a b)) := by
    rw [closure_Ico hab.ne]
    intro x hx t ht
    rcases lt_or_eq_of_le ht.2 with htb | rfl
    · apply (hG x hx t ⟨ht.1, htb⟩).mono_of_mem_nhdsWithin
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htb)]
        with z hz hzb
      exact ⟨hz.1, hzb⟩
    · have h := ContinuousWithinAt.insert (hlimit x hx)
      rwa [Ico_insert_right hab.le] at h
  simpa only [closure_Ico hab.ne] using
    contDiffOn_and_continuousOn_spatial_iteratedFDeriv_closure hU G hGc hGs hbdd

end DifferentialGeometry.CheegerGromovCompactness

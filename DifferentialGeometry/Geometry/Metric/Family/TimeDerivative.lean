import DifferentialGeometry.Bundle.PartialMfderiv.TimeDerivative
import DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair
import DifferentialGeometry.Geometry.Metric.Family.UniformEquivalence

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}

theorem contMDiffOn_inner_time_deriv
    (hg : MetricFamilySmoothOn (I := I) (M := M) D g) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, deriv (fun s => (g s).inner p.2) p.1⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (D.regular ×ˢ (univ : Set M)) := by
  let : ∀ x : M, NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    fun _ => inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
  let : ∀ x : M, NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    fun _ => inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
  intro p hp
  exact ((hg.metricCLMSmoothAt (D.regular_isOpen.mem_nhds hp.1)).fiberwise_time_deriv
    (by simp)).contMDiffWithinAt

theorem hasDerivAt_inner
    (hg : MetricFamilySmoothOn (I := I) (M := M) D g)
    {t : ℝ} (ht : t ∈ D.regular) (x : M) (v w : TangentSpace I x) :
    HasDerivAt (fun s => (g s).inner x v w)
      (deriv (fun s => (g s).inner x) t v w) t := by
  let : ∀ y : M, NormedAddCommGroup (TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) :=
    fun _ => inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
  let : ∀ y : M, NormedSpace ℝ (TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) :=
    fun _ => inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
  have hs := hg.metricCLMSmoothAt (t := t) (x := x) (D.regular_isOpen.mem_nhds ht)
  have hfixed : ContDiffAt ℝ ∞ (fun s => (g s).inner x) t := by
    rw [← contDiffWithinAt_univ]
    apply ContMDiffWithinAt.fiberwise_time_contDiffWithinAt (I := I)
      (F := E →L[ℝ] E →L[ℝ] ℝ)
      (V := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
      (u := univ) ?_ (mem_univ x)
    simpa only [univ_prod_univ] using hs.contMDiffWithinAt (s := univ)
  have hd := ((hfixed.differentiableAt (by simp)).hasDerivAt.clm_apply
    (hasDerivAt_const t v)).clm_apply (hasDerivAt_const t w)
  simpa only [map_zero, zero_apply, add_zero] using hd

theorem exists_inner_time_deriv_bound [CompactSpace M] [T2Space M]
    (hg : MetricFamilySmoothOn (I := I) (M := M) D g)
    {K : Set ℝ} (hK : IsCompact K) (hreg : K ⊆ D.regular) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K, ∀ x : M, ∀ v : TangentSpace I x,
      |deriv (fun s => (g s).inner x) t v v| ≤ C * (g t).inner x v v := by
  let q := g 0
  let P := K × MetricUnitTangent (I := I) (M := M) q
  let b : P → M := fun p => p.2.1.proj
  let v : (p : P) → TangentSpace I (b p) := fun p => p.2.1.2
  let F : P → ℝ × M := fun p => (p.1.1, b p)
  have hb : Continuous b :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp
      (continuous_subtype_val.comp continuous_snd)
  have hF : Continuous F :=
    (continuous_subtype_val.comp continuous_fst).prodMk hb
  have hv : Continuous (fun p : P =>
      (⟨b p, v p⟩ : TangentBundle I M)) :=
    continuous_subtype_val.comp continuous_snd
  have hmap : MapsTo F univ (D.regular ×ˢ (univ : Set M)) :=
    fun p _ => ⟨hreg p.1.2, mem_univ _⟩
  have hd := continuousOn_univ.mp
    (hg.contMDiffOn_inner_time_deriv.continuousOn.comp hF.continuousOn hmap)
  have hpair : Continuous (fun p : P =>
      (⟨b p, deriv (fun s => (g s).inner (b p)) p.1.1 (v p) (v p)⟩ :
        TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
    hd.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hv hv
  have hscalar : Continuous (fun p : P =>
      deriv (fun s => (g s).inner (b p)) p.1.1 (v p) (v p)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hp := hpair.continuousAt (x := p)
    rw [FiberBundle.continuousAt_totalSpace] at hp
    exact hp.2
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let _ : CompactSpace (MetricUnitTangent (I := I) (M := M) q) :=
    isCompact_univ_iff.mp (metricUnit_compact q)
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hscalar.continuousOn
  let A : (t : ℝ) → (x : M) → Tensor0SSpace 2 I x := fun t x =>
    (((continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap).comp
      (deriv (fun s => (g s).inner x) t)).uncurryLeft
  have hbound : ∀ t ∈ K, ∀ x : M, ∀ w : TangentSpace I x,
      |deriv (fun s => (g s).inner x) t w w| ≤ max R 0 * q.inner x w w := by
    intro t ht
    have hunit : ∀ p : MetricUnitTangent (I := I) (M := M) q,
        |quad02 (A t (MetricUnitTangent.base p)) (MetricUnitTangent.vec p)| ≤ max R 0 := by
      intro p
      have h := hR (⟨t, ht⟩, p) (mem_univ _)
      rw [Real.norm_eq_abs] at h
      exact h.trans (le_max_left _ _)
    exact unitAbsBound_to_all q (A t) hunit
  obtain ⟨Cg, hCg, hequiv⟩ :=
    exists_metric_equivalence_bound_on_compact_time_of_metricFamilySmoothOn
      g hg hK (hreg.trans D.regular_subset) q
  have hCgpos : 0 < Cg := zero_lt_one.trans_le hCg
  refine ⟨max R 0 * Cg, mul_nonneg (le_max_right _ _) hCgpos.le, fun t ht x w => ?_⟩
  have hlo := (hequiv t ht x w).1
  have hqle : q.inner x w w ≤ Cg * (g t).inner x w w := by
    have h := mul_le_mul_of_nonneg_left hlo hCgpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hCgpos.ne', one_mul] at h
  exact (hbound t ht x w).trans
    ((mul_le_mul_of_nonneg_left hqle (le_max_right R 0)).trans_eq (by ring))

end DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

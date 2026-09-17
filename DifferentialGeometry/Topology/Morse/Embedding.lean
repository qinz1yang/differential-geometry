import DifferentialGeometry.Topology.Embedding.Stability
import DifferentialGeometry.Topology.Morse.CriticalFinite
import DifferentialGeometry.Topology.Morse.ExcellentFamily
import DifferentialGeometry.Topology.Order.FiniteSeparation

open Set Filter
open scoped Topology Manifold ContDiff

namespace Manifold.IsSmoothEmbedding

open DifferentialGeometry.Morse DifferentialGeometry.Topology.Morse

variable {E H M V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
  [CompactSpace M] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] in
private theorem eventually_exists_ambient_isotopy_finitePerturbation
    {e : M → V} (he : IsSmoothEmbedding I 𝓘(ℝ, V) ∞ e)
    (ℓ : V →L[ℝ] ℝ) {v : V} (hv : ℓ v = 1)
    {n : ℕ} {φ : Fin n → M → ℝ}
    (hφ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i)) :
    ∀ᶠ p in 𝓝 (0 : Fin n → ℝ), ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (fun x => ℓ (Φ 1 (e x))) = finitePerturbation (ℓ ∘ e) φ p := by
  let f : M → ℝ := ℓ ∘ e
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ℓ.contDiff.contMDiff.comp he.contMDiff
  let F : (Fin n → ℝ) × M → V := fun q =>
    e q.2 + (finitePerturbation f φ q.1 q.2 - f q.2) • v
  have hF : ContMDiff (𝓘(ℝ, Fin n → ℝ).prod I) 𝓘(ℝ, V) ∞ F :=
    (he.contMDiff.comp contMDiff_snd).add
      (((contMDiff_joint_finitePerturbation hf hφ).sub
        (hf.comp contMDiff_snd)).smul contMDiff_const)
  have hFzero : (fun x => F (0, x)) = e := by
    ext x
    simp [F, finitePerturbation]
  have hevent := Manifold.eventually_exists_contDiff_ambient_isotopy hF
    (hFzero.symm ▸ he)
  filter_upwards [hevent] with p hp
  obtain ⟨Φ, hΦ, hΦi, hΦzero, hΦone, _⟩ := hp
  refine ⟨Φ, hΦ, hΦi, hΦzero, funext fun x => ?_⟩
  have hmap : Φ 1 (e x) = F (p, x) := by
    simpa only [congrFun hFzero x] using hΦone x
  rw [hmap]
  simp only [F, map_add, map_smul, hv, smul_eq_mul, mul_one]
  change f x + (finitePerturbation f φ p x - f x) = finitePerturbation f φ p x
  abel

private theorem exists_contDiff_ambient_isotopy_morse_height_of_apply_eq_one
    {e : M → V} (he : IsSmoothEmbedding I 𝓘(ℝ, V) ∞ e)
    (ℓ : V →L[ℝ] ℝ) {v : V} (hv : ℓ v = 1) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      ∀ x, IsCriticalPointAt I (fun y => ℓ (Φ 1 (e y))) x →
        IsNondegenerateCriticalPointAt I (fun y => ℓ (Φ 1 (e y))) x := by
  let : T2Space M := he.isEmbedding.t2Space
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (ℓ ∘ e) :=
    ℓ.contDiff.contMDiff.comp he.contMDiff
  obtain ⟨n, φ, hφ, _, hsmall⟩ :=
    exists_arbitrarily_small_relative_nondegenerate_manifold_finitePerturbation
      hf isCompact_univ isOpen_univ (subset_refl univ)
      (fun _ _ => BoundarylessManifold.isInteriorPoint)
  have hevent := eventually_exists_ambient_isotopy_finitePerturbation he ℓ hv
    (fun i => (hφ i).1)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
  obtain ⟨p, hp, hreg⟩ := hsmall ε hε
  obtain ⟨Φ, hΦ, hΦi, hΦzero, hΦone⟩ :=
    hball (show p ∈ Metric.ball 0 ε by simpa using hp)
  refine ⟨Φ, hΦ, hΦi, hΦzero, ?_⟩
  rw [hΦone]
  intro x hx
  exact isNondegenerateCriticalPointAt_of_bijective_hessian
    (contMDiff_finitePerturbation hf (fun i => (hφ i).1) p)
    BoundarylessManifold.isInteriorPoint hx (hreg x (mem_univ x) hx)

private theorem exists_contDiff_ambient_isotopy_excellent_height_of_morse
    {e : M → V} (he : IsSmoothEmbedding I 𝓘(ℝ, V) ∞ e)
    (ℓ : V →L[ℝ] ℝ) {v : V} (hv : ℓ v = 1)
    (hnd : ∀ x, IsCriticalPointAt I (ℓ ∘ e) x →
      IsNondegenerateCriticalPointAt I (ℓ ∘ e) x) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ x, IsCriticalPointAt I (fun y => ℓ (Φ 1 (e y))) x →
        IsNondegenerateCriticalPointAt I (fun y => ℓ (Φ 1 (e y))) x) ∧
      InjOn (fun y => ℓ (Φ 1 (e y)))
        {x | IsCriticalPointAt I (fun y => ℓ (Φ 1 (e y))) x} := by
  let : T2Space M := he.isEmbedding.t2Space
  let f : M → ℝ := ℓ ∘ e
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ℓ.contDiff.contMDiff.comp he.contMDiff
  have hC : {x | IsCriticalPointAt I f x}.Finite :=
    finite_criticalPoints_of_isCompact hf isCompact_univ
      (fun _ _ => BoundarylessManifold.isInteriorPoint) (fun _ _ => mem_univ _) hnd
  obtain ⟨n, c, φ, ε, _, hcC, hφ, hgerm, hε, hcrit⟩ :=
    exists_critical_value_perturbation_family hf hC isOpen_univ (subset_univ _)
      (fun _ _ => BoundarylessManifold.isInteriorPoint)
  have hevent := eventually_exists_ambient_isotopy_finitePerturbation he ℓ hv
    (fun i => (hφ i).1)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  obtain ⟨p, hp, hinj⟩ := DifferentialGeometry.Topology.exists_small_injective_add
    (fun i => f (c i)) (lt_min hε hδ)
  have hpε : ‖p‖ < ε := hp.trans_le (min_le_left _ _)
  have hpδ : ‖p‖ < δ := hp.trans_le (min_le_right _ _)
  obtain ⟨Φ, hΦ, hΦi, hΦzero, hΦone⟩ :=
    hball (show p ∈ Metric.ball 0 δ by simpa using hpδ)
  refine ⟨Φ, hΦ, hΦi, hΦzero, ?_, ?_⟩
  · rw [hΦone]
    intro x hx
    have hxC := (Set.ext_iff.mp (hcrit p hpε) x).mp hx
    obtain ⟨i, rfl⟩ := hcC.symm ▸ hxC
    exact (isNondegenerateCriticalPointAt_iff_of_eventuallyEq_add_const
      (hf.mdifferentiableAt (by simp)) BoundarylessManifold.isInteriorPoint
      (hgerm i p)).mpr (hnd (c i) ((Set.ext_iff.mp (hcrit p hpε) (c i)).mp hx))
  · rw [hΦone]
    intro x hx y hy hxy
    have hxC := (Set.ext_iff.mp (hcrit p hpε) x).mp hx
    have hyC := (Set.ext_iff.mp (hcrit p hpε) y).mp hy
    obtain ⟨i, rfl⟩ := hcC.symm ▸ hxC
    obtain ⟨j, rfl⟩ := hcC.symm ▸ hyC
    apply congrArg c
    apply hinj
    exact (hgerm i p).eq_of_nhds.symm.trans (hxy.trans (hgerm j p).eq_of_nhds)

theorem exists_contDiff_ambient_isotopy_excellent_height
    {e : M → V} (he : IsSmoothEmbedding I 𝓘(ℝ, V) ∞ e)
    (ℓ : V →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ x, IsCriticalPointAt I (fun y => ℓ (Φ 1 (e y))) x →
        IsNondegenerateCriticalPointAt I (fun y => ℓ (Φ 1 (e y))) x) ∧
      InjOn (fun y => ℓ (Φ 1 (e y)))
        {x | IsCriticalPointAt I (fun y => ℓ (Φ 1 (e y))) x} := by
  have hnonzero : ∃ w, ℓ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (ContinuousLinearMap.ext h)
  obtain ⟨w, hw⟩ := hnonzero
  have hv : ℓ ((ℓ w)⁻¹ • w) = 1 := by simp [hw]
  obtain ⟨Φ, hΦ, hΦi, hΦzero, hΦnd⟩ :=
    exists_contDiff_ambient_isotopy_morse_height_of_apply_eq_one he ℓ hv
  obtain ⟨Ψ, hΨ, hΨi, hΨzero, hΨnd, hΨinj⟩ :=
    exists_contDiff_ambient_isotopy_excellent_height_of_morse
      (he.diffeomorph_comp (Φ 1)) ℓ hv hΦnd
  refine ⟨fun t => (Φ t).trans (Ψ t), ?_, ?_, ?_, hΨnd, hΨinj⟩
  · exact hΨ.comp (contDiff_fst.prodMk hΦ)
  · exact hΦi.comp (contDiff_fst.prodMk hΨi)
  · change (Φ 0).trans (Ψ 0) = _
    rw [hΦzero, hΨzero]
    rfl

theorem exists_diffeomorph_excellent_height
    {e : M → V} (he : IsSmoothEmbedding I 𝓘(ℝ, V) ∞ e)
    (ℓ : V →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    ∃ Φ : V ≃ₘ[ℝ] V,
      (∀ x, IsCriticalPointAt I (fun y => ℓ (Φ (e y))) x →
        IsNondegenerateCriticalPointAt I (fun y => ℓ (Φ (e y))) x) ∧
      InjOn (fun y => ℓ (Φ (e y)))
        {x | IsCriticalPointAt I (fun y => ℓ (Φ (e y))) x} := by
  obtain ⟨Φ, _, _, _, hnd, hinj⟩ := he.exists_contDiff_ambient_isotopy_excellent_height ℓ hℓ
  exact ⟨Φ 1, hnd, hinj⟩

end Manifold.IsSmoothEmbedding

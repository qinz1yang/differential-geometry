import DifferentialGeometry.Topology.Manifold.Collar.Rescaling
import DifferentialGeometry.Topology.Manifold.Interval.CompressionInverse
import DifferentialGeometry.Topology.Collar.AttachmentRescaling

open Set Function Manifold Topology TopologicalSpace
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.Collar

theorem exists_smooth_attachment_realization
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    {F G M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace G M] [T2Space M]
    {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F G}
    {ε δ r : ℝ} [Fact ((0 : ℝ) < ε)] (hr : 0 < r)
    (hrε : 2 * r ≤ ε) (hrδ : 2 * r < δ)
    (f : C(B, M)) (c : C(B × Icc (0 : ℝ) ε, M)) (hc : IsEmbedding c)
    (hcs : ContMDiff (J.prod (𝓡∂ 1)) I ∞ c)
    (hzero : ∀ p, c (p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩) = f p)
    (Y : Opens M)
    (e : Diffeomorph (J.prod (𝓡∂ 1)) I
      (⟨{q : B × Icc (0 : ℝ) ε | q.2.val < δ},
        isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩ : Opens _) Y ∞)
    (he : ∀ q, (e q : M) = c q.val) :
    ∃ (a : ℝ) (ha : 0 < a) (_ : a < r),
      ∃ (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε)) (d : ℝ ≃ₘ[ℝ] ℝ),
        (∀ t : Icc (0 : ℝ) ε, (σ t).val = d t.val) ∧
        ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ σ ∧ StrictMono σ ∧
        range σ = {t : Icc (0 : ℝ) ε | a ≤ t.val} ∧
        (∀ t : Icc (0 : ℝ) ε, t.val ≤ r → (σ t).val = t.val + a) ∧
        (∀ t : Icc (0 : ℝ) ε, 2 * r ≤ t.val → σ t = t) ∧
        ∃ h : DifferentialGeometry.Topology.MappingCylinder f ≃ₜ M,
          (∀ x, h (DifferentialGeometry.Topology.mappingCylinderOriginal f x) =
            DifferentialGeometry.Topology.Collar.rescale c hc σ x) ∧
          (∀ q : B × Icc (0 : ℝ) 1, h (DifferentialGeometry.Topology.mappingCylinderProduct f q) =
            c (q.1, ⟨a * (1 - q.2.val),
              ⟨mul_nonneg ha.le (sub_nonneg.mpr q.2.property.2), by
                nlinarith [q.2.property.1]⟩⟩)) ∧
          ContMDiff I I ∞ (fun x => h (DifferentialGeometry.Topology.mappingCylinderOriginal f x)) ∧
          ContMDiff (J.prod (𝓡∂ 1)) I ∞ (fun q => h (DifferentialGeometry.Topology.mappingCylinderProduct f q)) := by
  have hε : 0 < ε := Fact.out
  have hY : (Y : Set M) = c '' {q | q.2.val < δ} := by
    ext y
    constructor
    · intro hy
      let q := e.symm ⟨y, hy⟩
      exact ⟨q.val, q.property, (he q).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩))⟩
    · rintro ⟨q, hq, rfl⟩
      rw [← he ⟨q, hq⟩]
      exact (e ⟨q, hq⟩).property
  obtain ⟨a, ha, har, σ, d, hσd, hσs, hσmono, hσrange, hσnear, hσfix⟩ :=
    DifferentialGeometry.Manifold.Interval.exists_smooth_compression_with_diffeomorph hr hrε
  let cut : Icc (0 : ℝ) ε := ⟨a, ha.le, by linarith⟩
  have hσ0 : σ ⟨0, ⟨le_rfl, hε.le⟩⟩ = cut := by
    apply Subtype.ext
    simpa [cut] using hσnear ⟨0, ⟨le_rfl, hε.le⟩⟩ hr.le
  obtain ⟨h, hO, hP⟩ := DifferentialGeometry.Topology.Collar.exists_attachment_homeomorph_of_rescaling
    f (a := cut) ha (k := 2 * r) hrδ c hc hzero
    (hY ▸ Y.isOpen) σ hσmono.injective hσ0 hσrange hσfix
  have hOs : ContMDiff I I ∞ (fun x => h (DifferentialGeometry.Topology.mappingCylinderOriginal f x)) := by
    have hh := contMDiff_rescale c hc hcs σ hσs e he
      (k := 2 * r) (fun _ hq => hq.trans_lt hrδ) hσfix
    exact hh.congr hO
  let ρ : Icc (0 : ℝ) 1 → Icc (0 : ℝ) ε :=
    fun t => ⟨a * (1 - t.val), mul_nonneg ha.le (sub_nonneg.mpr t.property.2), by
      nlinarith [t.property.1]⟩
  have hρ : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ ρ := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    refine ⟨by fun_prop, ?_⟩
    have hlin : ContDiff ℝ ∞ (fun t : ℝ => a * (1 - t)) := by fun_prop
    exact hlin.contMDiff.comp (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1))
  exact ⟨a, ha, har, σ, d, hσd, hσs, hσmono, hσrange, hσnear, hσfix,
    h, hO, hP, hOs, (hcs.comp (contMDiff_id.prodMap hρ)).congr hP⟩

end DifferentialGeometry.Manifold.Collar

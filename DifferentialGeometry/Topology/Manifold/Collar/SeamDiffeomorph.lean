import DifferentialGeometry.Topology.Manifold.Collar.AttachmentSeam
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Restriction
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Preimage

open Set Function Manifold Topology TopologicalSpace
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.Collar

local instance : Fact ((-1 : ℝ) < 1) := ⟨by norm_num⟩

private def seamParameterDiffeomorph
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (J : ModelWithCorners ℝ E H) {ε : ℝ} [Fact ((0 : ℝ) < ε)]
    (a : ℝ) (ha : 0 < a) (h2a : 2 * a ≤ ε)
    (U : Opens (B × Icc (-1 : ℝ) 1)) (R : Opens (B × Icc (0 : ℝ) ε))
    (hR : ∀ q : R, q.val.2.val ≤ 2 * a)
    (hUR : ∀ q : U, (q.val.1, (⟨a * (1 - q.val.2.val), by
      constructor <;> nlinarith [q.val.2.property.1, q.val.2.property.2]⟩ : Icc (0 : ℝ) ε)) ∈ R)
    (hRU : ∀ q : R, (q.val.1, (⟨1 - q.val.2.val / a, by
      have hlo : 0 ≤ q.val.2.val / a := div_nonneg q.val.2.property.1 ha.le
      have hhi : q.val.2.val / a ≤ 2 := (div_le_iff₀ ha).mpr (by linarith [hR q])
      constructor <;> linarith⟩ : Icc (-1 : ℝ) 1)) ∈ U) :
    Diffeomorph (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) U R ∞ := by
  let f : U → R := fun q =>
    ⟨(q.val.1, ⟨a * (1 - q.val.2.val), by
      constructor <;> nlinarith [q.val.2.property.1, q.val.2.property.2]⟩), hUR q⟩
  let g : R → U := fun q =>
    ⟨(q.val.1, ⟨1 - q.val.2.val / a, by
      have hlo : 0 ≤ q.val.2.val / a := div_nonneg q.val.2.property.1 ha.le
      have hhi : q.val.2.val / a ≤ 2 := (div_le_iff₀ ha).mpr (by linarith [hR q])
      constructor <;> linarith⟩), hRU q⟩
  have hfg (q : U) : g (f q) = q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change 1 - a * (1 - q.val.2.val) / a = q.val.2.val
      field_simp
      ring
  have hgf (q : R) : f (g q) = q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change a * (1 - (1 - q.val.2.val / a)) = q.val.2.val
      field_simp
      ring
  have hf : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff R f).mp
    apply ContMDiff.prodMk
    · exact contMDiff_fst.comp contMDiff_subtype_val
    · apply contMDiff_iff_comp_subtypeVal_Icc.mpr
      refine ⟨by fun_prop, ?_⟩
      have hlin : ContDiff ℝ ∞ (fun t : ℝ => a * (1 - t)) := by fun_prop
      exact hlin.contMDiff.comp ((contMDiff_subtypeVal_Icc (x := (-1 : ℝ)) (y := 1)).comp
        (contMDiff_snd.comp contMDiff_subtype_val))
  have hg : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) ∞ g := by
    apply (ContMDiff.subtypeVal_comp_iff U g).mp
    apply ContMDiff.prodMk
    · exact contMDiff_fst.comp contMDiff_subtype_val
    · apply contMDiff_iff_comp_subtypeVal_Icc.mpr
      refine ⟨by fun_prop, ?_⟩
      have hlin : ContDiff ℝ ∞ (fun t : ℝ => 1 - t / a) := by fun_prop
      exact hlin.contMDiff.comp ((contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := ε)).comp
        (contMDiff_snd.comp contMDiff_subtype_val))
  exact ⟨⟨f, g, hfg, hgf⟩, hf, hg⟩

theorem exists_attachmentSeam_diffeomorph
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    {F G M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace G M]
    {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F G} [IsManifold I ∞ M]
    {ε : ℝ} [Fact ((0 : ℝ) < ε)]
    (f : C(B, M)) (c : C(B × Icc (0 : ℝ) ε, M)) (a : Icc (0 : ℝ) ε)
    (ha : 0 < a.val) (h2a : 2 * a.val ≤ ε)
    (hzero : ∀ p, c (p, ⟨0, ⟨le_rfl, a.property.1.trans a.property.2⟩⟩) = f p)
    (hc : IsEmbedding c)
    {Ω : Opens (B × Icc (0 : ℝ) ε)} {Y : Opens M}
    (e : Diffeomorph (J.prod (𝓡∂ 1)) I Ω Y ∞)
    (he : ∀ q : Ω, (e q : M) = c q.val)
    (hcore : {q : B × Icc (0 : ℝ) ε | 0 < q.2.val ∧ q.2.val < 2 * a.val} ⊆ Ω)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε))
    (hσnear : ∀ t : Icc (0 : ℝ) ε, t.val ≤ a.val → (σ t).val = t.val + a.val)
    (h : DifferentialGeometry.Topology.MappingCylinder f ≃ₜ M)
    (hO : ∀ x, h (DifferentialGeometry.Topology.mappingCylinderOriginal f x) =
      DifferentialGeometry.Topology.Collar.rescale c hc σ x)
    (hP : ∀ q : B × Icc (0 : ℝ) 1, h (DifferentialGeometry.Topology.mappingCylinderProduct f q) =
      c (q.1, ⟨a.val * (1 - q.2.val),
        ⟨mul_nonneg a.property.1 (sub_nonneg.mpr q.2.property.2), by
          nlinarith [q.2.property.1, a.property.1, a.property.2]⟩⟩)) :
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := G) h
    let U : Opens (B × Icc (-1 : ℝ) 1) :=
      ⟨{q | -1 < q.2.val ∧ q.2.val < 1},
        (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
          (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)⟩
    ∃ Z : Opens (DifferentialGeometry.Topology.MappingCylinder f),
      (Z : Set _) = DifferentialGeometry.Topology.Collar.attachmentSeam f c a hzero '' (U : Set _) ∧
      ∃ d : Diffeomorph (J.prod (𝓡∂ 1)) I U Z ∞,
        (∀ q : U, (d q : DifferentialGeometry.Topology.MappingCylinder f) =
          DifferentialGeometry.Topology.Collar.attachmentSeam f c a hzero q.val) ∧
        ∀ z : Z, DifferentialGeometry.Topology.Collar.attachmentSeam f c a hzero (d.symm z).val = z.val := by
  intro C U
  let _ := C
  let R : Opens (B × Icc (0 : ℝ) ε) :=
    ⟨{q | 0 < q.2.val ∧ q.2.val < 2 * a.val},
      (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
        (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)⟩
  let p : Diffeomorph (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) U R ∞ :=
    seamParameterDiffeomorph J a.val ha h2a U R (fun q => q.property.2.le)
      (fun q => by constructor <;> nlinarith [q.property.1, q.property.2])
      (fun q => by
        have hlo : 0 < q.val.2.val / a.val := div_pos q.property.1 ha
        have hhi : q.val.2.val / a.val < 2 := (div_lt_iff₀ ha).mpr (by linarith [q.property.2])
        constructor <;> linarith)
  obtain ⟨W, _, _, eR, heR, _⟩ :=
    DifferentialGeometry.Manifold.Diffeomorph.exists_restrict_opens e R hcore
  let k := p.trans eR
  let g : U → DifferentialGeometry.Topology.MappingCylinder f := fun q => h.symm (k q : M)
  have hgeq (q : U) : g q = DifferentialGeometry.Topology.Collar.attachmentSeam f c a hzero q.val := by
    apply h.injective
    change h (h.symm (eR (p q) : M)) = _
    rw [h.apply_symm_apply, heR, he]
    exact (DifferentialGeometry.Topology.Collar.attachmentSeam_realization
      f c a hzero hc h2a σ hσnear h hO hP q.val).symm
  let dh : Diffeomorph I I (DifferentialGeometry.Topology.MappingCylinder f) M ∞ :=
    DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph h
  let Z : Opens (DifferentialGeometry.Topology.MappingCylinder f) := ⟨h ⁻¹' W, W.isOpen.preimage h.continuous⟩
  let d : Diffeomorph (J.prod (𝓡∂ 1)) I U Z ∞ :=
    k.trans (DifferentialGeometry.Manifold.Diffeomorph.preimage dh W).symm
  have hd (q : U) : (d q : DifferentialGeometry.Topology.MappingCylinder f) = g q := rfl
  refine ⟨Z, ?_, d, (fun q => (hd q).trans (hgeq q)), ?_⟩
  · ext z
    constructor
    · intro hz
      let q := k.symm ⟨h z, hz⟩
      refine ⟨q.val, q.property, ?_⟩
      rw [← hgeq q]
      change h.symm (k (k.symm ⟨h z, hz⟩) : M) = z
      rw [k.apply_symm_apply]
      exact h.symm_apply_apply z
    · rintro ⟨q, hq, rfl⟩
      rw [← hgeq ⟨q, hq⟩]
      change h (h.symm (k ⟨q, hq⟩ : M)) ∈ W
      rw [h.apply_symm_apply]
      exact (k ⟨q, hq⟩).property
  · intro z
    exact (hgeq (d.symm z)).symm.trans (congrArg Subtype.val (d.apply_symm_apply z))

theorem exists_attachmentSeam_boundary_diffeomorph
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    {F G M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace G M]
    {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F G} [IsManifold I ∞ M]
    {ε : ℝ} [Fact ((0 : ℝ) < ε)]
    (f : C(B, M)) (c : C(B × Icc (0 : ℝ) ε, M)) (a : Icc (0 : ℝ) ε)
    (ha : 0 < a.val) (h2a : 2 * a.val ≤ ε)
    (hzero : ∀ p, c (p, ⟨0, ⟨le_rfl, a.property.1.trans a.property.2⟩⟩) = f p)
    (hc : IsEmbedding c)
    {Ω : Opens (B × Icc (0 : ℝ) ε)} {Y : Opens M}
    (e : Diffeomorph (J.prod (𝓡∂ 1)) I Ω Y ∞)
    (he : ∀ q : Ω, (e q : M) = c q.val)
    (hcore : {q : B × Icc (0 : ℝ) ε | q.2.val < 2 * a.val} ⊆ Ω)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε))
    (hσnear : ∀ t : Icc (0 : ℝ) ε, t.val ≤ a.val → (σ t).val = t.val + a.val)
    (h : DifferentialGeometry.Topology.MappingCylinder f ≃ₜ M)
    (hO : ∀ x, h (DifferentialGeometry.Topology.mappingCylinderOriginal f x) =
      DifferentialGeometry.Topology.Collar.rescale c hc σ x)
    (hP : ∀ q : B × Icc (0 : ℝ) 1, h (DifferentialGeometry.Topology.mappingCylinderProduct f q) =
      c (q.1, ⟨a.val * (1 - q.2.val),
        ⟨mul_nonneg a.property.1 (sub_nonneg.mpr q.2.property.2), by
          nlinarith [q.2.property.1, a.property.1, a.property.2]⟩⟩)) :
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := G) h
    let U : Opens (B × Icc (-1 : ℝ) 1) :=
      ⟨{q | -1 < q.2.val}, isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)⟩
    ∃ Z : Opens (DifferentialGeometry.Topology.MappingCylinder f),
      (Z : Set _) = DifferentialGeometry.Topology.Collar.attachmentSeam f c a hzero '' (U : Set _) ∧
      range (DifferentialGeometry.Topology.mappingCylinderProduct f) ⊆ Z ∧
      ∃ d : Diffeomorph (J.prod (𝓡∂ 1)) I U Z ∞,
        (∀ q : U, (d q : DifferentialGeometry.Topology.MappingCylinder f) =
          DifferentialGeometry.Topology.Collar.attachmentSeam f c a hzero q.val) ∧
        ∀ z : Z, DifferentialGeometry.Topology.Collar.attachmentSeam f c a hzero (d.symm z).val = z.val := by
  intro C U
  let _ := C
  let R : Opens (B × Icc (0 : ℝ) ε) :=
    ⟨{q | q.2.val < 2 * a.val},
      isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
  let p : Diffeomorph (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) U R ∞ :=
    seamParameterDiffeomorph J a.val ha h2a U R (fun q => q.property.le)
      (fun q => by
        have hq : -1 < q.val.2.val := q.property
        change a.val * (1 - q.val.2.val) < 2 * a.val
        nlinarith)
      (fun q => by
        have hhi : q.val.2.val / a.val < 2 := (div_lt_iff₀ ha).mpr q.property
        change -1 < 1 - q.val.2.val / a.val
        linarith)
  obtain ⟨W, _, _, eR, heR, _⟩ :=
    DifferentialGeometry.Manifold.Diffeomorph.exists_restrict_opens e R hcore
  let k := p.trans eR
  let g : U → DifferentialGeometry.Topology.MappingCylinder f := fun q => h.symm (k q : M)
  have hgeq (q : U) : g q = DifferentialGeometry.Topology.Collar.attachmentSeam f c a hzero q.val := by
    apply h.injective
    change h (h.symm (eR (p q) : M)) = _
    rw [h.apply_symm_apply, heR, he]
    exact (DifferentialGeometry.Topology.Collar.attachmentSeam_realization
      f c a hzero hc h2a σ hσnear h hO hP q.val).symm
  let dh : Diffeomorph I I (DifferentialGeometry.Topology.MappingCylinder f) M ∞ :=
    DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph h
  let Z : Opens (DifferentialGeometry.Topology.MappingCylinder f) := ⟨h ⁻¹' W, W.isOpen.preimage h.continuous⟩
  let d : Diffeomorph (J.prod (𝓡∂ 1)) I U Z ∞ :=
    k.trans (DifferentialGeometry.Manifold.Diffeomorph.preimage dh W).symm
  have hd (q : U) : (d q : DifferentialGeometry.Topology.MappingCylinder f) = g q := rfl
  refine ⟨Z, ?_, ?_, d, (fun q => (hd q).trans (hgeq q)), ?_⟩
  · ext z
    constructor
    · intro hz
      let q := k.symm ⟨h z, hz⟩
      refine ⟨q.val, q.property, ?_⟩
      rw [← hgeq q]
      change h.symm (k (k.symm ⟨h z, hz⟩) : M) = z
      rw [k.apply_symm_apply]
      exact h.symm_apply_apply z
    · rintro ⟨q, hq, rfl⟩
      rw [← hgeq ⟨q, hq⟩]
      change h (h.symm (k ⟨q, hq⟩ : M)) ∈ W
      rw [h.apply_symm_apply]
      exact (k ⟨q, hq⟩).property
  · rintro z ⟨⟨p, t⟩, rfl⟩
    let q : U := ⟨(p, ⟨t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩),
      by change -1 < t.val; linarith [t.property.1]⟩
    have hq : g q = DifferentialGeometry.Topology.mappingCylinderProduct f (p, t) :=
      (hgeq q).trans (DifferentialGeometry.Topology.Collar.attachmentSeam_nonneg f c a hzero q.val t.property.1)
    rw [← hq]
    change h (h.symm (k q : M)) ∈ W
    rw [h.apply_symm_apply]
    exact (k q).property
  · intro z
    exact (hgeq (d.symm z)).symm.trans (congrArg Subtype.val (d.apply_symm_apply z))

end DifferentialGeometry.Manifold.Collar

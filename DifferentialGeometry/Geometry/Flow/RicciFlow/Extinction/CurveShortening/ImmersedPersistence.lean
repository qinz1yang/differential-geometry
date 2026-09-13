import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistenceFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Connection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CalculusGeometry
import DifferentialGeometry.Topology.Manifold.AddCircle

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem isOpen_setOf_tangentBundle_snd_ne_zero :
    IsOpen {v : TangentBundle I M | v.2 ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  intro v hv
  set e := trivializationAt E (TangentSpace I) v.1 with he
  have hbase : v.1 ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) v.1
  have hvsrc : v ∈ e.source := (e.mem_source).mpr hbase
  have hU : IsOpen {z : M × E | z.2 ≠ 0} :=
    isOpen_compl_singleton.preimage continuous_snd
  have hsub : e.source ∩ e ⁻¹' {z : M × E | z.2 ≠ 0} ⊆ {w : TangentBundle I M | w.2 ≠ 0} := by
    rintro ⟨proj, snd⟩ hw hw0
    have hsnd : snd = 0 := by simpa using hw0
    have hwb : proj ∈ e.baseSet := (e.mem_source).mp hw.1
    have h' := congrArg Prod.snd
      (e.apply_eq_prod_continuousLinearEquivAt ℝ proj hwb snd)
    exact hw.2 (by simpa only [hsnd, map_zero] using h')
  refine mem_of_superset ?_ hsub
  have hvU : v ∈ e.source ∩ e ⁻¹' {z : M × E | z.2 ≠ 0} := by
    refine ⟨hvsrc, ?_⟩
    change (e v).2 ≠ 0
    rw [e.apply_eq_prod_continuousLinearEquivAt ℝ v.1 hbase v.2]
    exact fun hcon => hv ((e.continuousLinearEquivAt ℝ v.1 hbase).map_eq_zero_iff.mp hcon)
  exact (e.isOpen_inter_preimage hU).mem_nhds hvU

private theorem exists_eventually_forall_mem_of_isCompact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {t₀ T : ℝ} (ht : t₀ < T) {Y : Type*} [TopologicalSpace Y]
    {f : X × ℝ → Y} {U : Set Y} (hU : IsOpen U)
    (hf : ContinuousOn f (K ×ˢ Icc t₀ T))
    (hKU : ∀ x, x ∈ K → f (x, t₀) ∈ U) :
    ∃ τ, 0 < τ ∧ τ ≤ T - t₀ ∧
      ∀ x, x ∈ K → ∀ t, t ∈ Icc t₀ (t₀ + τ) → f (x, t) ∈ U := by
  have hpre : f ⁻¹' U ∈ 𝓝ˢ[K ×ˢ Icc t₀ T] (K ×ˢ ({t₀} : Set ℝ)) := by
    have hU' : U ∈ 𝓝ˢ (f '' (K ×ˢ ({t₀} : Set ℝ))) :=
      hU.mem_nhdsSet.mpr <| by
        rintro _ ⟨p, hp, rfl⟩
        rcases p with ⟨x, t⟩
        rcases hp with ⟨hx, htmem⟩
        have ht' : t = t₀ := by simpa using htmem
        subst t
        exact hKU x hx
    have hpre' := hf.preimage_mem_nhdsSetWithin_of_mem_nhdsSet hU'
    refine (nhdsSetWithin_mono_left ?_ hpre')
    intro p hp
    rcases p with ⟨x, t⟩
    rcases hp with ⟨hx, htmem⟩
    have ht' : t = t₀ := by simpa using htmem
    subst t
    exact ⟨⟨hx, ⟨le_rfl, ht.le⟩⟩, ⟨x, t₀⟩, ⟨hx, rfl⟩, rfl⟩
  obtain ⟨V, hVopen, hVtarget, hVsub⟩ := mem_nhdsSetWithin.mp hpre
  obtain ⟨Ux, Vt, hUxopen, hVtopen, hKUx, ht₀Vt, hUV⟩ :=
    generalized_tube_lemma hK isCompact_singleton hVopen hVtarget
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hVtopen.mem_nhds (ht₀Vt rfl))
  refine ⟨min (ε / 2) (T - t₀), lt_min (by positivity) (sub_pos.mpr ht), min_le_right _ _, ?_⟩
  intro x hx t htI
  have htt : t ∈ Vt := by
    refine hεsub ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr htI.1)]
    have htminus : t - t₀ ≤ min (ε / 2) (T - t₀) := by linarith [htI.2]
    have hτ : min (ε / 2) (T - t₀) < ε :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    exact lt_of_le_of_lt htminus hτ
  have htT : t ∈ Icc t₀ T := by
    refine ⟨htI.1, ?_⟩
    linarith [htI.2, min_le_right (ε / 2) (T - t₀)]
  exact hVsub ⟨hUV ⟨hKUx hx, htt⟩, ⟨hx, htT⟩⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem curveShorteningImmersedPersistence :
    CurveShorteningImmersedPersistence (I := I) (M := M) := by
  intro t₀ T ht c hc hX₀
  let F : ℝ × ℝ → TangentBundle I M := fun p =>
    (⟨c.lift p.1 p.2, c.X p.1 p.2⟩ : TangentBundle I M)
  let U : Set (TangentBundle I M) := {v | v.2 ≠ 0}
  have hU : IsOpen U := isOpen_setOf_tangentBundle_snd_ne_zero (I := I) (M := M)
  have hF : ContinuousOn F ((Icc (0 : ℝ) 1) ×ˢ Icc t₀ T) :=
    (CurveMap.Field.smoothOn_X c (Icc t₀ T) hc).continuousOn.mono
      (Set.prod_mono (subset_univ _) Subset.rfl)
  obtain ⟨τ, hτpos, hτle, hτ⟩ :=
    exists_eventually_forall_mem_of_isCompact isCompact_Icc ht hU hF
      (fun x _ => hX₀ x)
  refine ⟨τ, hτpos, hτle, ?_⟩
  intro x t htI
  obtain ⟨y, hyI, hyx⟩ := AddCircle.eq_coe_Ico (x : AddCircle (1 : ℝ))
  have hXper : Function.Periodic (fun z : ℝ => c.X (I := I) z t) 1 := fun z =>
    have hspace : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun y : ℝ => c.lift y t) :=
      contMDiffOn_univ.mp (CurveMap.space_slice_contMDiffOn c (Icc t₀ T) hc t
        ⟨htI.1, by linarith [htI.2, hτle]⟩)
    CurveMap.X_add_period c t z
      ((hspace (z + 1)).mdifferentiableAt (by simp))
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk'_eq_mk' (N := AddSubgroup.zmultiples (1 : ℝ)) |>.mp (by
    simpa only [QuotientAddGroup.mk'_apply] using hyx.symm)
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hz.1
  have hxy : x + (n : ℤ) • (1 : ℝ) = y := by
    rw [hn]
    exact hz.2
  have hXyx : c.X (I := I) x t = c.X (I := I) y t := by
    rw [← hxy]
    have harg : x + (n : ℤ) • (1 : ℝ) = x + (n : ℝ) * 1 := by
      rw [zsmul_eq_mul]
    rw [harg]
    exact ((hXper.int_mul n) x).symm
  rw [hXyx]
  exact hτ y (⟨hyI.1, hyI.2.le⟩) t htI

theorem exists_curveShorteningImmersedPersistence_addCircle :
    ∃ c : CurveMap (AddCircle (1 : ℝ)),
      c.SmoothOn (I := 𝓘(ℝ, ℝ)) (Icc (0 : ℝ) 1) ∧
      (∀ x, c.X (I := 𝓘(ℝ, ℝ)) x 0 ≠ 0) ∧
      ∃ τ, 0 < τ ∧ τ ≤ 1 ∧ c.ImmersedOn (I := 𝓘(ℝ, ℝ)) (Icc 0 (0 + τ)) := by
  let c : CurveMap (AddCircle (1 : ℝ)) := fun z _ => z
  have hc : c.SmoothOn (I := 𝓘(ℝ, ℝ)) (Icc (0 : ℝ) 1) := by
    rw [CurveMap.SmoothOn]
    change ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × ℝ => (p.1 : AddCircle (1 : ℝ))) (univ ×ˢ Icc (0 : ℝ) 1)
    have hfst : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × ℝ => p.1) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact contMDiff_fst
    exact (AddCircle.contMDiff_coe.comp hfst).contMDiffOn
  have hX : ∀ x, c.X (I := 𝓘(ℝ, ℝ)) x 0 ≠ 0 := by
    intro x
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun y : ℝ => (y : AddCircle (1 : ℝ))) x) 1 ≠ 0
    intro hzero
    have hb := (AddCircle.bijective_mfderiv_coe x).1
    have hL0 : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun y : ℝ => (y : AddCircle (1 : ℝ))) x) 1 =
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun y : ℝ => (y : AddCircle (1 : ℝ))) x) 0 := by
      rw [hzero, map_zero]
    exact (one_ne_zero : (1 : ℝ) ≠ 0) (hb hL0)
  obtain ⟨τ, hτpos, hτle, himm⟩ :=
    curveShorteningImmersedPersistence (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
      (by norm_num : (0 : ℝ) < 1) c hc hX
  exact ⟨c, hc, hX, τ, hτpos, by simpa using hτle, by simpa using himm⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

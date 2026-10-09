import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.VelocityExtensionLocalGluing
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartSection
import DifferentialGeometry.Analysis.Calculus.Inverse.SmoothLocalInverse
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology
open DifferentialGeometry.Geometry.Connection

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]

theorem continuousLinearMap_eq_smulRight_one (f : ℝ →L[ℝ] T) :
    f = (1 : ℝ →L[ℝ] ℝ).smulRight (f 1) := by
  ext
  simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
theorem hasMFDerivWithinAt_of_hasFDerivWithinAt_chartReading
    {c : ℝ → M} {α : M} {s : Set ℝ} {t : ℝ}
    (ht : t ∈ s) (hsrc : ∀ r ∈ s, c r ∈ (chartAt H α).source)
    {L : ℝ →L[ℝ] E}
    (h : HasFDerivWithinAt (fun r => extChartAt I α (c r)) L s t) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I c s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (trivFromE (I := I) α (c t) (L 1))) := by
  have hf : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => extChartAt I α (c r)) s t L :=
    h.hasMFDerivWithinAt
  have hg : HasMFDerivAt[Set.range (I : H → E)] (extChartAt I α).symm
      (extChartAt I α (c t)) (trivFromE (I := I) α (c t)) := by
    have h1 :=
      (mdifferentiableWithinAt_extChartAt_symm (I := I)
        ((extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc t ht))
        ).hasMFDerivWithinAt
    rwa [← TangentBundle.symmL_trivializationAt (I := I) (hsrc t ht)] at h1
  have hcomp := HasMFDerivWithinAt.comp t hg hf
    (fun r _ => show extChartAt I α (c r) ∈ Set.range (I : H → E) from
      ⟨(chartAt H α) (c r), rfl⟩)
  have hcongr : Set.EqOn ((extChartAt I α).symm ∘ fun r => extChartAt I α (c r)) c s :=
    fun r hr => (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hsrc r hr)
  have hkey : (trivFromE (I := I) α (c t)).comp L =
      (1 : ℝ →L[ℝ] ℝ).smulRight (trivFromE (I := I) α (c t) (L 1)) := by
    ext
    simp [ContinuousLinearMap.smulRight_apply]
  rw [← hkey]
  refine HasMFDerivWithinAt.congr_of_eventuallyEq
    (f := fun r => (extChartAt I α).symm (extChartAt I α (c r))) (f₁ := c) hcomp ?_ ?_
  · exact Filter.eventuallyEq_of_mem self_mem_nhdsWithin hcongr.symm
  · exact (hcongr ht).symm

omit [FiniteDimensional ℝ E] in
theorem hasFDerivWithinAt_chartReading_of_hasMFDerivWithinAt
    {c : ℝ → M} {α : M} {s : Set ℝ} {t : ℝ}
    (ht : t ∈ s) (hsrc : ∀ r ∈ s, c r ∈ (chartAt H α).source)
    {v : TangentSpace I (c t)}
    (h : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I c s t ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    HasFDerivWithinAt (fun r => extChartAt I α (c r))
      ((1 : ℝ →L[ℝ] ℝ).smulRight (trivToE (I := I) α (c t) v)) s t := by
  have hψ : HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I α) (c t) (trivToE (I := I) α (c t)) := by
    have h1 := (mdifferentiableAt_extChartAt (I := I) (hsrc t ht)).hasMFDerivAt
    rwa [← TangentBundle.continuousLinearMapAt_trivializationAt (I := I) (hsrc t ht)] at h1
  have hcomp := HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_univ.mpr hψ) h
    (fun _ _ => mem_univ _)
  have hkey : (trivToE (I := I) α (c t)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight v) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (trivToE (I := I) α (c t) v) := by
    ext
    simp [ContinuousLinearMap.smulRight_apply]
  rw [← hkey]
  exact hcomp.hasFDerivWithinAt

omit [FiniteDimensional ℝ E] in
theorem contMDiffOn_lift_trivFromE_reading (α : M) (g : ℝ → E → E) (W : Set (ℝ × E))
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) W) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 ((trivFromE (I := I) α q.2) (g q.1 (extChartAt I α q.2))) :
          TangentBundle I M))
      {q : ℝ × M | q.2 ∈ (chartAt H α).source ∧ (q.1, extChartAt I α q.2) ∈ W} := by
  classical
  set S : Set (ℝ × M) :=
    {q : ℝ × M | q.2 ∈ (chartAt H α).source ∧ (q.1, extChartAt I α q.2) ∈ W}
  set e : Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α
  set Y : ℝ → ∀ x : M, TangentSpace I x :=
    fun t x => (trivFromE (I := I) α x) (g t (extChartAt I α x))
  have hbase : ∀ q ∈ S, q.2 ∈ e.baseSet := by
    intro q hq
    rw [TangentBundle.trivializationAt_baseSet]
    exact hq.1
  have hmaps : Set.MapsTo
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y q.1 q.2) : TangentBundle I M)) S e.source := by
    intro q hq
    rw [Trivialization.mem_source]
    exact hbase q hq
  have hiff := e.contMDiffOn_iff (n := ∞) (IM := 𝓘(ℝ, ℝ).prod I) (IB := I)
    (f := fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y q.1 q.2) : TangentBundle I M)) hmaps
  have hgextM :
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (Function.uncurry g) W := by
    rw [← contMDiffOn_iff_contDiffOn, ← chartedSpaceSelf_prod, modelWithCornersSelf_prod] at hg
    exact hg
  have hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (q.1, extChartAt I α q.2)) S := by
    refine ContMDiffOn.prodMk contMDiffOn_fst ?_
    refine (contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)).comp contMDiffOn_snd ?_
    intro q hq; exact hq.1
  have hread : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => g q.1 (extChartAt I α q.2)) S :=
    hgextM.comp hΦ fun q hq => hq.2
  refine (hiff.mpr ⟨contMDiffOn_snd, ?_⟩)
  refine hread.congr ?_
  intro q hq
  have hq2 : q.2 ∈ e.baseSet := hbase q hq
  change (e (TotalSpace.mk' E q.2 (Y q.1 q.2))).2 = g q.1 (extChartAt I α q.2)
  rw [← chartE_section_repr_eq_trivialization_snd (I := I) α (Y q.1) hq2]
  change trivToE (I := I) α q.2
      ((trivFromE (I := I) α q.2) (g q.1 (extChartAt I α q.2))) = g q.1 (extChartAt I α q.2)
  rw [trivToE_trivFromE (I := I) α hq2]

omit [FiniteDimensional ℝ E] in
theorem fderiv_chartReading_eq (c : ℝ → M) (α : M) (t : ℝ)
    (hct : c t ∈ (chartAt H α).source)
    (hsrc : ∀ᶠ r in 𝓝 t, c r ∈ (chartAt H α).source)
    (hd : MDifferentiableAt 𝓘(ℝ, ℝ) I c t) :
    fderiv ℝ (fun r => extChartAt I α (c r)) t 1 =
      trivToE (I := I) α (c t) (mfderiv 𝓘(ℝ, ℝ) I c t 1) := by
  have hkey : mfderiv 𝓘(ℝ, ℝ) I c t =
      (1 : ℝ →L[ℝ] ℝ).smulRight (mfderiv 𝓘(ℝ, ℝ) I c t 1) := by
    exact continuousLinearMap_eq_smulRight_one
      (mfderiv 𝓘(ℝ, ℝ) I c t : ℝ →L[ℝ] TangentSpace I (c t))
  have hs_nhds : c ⁻¹' (chartAt H α).source ∈ 𝓝 t := hsrc
  have hts : t ∈ c ⁻¹' (chartAt H α).source := hct
  have hwit : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I c (c ⁻¹' (chartAt H α).source) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mfderiv 𝓘(ℝ, ℝ) I c t 1)) := by
    have h1 : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I c univ t (mfderiv 𝓘(ℝ, ℝ) I c t) :=
      hasMFDerivWithinAt_univ.mpr hd.hasMFDerivAt
    have h2 : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I c (c ⁻¹' (chartAt H α).source) t
        (mfderiv 𝓘(ℝ, ℝ) I c t) :=
      HasMFDerivWithinAt.mono h1 (subset_univ _)
    rwa [hkey] at h2
  have hb := hasFDerivWithinAt_chartReading_of_hasMFDerivWithinAt (I := I) hts
    (fun r hr => hr) hwit
  have hAt : HasFDerivAt (fun r => extChartAt I α (c r))
      ((1 : ℝ →L[ℝ] ℝ).smulRight (trivToE (I := I) α (c t)
        (mfderiv 𝓘(ℝ, ℝ) I c t 1))) t :=
    hb.hasFDerivAt hs_nhds
  rw [hAt.fderiv]
  simp [ContinuousLinearMap.smulRight_apply]

omit [FiniteDimensional ℝ E] in
theorem injective_fderiv_chartGraph
    {γ : ℝ → ContinuousFreeLoop M} {a b t₀ x₀ : ℝ} {α : M}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (ht₀ : t₀ ∈ Icc a b) (hα : α = γ t₀ (x₀ : Surgery.Topology.Circle))
    {gE : ℝ → ℝ → E} {W : Set (ℝ × ℝ)} (hWo : IsOpen W) (hW : (t₀, x₀) ∈ W)
    (hsm : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => gE p.1 p.2) W)
    (hag : ∀ p ∈ W, p.1 ∈ Icc a b →
      γ p.1 (p.2 : Surgery.Topology.Circle) ∈ (chartAt H α).source ∧
      gE p.1 p.2 = extChartAt I α (γ p.1 (p.2 : Surgery.Topology.Circle))) :
    Injective (fderiv ℝ (fun p : ℝ × ℝ => (p.1, gE p.1 p.2)) (t₀, x₀)) := by
  subst hα
  have hsm_at : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => gE p.1 p.2) (t₀, x₀) :=
    hsm.contDiffAt (hWo.mem_nhds hW)
  have hL : HasFDerivAt (fun p : ℝ × ℝ => gE p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t₀, x₀)) (t₀, x₀) :=
    (hsm_at.differentiableAt (by simp)).hasFDerivAt
  have hD : fderiv ℝ (fun p : ℝ × ℝ => (p.1, gE p.1 p.2)) (t₀, x₀) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t₀, x₀)) :=
    (hasFDerivAt_fst.prodMk hL).fderiv
  obtain ⟨u, hu, v, hv, huv⟩ :=
    Filter.mem_prod_iff.mp (show W ∈ 𝓝 t₀ ×ˢ 𝓝 x₀ by
      rw [← nhds_prod_eq]; exact hWo.mem_nhds hW)
  have hWn : ∀ᶠ y in 𝓝 x₀, (t₀, y) ∈ W :=
    Filter.eventually_of_mem hv fun y hy => huv ⟨mem_of_mem_nhds hu, hy⟩
  have hslice : fderiv ℝ (fun y : ℝ => gE t₀ y) x₀ =
      (fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t₀, x₀)).comp
        ((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)) := by
    have hinr : HasFDerivAt (fun y : ℝ => (t₀, y))
        ((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)) x₀ :=
      (hasFDerivAt_const t₀ x₀).prodMk (hasFDerivAt_id x₀)
    exact (hL.comp x₀ hinr).fderiv
  have hslice_one : fderiv ℝ (fun y : ℝ => gE t₀ y) x₀ 1 =
      fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t₀, x₀) (0, 1) := by
    rw [hslice]
    simp [ContinuousLinearMap.prod_apply]
  have heq : (fun y : ℝ => gE t₀ y) =ᶠ[𝓝 x₀]
      (fun y : ℝ => extChartAt I (γ t₀ (x₀ : Surgery.Topology.Circle))
        (γ t₀ (y : Surgery.Topology.Circle))) := by
    filter_upwards [hWn] with y hy
    exact (hag (t₀, y) hy ht₀).2
  have hsrc : ∀ᶠ r : ℝ in 𝓝 x₀,
      γ t₀ (r : Surgery.Topology.Circle)
        ∈ (chartAt H (γ t₀ (x₀ : Surgery.Topology.Circle))).source := by
    filter_upwards [hWn] with y hy
    exact (hag (t₀, y) hy ht₀).1
  have hd : MDifferentiableAt 𝓘(ℝ, ℝ) I
      (fun y : ℝ => γ t₀ (y : Surgery.Topology.Circle)) x₀ :=
    ((curveOfLoopFamily γ).smooth_slice hγ ht₀).mdifferentiableAt (by simp)
  have hval : fderiv ℝ (fun y : ℝ => gE t₀ y) x₀ 1 =
      trivToE (I := I) (γ t₀ (x₀ : Surgery.Topology.Circle))
        (γ t₀ (x₀ : Surgery.Topology.Circle)) ((curveOfLoopFamily γ).X x₀ t₀) := by
    rw [heq.fderiv_eq]
    exact fderiv_chartReading_eq (I := I)
      (c := fun y : ℝ => γ t₀ (y : Surgery.Topology.Circle))
      (γ t₀ (x₀ : Surgery.Topology.Circle)) x₀ (mem_chart_source H _) hsrc hd
  have hbase : γ t₀ (x₀ : Surgery.Topology.Circle) ∈
      (trivializationAt E (TangentSpace I) (γ t₀ (x₀ : Surgery.Topology.Circle))).baseSet :=
    by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H _
  have hne : fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t₀, x₀) (0, 1) ≠ 0 := by
    rw [← hslice_one, hval]
    intro h0
    have h1 := trivFromE_trivToE (I := I) (γ t₀ (x₀ : Surgery.Topology.Circle)) hbase
      ((curveOfLoopFamily γ).X x₀ t₀)
    rw [h0, map_zero] at h1
    exact hi x₀ t₀ ht₀ h1.symm
  rw [hD]
  intro u v huv
  have hfst : u.1 = v.1 := by
    simpa [ContinuousLinearMap.prod_apply] using congrArg Prod.fst huv
  have hsnd : fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t₀, x₀) u =
      fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t₀, x₀) v := by
    simpa [ContinuousLinearMap.prod_apply] using congrArg Prod.snd huv
  have hdif : fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t₀, x₀) (u - v) = 0 := by
    rw [map_sub, hsnd, sub_self]
  have hunit : u - v = (u.2 - v.2) • (0, 1) := by
    ext <;> simp [hfst]
  have hsec :
      (u.2 - v.2) • fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t₀, x₀) (0, 1) = 0 := by
    rw [← map_smul, ← hunit]
    exact hdif
  have h2eq : u.2 = v.2 := by
    rcases smul_eq_zero.mp hsec with h | h
    · linarith
    · exact absurd h hne
  exact Prod.ext hfst h2eq

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_chartReading_of_contMDiffOn {F : ℝ × ℝ → M} {U : Set (ℝ × ℝ)}
    {α : M} (hF : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ F U)
    (hsrc : ∀ p ∈ U, F p ∈ (chartAt H α).source) :
    ContDiffOn ℝ ∞ (fun p => extChartAt I α (F p)) U := by
  rw [← contMDiffOn_iff_contDiffOn]
  intro p hp
  exact (contMDiffOn_extChartAt (I := I) (n := ∞) (x := α) (F p) (hsrc p hp)).comp p
    (hF p hp) fun q hq => hsrc q hq

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

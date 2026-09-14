import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.VelocityExtensionChartLocal
import DifferentialGeometry.Analysis.Calculus.Inverse.SmoothLocalInverse

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] in
theorem exists_isOpen_trace_lift_mem {a b t₀ x₀ : ℝ} {γ : ℝ → ContinuousFreeLoop M}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hinj : Injective (γ t₀)) {V : Set (ℝ × ℝ)} (hVo : IsOpen V) (hV : (t₀, x₀) ∈ V) :
    ∃ O : Set (ℝ × M), IsOpen O ∧ (t₀, γ t₀ (x₀ : Surgery.Topology.Circle)) ∈ O ∧
      ∀ t ∈ Icc a b, ∀ z : Surgery.Topology.Circle, (t, γ t z) ∈ O →
        ∃ y : ℝ, (y : Surgery.Topology.Circle) = z ∧ (t, y) ∈ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hVo.mem_nhds hV)
  set r : ℝ := ε / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hbox : Ioo (t₀ - r) (t₀ + r) ×ˢ Ioo (x₀ - r) (x₀ + r) ⊆ V := by
    intro p hp
    refine hball ?_
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    refine max_lt ?_ ?_
    · have h1 : |p.1 - t₀| < r :=
        abs_sub_lt_iff.mpr ⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩
      rw [hrdef] at h1
      linarith
    · have h2 : |p.2 - x₀| < r :=
        abs_sub_lt_iff.mpr ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩
      rw [hrdef] at h2
      linarith
  set A : Set Surgery.Topology.Circle :=
    (fun y : ℝ => (y : Surgery.Topology.Circle)) '' Ioo (x₀ - r) (x₀ + r) with hAdef
  have hAo : IsOpen A := by
    rw [hAdef]
    exact QuotientAddGroup.isOpenMap_coe (Ioo (x₀ - r) (x₀ + r)) isOpen_Ioo
  have hAc : IsClosed Aᶜ := hAo.isClosed_compl
  have hcoe : Continuous (fun y : ℝ => (y : Surgery.Topology.Circle)) :=
    AddCircle.continuous_mk' (1 : ℝ)
  set K : Set ℝ :=
    Icc (x₀ - 1) x₀ ∩ (fun y : ℝ => (y : Surgery.Topology.Circle)) ⁻¹' Aᶜ with hKdef
  have hKc : IsCompact K := by
    rw [hKdef]
    exact isCompact_Icc.inter_right (hAc.preimage hcoe)
  have hrepr : ∀ z : Surgery.Topology.Circle,
      ∃ y : ℝ, y ∈ Icc (x₀ - 1) x₀ ∧ (y : Surgery.Topology.Circle) = z := by
    intro z
    have h : z ∈ (QuotientAddGroup.mk '' Icc (x₀ - 1) ((x₀ - 1) + 1) :
        Set Surgery.Topology.Circle) := by
      rw [AddCircle.coe_image_Icc_eq (1 : ℝ) (x₀ - 1)]
      exact mem_univ z
    rw [show (x₀ - 1) + 1 = x₀ from by ring] at h
    exact h
  set Φ : ℝ × ℝ → ℝ × M := fun p => (p.2, γ p.2 (p.1 : Surgery.Topology.Circle))
    with hΦdef
  have hΦcont : ContinuousOn Φ (univ ×ˢ Icc a b) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => p.2) (univ ×ˢ Icc a b) := continuousOn_snd
    have h2 : ContinuousOn (fun p : ℝ × ℝ => γ p.2 (p.1 : Surgery.Topology.Circle))
        (univ ×ˢ Icc a b) := hγ.continuousOn
    simpa only [hΦdef] using h1.prodMk h2
  set F : Set (ℝ × M) := Φ '' (K ×ˢ Icc a b) with hFdef
  have hFc : IsCompact F := by
    rw [hFdef]
    exact (hKc.prod isCompact_Icc).image_of_continuousOn
      (hΦcont.mono fun p hp => ⟨trivial, hp.2⟩)
  have hFcl : IsClosed F := hFc.isClosed
  have hnot : (t₀, γ t₀ (x₀ : Surgery.Topology.Circle)) ∉ F := by
    rintro ⟨p, hp, hpe⟩
    have hpt : p.2 = t₀ := by
      have h := congrArg Prod.fst hpe
      simpa only [hΦdef] using h
    have hps : γ p.2 (p.1 : Surgery.Topology.Circle) =
        γ t₀ (x₀ : Surgery.Topology.Circle) := by
      have h := congrArg Prod.snd hpe
      simpa only [hΦdef] using h
    have hps' : γ t₀ (p.1 : Surgery.Topology.Circle) =
        γ t₀ (x₀ : Surgery.Topology.Circle) := by
      rw [hpt] at hps
      exact hps
    have heq : (p.1 : Surgery.Topology.Circle) = (x₀ : Surgery.Topology.Circle) :=
      hinj hps'
    have hmem : (p.1 : Surgery.Topology.Circle) ∈ A := by
      rw [heq]
      exact ⟨x₀, ⟨by linarith, by linarith⟩, rfl⟩
    exact hp.1.2 hmem
  refine ⟨(Ioo (t₀ - r) (t₀ + r) ×ˢ univ) ∩ Fᶜ, ?_, ?_, ?_⟩
  · exact (isOpen_Ioo.prod isOpen_univ).inter hFcl.isOpen_compl
  · exact ⟨⟨⟨by linarith, by linarith⟩, trivial⟩, hnot⟩
  · intro t ht z hz
    have htI : t ∈ Ioo (t₀ - r) (t₀ + r) := hz.1.1
    have hzF : (t, γ t z) ∉ F := hz.2
    have hzA : z ∈ A := by
      by_contra hznot
      obtain ⟨y, hy, hyz⟩ := hrepr z
      have hyK : y ∈ K := by
        rw [hKdef]
        refine ⟨hy, ?_⟩
        change (y : Surgery.Topology.Circle) ∉ A
        rw [hyz]
        exact hznot
      have hmem : Φ (y, t) ∈ F := by
        rw [hFdef]
        exact ⟨(y, t), ⟨hyK, ht⟩, rfl⟩
      exact hzF (by simpa only [hΦdef, hyz] using hmem)
    obtain ⟨y, hy, hyz⟩ := hzA
    exact ⟨y, hyz, hbox ⟨htI, hy⟩⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in
def LoopFamilyVelocityExtensionChartReading (γ : ℝ → ContinuousFreeLoop M)
    (a b t₀ x₀ : ℝ) : Prop :=
  ∃ (gE : ℝ → ℝ → E) (W : Set (ℝ × ℝ)),
    IsOpen W ∧ (t₀, x₀) ∈ W ∧
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => gE p.1 p.2) W ∧
    ∀ p ∈ W, p.1 ∈ Icc a b →
      γ p.1 (p.2 : Surgery.Topology.Circle)
          ∈ (chartAt H (γ t₀ (x₀ : Surgery.Topology.Circle))).source ∧
        gE p.1 p.2 = extChartAt I (γ t₀ (x₀ : Surgery.Topology.Circle))
          (γ p.1 (p.2 : Surgery.Topology.Circle))

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
private theorem hasMFDerivWithinAt_trace_of_chartReading {a b t₀ x₀ t y : ℝ}
    {γ : ℝ → ContinuousFreeLoop M} {z : Surgery.Topology.Circle} {S : Set ℝ}
    {gE : ℝ → ℝ → E} {W : Set (ℝ × ℝ)}
    (hwo : IsOpen W) (hsm : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => gE p.1 p.2) W)
    (hag : ∀ p ∈ W, p.1 ∈ Icc a b →
      γ p.1 (p.2 : Surgery.Topology.Circle)
          ∈ (chartAt H (γ t₀ (x₀ : Surgery.Topology.Circle))).source ∧
        gE p.1 p.2 = extChartAt I (γ t₀ (x₀ : Surgery.Topology.Circle))
          (γ p.1 (p.2 : Surgery.Topology.Circle)))
    (ht : t ∈ Icc a b) (hyW : (t, y) ∈ W) (hyz : (y : Surgery.Topology.Circle) = z)
    (hSicc : Icc a b ∈ 𝓝[S] t) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ s z) S t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (trivFromE (I := I) (γ t₀ (x₀ : Surgery.Topology.Circle))
        (γ t z) (fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t, y) (1, 0)))) := by
  set T : Set ℝ := Icc a b ∩ {s : ℝ | (s, y) ∈ W} with hTdef
  have hslice : {s : ℝ | (s, y) ∈ W} ∈ 𝓝 t := by
    have hc : Continuous fun s : ℝ => (s, y) := continuous_id.prodMk continuous_const
    exact hc.continuousAt.preimage_mem_nhds (hwo.mem_nhds hyW)
  have hTmem : T ∈ 𝓝[S] t :=
    Filter.inter_mem hSicc (nhdsWithin_le_nhds hslice)
  have htT : t ∈ T := ⟨ht, hyW⟩
  have hD : HasFDerivAt (fun p : ℝ × ℝ => gE p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t, y)) (t, y) :=
    ((hsm.contDiffAt (hwo.mem_nhds hyW)).differentiableAt (by simp)).hasFDerivAt
  have hinl : HasFDerivAt (fun s : ℝ => (s, y))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)) t :=
    (hasFDerivAt_id t).prodMk (hasFDerivAt_const y t)
  have hcomp : HasFDerivAt ((fun p : ℝ × ℝ => gE p.1 p.2) ∘ fun s : ℝ => (s, y))
      ((fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t, y)).comp
        ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ))) t :=
    HasFDerivAt.comp (x := t) hD hinl
  have hEqOn : Set.EqOn (fun s : ℝ => gE s y)
      (fun s : ℝ => extChartAt I (γ t₀ (x₀ : Surgery.Topology.Circle)) (γ s z)) T := by
    intro s hs
    obtain ⟨hsI, hsW⟩ := hs
    simpa only [hyz] using (hag (s, y) hsW hsI).2
  have hF : HasFDerivWithinAt
      (fun s : ℝ => extChartAt I (γ t₀ (x₀ : Surgery.Topology.Circle)) (γ s z))
      ((fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t, y)).comp
        ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ))) T t :=
    (hcomp.hasFDerivWithinAt).congr_of_eventuallyEq
      (Filter.eventually_of_mem self_mem_nhdsWithin hEqOn.symm) (hEqOn htT).symm
  have hsrc : ∀ s ∈ T,
      γ s z ∈ (chartAt H (γ t₀ (x₀ : Surgery.Topology.Circle))).source := by
    intro s hs
    obtain ⟨hsI, hsW⟩ := hs
    rw [← hyz]
    exact (hag (s, y) hsW hsI).1
  have hb := hasMFDerivWithinAt_of_hasFDerivWithinAt_chartReading (I := I) htT hsrc hF
  have hL1 : (((fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t, y)).comp
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ))) (1 : ℝ)) =
      fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t, y) (1, 0) := by
    simp [ContinuousLinearMap.prod_apply]
  rw [hL1] at hb
  exact hb.mono_of_mem_nhdsWithin hTmem

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in
private theorem Icc_mem_nhdsWithin_Ici {a b t : ℝ} (ht : t ∈ Ico a b) :
    Icc a b ∈ 𝓝[Ici t] t :=
  mem_nhdsWithin.mpr
    ⟨Iio b, isOpen_Iio, ht.2, fun x hx =>
      show x ∈ Icc a b from ⟨le_trans ht.1 hx.2, le_of_lt hx.1⟩⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in
private theorem Icc_mem_nhdsWithin_Iic {a b t : ℝ} (ht : t ∈ Ioc a b) :
    Icc a b ∈ 𝓝[Iic t] t :=
  mem_nhdsWithin.mpr
    ⟨Ioi a, isOpen_Ioi, ht.1, fun x hx =>
      show x ∈ Icc a b from ⟨le_of_lt hx.1, le_trans hx.2 ht.2⟩⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in
private theorem trace_apply_leftInverse {t₀ x₀ t y : ℝ} {γ : ℝ → ContinuousFreeLoop M}
    {z : Surgery.Topology.Circle} {gE : ℝ → ℝ → E} {V : Set (ℝ × ℝ)}
    {r : ℝ × E → ℝ × ℝ}
    (hleft : ∀ y' ∈ V, r (y'.1, gE y'.1 y'.2) = y') (hyV : (t, y) ∈ V)
    (he : gE t y = extChartAt I (γ t₀ (x₀ : Surgery.Topology.Circle)) (γ t z)) :
    r (t, extChartAt I (γ t₀ (x₀ : Surgery.Topology.Circle)) (γ t z)) = (t, y) := by
  have h2 : ((t, y).1, gE (t, y).1 (t, y).2) =
      (t, extChartAt I (γ t₀ (x₀ : Surgery.Topology.Circle)) (γ t z)) := by
    change (t, gE t y) = (t, extChartAt I (γ t₀ (x₀ : Surgery.Topology.Circle)) (γ t z))
    rw [he]
  rw [← h2]
  exact hleft (t, y) hyV

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
private theorem traceVelocity_eq {t₀ x₀ t y : ℝ} {γ : ℝ → ContinuousFreeLoop M}
    {z : Surgery.Topology.Circle} {gE : ℝ → ℝ → E} {V : Set (ℝ × ℝ)}
    {r : ℝ × E → ℝ × ℝ}
    (hleft : ∀ y' ∈ V, r (y'.1, gE y'.1 y'.2) = y') (hyV : (t, y) ∈ V)
    (he : gE t y = extChartAt I (γ t₀ (x₀ : Surgery.Topology.Circle)) (γ t z)) :
    (trivFromE (I := I) (γ t₀ (x₀ : Surgery.Topology.Circle)) (γ t z))
        (fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2)
          (r (t, extChartAt I (γ t₀ (x₀ : Surgery.Topology.Circle)) (γ t z))) (1, 0)) =
      (trivFromE (I := I) (γ t₀ (x₀ : Surgery.Topology.Circle)) (γ t z))
        (fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t, y) (1, 0)) := by
  rw [trace_apply_leftInverse (I := I) hleft hyV he]

omit [SigmaCompactSpace M] in
theorem loopFamilyVelocityExtensionLocalAt_of_chartReading {a b t₀ x₀ : ℝ}
    {γ : ℝ → ContinuousFreeLoop M}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hinj : Injective (γ t₀)) (ht₀ : t₀ ∈ Icc a b)
    (hread : LoopFamilyVelocityExtensionChartReading (I := I) γ a b t₀ x₀) :
    LoopFamilyVelocityExtensionLocalAt (I := I) γ a b
      (t₀, γ t₀ (x₀ : Surgery.Topology.Circle)) := by
  classical
  obtain ⟨gE, W, hWo, hW₀, hsm, hag⟩ := hread
  set α : M := γ t₀ (x₀ : Surgery.Topology.Circle) with hα
  obtain ⟨r, U, V, hUo, hfxU, hVo, hV₀, hVW, hr, hleft, hleft₀⟩ :=
    exists_smooth_local_leftInverse (f := fun p : ℝ × ℝ => (p.1, gE p.1 p.2))
      hWo (contDiffOn_fst.prodMk hsm) hW₀
      (injective_fderiv_chartGraph (I := I) hγ hi ht₀ rfl hWo hW₀ hsm hag)
  obtain ⟨O₀, hO₀o, hO₀mem, hO₀tr⟩ :=
    exists_isOpen_trace_lift_mem (I := I) hγ hinj hVo hV₀
  set U' : Set (ℝ × E) := {q | q ∈ U ∧ r q ∈ W} with hU'def
  have hU'o : IsOpen U' := by
    rw [hU'def]
    exact hr.continuousOn.isOpen_inter_preimage hUo hWo
  have hDsm : ContDiffOn ℝ ∞
      (fun q : ℝ × E => fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (r q)) U' :=
    (hsm.fderiv_of_isOpen hWo (by simp)).comp (hr.mono fun q hq => hq.1)
      fun q hq => hq.2
  have hgl : ContDiffOn ℝ ∞
      (fun q : ℝ × E => fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (r q) (1, 0)) U' :=
    hDsm.clm_apply (contDiffOn_const :
      ContDiffOn ℝ ∞ (fun _ : ℝ × E => ((1 : ℝ), (0 : ℝ))) U')
  let X : ℝ → (p : M) → TangentSpace I p := fun t x =>
    (trivFromE (I := I) α x)
      (fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (r (t, extChartAt I α x)) (1, 0))
  have hXs : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      {q : ℝ × M | q.2 ∈ (chartAt H α).source ∧ (q.1, extChartAt I α q.2) ∈ U'} :=
    contMDiffOn_lift_trivFromE_reading (I := I) α
      (fun t w => fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (r (t, w)) (1, 0)) U' hgl
  have hO₁o : IsOpen {q : ℝ × M | q.2 ∈ (chartAt H α).source ∧
      (q.1, extChartAt I α q.2) ∈ U'} := by
    have hext : ContinuousOn (fun q : ℝ × M => extChartAt I α q.2)
        {q : ℝ × M | q.2 ∈ (chartAt H α).source} :=
      ContinuousOn.comp (continuousOn_extChartAt (I := I) α) continuousOn_snd
        (fun q hq => by rw [extChartAt_source]; exact hq)
    have hcont : ContinuousOn (fun q : ℝ × M => (q.1, extChartAt I α q.2))
        {q : ℝ × M | q.2 ∈ (chartAt H α).source} :=
      continuousOn_fst.prodMk hext
    have hsrc : IsOpen {q : ℝ × M | q.2 ∈ (chartAt H α).source} :=
      (chartAt H α).open_source.preimage continuous_snd
    have h := hcont.isOpen_inter_preimage hsrc hU'o
    convert h using 1
    ext q
    rfl
  set O : Set (ℝ × M) := O₀ ∩ {q : ℝ × M | q.2 ∈ (chartAt H α).source ∧
      (q.1, extChartAt I α q.2) ∈ U'} with hOdef
  have hOo : IsOpen O := by
    rw [hOdef]
    exact hO₀o.inter hO₁o
  have hU₀ : (t₀, extChartAt I α α) ∈ U' := by
    have hg₀ := hag (t₀, x₀) hW₀ ht₀
    have h1 : (t₀, extChartAt I α α) =
        (fun p : ℝ × ℝ => (p.1, gE p.1 p.2)) (t₀, x₀) := by
      change _ = (t₀, gE t₀ x₀)
      rw [hg₀.2]
    rw [hU'def]
    exact ⟨by rw [h1]; exact hfxU, by rw [h1, hleft₀]; exact hVW hV₀⟩
  have hOmem : (t₀, α) ∈ O := by
    rw [hOdef]
    exact ⟨hO₀mem, mem_chart_source H α, hU₀⟩
  have hvel : LoopFamilyVelocityExtensionOn (I := I) γ a b O X := by
    refine ⟨?_, ?_⟩
    · intro t ht z hz
      have htI : t ∈ Icc a b := ⟨ht.1, le_of_lt ht.2⟩
      obtain ⟨y, hyz, hyV⟩ := hO₀tr t htI z hz.1
      have hyW : (t, y) ∈ W := hVW hyV
      have he : gE t y = extChartAt I α (γ t z) := by
        simpa only [hyz] using (hag (t, y) hyW htI).2
      have hgoal := hasMFDerivWithinAt_trace_of_chartReading (I := I) (S := Ici t)
        hWo hsm hag htI hyW hyz (Icc_mem_nhdsWithin_Ici ht)
      have hXval : X t (γ t z) = trivFromE (I := I) α (γ t z)
          (fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t, y) (1, 0)) :=
        traceVelocity_eq (I := I) hleft hyV he
      rw [hXval]
      exact hgoal
    · intro t ht z hz
      have htI : t ∈ Icc a b := ⟨le_of_lt ht.1, ht.2⟩
      obtain ⟨y, hyz, hyV⟩ := hO₀tr t htI z hz.1
      have hyW : (t, y) ∈ W := hVW hyV
      have he : gE t y = extChartAt I α (γ t z) := by
        simpa only [hyz] using (hag (t, y) hyW htI).2
      have hgoal := hasMFDerivWithinAt_trace_of_chartReading (I := I) (S := Iic t)
        hWo hsm hag htI hyW hyz (Icc_mem_nhdsWithin_Iic ht)
      have hXval : X t (γ t z) = trivFromE (I := I) α (γ t z)
          (fderiv ℝ (fun p : ℝ × ℝ => gE p.1 p.2) (t, y) (1, 0)) :=
        traceVelocity_eq (I := I) hleft hyV he
      rw [hXval]
      exact hgoal
  exact ⟨X, O, hOo, hOmem, hXs.mono fun q hq => hq.2, hvel⟩

omit [SigmaCompactSpace M] in
theorem loopFamilyVelocityExtensionLocalCover_of_chartReading {a b : ℝ}
    {γ : ℝ → ContinuousFreeLoop M}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (γ t))
    (h : ∀ t ∈ Icc a b, ∀ x : ℝ,
      LoopFamilyVelocityExtensionChartReading (I := I) γ a b t x) :
    LoopFamilyVelocityExtensionLocalCover (I := I) γ a b :=
  fun t ht x =>
    loopFamilyVelocityExtensionLocalAt_of_chartReading (I := I) hγ hi
      (hemb t ht).injective ht (h t ht x)

theorem loopFamilyVelocityExtension_of_chartReading {a b : ℝ}
    {γ : ℝ → ContinuousFreeLoop M}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (γ t))
    (h : ∀ t ∈ Icc a b, ∀ x : ℝ,
      LoopFamilyVelocityExtensionChartReading (I := I) γ a b t x) :
    LoopFamilyVelocityExtension (I := I) a b γ :=
  loopFamilyVelocityExtension_of_localCover (I := I) hγ
    (loopFamilyVelocityExtensionLocalCover_of_chartReading (I := I) hγ hi hemb h)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem chartReading_constLoopFamily {a b t₀ x₀ : ℝ} (m : M) :
    LoopFamilyVelocityExtensionChartReading (I := I)
      (fun _ : ℝ => constantLoops m) a b t₀ x₀ := by
  refine ⟨fun _ _ => extChartAt I ((constantLoops m) (x₀ : Surgery.Topology.Circle)) m,
    univ, isOpen_univ, mem_univ _, contDiffOn_const, ?_⟩
  intro p _ _
  exact ⟨mem_chart_source H _, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

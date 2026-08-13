import DifferentialGeometry.Geometry.Exponential.GaussLemma
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Geodesic.Homogeneity
import DifferentialGeometry.Geometry.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Geodesic.ProjDerivative
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.ZeroSectionConstancy
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz
import DifferentialGeometry.Geometry.Comparison.GeodesicSpeedBound
import DifferentialGeometry.Geometry.Comparison.ChartVelocityConvergence
import DifferentialGeometry.Geometry.Comparison.LocalGeodesicSeed
import DifferentialGeometry.Geometry.Comparison.EndpointContinuation
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace HopfRinow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

section GeodesicCompleteness

open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Integral.DivergenceTheorem

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

omit [T2Space M] [SigmaCompactSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesicOn_Iio_extend
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {b : ℝ}
    (hγ : IsGeodesicOn (I := I) g γ (Set.Iio b))
    (hcont : HasEndpointContinuation (I := I) g γ b) :
    ∃ (γ' : ℝ → M) (b' : ℝ), b < b' ∧
      IsGeodesicOn (I := I) g γ' (Set.Iio b') ∧
      (∀ t < b, γ' t = γ t) := by
  obtain ⟨η, δ, hδ, hη, _hη_mdiff, hmatch⟩ := hcont
  obtain ⟨γ', hgeo', hagree⟩ :=
    isGeodesicOn_extends_past_finite_endpoint (I := I) g hδ hγ hη hmatch
  exact ⟨γ', b + δ, by linarith, hgeo', hagree⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
 [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M] in
private theorem hasGeodesicEquationAt_congr_of_eventuallyEq
    {g : SmoothRiemannianMetric I M} {γ γ' : ℝ → M} {t : ℝ}
    (heq : γ =ᶠ[nhds t] γ') (h : HasGeodesicEquationAt (I := I) g γ' t) :
    HasGeodesicEquationAt (I := I) g γ t := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at (I := I) (g := g)
    (heq.eq_of_nhds) heq h

omit [T2Space M] [SigmaCompactSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesicOn_Ici_of_endpointContinuation
    (g : SmoothRiemannianMetric I M) {γ₀ : ℝ → M} {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hγ₀ : IsGeodesicOn (I := I) g γ₀ (Set.Iio b₀))
    (hcont : ∀ (γ : ℝ → M) (b : ℝ), 0 < b →
      IsGeodesicOn (I := I) g γ (Set.Iio b) →
      (∀ t < b₀, t < b → γ t = γ₀ t) →
      HasEndpointContinuation (I := I) g γ b) :
    ∃ γ : ℝ → M,
      IsGeodesicOn (I := I) g γ (Set.Ici (0 : ℝ)) ∧
      (∀ t, t < b₀ → γ t = γ₀ t) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Good : (ℝ × (ℝ → M)) → Prop := fun br =>
    b₀ ≤ br.1 ∧ IsGeodesicOn (I := I) g br.2 (Set.Iio br.1) ∧
      (∀ t < b₀, br.2 t = γ₀ t)
  let Rec := {br : ℝ × (ℝ → M) // Good br}
  let R : Rec → Rec → Prop := fun a a' =>
    a.1.1 ≤ a'.1.1 ∧ (∀ t < a.1.1, a'.1.2 t = a.1.2 t)
  have hGood_r₀ : Good (b₀, γ₀) := ⟨le_refl _, hγ₀, fun t _ => rfl⟩
  let r₀ : Rec := ⟨(b₀, γ₀), hGood_r₀⟩
  have hchain0 : IsChain R {r₀} := by
    intro a ha b hb hab
    rw [Set.mem_singleton_iff] at ha hb; exact absurd (ha.trans hb.symm) hab
  obtain ⟨Mc, hMc_max, hMc_sub⟩ := hchain0.exists_maxChain
  have hr₀_mem : r₀ ∈ Mc := hMc_sub (Set.mem_singleton _)
  have hMc_chain : IsChain R Mc := hMc_max.1
  have hconsist : ∀ a ∈ Mc, ∀ a' ∈ Mc, ∀ t, t < a.1.1 → t < a'.1.1 →
      a.1.2 t = a'.1.2 t := by
    intro a ha a' ha' t hta hta'
    rcases eq_or_ne a a' with rfl | hne
    · rfl
    · rcases hMc_chain ha ha' hne with hR | hR
      · exact (hR.2 t hta).symm
      · exact hR.2 t hta'
  let Γ : ℝ → M := fun t =>
    if h : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 then (h.choose.1.2 t) else γ₀ t
  have hΓ_val : ∀ a ∈ Mc, ∀ t, t < a.1.1 → Γ t = a.1.2 t := by
    intro a ha t hta
    have hex : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 := ⟨a, ha, hta⟩
    change (if h : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 then (h.choose.1.2 t)
      else γ₀ t) = a.1.2 t
    rw [dif_pos hex]
    obtain ⟨hb_mem, hb_lt⟩ := hex.choose_spec
    exact hconsist _ hb_mem a ha t hb_lt hta
  have hΓ_agree : ∀ t, t < b₀ → Γ t = γ₀ t := by
    intro t ht
    have := hΓ_val r₀ hr₀_mem t ht
    simpa [r₀] using this
  have hΓ_geo_at : ∀ a ∈ Mc, ∀ t, t < a.1.1 →
      HasGeodesicEquationAt (I := I) g Γ t := by
    intro a ha t hta
    have hIio_nhds : Set.Iio a.1.1 ∈ 𝓝 t := isOpen_Iio.mem_nhds hta
    have heq : Γ =ᶠ[𝓝 t] a.1.2 := by
      filter_upwards [hIio_nhds] with s hs
      exact hΓ_val a ha s hs
    exact hasGeodesicEquationAt_congr_of_eventuallyEq (g := g) heq (a.2.2.1 t hta)
  let S : Set ℝ := (fun a : Rec => a.1.1) '' Mc
  have hS_ne : S.Nonempty := ⟨b₀, ⟨r₀, hr₀_mem, rfl⟩⟩
  by_cases hbdd : BddAbove S
  · exfalso
    let s := sSup S
    have hb₀_le_s : b₀ ≤ s := le_csSup hbdd ⟨r₀, hr₀_mem, rfl⟩
    have hs_pos : 0 < s := lt_of_lt_of_le hb₀ hb₀_le_s
    have hΓ_geo_Iios : IsGeodesicOn (I := I) g Γ (Set.Iio s) := by
      intro t ht
      obtain ⟨b, hbS, htb⟩ := exists_lt_of_lt_csSup hS_ne ht
      obtain ⟨a, ha, hab⟩ := hbS
      exact hΓ_geo_at a ha t (lt_of_lt_of_eq htb hab.symm)
    have hagree_s : ∀ t < b₀, t < s → Γ t = γ₀ t := fun t ht _ => hΓ_agree t ht
    have hcont_s : HasEndpointContinuation (I := I) g Γ s :=
      hcont Γ s hs_pos hΓ_geo_Iios hagree_s
    obtain ⟨Γ', s', hss', hΓ'_geo, hΓ'_agree⟩ :=
      isGeodesicOn_Iio_extend (I := I) g hΓ_geo_Iios hcont_s
    have hGood' : Good (s', Γ') := by
      refine ⟨le_trans hb₀_le_s hss'.le, hΓ'_geo, ?_⟩
      intro t ht
      have ht_s : t < s := lt_of_lt_of_le ht hb₀_le_s
      change Γ' t = γ₀ t
      rw [hΓ'_agree t ht_s]; exact hΓ_agree t ht
    let r' : Rec := ⟨(s', Γ'), hGood'⟩
    have hr'_notMem : r' ∉ Mc := by
      intro hmem
      have hmemS : s' ∈ S := ⟨r', hmem, rfl⟩
      exact absurd (le_csSup hbdd hmemS) (not_le.mpr hss')
    have hchain' : IsChain R (insert r' Mc) := by
      refine hMc_chain.insert ?_
      intro a ha _
      right
      have ha_mem_S : a.1.1 ∈ S := ⟨a, ha, rfl⟩
      have ha_le_s : a.1.1 ≤ s := le_csSup hbdd ha_mem_S
      refine ⟨?_, ?_⟩
      · change a.1.1 ≤ s'
        exact le_trans ha_le_s hss'.le
      · intro t hta
        have ht_s : t < s := lt_of_lt_of_le hta ha_le_s
        change Γ' t = a.1.2 t
        rw [hΓ'_agree t ht_s]; exact hΓ_val a ha t hta
    have heq_chain : Mc = insert r' Mc :=
      hMc_max.2 hchain' (Set.subset_insert _ _)
    exact hr'_notMem (heq_chain ▸ Set.mem_insert _ _)
  · refine ⟨Γ, ?_, hΓ_agree⟩
    intro t _
    rw [not_bddAbove_iff] at hbdd
    obtain ⟨b, hbS, htb⟩ := hbdd t
    obtain ⟨a, ha, hab⟩ := hbS
    exact hΓ_geo_at a ha t (lt_of_lt_of_eq htb hab.symm)

omit [T2Space M] [SigmaCompactSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M] in
theorem chartCurve_contDiffAt_one_of_isGeodesicOn
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hs : IsOpen s) (ht : t ∈ s)
    (hγ : IsGeodesicOn (I := I) g γ s) (hcont : ContinuousOn γ s) :
    ContDiffAt ℝ 1 (chartCurve (I := I) (γ t) γ) t := by
  classical
  set α : M := γ t with hα_def
  set u : ℝ → E := chartCurve (I := I) α γ with hu_def
  have hα_src : α ∈ (chartAt H α).source := mem_chart_source H α
  have hcontAt_t : ContinuousAt γ t :=
    hcont.continuousAt (hs.mem_nhds ht)
  have hsrc_nhds : (fun s' => γ s') ⁻¹' (chartAt H α).source ∈ 𝓝 t := by
    have : α ∈ (chartAt H α).source := hα_src
    exact hcontAt_t.preimage_mem_nhds
      ((chartAt H α).open_source.mem_nhds (by rw [hα_def] at this ⊢; exact this))
  obtain ⟨V, hV_nhds, hV_src⟩ := Filter.eventually_iff_exists_mem.mp
    (Filter.eventually_of_mem hsrc_nhds (fun _ h => h))
  set W : Set ℝ := V ∩ s with hW_def
  have hW_nhds : W ∈ 𝓝 t := Filter.inter_mem hV_nhds (hs.mem_nhds ht)
  have hW_src : ∀ s' ∈ W, γ s' ∈ (chartAt H α).source := fun s' hs' => hV_src s' hs'.1
  have hW_geo : ∀ s' ∈ W, HasGeodesicEquationAt (I := I) g γ s' :=
    fun s' hs' => hγ s' hs'.2
  have hW_contAt : ∀ s' ∈ W, ContinuousAt γ s' :=
    fun s' hs' => hcont.continuousAt (hs.mem_nhds hs'.2)
  have hODE : ∀ s' ∈ W,
      HasDerivAt (deriv u)
        (- chartChristoffelContraction (I := I) g α (deriv u s') (deriv u s') (u s')) s' := by
    intro s' hs'
    simpa [hu_def] using
      hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity (I := I) g α
        (γ := γ) (t := s') (hW_contAt s' hs') (hW_src s' hs') (hW_geo s' hs')
  obtain ⟨W', hW'_sub, hW'_open, hW'_mem⟩ := mem_nhds_iff.mp hW_nhds
  have hderiv_diffOn : ∀ s' ∈ W', DifferentiableAt ℝ (deriv u) s' :=
    fun s' hs' => (hODE s' (hW'_sub hs')).differentiableAt
  have hderiv_contOn : ContinuousOn (deriv u) W' :=
    fun s' hs' => (hderiv_diffOn s' hs').continuousAt.continuousWithinAt
  rw [contDiffAt_one_iff]
  refine ⟨fun s' => ContinuousLinearMap.toSpanSingleton ℝ (deriv u s'), W',
    hW'_open.mem_nhds hW'_mem, ?_, ?_⟩
  · have hCLE : Continuous
        (fun w : E => (ContinuousLinearMap.toSpanSingleton ℝ w : ℝ →L[ℝ] E)) :=
      ContinuousLinearMap.toSpanSingletonCLE.continuous
    exact hCLE.comp_continuousOn hderiv_contOn
  · intro s' hs'
    have hcont_s' : ContinuousAt γ s' := hW_contAt s' (hW'_sub hs')
    have hsrc_s' : γ s' ∈ (chartAt H (γ t)).source := hW_src s' (hW'_sub hs')
    have hu_ev' : ∀ᶠ r in 𝓝 s', HasDerivAt u (deriv u r) r := by
      simpa [hu_def] using
        hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt (I := I) g α
          (γ := γ) (t := s') hcont_s' (by rw [hα_def]; exact hsrc_s')
          (hW_geo s' (hW'_sub hs'))
    exact hu_ev'.self_of_nhds.hasFDerivAt

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space M] [SigmaCompactSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M] in
theorem isGeodesicOn_contMDiffAt_one
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hs : IsOpen s) (ht : t ∈ s)
    (hγ : IsGeodesicOn (I := I) g γ s) (hcont : ContinuousOn γ s) :
    ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t := by
  classical
  set α : M := γ t with hα_def
  set u : ℝ → E := chartCurve (I := I) α γ with hu_def
  have hu_cd : ContDiffAt ℝ 1 u t :=
    chartCurve_contDiffAt_one_of_isGeodesicOn (I := I) g hs ht hγ hcont
  have hu_cmd : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 u t := hu_cd.contMDiffAt
  have hα_src : α ∈ (chartAt H α).source := mem_chart_source H α
  have hα_ext_src : α ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hα_src
  have hut_eq : u t = extChartAt I α α := by
    rw [hu_def, chartCurve_def, hα_def]
  have hut_target : u t ∈ (extChartAt I α).target := by
    rw [hut_eq]; exact (extChartAt I α).map_source hα_ext_src
  have htarget_nhds : (extChartAt I α).target ∈ 𝓝 (u t) := by
    have hut_int : u t ∈ interior (extChartAt I α).target := by
      rw [hut_eq]
      exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
        ((extChartAt I α).map_source hα_ext_src)
    exact mem_nhds_iff.mpr ⟨interior (extChartAt I α).target, interior_subset,
      isOpen_interior, hut_int⟩
  have hsymm_within : ContMDiffWithinAt 𝓘(ℝ, E) I 1
      (extChartAt I α).symm (extChartAt I α).target (u t) :=
    contMDiffWithinAt_extChartAt_symm_target (I := I) α hut_target
  have hsymm_at : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I α).symm (u t) :=
    hsymm_within.contMDiffAt htarget_nhds
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) I 1 ((extChartAt I α).symm ∘ u) t :=
    hsymm_at.comp t hu_cmd
  have hcontAt_t : ContinuousAt γ t := hcont.continuousAt (hs.mem_nhds ht)
  have hsrc_nhds : (fun s' => γ s') ⁻¹' (chartAt H α).source ∈ 𝓝 t :=
    hcontAt_t.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hα_src)
  have heq : ((extChartAt I α).symm ∘ u) =ᶠ[𝓝 t] γ := by
    filter_upwards [hsrc_nhds] with s' hs'
    have hs'_ext : γ s' ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hs'
    change (extChartAt I α).symm (u s') = γ s'
    rw [hu_def, chartCurve_def]
    exact (extChartAt I α).left_inv hs'_ext
  exact hcomp.congr_of_eventuallyEq heq.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space M] [SigmaCompactSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M] in
theorem isGeodesicOn_contMDiffOn_one
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ}
    (hs : IsOpen s)
    (hγ : IsGeodesicOn (I := I) g γ s) (hcont : ContinuousOn γ s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s := fun _t ht =>
  (isGeodesicOn_contMDiffAt_one (I := I) g hs ht hγ hcont).contMDiffWithinAt

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem isGeodesicOn_Ici_of_complete
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {γ₀ : ℝ → M} {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hγ₀ : IsGeodesicOn (I := I) g γ₀ (Set.Iio b₀))
    (hreg : ∀ (γ : ℝ → M) (b : ℝ), 0 < b →
      IsGeodesicOn (I := I) g γ (Set.Iio b) →
      (∀ t < b₀, t < b → γ t = γ₀ t) →
      ∃ c : ℝ, 0 ≤ c ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Iio b) ∧
        (∀ τ ∈ Set.Iio b,
          ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ ≤ ENNReal.ofReal c) ∧
        (∀ s ∈ Set.Iio b,
          (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
              (mfderiv 𝓘(ℝ, ℝ) I γ s 1) ≤ c ^ 2)) :
    ∃ γ : ℝ → M,
      IsGeodesicOn (I := I) g γ (Set.Ici (0 : ℝ)) ∧
      (∀ t, t < b₀ → γ t = γ₀ t) := by
  refine isGeodesicOn_Ici_of_endpointContinuation (I := I) g hb₀ hγ₀ ?_
  intro γ b hb hγ hagree
  obtain ⟨c, hc_nonneg, hγ_smooth, hSpeedBound, hSpeedSq⟩ := hreg γ b hb hγ hagree
  have hsub : Set.Ioo (b - 1) b ⊆ Set.Iio b := fun s hs => hs.2
  exact hasEndpointContinuation_of_complete (I := I) g (by linarith : b - 1 < b)
    hc_nonneg (hγ_smooth.mono hsub) (fun τ hτ => hSpeedBound τ (hsub hτ))
    (fun s hs => hSpeedSq s (hsub hs)) (hγ.mono hsub)

omit [T2Space M] [SigmaCompactSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesicOn_Ioo_extend
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a₀ b : ℝ} (ha₀b : a₀ < b)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Ioo a₀ b))
    (hγ_cont : ContinuousOn γ (Set.Ioo a₀ b))
    (hcont : HasEndpointContinuation (I := I) g γ b) :
    ∃ (γ' : ℝ → M) (b' : ℝ), b < b' ∧
      IsGeodesicOn (I := I) g γ' (Set.Ioo a₀ b') ∧
      ContinuousOn γ' (Set.Ioo a₀ b') ∧
      (∀ t < b, γ' t = γ t) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨η, δ, hδ, hη, hη_mdiff, hmatch⟩ := hcont
  set G : ℝ → M := fun t => if t < b then γ t else η (t - b) with hG_def
  have hη_cont : ContinuousOn η (Set.Ioo (-δ) δ) :=
    fun t ht => (hη_mdiff t ht).continuousAt.continuousWithinAt
  have hηb_cont : ContinuousOn (fun t => η (t - b)) (Set.Ioo (b - δ) (b + δ)) := by
    have hshift : ContinuousOn (fun t : ℝ => t - b) (Set.Ioo (b - δ) (b + δ)) :=
      (continuous_sub_right b).continuousOn
    have hmaps : Set.MapsTo (fun t : ℝ => t - b) (Set.Ioo (b - δ) (b + δ))
        (Set.Ioo (-δ) δ) := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact hη_cont.comp hshift hmaps
  have hG_cont : ContinuousOn G (Set.Ioo a₀ (b + δ)) := by
    intro t ht
    rcases lt_trichotomy t b with hlt | heq | hgt
    · have htγ : t ∈ Set.Ioo a₀ b := ⟨ht.1, hlt⟩
      have hGγ : G =ᶠ[𝓝[Set.Ioo a₀ (b + δ)] t] γ := by
        have hnhds : Set.Iio b ∈ 𝓝 t := isOpen_Iio.mem_nhds hlt
        filter_upwards [nhdsWithin_le_nhds hnhds] with s hs
        simp only [hG_def, if_pos (mem_Iio.mp hs)]
      have hγ_at : ContinuousWithinAt γ (Set.Ioo a₀ (b + δ)) t := by
        refine (hγ_cont t htγ).mono_of_mem_nhdsWithin ?_
        exact mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds htγ)
      refine hγ_at.congr_of_eventuallyEq hGγ ?_
      simp only [hG_def, if_pos hlt]
    · subst heq
      have hG_eq_ηb : G =ᶠ[𝓝[Set.Ioo a₀ (t + δ)] t] (fun s => η (s - t)) := by
        rw [eventuallyEq_nhdsWithin_iff]
        have hleft : ∀ᶠ s in 𝓝[<] t, G s = η (s - t) := by
          have hmatch' : γ =ᶠ[𝓝[<] t] (fun s => η (s - t)) := hmatch
          have hGγ : G =ᶠ[𝓝[<] t] γ := by
            filter_upwards [self_mem_nhdsWithin] with s hs
            simp only [hG_def, if_pos (mem_Iio.mp hs)]
          exact hGγ.trans hmatch'
        have hright : ∀ᶠ s in 𝓝[≥] t, G s = η (s - t) := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          simp only [hG_def, if_neg (not_lt.mpr (mem_Ici.mp hs))]
        have hfull : G =ᶠ[𝓝 t] (fun s => η (s - t)) := by
          rw [← nhdsLT_sup_nhdsGE t, Filter.EventuallyEq, eventually_sup]
          exact ⟨hleft, hright⟩
        filter_upwards [hfull] with s hs _ using hs
      have hηb_at : ContinuousWithinAt (fun s => η (s - t)) (Set.Ioo a₀ (t + δ)) t := by
        have htmem : t ∈ Set.Ioo (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
        refine (hηb_cont t htmem).mono_of_mem_nhdsWithin ?_
        exact mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds htmem)
      refine hηb_at.congr_of_eventuallyEq hG_eq_ηb ?_
      simp only [hG_def, if_neg (lt_irrefl t), sub_self]
    · have htηb : t ∈ Set.Ioo (b - δ) (b + δ) := ⟨by linarith, ht.2⟩
      have hGηb : G =ᶠ[𝓝[Set.Ioo a₀ (b + δ)] t] (fun s => η (s - b)) := by
        have hnhds : Set.Ioi b ∈ 𝓝 t := isOpen_Ioi.mem_nhds hgt
        filter_upwards [nhdsWithin_le_nhds hnhds] with s hs
        simp only [hG_def, if_neg (not_lt.mpr (le_of_lt (mem_Ioi.mp hs)))]
      refine ContinuousWithinAt.congr_of_eventuallyEq ?_ hGηb ?_
      · refine (hηb_cont t htηb).mono_of_mem_nhdsWithin ?_
        exact mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds htηb)
      · simp only [hG_def, if_neg (not_lt.mpr (le_of_lt hgt))]
  refine ⟨G, b + δ, by linarith,
    Geodesic.isGeodesicOn_glue_at_limit_Ioo (I := I) g hδ ha₀b hγ hη hmatch,
    hG_cont, ?_⟩
  intro t ht
  simp only [hG_def, if_pos ht]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M] in
theorem isGeodesicOn_Ioi_of_endpointContinuation
    (g : SmoothRiemannianMetric I M) {γ₀ : ℝ → M} {a₀ b₀ : ℝ}
    (ha₀ : a₀ < 0) (hb₀ : 0 < b₀)
    (hγ₀ : IsGeodesicOn (I := I) g γ₀ (Set.Ioo a₀ b₀))
    (hγ₀_cont : ContinuousOn γ₀ (Set.Ioo a₀ b₀))
    (hcont : ∀ (γ : ℝ → M) (b : ℝ), 0 < b →
      IsGeodesicOn (I := I) g γ (Set.Ioo a₀ b) →
      ContinuousOn γ (Set.Ioo a₀ b) →
      (∀ t < b₀, t < b → γ t = γ₀ t) →
      HasEndpointContinuation (I := I) g γ b) :
    ∃ γ : ℝ → M,
      IsGeodesicOn (I := I) g γ (Set.Ioi a₀) ∧
      ContinuousOn γ (Set.Ioi a₀) ∧
      (∀ t, t < b₀ → γ t = γ₀ t) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have ha₀b₀ : a₀ < b₀ := lt_trans ha₀ hb₀
  let Good : (ℝ × (ℝ → M)) → Prop := fun br =>
    b₀ ≤ br.1 ∧ IsGeodesicOn (I := I) g br.2 (Set.Ioo a₀ br.1) ∧
      ContinuousOn br.2 (Set.Ioo a₀ br.1) ∧
      (∀ t < b₀, br.2 t = γ₀ t)
  let Rec := {br : ℝ × (ℝ → M) // Good br}
  let R : Rec → Rec → Prop := fun a a' =>
    a.1.1 ≤ a'.1.1 ∧ (∀ t < a.1.1, a'.1.2 t = a.1.2 t)
  have hGood_r₀ : Good (b₀, γ₀) := ⟨le_refl _, hγ₀, hγ₀_cont, fun t _ => rfl⟩
  let r₀ : Rec := ⟨(b₀, γ₀), hGood_r₀⟩
  have hchain0 : IsChain R {r₀} := by
    intro a ha b hb hab
    rw [Set.mem_singleton_iff] at ha hb; exact absurd (ha.trans hb.symm) hab
  obtain ⟨Mc, hMc_max, hMc_sub⟩ := hchain0.exists_maxChain
  have hr₀_mem : r₀ ∈ Mc := hMc_sub (Set.mem_singleton _)
  have hMc_chain : IsChain R Mc := hMc_max.1
  have hconsist : ∀ a ∈ Mc, ∀ a' ∈ Mc, ∀ t, t < a.1.1 → t < a'.1.1 →
      a.1.2 t = a'.1.2 t := by
    intro a ha a' ha' t hta hta'
    rcases eq_or_ne a a' with rfl | hne
    · rfl
    · rcases hMc_chain ha ha' hne with hR | hR
      · exact (hR.2 t hta).symm
      · exact hR.2 t hta'
  let Γ : ℝ → M := fun t =>
    if h : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 then (h.choose.1.2 t) else γ₀ t
  have hΓ_val : ∀ a ∈ Mc, ∀ t, t < a.1.1 → Γ t = a.1.2 t := by
    intro a ha t hta
    have hex : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 := ⟨a, ha, hta⟩
    change (if h : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 then (h.choose.1.2 t)
      else γ₀ t) = a.1.2 t
    rw [dif_pos hex]
    obtain ⟨hb_mem, hb_lt⟩ := hex.choose_spec
    exact hconsist _ hb_mem a ha t hb_lt hta
  have hΓ_agree : ∀ t, t < b₀ → Γ t = γ₀ t := by
    intro t ht
    have := hΓ_val r₀ hr₀_mem t ht
    simpa [r₀] using this
  have hΓ_geo_at : ∀ a ∈ Mc, ∀ t, a₀ < t → t < a.1.1 →
      HasGeodesicEquationAt (I := I) g Γ t := by
    intro a ha t hta_lo hta
    have hIoo_nhds : Set.Ioo a₀ a.1.1 ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨hta_lo, hta⟩
    have heq : Γ =ᶠ[𝓝 t] a.1.2 := by
      filter_upwards [hIoo_nhds] with s hs
      exact hΓ_val a ha s hs.2
    exact hasGeodesicEquationAt_congr_of_eventuallyEq (g := g) heq
      (a.2.2.1 t ⟨hta_lo, hta⟩)
  have hΓ_cont_at : ∀ a ∈ Mc, ∀ t, a₀ < t → t < a.1.1 →
      ContinuousWithinAt Γ (Set.Ioi a₀) t := by
    intro a ha t hta_lo hta
    have htmem : t ∈ Set.Ioo a₀ a.1.1 := ⟨hta_lo, hta⟩
    have heq : Γ =ᶠ[𝓝[Set.Ioi a₀] t] a.1.2 := by
      have hnhds : Set.Iio a.1.1 ∈ 𝓝 t := isOpen_Iio.mem_nhds hta
      filter_upwards [nhdsWithin_le_nhds hnhds] with s hs
      exact hΓ_val a ha s (mem_Iio.mp hs)
    have hmem_at : ContinuousWithinAt a.1.2 (Set.Ioi a₀) t := by
      refine ((a.2.2.2.1 t htmem)).mono_of_mem_nhdsWithin ?_
      exact mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds htmem)
    exact hmem_at.congr_of_eventuallyEq heq (hΓ_val a ha t hta)
  let S : Set ℝ := (fun a : Rec => a.1.1) '' Mc
  have hS_ne : S.Nonempty := ⟨b₀, ⟨r₀, hr₀_mem, rfl⟩⟩
  by_cases hbdd : BddAbove S
  · exfalso
    let s := sSup S
    have hb₀_le_s : b₀ ≤ s := le_csSup hbdd ⟨r₀, hr₀_mem, rfl⟩
    have hs_pos : 0 < s := lt_of_lt_of_le hb₀ hb₀_le_s
    have ha₀_lt_s : a₀ < s := lt_of_lt_of_le ha₀b₀ hb₀_le_s
    have hΓ_geo_Ioos : IsGeodesicOn (I := I) g Γ (Set.Ioo a₀ s) := by
      intro t ht
      obtain ⟨b, hbS, htb⟩ := exists_lt_of_lt_csSup hS_ne ht.2
      obtain ⟨a, ha, hab⟩ := hbS
      exact hΓ_geo_at a ha t ht.1 (lt_of_lt_of_eq htb hab.symm)
    have hΓ_cont_Ioos : ContinuousOn Γ (Set.Ioo a₀ s) := by
      intro t ht
      obtain ⟨b, hbS, htb⟩ := exists_lt_of_lt_csSup hS_ne ht.2
      obtain ⟨a, ha, hab⟩ := hbS
      have hcw := hΓ_cont_at a ha t ht.1 (lt_of_lt_of_eq htb hab.symm)
      exact hcw.mono (fun u hu => hu.1)
    have hagree_s : ∀ t < b₀, t < s → Γ t = γ₀ t := fun t ht _ => hΓ_agree t ht
    have hcont_s : HasEndpointContinuation (I := I) g Γ s :=
      hcont Γ s hs_pos hΓ_geo_Ioos hΓ_cont_Ioos hagree_s
    obtain ⟨Γ', s', hss', hΓ'_geo, hΓ'_cont, hΓ'_agree⟩ :=
      isGeodesicOn_Ioo_extend (I := I) g ha₀_lt_s hΓ_geo_Ioos hΓ_cont_Ioos hcont_s
    have hGood' : Good (s', Γ') := by
      refine ⟨le_trans hb₀_le_s hss'.le, hΓ'_geo, hΓ'_cont, ?_⟩
      intro t ht
      have ht_s : t < s := lt_of_lt_of_le ht hb₀_le_s
      change Γ' t = γ₀ t
      rw [hΓ'_agree t ht_s]; exact hΓ_agree t ht
    let r' : Rec := ⟨(s', Γ'), hGood'⟩
    have hr'_notMem : r' ∉ Mc := by
      intro hmem
      have hmemS : s' ∈ S := ⟨r', hmem, rfl⟩
      exact absurd (le_csSup hbdd hmemS) (not_le.mpr hss')
    have hchain' : IsChain R (insert r' Mc) := by
      refine hMc_chain.insert ?_
      intro a ha _
      right
      have ha_mem_S : a.1.1 ∈ S := ⟨a, ha, rfl⟩
      have ha_le_s : a.1.1 ≤ s := le_csSup hbdd ha_mem_S
      refine ⟨?_, ?_⟩
      · change a.1.1 ≤ s'
        exact le_trans ha_le_s hss'.le
      · intro t hta
        have ht_s : t < s := lt_of_lt_of_le hta ha_le_s
        change Γ' t = a.1.2 t
        rw [hΓ'_agree t ht_s]; exact hΓ_val a ha t hta
    have heq_chain : Mc = insert r' Mc :=
      hMc_max.2 hchain' (Set.subset_insert _ _)
    exact hr'_notMem (heq_chain ▸ Set.mem_insert _ _)
  · refine ⟨Γ, ?_, ?_, hΓ_agree⟩
    · intro t ht
      rw [not_bddAbove_iff] at hbdd
      obtain ⟨b, hbS, htb⟩ := hbdd t
      obtain ⟨a, ha, hab⟩ := hbS
      exact hΓ_geo_at a ha t ht (lt_of_lt_of_eq htb hab.symm)
    · intro t ht
      rw [not_bddAbove_iff] at hbdd
      obtain ⟨b, hbS, htb⟩ := hbdd t
      obtain ⟨a, ha, hab⟩ := hbS
      exact hΓ_cont_at a ha t ht (lt_of_lt_of_eq htb hab.symm)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem isGeodesicOn_Ici_of_complete_Ioo
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {γ₀ : ℝ → M} {a₀ b₀ : ℝ}
    (ha₀ : a₀ < 0) (hb₀ : 0 < b₀)
    (hγ₀ : IsGeodesicOn (I := I) g γ₀ (Set.Ioo a₀ b₀))
    (hγ₀_cont : ContinuousOn γ₀ (Set.Ioo a₀ b₀))
    (hreg : ∀ (γ : ℝ → M) (b : ℝ), 0 < b → IsGeodesicOn (I := I) g γ (Set.Ioo a₀ b) →
      ContinuousOn γ (Set.Ioo a₀ b) →
      (∀ t, a₀ < t → t < b₀ → t < b → γ t = γ₀ t) →
      ∃ c : ℝ, 0 ≤ c ∧ ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Ioo a₀ b) ∧
        (∀ τ ∈ Set.Ioo a₀ b, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ 1‖ₑ ≤ ENNReal.ofReal c) ∧
        (∀ s ∈ Set.Ioo a₀ b, (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
          (mfderiv 𝓘(ℝ, ℝ) I γ s 1) ≤ c ^ 2)) :
    ∃ γ : ℝ → M, IsGeodesicOn (I := I) g γ (Set.Ioi a₀) ∧
      (∀ t, t < b₀ → γ t = γ₀ t) := by
  have hcont : ∀ (γ : ℝ → M) (b : ℝ), 0 < b →
      IsGeodesicOn (I := I) g γ (Set.Ioo a₀ b) →
      ContinuousOn γ (Set.Ioo a₀ b) →
      (∀ t < b₀, t < b → γ t = γ₀ t) →
      HasEndpointContinuation (I := I) g γ b := by
    intro γ b hb hγ hγ_cont hagree
    obtain ⟨c, hc_nonneg, hγ_smooth, hSpeedBound, hSpeedSq⟩ :=
      hreg γ b hb hγ hγ_cont (fun t _ ht_b₀ ht_b => hagree t ht_b₀ ht_b)
    exact hasEndpointContinuation_of_complete (I := I) g (lt_trans ha₀ hb)
      hc_nonneg hγ_smooth hSpeedBound hSpeedSq hγ
  obtain ⟨γ, hgeo, _hcontΓ, hagreeΓ⟩ :=
    isGeodesicOn_Ioi_of_endpointContinuation (I := I) g ha₀ hb₀ hγ₀ hγ₀_cont hcont
  exact ⟨γ, hgeo, hagreeΓ⟩

end GeodesicCompleteness

end HopfRinow
end Riemannian
end Geometry
end DifferentialGeometry

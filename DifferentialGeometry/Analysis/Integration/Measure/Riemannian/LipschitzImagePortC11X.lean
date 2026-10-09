import DifferentialGeometry.Analysis.Integration.Measure.Jacobian.LipschitzImageIntegral
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.DensityComparisonC11X
import DifferentialGeometry.Analysis.Integration.Measure.ParamDensityComposition
import DifferentialGeometry.Geometry.Metric.InfinitesimalDistance
import DifferentialGeometry.Geometry.Metric.ChartLipschitz
import DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
import DifferentialGeometry.Topology.FiberBundle.Separation
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Topology.LocallyLipschitzOperations
import Mathlib.Topology.Compactness.Lindelof

/-! A locally nonexpanding map does not increase Riemannian volume on compact sets.
The metrics in the distance hypothesis are the metrics defining both measures. -/

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E H'}
  [I.Boundaryless] [J.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]
  [IsManifold I ∞ M] [IsManifold J ∞ N]
  [T2Space M] [T2Space N] [SigmaCompactSpace M] [SigmaCompactSpace N]

private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
private local instance : IsManifold J 1 N := IsManifold.of_le (n := ∞) (by decide)
private local instance : T2Space (TangentBundle I M) := inferInstance
private local instance : T2Space (TangentBundle J N) := inferInstance

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

private theorem measurableSet_of_isSigmaCompact {X : Type*} [TopologicalSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] {S : Set X}
    (hS : IsSigmaCompact S) : MeasurableSet S := by
  obtain ⟨K, hK, rfl⟩ := hS
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

private theorem sigmaCompact_inter_closed {X : Type*} [TopologicalSpace X]
    {S A : Set X} (hS : IsSigmaCompact S) (hA : IsClosed A) :
    IsSigmaCompact (S ∩ A) := by
  obtain ⟨K, hK, hcover⟩ := hS
  refine ⟨fun n => K n ∩ A, fun n => (hK n).inter_right hA, ?_⟩
  rw [← Set.iUnion_inter, hcover]

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem inner_mfderiv_le_of_eventually_edist_le
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {u : E → M} {v : E → N} {x : E}
    (hu : MDifferentiableAt 𝓘(ℝ, E) I u x)
    (hv : MDifferentiableAt 𝓘(ℝ, E) J v x)
    (hbound : ∀ᶠ y in 𝓝 x,
      riemannianEDistOf h (v x) (v y) ≤ riemannianEDistOf g (u x) (u y))
    (z : E) :
    h.inner (v x) (mfderiv 𝓘(ℝ, E) J v x z) (mfderiv 𝓘(ℝ, E) J v x z) ≤
      g.inner (u x) (mfderiv 𝓘(ℝ, E) I u x z) (mfderiv 𝓘(ℝ, E) I u x z) := by
  have hray : Tendsto (fun t : ℝ => x + t⁻¹ • z) atTop (𝓝 x) := by
    simpa only [zero_smul, add_zero] using
      (tendsto_const_nhds (x := x)).add
        ((tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).smul
          (tendsto_const_nhds (x := z)))
  have hlocal := (hu.continuousAt.tendsto.comp hray).eventually
    (Geometry.eventually_riemannianEDistOf_eq_normal_norm g (u x))
  have hsqrt : Real.sqrt (h.inner (v x)
      (mfderiv 𝓘(ℝ, E) J v x z) (mfderiv 𝓘(ℝ, E) J v x z)) ≤
      Real.sqrt (g.inner (u x)
        (mfderiv 𝓘(ℝ, E) I u x z) (mfderiv 𝓘(ℝ, E) I u x z)) := by
    apply le_of_tendsto_of_tendsto
      (Geometry.tendsto_riemannianEDistOf_ray h hv z)
      (Geometry.tendsto_riemannianEDistOf_ray g hu z)
    filter_upwards [hray.eventually hbound, hlocal] with t ht hfin
    have htop : riemannianEDistOf g (u x) (u (x + t⁻¹ • z)) ≠ ⊤ := by
      dsimp only [Function.comp_apply] at hfin
      rw [hfin]
      exact ENNReal.ofReal_ne_top
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono htop ht) (abs_nonneg t)
  exact (Real.sqrt_le_sqrt_iff (metric_inner_self_nonneg g _ _)).mp hsqrt

private theorem volume_image_chart_le
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) J E N 1)
    {F : E → E} {U S : Set E} (hU : IsOpen U) (hS : IsSigmaCompact S)
    (hSU : S ⊆ U) (hUΦ : U ⊆ Φ.source) (hFΨ : MapsTo F U Ψ.source)
    (hF : Measurable F) (hLip : LocallyLipschitzOn U F)
    (hshort : ∀ x ∈ U, ∀ y ∈ U,
      riemannianEDistOf h (Ψ (F x)) (Ψ (F y)) ≤ riemannianEDistOf g (Φ x) (Φ y)) :
    riemannianVolumeMeasure (I := J) (M := N) h (Ψ '' (F '' S)) ≤
      riemannianVolumeMeasure (I := I) (M := M) g (Φ '' S) := by
  classical
  have hSm := measurableSet_of_isSigmaCompact hS
  have hFcont : ContinuousOn F U := hLip.continuousOn
  have him : MeasurableSet (F '' S) :=
    measurableSet_of_isSigmaCompact (hS.image_of_continuousOn (hFcont.mono hSU))
  let w : E → ℝ≥0∞ := Ψ.source.piecewise
    (fun y => ENNReal.ofReal (paramDensity h Ψ y)) (fun _ => 0)
  have hw : Measurable w := ContinuousOn.measurable_piecewise
    (ENNReal.continuous_ofReal.comp_continuousOn (paramDensity_contOn h Ψ))
    continuousOn_const Ψ.open_source.measurableSet
  have hwF (x : E) (hx : x ∈ U) :
      w (F x) = ENNReal.ofReal (paramDensity h Ψ (F x)) := by
    exact Set.piecewise_eq_of_mem _ _ _ (hFΨ hx)
  rw [riemannianVolumeMeasure_image_param_eq h Ψ him
      (image_subset_iff.mpr (hFΨ.mono_left hSU)),
    riemannianVolumeMeasure_image_param_eq g Φ hSm (hSU.trans hUΦ)]
  calc
    (∫⁻ y in F '' S, ENNReal.ofReal (paramDensity h Ψ y) ∂modelHaar) =
        ∫⁻ y in F '' S, w y ∂modelHaar := by
      apply setLIntegral_congr_fun him
      rintro y ⟨x, hx, rfl⟩
      exact (hwF x (hSU hx)).symm
    _ ≤ ∫⁻ x in S, w (F x) * ENNReal.ofReal |(fderiv ℝ F x).det| ∂modelHaar :=
      image_lintegral_le_of_locallyLipschitzOn modelHaar hU hSm hSU hF hLip hw
    _ ≤ ∫⁻ x in S, ENNReal.ofReal (paramDensity g Φ x) ∂modelHaar := by
      apply lintegral_mono_ae
      have hd : ∀ᵐ x ∂(modelHaar (E := E)), x ∈ U → DifferentiableAt ℝ F x := by
        filter_upwards [hLip.ae_differentiableWithinAt_of_mem
          (μ := modelHaar (E := E))] with x hx
        exact fun hxU => (hx hxU).differentiableAt (hU.mem_nhds hxU)
      filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem hSm] with x hx hxS
      have hxU := hSU hxS
      have hFx := hx hxU
      have hΦ := Φ.mdifferentiableAt one_ne_zero (hUΦ hxU)
      have hΨ := Ψ.mdifferentiableAt one_ne_zero (hFΨ hxU)
      have hc := paramDensity_le_of_inner_mfderiv_le g h
        (u := Φ) (v := Ψ ∘ F) (x := x)
        (LinearMap.ker_eq_bot.mp (paramDeriv_ker Φ (hUΦ hxU)))
        (inner_mfderiv_le_of_eventually_edist_le g h hΦ
          (hΨ.comp x hFx.mdifferentiableAt)
          (Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => hshort x hxU y hy))
      rw [paramDensity_comp h hΨ hFx] at hc
      rw [hwF x hxU]
      calc
        _ = ENNReal.ofReal (|(fderiv ℝ F x).det| * paramDensity h Ψ (F x)) := by
          rw [ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
        _ ≤ _ := ENNReal.ofReal_le_ofReal hc

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_open_volume_image_le
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N)) (p : M)
    (hshort : ∃ V ∈ 𝓝 p, ∀ y ∈ V, ∀ z ∈ V,
      riemannianEDistOf h (f y) (f z) ≤ riemannianEDistOf g y z) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      ∀ S : Set M, IsSigmaCompact S → S ⊆ V →
        riemannianVolumeMeasure (I := J) (M := N) h (f '' S) ≤ riemannianVolumeMeasure (I := I) (M := M) g S := by
  classical
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace H' := J.locallyCompactSpace
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace H' N
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  let : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  let : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace J : N → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace N := .ofRiemannianMetric J N
  let : IsRiemannianManifold J N := ⟨fun _ _ => rfl⟩
  obtain ⟨V₀, hV₀, hshort⟩ := hshort
  obtain ⟨V₁, hV₁V₀, hV₁, hpV₁⟩ := mem_nhds_iff.mp hV₀
  let Φ := (PartialDiffeomorph.extChartAt I 1 p).symm
  let Ψ := (PartialDiffeomorph.extChartAt J 1 (f p)).symm
  let V : Set M := V₁ ∩ Φ.target ∩ f ⁻¹' Ψ.target
  have hV : IsOpen V := (hV₁.inter Φ.open_target).inter
    (Ψ.open_target.preimage f.continuous)
  have hpV : p ∈ V := ⟨⟨hpV₁, mem_extChartAt_source p⟩,
    mem_extChartAt_source (f p)⟩
  let U : Set E := Φ.source ∩ Φ ⁻¹' V
  have hU : IsOpen U := Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
    Φ.open_source hV
  let F₀ : E → E := Ψ.symm ∘ f ∘ Φ
  have hfLip : LipschitzOnWith 1 f V := by
    intro y hy z hz
    change riemannianEDistOf h (f y) (f z) ≤
      (1 : ℝ≥0∞) * riemannianEDistOf g y z
    simpa only [one_mul] using
      hshort y (hV₁V₀ hy.1.1) z (hV₁V₀ hz.1.1)
  have hfLocal : LocallyLipschitzOn V f :=
    fun _ _ => ⟨1, V, self_mem_nhdsWithin, hfLip⟩
  have hΦLip : LocallyLipschitzOn U Φ :=
    (Geometry.Riemannian.locallyLipschitzOn_extChartAt_symm (I := I) p).mono
      inter_subset_left
  have hF₀Lip : LocallyLipschitzOn U F₀ :=
    (Geometry.Riemannian.locallyLipschitzOn_extChartAt (I := J) (f p)).comp
      (hfLocal.comp hΦLip (fun _ hx => hx.2)) (fun _ hx => hx.2.2)
  let F : E → E := U.piecewise F₀ (fun _ => 0)
  have hFeq (x : E) (hx : x ∈ U) : F x = F₀ x :=
    Set.piecewise_eq_of_mem _ _ _ hx
  have hFm : Measurable F := ContinuousOn.measurable_piecewise
    hF₀Lip.continuousOn continuousOn_const hU.measurableSet
  have hFLip : LocallyLipschitzOn U F := by
    intro x hx
    obtain ⟨L, A, hA, hLA⟩ := hF₀Lip hx
    refine ⟨L, A ∩ U, inter_mem hA self_mem_nhdsWithin, ?_⟩
    intro y hy z hz
    rw [hFeq y hy.2, hFeq z hz.2]
    exact hLA hy.1 hz.1
  have hFΨ : MapsTo F U Ψ.source := by
    intro x hx
    rw [hFeq x hx]
    exact Ψ.map_target hx.2.2
  have hΨF (x : E) (hx : x ∈ U) : Ψ (F x) = f (Φ x) := by
    rw [hFeq x hx]
    exact Ψ.right_inv hx.2.2
  refine ⟨V, hV, hpV, ?_⟩
  intro S hS hSV
  let B : Set E := Φ.symm '' S
  have hBS : B ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    have hyV := hSV hy
    refine ⟨Φ.map_target hyV.1.2, ?_⟩
    change Φ.toPartialEquiv (Φ.toPartialEquiv.symm y) ∈ V
    rwa [Φ.toPartialEquiv.right_inv hyV.1.2]
  have hB : IsSigmaCompact B := hS.image_of_continuousOn
    (Φ.contMDiffOn_invFun.continuousOn.mono (fun _ hy => (hSV hy).1.2))
  have hΦB : Φ '' B = S := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      change Φ.toPartialEquiv (Φ.toPartialEquiv.symm z) ∈ S
      rwa [Φ.toPartialEquiv.right_inv (hSV hz).1.2]
    · intro hy
      exact ⟨Φ.symm y, ⟨y, hy, rfl⟩, Φ.right_inv (hSV hy).1.2⟩
  have hΨFB : Ψ '' (F '' B) = f '' S := by
    calc
      Ψ '' (F '' B) = (fun x => Ψ (F x)) '' B := image_image Ψ F B
      _ = (fun x => f (Φ x)) '' B := image_congr fun x hx => hΨF x (hBS hx)
      _ = f '' (Φ '' B) := (image_image f Φ B).symm
      _ = f '' S := by rw [hΦB]
  rw [← hΨFB, ← hΦB]
  apply volume_image_chart_le g h Φ Ψ hU hB hBS inter_subset_left hFΨ hFm hFLip
  intro x hx y hy
  rw [hΨF x hx, hΨF y hy]
  exact hshort (Φ x) (hV₁V₀ hx.2.1.1) (Φ y) (hV₁V₀ hy.2.1.1)

/-- A continuous map that is locally nonexpanding for the two actual Riemannian distances
does not increase volume on a compact source set. No injectivity is required. -/
theorem riemannianVolumeMeasure_image_le_of_locally_nonexpanding
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C(M, N)) {K : Set M} (hK : IsCompact K)
    (hshort : ∀ p ∈ K, ∃ V ∈ 𝓝 p, ∀ y ∈ V, ∀ z ∈ V,
      riemannianEDistOf h (f y) (f z) ≤ riemannianEDistOf g y z) :
    riemannianVolumeMeasure (I := J) (M := N) h (f '' K) ≤ riemannianVolumeMeasure (I := I) (M := M) g K := by
  classical
  by_cases hzero : K = ∅
  · simp [hzero]
  obtain ⟨p₀, hp₀⟩ := Set.nonempty_iff_ne_empty.mpr hzero
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hlocal (p : K) := exists_open_volume_image_le g h f p.1 (hshort p.1 p.2)
  choose V hV hpV hvolume using hlocal
  obtain ⟨t, htc, hcover⟩ := countable_cover_nhds (fun p : K =>
    ((hV p).preimage continuous_subtype_val).mem_nhds (hpV p))
  let enum : ℕ → K := Set.enumerateCountable htc ⟨p₀, hp₀⟩
  have ht_range : t ⊆ Set.range enum :=
    Set.subset_range_enumerate htc ⟨p₀, hp₀⟩
  let A : ℕ → Set M := fun n => V (enum n)
  have hKA : K ⊆ ⋃ n, A n := by
    intro x hx
    have hm : (⟨x, hx⟩ : K) ∈ ⋃ p ∈ t, Subtype.val ⁻¹' V p := by
      rw [hcover]
      exact Set.mem_univ _
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hm
    obtain ⟨n, hn⟩ := ht_range hp
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change x ∈ V (enum n)
    rw [hn]
    exact hxp
  let P : ℕ → Set M := fun n => K ∩ disjointed A n
  have hPm (n : ℕ) : MeasurableSet (P n) := hK.measurableSet.inter
    (MeasurableSet.disjointed (fun k => (hV (enum k)).measurableSet) n)
  have hPdisj : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    intro i j hij
    exact (disjoint_disjointed A hij).mono inter_subset_right inter_subset_right
  have hPK : (⋃ n, P n) = K := by
    change (⋃ n, K ∩ disjointed A n) = K
    rw [← Set.inter_iUnion, iUnion_disjointed, Set.inter_eq_left]
    exact hKA
  have hPσ (n : ℕ) : IsSigmaCompact (P n) := by
    let C : Set M := K ∩ ⋂ j < n, (A j)ᶜ
    have hC : IsClosed C := hK.isClosed.inter
      (isClosed_iInter fun j => isClosed_iInter fun _ => (hV (enum j)).isClosed_compl)
    have heq : P n = A n ∩ C := by
      ext x
      simp only [P, C, disjointed_eq_inf_compl, Set.inf_eq_inter,
        Set.iInf_eq_iInter, Set.mem_inter_iff,
        Set.mem_iInter, Set.mem_compl_iff]
      tauto
    rw [heq]
    exact sigmaCompact_inter_closed (Geometry.isSigmaCompact_of_isOpen I (hV (enum n))) hC
  calc
    riemannianVolumeMeasure (I := J) (M := N) h (f '' K) =
        riemannianVolumeMeasure (I := J) (M := N) h (⋃ n, f '' P n) := by rw [← image_iUnion, hPK]
    _ ≤ ∑' n, riemannianVolumeMeasure (I := J) (M := N) h (f '' P n) := measure_iUnion_le _
    _ ≤ ∑' n, riemannianVolumeMeasure (I := I) (M := M) g (P n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      exact hvolume (enum n) (P n) (hPσ n)
        (fun _ hx => disjointed_subset A n hx.2)
    _ = riemannianVolumeMeasure (I := I) (M := M) g K := by
      rw [← measure_iUnion hPdisj hPm, hPK]

end DifferentialGeometry.Integral.Measure

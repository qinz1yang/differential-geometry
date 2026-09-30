import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.Pullback
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PullbackLocalIso

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

open Bundle Filter Manifold Set TopologicalSpace
open scoped Topology Manifold ContDiff

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem trivialization_opens_eq
    (U : Opens M) (a x : U) (hx : (x : M) ∈ (chartAt H (a : M)).source) :
    (trivializationAt E (TangentSpace I (M := U)) a).continuousLinearMapAt ℝ x =
      (trivializationAt E (TangentSpace I (M := M)) (a : M)).continuousLinearMapAt
        ℝ (x : M) := by
  have hxU : x ∈ (chartAt H a).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact hx
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hxU,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx,
    tangentCoordChange_opens x a x (mem_chart_source H (x : M))]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
theorem chartRepAt_opens_eventuallyEq
    (U : Opens M) (c : ℝ → U) (W : ∀ s, TangentSpace I (c s)) {t : ℝ}
    (hc : ContinuousAt c t) :
    chartRepAt (I := I) c W t =ᶠ[𝓝 t]
      chartRepAt (I := I) (fun s => (c s : M)) (fun s => (W s : E)) t := by
  have hn : ∀ᶠ s in 𝓝 t, (c s : M) ∈ (chartAt H (c t : M)).source :=
    (continuous_subtype_val.continuousAt.comp hc).eventually
      ((chartAt H (c t : M)).open_source.mem_nhds (mem_chart_source H (c t : M)))
  filter_upwards [hn] with s hs
  change (trivializationAt E (TangentSpace I (M := U)) (c t)).continuousLinearMapAt
      ℝ (c s) (W s) =
    (trivializationAt E (TangentSpace I (M := M)) (c t : M)).continuousLinearMapAt
      ℝ (c s : M) (W s)
  exact congrArg (fun L => L (W s)) (trivialization_opens_eq U (c t) (c s) hs)

open scoped Classical in
private def opensCurve (U : Opens M) (γ : ℝ → M) (x₀ : U) : ℝ → U := fun s =>
  if hs : γ s ∈ U then ⟨γ s, hs⟩ else x₀

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem opensCurve_eventuallyEq
    (U : Opens M) (γ : ℝ → M) {t : ℝ} (ht : γ t ∈ U) (hγ : ContinuousAt γ t) :
    (fun s => (opensCurve U γ ⟨γ t, ht⟩ s : M)) =ᶠ[𝓝 t] γ := by
  filter_upwards [hγ.preimage_mem_nhds (U.isOpen.mem_nhds ht)] with s hs
  simp only [opensCurve, dite_eq_left (show γ s ∈ U from hs)]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem opensCurve_self (U : Opens M) (γ : ℝ → M) {t : ℝ} (ht : γ t ∈ U) :
    opensCurve U γ ⟨γ t, ht⟩ t = ⟨γ t, ht⟩ := by
  simp only [opensCurve, dite_eq_left ht]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem opensCurve_continuousAt
    (U : Opens M) (γ : ℝ → M) {t : ℝ} (ht : γ t ∈ U) (hγ : ContinuousAt γ t) :
    ContinuousAt (opensCurve U γ ⟨γ t, ht⟩) t :=
  Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    (hγ.congr (opensCurve_eventuallyEq U γ ht hγ).symm)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] in
private theorem opensCurve_mdifferentiableAt
    (U : Opens M) (γ : ℝ → M) {t : ℝ} (ht : γ t ∈ U)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I (opensCurve U γ ⟨γ t, ht⟩) t :=
  (MDifferentiableAt.subtypeVal_comp_iff _ t).mp
    (hγ.congr_of_eventuallyEq (opensCurve_eventuallyEq U γ ht hγ.continuousAt))

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem chartRepAt_opensCurve
    (U : Opens M) (γ : ℝ → M) (V : ∀ s, TangentSpace I (γ s)) {t : ℝ}
    (ht : γ t ∈ U) (hγ : ContinuousAt γ t) :
    chartRepAt (I := I) (opensCurve U γ ⟨γ t, ht⟩) (fun s => (V s : E)) t =ᶠ[𝓝 t]
      chartRepAt (I := I) γ V t :=
  (chartRepAt_opens_eventuallyEq U _ _ (opensCurve_continuousAt U γ ht hγ)).trans
    (chartRep_congr_curve (I := I) _ V (opensCurve_eventuallyEq U γ ht hγ)
      (Eventually.of_forall fun _ => rfl))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless]
  [T2Space M] [T2Space N] [IsManifold I ∞ M] [IsManifold J ∞ N] in
private theorem mfderiv_toOpensDiffeo_symm_apply
    (Φ : PartialDiffeomorph I J M N ∞) {U : Opens M} (hU : (U : Set M) ⊆ Φ.source)
    (x : U) (v : TangentSpace I x) :
    mfderiv J I (PartialDiffeomorph.toOpensDiffeo Φ hU).symm
        (PartialDiffeomorph.toOpensDiffeo Φ hU x)
        (mfderiv I J (PartialDiffeomorph.toOpensDiffeo Φ hU) x v) = v := by
  let Ψ := PartialDiffeomorph.toOpensDiffeo Φ hU
  have hcomp := mfderiv_comp_apply (I := I) (I' := J) (I'' := I) x
    (Ψ.symm.contMDiff.mdifferentiableAt (by decide))
    (Ψ.contMDiff.mdifferentiableAt (by decide)) v
  have hid : (Ψ.symm : _ → U) ∘ (Ψ : U → _) = id := funext Ψ.symm_apply_apply
  rw [hid, mfderiv_id] at hcomp
  exact hcomp.symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless]
  [T2Space M] [T2Space N] [IsManifold I ∞ M] [IsManifold J ∞ N] in
private theorem toOpensDiffeo_opensCurve_eventuallyEq
    (Φ : PartialDiffeomorph I J M N ∞) (γ : ℝ → M) (V : ∀ s, TangentSpace I (γ s))
    {t : ℝ} (ht : γ t ∈ Φ.source) (hγ : ContinuousAt γ t) :
    (fun s => ((PartialDiffeomorph.toOpensDiffeo Φ (U := ⟨Φ.source, Φ.open_source⟩)
        subset_rfl (opensCurve ⟨Φ.source, Φ.open_source⟩ γ ⟨γ t, ht⟩ s) : _) : N))
        =ᶠ[𝓝 t] (fun s => Φ (γ s)) ∧
      ∀ᶠ s in 𝓝 t, (mfderiv I J (PartialDiffeomorph.toOpensDiffeo Φ
        (U := ⟨Φ.source, Φ.open_source⟩) subset_rfl)
          (opensCurve ⟨Φ.source, Φ.open_source⟩ γ ⟨γ t, ht⟩ s) (V s) : F) =
        mfderiv I J Φ (γ s) (V s) := by
  have hev := opensCurve_eventuallyEq ⟨Φ.source, Φ.open_source⟩ γ ht hγ
  refine ⟨?_, ?_⟩
  · filter_upwards [hev] with s hs
    exact congrArg (Φ : M → N) hs
  · filter_upwards [hev] with s hs
    refine (PartialDiffeomorph.mfderiv_toOpensDiffeo Φ subset_rfl _ (V s)).trans ?_
    exact congrArg (fun y : M => (mfderiv I J Φ y (show TangentSpace I y from (V s : E)) : F)) hs

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [T2Space N]
  [J.Boundaryless] in
theorem differentiableAt_chartRepAt_partialDiffeomorph_comp
    (Φ : PartialDiffeomorph I J M N ∞) (γ : ℝ → M) (V : ∀ s, TangentSpace I (γ s))
    {t : ℝ} (ht : γ t ∈ Φ.source) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    DifferentiableAt ℝ
      (chartRepAt (I := J) (fun s => Φ (γ s))
        (fun s => mfderiv I J Φ (γ s) (V s)) t) t := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold J 1 N := IsManifold.of_le (n := ∞) (by decide)
  let U : Opens M := ⟨Φ.source, Φ.open_source⟩
  have hU : (U : Set M) ⊆ Φ.source := subset_rfl
  let Ψ := PartialDiffeomorph.toOpensDiffeo Φ hU
  let γU := opensCurve U γ ⟨γ t, ht⟩
  have hγc := hγ.continuousAt
  have hev := opensCurve_eventuallyEq U γ ht hγc
  have hVU : DifferentiableAt ℝ (chartRepAt (I := I) γU (fun s => (V s : E)) t) t :=
    ((chartRepAt_opensCurve U γ V ht hγc).differentiableAt_iff).mpr hV
  have hmap := chartRep_map_diff (I := I) (J := J) Ψ γU (fun s => (V s : E)) t
    (opensCurve_mdifferentiableAt U γ ht hγ) hVU
  have hΨc : ContinuousAt (fun s => Ψ (γU s)) t :=
    Ψ.continuous.continuousAt.comp (opensCurve_continuousAt U γ ht hγc)
  refine ((chartRepAt_opens_eventuallyEq _ _ _ hΨc).trans
    (chartRep_congr_curve (I := J) _ _ ?_ ?_)).differentiableAt_iff.mp hmap
  · exact (toOpensDiffeo_opensCurve_eventuallyEq Φ γ V ht hγc).1
  · exact (toOpensDiffeo_opensCurve_eventuallyEq Φ γ V ht hγc).2

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [T2Space N]
  [I.Boundaryless] in
theorem mdifferentiableAt_and_differentiableAt_chartRepAt_of_partialDiffeomorph_comp
    (Φ : PartialDiffeomorph I J M N ∞) (γ : ℝ → M) (V : ∀ s, TangentSpace I (γ s))
    {t : ℝ} (ht : γ t ∈ Φ.source) (hγ : ContinuousAt γ t)
    (hΦγ : MDifferentiableAt 𝓘(ℝ, ℝ) J (fun s => Φ (γ s)) t)
    (hW : DifferentiableAt ℝ
      (chartRepAt (I := J) (fun s => Φ (γ s))
        (fun s => mfderiv I J Φ (γ s) (V s)) t) t) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I γ t ∧
      DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold J 1 N := IsManifold.of_le (n := ∞) (by decide)
  let U : Opens M := ⟨Φ.source, Φ.open_source⟩
  have hU : (U : Set M) ⊆ Φ.source := subset_rfl
  let Un : Opens N := ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  let Ψ : U ≃ₘ⟮I, J⟯ Un := PartialDiffeomorph.toOpensDiffeo Φ hU
  let γU := opensCurve U γ ⟨γ t, ht⟩
  let δU : ℝ → Un := fun s => Ψ (γU s)
  have hev := opensCurve_eventuallyEq U γ ht hγ
  have hδev : (fun s => (δU s : N)) =ᶠ[𝓝 t] fun s => Φ (γ s) :=
    (toOpensDiffeo_opensCurve_eventuallyEq Φ γ V ht hγ).1
  have hδc : ContinuousAt δU t :=
    Ψ.continuous.continuousAt.comp (opensCurve_continuousAt U γ ht hγ)
  have hδ : MDifferentiableAt 𝓘(ℝ, ℝ) J δU t :=
    (MDifferentiableAt.subtypeVal_comp_iff _ t).mp (hΦγ.congr_of_eventuallyEq hδev)
  have hγU : γU = fun s => Ψ.symm (δU s) := funext fun s => (Ψ.symm_apply_apply _).symm
  have hγUd : MDifferentiableAt 𝓘(ℝ, ℝ) I γU t := by
    rw [hγU]
    exact (Ψ.symm.contMDiff.mdifferentiableAt (by decide)).comp t hδ
  let WU : ∀ s, TangentSpace J (δU s) := fun s => mfderiv I J Ψ (γU s) (V s)
  have hWev : ∀ᶠ s in 𝓝 t, (WU s : F) = mfderiv I J Φ (γ s) (V s) :=
    (toOpensDiffeo_opensCurve_eventuallyEq Φ γ V ht hγ).2
  have hWU : DifferentiableAt ℝ (chartRepAt (I := J) δU WU t) t :=
    ((chartRepAt_opens_eventuallyEq _ δU WU hδc).trans
      (chartRep_congr_curve (I := J) _ _ hδev hWev)).differentiableAt_iff.mpr hW
  have hback := chartRep_map_diff (I := J) (J := I) Ψ.symm δU WU t hδ hWU
  have hγUc : ContinuousAt γU t := opensCurve_continuousAt U γ ht hγ
  have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s => (γU s : M)) t :=
    (MDifferentiableAt.subtypeVal_comp_iff γU t).mpr hγUd
  refine ⟨hγd.congr_of_eventuallyEq hev.symm, ?_⟩
  have h1 : chartRepAt (I := I) (fun s => Ψ.symm (δU s))
      (fun s => mfderiv J I Ψ.symm (δU s) (WU s)) t =ᶠ[𝓝 t]
      chartRepAt (I := I) γU (fun s => (V s : E)) t :=
    chartRep_congr_curve (I := I) _ _
      (Eventually.of_forall fun s => Ψ.symm_apply_apply (γU s))
      (Eventually.of_forall fun s => mfderiv_toOpensDiffeo_symm_apply Φ hU (γU s) (V s))
  have h2 : chartRepAt (I := I) γU (fun s => (V s : E)) t =ᶠ[𝓝 t]
      chartRepAt (I := I) γ V t := chartRepAt_opensCurve U γ V ht hγ
  exact ((h1.trans h2).differentiableAt_iff).mp hback

theorem mfderiv_covDerivAlong_partialDiffeomorph
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph I J M N ∞)
    (hmet : ∀ x ∈ Φ.source, ∀ v w : TangentSpace I x,
      h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w) = g.inner x v w)
    (γ : ℝ → M) (V : ∀ s, TangentSpace I (γ s)) {t : ℝ} (ht : γ t ∈ Φ.source)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    mfderiv I J Φ (γ t) (covDerivAlong g γ V t) =
      covDerivAlong h (fun s => Φ (γ s)) (fun s => mfderiv I J Φ (γ s) (V s)) t := by
  let U : Opens M := ⟨Φ.source, Φ.open_source⟩
  have hU : (U : Set M) ⊆ Φ.source := subset_rfl
  let Un : Opens N := ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  let Ψ : U ≃ₘ⟮I, J⟯ Un := PartialDiffeomorph.toOpensDiffeo Φ hU
  let γU := opensCurve U γ ⟨γ t, ht⟩
  have hγc := hγ.continuousAt
  have hev := opensCurve_eventuallyEq U γ ht hγc
  have hγUc : ContinuousAt γU t := opensCurve_continuousAt U γ ht hγc
  have hVU : DifferentiableAt ℝ (chartRepAt (I := I) γU (fun s => (V s : E)) t) t :=
    ((chartRepAt_opensCurve U γ V ht hγc).differentiableAt_iff).mpr hV
  have hmetric : g.restrictOpen U =
      Diffeomorph.pullbackMetricCross (h.restrictOpen Un) Ψ := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [SmoothRiemannianMetric.restrictOpen_inner, Diffeomorph.pullbackMetricCross_inner,
      SmoothRiemannianMetric.restrictOpen_inner, PartialDiffeomorph.mfderiv_toOpensDiffeo,
      PartialDiffeomorph.mfderiv_toOpensDiffeo]
    exact (hmet x x.2 v w).symm
  have hnat := covDerivAlong_pullback (h.restrictOpen Un) Ψ γU (fun s => (V s : E)) t
    (opensCurve_mdifferentiableAt U γ ht hγ) hVU
  rw [← hmetric] at hnat
  have hleft : (covDerivAlong (g.restrictOpen U) γU (fun s => (V s : E)) t : E) =
      covDerivAlong g γ V t :=
    (DifferentialGeometry.Geometry.covDerivAlong_restrictOpen g U γU _ t hγUc).trans
      (covDerivAlong_congr_curve g _ V hev (Eventually.of_forall fun _ => rfl))
  have hΨc : ContinuousAt (fun s => Ψ (γU s)) t :=
    Ψ.continuous.continuousAt.comp hγUc
  have hright := (DifferentialGeometry.Geometry.covDerivAlong_restrictOpen h Un
    (fun s => Ψ (γU s)) (fun s => mfderiv I J Ψ (γU s) (V s)) t hΨc).trans
      (covDerivAlong_congr_curve (I := J) h _
        (fun s => mfderiv I J Φ (γ s) (V s)) (γ' := fun s => Φ (γ s))
        (toOpensDiffeo_opensCurve_eventuallyEq Φ γ V ht hγc).1
        (toOpensDiffeo_opensCurve_eventuallyEq Φ γ V ht hγc).2)
  rw [← hright, ← hnat, PartialDiffeomorph.mfderiv_toOpensDiffeo Φ hU (γU t), hleft]
  have hγUt : (γU t : M) = γ t := congrArg Subtype.val (opensCurve_self U γ ht)
  exact congrArg (fun y : M => mfderiv I J Φ y
    (show TangentSpace I y from (covDerivAlong g γ V t : E))) hγUt.symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless]
  [T2Space M] [T2Space N] [IsManifold I ∞ M] [IsManifold J ∞ N] in
private theorem exists_partialDiffeomorph_eventuallyEq_comp
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) (γ : ℝ → M) {t : ℝ}
    (hγ : ContinuousAt γ t) :
    ∃ Φ : PartialDiffeomorph I J M N ∞, γ t ∈ Φ.source ∧
      (∀ x ∈ Φ.source, f x = Φ x ∧ mfderiv I J f x = mfderiv I J Φ x) ∧
      (fun s => f (γ s)) =ᶠ[𝓝 t] (fun s => Φ (γ s)) ∧ ∀ᶠ s in 𝓝 t, γ s ∈ Φ.source := by
  obtain ⟨Φ, hx, hEq⟩ := hf (γ t)
  have hsrc : ∀ᶠ s in 𝓝 t, γ s ∈ Φ.source := hγ.preimage_mem_nhds (Φ.open_source.mem_nhds hx)
  refine ⟨Φ, hx, fun x hx' => ⟨hEq hx', ?_⟩, ?_, hsrc⟩
  · exact (Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds hx') hEq).mfderiv_eq
  · filter_upwards [hsrc] with s hs
    exact hEq hs

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [T2Space N]
  [J.Boundaryless] in
theorem differentiableAt_chartRepAt_comp_of_isLocalDiffeomorph
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) (γ : ℝ → M)
    (V : ∀ s, TangentSpace I (γ s)) {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    DifferentiableAt ℝ
      (chartRepAt (I := J) (fun s => f (γ s)) (fun s => mfderiv I J f (γ s) (V s)) t) t := by
  obtain ⟨Φ, hx, hΦ, hcurve, hsrc⟩ :=
    exists_partialDiffeomorph_eventuallyEq_comp hf γ hγ.continuousAt
  refine (chartRep_congr_curve (I := J) _ _ hcurve.symm ?_).differentiableAt_iff.mp
    (differentiableAt_chartRepAt_partialDiffeomorph_comp Φ γ V hx hγ hV)
  filter_upwards [hsrc] with s hs
  rw [(hΦ _ hs).2]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [T2Space N]
  [I.Boundaryless] in
theorem mdifferentiableAt_and_differentiableAt_chartRepAt_of_isLocalDiffeomorph_comp
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) (γ : ℝ → M)
    (V : ∀ s, TangentSpace I (γ s)) {t : ℝ} (hγ : ContinuousAt γ t)
    (hfγ : MDifferentiableAt 𝓘(ℝ, ℝ) J (fun s => f (γ s)) t)
    (hW : DifferentiableAt ℝ
      (chartRepAt (I := J) (fun s => f (γ s)) (fun s => mfderiv I J f (γ s) (V s)) t) t) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I γ t ∧
      DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t := by
  obtain ⟨Φ, hx, hΦ, hcurve, hsrc⟩ := exists_partialDiffeomorph_eventuallyEq_comp hf γ hγ
  refine mdifferentiableAt_and_differentiableAt_chartRepAt_of_partialDiffeomorph_comp
    Φ γ V hx hγ (hfγ.congr_of_eventuallyEq hcurve.symm) ?_
  refine (chartRep_congr_curve (I := J) _ _ hcurve ?_).differentiableAt_iff.mp hW
  filter_upwards [hsrc] with s hs
  rw [(hΦ _ hs).2]
  rfl

theorem mfderiv_covDerivAlong_of_isLocalDiffeomorph
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f)
    (hmet : ∀ x (v w : TangentSpace I x),
      h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) = g.inner x v w)
    (γ : ℝ → M) (V : ∀ s, TangentSpace I (γ s)) {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    mfderiv I J f (γ t) (covDerivAlong g γ V t) =
      covDerivAlong h (fun s => f (γ s)) (fun s => mfderiv I J f (γ s) (V s)) t := by
  obtain ⟨Φ, hx, hΦ, hcurve, hsrc⟩ :=
    exists_partialDiffeomorph_eventuallyEq_comp hf γ hγ.continuousAt
  have hmetΦ : ∀ x ∈ Φ.source, ∀ v w : TangentSpace I x,
      h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w) = g.inner x v w := by
    intro x hx' v w
    rw [← (hΦ x hx').1, ← (hΦ x hx').2]
    exact hmet x v w
  have hnat := mfderiv_covDerivAlong_partialDiffeomorph g h Φ hmetΦ γ V hx hγ hV
  have e1 : (mfderiv I J f (γ t) (covDerivAlong g γ V t) : F) =
      mfderiv I J Φ (γ t) (covDerivAlong g γ V t) := by
    rw [(hΦ _ hx).2]
    rfl
  refine e1.trans (hnat.trans (covDerivAlong_congr_curve (I := J) h _ _ hcurve.symm ?_))
  filter_upwards [hsrc] with s hs
  rw [(hΦ _ hs).2]
  rfl

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

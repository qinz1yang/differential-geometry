import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Connection.OpenTarget
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

open Bundle Filter Manifold Set TopologicalSpace
open scoped Topology Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F] [NeZero (Module.finrank ℝ F)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [FiniteDimensional ℝ F] [CompleteSpace F] [NeZero (Module.finrank ℝ F)] in
private theorem tangent_trivialization_open
    (U : Opens M) (a x : U)
    (hx : (x : M) ∈ (chartAt H (a : M)).source) :
    (trivializationAt E (TangentSpace I (M := U)) a).continuousLinearMapAt ℝ x =
      (trivializationAt E (TangentSpace I (M := M)) (a : M)).continuousLinearMapAt
        ℝ (x : M) := by
  have hxU : x ∈ (chartAt H a).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact hx
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hxU,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx,
    tangentCoordChange_opens x a x (mem_chart_source H (x : M))]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace F] [NeZero (Module.finrank ℝ F)] in
theorem covDerivAlong_map_localIso
    [I.Boundaryless] [J.Boundaryless]
    [T2Space M] [BoundarylessManifold I M]
    [T2Space N] [BoundarylessManifold J N]
    (g : SmoothRiemannianMetric I M) (g' : SmoothRiemannianMetric J N)
    {f : M → N} (hld : IsLocalDiffeomorph I J ∞ f)
    (hpres : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = g'.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    mfderiv I J f (γ t) (covDerivAlong (I := I) g γ V t) =
      covDerivAlong (I := J) g' (fun s => f (γ s))
        (fun s => mfderiv I J f (γ s) (V s)) t := by
  classical
  obtain ⟨Φ, htΦ, hfΦ⟩ := hld (γ t)
  let U : Opens M :=
    ⟨Φ.source ∩ (chartAt H (γ t)).source,
      Φ.open_source.inter (chartAt H (γ t)).open_source⟩
  have hUΦ : (U : Set M) ⊆ Φ.source := fun _ hx => hx.1
  let Un : Opens N :=
    ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hUΦ⟩
  let Ψ : Diffeomorph I J U Un ∞ :=
    PartialDiffeomorph.toOpensDiffeo Φ hUΦ
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : SecondCountableTopology H := I.secondCountableTopology
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let e : U ≃ₜ ((chartAt H (γ t)) '' (U : Set M)) :=
    (chartAt H (γ t)).homeomorphOfImageSubsetSource (fun _ hy => hy.2) rfl
  let : SecondCountableTopology U := e.secondCountableTopology
  let : SigmaCompactSpace U := inferInstance
  let : SigmaCompactSpace Un := isSigmaCompact_iff_sigmaCompactSpace.mp
    (isSigmaCompact_iff_isSigmaCompact_univ.mpr (by
      simpa using isSigmaCompact_univ.image Ψ.toHomeomorph.continuous))
  let γtU : U := ⟨γ t, htΦ, mem_chart_source H (γ t)⟩
  let γU : ℝ → U := fun s =>
    if hs : γ s ∈ (U : Set M) then ⟨γ s, hs⟩ else γtU
  let VU : ∀ s, TangentSpace I (γU s) := fun s => V s
  have hmem : ∀ᶠ s in 𝓝 t, γ s ∈ (U : Set M) :=
    hγ.continuousAt.preimage_mem_nhds (U.isOpen.mem_nhds γtU.property)
  have hγU_val : (fun s => ((γU s : U) : M)) =ᶠ[𝓝 t] γ := by
    filter_upwards [hmem] with s hs
    simp only [γU, dite_eq_left hs]
  have hγU_smooth : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γU t := by
    have hamb : ContMDiffAt 𝓘(ℝ, ℝ) I ∞
        (fun s => ((γU s : U) : M)) t :=
      hγ.congr_of_eventuallyEq hγU_val
    have hcod := codRestr_contMDiffAt
      (I := 𝓘(ℝ, ℝ)) (J := I) (V := U)
      (f := fun s => ((γU s : U) : M))
      (fun s => (γU s).property) hamb
    simpa only [Subtype.coe_eta] using hcod
  have hΦmfd : ∀ x : U,
      mfderiv I J (Φ : M → N) (x : M) = mfderiv I J f (x : M) := by
    intro x
    have heq : f =ᶠ[𝓝 (x : M)] (Φ : M → N) :=
      Filter.eventuallyEq_of_mem
        (Φ.open_source.mem_nhds x.property.1) hfΦ
    exact heq.mfderiv_eq.symm
  have hmetric :
      g.restrictOpen (I := I) U =
        Diffeomorph.pullbackMetricCross (I := I) (J := J)
          (g'.restrictOpen (I := J) Un) Ψ := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    dsimp only [Ψ]
    rw [SmoothRiemannianMetric.restrictOpen_inner,
      Diffeomorph.pullbackMetricCross_inner,
      SmoothRiemannianMetric.restrictOpen_inner,
      PartialDiffeomorph.mfderiv_toOpensDiffeo,
      PartialDiffeomorph.mfderiv_toOpensDiffeo,
      hΦmfd x]
    change g.inner (x : M) v w =
      g'.inner ((Ψ x : Un) : N)
        (mfderiv I J f (x : M) v) (mfderiv I J f (x : M) w)
    have hval : ((Ψ x : Un) : N) = f (x : M) := by
      change (Φ : M → N) (x : M) = f (x : M)
      exact (hfΦ x.property.1).symm
    rw [hval]
    exact hpres (x : M) v w
  have hVU : DifferentiableAt ℝ (chartRepAt (I := I) γU VU t) t := by
    have h1 : chartRepAt (I := I) γU VU t =ᶠ[𝓝 t]
        chartRepAt (I := I) (fun s => ((γU s : U) : M)) VU t := by
      have hn : ∀ᶠ s in 𝓝 t,
          ((γU s : U) : M) ∈ (chartAt H ((γU t : U) : M)).source :=
        (((continuous_subtype_val.continuousAt.comp hγU_smooth.continuousAt).tendsto).eventually
          ((chartAt H ((γU t : U) : M)).open_source.mem_nhds
            (mem_chart_source H ((γU t : U) : M))))
      filter_upwards [hn] with s hs
      change (trivializationAt E (TangentSpace I (M := U)) (γU t)).continuousLinearMapAt
          ℝ (γU s) (VU s) =
        (trivializationAt E (TangentSpace I (M := M)) ((γU t : U) : M)).continuousLinearMapAt
          ℝ ((γU s : U) : M) (VU s)
      exact congrArg (fun L => L (VU s))
        (tangent_trivialization_open (I := I) U (γU t) (γU s) hs)
    have h2 : chartRepAt (I := I) (fun s => ((γU s : U) : M)) VU t =ᶠ[𝓝 t]
        chartRepAt (I := I) γ V t :=
      chartRep_congr_curve (I := I)
        (γ := fun s => ((γU s : U) : M)) (γ' := γ) VU V hγU_val
        (Filter.Eventually.of_forall fun _ => rfl)
    exact ((h1.trans h2).differentiableAt_iff).mpr hV
  have hnat := covAlong_natCrossAt (I := I) (J := J)
    (g'.restrictOpen (I := J) Un) Ψ γU VU t hγU_smooth hVU
  have hleft : (covDerivAlong (I := I) g γ V t : E) =
      (covDerivAlong (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J)
          (g'.restrictOpen (I := J) Un) Ψ) γU VU t : E) := by
    rw [← hmetric]
    rw [DifferentialGeometry.Geometry.covDerivAlong_restrictOpen g U γU VU t
      hγU_smooth.continuousAt]
    exact covDerivAlong_congr_curve (I := I) (γ := γ) (γ' := Subtype.val ∘ γU) g V
      (fun s => VU s) hγU_val.symm
      (Filter.Eventually.of_forall fun _ => rfl)
  have hΨmf : mfderiv I J f (γ t) = mfderiv I J (Ψ : U → Un) (γU t) := by
    ext v
    change mfderiv I J f (γ t) v =
      mfderiv I J (PartialDiffeomorph.toOpensDiffeo Φ hUΦ : U → Un) (γU t) v
    rw [PartialDiffeomorph.mfderiv_toOpensDiffeo Φ hUΦ (γU t) v]
    rw [show ((γU t : U) : M) = γ t from hγU_val.eq_of_nhds, hΦmfd γtU]
    rfl
  have hfield : ∀ᶠ s in 𝓝 t,
      ((mfderiv I J (Ψ : U → Un) (γU s) (VU s)) : F) =
        ((mfderiv I J f (γ s) (V s)) : F) := by
    filter_upwards [hmem] with s hs
    rw [PartialDiffeomorph.mfderiv_toOpensDiffeo Φ hUΦ (γU s) (VU s)]
    rw [show ((γU s : U) : M) = γ s from by simp only [γU, dite_eq_left hs],
      hΦmfd ⟨γ s, hs⟩]
    rfl
  have hcont : ContinuousAt (fun s : ℝ => Ψ (γU s)) t :=
    Ψ.contMDiff_toFun.continuous.continuousAt.comp hγU_smooth.continuousAt
  have hmap : (fun s => ((Ψ (γU s) : Un) : N)) =ᶠ[𝓝 t] (fun s => f (γ s)) := by
    filter_upwards [hmem] with s hs
    dsimp only [Ψ]
    have hγUs : ((γU s : U) : M) = γ s := by simp only [γU, dite_eq_left hs]
    change (Φ : M → N) ((γU s : U) : M) = f (γ s)
    rw [hγUs]
    exact (hfΦ hs.1).symm
  let A : TangentSpace I (γU t) := covDerivAlong (I := I)
    (Diffeomorph.pullbackMetricCross (I := I) (J := J)
      (g'.restrictOpen (I := J) Un) Ψ) γU VU t
  let Wt : ∀ s, TangentSpace J (Ψ (γU s)) :=
    fun s => mfderiv I J (Ψ : U → Un) (γU s) (VU s)
  have hstep1 : mfderiv I J f (γ t) (covDerivAlong (I := I) g γ V t) =
      mfderiv I J (Ψ : U → Un) (γU t) A := by
    rw [hleft, hΨmf]
    rfl
  have hstep2 : mfderiv I J (Ψ : U → Un) (γU t) A =
      covDerivAlong (I := J) (g'.restrictOpen (I := J) Un)
        (fun s => Ψ (γU s)) Wt t := hnat
  have hstep3 : covDerivAlong (I := J) (g'.restrictOpen (I := J) Un)
        (fun s => Ψ (γU s)) Wt t =
      covDerivAlong (I := J) g' (fun s => ((Ψ (γU s) : Un) : N)) Wt t :=
    DifferentialGeometry.Geometry.covDerivAlong_restrictOpen g' Un
      (fun s => Ψ (γU s)) Wt t hcont
  have hstep4 : covDerivAlong (I := J) g' (fun s => ((Ψ (γU s) : Un) : N)) Wt t =
      covDerivAlong (I := J) g' (fun s => f (γ s))
        (fun s => mfderiv I J f (γ s) (V s)) t :=
    covDerivAlong_congr_curve (I := J) g'
      (γ := fun s => ((Ψ (γU s) : Un) : N))
      (γ' := fun s => f (γ s)) Wt
      (fun s => mfderiv I J f (γ s) (V s)) hmap hfield
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace F] [NeZero (Module.finrank ℝ F)] in
theorem covDerivAlong_map_localPullMetric
    [I.Boundaryless] [J.Boundaryless]
    [T2Space M] [BoundarylessManifold I M]
    [T2Space N] [BoundarylessManifold J N]
    (g : SmoothRiemannianMetric J N) {f : M → N} (hld : IsLocalDiffeomorph I J ∞ f)
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    mfderiv I J f (γ t)
        (covDerivAlong (I := I) (localPullMetric (I := I) (J := J) g f hld) γ V t) =
      covDerivAlong (I := J) g (fun s => f (γ s))
        (fun s => mfderiv I J f (γ s) (V s)) t :=
  covDerivAlong_map_localIso (I := I) (J := J)
    (localPullMetric (I := I) (J := J) g f hld) g hld
    (fun x v w => localPullMetric_inner (I := I) (J := J) g f hld x v w) γ V t hγ hV

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace F] [NeZero (Module.finrank ℝ F)] in
theorem covDerivAlong_map_of_eq_localPullMetric
    [I.Boundaryless] [J.Boundaryless]
    [T2Space M] [BoundarylessManifold I M]
    [T2Space N] [BoundarylessManifold J N]
    (g : SmoothRiemannianMetric J N) {f : M → N} (hld : IsLocalDiffeomorph I J ∞ f)
    (k : SmoothRiemannianMetric I M)
    (hk : localPullMetric (I := I) (J := J) g f hld = k)
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    mfderiv I J f (γ t) (covDerivAlong (I := I) k γ V t) =
      covDerivAlong (I := J) g (fun s => f (γ s))
        (fun s => mfderiv I J f (γ s) (V s)) t := by
  subst hk
  exact covDerivAlong_map_localPullMetric (I := I) (J := J) g hld γ V t hγ hV

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace F] [NeZero (Module.finrank ℝ F)] in
theorem covDerivAlong_map_localIso_id_witness
    (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    mfderiv I I (_root_.id : M → M) (γ t) (covDerivAlong (I := I) g γ V t) =
      covDerivAlong (I := I) g (fun s => _root_.id (γ s))
        (fun s => mfderiv I I (_root_.id : M → M) (γ s) (V s)) t := by
  simp only [mfderiv_id, ContinuousLinearMap.id_apply]
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace F] [NeZero (Module.finrank ℝ F)] in
theorem covDerivAlong_restrictOpen_witness
    [I.Boundaryless] (g : SmoothRiemannianMetric I M) (U : Opens M) [T2Space U]
    (γ : ℝ → U) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) (hγ : ContinuousAt γ t) :
    mfderiv I I (Subtype.val : U → M) (γ t)
        (covDerivAlong (I := I) (g.restrictOpen U) γ V t) =
      covDerivAlong (I := I) g (fun s => ((γ s : U) : M))
        (fun s => mfderiv I I (Subtype.val : U → M) (γ s) (V s)) t := by
  rw [DifferentialGeometry.Geometry.covDerivAlong_restrictOpen g U γ V t hγ]
  have houter : mfderiv I I (Subtype.val : U → M) (γ t)
      (covDerivAlong (I := I) g (Subtype.val ∘ γ) (fun s => V s) t) =
      covDerivAlong (I := I) g (Subtype.val ∘ γ) (fun s => V s) t :=
    mfderiv_subtype_val_apply (I := I) U (γ t) _
  have hfield : (fun s => mfderiv I I (Subtype.val : U → M) (γ s) (V s)) =
      fun s => V s :=
    funext fun s => mfderiv_subtype_val_apply (I := I) U (γ s) (V s)
  rw [houter, hfield]
  rfl

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

end

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

open Bundle Filter Set TopologicalSpace
open scoped Manifold ContDiff Topology

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

theorem covDerivAlong_map_of_local_isometry_on
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : IsLocalDiffeomorphOn I J ∞ f U)
    (hmetric : ∀ (x : M), x ∈ U → ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (gamma : ℝ → M) (V : ∀ s, TangentSpace I (gamma s)) {t : ℝ}
    (ht : gamma t ∈ U) (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ gamma t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) gamma V t) t) :
    mfderiv I J f (gamma t) (covDerivAlong g gamma V t) =
      covDerivAlong h (fun s ↦ f (gamma s))
        (fun s ↦ mfderiv I J f (gamma s) (V s)) t := by
  classical
  let O : Opens M := ⟨U, hU⟩
  let gammaO : ℝ → O := fun s ↦
    if hs : gamma s ∈ U then ⟨gamma s, hs⟩ else ⟨gamma t, ht⟩
  let VO : ∀ s, TangentSpace I (gammaO s) := fun s ↦ V s
  have hmem : ∀ᶠ s in 𝓝 t, gamma s ∈ U :=
    hgamma.continuousAt.preimage_mem_nhds (hU.mem_nhds ht)
  have heq : (fun s ↦ (gammaO s : M)) =ᶠ[𝓝 t] gamma := by
    filter_upwards [hmem] with s hs
    simp only [gammaO, dite_eq_left hs]
  have hgammaO : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ gammaO t := by
    have hamb : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun s ↦ (gammaO s : M)) t :=
      hgamma.congr_of_eventuallyEq heq
    simpa only [Subtype.coe_eta] using
      codRestr_contMDiffAt (I := 𝓘(ℝ, ℝ)) (J := I) (V := O)
        (fun s ↦ (gammaO s).property) hamb
  have hfO : IsLocalDiffeomorph I J ∞ (fun x : O ↦ f (x : M)) :=
    DifferentialGeometry.isLocalDiffeomorph_restrict_open O hf
  have hmetricO (x : O) (v w : TangentSpace I x) :
      (g.restrictOpen O).inner x v w =
        h.inner (f x) (mfderiv I J (fun y : O ↦ f (y : M)) x v)
          (mfderiv I J (fun y : O ↦ f (y : M)) x w) := by
    change g.inner (x : M) v w = _
    rw [DifferentialGeometry.mfderiv_restrict_open (I := I) (J := J) f O x]
    exact hmetric x x.2 v w
  have hVO : DifferentiableAt ℝ (chartRepAt (I := I) gammaO VO t) t := by
    have hchart : chartRepAt (I := I) gammaO VO t =ᶠ[𝓝 t]
        chartRepAt (I := I) (fun s ↦ (gammaO s : M)) VO t := by
      have hn : ∀ᶠ s in 𝓝 t,
          (gammaO s : M) ∈ (chartAt H (gammaO t : M)).source :=
        (continuous_subtype_val.continuousAt.comp hgammaO.continuousAt).eventually
          ((chartAt H (gammaO t : M)).open_source.mem_nhds
            (mem_chart_source H (gammaO t : M)))
      filter_upwards [hn] with s hs
      have hsub : gammaO s ∈ (chartAt H (gammaO t)).source := by
        rw [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
        exact hs
      change (trivializationAt E (TangentSpace I (M := O)) (gammaO t)).continuousLinearMapAt
          ℝ (gammaO s) (VO s) =
        (trivializationAt E (TangentSpace I (M := M)) (gammaO t : M)).continuousLinearMapAt
          ℝ (gammaO s : M) (VO s)
      rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hsub,
        TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hs,
        tangentCoordChange_opens (gammaO s) (gammaO t) (gammaO s)
          (mem_chart_source H (gammaO s : M))]
      rfl
    have hrep := chartRep_congr_curve (I := I)
      (γ := fun s ↦ (gammaO s : M)) (γ' := gamma) VO V heq
      (Eventually.of_forall fun _ ↦ rfl)
    exact ((hchart.trans hrep).differentiableAt_iff).mpr hV
  have hnat := covDerivAlong_map_localIso (g.restrictOpen O) h hfO hmetricO
    gammaO VO t hgammaO hVO
  have hleft : (covDerivAlong (g.restrictOpen O) gammaO VO t : E) =
      covDerivAlong g gamma V t :=
    (DifferentialGeometry.Geometry.covDerivAlong_restrictOpen g O gammaO VO t
      hgammaO.continuousAt).trans
        (covDerivAlong_congr_curve g VO V heq (Eventually.of_forall fun _ ↦ rfl))
  have hmf : (mfderiv I J (fun x : O ↦ f (x : M)) (gammaO t) : E →L[ℝ] F) =
      (mfderiv I J f (gamma t) : E →L[ℝ] F) := by
    have hrestrict : (mfderiv I J (fun x : O ↦ f (x : M)) (gammaO t) : E →L[ℝ] F) =
        (mfderiv I J f (gammaO t : M) : E →L[ℝ] F) :=
      DifferentialGeometry.mfderiv_restrict_open (I := I) (J := J) f O (gammaO t)
    have hpoint : (mfderiv I J f (gammaO t : M) : E →L[ℝ] F) =
        (mfderiv I J f (gamma t) : E →L[ℝ] F) := by
      congr 1
      exact heq.eq_of_nhds
    exact hrestrict.trans hpoint
  have hmap : (fun s ↦ f (gammaO s : M)) =ᶠ[𝓝 t] (fun s ↦ f (gamma s)) := by
    filter_upwards [heq] with s hs
    exact congrArg f hs
  have hfield : ∀ᶠ s in 𝓝 t,
      (mfderiv I J (fun x : O ↦ f (x : M)) (gammaO s) (VO s) : F) =
        mfderiv I J f (gamma s) (V s) := by
    filter_upwards [heq] with s hs
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact congrArg (fun x : M ↦ mfderiv I J f x (V s)) hs
  have hright := covDerivAlong_congr_curve h
    (fun s ↦ mfderiv I J (fun x : O ↦ f (x : M)) (gammaO s) (VO s))
    (fun s ↦ mfderiv I J f (gamma s) (V s)) hmap hfield
  have hstart : (mfderiv I J f (gamma t) (covDerivAlong g gamma V t) : F) =
      mfderiv I J (fun x : O ↦ f (x : M)) (gammaO t)
        (covDerivAlong (g.restrictOpen O) gammaO VO t) := by
    exact (congrArg (fun z : E ↦ (mfderiv I J f (gamma t) z : F)) hleft.symm).trans
      (congrArg (fun L : E →L[ℝ] F ↦ L (covDerivAlong (g.restrictOpen O) gammaO VO t))
        hmf.symm)
  exact hstart.trans (hnat.trans hright)

theorem covDerivAlong_velocity_map_of_local_isometry_on
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : IsLocalDiffeomorphOn I J ∞ f U)
    (hmetric : ∀ (x : M), x ∈ U → ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (gamma : ℝ → M) {t : ℝ} (ht : gamma t ∈ U)
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ gamma t) :
    mfderiv I J f (gamma t)
        (covDerivAlong g gamma (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I gamma s 1) t) =
      covDerivAlong h (fun s ↦ f (gamma s))
        (fun s ↦ mfderiv 𝓘(ℝ, ℝ) J (fun r ↦ f (gamma r)) s 1) t := by
  have hgamma₂ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 gamma t := hgamma.of_le
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hnat := covDerivAlong_map_of_local_isometry_on g h hU hf hmetric gamma
    (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I gamma s 1) ht hgamma
    (differentiableAt_chartRepAt_curveVelocity hgamma₂)
  have hmem : ∀ᶠ s in 𝓝 t, gamma s ∈ U :=
    hgamma.continuousAt.preimage_mem_nhds (hU.mem_nhds ht)
  have hdiff : ∀ᶠ s in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) I gamma s := by
    filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hgamma₂]
      with s hs
    exact hs.mdifferentiableAt (by decide)
  have hfield : ∀ᶠ s in 𝓝 t,
      (mfderiv I J f (gamma s) (mfderiv 𝓘(ℝ, ℝ) I gamma s 1) : F) =
        mfderiv 𝓘(ℝ, ℝ) J (fun r ↦ f (gamma r)) s 1 := by
    filter_upwards [hmem, hdiff] with s hs hds
    exact (mfderiv_comp_apply s ((hf ⟨gamma s, hs⟩).mdifferentiableAt (by simp)) hds 1).symm
  exact hnat.trans (covDerivAlong_congr_curve h
    (fun s ↦ mfderiv I J f (gamma s) (mfderiv 𝓘(ℝ, ℝ) I gamma s 1))
    (fun s ↦ mfderiv 𝓘(ℝ, ℝ) J (fun r ↦ f (gamma r)) s 1)
    (EventuallyEq.refl _ _) hfield)

theorem covDerivAlong_velocity_norm_map_of_local_isometry_on
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : IsLocalDiffeomorphOn I J ∞ f U)
    (hmetric : ∀ (x : M), x ∈ U → ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (gamma : ℝ → M) {t : ℝ} (ht : gamma t ∈ U)
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ gamma t) :
    Real.sqrt (h.inner (f (gamma t))
      (covDerivAlong h (fun s ↦ f (gamma s))
        (fun s ↦ mfderiv 𝓘(ℝ, ℝ) J (fun r ↦ f (gamma r)) s 1) t)
      (covDerivAlong h (fun s ↦ f (gamma s))
        (fun s ↦ mfderiv 𝓘(ℝ, ℝ) J (fun r ↦ f (gamma r)) s 1) t)) =
      Real.sqrt (g.inner (gamma t)
        (covDerivAlong g gamma (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I gamma s 1) t)
        (covDerivAlong g gamma (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I gamma s 1) t)) := by
  have hnat := covDerivAlong_velocity_map_of_local_isometry_on g h hU hf hmetric gamma ht hgamma
  rw [← hnat, ← hmetric (gamma t) ht]

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

end

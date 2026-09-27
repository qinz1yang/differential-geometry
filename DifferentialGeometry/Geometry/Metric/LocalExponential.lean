import DifferentialGeometry.Geometry.Geodesic.Naturality.LocalIsometry.Geodesic
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NeZero (Module.finrank ℝ F)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N] [BoundarylessManifold J N]

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem geoEq_restrictOpen_iff (g : SmoothRiemannianMetric I M)
    (U : Opens M) (γ : ℝ → U) (t : ℝ) :
    HasGeodesicEquationAt (g.restrictOpen U) γ t ↔
      HasGeodesicEquationAt g (fun s => (γ s : M)) t := by
  simpa only [IsGeodesicOn, mem_singleton_iff, forall_eq] using
    (geodesicOn_open_iff g U γ ({t} : Set ℝ))

omit [NeZero (Module.finrank ℝ F)] in
private theorem geoEq_map_partialIso (g : SmoothRiemannianMetric I M)
    (g' : SmoothRiemannianMetric J N) (Φ : PartialDiffeomorph I J M N ∞)
    (U : Opens M) (hU : (U : Set M) ⊆ Φ.source)
    (hpres : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      g.inner x v w = g'.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    {γ : ℝ → M} {t : ℝ} (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t)
    (hγt : γ t ∈ U) (hgeo : HasGeodesicEquationAt g γ t) :
    HasGeodesicEquationAt g' (fun s => Φ (γ s)) t := by
  classical
  let V : Opens N := ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  let Ψ : Diffeomorph I J U V ∞ := PartialDiffeomorph.toOpensDiffeo Φ hU
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen J V.isOpen)
  let γU : ℝ → U := fun s => if hs : γ s ∈ U then ⟨γ s, hs⟩ else ⟨γ t, hγt⟩
  have hmem : ∀ᶠ s in 𝓝 t, γ s ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (U.isOpen.mem_nhds hγt)
  have hval : (fun s => (γU s : M)) =ᶠ[𝓝 t] γ := by
    filter_upwards [hmem] with s hs
    simp only [γU, dif_pos hs]
  have hγU : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γU t := by
    have h := codRestr_contMDiffAt (V := U) (fun s => (γU s).property)
      (hγ.congr_of_eventuallyEq hval)
    simpa only [Subtype.coe_eta] using h
  have hgeoU : HasGeodesicEquationAt (g.restrictOpen U) γU t :=
    (geoEq_restrictOpen_iff g U γU t).mpr
      (HasGeodesicEquationAt.congr_of_eventuallyEq_at hval.eq_of_nhds hval hgeo)
  have hpresΨ : ∀ (x : U) (v w : TangentSpace I x),
      (g.restrictOpen U).inner x v w = (g'.restrictOpen V).inner (Ψ x)
        (mfderiv I J Ψ x v) (mfderiv I J Ψ x w) := by
    intro x v w
    rw [SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner,
      PartialDiffeomorph.mfderiv_toOpensDiffeo,
      PartialDiffeomorph.mfderiv_toOpensDiffeo]
    exact hpres x x.property v w
  have hV := geoEq_map_localIso (g.restrictOpen U) (g'.restrictOpen V)
    Ψ.isLocalDiffeomorph hpresΨ γU t hγU hgeoU
  have hN := (geoEq_restrictOpen_iff g' V (fun s => Ψ (γU s)) t).mp hV
  have heq : (fun s => Φ (γ s)) =ᶠ[𝓝 t] (fun s => (Ψ (γU s) : N)) := by
    filter_upwards [hval] with s hs
    change Φ (γ s) = Φ (γU s : M)
    exact congrArg (Φ : M → N) hs.symm
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at heq.eq_of_nhds heq hN

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : N => TangentSpace J x)]
  [PseudoEMetricSpace N] [IsRiemannianManifold J N] [CompleteSpace N]
  [IsContinuousRiemannianBundle F (fun x : N => TangentSpace J x)]

theorem map_geodesic_end_eq_expMapIntrinsic (g : SmoothRiemannianMetric I M)
    (g' : SmoothRiemannianMetric J N) (hnorm' : IsMetricNorm g')
    (Φ : PartialDiffeomorph I J M N ∞) (U : Opens M) (hU : (U : Set M) ⊆ Φ.source)
    (hpres : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      g.inner x v w = g'.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    {γ : ℝ → M} (hcont : ContinuousOn γ (Icc (-1 : ℝ) 1))
    (hgeo : IsGeodesicOn g γ (Ioo (-1 : ℝ) 1))
    (hstay : MapsTo γ (Icc (-1 : ℝ) 1) U) :
    Φ (γ 1) = expMapIntrinsic g' hnorm' (Φ (γ 0))
      (mfderiv I J Φ (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ))) := by
  have hcontMap : ContinuousOn (fun t => Φ (γ t)) (Icc (-1 : ℝ) 1) :=
    Φ.contMDiffOn_toFun.continuousOn.comp hcont (fun t ht => hU (hstay ht))
  have hgeoMap : IsGeodesicOn g' (fun t => Φ (γ t)) (Ioo (-1 : ℝ) 1) := by
    intro t ht
    exact geoEq_map_partialIso g g' Φ U hU hpres
      (isGeodesicOn_contMDiffAt_infty g isOpen_Ioo ht hgeo
        (hcont.mono Ioo_subset_Icc_self))
      (hstay (Ioo_subset_Icc_self ht)) (hgeo t ht)
  apply geo_end_eq_intr g' hnorm' (Φ (γ 0)) _ hcontMap hgeoMap rfl
  have hγ0 := (isGeodesicOn_contMDiffAt_infty g isOpen_Ioo
    (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1) hgeo
    (hcont.mono Ioo_subset_Icc_self)).mdifferentiableAt (by decide)
  have hΦ0 := Φ.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    (hU (hstay (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1)))
  exact congrArg (fun D => D (1 : ℝ)) (mfderiv_comp 0 hΦ0 hγ0)

variable [NeZero (Module.finrank ℝ E)]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem expMapIntrinsic_map_partialIso (g : SmoothRiemannianMetric I M)
    (g' : SmoothRiemannianMetric J N) (hnorm : IsMetricNorm g) (hnorm' : IsMetricNorm g')
    (Φ : PartialDiffeomorph I J M N ∞) (U : Opens M) (hU : (U : Set M) ⊆ Φ.source)
    (hpres : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      g.inner x v w = g'.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    (p : M) (v : TangentSpace I p)
    (hstay : MapsTo (intrinsicGeodesic g hnorm p v) (Icc (-1 : ℝ) 1) U) :
    Φ (expMapIntrinsic g hnorm p v) =
      expMapIntrinsic g' hnorm' (Φ p) (mfderiv I J Φ p v) := by
  have h := map_geodesic_end_eq_expMapIntrinsic g g' hnorm' Φ U hU hpres
    (intrinsicGeodesic_continuous g hnorm p v).continuousOn
    ((intrinsicGeodesic_isGeodesic g hnorm p v).isGeodesicOn _) hstay
  let endpoint : M → E → N := fun q w =>
    expMapIntrinsic g' hnorm' (Φ q) (mfderiv I J Φ q (show TangentSpace I q from w))
  have hfinish := congrArg₂ endpoint (intrinsicGeodesic_zero g hnorm p v)
    (intrinsicGeodesic_mfderiv_zero g hnorm p v)
  exact h.trans hfinish

end DifferentialGeometry.Geometry.Riemannian

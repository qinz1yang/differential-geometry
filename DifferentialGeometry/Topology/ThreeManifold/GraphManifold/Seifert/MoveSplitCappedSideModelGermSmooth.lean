import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelGermSolid

/-!
# Smoothness of the capped solid tori up to the boundary

Lane N2f, side model, step 7 (germ smoothness). The embedding of the filling disc into `ℂ` is an
immersion between surfaces, so its differential is bijective at every point
(`bijective_mfderiv_embedding`); at interior points `germSolid` is `solMap` after this embedding, a
local diffeomorphism. Near the boundary circle `germSolid` is the side collar of the port in the
cut carrier, read through the inverse collar chart of the disc and the holonomy (`collarY`),
followed by the cut map (bijective differential) and the core map (a local diffeomorphism at these
core points). Hence `germSolid` is smooth with bijective differential at every point, boundary
points included (`contMDiff_germSolid`, `bijective_mfderiv_germSolid`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.ElementaryPresentation

open SplitTube

theorem bijective_mfderiv_of_localDiffeo {E' H' M' F' G' N' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] [NormedAddCommGroup F'] [NormedSpace ℝ F'] [TopologicalSpace G']
    {J : ModelWithCorners ℝ F' G'} [TopologicalSpace N'] [ChartedSpace G' N']
    {f : M' → N'} {x : M'} (hf : IsLocalDiffeomorphAt I J ∞ f x) :
    Bijective (mfderiv I J f x) := by
  rw [← hf.mfderivToContinuousLinearEquiv_coe (by simp)]
  exact (hf.mfderivToContinuousLinearEquiv (by simp)).bijective

theorem bijective_mfderiv_embedding (x : (discPlanarBase.{u} 1).surface.Carrier) :
    Bijective (mfderiv (SurfaceModel.model (discPlanarBase.{u} 1).surface.kind) 𝓘(ℝ, ℂ)
      (discPlanarBase.{u} 1).embedding x) := by
  have hinj :=
    ((discPlanarBase.{u} 1).isSmoothEmbedding.isImmersion.isImmersionAt x).mfderiv_injective
      (by simp)
  refine ⟨hinj, ?_⟩
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = Module.finrank ℝ ℂ := by
    rw [finrank_euclideanSpace_fin, Complex.finrank_real_complex]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
    (f := (mfderiv (SurfaceModel.model (discPlanarBase.{u} 1).surface.kind) 𝓘(ℝ, ℂ)
      (discPlanarBase.{u} 1).embedding x : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ).toLinearMap)).mp
    hinj

theorem contMDiff_embedding :
    ContMDiff (SurfaceModel.model (discPlanarBase.{u} 1).surface.kind) 𝓘(ℝ, ℂ) ∞
      (discPlanarBase.{u} 1).embedding :=
  (discPlanarBase.{u} 1).isSmoothEmbedding.contMDiff

theorem contMDiff_embeddingProd :
    ContMDiff ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1))
      (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞ (Prod.map (discPlanarBase.{u} 1).embedding (id : Circle → Circle)) :=
  contMDiff_embedding.prodMap contMDiff_id

theorem bijective_mfderiv_embeddingProd (q : (discPlanarBase.{u} 1).surface.Carrier × Circle) :
    Bijective (mfderiv ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1))
      (𝓘(ℝ, ℂ).prod (𝓡 1)) (Prod.map (discPlanarBase.{u} 1).embedding (id : Circle → Circle))
        q) := by
  rw [mfderiv_prodMap (contMDiff_embedding.mdifferentiableAt (by simp))
    (mdifferentiableAt_id), mfderiv_id]
  exact (bijective_mfderiv_embedding q.1).prodMap bijective_id

theorem embedding_eq_of_mem_target {x : (discPlanarBase.{u} 1).surface.Carrier}
    (hx : x ∈ ((discPlanarBase.{u} 1).collar 0).target) :
    (discPlanarBase.{u} 1).embedding x =
      (3 - 3 * (((discPlanarBase.{u} 1).collar 0).symm x).2.val 0 / 2 : ℝ) •
        ((((discPlanarBase.{u} 1).collar 0).symm x).1 : ℂ) := by
  set σ := ((discPlanarBase.{u} 1).collar 0).symm x with hσ
  have hsrc : σ ∈ ((discPlanarBase.{u} 1).collar 0).source :=
    ((discPlanarBase.{u} 1).collar 0).map_target hx
  have hxe : (discPlanarBase.{u} 1).collar 0 σ = x :=
    ((discPlanarBase.{u} 1).collar 0).right_inv hx
  have h1 : σ.2.val 0 < 1 := hsrc
  conv_lhs => rw [← hxe, show σ = (σ.1, halfPoint (σ.2.val 0) σ.2.2) by
    rw [halfPoint_coord]]
  exact embedding_collar.{u} σ.1 σ.2.2 h1


section Chart

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)

theorem bijective_mfderiv_cutMap' (x : E.toTorus.cutCarrier.Carrier) :
    Bijective (mfderiv E.toTorus.cutCarrier.model (NoCuts.carrier Q).model E.toTorus.cutMap x) := by
  obtain ⟨L, hL, -⟩ := E.toTorus.quotient_oriented x
  have he : (mfderiv E.toTorus.cutCarrier.model (NoCuts.carrier Q).model E.toTorus.cutMap x :
      _ → _) = L := funext fun v => (hL v).symm
  rw [he]
  exact L.bijective

def sideCollarHol : ((Circle × EuclideanHalfSpace 1) × Circle) ≃ₘ⟮circleCollarModel.prod (𝓡 1),
    halfCollarModel⟯ (Torus × EuclideanHalfSpace 1) :=
  collarHol ((E.splitCharts h hlin).e₀ * (E.splitCharts h hlin).d) (E.splitCharts h hlin).e₁
    (E.splitCharts h hlin).he₁

def collarY (t : Bool) (q : (discPlanarBase.{u} 1).surface.Carrier × Circle) :
    E.toTorus.cutCarrier.Carrier :=
  E.toTorus.sideCollar (E.portSide' h t)
    (E.sideCollarHol h hlin (((discPlanarBase.{u} 1).collar 0).symm q.1, q.2))

theorem isLocalDiffeomorphAt_collarY (t : Bool)
    {q : (discPlanarBase.{u} 1).surface.Carrier × Circle}
    (hq : q.1 ∈ ((discPlanarBase.{u} 1).collar 0).target) :
    IsLocalDiffeomorphAt ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1))
      E.toTorus.cutCarrier.model ∞ (E.collarY h hlin t) q := by
  have a1 : IsLocalDiffeomorphAt
      ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1))
      (circleCollarModel.prod (𝓡 1)) ∞
      (Prod.map ((discPlanarBase.{u} 1).collar 0).symm (id : Circle → Circle)) q :=
    (((discPlanarBase.{u} 1).collar 0).symm.isLocalDiffeomorphAt _ _ ∞ hq).prodMap
      ((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph q.2)
  have a2 := a1.comp _ _ ((E.sideCollarHol h hlin).isLocalDiffeomorph _)
  have hsrc : E.sideCollarHol h hlin (((discPlanarBase.{u} 1).collar 0).symm q.1, q.2) ∈
      (E.toTorus.sideCollar (E.portSide' h t)).source := by
    rw [E.toTorus.sideCollar_source]
    exact (show (((discPlanarBase.{u} 1).collar 0).symm q.1).2.val 0 < 1 from
      ((discPlanarBase.{u} 1).collar 0).map_target hq)
  exact a2.comp _ _ ((E.toTorus.sideCollar (E.portSide' h t)).isLocalDiffeomorphAt _ _ ∞ hsrc)

theorem liftMap_eq_collarY (t : Bool) {q : (discPlanarBase.{u} 1).surface.Carrier × Circle}
    (hq : q.1 ∈ ((discPlanarBase.{u} 1).collar 0).target)
    (hε : (((discPlanarBase.{u} 1).collar 0).symm q.1).2.val 0 < min (1 / 3) (E.splitData h).δ) :
    (E.splitCharts h hlin).liftMap t ((discPlanarBase.{u} 1).embedding q.1, q.2) =
      E.toTorus.cutMap (E.collarY h hlin t q) := by
  set σ := ((discPlanarBase.{u} 1).collar 0).symm q.1 with hσ
  rw [embedding_eq_of_mem_target hq, E.liftMap_eq_sideCollar h hlin t σ.1 q.2 σ.2.2
    (lt_of_lt_of_le hε (min_le_left _ _)) (lt_of_lt_of_le hε (min_le_right _ _)), halfPoint_coord]
  rfl

theorem norm_embedding_of_mem_target {x : (discPlanarBase.{u} 1).surface.Carrier}
    (hx : x ∈ ((discPlanarBase.{u} 1).collar 0).target) :
    ‖(discPlanarBase.{u} 1).embedding x‖ =
      3 - 3 * (((discPlanarBase.{u} 1).collar 0).symm x).2.val 0 / 2 := by
  have h1 : (((discPlanarBase.{u} 1).collar 0).symm x).2.val 0 < 1 :=
    ((discPlanarBase.{u} 1).collar 0).map_target hx
  rw [embedding_eq_of_mem_target hx, norm_three_sub_smul (by linarith)]

end Chart

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {E : ElementaryPresentation (NoCuts.carrier Q)}
  {j : Fin E.toTorus.pairing.count} {b : Bool} {h : E.IsSplitSeam j b} {hlin : E.IsLinearSeam j}
  {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N (E.splitSeamTube j b h hlin)}

variable (S : ∀ t, E.SideCap h hlin K t)

theorem germSolid_eq_comp (t : Bool) :
    germSolid S t =
      (S t).solMap ∘ Prod.map (discPlanarBase.{u} 1).embedding (id : Circle → Circle) :=
  rfl

theorem isLocalDiffeomorphAt_germSolid_interior (t : Bool)
    {q : (discPlanarBase.{u} 1).surface.Carrier × Circle}
    (h3 : ‖(discPlanarBase.{u} 1).embedding q.1‖ < 3) :
    ContMDiffAt ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1)) (𝓡 3) ∞
        (germSolid S t) q ∧
      Bijective (mfderiv ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1))
        (𝓡 3) (germSolid S t) q) := by
  have hs := (S t).isLocalDiffeomorphAt_solMap (q := ((discPlanarBase.{u} 1).embedding q.1, q.2)) h3
  rw [germSolid_eq_comp]
  refine ⟨hs.contMDiffAt.comp q contMDiff_embeddingProd.contMDiffAt, ?_⟩
  rw [mfderiv_comp q (hs.contMDiffAt.mdifferentiableAt (by simp))
    (contMDiff_embeddingProd.mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
  exact (bijective_mfderiv_of_localDiffeo hs).comp (bijective_mfderiv_embeddingProd q)

theorem germSolid_boundary (t : Bool) {q : (discPlanarBase.{u} 1).surface.Carrier × Circle}
    (h3 : ‖(discPlanarBase.{u} 1).embedding q.1‖ = 3) :
    ContMDiffAt ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1)) (𝓡 3) ∞
        (germSolid S t) q ∧
      Bijective (mfderiv ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1))
        (𝓡 3) (germSolid S t) q) := by
  set C := (discPlanarBase.{u} 1).collar 0 with hC
  set ε := min (1 / 3) (E.splitData h).δ with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (E.splitData h).hδ
  have hT : q.1 ∈ C.target := by
    change -seamDepth 1 ‖(discPlanarBase.{u} 1).embedding q.1‖ < 1
    rw [h3]
    simp [seamDepth]
  have hd0 : (C.symm q.1).2.val 0 = 0 := by
    have := norm_embedding_of_mem_target hT
    rw [h3] at this
    linarith
  set U : Set ((discPlanarBase.{u} 1).surface.Carrier × Circle) :=
    (C.target ×ˢ univ) ∩ (fun q => (C.symm q.1).2.val 0) ⁻¹' Iio ε with hU
  have hUo : IsOpen U := by
    have hc : ContinuousOn (fun q : (discPlanarBase.{u} 1).surface.Carrier × Circle =>
        (C.symm q.1).2.val 0) (C.target ×ˢ univ) := by
      have h1 : ContinuousOn (fun q : (discPlanarBase.{u} 1).surface.Carrier × Circle => C.symm q.1)
          (C.target ×ˢ univ) :=
        C.symm.toOpenPartialHomeomorph.continuousOn.comp continuous_fst.continuousOn
          fun q hq => hq.1
      have h2 : Continuous (fun σ : Circle × EuclideanHalfSpace 1 => σ.2.val 0) :=
        ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.comp
          continuous_subtype_val).comp continuous_snd
      exact h2.comp_continuousOn h1
    exact hc.isOpen_inter_preimage (C.open_target.prod isOpen_univ) isOpen_Iio
  have hqU : q ∈ U := ⟨⟨hT, trivial⟩, by
    change (C.symm q.1).2.val 0 < ε
    rw [hd0]
    exact hε⟩
  have hlev : ∀ q' ∈ U,
      3 < sgnR t * E.sideLevel h t ((discPlanarBase.{u} 1).embedding q'.1, q'.2) := by
    intro q' hq'
    have hn := norm_embedding_of_mem_target hq'.1.1
    have hd := (show (C.symm q'.1).2.val 0 < ε from hq'.2)
    have hd' : 0 ≤ (C.symm q'.1).2.val 0 := (C.symm q'.1).2.2
    have hεl : ε ≤ 1 / 3 := min_le_left _ _
    exact E.three_lt_sideLevel_of_ge h t (q := ((discPlanarBase.{u} 1).embedding q'.1, q'.2))
      (by change 5 / 2 ≤ ‖(discPlanarBase.{u} 1).embedding q'.1‖; rw [hn]; linarith)
      (norm_embedding_le q'.1)
  have heq : germSolid S t =ᶠ[𝓝 q] (coreMap K ∘ E.toTorus.cutMap ∘ E.collarY h hlin t) := by
    refine eventuallyEq_of_mem (hUo.mem_nhds hqU) fun q' hq' => ?_
    change (S t).solMap ((discPlanarBase.{u} 1).embedding q'.1, q'.2) = _
    rw [(S t).solMap_of_real (by linarith [hlev q' hq']),
      E.liftMap_eq_collarY h hlin t hq'.1.1 hq'.2]
    rfl
  have hY := E.isLocalDiffeomorphAt_collarY h hlin t hT
  have hP := E.liftMap_eq_collarY h hlin t hT (show (C.symm q.1).2.val 0 < ε by rw [hd0]; exact hε)
  have hl := hlev q hqU
  have hdom : E.sideDom h t ((discPlanarBase.{u} 1).embedding q.1, q.2) :=
    (E.sideDom_iff h).mpr ⟨norm_embedding_le q.1, by linarith⟩
  have hlev1 := one_lt_abs_sideLevel (h := h) (t := t) (by linarith)
  have hc : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (coreMap K)
      (E.toTorus.cutMap (E.collarY h hlin t q)) := by
    rw [← hP]
    exact isLocalDiffeomorphAt_coreMap K ⟨_, liftMap_mem_core hdom hlev1⟩
      (isInteriorPoint_of_forall_ne K _ fun c z => liftMap_ne_boundarySphere hdom hlev1 c z)
  have hcut : ContMDiff E.toTorus.cutCarrier.model (NoCuts.carrier Q).model ∞ E.toTorus.cutMap :=
    E.toTorus.quotient_smooth
  have hcY : ContMDiffAt ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1))
      (𝓡 3) ∞ (E.toTorus.cutMap ∘ E.collarY h hlin t) q :=
    hcut.contMDiffAt.comp q hY.contMDiffAt
  refine ⟨(hc.contMDiffAt.comp q hcY).congr_of_eventuallyEq heq, ?_⟩
  rw [heq.mfderiv_eq, mfderiv_comp q (hc.contMDiffAt.mdifferentiableAt (by simp))
    (hcY.mdifferentiableAt (by simp)), mfderiv_comp q (hcut.contMDiffAt.mdifferentiableAt (by simp))
    (hY.contMDiffAt.mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_comp]
  exact (bijective_mfderiv_of_localDiffeo hc).comp
    ((E.bijective_mfderiv_cutMap' _).comp (bijective_mfderiv_of_localDiffeo hY))

theorem germSolid_smooth_bijective (t : Bool)
    (q : (discPlanarBase.{u} 1).surface.Carrier × Circle) :
    ContMDiffAt ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1)) (𝓡 3) ∞
        (germSolid S t) q ∧
      Bijective (mfderiv ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1))
        (𝓡 3) (germSolid S t) q) := by
  rcases lt_or_eq_of_le (norm_embedding_le q.1) with h3 | h3
  · exact isLocalDiffeomorphAt_germSolid_interior S t h3
  · exact germSolid_boundary S t h3

theorem contMDiff_germSolid (t : Bool) :
    ContMDiff ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1)) (𝓡 3) ∞
      (germSolid S t) :=
  fun q => (germSolid_smooth_bijective S t q).1

theorem bijective_mfderiv_germSolid (t : Bool)
    (q : (discPlanarBase.{u} 1).surface.Carrier × Circle) :
    Bijective (mfderiv ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1))
      (𝓡 3) (germSolid S t) q) :=
  (germSolid_smooth_bijective S t q).2

end GC.Seifert.ElementaryPresentation

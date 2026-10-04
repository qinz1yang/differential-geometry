import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSideDataCover
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelGermSmooth

/-!
# The capped solid tori of a mixed split on the filling disc

Lane N2f, tier 2. The texts of `MoveSplitCappedSideModelGermSolid` and
`MoveSplitCappedSideModelGermSmooth` for a mixed split site: the solid tori `germSolid` on the
filling disc, their holonomy `sideHol`, the collar formula on the germ `s < 1/3` with width `1`
(`germSolid_collar`), injectivity, cover, image and boundary clauses, and smoothness with bijective
differential at every point, boundary points included (`contMDiff_germSolid`,
`bijective_mfderiv_germSolid`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace GC.Seifert.RelativeNormalization.MixedStage

open GC.Seifert.ElementaryPresentation (clampDisc clampPants clampDisc_val clampPants_val
  discCollar_eq pantsCollar_eq isLocalDiffeomorphAt_clampDisc isLocalDiffeomorphAt_clampPants
  sideHeight sideHeight_not sideHeight_neg seamRadius_one OnSolidBoundary neg_three_lt_sgnR_mul
  sgnR_mul_lt_three sqrt_three_half_sq sqrt_three_half_lt_one seamHeight_pos_of_lt
  seamHeight_sqrt_three_half seamHeight_neg_sqrt_three_half exists_bandHeight_eq
  abs_sgnR_mul_of_pos sgnR_false sgnR_true exists_sgnR_mul_eq_abs rank_lt_E3 germHol
  germHol_apply collarHol halfPoint_coord collarDepth_three_sub norm_three_sub_smul
  norm_embedding_le embedding_injective embedding_clampDisc embedding_collar
  onSolidBoundary_of_norm bijective_mfderiv_embedding contMDiff_embedding contMDiff_embeddingProd
  bijective_mfderiv_embeddingProd embedding_eq_of_mem_target norm_embedding_of_mem_target)

section

open SplitTube


section Collar

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {j : Fin σ.toTorus.pairing.count} {b : Bool} (h : σ.IsSplitSeam j b) (SD : σ.SplitData h)
  (hlin : σ.IsLinearSeam j)

def sideHol : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  germHol ((σ.splitCharts SD hlin).e₀ * (σ.splitCharts SD hlin).d) (σ.splitCharts SD hlin).e₁
    (σ.splitCharts SD hlin).he₁

theorem hostPt_collar_of_lt (l : Fin 3) (θ ν : Circle) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1)
    (hδ : s < (SD).δ) :
    σ.hostPt h SD (planarCollarFormula 3 l ((θ : ℂ), s)) ν =
      σ.toTorus.sideCollar
        (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 l).val
        ((θ, ν), halfPoint s hs) := by
  have hp : ((θ, ν), halfPoint s hs) ∈ halfCollarSource := hs1
  have e1 := TorusPresentation.pieceCollar_apply σ.toTorus (σ.hostPiece j b)
    (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 l) hp
  have e2 := (SD).hH l ((θ, ν), halfPoint s hs) hp hδ
  rw [← e1, e2]
  change ((SD).ΘH (clampPants (planarCollarFormula 3 l ((θ : ℂ), s)), ν) :
      σ.toTorus.cutCarrier.Carrier) =
    ((SD).ΘH (pantsPlanarBase.{u}.collar l (θ, halfPoint s hs), ν) :
      σ.toTorus.cutCarrier.Carrier)
  rw [pantsCollar_eq l hs hs1]

theorem liftMap_eq_sideCollar (t : Bool) (θ u : Circle) {s : ℝ} (hs : 0 ≤ s) (hs3 : s < 1 / 3)
    (hδ : s < (SD).δ) :
    (σ.splitCharts SD hlin).liftMap t ((3 - 3 * s / 2 : ℝ) • (θ : ℂ), u) =
      σ.toTorus.cutMap (σ.toTorus.sideCollar (σ.portSide' h t)
        (σ.sideHol h SD hlin (θ, u), halfPoint s hs)) := by
  have hn := norm_three_sub_smul (s := s) (by linarith) θ
  rw [SplitCharts.liftMap_of_gt _ t (by rw [hn]; linarith)]
  unfold SplitCharts.liftH
  rw [hn, sideData_point_collar _ t (by linarith) (by linarith), hostChart_hostInv,
    collarDepth_three_sub, unitOf_smul (by linarith) θ]
  change σ.toTorus.cutMap (σ.hostPt h SD _ _) = _
  rw [σ.hostPt_collar_of_lt h SD _ _ _ hs (by linarith) hδ]
  rfl

end Collar

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q}
  {j : Fin σ.toTorus.pairing.count} {b : Bool} {h : σ.IsSplitSeam j b} {SD : σ.SplitData h}
  {hlin : σ.IsLinearSeam j}
  {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N (σ.splitSeamTube SD hlin)}



variable (S : ∀ t, σ.SideCap h SD hlin K t)

def germSolid (t : Bool) (q : (discPlanarBase.{u} 1).surface.Carrier × Circle) : N.Carrier :=
  (S t).solMap ((discPlanarBase.{u} 1).embedding q.1, q.2)

theorem germSolid_injective (t : Bool) : Injective (germSolid S t) := by
  intro q q' he
  have e := (S t).solMap_injOn (norm_embedding_le q.1) (norm_embedding_le q'.1) he
  obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
  exact Prod.ext (embedding_injective e1) e2

theorem germSolid_collar (t : Bool) (p : Torus) (s : ℝ) (hs : 0 ≤ s) (hs3 : s < 1 / 3) :
    germSolid S t ((discPlanarBase.{u} 1).collar 0 (p.1, halfPoint s hs), p.2) =
      coreMap K (σ.hostMap SD (planarCollarFormula 3 (sidePort (σ.hostSide h) t)
        (((σ.sideHol h SD hlin p).1 : ℂ), 1 * s), (σ.sideHol h SD hlin p).2)) := by
  have hn := norm_three_sub_smul (s := s) (by linarith) p.1
  unfold germSolid
  rw [embedding_collar p.1 hs (by linarith), (S t).solMap_collar (by rw [hn]; linarith)
    (by rw [hn]; linarith), hn, collarDepth_three_sub, one_mul]
  unfold liftFib
  rw [unitOf_smul (by linarith) p.1]
  rfl

theorem germSolid_cap_mem (t : Bool) (w : ClosedCell 3) :
    ∃ q, germSolid S t q = K.cap ((), t) w := by
  obtain ⟨q, hq, he⟩ := (S t).exists_solMap_eq_cap w
  refine ⟨(clampDisc.{u} q.1, q.2), ?_⟩
  unfold germSolid
  rw [embedding_clampDisc hq]
  exact he

theorem germSolid_core_mem {y : σ.toTorus.cutCarrier.Carrier}
    (hy : σ.InSplitRegion (j := j) (b := b) y)
    (hc : σ.toTorus.cutMap y ∈ (σ.splitSeamTube SD hlin).core) :
    ∃ t q, germSolid S t q = coreMap K (σ.toTorus.cutMap y) := by
  obtain ⟨t, q, hq, he⟩ := exists_solMap_eq_of_splitRegion S hy hc
  refine ⟨t, (clampDisc.{u} q.1, q.2), ?_⟩
  unfold germSolid
  rw [embedding_clampDisc hq]
  exact he

theorem germSolid_image (t : Bool) (q : (discPlanarBase.{u} 1).surface.Carrier × Circle) :
    (∃ w, germSolid S t q = K.cap ((), t) w) ∨ ∃ y : σ.toTorus.cutCarrier.Carrier,
      σ.InSplitRegion (j := j) (b := b) y ∧
        σ.toTorus.cutMap y ∈ (σ.splitSeamTube SD hlin).core ∧
          germSolid S t q = coreMap K (σ.toTorus.cutMap y) :=
  (S t).solMap_image (norm_embedding_le q.1)

theorem germSolid_boundary_of_eq (q q' : (discPlanarBase.{u} 1).surface.Carrier × Circle)
    (he : germSolid S false q = germSolid S true q') :
    OnSolidBoundary q ∧ OnSolidBoundary q' := by
  obtain ⟨h1, h2⟩ := solMap_cross (S false) (S true) (norm_embedding_le q.1)
    (norm_embedding_le q'.1) he
  exact ⟨onSolidBoundary_of_norm h1, onSolidBoundary_of_norm h2⟩

end

section

open SplitTube

theorem bijective_mfderiv_of_localDiffeo {E' H' M' F' G' N' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] [NormedAddCommGroup F'] [NormedSpace ℝ F'] [TopologicalSpace G']
    {J : ModelWithCorners ℝ F' G'} [TopologicalSpace N'] [ChartedSpace G' N']
    {f : M' → N'} {x : M'} (hf : IsLocalDiffeomorphAt I J ∞ f x) :
    Bijective (mfderiv I J f x) := by
  rw [← hf.mfderivToContinuousLinearEquiv_coe (by simp)]
  exact (hf.mfderivToContinuousLinearEquiv (by simp)).bijective


section Chart

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {j : Fin σ.toTorus.pairing.count} {b : Bool} (h : σ.IsSplitSeam j b) (SD : σ.SplitData h)
  (hlin : σ.IsLinearSeam j)

theorem bijective_mfderiv_cutMap' (x : σ.toTorus.cutCarrier.Carrier) :
    Bijective (mfderiv σ.toTorus.cutCarrier.model (NoCuts.carrier Q).model σ.toTorus.cutMap x) := by
  obtain ⟨L, hL, -⟩ := σ.toTorus.quotient_oriented x
  have he : (mfderiv σ.toTorus.cutCarrier.model (NoCuts.carrier Q).model σ.toTorus.cutMap x :
      _ → _) = L := funext fun v => (hL v).symm
  rw [he]
  exact L.bijective

def sideCollarHol : ((Circle × EuclideanHalfSpace 1) × Circle) ≃ₘ⟮circleCollarModel.prod (𝓡 1),
    halfCollarModel⟯ (Torus × EuclideanHalfSpace 1) :=
  collarHol ((σ.splitCharts SD hlin).e₀ * (σ.splitCharts SD hlin).d) (σ.splitCharts SD hlin).e₁
    (σ.splitCharts SD hlin).he₁

def collarY (t : Bool) (q : (discPlanarBase.{u} 1).surface.Carrier × Circle) :
    σ.toTorus.cutCarrier.Carrier :=
  σ.toTorus.sideCollar (σ.portSide' h t)
    (σ.sideCollarHol h SD hlin (((discPlanarBase.{u} 1).collar 0).symm q.1, q.2))

theorem isLocalDiffeomorphAt_collarY (t : Bool)
    {q : (discPlanarBase.{u} 1).surface.Carrier × Circle}
    (hq : q.1 ∈ ((discPlanarBase.{u} 1).collar 0).target) :
    IsLocalDiffeomorphAt ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1))
      σ.toTorus.cutCarrier.model ∞ (σ.collarY h SD hlin t) q := by
  have a1 : IsLocalDiffeomorphAt
      ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1))
      (circleCollarModel.prod (𝓡 1)) ∞
      (Prod.map ((discPlanarBase.{u} 1).collar 0).symm (id : Circle → Circle)) q :=
    (((discPlanarBase.{u} 1).collar 0).symm.isLocalDiffeomorphAt _ _ ∞ hq).prodMap
      ((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph q.2)
  have a2 := a1.comp _ _ ((σ.sideCollarHol h SD hlin).isLocalDiffeomorph _)
  have hsrc : σ.sideCollarHol h SD hlin (((discPlanarBase.{u} 1).collar 0).symm q.1, q.2) ∈
      (σ.toTorus.sideCollar (σ.portSide' h t)).source := by
    rw [σ.toTorus.sideCollar_source]
    exact (show (((discPlanarBase.{u} 1).collar 0).symm q.1).2.val 0 < 1 from
      ((discPlanarBase.{u} 1).collar 0).map_target hq)
  exact a2.comp _ _ ((σ.toTorus.sideCollar (σ.portSide' h t)).isLocalDiffeomorphAt _ _ ∞ hsrc)

theorem liftMap_eq_collarY (t : Bool) {q : (discPlanarBase.{u} 1).surface.Carrier × Circle}
    (hq : q.1 ∈ ((discPlanarBase.{u} 1).collar 0).target)
    (hε : (((discPlanarBase.{u} 1).collar 0).symm q.1).2.val 0 < min (1 / 3) (SD).δ) :
    (σ.splitCharts SD hlin).liftMap t ((discPlanarBase.{u} 1).embedding q.1, q.2) =
      σ.toTorus.cutMap (σ.collarY h SD hlin t q) := by
  set ϖ := ((discPlanarBase.{u} 1).collar 0).symm q.1 with hϖ
  rw [embedding_eq_of_mem_target hq, σ.liftMap_eq_sideCollar h SD hlin t ϖ.1 q.2 ϖ.2.2
    (lt_of_lt_of_le hε (min_le_left _ _)) (lt_of_lt_of_le hε (min_le_right _ _)), halfPoint_coord]
  rfl

end Chart

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q}
  {j : Fin σ.toTorus.pairing.count} {b : Bool} {h : σ.IsSplitSeam j b} {SD : σ.SplitData h}
  {hlin : σ.IsLinearSeam j}
  {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N (σ.splitSeamTube SD hlin)}

variable (S : ∀ t, σ.SideCap h SD hlin K t)

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
  set ε := min (1 / 3) (SD).δ with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (SD).hδ
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
      have h2 : Continuous (fun ϖ : Circle × EuclideanHalfSpace 1 => ϖ.2.val 0) :=
        ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.comp
          continuous_subtype_val).comp continuous_snd
      exact h2.comp_continuousOn h1
    exact hc.isOpen_inter_preimage (C.open_target.prod isOpen_univ) isOpen_Iio
  have hqU : q ∈ U := ⟨⟨hT, trivial⟩, by
    change (C.symm q.1).2.val 0 < ε
    rw [hd0]
    exact hε⟩
  have hlev : ∀ q' ∈ U,
      3 < sgnR t * σ.sideLevel h t ((discPlanarBase.{u} 1).embedding q'.1, q'.2) := by
    intro q' hq'
    have hn := norm_embedding_of_mem_target hq'.1.1
    have hd := (show (C.symm q'.1).2.val 0 < ε from hq'.2)
    have hd' : 0 ≤ (C.symm q'.1).2.val 0 := (C.symm q'.1).2.2
    have hεl : ε ≤ 1 / 3 := min_le_left _ _
    exact σ.three_lt_sideLevel_of_ge h t (q := ((discPlanarBase.{u} 1).embedding q'.1, q'.2))
      (by change 5 / 2 ≤ ‖(discPlanarBase.{u} 1).embedding q'.1‖; rw [hn]; linarith)
      (norm_embedding_le q'.1)
  have heq : germSolid S t =ᶠ[𝓝 q] (coreMap K ∘ σ.toTorus.cutMap ∘ σ.collarY h SD hlin t) := by
    refine eventuallyEq_of_mem (hUo.mem_nhds hqU) fun q' hq' => ?_
    change (S t).solMap ((discPlanarBase.{u} 1).embedding q'.1, q'.2) = _
    rw [(S t).solMap_of_real (by linarith [hlev q' hq']),
      σ.liftMap_eq_collarY h SD hlin t hq'.1.1 hq'.2]
    rfl
  have hY := σ.isLocalDiffeomorphAt_collarY h SD hlin t hT
  have hP := σ.liftMap_eq_collarY h SD hlin t hT
    (show (C.symm q.1).2.val 0 < ε by rw [hd0]; exact hε)
  have hl := hlev q hqU
  have hdom : σ.sideDom h t ((discPlanarBase.{u} 1).embedding q.1, q.2) :=
    (σ.sideDom_iff h).mpr ⟨norm_embedding_le q.1, by linarith⟩
  have hlev1 := one_lt_abs_sideLevel (h := h) (t := t) (by linarith)
  have hc : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (coreMap K)
      (σ.toTorus.cutMap (σ.collarY h SD hlin t q)) := by
    rw [← hP]
    exact isLocalDiffeomorphAt_coreMap K ⟨_, liftMap_mem_core hdom hlev1⟩
      (isInteriorPoint_of_forall_ne K _ fun c z => liftMap_ne_boundarySphere hdom hlev1 c z)
  have hcut : ContMDiff σ.toTorus.cutCarrier.model (NoCuts.carrier Q).model ∞ σ.toTorus.cutMap :=
    σ.toTorus.quotient_smooth
  have hcY : ContMDiffAt ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1))
      (𝓡 3) ∞ (σ.toTorus.cutMap ∘ σ.collarY h SD hlin t) q :=
    hcut.contMDiffAt.comp q hY.contMDiffAt
  refine ⟨(hc.contMDiffAt.comp q hcY).congr_of_eventuallyEq heq, ?_⟩
  rw [heq.mfderiv_eq, mfderiv_comp q (hc.contMDiffAt.mdifferentiableAt (by simp))
    (hcY.mdifferentiableAt (by simp)), mfderiv_comp q (hcut.contMDiffAt.mdifferentiableAt (by simp))
    (hY.contMDiffAt.mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_comp]
  exact (bijective_mfderiv_of_localDiffeo hc).comp
    ((σ.bijective_mfderiv_cutMap' _).comp (bijective_mfderiv_of_localDiffeo hY))

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

end

end GC.Seifert.RelativeNormalization.MixedStage

import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainHprimCoreJN74
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeZeroFaceExplicitJN74

/-!
# Draft 74, the endpoint primitives at `D_R`: the face equation of a zero label

Lane S-JUNCTIONS (by S-JUNCTIONS5), G32 (suffix `_JN74`). For an endpoint `e` whose label is a
zero model face `⟨i, Fm⟩`: the face function `ratio i` (the global ratio of the zero piece `i`)
equals
`b ∘ q₁` on the face neighbourhood, with `b = zspBaseFun_ZSP35 k ∘ ι` (`k = σ i`, G20's explicit
`b_k = u_k/v_k − 2/5`), smooth near `e` (the marker `v_k` is positive along `∂Z_k`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)

/-- **The chain data of a zero label**: the zero index `k = σ i`, a point `z` of the edge source
over `e` whose chain point `y = ψ⁻¹ z` lies on `∂Z_k`, and the buffer equation
`ratio i = u_k/v_k − 2/5`
on `near i`. -/
theorem zero_label_data_JN74
    (Rw : StageCutRows74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (e : Rw.edge.EdgeEnd) (i : Fin zero.rows.count)
    (Fm : ModelBoundaryFace (zero.rows.piece i))
    (hdisk : Rw.edge.disk e.1 ⊆ (zero.rows.piece i).map '' Fm.1) :
    ∃ (k : S.ZeroIdx74) (z : Rw.edge.source), Rw.edge.proj z = e.1 ∧
      M.ψ.symm z.1 ∈ frontier (S.zeroDom74 k) ∧
      ∀ x ∈ (zero.rows.near i : Set W.Carrier),
        zero.rows.ratio i x = S.zeroUV74 k (M.ψ.symm x) := by
  obtain ⟨σ, hσ⟩ := zero.link
  obtain ⟨x₀, hx₀⟩ := Rw.disk_nonempty_JN74 e.1
  have hx₀m := hdisk hx₀
  obtain ⟨z, ⟨hzc, -⟩, rfl⟩ := hx₀
  have hbd : (z : W.Carrier) ∈ pieceBoundary (zero.rows.piece i) := by
    obtain ⟨p, hp, hpx⟩ := hx₀m
    exact ⟨p, Fm.subset hp, hpx⟩
  rw [(hσ i).2.1] at hbd
  obtain ⟨y, hy, hyz⟩ := hbd
  have hyz' : M.ψ.symm (z : W.Carrier) = y := by
    rw [← hyz]
    exact M.ψ.toEquiv.symm_apply_apply y
  exact ⟨σ i, z, hzc, hyz' ▸ hy, (hσ i).2.2.2.2.1⟩

/-- **Smoothness of the zero face equation near the endpoint**. -/
theorem zero_smooth_JN74
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (k : S.ZeroIdx74) (c₀ : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base)
    (z : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).source)
    (hzc : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).proj z = c₀)
    (hy : M.ψ.symm z.1 ∈ frontier (S.zeroDom74 k)) :
    let _ := A.edgeChartedSpace1
    ∃ U₀ : TopologicalSpace.Opens (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base, c₀ ∈ U₀ ∧
      ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun c => zspBaseFun_ZSP35 S.F.family.toLocalChartPacketsC14 k
        (S.edgeVal_JN74 B hT hεr A zero F c)) U₀ := by
  intro _
  have hv := (S.chain.toGaf02ChainE.zero_face_ratio_aux_JN74 hεr k hy).1
  let marker : CGPTag S.F.family.toLocalChartPacketsC14.toLocalChartFamily
      S.F.family.toLocalChartPacketsC14.zero := Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))
  let Nset : Set S.blockSpace_R74 := {w | (w marker).snd ≠ 0}
  have hNo : IsOpen Nset :=
    (isClosed_singleton.isOpen_compl).preimage
      (blockMarkerCLM (V := fun _ : CGPTag S.F.family.toLocalChartPacketsC14.toLocalChartFamily
        S.F.family.toLocalChartPacketsC14.zero => EuclideanSpace ℝ (Fin 2)) marker).continuous
  have hev := S.contMDiff_edgeVal_JN74 B hT hεr A zero F
  refine ⟨⟨{c | S.edgeVal_JN74 B hT hεr A zero F c ∈ Nset}, hNo.preimage hev.continuous⟩, ?_, ?_⟩
  · change (S.edgeVal_JN74 B hT hεr A zero F c₀ marker).snd ≠ 0
    rw [← hzc, S.edgeVal_proj_JN74 B hT hεr A zero F z]
    have h2 := gafStageQ_starProjection_zeroTag_GAF8 S.F.family.toLocalChartPacketsC14 1 k
      (S.chain.toChain.E (M.ψ.symm z.1))
    change ((gafStageQ S.F.family.toLocalChartPacketsC14.toLocalChartFamily
      S.F.family.toLocalChartPacketsC14.zero 1).starProjection
        (S.chain.toChain.E (M.ψ.symm z.1)) marker).snd ≠ 0
    rw [h2]
    exact hv.ne'
  · have hg : ContDiffOn ℝ ∞ (zspBaseFun_ZSP35 S.F.family.toLocalChartPacketsC14 k) Nset :=
      fun w hw => (zero_base_function_smooth_ZSP35 marker w hw).contDiffWithinAt
    exact hg.contMDiffOn.comp hev.contMDiffOn (fun c hc => hc)

/-- The retained ratio of the zero stage as an explicit quotient. -/
theorem zeroUV_eq_JN74 (k : S.ZeroIdx74) (z : M.X) :
    S.zeroUV74 k z = ((S.chain.toChain.E z (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))).fst :
        EuclideanSpace ℝ (Fin 2)) 0 /
        (S.chain.toChain.E z (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))).snd - 2 / 5 := by
  unfold ClosedChainEZRowsSource_RGC.zeroUV74
  rfl

/-- **`u_k/v_k − 2/5 = b_k ∘ π₂E`** (G20's `zeroBaseComp_eq_JN74`). -/
theorem zeroUV_comp_JN74 (k : S.ZeroIdx74) (z : M.X) :
    zspBaseFun_ZSP35 S.F.family.toLocalChartPacketsC14 k
      (S.chain.toGaf02ChainE.edgeBlockProj_EFE z) = S.zeroUV74 k z := by
  have h := S.chain.toGaf02ChainE.zeroBaseComp_eq_JN74 k z
  rw [S.zeroUV_eq_JN74 k z]
  exact h

/-- **The zero buffer equation reads `u_k/v_k − 2/5 = b_k ∘ ι ∘ q₁`** on the edge source. -/
theorem zero_eq_JN74
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (k : S.ZeroIdx74) (x : W.Carrier) (hx : x ∈ (edgeBundle74
      (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).source) :
    S.zeroUV74 k (M.ψ.symm x) = zspBaseFun_ZSP35 S.F.family.toLocalChartPacketsC14 k
      (S.edgeVal_JN74 B hT hεr A zero F ((edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut F).proj ⟨x, hx⟩)) := by
  rw [S.edgeVal_proj_JN74 B hT hεr A zero F ⟨x, hx⟩]
  exact (S.zeroUV_comp_JN74 k (M.ψ.symm x)).symm

/-- **The face equation of a zero label.** -/
theorem exists_zeroEq_JN74
    (Rw : StageCutRows74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (e : Rw.edge.EdgeEnd) (i : Fin zero.rows.count)
    (Fm : ModelBoundaryFace (zero.rows.piece i))
    (hdisk : Rw.edge.disk e.1 ⊆ (zero.rows.piece i).map '' Fm.1) :
    let _ := A.edgeChartedSpace1
    ∃ (b : Rw.edge.Base → ℝ) (U₀ : TopologicalSpace.Opens Rw.edge.Base), e.1 ∈ U₀ ∧
      ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U₀ ∧
      ∀ x (hx : x ∈ Rw.edge.source), x ∈ (zero.rows.near i : Set W.Carrier) →
        zero.rows.ratio i x = b (Rw.edge.proj ⟨x, hx⟩) := by
  intro _
  obtain ⟨k, z, hzc, hy, hbuf⟩ := S.zero_label_data_JN74 B hT hεr A zero Rw e i Fm hdisk
  obtain ⟨U₀, heU, hsm⟩ := S.zero_smooth_JN74 B hT hεr A zero Rw.edgeFacts k e.1 z hzc hy
  refine ⟨fun c => zspBaseFun_ZSP35 S.F.family.toLocalChartPacketsC14 k
    (S.edgeVal_JN74 B hT hεr A zero Rw.edgeFacts c), U₀, heU, hsm, fun x hx hn => ?_⟩
  rw [hbuf x hn]
  exact S.zero_eq_JN74 B hT hεr A zero Rw.edgeFacts k x hx

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse

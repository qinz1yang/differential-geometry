import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainHorizontalDisksJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerDescentJN74

/-!
# Draft 74, the corner descent at `D_R`: `T − 4Δ` is constant on the circle fibres

Lane S-JUNCTIONS (by S-JUNCTIONS3), G19 (suffix `_JN74`). On the produced stage geometry
`P = S.closedStagesAt_OCL B hT hεr A zero` and any rows `Rw : StageCutRows74 P.A P.cut`:

* `zero_ratio_fibreConst_JN74`: the ratio of a zero domain is a function of `E` on its
  neighbourhood (`ZeroLink_LND74`: `ratio = u_k(E)/v_k(E) − 2/5`): the face function of a ZERO face
  is constant on the `q₀`-fibres (the input `hconstH` of `cornerDescent_ofFibreConst_JN74` for zero
  labels; slim labels need the clause of HANDOVER ADDENDUM 3);
* `cornerT_fibreConst_at_JN74`: two points `x, y` of the circle domain inside the edge source on
  the same `q₀`-fibre have the same `cornerT` (`T = A/s` is determined by `E`, and `q₀ = E`):
  the input `hconstT` of `cornerDescent_ofFibreConst_JN74`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2)

/-- **`cornerT` is constant on the `q₀`-fibres** (inside the edge source). -/
theorem cornerT_fibreConst_at_JN74 (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (Rw : StageCutRows74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (x y : Rw.circle.domain) (hx : (x : W.Carrier) ∈ Rw.edge.source)
    (hy : (y : W.Carrier) ∈ Rw.edge.source) (hxy : Rw.circle.proj y = Rw.circle.proj x) :
    Rw.cornerT x = Rw.cornerT y := by
  have hπ0 := gafStageQ_zero_starProjection_BAS
    S.F.family.toLocalChartPacketsC14.toLocalChartPackets
  have hxp : (x : W.Carrier) ∈ (S.closedStagesAt_OCL B hT hεr A zero).A.circle.parent :=
    (S.closedStagesAt_OCL B hT hεr A zero).A.circle.restrictParent_le _ x.2
  have hyp : (y : W.Carrier) ∈ (S.closedStagesAt_OCL B hT hεr A zero).A.circle.parent :=
    (S.closedStagesAt_OCL B hT hεr A zero).A.circle.restrictParent_le _ y.2
  have hqx := (S.closedStagesAt_OCL B hT hεr A zero).circle_ident.proj_eq ⟨x, hxp⟩
  have hqy := (S.closedStagesAt_OCL B hT hεr A zero).circle_ident.proj_eq ⟨y, hyp⟩
  have hq : S.chain.toGaf02ChainE.cutQ_R74 0 (M.ψ.symm y) =
      S.chain.toGaf02ChainE.cutQ_R74 0 (M.ψ.symm x) :=
    hqy.symm.trans ((congrArg (fun v : (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen =>
      (S.closedStagesAt_OCL B hT hεr A zero).ιcircle v.1) hxy).trans hqx)
  have hE : S.chain.toChain.E (M.ψ.symm x) = S.chain.toChain.E (M.ψ.symm y) := by
    have h : (gafStageQ S.F.family.toLocalChartPacketsC14.toLocalChartFamily
        S.F.family.toLocalChartPacketsC14.zero 0).starProjection
          (S.chain.toChain.E (M.ψ.symm y)) =
      (gafStageQ S.F.family.toLocalChartPacketsC14.toLocalChartFamily
        S.F.family.toLocalChartPacketsC14.zero 0).starProjection
          (S.chain.toChain.E (M.ψ.symm x)) := hq
    rw [hπ0, hπ0] at h
    exact h.symm
  have hTT := (S.chain.toChain.edgeRim_data_eq_of_E_eq_EFE hE).2
  have hxe : (x : W.Carrier) ∈ (S.closedStagesAt_OCL B hT hεr A zero).A.edge.parent :=
    (S.closedStagesAt_OCL B hT hεr A zero).A.edge.restrictParent_le _ hx
  have hye : (y : W.Carrier) ∈ (S.closedStagesAt_OCL B hT hεr A zero).A.edge.parent :=
    (S.closedStagesAt_OCL B hT hεr A zero).A.edge.restrictParent_le _ hy
  have hhx := (S.closedStagesAt_OCL B hT hεr A zero).edge_height ⟨x, hxe⟩
  have hhy := (S.closedStagesAt_OCL B hT hεr A zero).edge_height ⟨y, hye⟩
  simp only [StageCutRows74.cornerT, hx, hy, ↓reduceDIte]
  have hHx : (S.closedStagesAt_OCL B hT hεr A zero).A.edge.height ⟨x, hxe⟩ =
      (S.closedStagesAt_OCL B hT hεr A zero).A.edge.height ⟨y, hye⟩ := by
    rw [hhx, hhy, S.height_eq_OCL, S.height_eq_OCL]
    exact hTT
  exact sub_left_inj.2 hHx

/-- **The ratio of a zero domain is a function of `E` near the zero domain** (`ZeroLink_LND74`). -/
theorem zero_ratio_fibreConst_JN74 (zero : ZSP02SmoothExit74 S) (i : Fin zero.rows.count)
    {x y : W.Carrier} (hx : x ∈ (zero.rows.near i : Set W.Carrier))
    (hy : y ∈ (zero.rows.near i : Set W.Carrier))
    (hE : S.chain.toChain.E (M.ψ.toEquiv.symm x) = S.chain.toChain.E (M.ψ.toEquiv.symm y)) :
    zero.rows.ratio i x = zero.rows.ratio i y := by
  obtain ⟨σ, hσ⟩ := zero.link
  rw [(hσ i).2.2.2.2.1 x hx, (hσ i).2.2.2.2.1 y hy]
  unfold ClosedChainEZRowsSource_RGC.zeroUV74
  rw [hE]

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse

import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGate6bJN74
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimM2DomainZSP35

/-!
# Draft 74, the zero faces over `D₃` are removed (`hKR`) at `D_R`

Lane S-JUNCTIONS (by S-JUNCTIONS4), G24 (suffix `_JN74`). A point of the boundary of a zero domain
whose `f₃`-image lies in `D₃` is in the relative interior of the slim set inside `M₁`:

* `zeroFrontier_slim_relInt_JN74` (chain level): `∂Z_k ∩ f₃⁻¹(D₃) ⊆ relInt_{M₁}(f₃⁻¹ D₃)` from
  ZSP05's collar clause `slimPiece ∩ ∂M₁ ⊆ relInt_{M₁} slimPiece`
  (`slim_piece_facts_ZSP35`), `∂Z_k ⊆ ∂Z ⊆ ∂M₁` (`slim_zero_domain_ZSP35`);
* `zeroFace_slim_relInt_at_JN74` (`W` level, the input `hKR` of `exists_faceModel_JN74`):
  `pieceBoundary (piece i) ∩ slimSet ⊆ relInt_{M₁} slimSet` for the zero rows of the carried stage
  geometry (ZeroLink + the transport of `M₁` and of the slim set by `M.ψ`).
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

/-- **The boundary of a zero domain over `D₃` lies in the relative interior of the slim set.** -/
theorem zeroFrontier_slim_relInt_JN74 (k : S.ZeroIdx74) :
    frontier (S.zeroDom74 k) ∩ (S.goodCut_OCL B hT hεr).slimSet ⊆
      relInt S.chain.toGaf02ChainE.cutM1_R74 (S.goodCut_OCL B hT hεr).slimSet := by
  obtain ⟨hD, hKs, hKF, -⟩ := S.chain.slimDomains_spec_OCL hεr
  have hDreg := S.goodCut_D₃_reg_OCL B hT hεr
  obtain ⟨hSD, -, -, -, -, hcollar, -, -, -⟩ := S.chain.slim_piece_facts_ZSP35 hεr
    (S.chain.slimK₃_OCL hεr) (S.chain.slimD₃_OCL hεr) hD hKs hKF hDreg
  have hcl : ∀ k : S.ZeroIdx74, IsClosed (S.zeroDom74 k) := fun k =>
    (S.chain.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).1.isClosed
  obtain ⟨hfrk, hfru⟩ := frontier_disjoint_iUnion_ZSP35 (fun k : S.ZeroIdx74 => S.zeroDom74 k) hcl
    (fun k k' hkk => S.chain.toGaf02ChainE.zsp02_disjoint_ZSP35 hεr hkk)
  obtain ⟨-, hfr2⟩ := S.chain.slim_zero_domain_ZSP35 hεr
  rintro z ⟨hzf, hzs⟩
  have hzU : z ∈ frontier S.chain.zeroUnion_ZSP35 := by
    have : z ∈ ⋃ k, frontier (S.zeroDom74 k) := mem_iUnion.2 ⟨k, hzf⟩
    exact hfru ▸ this
  have hzp : z ∈ S.chain.slimPiece_ZSP35 (S.chain.slimK₃_OCL hεr).carrier := by
    rw [hSD]
    exact hzs
  have key := hcollar ⟨hzp, hfr2 hzU⟩
  have hs : (S.goodCut_OCL B hT hεr).slimSet =
      S.chain.slimPiece_ZSP35 (S.chain.slimK₃_OCL hεr).carrier := hSD.symm
  rw [hs]
  exact key

/-- **`hKR` at `D_R`** (`W` level): `∂Z_i ∩ slimSet ⊆ relInt_{M₁} slimSet` for the zero rows. -/
theorem zeroFace_slim_relInt_at_JN74 (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (i : Fin (S.closedStagesAt_OCL B hT hεr A zero).A.zero.count) :
    pieceBoundary ((S.closedStagesAt_OCL B hT hεr A zero).A.zero.piece i) ∩
        (S.closedStagesAt_OCL B hT hεr A zero).cut.slimSet ⊆
      relInt (regionM1 (S.closedStagesAt_OCL B hT hεr A zero).A.zero
        (S.closedStagesAt_OCL B hT hεr A zero).A.cusp)
        (S.closedStagesAt_OCL B hT hεr A zero).cut.slimSet := by
  obtain ⟨σ, hσ⟩ := zero.link
  rintro x ⟨hxb, hxs⟩
  have hb : pieceBoundary (zero.rows.piece i) = M.ψ '' frontier (S.zeroDom74 (σ i)) := (hσ i).2.1
  rw [slimSet_at_OCL] at hxs
  change x ∈ pieceBoundary (zero.rows.piece i) at hxb
  rw [hb] at hxb
  obtain ⟨z, hz, rfl⟩ := hxb
  obtain ⟨z', hz's, hzz'⟩ := hxs
  have hzs : z ∈ (S.goodCut_OCL B hT hεr).slimSet := by
    rw [← M.ψ.injective hzz']
    exact hz's
  have hrel := S.zeroFrontier_slim_relInt_JN74 B hT hεr (σ i) ⟨hz, hzs⟩
  change M.ψ z ∈ relInt (regionM1 zero.rows M.cusp_R74)
    (S.closedStagesAt_OCL B hT hεr A zero).cut.slimSet
  rw [S.regionM1_at_OCL zero, S.slimSet_at_OCL B hT hεr A zero, relInt_image_R74 M.ψ]
  exact ⟨z, hrel, rfl⟩

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse

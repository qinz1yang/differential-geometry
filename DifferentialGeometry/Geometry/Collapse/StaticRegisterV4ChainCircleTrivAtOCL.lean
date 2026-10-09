import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCircleFactsAtOCL
import DifferentialGeometry.Geometry.Fibration.ActualStageChainCircleBundleBaseEFE

/-!
# Draft 74 CL0, G8b: the local circle trivializations at `D_R` (clause (f), second part)

Lane O-CL1 (`_OCL`), group G8b. The four trivialization fields of `CircleCutFacts74 P.A P.cut`
(`neighborhood`, `mem_neighborhood`, `trivialization`, `projection_trivialization`) for the
produced stage geometry `P` at `D_R`, from lane S-EDP-FDC2's `circleProj_trivial_EFE` on the actual
chain, carried to `W` by `M.ψ`:

* generic: `Diffeomorph.opensCongr_OCL` (cast along `U = U'`), `Diffeomorph.opensTop_OCL`
  (`⊤ ≃ₘ N`), and **`trivPullback_OCL`**: a local trivialization of `πX` over `Q` pulled back along
  diffeomorphisms `α` (total spaces) and `β` (bases) with `πX ∘ α = β ∘ πW`, with
  `trivPullback_OCL_proj` (the first coordinate is `πW`);
* at `D_R`: `circleParent_eq_OCL` (the carried circle source is `M.ψ(circleDomain_EFE)`),
  `circleTotal_OCL` (`α`), `circleTotal_comm_OCL`;
* **`circleCutFactsAt2_OCL`**: `CircleCutFacts74 P.A P.cut` from FDC03's saturation
  `M₃ = q₀⁻¹(C₁)` ALONE (with G8a's `proper` and `cbase_compact`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold TopologicalSpace
open scoped Manifold ContDiff Topology
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

section Generic

variable {EN HN EN' HN' : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [NormedAddCommGroup EN'] [NormedSpace ℝ EN'] [TopologicalSpace HN']
  {I : ModelWithCorners ℝ EN HN} {I' : ModelWithCorners ℝ EN' HN'} {N : Type*}
  [TopologicalSpace N] [ChartedSpace HN N]

/-- The diffeomorphism along an equality of open sets. -/
def _root_.Diffeomorph.opensCongr_OCL {U U' : Opens N} (h : U = U') : U ≃ₘ⟮I, I⟯ U' where
  toFun x := ⟨x.1, by rw [← h]; exact x.2⟩
  invFun y := ⟨y.1, by rw [h]; exact y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff U' _).mp contMDiff_subtype_val
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff U _).mp contMDiff_subtype_val

/-- The top open set is diffeomorphic to the space. -/
def _root_.Diffeomorph.opensTop_OCL : (⊤ : Opens N) ≃ₘ⟮I, I⟯ N where
  toFun x := x.1
  invFun y := ⟨y, trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff ⊤ _).mp contMDiff_id

variable {Dw Dx Bw Bx : Type*} [TopologicalSpace Dw] [ChartedSpace HN Dw]
  [TopologicalSpace Dx] [ChartedSpace HN' Dx]
  [TopologicalSpace Bw] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Bw]
  [TopologicalSpace Bx] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Bx]

/-- **A local trivialization pulled back** along diffeomorphisms of the total spaces (`α`) and of
the bases (`β`) commuting with the projections. -/
def trivPullback_OCL (πw : C(Dw, Bw)) (πx : C(Dx, Bx)) (α : Dw ≃ₘ⟮I, I'⟯ Dx)
    (β : Bw ≃ₘ⟮𝓡 2, 𝓡 2⟯ Bx) (hcomm : ∀ x, πx (α x) = β (πw x)) (Q : Opens Bx)
    (Ψ : (Opens.comap πx Q) ≃ₘ⟮I', (𝓡 2).prod (𝓡 1)⟯ (Q × Circle)) :
    (Opens.comap πw (Opens.comap ⟨β, β.continuous⟩ Q))
      ≃ₘ⟮I, (𝓡 2).prod (𝓡 1)⟯ ((Opens.comap ⟨β, β.continuous⟩ Q) × Circle) :=
  (Diffeomorph.opensCongr_OCL (I := I) (show Opens.comap πw (Opens.comap ⟨β, β.continuous⟩ Q) =
      Opens.comap ⟨α, α.continuous⟩ (Opens.comap πx Q) from
    Opens.ext (Set.ext fun x => by
      change β (πw x) ∈ Q ↔ πx (α x) ∈ Q
      rw [hcomm]))).trans
    ((α.restrictPreimage74 (Opens.comap πx Q)).trans
      (Ψ.trans ((β.restrictPreimage74 Q).symm.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞))))

/-- The pulled-back trivialization has first coordinate `πw`. -/
theorem trivPullback_OCL_proj (πw : C(Dw, Bw)) (πx : C(Dx, Bx)) (α : Dw ≃ₘ⟮I, I'⟯ Dx)
    (β : Bw ≃ₘ⟮𝓡 2, 𝓡 2⟯ Bx) (hcomm : ∀ x, πx (α x) = β (πw x)) (Q : Opens Bx)
    (Ψ : (Opens.comap πx Q) ≃ₘ⟮I', (𝓡 2).prod (𝓡 1)⟯ (Q × Circle))
    (hΨ : ∀ x, (Ψ x).1.1 = πx x.1)
    (x : Opens.comap πw (Opens.comap ⟨β, β.continuous⟩ Q)) :
    ((trivPullback_OCL πw πx α β hcomm Q Ψ x).1).val = πw x.val := by
  change β.symm (Ψ _).1.1 = πw x.val
  rw [hΨ]
  change β.symm (πx (α x.1)) = πw x.val
  rw [hcomm, β.symm_apply_apply]

end Generic

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)

/-- The carried circle source of the produced stage geometry is `M.ψ(circleDomain_EFE)`. -/
theorem circleParent_eq_OCL :
    (S.closedStagesAt_OCL B hT hεr A zero).A.circle.restrictParent
        (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen =
      M.ψ.imageOpens74 S.chain.circleDomain_EFE := by
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · intro hx
    obtain ⟨hp, -⟩ :=
      (S.closedStagesAt_OCL B hT hεr A zero).A.circle.exists_of_mem_restrictParent hx
    obtain ⟨hq, hR⟩ := (S.circleStage74 A).exists_of_mem_restrictParent hp
    exact ⟨M.ψ.symm x, S.chain.mem_circleDomain_of_EFE (S.circleProj_R74 A ⟨x, hq⟩).2 hR,
      M.ψ.apply_symm_apply x⟩
  · rintro ⟨p, hp, rfl⟩
    have hU : p ∈ gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 0 := by
      refine (S.goodCut_circleSource_OCL B hT hεr).2 ?_
      rw [(S.goodCut_circleSource_OCL B hT hεr).1]
      exact hp
    have hq : M.ψ p ∈ S.circleParent_R74 := ⟨p, hU, rfl⟩
    have hR : S.circleProj_R74 A ⟨M.ψ p, hq⟩ ∈ S.circleBsOpens_OCL := by
      change S.chain.toGaf02ChainE.cutQ_R74 0 (M.ψ.symm (M.ψ p)) ∈
        gaf07CircleRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets
      rw [M.ψ.symm_apply_apply]
      exact (S.chain.circleDomain_mem_EFE hp).2
    exact (S.closedStagesAt_OCL B hT hεr A zero).A.circle.mem_restrictParent_of
      ((S.circleStage74 A).mem_restrictParent_of hq hR) trivial

/-- The total-space diffeomorphism `α`: the carried circle source to `circleDomain_EFE` by
`M.ψ⁻¹`. -/
def circleTotal_OCL :
    (S.closedStagesAt_OCL B hT hεr A zero).A.circle.restrictParent
        (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen
      ≃ₘ⟮W.model, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ S.chain.circleDomain_EFE :=
  (Diffeomorph.opensCongr_OCL (S.circleParent_eq_OCL B hT hεr A zero)).trans
    (M.ψ.restrictOpens74 S.chain.circleDomain_EFE)

/-- `α` commutes with the projections (`q₀` read on both sides). -/
theorem circleTotal_comm_OCL
    (x : (S.closedStagesAt_OCL B hT hεr A zero).A.circle.restrictParent
      (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen) :
    S.chain.circleProjC_EFE (S.circleTotal_OCL B hT hεr A zero x) =
      Diffeomorph.opensTop_OCL (I := 𝓡 2)
        (N := (S.closedStagesAt_OCL B hT hεr A zero).A.circle.Base)
        ((S.closedStagesAt_OCL B hT hεr A zero).A.circle.restrictProj
        (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen x) :=
  Subtype.ext (Subtype.ext rfl)

/-- **The circle facts at `D_R` from FDC03's saturation alone**: the local trivializations are
S-EDP-FDC2's `circleProj_trivial_EFE` pulled back along `M.ψ` (`trivPullback_OCL`); `proper` and
`cbase_compact` from G8a. -/
def circleCutFactsAt2_OCL (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (hsat : (S.closedStagesAt_OCL B hT hεr A zero).cut.M₃ =
      (S.closedStagesAt_OCL B hT hεr A zero).cut.circleRegion) :
    CircleCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) ↥(S.chain.toChain.finalBase_BAS 0) :=
    A.circleChartedSpace
  have htriv := S.chain.circleProj_trivial_EFE A (R.gaf07_numerics_OCL hT).1
    (R.gaf07_numerics_OCL hT).2
  let β := Diffeomorph.opensTop_OCL (I := 𝓡 2)
    (N := (S.closedStagesAt_OCL B hT hεr A zero).A.circle.Base)
  exact S.circleCutFactsAt_OCL B hT hεr A zero Htail
    (fun c => Opens.comap ⟨β, β.continuous⟩ (Classical.choose (htriv (β c))))
    (fun c => (Classical.choose_spec (htriv (β c))).1)
    (fun c => trivPullback_OCL _ S.chain.circleProjC_EFE (S.circleTotal_OCL B hT hεr A zero) β
      (S.circleTotal_comm_OCL B hT hεr A zero) _
      (Classical.choose (Classical.choose_spec (htriv (β c))).2))
    (fun c x => trivPullback_OCL_proj _ _ _ _ _ _ _
      (Classical.choose_spec (Classical.choose_spec (htriv (β c))).2) x)
    hsat

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse

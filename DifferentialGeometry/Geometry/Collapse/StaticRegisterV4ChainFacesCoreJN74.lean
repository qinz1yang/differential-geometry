import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFacesZeroJN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimEndOfArcOCL

/-!
# Draft 74, the zero and the new part of `∂M₂` at `D_R` (exit `slimExitAt3_OCL`)

Lane S-JUNCTIONS (by S-JUNCTIONS5), G30 (suffix `_JN74`). On the slim pieces `Pc` of the chosen
exit `slimExitAt3_OCL` (G4/G5 of S-REG-CHAIN6: end values, end classification):

* `zeroPart_fwd_JN74` / `zeroPart_bwd_JN74`: a point `x` of `∂M₁` outside the slim piece lies in
  an UNSHARED zero face, and conversely;
* `newPart_fwd_JN74` / `newPart_bwd_JN74`: a point of `∂(slim piece) ∖ ∂M₁` lies in a NEW end,
  and conversely.
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

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (hK : 5 ≤ K)

/-- The slim pieces of the chosen exit `slimExitAt3_OCL`. -/
abbrev slimPieces3_JN74 : SlimPiecesV2 W (S.zsp02SmoothExit74 hεr).rows M.cusp_R74 :=
  slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
    (S.slimExitAt3_OCL B hT hεr A hK).disjoint

/-- **The end set of an end of the pieces of `slimExitAt3_OCL` is the image of the slim piece
part**: every point of an end set is `ψ` of a point of the slim piece. -/
theorem endSet_mem_slimPiece_JN74 (e : (S.slimPieces3_JN74 B hT hεr A hK).End) {z : W.Carrier}
    (hz : z ∈ (S.slimPieces3_JN74 B hT hεr A hK).endSet e) :
    ∃ y : M.X, M.ψ y = z ∧
      y ∈ S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier := by
  have hU : z ∈ (S.slimPieces3_JN74 B hT hεr A hK).union :=
    mem_iUnion.2 ⟨e.1.1, (S.slimPieces3_JN74 B hT hεr A hK).endSet_subset_GSAFE e hz⟩
  have hU' : z ∈ (S.stagesAtZ_OCL B hT hεr A).cut.slimSet := by
    have h := (slimCutPieces_of_exit74 (S.slimExitAt3_OCL B hT hεr A hK)).union_eq
    exact h ▸ hU
  rw [S.slimSet_at_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)] at hU'
  obtain ⟨y, hy, rfl⟩ := hU'
  exact ⟨y, rfl, (S.goodCut_OCL B hT hεr).slimSet_eq ▸ hy⟩

/-- **A point of `∂M₁` outside the slim piece lies in an unshared zero face.** -/
theorem zeroPart_fwd_JN74 {x : M.X}
    (hxM : x ∈ frontier (interior S.chain.zeroUnion_ZSP35)ᶜ)
    (hxS : x ∉ S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier) :
    ∃ F : (S.slimPieces3_JN74 B hT hεr A hK).ResidualFace, Sum.isLeft F = true ∧
      M.ψ x ∈ (S.slimPieces3_JN74 B hT hεr A hK).residualSet F := by
  obtain ⟨i, Fm, hxF⟩ := S.exists_zeroFace_of_frontier_JN74 hεr (S.zsp02SmoothExit74 hεr)
    ((S.frontier_M₁_eq_zero_JN74 hεr) ▸ hxM)
  refine ⟨Sum.inl ⟨Sum.inl ⟨i, Fm⟩, ?_⟩, rfl, hxF⟩
  intro e' hk
  have hsh := slimPiecesOfExits74_shared_eq (S.slimExitAt3_OCL B hT hεr A hK).exit
    (S.slimExitAt3_OCL B hT hεr A hK).disjoint e' _ hk
  have hxe : M.ψ x ∈ (S.slimPieces3_JN74 B hT hεr A hK).endSet e' := hsh ▸ hxF
  obtain ⟨y, hy, hyS⟩ := S.endSet_mem_slimPiece_JN74 B hT hεr A hK e' hxe
  rw [M.ψ.injective hy] at hyS
  exact hxS hyS

/-- **A point of an unshared zero face lies on `∂M₁` outside the slim piece.** -/
theorem zeroPart_bwd_JN74 {x : M.X}
    (F : {F : NeighbourFace (S.zsp02SmoothExit74 hεr).rows M.cusp_R74 //
      ∀ e, (S.slimPieces3_JN74 B hT hεr A hK).endKind e ≠ some F})
    (hxF : M.ψ x ∈ neighbourSet F.1) :
    x ∈ frontier (interior S.chain.zeroUnion_ZSP35)ᶜ ∧
      x ∉ S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier := by
  obtain ⟨F', hF'⟩ := F
  rcases F' with ⟨i, Fm⟩ | ⟨b, -⟩
  swap
  · exact (IsEmpty.false b).elim
  have hxZ := S.frontier_of_zeroFace_JN74 hεr (S.zsp02SmoothExit74 hεr) i Fm hxF
  refine ⟨(S.frontier_M₁_eq_zero_JN74 hεr).symm ▸ hxZ, fun hxS => ?_⟩
  obtain ⟨k, b, hkb, hfp⟩ := S.facePoint_arcEnd_JN74 B hT hεr hxS hxZ
  obtain ⟨e, -, -, hset, hiff⟩ := S.exists_slimEnd_of_arcEnd_OCL B hT hεr A hK k b
  have hkind : (S.slimPieces3_JN74 B hT hεr A hK).endKind e ≠ none := fun h =>
    (hiff.1 h) (hkb ▸ hfp)
  obtain ⟨F'', hF''⟩ := Option.ne_none_iff_exists'.1 hkind
  have hsh := slimPiecesOfExits74_shared_eq (S.slimExitAt3_OCL B hT hεr A hK).exit
    (S.slimExitAt3_OCL B hT hεr A hK).disjoint e F'' hF''
  have hxe : M.ψ x ∈ neighbourSet F'' := by
    rw [← hsh, hset]
    exact ⟨x, hkb, rfl⟩
  rcases F'' with ⟨i', Fm'⟩ | ⟨b', -⟩
  swap
  · exact (IsEmpty.false b').elim
  obtain ⟨p, hp, hpx⟩ := hxF
  obtain ⟨p', hp', hpx'⟩ := hxe
  by_cases hii : i' = i
  · subst hii
    have hpp : p' = p := ((S.zsp02SmoothExit74 hεr).rows.piece i').injective (hpx'.trans hpx.symm)
    subst hpp
    have hFm : Fm' = Fm := ActualComponent.eq_of_mem hp' hp
    subst hFm
    exact hF' e hF''
  · exact disjoint_left.1 ((S.zsp02SmoothExit74 hεr).rows.disjoint hii) ⟨p', hpx'⟩ ⟨p, hpx⟩

/-- **A point of `∂(slim piece)` off `∂M₁` lies in a NEW end.** -/
theorem newPart_fwd_JN74 {x : M.X}
    (hxS : x ∈ frontier (S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier))
    (hxM : x ∉ frontier (interior S.chain.zeroUnion_ZSP35)ᶜ) :
    ∃ en : (S.slimPieces3_JN74 B hT hεr A hK).NewEnd,
      M.ψ x ∈ (S.slimPieces3_JN74 B hT hεr A hK).endSet en.1 := by
  obtain ⟨k, b, hkb⟩ := S.frontier_slim_arcEnd_JN74 B hT hεr hxS
  obtain ⟨e, -, -, hset, -⟩ := S.exists_slimEnd_of_arcEnd_OCL B hT hεr A hK k b
  have hxe : M.ψ x ∈ (S.slimPieces3_JN74 B hT hεr A hK).endSet e := by
    rw [hset]
    exact ⟨x, hkb, rfl⟩
  by_cases hnone : (S.slimPieces3_JN74 B hT hεr A hK).endKind e = none
  · exact ⟨⟨e, hnone⟩, hxe⟩
  · exfalso
    obtain ⟨F'', hF''⟩ := Option.ne_none_iff_exists'.1 hnone
    have hsh := slimPiecesOfExits74_shared_eq (S.slimExitAt3_OCL B hT hεr A hK).exit
      (S.slimExitAt3_OCL B hT hεr A hK).disjoint e F'' hF''
    have hxn : M.ψ x ∈ neighbourSet F'' := hsh ▸ hxe
    rcases F'' with ⟨i', Fm'⟩ | ⟨b', -⟩
    · exact hxM ((S.frontier_M₁_eq_zero_JN74 hεr).symm ▸
        S.frontier_of_zeroFace_JN74 hεr (S.zsp02SmoothExit74 hεr) i' Fm' hxn)
    · exact (IsEmpty.false b').elim

/-- **A point of a NEW end lies on `∂(slim piece)` and off `∂M₁`.** -/
theorem newPart_bwd_JN74 {x : M.X}
    (en : (S.slimPieces3_JN74 B hT hεr A hK).NewEnd)
    (hxe : M.ψ x ∈ (S.slimPieces3_JN74 B hT hεr A hK).endSet en.1) :
    x ∈ frontier (S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier) ∧
      x ∉ frontier (interior S.chain.zeroUnion_ZSP35)ᶜ := by
  obtain ⟨k, -, hset, hiff⟩ := S.slimEnd_free_iff_OCL B hT hεr A hK en.1
  have hxe' : M.ψ x ∈ M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
      {(S.chain.slimD₃_OCL hεr).arc k (iccEnd en.1.1.2)}) := hset ▸ hxe
  obtain ⟨y, hy, hyx⟩ := hxe'
  have hyx' : y = x := M.ψ.injective hyx
  subst hyx'
  have hfree : (S.chain.slimD₃_OCL hεr).arc k (iccEnd en.1.1.2) ∉ S.chain.slimFacePoints_ZSP35 :=
    hiff.1 en.2
  obtain ⟨hfr, hxS⟩ := S.mem_frontier_slim_of_arcEnd_JN74 B hT hεr k en.1.1.2 hy
  refine ⟨hfr, fun hxM => ?_⟩
  have hfp := S.facePoint_of_frontier_slim_JN74 B hT hεr hxS hxM
  rw [hy] at hfp
  exact hfree hfp

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse

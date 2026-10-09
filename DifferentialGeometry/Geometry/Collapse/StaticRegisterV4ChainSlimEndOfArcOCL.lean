import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimEndFreeOCL

/-!
# Draft 74, G5: every end value of an arc of `D₃` is an end of the pieces of `slimExitAt3_OCL`

Lane C14-REG-CHAIN (by S-REG-CHAIN6), G5 (suffix `_OCL`). The converse direction of
`slimEnd_free_iff_OCL` (G4): from an arc end value to an END of the slim pieces.

* `slimPieceExit_isInterval_OCL` (kernel): an arc exit has an interval model (so its ends are ends
  in the sense of `SlimEnd`);
* `exists_slimEnd_of_arcEnd_OCL`: for every arc `k` of `D₃` of `D_R` and every `b : Bool`
  there is an end `e` of the pieces of `slimExitAt3_OCL` with `e.1.2 = b`, whose exit is the exit
  of the component of arc `k`, whose end set is the `ψ`-image of the whole `f₃`-fibre over the end
  value `arc k (iccEnd b)`, and which is a free (new) end iff that end value is not a slim face
  point.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace GC.GraphManifold.Assembly.FC39P0

/-- **An arc exit has an interval model.** -/
theorem slimPieceExit_isInterval_OCL {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n}
    {Z : ZeroDomains W} {C : CuspCores W E} (x : SlimPieceExit74 Z C)
    (hx : (∃ a : SphereArcExit74 Z C, x = .sphereArc a) ∨ ∃ a : TorusArcExit74 Z C,
      x = .torusArc a) : slimModelIsInterval x.model := by
  rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact trivial
  · exact trivial

end GC.GraphManifold.Assembly.FC39P0

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

/-- **From an arc end value to an end of the slim pieces** (G5): for every arc `k` of `D₃` of
`D_R` and every end `b`, an end `e` of the slim pieces of `slimExitAt3_OCL` with `e.1.2 = b`, whose
exit carries the component of arc `k`, with end set the `ψ`-image of the whole `f₃`-fibre over
`arc k (iccEnd b)`, and `endKind e = none` (a new end) iff that end value is not a slim face
point. -/
theorem exists_slimEnd_of_arcEnd_OCL (k : Fin (S.chain.slimD₃_OCL hεr).m) (b : Bool) :
    ∃ e : (slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
        (S.slimExitAt3_OCL B hT hεr A hK).disjoint).End,
      e.1.2 = b ∧
      ((S.stagesAtZ_OCL B hT hεr A).comp
        ((S.slimExitAt3_OCL B hT hεr A hK).componentEquiv e.1.1)).1 =
          (S.chain.slimD₃_OCL hεr).arc k '' Icc 0 1 ∧
      (slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
        (S.slimExitAt3_OCL B hT hεr A hK).disjoint).endSet e =
          M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
            {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)}) ∧
      ((slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
        (S.slimExitAt3_OCL B hT hεr A hK).disjoint).endKind e = none ↔
          (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∉ S.chain.slimFacePoints_ZSP35) := by
  obtain ⟨harc, -⟩ := S.slimExitOf3_rel3_OCL B hT hεr (S.zsp02SmoothExit74 hεr)
    (S.stagesAtZ_OCL B hT hεr A) hK
  obtain ⟨jx, hjx, h⟩ := harc k
  rcases h with ⟨a, ha, -, hsl, -, hiff⟩ | ⟨a, ha, -, hsl, -, hiff⟩
  · have hI := slimPieceExit_isInterval_OCL ((S.slimExitAt3_OCL B hT hεr A hK).exit jx)
      (Or.inl ⟨a, ha⟩)
    have hd := slimPieceExit_endData_OCL ((S.slimExitAt3_OCL B hT hεr A hK).exit jx)
      (fun b => M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹' {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)}))
      (fun b => (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∉ S.chain.slimFacePoints_ZSP35)
      (Or.inl ⟨a, ha, hsl, hiff⟩) b hI
    exact ⟨⟨(jx, b), hI⟩, rfl, hjx,
      (((S.slimExitAt3_OCL B hT hεr A hK).exit jx).image_end_eq b hI).trans hd.1, hd.2⟩
  · have hI := slimPieceExit_isInterval_OCL ((S.slimExitAt3_OCL B hT hεr A hK).exit jx)
      (Or.inr ⟨a, ha⟩)
    have hd := slimPieceExit_endData_OCL ((S.slimExitAt3_OCL B hT hεr A hK).exit jx)
      (fun b => M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹' {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)}))
      (fun b => (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∉ S.chain.slimFacePoints_ZSP35)
      (Or.inr ⟨a, ha, hsl, hiff⟩) b hI
    exact ⟨⟨(jx, b), hI⟩, rfl, hjx,
      (((S.slimExitAt3_OCL B hT hεr A hK).exit jx).image_end_eq b hI).trans hd.1, hd.2⟩

/-- **From a free arc end value to a NEW end of the slim pieces** (G5): if the end value
`arc k (iccEnd b)` is not a slim face point, the end `e` of `exists_slimEnd_of_arcEnd_OCL` is a new
end (an actual face of `M₂`), with the same end set. -/
theorem exists_newEnd_of_arcEnd_OCL (k : Fin (S.chain.slimD₃_OCL hεr).m) (b : Bool)
    (hfree : (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∉ S.chain.slimFacePoints_ZSP35) :
    ∃ en : (slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
        (S.slimExitAt3_OCL B hT hεr A hK).disjoint).NewEnd,
      en.1.1.2 = b ∧
      ((S.stagesAtZ_OCL B hT hεr A).comp
        ((S.slimExitAt3_OCL B hT hεr A hK).componentEquiv en.1.1.1)).1 =
          (S.chain.slimD₃_OCL hεr).arc k '' Icc 0 1 ∧
      (slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
        (S.slimExitAt3_OCL B hT hεr A hK).disjoint).endSet en.1 =
          M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
            {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)}) := by
  obtain ⟨e, hb, hc, hset, hiff⟩ := S.exists_slimEnd_of_arcEnd_OCL B hT hεr A hK k b
  exact ⟨⟨e, hiff.mpr hfree⟩, hb, hc, hset⟩

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse

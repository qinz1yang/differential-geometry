import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimExitRel2OCL

/-!
# Draft 74, clause (b) of the closed gate: the chosen slim exit WITH the end coordinates

Lane C14-REG-CHAIN (by S-REG-CHAIN6), G2 (suffix `_OCL`, Option A). The choice of an exit
satisfying `exists_slimExit_rel2_OCL` (G1), replacing G40's `slimExitAt_OCL` (untouched):

* `slimExitOf2_OCL`: a choice from `exists_slimExit_rel2_OCL` at ANY stage geometry record `P` of
  the closed route at `D_R` (and any zero exit); `slimExitOf2_rel2_OCL` is its specification (all
  relations of G40 and the end coordinate of every free end, for the chosen exit itself);
* `slimExitAt2_OCL`: the choice at `S.stagesAtZ_OCL B hT hεr A` (the exit the gate takes), with
  `slimExitAt2_rel2_OCL`.
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
  (hεr : εr < 1 / 2) (zero : ZSP02SmoothExit74 S)
  (P : ClosedStageGeometryU74 (S.goodCut_OCL B hT hεr) zero) (hK : 5 ≤ K)

/-- **The chosen slim exit at a stage geometry record `P` of the closed route** (a choice from
G1's `exists_slimExit_rel2_OCL`). -/
def slimExitOf2_OCL : SlimExit74 P.A P.cut :=
  Classical.choose (S.exists_slimExit_rel2_OCL B hT hεr zero P hK)

local notation "Xc" => S.slimExitOf2_OCL B hT hεr zero P hK

/-- **The specification of the chosen exit**: all the relations of G40 (components, projection
identities, whole end fibres, loops) and, for every free arc end, the end coordinate
`fn b y = e (f₃ (ψ⁻¹ y))` on `near b`. -/
theorem slimExitOf2_rel2_OCL :
      (∀ k : Fin (S.chain.slimD₃_OCL hεr).m, ∃ jx : Fin (Xc).count,
        (P.comp ((Xc).componentEquiv jx)).1 = (S.chain.slimD₃_OCL hεr).arc k '' Icc 0 1 ∧
        ((∃ a : SphereArcExit74 P.A.zero P.A.cusp, (Xc).exit jx = .sphereArc a ∧
            (∀ z, S.chain.slimMap_ZSP35 (M.ψ.symm (a.F z)) =
              (S.chain.slimD₃_OCL hεr).arc k z.2) ∧
            (∀ b, range (fun z => a.F (z, iccEnd b)) = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
              {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)})) ∧
            ∀ b : Bool, a.ends.kind b = none →
              ∃ (Ne : Set S.blockSpace_R74) (e : S.blockSpace_R74 → ℝ),
                IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
                (∀ y ∈ (a.ends.near b : Set W.Carrier),
                  S.chain.slimMap_ZSP35 (M.ψ.symm y) ∈ Ne) ∧
                ∀ y ∈ (a.ends.near b : Set W.Carrier),
                  a.ends.fn b y = e (S.chain.slimMap_ZSP35 (M.ψ.symm y))) ∨
          (∃ a : TorusArcExit74 P.A.zero P.A.cusp, (Xc).exit jx = .torusArc a ∧
            (∀ z, S.chain.slimMap_ZSP35 (M.ψ.symm (a.F z)) =
              (S.chain.slimD₃_OCL hεr).arc k z.2) ∧
            (∀ b, range (fun z => a.F (z, iccEnd b)) = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
              {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)})) ∧
            ∀ b : Bool, a.ends.kind b = none →
              ∃ (Ne : Set S.blockSpace_R74) (e : S.blockSpace_R74 → ℝ),
                IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
                (∀ y ∈ (a.ends.near b : Set W.Carrier),
                  S.chain.slimMap_ZSP35 (M.ψ.symm y) ∈ Ne) ∧
                ∀ y ∈ (a.ends.near b : Set W.Carrier),
                  a.ends.fn b y = e (S.chain.slimMap_ZSP35 (M.ψ.symm y))))) ∧
      ∀ j : Fin (S.chain.slimD₃_OCL hεr).l, ∃ jx : Fin (Xc).count,
        (P.comp ((Xc).componentEquiv jx)).1 = range ((S.chain.slimD₃_OCL hεr).loop j) ∧
        ((∃ l : SphereLoopExit74 W, (Xc).exit jx = .sphereLoop l ∧
            l.region.O = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
              range ((S.chain.slimD₃_OCL hεr).loop j)) ∧
            ∀ y ∈ l.region.O, ∀ t : ℝ, l.p y = Circle.exp (2 * Real.pi * t) ↔
              S.chain.slimMap_ZSP35 (M.ψ.symm y) = (S.chain.slimD₃_OCL hεr).loop j t) ∨
          (∃ l : TorusLoopExit74 W, (Xc).exit jx = .torusLoop l ∧
            l.region.O = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
              range ((S.chain.slimD₃_OCL hεr).loop j)) ∧
            ∀ y ∈ l.region.O, ∀ t : ℝ, l.p y = Circle.exp (2 * Real.pi * t) ↔
              S.chain.slimMap_ZSP35 (M.ψ.symm y) = (S.chain.slimD₃_OCL hεr).loop j t)) :=
  Classical.choose_spec (S.exists_slimExit_rel2_OCL B hT hεr zero P hK)

end At

section AtZ

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (hK : 5 ≤ K)

/-- **The produced slim exit at `D_R`, with the end coordinates** (clause (b)): the choice of
`slimExitOf2_OCL` at the stage geometry `S.stagesAtZ_OCL B hT hεr A` and the zero exit
`S.zsp02SmoothExit74 hεr` the gate takes; an `abbrev`, so
`S.slimExitOf2_rel2_OCL B hT hεr (S.zsp02SmoothExit74 hεr) (S.stagesAtZ_OCL B hT hεr A) hK` IS the
specification of `slimExitAt2_OCL` (G40's relations and the end coordinate of every free end). -/
abbrev slimExitAt2_OCL :
    SlimExit74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut :=
  S.slimExitOf2_OCL B hT hεr (S.zsp02SmoothExit74 hεr) (S.stagesAtZ_OCL B hT hεr A) hK

end AtZ

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse

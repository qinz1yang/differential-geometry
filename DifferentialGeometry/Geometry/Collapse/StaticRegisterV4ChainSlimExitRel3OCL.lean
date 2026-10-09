import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimExitRel2OCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimArcExits3OCL

/-!
# Draft 74, clause (b) of the closed gate, with the end classification exposed

Lane C14-REG-CHAIN (by S-REG-CHAIN6), G4 (suffix `_OCL`). `exists_slimExit_rel3_OCL` (G1,
untouched) with ONE more conjunct in each arc disjunct (sphere and torus): the end of the arc is
free iff its end value is not a slim face point,
`∀ b, a.ends.kind b = none ↔
  (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∉ S.chain.slimFacePoints_ZSP35`.
The loop exits are G1's (`exists_slimLoopExit_OCL`).
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
  (P : ClosedStageGeometryU74 (S.goodCut_OCL B hT hεr) zero)

/-- **The slim arc exit of the component of arc `k` at `D_R`, with the end coordinate of every
free end and the end classification**: the arc exit of G39 for the data of `D_R`
(`zero_end_face74` for the zero-face ends), the descent clause and the classification clause of
`slim_arc_exit3_OCL`. -/
theorem exists_slimArcExit3_OCL (hK : 5 ≤ K) (k : Fin (S.chain.slimD₃_OCL hεr).m) :
    ∃ x : SlimPieceExit74 P.A.zero P.A.cusp,
      range x.piece.map = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
        ((S.chain.slimD₃_OCL hεr).arc k '' Icc 0 1)) ∧
      ((∃ a : SphereArcExit74 P.A.zero P.A.cusp, x = .sphereArc a ∧
          (∀ z, S.chain.slimMap_ZSP35 (M.ψ.symm (a.F z)) =
            (S.chain.slimD₃_OCL hεr).arc k z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
            {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)})) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set S.blockSpace_R74) (e : S.blockSpace_R74 → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier),
                S.chain.slimMap_ZSP35 (M.ψ.symm y) ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier),
                a.ends.fn b y = e (S.chain.slimMap_ZSP35 (M.ψ.symm y))) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∉ S.chain.slimFacePoints_ZSP35) ∨
        (∃ a : TorusArcExit74 P.A.zero P.A.cusp, x = .torusArc a ∧
          (∀ z, S.chain.slimMap_ZSP35 (M.ψ.symm (a.F z)) =
            (S.chain.slimD₃_OCL hεr).arc k z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
            {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)})) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set S.blockSpace_R74) (e : S.blockSpace_R74 → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier),
                S.chain.slimMap_ZSP35 (M.ψ.symm y) ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier),
                a.ends.fn b y = e (S.chain.slimMap_ZSP35 (M.ψ.symm y))) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∉ S.chain.slimFacePoints_ZSP35)) := by
  obtain ⟨hD, hKs, hKF, -⟩ := S.chain.slimDomains_spec_OCL hεr
  exact S.chain.slim_arc_exit3_OCL hεr hK M.ψ M.boundary_empty_R74
    (S.chain.slimK₃_OCL hεr) (S.chain.slimD₃_OCL hεr) hD hKs hKF
    (S.goodCut_D₃_reg_OCL B hT hεr) (S.goodCut_D₃_bdry_OCL B hT hεr)
    (fun y hy hs hne => S.zero_end_face74 zero hεr hy hs hne) k

/-- **Clause (b) of the closed gate at `D_R`, with the binding relations of G40, the end
coordinate of every free slim end (G1) and the end classification** (G4): the slim exit of the
stage geometry `P` and its cut, over the arcs and loops of `D₃` of `D_R`. The exit of the
component of arc `k` is a sphere / torus arc exit with the projection identity
`f₃(ψ⁻¹(F (z, t))) = arc k t`, both end slices the whole end fibres, for every free end `b` a
smooth `e` on an open `Ne` with `a.ends.fn b y = e (f₃ (ψ⁻¹ y))` on `a.ends.near b`, and the end
`b` is free iff its end value `arc k (iccEnd b)` is not a slim face point; the exit of the
component of loop `j` is as in G40. -/
theorem exists_slimExit_rel3_OCL (hK : 5 ≤ K) :
    ∃ Xe : SlimExit74 P.A P.cut,
      (∀ k : Fin (S.chain.slimD₃_OCL hεr).m, ∃ jx : Fin Xe.count,
        (P.comp (Xe.componentEquiv jx)).1 = (S.chain.slimD₃_OCL hεr).arc k '' Icc 0 1 ∧
        ((∃ a : SphereArcExit74 P.A.zero P.A.cusp, Xe.exit jx = .sphereArc a ∧
            (∀ z, S.chain.slimMap_ZSP35 (M.ψ.symm (a.F z)) =
              (S.chain.slimD₃_OCL hεr).arc k z.2) ∧
            (∀ b, range (fun z => a.F (z, iccEnd b)) = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
              {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)})) ∧
            (∀ b : Bool, a.ends.kind b = none →
              ∃ (Ne : Set S.blockSpace_R74) (e : S.blockSpace_R74 → ℝ),
                IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
                (∀ y ∈ (a.ends.near b : Set W.Carrier),
                  S.chain.slimMap_ZSP35 (M.ψ.symm y) ∈ Ne) ∧
                ∀ y ∈ (a.ends.near b : Set W.Carrier),
                  a.ends.fn b y = e (S.chain.slimMap_ZSP35 (M.ψ.symm y))) ∧
            ∀ b : Bool, a.ends.kind b = none ↔
              (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∉ S.chain.slimFacePoints_ZSP35) ∨
          (∃ a : TorusArcExit74 P.A.zero P.A.cusp, Xe.exit jx = .torusArc a ∧
            (∀ z, S.chain.slimMap_ZSP35 (M.ψ.symm (a.F z)) =
              (S.chain.slimD₃_OCL hεr).arc k z.2) ∧
            (∀ b, range (fun z => a.F (z, iccEnd b)) = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
              {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)})) ∧
            (∀ b : Bool, a.ends.kind b = none →
              ∃ (Ne : Set S.blockSpace_R74) (e : S.blockSpace_R74 → ℝ),
                IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
                (∀ y ∈ (a.ends.near b : Set W.Carrier),
                  S.chain.slimMap_ZSP35 (M.ψ.symm y) ∈ Ne) ∧
                ∀ y ∈ (a.ends.near b : Set W.Carrier),
                  a.ends.fn b y = e (S.chain.slimMap_ZSP35 (M.ψ.symm y))) ∧
            ∀ b : Bool, a.ends.kind b = none ↔
              (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∉ S.chain.slimFacePoints_ZSP35))) ∧
      ∀ j : Fin (S.chain.slimD₃_OCL hεr).l, ∃ jx : Fin Xe.count,
        (P.comp (Xe.componentEquiv jx)).1 = range ((S.chain.slimD₃_OCL hεr).loop j) ∧
        ((∃ l : SphereLoopExit74 W, Xe.exit jx = .sphereLoop l ∧
            l.region.O = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
              range ((S.chain.slimD₃_OCL hεr).loop j)) ∧
            ∀ y ∈ l.region.O, ∀ t : ℝ, l.p y = Circle.exp (2 * Real.pi * t) ↔
              S.chain.slimMap_ZSP35 (M.ψ.symm y) = (S.chain.slimD₃_OCL hεr).loop j t) ∨
          (∃ l : TorusLoopExit74 W, Xe.exit jx = .torusLoop l ∧
            l.region.O = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
              range ((S.chain.slimD₃_OCL hεr).loop j)) ∧
            ∀ y ∈ l.region.O, ∀ t : ℝ, l.p y = Circle.exp (2 * Real.pi * t) ↔
              S.chain.slimMap_ZSP35 (M.ψ.symm y) = (S.chain.slimD₃_OCL hεr).loop j t)) :=
  exists_slimExit74_of_exits P.slim_ident (S.chain.slimD₃_OCL hεr) P.comp P.comp_eq
    (fun k x => (∃ a : SphereArcExit74 P.A.zero P.A.cusp, x = .sphereArc a ∧
        (∀ z, S.chain.slimMap_ZSP35 (M.ψ.symm (a.F z)) = (S.chain.slimD₃_OCL hεr).arc k z.2) ∧
        (∀ b, range (fun z => a.F (z, iccEnd b)) = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
          {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)})) ∧
        (∀ b : Bool, a.ends.kind b = none →
          ∃ (Ne : Set S.blockSpace_R74) (e : S.blockSpace_R74 → ℝ),
            IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
            (∀ y ∈ (a.ends.near b : Set W.Carrier),
              S.chain.slimMap_ZSP35 (M.ψ.symm y) ∈ Ne) ∧
            ∀ y ∈ (a.ends.near b : Set W.Carrier),
              a.ends.fn b y = e (S.chain.slimMap_ZSP35 (M.ψ.symm y))) ∧
        ∀ b : Bool, a.ends.kind b = none ↔
          (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∉ S.chain.slimFacePoints_ZSP35) ∨
      (∃ a : TorusArcExit74 P.A.zero P.A.cusp, x = .torusArc a ∧
        (∀ z, S.chain.slimMap_ZSP35 (M.ψ.symm (a.F z)) = (S.chain.slimD₃_OCL hεr).arc k z.2) ∧
        (∀ b, range (fun z => a.F (z, iccEnd b)) = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
          {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)})) ∧
        (∀ b : Bool, a.ends.kind b = none →
          ∃ (Ne : Set S.blockSpace_R74) (e : S.blockSpace_R74 → ℝ),
            IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
            (∀ y ∈ (a.ends.near b : Set W.Carrier),
              S.chain.slimMap_ZSP35 (M.ψ.symm y) ∈ Ne) ∧
            ∀ y ∈ (a.ends.near b : Set W.Carrier),
              a.ends.fn b y = e (S.chain.slimMap_ZSP35 (M.ψ.symm y))) ∧
        ∀ b : Bool, a.ends.kind b = none ↔
          (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∉ S.chain.slimFacePoints_ZSP35))
    (fun j x => (∃ l : SphereLoopExit74 W, x = .sphereLoop l ∧
        l.region.O = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹' range ((S.chain.slimD₃_OCL hεr).loop j)) ∧
        ∀ y ∈ l.region.O, ∀ t : ℝ, l.p y = Circle.exp (2 * Real.pi * t) ↔
          S.chain.slimMap_ZSP35 (M.ψ.symm y) = (S.chain.slimD₃_OCL hεr).loop j t) ∨
      (∃ l : TorusLoopExit74 W, x = .torusLoop l ∧
        l.region.O = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹' range ((S.chain.slimD₃_OCL hεr).loop j)) ∧
        ∀ y ∈ l.region.O, ∀ t : ℝ, l.p y = Circle.exp (2 * Real.pi * t) ↔
          S.chain.slimMap_ZSP35 (M.ψ.symm y) = (S.chain.slimD₃_OCL hεr).loop j t))
    (fun k => S.exists_slimArcExit3_OCL B hT hεr zero P hK k)
    (fun j => S.exists_slimLoopExit_OCL B hT hεr zero P hK j)

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse

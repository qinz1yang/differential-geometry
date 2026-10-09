import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimExitRel2OCL

/-!
# Draft 74, G1 consumer: the end function of a free slim end is constant on the `f₃`-fibres

Lane C14-REG-CHAIN (by S-REG-CHAIN6), G1 consumer (suffix `_OCL`). From the end coordinate clause
of `exists_slimExit_rel2_OCL`:

* `endFn_fibreConst_of_coord_OCL` (generic): if `fn = e ∘ f` on a set `N` then `fn` takes equal
  values at two points of `N` with equal `f`;
* `exists_slimExit_endFibreConst_OCL`: the exit of the component of every arc is a sphere / torus
  arc exit all of whose free end functions take equal values at two points of the end
  neighbourhood with the same `f₃ ∘ ψ⁻¹`; in particular `nonempty_slimExit2_OCL`.
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

/-- **A function that is `e ∘ f` on a set is constant on the `f`-fibres of the set.** -/
theorem endFn_fibreConst_of_coord_OCL {α β : Type*} {f : α → β} {fn : α → ℝ} {N : Set α}
    {e : β → ℝ} (h : ∀ y ∈ N, fn y = e (f y)) {y y' : α} (hy : y ∈ N) (hy' : y' ∈ N)
    (hf : f y = f y') : fn y = fn y' := by
  rw [h y hy, h y' hy', hf]

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (zero : ZSP02SmoothExit74 S)
  (P : ClosedStageGeometryU74 (S.goodCut_OCL B hT hεr) zero)

/-- **The produced slim exit's free end functions are constant on the `f₃`-fibres** (consumer of
G1): the exit of the component of every arc is a sphere / torus arc exit all of whose free end
functions take equal values at two points of the end neighbourhood with the same
`f₃ (ψ⁻¹ y)`. -/
theorem exists_slimExit_endFibreConst_OCL (hK : 5 ≤ K) :
    ∃ Xe : SlimExit74 P.A P.cut, ∀ k : Fin (S.chain.slimD₃_OCL hεr).m, ∃ jx : Fin Xe.count,
      (P.comp (Xe.componentEquiv jx)).1 = (S.chain.slimD₃_OCL hεr).arc k '' Icc 0 1 ∧
      ((∃ a : SphereArcExit74 P.A.zero P.A.cusp, Xe.exit jx = .sphereArc a ∧
          ∀ b : Bool, a.ends.kind b = none → ∀ y ∈ (a.ends.near b : Set W.Carrier),
            ∀ y' ∈ (a.ends.near b : Set W.Carrier),
              S.chain.slimMap_ZSP35 (M.ψ.symm y) = S.chain.slimMap_ZSP35 (M.ψ.symm y') →
                a.ends.fn b y = a.ends.fn b y') ∨
        (∃ a : TorusArcExit74 P.A.zero P.A.cusp, Xe.exit jx = .torusArc a ∧
          ∀ b : Bool, a.ends.kind b = none → ∀ y ∈ (a.ends.near b : Set W.Carrier),
            ∀ y' ∈ (a.ends.near b : Set W.Carrier),
              S.chain.slimMap_ZSP35 (M.ψ.symm y) = S.chain.slimMap_ZSP35 (M.ψ.symm y') →
                a.ends.fn b y = a.ends.fn b y')) := by
  obtain ⟨Xe, harc, -⟩ := S.exists_slimExit_rel2_OCL B hT hεr zero P hK
  refine ⟨Xe, fun k => ?_⟩
  obtain ⟨jx, hjx, h⟩ := harc k
  refine ⟨jx, hjx, ?_⟩
  rcases h with ⟨a, ha, -, -, hend⟩ | ⟨a, ha, -, -, hend⟩
  · refine Or.inl ⟨a, ha, fun b hb y hy y' hy' hf => ?_⟩
    obtain ⟨Ne, e, -, -, -, hfe⟩ := hend b hb
    exact endFn_fibreConst_of_coord_OCL (f := fun y => S.chain.slimMap_ZSP35 (M.ψ.symm y))
      (N := (a.ends.near b : Set W.Carrier)) hfe hy hy' hf
  · refine Or.inr ⟨a, ha, fun b hb y hy y' hy' hf => ?_⟩
    obtain ⟨Ne, e, -, -, -, hfe⟩ := hend b hb
    exact endFn_fibreConst_of_coord_OCL (f := fun y => S.chain.slimMap_ZSP35 (M.ψ.symm y))
      (N := (a.ends.near b : Set W.Carrier)) hfe hy hy' hf

/-- **Clause (b) of the closed gate at `D_R`** (G40's `nonempty_slimExit_OCL`) from the
strengthened construction `exists_slimExit_rel2_OCL`. -/
theorem nonempty_slimExit2_OCL (hK : 5 ≤ K) : Nonempty (SlimExit74 P.A P.cut) :=
  (S.exists_slimExit_rel2_OCL B hT hεr zero P hK).elim fun Xe _ => ⟨Xe⟩

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse

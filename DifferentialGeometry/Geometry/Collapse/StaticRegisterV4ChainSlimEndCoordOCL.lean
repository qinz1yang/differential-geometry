import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimExitAt2OCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimExitRel2OCLConsumer
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Junctions

/-!
# Draft 74, G3: the end coordinate of a NEW slim end of the chosen exit, and its `E`-fibre constancy

Lane C14-REG-CHAIN (by S-REG-CHAIN6), G3 (suffix `_OCL`), the minimal consumer of the end
coordinate clause of G1 for S-JUNCTIONS4 (slim-end label case of `hdesc` / the `g1`-`g3` adapter).

* `exit_cover_of_rel_OCL` (kernel): if for every arc `k` (loop `j`) of the domain some exit of
  the component of that arc (loop) satisfies `Parc k` (`Ploop j`), then EVERY exit of the slim exit
  satisfies `Parc k` for some arc or `Ploop j` for some loop (components of `D₃` are arcs and
  loops, `componentEquiv` is injective);
* `slimPieceExit_endCoord_OCL` (kernel): the end coordinate clause for the ends of an exit that is
  an arc exit satisfying it (a loop exit has no end);
* `slimEnd_coord_OCL`: for every NEW end `en` of the pieces of `slimExitAt2_OCL`, the residual
  face function of the slim face `.inr en` is `e ∘ f₃ ∘ ψ⁻¹` on its neighbourhood, `e` smooth on an
  open `Ne`;
* `slimEnd_fibreConst_OCL`: hence it takes equal values at two points of the neighbourhood with
  `E (ψ⁻¹ y) = E (ψ⁻¹ y')` (`f₃ = Q₃ ∘ E`): the shape of `zero_ratio_fibreConst_JN74` for the
  slim faces.
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

/-- **Every exit of a slim exit is the exit of an arc or of a loop**: if every arc and every loop
of the one-dimensional domain `Dc` has an exit of its component satisfying `Parc k` resp.
`Ploop j`, then every exit `jx` of the slim exit satisfies `Parc k` for some arc `k` or `Ploop j`
for some loop `j`. -/
theorem exit_cover_of_rel_OCL {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n}
    {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {Bs : Set H}
    (Dc : SmoothCompactOneDomain_BCF Bs) (comp : ActualComponent D.D₃ ≃ ActualComponent Dc.carrier)
    (Xe : SlimExit74 A D) (Parc : Fin Dc.m → Fin Xe.count → Prop)
    (Ploop : Fin Dc.l → Fin Xe.count → Prop)
    (harc : ∀ k : Fin Dc.m, ∃ jx : Fin Xe.count,
      (comp (Xe.componentEquiv jx)).1 = Dc.arc k '' Icc 0 1 ∧ Parc k jx)
    (hloop : ∀ j : Fin Dc.l, ∃ jx : Fin Xe.count,
      (comp (Xe.componentEquiv jx)).1 = range (Dc.loop j) ∧ Ploop j jx) (jx : Fin Xe.count) :
    (∃ k, Parc k jx) ∨ ∃ j, Ploop j jx := by
  have hinj : Injective fun j : Fin Xe.count => comp (Xe.componentEquiv j) :=
    comp.injective.comp Xe.componentEquiv.injective
  have hc : Dc.componentEquiv74 (Dc.componentEquiv74.symm (comp (Xe.componentEquiv jx))) =
      comp (Xe.componentEquiv jx) := Dc.componentEquiv74.apply_symm_apply _
  rcases hi : Dc.componentEquiv74.symm (comp (Xe.componentEquiv jx)) with k | j
  · obtain ⟨jx', h1, hP⟩ := harc k
    have h2 : comp (Xe.componentEquiv jx') = comp (Xe.componentEquiv jx) := by
      apply Subtype.ext
      rw [h1, ← hc, hi]
      rfl
    have h3 : jx' = jx := hinj h2
    exact Or.inl ⟨k, h3 ▸ hP⟩
  · obtain ⟨jx', h1, hP⟩ := hloop j
    have h2 : comp (Xe.componentEquiv jx') = comp (Xe.componentEquiv jx) := by
      apply Subtype.ext
      rw [h1, ← hc, hi]
      rfl
    have h3 : jx' = jx := hinj h2
    exact Or.inr ⟨j, h3 ▸ hP⟩

/-- **The end coordinate of the ends of an exit that is a sphere or torus arc exit satisfying the
end coordinate clause** (a loop exit has no end): the end function of every free end of the exit is
`e ∘ f` on the end neighbourhood. -/
theorem slimPieceExit_endCoord_OCL {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n}
    {Z : ZeroDomains W} {C : CuspCores W E} {Hs : Type*} [NormedAddCommGroup Hs]
    [NormedSpace ℝ Hs] (f : W.Carrier → Hs) (x : SlimPieceExit74 Z C)
    (hx : (∃ a : SphereArcExit74 Z C, x = .sphereArc a ∧ ∀ b : Bool, a.ends.kind b = none →
          ∃ (Ne : Set Hs) (e : Hs → ℝ), IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
            (∀ y ∈ (a.ends.near b : Set W.Carrier), f y ∈ Ne) ∧
            ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (f y)) ∨
      (∃ a : TorusArcExit74 Z C, x = .torusArc a ∧ ∀ b : Bool, a.ends.kind b = none →
          ∃ (Ne : Set Hs) (e : Hs → ℝ), IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
            (∀ y ∈ (a.ends.near b : Set W.Carrier), f y ∈ Ne) ∧
            ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (f y)) ∨
      (∃ l : SphereLoopExit74 W, x = .sphereLoop l) ∨ ∃ l : TorusLoopExit74 W, x = .torusLoop l)
    (b : Bool) (h : slimModelIsInterval x.model) (hk : x.endKind b h = none) :
    ∃ (Ne : Set Hs) (e : Hs → ℝ), IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
      (∀ y ∈ (x.endNear b h : Set W.Carrier), f y ∈ Ne) ∧
      ∀ y ∈ (x.endNear b h : Set W.Carrier), x.endFn b h y = e (f y) := by
  rcases hx with ⟨a, rfl, hend⟩ | ⟨a, rfl, hend⟩ | ⟨l, rfl⟩ | ⟨l, rfl⟩
  · exact hend b hk
  · exact hend b hk
  · exact h.elim
  · exact h.elim

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

/-- **The end coordinate of a new slim end of the chosen exit** (G3): for every new end `en` of
the slim pieces of `slimExitAt2_OCL`, the face function of the residual face `.inr en` is
`e ∘ f₃ ∘ ψ⁻¹` on its neighbourhood, `e` smooth on an open `Ne ∋ f₃ (ψ⁻¹ y)`. -/
theorem slimEnd_coord_OCL
    (en : (slimPiecesOfExits74 (S.slimExitAt2_OCL B hT hεr A hK).exit
      (S.slimExitAt2_OCL B hT hεr A hK).disjoint).NewEnd) :
    ∃ (Ne : Set S.blockSpace_R74) (e : S.blockSpace_R74 → ℝ), IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
      (∀ y ∈ ((slimPiecesOfExits74 (S.slimExitAt2_OCL B hT hεr A hK).exit
          (S.slimExitAt2_OCL B hT hεr A hK).disjoint).residualNear (.inr en) : Set W.Carrier),
        S.chain.slimMap_ZSP35 (M.ψ.symm y) ∈ Ne) ∧
      ∀ y ∈ ((slimPiecesOfExits74 (S.slimExitAt2_OCL B hT hεr A hK).exit
          (S.slimExitAt2_OCL B hT hεr A hK).disjoint).residualNear (.inr en) : Set W.Carrier),
        (slimPiecesOfExits74 (S.slimExitAt2_OCL B hT hεr A hK).exit
          (S.slimExitAt2_OCL B hT hεr A hK).disjoint).residualFn (.inr en) y =
          e (S.chain.slimMap_ZSP35 (M.ψ.symm y)) := by
  obtain ⟨harc, hloop⟩ := S.slimExitOf2_rel2_OCL B hT hεr (S.zsp02SmoothExit74 hεr)
    (S.stagesAtZ_OCL B hT hεr A) hK
  have hcov := exit_cover_of_rel_OCL (S.chain.slimD₃_OCL hεr) (S.stagesAtZ_OCL B hT hεr A).comp
    (S.slimExitAt2_OCL B hT hεr A hK) _ _ harc hloop en.1.1.1
  refine slimPieceExit_endCoord_OCL (fun y => S.chain.slimMap_ZSP35 (M.ψ.symm y))
    ((S.slimExitAt2_OCL B hT hεr A hK).exit en.1.1.1) ?_ en.1.1.2 en.1.2 en.2
  rcases hcov with ⟨k, ⟨a, ha, -, -, hend⟩ | ⟨a, ha, -, -, hend⟩⟩ |
    ⟨j, ⟨l, hl, -⟩ | ⟨l, hl, -⟩⟩
  exacts [Or.inl ⟨a, ha, hend⟩, Or.inr (Or.inl ⟨a, ha, hend⟩),
    Or.inr (Or.inr (Or.inl ⟨l, hl⟩)), Or.inr (Or.inr (Or.inr ⟨l, hl⟩))]

/-- **The face function of a new slim end is constant on the `E`-fibres** (G3, the shape of
`zero_ratio_fibreConst_JN74`): two points of the neighbourhood of the end whose carrier preimages
have the same `E` have the same residual face function (`f₃ = Q₃ ∘ E`). -/
theorem slimEnd_fibreConst_OCL
    (en : (slimPiecesOfExits74 (S.slimExitAt2_OCL B hT hεr A hK).exit
      (S.slimExitAt2_OCL B hT hεr A hK).disjoint).NewEnd) {y y' : W.Carrier}
    (hy : y ∈ ((slimPiecesOfExits74 (S.slimExitAt2_OCL B hT hεr A hK).exit
      (S.slimExitAt2_OCL B hT hεr A hK).disjoint).residualNear (.inr en) : Set W.Carrier))
    (hy' : y' ∈ ((slimPiecesOfExits74 (S.slimExitAt2_OCL B hT hεr A hK).exit
      (S.slimExitAt2_OCL B hT hεr A hK).disjoint).residualNear (.inr en) : Set W.Carrier))
    (hE : S.chain.toChain.E (M.ψ.symm y) = S.chain.toChain.E (M.ψ.symm y')) :
    (slimPiecesOfExits74 (S.slimExitAt2_OCL B hT hεr A hK).exit
      (S.slimExitAt2_OCL B hT hεr A hK).disjoint).residualFn (.inr en) y =
    (slimPiecesOfExits74 (S.slimExitAt2_OCL B hT hεr A hK).exit
      (S.slimExitAt2_OCL B hT hεr A hK).disjoint).residualFn (.inr en) y' := by
  obtain ⟨Ne, e, -, -, -, hfe⟩ := S.slimEnd_coord_OCL B hT hεr A hK en
  refine endFn_fibreConst_of_coord_OCL (f := fun y => S.chain.slimMap_ZSP35 (M.ψ.symm y))
    hfe hy hy' ?_
  unfold Gaf02ChainE.slimMap_ZSP35
  rw [hE]

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse

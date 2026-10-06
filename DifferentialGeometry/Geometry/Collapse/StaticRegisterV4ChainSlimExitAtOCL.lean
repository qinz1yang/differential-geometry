import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGate4OCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimLoopExitsRel74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimArcExits74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimZeroEndFace74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimPiecesOfExits74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RowsLinkOfStage74

/-!
# Draft 74, clause (b) of the closed gate: `SlimExit74` at the produced cut choice `D_R`

Lane C14-REG-CHAIN (by S-REG-CHAIN5), G40 (with the binding rules of review 78, D78-6). For ANY
stage-geometry record `P` of the closed route at `D_R` (so in particular
`S.stagesAtZ_OCL B hT hεr A`) one slim piece exit for every arc (G39 `slim_arc_exit74`,
zero-face ends by G38 `zero_end_face74`) and every loop (G39 `slim_loop_exit_rel74`) of `D₃` of
`D_R`, assembled into `SlimExit74 P.A P.cut` through the component equivalence `P.comp`:

* `exists_slimExit74_of_exits` (kernel): `SlimExit74 A D` from per-arc and per-loop exits with
  image `ψ(q⁻¹(piece))` over the one-dimensional domain `Dc` of a stage identification
  (`StageIdent_LND74`) and a component equivalence `comp : ActualComponent D.D₃ ≃
  ActualComponent Dc.carrier` compatible with `ι`; the exit of the component of arc `k` (resp.
  loop `j`) satisfies any predicate the per-arc (resp. per-loop) exit satisfies;
* `ClosedChainEZRowsSource_RGC.exists_slimExit_rel_OCL`: the exit of the component of every arc is
  the sphere / torus arc exit with the projection identity and both whole end fibres, the exit
  of the component of every loop is the sphere / torus `overCircle` loop exit whose circle
  projection satisfies `p y = exp(2π t) ↔ f₃(ψ⁻¹ y) = loop j t` (monodromy kept, no product
  asserted); `nonempty_slimExit_OCL` is the clause (b) input `X : SlimExit74 P.A P.cut`.
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

universe v w

/-- **`SlimExit74` from per-arc and per-loop exits**: given the identification `hid` of the slim
stage with a map `q` through `ψ`, a one-dimensional domain `Dc` whose components correspond to
those of `D.D₃` (`comp`, compatible with `ι`), and for every arc and loop of `Dc` a slim piece
exit with image `ψ(q⁻¹(arc))` resp. `ψ(q⁻¹(loop))` satisfying `Parc k` resp. `Ploop j`. The exit
assigned to the component of arc `k` (resp. loop `j`) satisfies `Parc k` (resp. `Ploop j`). -/
theorem exists_slimExit74_of_exits {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n}
    {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A} {X : Type v}
    {H : Type w} [NormedAddCommGroup H] [NormedSpace ℝ H] {Bs : Set H} {ψ : X ≃ W.Carrier}
    {q : X → H} {ι : A.slim.Base → H}
    (hid : StageIdent_LND74 ψ A.slim.toStageProj74 q ι) (Dc : SmoothCompactOneDomain_BCF Bs)
    (comp : ActualComponent D.D₃ ≃ ActualComponent Dc.carrier)
    (hcomp : ∀ c, ι '' c.1 = (comp c).1)
    (Parc : Fin Dc.m → SlimPieceExit74 A.zero A.cusp → Prop)
    (Ploop : Fin Dc.l → SlimPieceExit74 A.zero A.cusp → Prop)
    (arcX : ∀ k : Fin Dc.m, ∃ x : SlimPieceExit74 A.zero A.cusp,
      range x.piece.map = ψ '' (q ⁻¹' (Dc.arc k '' Icc 0 1)) ∧ Parc k x)
    (loopX : ∀ j : Fin Dc.l, ∃ x : SlimPieceExit74 A.zero A.cusp,
      range x.piece.map = ψ '' (q ⁻¹' range (Dc.loop j)) ∧ Ploop j x) :
    ∃ Xe : SlimExit74 A D,
      (∀ k : Fin Dc.m, ∃ jx : Fin Xe.count,
        (comp (Xe.componentEquiv jx)).1 = Dc.arc k '' Icc 0 1 ∧ Parc k (Xe.exit jx)) ∧
      ∀ j : Fin Dc.l, ∃ jx : Fin Xe.count,
        (comp (Xe.componentEquiv jx)).1 = range (Dc.loop j) ∧ Ploop j (Xe.exit jx) := by
  choose xa ha hpa using arcX
  choose xl hl hpl using loopX
  have hR : ∀ i : Fin Dc.m ⊕ Fin Dc.l,
      range (Sum.elim xa xl i).piece.map = ψ '' (q ⁻¹' Dc.piece74 i) := by
    rintro (k | j)
    · exact ha k
    · exact hl j
  let Xe : SlimExit74 A D := {
    count := Dc.m + Dc.l
    exit := fun j => Sum.elim xa xl (finSumFinEquiv.symm j)
    componentEquiv := finSumFinEquiv.symm.trans (Dc.componentEquiv74.trans comp.symm)
    piece_range := fun j => by
      change range (Sum.elim xa xl (finSumFinEquiv.symm j)).piece.map = {x |
        ∃ h : x ∈ A.slim.parent,
          A.slim.proj ⟨x, h⟩ ∈ (comp.symm (Dc.componentEquiv74 (finSumFinEquiv.symm j))).1}
      rw [hR, stageSet_LND74 hid, hcomp, comp.apply_symm_apply]
      rfl }
  refine ⟨Xe, fun k => ⟨finSumFinEquiv (Sum.inl k), ?_, ?_⟩,
    fun j => ⟨finSumFinEquiv (Sum.inr j), ?_, ?_⟩⟩
  · change (comp (comp.symm (Dc.componentEquiv74
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl k)))))).1 = _
    rw [Equiv.symm_apply_apply, comp.apply_symm_apply]
    rfl
  · change Parc k (Sum.elim xa xl (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl k))))
    rw [Equiv.symm_apply_apply]
    exact hpa k
  · change (comp (comp.symm (Dc.componentEquiv74
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j)))))).1 = _
    rw [Equiv.symm_apply_apply, comp.apply_symm_apply]
    rfl
  · change Ploop j (Sum.elim xa xl (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))))
    rw [Equiv.symm_apply_apply]
    exact hpl j

end GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (zero : ZSP02SmoothExit74 S)
  (P : ClosedStageGeometryU74 (S.goodCut_OCL B hT hεr) zero)

/-- **Clause (b) of the closed gate at `D_R`, with the binding relations**: the slim exit of the
stage geometry `P` and its cut, over the arcs and loops of `D₃` of `D_R`. The exit of the
component of arc `k` is a sphere / torus arc exit with the projection identity
`f₃(ψ⁻¹(F (z, t))) = arc k t` and both end slices the whole end fibres; the exit of the component
of loop `j` is a sphere / torus loop exit over the whole preimage of the loop whose circle
projection satisfies `p y = exp(2π t) ↔ f₃(ψ⁻¹ y) = loop j t`. -/
theorem exists_slimExit_rel_OCL (hK : 5 ≤ K) :
    ∃ Xe : SlimExit74 P.A P.cut,
      (∀ k : Fin (S.chain.slimD₃_OCL hεr).m, ∃ jx : Fin Xe.count,
        (P.comp (Xe.componentEquiv jx)).1 = (S.chain.slimD₃_OCL hεr).arc k '' Icc 0 1 ∧
        ((∃ a : SphereArcExit74 P.A.zero P.A.cusp, Xe.exit jx = .sphereArc a ∧
            (∀ z, S.chain.slimMap_ZSP35 (M.ψ.symm (a.F z)) =
              (S.chain.slimD₃_OCL hεr).arc k z.2) ∧
            ∀ b, range (fun z => a.F (z, iccEnd b)) = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
              {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)})) ∨
          (∃ a : TorusArcExit74 P.A.zero P.A.cusp, Xe.exit jx = .torusArc a ∧
            (∀ z, S.chain.slimMap_ZSP35 (M.ψ.symm (a.F z)) =
              (S.chain.slimD₃_OCL hεr).arc k z.2) ∧
            ∀ b, range (fun z => a.F (z, iccEnd b)) = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
              {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)})))) ∧
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
              S.chain.slimMap_ZSP35 (M.ψ.symm y) = (S.chain.slimD₃_OCL hεr).loop j t)) := by
  obtain ⟨hD, hKs, hKF, -⟩ := S.chain.slimDomains_spec_OCL hεr
  have hdD := S.goodCut_D₃_bdry_OCL B hT hεr
  have hDreg := S.goodCut_D₃_reg_OCL B hT hεr
  refine exists_slimExit74_of_exits P.slim_ident (S.chain.slimD₃_OCL hεr) P.comp P.comp_eq
    (fun k x => (∃ a : SphereArcExit74 P.A.zero P.A.cusp, x = .sphereArc a ∧
        (∀ z, S.chain.slimMap_ZSP35 (M.ψ.symm (a.F z)) = (S.chain.slimD₃_OCL hεr).arc k z.2) ∧
        ∀ b, range (fun z => a.F (z, iccEnd b)) = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
          {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)})) ∨
      (∃ a : TorusArcExit74 P.A.zero P.A.cusp, x = .torusArc a ∧
        (∀ z, S.chain.slimMap_ZSP35 (M.ψ.symm (a.F z)) = (S.chain.slimD₃_OCL hεr).arc k z.2) ∧
        ∀ b, range (fun z => a.F (z, iccEnd b)) = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
          {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)})))
    (fun j x => (∃ l : SphereLoopExit74 W, x = .sphereLoop l ∧
        l.region.O = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹' range ((S.chain.slimD₃_OCL hεr).loop j)) ∧
        ∀ y ∈ l.region.O, ∀ t : ℝ, l.p y = Circle.exp (2 * Real.pi * t) ↔
          S.chain.slimMap_ZSP35 (M.ψ.symm y) = (S.chain.slimD₃_OCL hεr).loop j t) ∨
      (∃ l : TorusLoopExit74 W, x = .torusLoop l ∧
        l.region.O = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹' range ((S.chain.slimD₃_OCL hεr).loop j)) ∧
        ∀ y ∈ l.region.O, ∀ t : ℝ, l.p y = Circle.exp (2 * Real.pi * t) ↔
          S.chain.slimMap_ZSP35 (M.ψ.symm y) = (S.chain.slimD₃_OCL hεr).loop j t))
    (fun k => ?_) (fun j => ?_)
  · obtain ⟨x, hx, hrel⟩ := S.chain.slim_arc_exit74 hεr hK M.ψ M.boundary_empty_R74
      (S.chain.slimK₃_OCL hεr) (S.chain.slimD₃_OCL hεr) hD hKs hKF hDreg hdD
      (fun y hy hs hne => S.zero_end_face74 zero hεr hy hs hne) k
    exact ⟨x, hx, hrel⟩
  · obtain ⟨x, hx, hrel⟩ := S.chain.slim_loop_exit_rel74 hK M.ψ M.boundary_empty_R74
      (S.chain.slimD₃_OCL hεr) j
    exact ⟨x, hx, hrel⟩

/-- **Clause (b) of the closed gate at `D_R`**: `X : SlimExit74 P.A P.cut`. -/
theorem nonempty_slimExit_OCL (hK : 5 ≤ K) : Nonempty (SlimExit74 P.A P.cut) :=
  (S.exists_slimExit_rel_OCL B hT hεr zero P hK).elim fun Xe _ => ⟨Xe⟩

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse

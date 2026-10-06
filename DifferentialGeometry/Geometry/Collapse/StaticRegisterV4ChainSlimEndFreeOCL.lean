import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimExitAt3OCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimEndCoordOCL

/-!
# Draft 74, G4: the end classification of the ends of the chosen exit `slimExitAt3_OCL`

Lane C14-REG-CHAIN (by S-REG-CHAIN6), G4 (suffix `_OCL`). Per-exit and per-end forms of the end
classification of `exists_slimExit_rel3_OCL`, and the G3 consequences (end coordinate, `E`-fibre
constancy) restated for the exit `slimExitAt3_OCL`:

* `exit_cover_comp_of_rel_OCL` (kernel): `exit_cover_of_rel_OCL` together with the identification
  of the component of the exit;
* `slimPieceExit_endData_OCL` (kernel): the end slice and the end classification of an exit that is
  an arc exit satisfying them; `slimPieceExit_noEnd_OCL`: a loop exit has no end;
* `slimEnd_free_iff_OCL`: for EVERY end `e` of the pieces of `slimExitAt3_OCL`: the arc `k` of
  `D₃` whose component carries the exit of `e`, the end set of `e` is the `ψ`-image of the whole
  `f₃`-fibre over the end value `arc k (iccEnd b)`, and `e` is a free (new) end iff that end value
  is not a slim face point;
* `slimEnd3_coord_OCL`, `slimEnd3_fibreConst_OCL`: as G3's `slimEnd_coord_OCL` /
  `slimEnd_fibreConst_OCL` for `slimExitAt3_OCL`.
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

/-- **Every exit of a slim exit is the exit of an arc or of a loop, with its component**: as
`exit_cover_of_rel_OCL`, keeping the identification of the component of the exit. -/
theorem exit_cover_comp_of_rel_OCL {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n}
    {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {Bs : Set H}
    (Dc : SmoothCompactOneDomain_BCF Bs) (comp : ActualComponent D.D₃ ≃ ActualComponent Dc.carrier)
    (Xe : SlimExit74 A D) (Parc : Fin Dc.m → Fin Xe.count → Prop)
    (Ploop : Fin Dc.l → Fin Xe.count → Prop)
    (harc : ∀ k : Fin Dc.m, ∃ jx : Fin Xe.count,
      (comp (Xe.componentEquiv jx)).1 = Dc.arc k '' Icc 0 1 ∧ Parc k jx)
    (hloop : ∀ j : Fin Dc.l, ∃ jx : Fin Xe.count,
      (comp (Xe.componentEquiv jx)).1 = range (Dc.loop j) ∧ Ploop j jx) (jx : Fin Xe.count) :
    (∃ k, (comp (Xe.componentEquiv jx)).1 = Dc.arc k '' Icc 0 1 ∧ Parc k jx) ∨
      ∃ j, (comp (Xe.componentEquiv jx)).1 = range (Dc.loop j) ∧ Ploop j jx := by
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
    subst h3
    exact Or.inl ⟨k, h1, hP⟩
  · obtain ⟨jx', h1, hP⟩ := hloop j
    have h2 : comp (Xe.componentEquiv jx') = comp (Xe.componentEquiv jx) := by
      apply Subtype.ext
      rw [h1, ← hc, hi]
      rfl
    have h3 : jx' = jx := hinj h2
    subst h3
    exact Or.inr ⟨j, h1, hP⟩

/-- **A loop exit has no end.** -/
theorem slimPieceExit_noEnd_OCL {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n}
    {Z : ZeroDomains W} {C : CuspCores W E} (x : SlimPieceExit74 Z C)
    (hx : (∃ l : SphereLoopExit74 W, x = .sphereLoop l) ∨ ∃ l : TorusLoopExit74 W,
      x = .torusLoop l) (h : slimModelIsInterval x.model) : False := by
  rcases hx with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · exact h.elim
  · exact h.elim

/-- **The end slice and the end classification of an exit that is a sphere or torus arc exit
satisfying them**: for given end slices `Sl b` and end conditions `Pb b`, an exit `x` that is an arc
exit with `range (F (·, iccEnd b)) = Sl b` and `kind b = none ↔ Pb b` has, at every end `b`,
`slice b = Sl b` and `endKind b = none ↔ Pb b`. -/
theorem slimPieceExit_endData_OCL {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n}
    {Z : ZeroDomains W} {C : CuspCores W E} (x : SlimPieceExit74 Z C)
    (Sl : Bool → Set W.Carrier) (Pb : Bool → Prop)
    (hx : (∃ a : SphereArcExit74 Z C, x = .sphereArc a ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) = Sl b) ∧
          ∀ b : Bool, a.ends.kind b = none ↔ Pb b) ∨
      (∃ a : TorusArcExit74 Z C, x = .torusArc a ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) = Sl b) ∧
          ∀ b : Bool, a.ends.kind b = none ↔ Pb b))
    (b : Bool) (h : slimModelIsInterval x.model) :
    x.slice b = Sl b ∧ (x.endKind b h = none ↔ Pb b) := by
  rcases hx with ⟨a, rfl, hsl, hiff⟩ | ⟨a, rfl, hsl, hiff⟩
  · exact ⟨hsl b, hiff b⟩
  · exact ⟨hsl b, hiff b⟩

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

/-- **The end classification of the ends of the chosen exit** (G4): for EVERY end `e` of the
slim pieces of `slimExitAt3_OCL`, the arc `k` of `D₃` whose component carries the exit of `e`
(`P.comp (componentEquiv e.1.1)` is the arc image), the end set of `e` is the `ψ`-image of the
whole `f₃`-fibre over the end value `arc k (iccEnd e.1.2)`, and `e` is a free end (`endKind e =
none`, a new end) iff that end value is not a slim face point. -/
theorem slimEnd_free_iff_OCL
    (e : (slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
      (S.slimExitAt3_OCL B hT hεr A hK).disjoint).End) :
    ∃ k : Fin (S.chain.slimD₃_OCL hεr).m,
      ((S.stagesAtZ_OCL B hT hεr A).comp
        ((S.slimExitAt3_OCL B hT hεr A hK).componentEquiv e.1.1)).1 =
          (S.chain.slimD₃_OCL hεr).arc k '' Icc 0 1 ∧
      (slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
        (S.slimExitAt3_OCL B hT hεr A hK).disjoint).endSet e =
          M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
            {(S.chain.slimD₃_OCL hεr).arc k (iccEnd e.1.2)}) ∧
      ((slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
        (S.slimExitAt3_OCL B hT hεr A hK).disjoint).endKind e = none ↔
          (S.chain.slimD₃_OCL hεr).arc k (iccEnd e.1.2) ∉ S.chain.slimFacePoints_ZSP35) := by
  obtain ⟨harc, hloop⟩ := S.slimExitOf3_rel3_OCL B hT hεr (S.zsp02SmoothExit74 hεr)
    (S.stagesAtZ_OCL B hT hεr A) hK
  have hcov := exit_cover_comp_of_rel_OCL (S.chain.slimD₃_OCL hεr)
    (S.stagesAtZ_OCL B hT hεr A).comp (S.slimExitAt3_OCL B hT hεr A hK) _ _ harc hloop e.1.1
  rcases hcov with ⟨k, hkc, ⟨a, ha, -, hsl, -, hiff⟩ | ⟨a, ha, -, hsl, -, hiff⟩⟩ |
    ⟨j, -, ⟨l, hl, -⟩ | ⟨l, hl, -⟩⟩
  · have hd := slimPieceExit_endData_OCL ((S.slimExitAt3_OCL B hT hεr A hK).exit e.1.1)
      (fun b => M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹' {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)}))
      (fun b => (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∉ S.chain.slimFacePoints_ZSP35)
      (Or.inl ⟨a, ha, hsl, hiff⟩) e.1.2 e.2
    exact ⟨k, hkc, ((S.slimExitAt3_OCL B hT hεr A hK).exit e.1.1).image_end_eq e.1.2 e.2 |>.trans
      hd.1, hd.2⟩
  · have hd := slimPieceExit_endData_OCL ((S.slimExitAt3_OCL B hT hεr A hK).exit e.1.1)
      (fun b => M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹' {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)}))
      (fun b => (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∉ S.chain.slimFacePoints_ZSP35)
      (Or.inr ⟨a, ha, hsl, hiff⟩) e.1.2 e.2
    exact ⟨k, hkc, ((S.slimExitAt3_OCL B hT hεr A hK).exit e.1.1).image_end_eq e.1.2 e.2 |>.trans
      hd.1, hd.2⟩
  · exact (slimPieceExit_noEnd_OCL _ (Or.inl ⟨l, hl⟩) e.2).elim
  · exact (slimPieceExit_noEnd_OCL _ (Or.inr ⟨l, hl⟩) e.2).elim

/-- **The end coordinate of a new slim end of the chosen exit** (G3 for the exit of G4): for every
new end `en` of the slim pieces of `slimExitAt3_OCL`, the face function of the residual face
`.inr en` is `e ∘ f₃ ∘ ψ⁻¹` on its neighbourhood, `e` smooth on an open `Ne ∋ f₃ (ψ⁻¹ y)`. -/
theorem slimEnd3_coord_OCL
    (en : (slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
      (S.slimExitAt3_OCL B hT hεr A hK).disjoint).NewEnd) :
    ∃ (Ne : Set S.blockSpace_R74) (e : S.blockSpace_R74 → ℝ), IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
      (∀ y ∈ ((slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
          (S.slimExitAt3_OCL B hT hεr A hK).disjoint).residualNear (.inr en) : Set W.Carrier),
        S.chain.slimMap_ZSP35 (M.ψ.symm y) ∈ Ne) ∧
      ∀ y ∈ ((slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
          (S.slimExitAt3_OCL B hT hεr A hK).disjoint).residualNear (.inr en) : Set W.Carrier),
        (slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
          (S.slimExitAt3_OCL B hT hεr A hK).disjoint).residualFn (.inr en) y =
          e (S.chain.slimMap_ZSP35 (M.ψ.symm y)) := by
  obtain ⟨harc, hloop⟩ := S.slimExitOf3_rel3_OCL B hT hεr (S.zsp02SmoothExit74 hεr)
    (S.stagesAtZ_OCL B hT hεr A) hK
  have hcov := exit_cover_of_rel_OCL (S.chain.slimD₃_OCL hεr) (S.stagesAtZ_OCL B hT hεr A).comp
    (S.slimExitAt3_OCL B hT hεr A hK) _ _ harc hloop en.1.1.1
  refine slimPieceExit_endCoord_OCL (fun y => S.chain.slimMap_ZSP35 (M.ψ.symm y))
    ((S.slimExitAt3_OCL B hT hεr A hK).exit en.1.1.1) ?_ en.1.1.2 en.1.2 en.2
  rcases hcov with ⟨k, ⟨a, ha, -, -, hend, -⟩ | ⟨a, ha, -, -, hend, -⟩⟩ |
    ⟨j, ⟨l, hl, -⟩ | ⟨l, hl, -⟩⟩
  exacts [Or.inl ⟨a, ha, hend⟩, Or.inr (Or.inl ⟨a, ha, hend⟩),
    Or.inr (Or.inr (Or.inl ⟨l, hl⟩)), Or.inr (Or.inr (Or.inr ⟨l, hl⟩))]

/-- **The face function of a new slim end is constant on the `E`-fibres** (G3 for the exit of G4,
the shape of
`zero_ratio_fibreConst_JN74`): two points of the neighbourhood of the end whose carrier preimages
have the same `E` have the same residual face function (`f₃ = Q₃ ∘ E`). -/
theorem slimEnd3_fibreConst_OCL
    (en : (slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
      (S.slimExitAt3_OCL B hT hεr A hK).disjoint).NewEnd) {y y' : W.Carrier}
    (hy : y ∈ ((slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
      (S.slimExitAt3_OCL B hT hεr A hK).disjoint).residualNear (.inr en) : Set W.Carrier))
    (hy' : y' ∈ ((slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
      (S.slimExitAt3_OCL B hT hεr A hK).disjoint).residualNear (.inr en) : Set W.Carrier))
    (hE : S.chain.toChain.E (M.ψ.symm y) = S.chain.toChain.E (M.ψ.symm y')) :
    (slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
      (S.slimExitAt3_OCL B hT hεr A hK).disjoint).residualFn (.inr en) y =
    (slimPiecesOfExits74 (S.slimExitAt3_OCL B hT hεr A hK).exit
      (S.slimExitAt3_OCL B hT hεr A hK).disjoint).residualFn (.inr en) y' := by
  obtain ⟨Ne, e, -, -, -, hfe⟩ := S.slimEnd3_coord_OCL B hT hεr A hK en
  refine endFn_fibreConst_of_coord_OCL (f := fun y => S.chain.slimMap_ZSP35 (M.ψ.symm y))
    hfe hy hy' ?_
  unfold Gaf02ChainE.slimMap_ZSP35
  rw [hE]

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse

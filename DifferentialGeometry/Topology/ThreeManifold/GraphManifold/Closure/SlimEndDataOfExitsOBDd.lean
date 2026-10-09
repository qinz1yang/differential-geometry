import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimPiecesOfExits74

/-!
# End data of the slim pieces from the arc exits (S-BD2d2, `_OBDd`), group G10f

Lane O-BD1 (by S-BD2d2), `SlimCutPieces74`. Generic kernels (no chain, no boundary vocabulary)
turning per-exit arc data into per-end data of `slimPiecesOfExits74`, as the closed twins
`slimPieceExit_endData_OCL` / `exit_cover_comp_of_rel_OCL` / `slimPieceExit_isInterval_OCL`
(with the defining-function clause of `rel3` carried along):

* `slimPieceExit_isInterval_OBDd`: an arc exit has an interval model;
* `slimPieceExit_endData_OBDd`: the end slice, the end classification and the defining-function
  clause of an exit that is a sphere / torus arc exit satisfying them;
* `exit_of_component_OBDd`: the exit of the component of an arc piece is the one the family of arc
  exits provides, if every exit lies at some piece and the exits at a piece are unique.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open GC.GraphManifold.Assembly
open scoped ContDiff

namespace GC.GraphManifold.Assembly.FC39P0

/-- **An arc exit has an interval model.** -/
theorem slimPieceExit_isInterval_OBDd {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n}
    {Z : ZeroDomains W} {C : CuspCores W E} (x : SlimPieceExit74 Z C)
    (hx : (∃ a : SphereArcExit74 Z C, x = .sphereArc a) ∨ ∃ a : TorusArcExit74 Z C,
      x = .torusArc a) : slimModelIsInterval x.model := by
  rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact trivial
  · exact trivial

/-- **The end data of an exit that is an arc exit satisfying the `rel3` clauses**: for the end
slices `src ∩ q⁻¹{g (iccEnd b)}` and the classification `g (iccEnd b) ∉ Fs`, an exit `x` that is a
sphere or torus arc exit with the projection identity `q (F z) = g z.2`, whole end fibres, the
defining function of every free end of the form `e ∘ q` on an open `Ne` and
`kind b = none ↔ g (iccEnd b) ∉ Fs` has, at every end `b`, the end slice `src ∩ q⁻¹{g (iccEnd b)}`,
`endKind b = none ↔ g (iccEnd b) ∉ Fs`, and the defining-function clause on `endNear b`. -/
theorem slimPieceExit_endData_OBDd {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n}
    {Z : ZeroDomains W} {Cu : CuspCores W E} {Amb : Type*} [NormedAddCommGroup Amb]
    [NormedSpace ℝ Amb] (q : W.Carrier → Amb) (src : Set W.Carrier) (g : ℝ → Amb)
    (Fs : Set Amb) (x : SlimPieceExit74 Z Cu)
    (hx : (∃ a : SphereArcExit74 Z Cu, x = .sphereArc a ∧ (∀ z, q (a.F z) = g z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) = src ∩ q ⁻¹' {g (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set Amb) (e : Amb → ℝ), IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), q y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (q y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔ g (iccEnd b) ∉ Fs) ∨
        (∃ a : TorusArcExit74 Z Cu, x = .torusArc a ∧ (∀ z, q (a.F z) = g z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) = src ∩ q ⁻¹' {g (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set Amb) (e : Amb → ℝ), IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), q y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (q y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔ g (iccEnd b) ∉ Fs))
    (b : Bool) (h : slimModelIsInterval x.model) :
    x.slice b = src ∩ q ⁻¹' {g (iccEnd b)} ∧ (x.endKind b h = none ↔ g (iccEnd b) ∉ Fs) ∧
      (x.endKind b h = none →
        ∃ (Ne : Set Amb) (e : Amb → ℝ), IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
          (∀ y ∈ (x.endNear b h : Set W.Carrier), q y ∈ Ne) ∧
          ∀ y ∈ (x.endNear b h : Set W.Carrier), x.endFn b h y = e (q y)) := by
  rcases hx with ⟨a, rfl, -, hsl, hco, hiff⟩ | ⟨a, rfl, -, hsl, hco, hiff⟩
  · exact ⟨hsl b, hiff b, hco b⟩
  · exact ⟨hsl b, hiff b, hco b⟩

/-- **The exit at a component is the exit assigned to the piece**: if the exits `Xe.exit` and the
family `pc` are matched by `harc` (an exit `jx` at the component `pc i` satisfying `Q i`) and every
component of `Xe` is one of the `pc i` (`hcov`), then EVERY exit `jx` satisfies `Q i` for the
piece `i` of its component. -/
theorem exit_of_component_OBDd {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n}
    {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A} {Bs : Type*} [TopologicalSpace Bs]
    {Dtot : Set Bs}
    (comp : ActualComponent D.D₃ ≃ ActualComponent Dtot) (Xe : SlimExit74 A D) {N : ℕ}
    (pc : Fin N → Set Bs) (Q : Fin N → SlimPieceExit74 A.zero A.cusp → Prop)
    (harc : ∀ i, ∃ jx : Fin Xe.count,
      (comp (Xe.componentEquiv jx)).1 = pc i ∧ Q i (Xe.exit jx))
    (hcov : ∀ jx : Fin Xe.count, ∃ i, (comp (Xe.componentEquiv jx)).1 = pc i)
    (jx : Fin Xe.count) :
    ∃ i, (comp (Xe.componentEquiv jx)).1 = pc i ∧ Q i (Xe.exit jx) := by
  obtain ⟨i, hi⟩ := hcov jx
  obtain ⟨jx', hi', hQ⟩ := harc i
  have h2 : comp (Xe.componentEquiv jx') = comp (Xe.componentEquiv jx) :=
    Subtype.ext (hi'.trans hi.symm)
  have h3 : jx' = jx := Xe.componentEquiv.injective (comp.injective h2)
  subst h3
  exact ⟨i, hi, hQ⟩

end GC.GraphManifold.Assembly.FC39P0

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OpenCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceTorusFamilyComponent_S19
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeamImage_CX4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedCores
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TruncationLevel

set_option autoImplicit false

/-!
# C5 skeleton: `exists_late_cut_family_assembly_S24` (CH12-S24)

Conclusion identical to A09 `GC.LongTime.exists_late_cut_family`; hypotheses = the A09 ones plus the
explicit inputs below.  Everything already proved is CALLED, not assumed:
`sliceTorusDecomposition_S19` (decomposition + port + seam equation, late j),
`seamImageFamily_of_pointwise_CX4` (`seam_image`), `hyperbolicAlternative_of_truncation_CX1`
(hyperbolic blocks), `cutAlongTori_C2a_S12` (early-j decompositions, empty seam family).

## Remaining inputs (input -> package -> status)
| input | package | status |
|---|---|---|
| `B : BufferedPersistentCores F (K+4)` | H2-H5 production (R1 5.1) | open |
| `base`, `level`, `two_le`, `hball` (collars of level-`level j` truncations lie in B(x,2/acc)) | H-package: truncation levels vs buffer | open |
| `hcore` (`core_in_ball`, truncation inside B(x,1/acc)) | H-package / TruncationLevelDiam | open |
| `hmetric` (every decomposition of a slice component has induced cut metrics) | C2b (metric/induced) | open |
| `hthin`: `thin` predicate, `finite_scales` | C4 (NearlyCuspidalBoundary collar, negative plane, closed-block alternative) | open |
| `hthin` dichotomy per block: thin volume geometry / diffeo of the block interior to a truncation core / closed nonnegative | C4 + HG (block = truncated core identification) + `boundaryVolumeCollapsed` | open |
| `hadm hdec hK` (A09 hypotheses) | not used by the skeleton | kept for A09 signature |
| early `j < first` | decomposition by empty collar family (proved); `thin := False` (proved) | done |
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open GC.Endpoint GC.GraphManifold DifferentialGeometry.Geometry.Hyperbolic Set
open GC.Topology GC.LongTime
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

section Pieces
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- Slice-level adaptation of `sliceTorusDecomposition_S19` along `postStage = Q`. -/
theorem sliceDecomp_S24 {K : ℕ} {cores : PersistentHyperbolicCores F K} {t : ℝ}
    (D : TruncatedCutData_IF4 cores t) (ht : cores.start ≤ t) (Q : OrientedThreeStage.{u})
    (h : postStage F.observation t = Q) :
    ∃ (G : ∀ C : ConnectedComponents Q.Carrier,
        TorusDecomposition (Q.toClosedOrientedManifold.component C))
      (port : (Σ C, Fin (G C).boundary.count) ≃ Σ i : Fin cores.count, Fin (D.truncation i).count),
      ∀ C (b : Fin (G C).boundary.count) (x : Torus),
        cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) h)
          (cores.map (port ⟨C, b⟩).1 t ht
            ((D.truncation (port ⟨C, b⟩).1).cuspMap (port ⟨C, b⟩).2 (x, halfZero))) =
          ((G C).reconstructionAtlas.torusInPrime (G C).reconstruction b x).val := by
  subst h
  obtain ⟨G, port, hG⟩ := sliceTorusDecomposition_S19 D ht
  exact ⟨G, port, fun C b x => (cast_eq _ _).trans (hG C b x).symm⟩

/-- The empty seam family on a component. -/
def emptyFamily_S24 (N : Type*) [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] : CollaredTorusFamily_C2a N where
  count := 0
  collar := fun i => i.elim0
  source_eq := fun i => i.elim0
  disjoint := fun i => i.elim0

/-- The truncation of the `j`-th slice (all `j`, early ones included). -/
def trunc_S24 {K : ℕ} (B : BufferedPersistentCores F K)
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i)) (level : ℕ → ℝ)
    (two_le : ∀ j, 2 ≤ level j) (j : ℕ) (i : Fin B.count) : HyperbolicTruncation (B.model i) :=
  truncationAtLevel_C1 (base i) (two_le j)

end Pieces

/-- Decomposition, port and seam equation for ALL `j` (early `j` get the empty-family cut). -/
theorem exists_decomposition_S24 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ}
    (B : BufferedPersistentCores F (K + 4))
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i)) (level : ℕ → ℝ)
    (two_le : ∀ j, 2 ≤ level j)
    (slices : ℕ → RegularSlice F.observation) (first : ℕ)
    (hfirst : ∀ j, first ≤ j → B.start ≤ (slices j).time)
    (hball : ∀ j, first ≤ j → ∀ i (q : Fin (base i).count) (p : CuspHalfSpace),
      p.2.val 0 ≤ level j + 200 →
        (base i).cuspMap q p ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
          (2 * (B.accuracy (slices j).time)⁻¹)) :
    ∃ dec : ∀ j (C : ConnectedComponents (slices j).stage.Carrier),
        TorusDecomposition ((slices j).stage.toClosedOrientedManifold.component C),
      ∃ port : ∀ j, first ≤ j →
        (Σ C : ConnectedComponents (slices j).stage.Carrier, Fin (dec j C).boundary.count) ≃
          Σ i : Fin B.toCores.count, Fin (trunc_S24 B base level two_le j i).count,
      ∀ j (hj : first ≤ j) C (b : Fin (dec j C).boundary.count) (x : Torus),
        sliceCast_CX4 (slices j)
          (B.toCores.map (port j hj ⟨C, b⟩).1 (slices j).time (hfirst j hj)
            ((trunc_S24 B base level two_le j (port j hj ⟨C, b⟩).1).cuspMap
              (port j hj ⟨C, b⟩).2 (x, halfZero))) =
          ((dec j C).reconstructionAtlas.torusInPrime (dec j C).reconstruction b x).val := by
  have key : ∀ j, ∃ G : ∀ C : ConnectedComponents (slices j).stage.Carrier,
      TorusDecomposition ((slices j).stage.toClosedOrientedManifold.component C),
      ∀ hj : first ≤ j, ∃ port : (Σ C : ConnectedComponents (slices j).stage.Carrier,
          Fin (G C).boundary.count) ≃
          Σ i : Fin B.toCores.count, Fin (trunc_S24 B base level two_le j i).count,
        ∀ C (b : Fin (G C).boundary.count) (x : Torus),
          sliceCast_CX4 (slices j)
            (B.toCores.map (port ⟨C, b⟩).1 (slices j).time (hfirst j hj)
              ((trunc_S24 B base level two_le j (port ⟨C, b⟩).1).cuspMap
                (port ⟨C, b⟩).2 (x, halfZero))) =
            ((G C).reconstructionAtlas.torusInPrime (G C).reconstruction b x).val := by
    intro j
    by_cases hj : first ≤ j
    · let D : TruncatedCutData_IF4 B.toCores (slices j).time :=
        TruncatedCutData_IF4.ofBuffered_S19 B (hfirst j hj) base (level j) (two_le j)
          (hball j hj)
      obtain ⟨G, port, hG⟩ := sliceDecomp_S24 D (hfirst j hj) (slices j).stage
        (postStage_eq_sliceStage_CX4 (slices j))
      exact ⟨G, fun _ => ⟨port, hG⟩⟩
    · choose G _ using fun C : ConnectedComponents (slices j).stage.Carrier =>
        cutAlongTori_C2a_S12 ((slices j).stage.toClosedOrientedManifold.component C)
          (emptyFamily_S24 _)
      exact ⟨G, fun h => absurd h hj⟩
  choose dec hdec using key
  exact ⟨dec, fun j hj => (hdec j hj).choose, fun j hj => (hdec j hj).choose_spec⟩

/-- **C5 skeleton.** Conclusion verbatim `exists_late_cut_family`; extra inputs tabulated in the
file header. -/
theorem exists_late_cut_family_assembly_S24 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
    -- (i) buffered cores and truncation levels (H2-H5 production, H-package)
    (B : BufferedPersistentCores F (K + 4))
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i)) (level : ℕ → ℝ)
    (two_le : ∀ j, 2 ≤ level j)
    (hball : ∀ j, ⌈B.start⌉₊ ≤ j → ∀ i (q : Fin (base i).count) (p : CuspHalfSpace),
      p.2.val 0 ≤ level j + 200 →
        (base i).cuspMap q p ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
          (2 * (B.accuracy (slices j).time)⁻¹))
    (hcore : ∀ j, ⌈B.start⌉₊ ≤ j → ∀ i : Fin B.count,
      Set.range (trunc_S24 B base level two_le j i).inclusion ⊆
        riemannianBallOf (B.model i).metric (B.model i).basepoint
          (B.accuracy (slices j).time)⁻¹)
    -- (ii) C2b: induced cut metrics for every torus decomposition of a slice component
    (hmetric : ∀ j (C : ConnectedComponents (slices j).stage.Carrier)
      (D : TorusDecomposition ((slices j).stage.toClosedOrientedManifold.component C)),
      ∃ met : ∀ i : Fin D.components.count,
          SmoothRiemannianMetric (D.component i).model (D.component i).Carrier,
        ∀ i, isInducedCutMetric ((slices j).componentMetric C) D i (met i))
    -- (iii) C4: thin predicate, finite scales and the block dichotomy, for the actual cut
    (hthin : ∀ (dec : ∀ j (C : ConnectedComponents (slices j).stage.Carrier),
          TorusDecomposition ((slices j).stage.toClosedOrientedManifold.component C))
      (met : ∀ j C (i : Fin (dec j C).components.count),
          SmoothRiemannianMetric ((dec j C).component i).model ((dec j C).component i).Carrier),
      (∀ j C i, isInducedCutMetric ((slices j).componentMetric C) (dec j C) i (met j C i)) →
      ∃ thin : ∀ j (C : ConnectedComponents (slices j).stage.Carrier),
          Fin (dec j C).components.count → Prop,
        (∀ j, ⌈B.start⌉₊ ≤ j → ∀ C i, thin j C i → ∀ p, curvatureRadius (met j C i) p ≠ ⊤) ∧
        ∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume →
          ∃ N : ℕ, ∀ j, N ≤ j → ∀ C (i : Fin (dec j C).components.count),
            (thin j C i ∧ hasThinVolumeGeometry ((dec j C).component i) (met j C i) K w) ∨
            (¬ thin j C i ∧
              ((∃ c : Fin B.count, Nonempty (Diffeomorph (dec j C).carrier.model
                  (trunc_S24 B base level two_le j c).core.model
                  ((dec j C).carrier.pieceInterior ((dec j C).components.piece i))
                  (trunc_S24 B base level two_le j c).core.interior ∞)) ∨
                (((dec j C).component i).model.boundary ((dec j C).component i).Carrier = ∅ ∧
                  DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow
                    (met j C i) 0)))) :
    Nonempty (LateCutFamily F K slices) := by
  classical
  set first : ℕ := ⌈B.start⌉₊ with hfirst_def
  have hfirst : ∀ j, first ≤ j → B.start ≤ (slices j).time := fun j hj =>
    ((Nat.le_ceil B.start).trans (by exact_mod_cast hj)).trans (htimes j).le
  obtain ⟨dec, port, hport⟩ := exists_decomposition_S24 B base level two_le slices first hfirst
    (fun j hj => hball j hj)
  choose met hind using fun j C => hmetric j C (dec j C)
  obtain ⟨thin0, hfin, halt⟩ := hthin dec met hind
  refine ⟨{
    cores := B.toCores
    decomposition := dec
    metric := met
    induced := hind
    thin := fun j C i => first ≤ j ∧ thin0 j C i
    first := first
    time_late := hfirst
    truncation := fun j i => trunc_S24 B base level two_le j i
    port := port
    core_in_ball := hcore
    seam_image := ?_
    finite_scales := fun j C i hi => hfin j hi.1 C i hi.2
    alternatives := ?_ }⟩
  · exact seamImageFamily_of_pointwise_CX4 slices B.toCores dec first hfirst
      (fun j i => trunc_S24 B base level two_le j i) port (fun _ _ _ _ => Equiv.refl Torus)
      (fun j hj C b x => hport j hj C b x)
  · intro w hw hwc
    obtain ⟨N0, hN0⟩ := halt w hw hwc
    refine ⟨max N0 first, fun j hj C => ?_⟩
    have hj0 : N0 ≤ j := (le_max_left _ _).trans hj
    have hj1 : first ≤ j := (le_max_right _ _).trans hj
    have hi : ∀ i : Fin (dec j C).components.count, Nonempty (HyperbolicOrThin (dec j C) (met j C)
        (fun i => first ≤ j ∧ thin0 j C i) K w i) := by
      intro i
      rcases hN0 j hj0 C i with ⟨hth, hgeo⟩ | ⟨hnot, ⟨c, ⟨e⟩⟩ | ⟨hclosed, hcurv⟩⟩
      · exact ⟨.thin ⟨hj1, hth⟩ hgeo⟩
      · exact hyperbolicAlternative_of_truncation_CX1 (trunc_S24 B base level two_le j c)
          (dec j C) (met j C) (fun i => first ≤ j ∧ thin0 j C i) K w i
          (fun h => hnot h.2) e
      · exact ⟨.nonnegative (fun h => hnot h.2) hclosed hcurv⟩
    exact ⟨fun i => Classical.choice (hi i)⟩

end GC.LongTime.Ch12

#check @GC.LongTime.Ch12.exists_late_cut_family_assembly_S24
#print axioms GC.LongTime.Ch12.exists_late_cut_family_assembly_S24
#print axioms GC.LongTime.Ch12.exists_decomposition_S24

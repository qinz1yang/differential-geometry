import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LateCutAssembly_S24
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RealCutDecomposition_S31
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutMetricMain_S25

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open GC.Endpoint GC.GraphManifold DifferentialGeometry.Geometry.Hyperbolic Set
open GC.Topology GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

theorem ceil_le_time_S31 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {K : ℕ} (B : BufferedPersistentCores F K) (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time) (j : ℕ) (hj : ⌈B.start⌉₊ ≤ j) :
    B.start ≤ (slices j).time :=
  ((Nat.le_ceil B.start).trans (by exact_mod_cast hj)).trans (htimes j).le


variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- Transport of a family of decompositions of the components along an equality of stages. -/
def transportDec_S31 {P' Q : OrientedThreeStage.{u}} (h : P' = Q)
    (G : ∀ C : ConnectedComponents P'.Carrier,
      TorusDecomposition (P'.toClosedOrientedManifold.component C)) :
    ∀ C : ConnectedComponents Q.Carrier, TorusDecomposition (Q.toClosedOrientedManifold.component C) :=
  Eq.rec (motive := fun Q _ => ∀ C : ConnectedComponents Q.Carrier,
    TorusDecomposition (Q.toClosedOrientedManifold.component C)) G h

/-- The real cut of every slice (the `S28` cut of the late slices transported to `(slices j).stage`;
the empty-family cut for early `j`). -/
def realDec_S31 {K : ℕ} (B : BufferedPersistentCores F (K + 4))
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i)) (level : ℕ → ℝ)
    (two_le : ∀ j, 2 ≤ level j) (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hball : ∀ j, ⌈B.start⌉₊ ≤ j → ∀ i (q : Fin (base i).count) (p : CuspHalfSpace),
      p.2.val 0 ≤ level j + 200 →
        (base i).cuspMap q p ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
          (2 * (B.accuracy (slices j).time)⁻¹)) (j : ℕ) :
    ∀ C : ConnectedComponents (slices j).stage.Carrier,
      TorusDecomposition ((slices j).stage.toClosedOrientedManifold.component C) :=
  if hj : ⌈B.start⌉₊ ≤ j then
    transportDec_S31 (postStage_eq_sliceStage_CX4 (slices j))
      (sliceDec_S28 (TruncatedCutData_IF4.ofBuffered_S19 B (ceil_le_time_S31 B slices htimes j hj)
        base (level j) (two_le j) (hball j hj)) (ceil_le_time_S31 B slices htimes j hj))
  else fun C => (cutAlongTori_C2a_S12 ((slices j).stage.toClosedOrientedManifold.component C)
    (emptyFamily_S24 _)).choose


/-- Early/late equation: for late `j` the real cut is the transported `sliceDec_S28`. -/
theorem realDec_eq_S31 {K : ℕ} (B : BufferedPersistentCores F (K + 4))
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i)) (level : ℕ → ℝ)
    (two_le : ∀ j, 2 ≤ level j) (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hball : ∀ j, ⌈B.start⌉₊ ≤ j → ∀ i (q : Fin (base i).count) (p : CuspHalfSpace),
      p.2.val 0 ≤ level j + 200 →
        (base i).cuspMap q p ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
          (2 * (B.accuracy (slices j).time)⁻¹)) (j : ℕ) (hj : ⌈B.start⌉₊ ≤ j) :
    realDec_S31 B base level two_le slices htimes hball j =
      transportDec_S31 (postStage_eq_sliceStage_CX4 (slices j))
        (sliceDec_S28 (TruncatedCutData_IF4.ofBuffered_S19 B (ceil_le_time_S31 B slices htimes j hj)
          base (level j) (two_le j) (hball j hj)) (ceil_le_time_S31 B slices htimes j hj)) := by
  unfold realDec_S31
  simp only [hj, ↓reduceDIte]

/-- Stage-transported port/seam equation for a decomposition family equal to the transported real
cut (the `subst` pattern of `sliceDecomp_S24`). -/
theorem sliceDecompReal_S31 {K : ℕ} {cores : PersistentHyperbolicCores F K} {t : ℝ}
    (D : TruncatedCutData_IF4 cores t) (ht : cores.start ≤ t) (Q : OrientedThreeStage.{u})
    (h : postStage F.observation t = Q)
    (dec : ∀ C : ConnectedComponents Q.Carrier, TorusDecomposition (Q.toClosedOrientedManifold.component C))
    (hdec : dec = transportDec_S31 h (sliceDec_S28 D ht)) :
    ∃ port : (Σ C, Fin (dec C).boundary.count) ≃ Σ i : Fin cores.count, Fin (D.truncation i).count,
      ∀ C (b : Fin (dec C).boundary.count) (x : Torus),
        cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) h)
          (cores.map (port ⟨C, b⟩).1 t ht
            ((D.truncation (port ⟨C, b⟩).1).cuspMap (port ⟨C, b⟩).2 (x, halfZero))) =
          ((dec C).reconstructionAtlas.torusInPrime (dec C).reconstruction b x).val := by
  subst hdec
  subst h
  obtain ⟨port, hport⟩ := sliceTorusDecomposition_S31 D ht
  exact ⟨port, fun C b x => (hport C b x).symm⟩

/-- The domain condition of S28 for the truncation data of a buffered family. -/
theorem hdom_ofBuffered_S31 {K : ℕ} (B : BufferedPersistentCores F (K + 4))
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i)) (level : ℕ → ℝ)
    (two_le : ∀ j, 2 ≤ level j) (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hball : ∀ j, ⌈B.start⌉₊ ≤ j → ∀ i (q : Fin (base i).count) (p : CuspHalfSpace),
      p.2.val 0 ≤ level j + 200 →
        (base i).cuspMap q p ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
          (2 * (B.accuracy (slices j).time)⁻¹))
    (hcore : ∀ j, ⌈B.start⌉₊ ≤ j → ∀ i : Fin B.count,
      Set.range (trunc_S24 B base level two_le j i).inclusion ⊆
        riemannianBallOf (B.model i).metric (B.model i).basepoint
          (B.accuracy (slices j).time)⁻¹)
    (j : ℕ) (hj : ⌈B.start⌉₊ ≤ j) (i : Fin B.count) :
    Set.range ((TruncatedCutData_IF4.ofBuffered_S19 B (ceil_le_time_S31 B slices htimes j hj)
        base (level j) (two_le j) (hball j hj)).truncation i).inclusion ⊆
      (B.toCores.domain i (slices j).time : Set (B.toCores.model i).Carrier) :=
  (hcore j hj i).trans (B.toCores.advertised_ball i (slices j).time
    (ceil_le_time_S31 B slices htimes j hj))

/-- The block dichotomy of the real cut, on the slice stage `Q` (after `subst`: the post-stage
statement `block_core_or_complement_S31`). -/
theorem realBlock_dichotomy_S31 {K : ℕ} {cores : PersistentHyperbolicCores F K} {t : ℝ}
    (D : TruncatedCutData_IF4 cores t) (ht : cores.start ≤ t)
    (hdom : ∀ i, range (D.truncation i).inclusion ⊆ (cores.domain i t : Set (cores.model i).Carrier))
    {Q : OrientedThreeStage.{u}} (h : postStage F.observation t = Q)
    (C : ConnectedComponents Q.Carrier)
    (dec : TorusDecomposition (Q.toClosedOrientedManifold.component C))
    (hdec : dec = transportDec_S31 h (sliceDec_S28 D ht) C) (i : Fin dec.components.count) :
    (∀ c : Fin cores.count,
      Disjoint
        ((fun x => ((dec.reconstruction.val (dec.boundary.quotientMap x)).val : Q.Carrier)) ''
          (dec.carrier.pieceInterior (dec.components.piece i) : Set _))
        ((fun x => cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) h)
            (cores.map c t ht ((D.truncation c).inclusion x))) ''
          ((D.truncation c).core.interior : Set _))) ∨
    ∃ c : Fin cores.count, Nonempty (Diffeomorph dec.carrier.model (D.truncation c).core.model
      (dec.carrier.pieceInterior (dec.components.piece i)) (D.truncation c).core.interior ∞) := by
  subst hdec
  subst h
  rcases block_core_or_complement_S31 D ht hdom C i with hc | ⟨c, -, hd⟩
  · left
    intro c
    by_cases hcc : coreComp_S28 D ht c = C
    · exact hc c hcc
    · refine Set.disjoint_left.mpr ?_
      rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyz⟩
      apply hcc
      have h1 := corePhi_comp_S28 D ht hdom c y
      have h2 : ConnectedComponents.mk (corePhi_S28 D ht c y) = C := by
        have : (corePhi_S28 D ht c y) =
          ((sliceDec_S28 D ht C).reconstruction.val ((sliceDec_S28 D ht C).boundary.quotientMap x)).val :=
          hyz
        rw [this]
        exact ((sliceDec_S28 D ht C).reconstruction.val
          ((sliceDec_S28 D ht C).boundary.quotientMap x)).property
      exact h1.symm.trans h2
  · exact Or.inr ⟨c, hd⟩

/-- **A09 assembly on the real cut (S31).**  Conclusion verbatim `exists_late_cut_family`.  No `hmetric`
(the metric is `cutMetric_S25`), no core-block hypothesis (`block_core_or_complement_S31` +
`hyperbolicAlternative_of_truncation_CX1`); only the thin side for the non-core blocks of the real cut
`realDec_S31` is an input. -/
theorem exists_late_cut_family_assembly_S31 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (_hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (_hadm : hasAnalyticAdmissibility F δ)
    (_hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (_hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
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
    -- thin side: the blocks of the real cut that avoid every core
    (thin : ∀ j (C : ConnectedComponents (slices j).stage.Carrier),
      Fin (realDec_S31 B base level two_le slices htimes hball j C).components.count → Prop)
    (hfin : ∀ j, ⌈B.start⌉₊ ≤ j → ∀ C i, thin j C i → ∀ p,
      curvatureRadius (cutMetric_S25 ((slices j).componentMetric C)
        (realDec_S31 B base level two_le slices htimes hball j C) i) p ≠ ⊤)
    (halt : ∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume →
      ∃ N : ℕ, ∀ j (hj : ⌈B.start⌉₊ ≤ j), N ≤ j →
        ∀ C (i : Fin (realDec_S31 B base level two_le slices htimes hball j C).components.count),
          (∀ c : Fin B.count,
            Disjoint
              ((fun x => (((realDec_S31 B base level two_le slices htimes hball j C).reconstruction.val
                  ((realDec_S31 B base level two_le slices htimes hball j C).boundary.quotientMap x)).val :
                    (slices j).stage.Carrier)) ''
                ((realDec_S31 B base level two_le slices htimes hball j C).carrier.pieceInterior
                  ((realDec_S31 B base level two_le slices htimes hball j C).components.piece i) :
                    Set _))
              ((fun x => sliceCast_CX4 (slices j)
                  (B.toCores.map c (slices j).time (ceil_le_time_S31 B slices htimes j hj)
                    ((trunc_S24 B base level two_le j c).inclusion x))) ''
                ((trunc_S24 B base level two_le j c).core.interior : Set _))) →
          (thin j C i ∧ hasThinVolumeGeometry
              ((realDec_S31 B base level two_le slices htimes hball j C).component i)
              (cutMetric_S25 ((slices j).componentMetric C)
                (realDec_S31 B base level two_le slices htimes hball j C) i) K w) ∨
            (¬ thin j C i ∧
              (((realDec_S31 B base level two_le slices htimes hball j C).component i).model.boundary
                  ((realDec_S31 B base level two_le slices htimes hball j C).component i).Carrier = ∅ ∧
                DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow
                  (cutMetric_S25 ((slices j).componentMetric C)
                    (realDec_S31 B base level two_le slices htimes hball j C) i) 0))) :
    Nonempty (LateCutFamily F K slices) := by
  classical
  have hfirst : ∀ j, ⌈B.start⌉₊ ≤ j → B.start ≤ (slices j).time :=
    fun j hj => ceil_le_time_S31 B slices htimes j hj
  have hex : ∀ j, ∃ port : ⌈B.start⌉₊ ≤ j →
      (Σ C : ConnectedComponents (slices j).stage.Carrier,
        Fin (realDec_S31 B base level two_le slices htimes hball j C).boundary.count) ≃
          Σ i : Fin B.toCores.count, Fin (trunc_S24 B base level two_le j i).count,
      ∀ (hj : ⌈B.start⌉₊ ≤ j) C
        (b : Fin (realDec_S31 B base level two_le slices htimes hball j C).boundary.count) (x : Torus),
        sliceCast_CX4 (slices j)
          (B.toCores.map (port hj ⟨C, b⟩).1 (slices j).time (hfirst j hj)
            ((trunc_S24 B base level two_le j (port hj ⟨C, b⟩).1).cuspMap
              (port hj ⟨C, b⟩).2 (x, halfZero))) =
          ((realDec_S31 B base level two_le slices htimes hball j C).reconstructionAtlas.torusInPrime
            (realDec_S31 B base level two_le slices htimes hball j C).reconstruction b x).val := by
    intro j
    by_cases hj : ⌈B.start⌉₊ ≤ j
    · obtain ⟨port, hport⟩ := sliceDecompReal_S31
        (TruncatedCutData_IF4.ofBuffered_S19 B (hfirst j hj) base (level j) (two_le j) (hball j hj))
        (hfirst j hj) (slices j).stage (postStage_eq_sliceStage_CX4 (slices j))
        (realDec_S31 B base level two_le slices htimes hball j)
        (realDec_eq_S31 B base level two_le slices htimes hball j hj)
      exact ⟨fun _ => port, fun _ C b x => hport C b x⟩
    · exact ⟨fun h => absurd h hj, fun h => absurd h hj⟩
  choose port hport using hex
  refine ⟨{
    cores := B.toCores
    decomposition := realDec_S31 B base level two_le slices htimes hball
    metric := fun j C i => cutMetric_S25 ((slices j).componentMetric C)
      (realDec_S31 B base level two_le slices htimes hball j C) i
    induced := fun j C i => isInducedCutMetric_cutMetric_S25 ((slices j).componentMetric C)
      (realDec_S31 B base level two_le slices htimes hball j C) i
    thin := fun j C i => ∃ hj : ⌈B.start⌉₊ ≤ j, thin j C i ∧
      (∀ c : Fin B.count,
        Disjoint
          ((fun x => (((realDec_S31 B base level two_le slices htimes hball j C).reconstruction.val
              ((realDec_S31 B base level two_le slices htimes hball j C).boundary.quotientMap x)).val :
                (slices j).stage.Carrier)) ''
            ((realDec_S31 B base level two_le slices htimes hball j C).carrier.pieceInterior
              ((realDec_S31 B base level two_le slices htimes hball j C).components.piece i) :
                Set _))
          ((fun x => sliceCast_CX4 (slices j)
              (B.toCores.map c (slices j).time (ceil_le_time_S31 B slices htimes j hj)
                ((trunc_S24 B base level two_le j c).inclusion x))) ''
            ((trunc_S24 B base level two_le j c).core.interior : Set _)))
    first := ⌈B.start⌉₊
    time_late := hfirst
    truncation := fun j i => trunc_S24 B base level two_le j i
    port := port
    core_in_ball := hcore
    seam_image := ?_
    finite_scales := fun j C i hi => hfin j hi.1 C i hi.2.1
    alternatives := ?_ }⟩
  · exact seamImageFamily_of_pointwise_CX4 slices B.toCores
      (realDec_S31 B base level two_le slices htimes hball) ⌈B.start⌉₊ hfirst
      (fun j i => trunc_S24 B base level two_le j i) port (fun _ _ _ _ => Equiv.refl Torus)
      (fun j hj C b x => hport j hj C b x)
  · intro w hw hwc
    obtain ⟨N0, hN0⟩ := halt w hw hwc
    refine ⟨max N0 ⌈B.start⌉₊, fun j hj C => ?_⟩
    have hj0 : N0 ≤ j := (le_max_left _ _).trans hj
    have hj1 : ⌈B.start⌉₊ ≤ j := (le_max_right _ _).trans hj
    refine ⟨fun i => Classical.choice ?_⟩
    by_cases hnc : (∀ c : Fin B.count,
        Disjoint
          ((fun x => (((realDec_S31 B base level two_le slices htimes hball j C).reconstruction.val
              ((realDec_S31 B base level two_le slices htimes hball j C).boundary.quotientMap x)).val :
                (slices j).stage.Carrier)) ''
            ((realDec_S31 B base level two_le slices htimes hball j C).carrier.pieceInterior
              ((realDec_S31 B base level two_le slices htimes hball j C).components.piece i) :
                Set _))
          ((fun x => sliceCast_CX4 (slices j)
              (B.toCores.map c (slices j).time (ceil_le_time_S31 B slices htimes j hj1)
                ((trunc_S24 B base level two_le j c).inclusion x))) ''
            ((trunc_S24 B base level two_le j c).core.interior : Set _)))
    · rcases hN0 j hj1 hj0 C i hnc with ⟨hth, hgeo⟩ | ⟨hnot, hclosed, hcurv⟩
      · exact ⟨.thin ⟨hj1, hth, hnc⟩ hgeo⟩
      · exact ⟨.nonnegative (fun h => hnot h.2.1) hclosed hcurv⟩
    · rcases realBlock_dichotomy_S31
        (TruncatedCutData_IF4.ofBuffered_S19 B (hfirst j hj1) base (level j) (two_le j) (hball j hj1))
        (hfirst j hj1) (hdom_ofBuffered_S31 B base level two_le slices htimes hball hcore j hj1)
        (postStage_eq_sliceStage_CX4 (slices j)) C
        (realDec_S31 B base level two_le slices htimes hball j C)
        (congrFun (realDec_eq_S31 B base level two_le slices htimes hball j hj1) C) i with
        h1 | ⟨c, ⟨e⟩⟩
      · exact absurd h1 hnc
      · exact hyperbolicAlternative_of_truncation_CX1 (trunc_S24 B base level two_le j c)
          (realDec_S31 B base level two_le slices htimes hball j C)
          (fun i => cutMetric_S25 ((slices j).componentMetric C)
            (realDec_S31 B base level two_le slices htimes hball j C) i)
          _ K w i (fun h => hnc h.2.2) e

end GC.LongTime.Ch12

import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainHprimZeroJN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainHprimSlimJN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGate7JN74

/-!
# Draft 74, the endpoint primitives `hprim` at `D_R` PRODUCED (exit `slimExitAt3_OCL`)

Lane S-JUNCTIONS (by S-JUNCTIONS5), G32 (suffix `_JN74`). For every endpoint `e` of the edge base of
the rows at `D_R`, with the label `F.horizontal e` of the produced face facts:

* `exists_faceEq_JN74`: the face function of any residual face containing the end disk equals
  `b ∘ q₁` on the face neighbourhood, with `b` smooth near `e` (zero face: `b_k ∘ ι`; new slim
  end: `e_en ∘ Q₂ ∘ ι`);
* **`hprim_at_JN74`**: `hprim` of `closed_rows_gate7_JN74` (G30): `hprim_of_eq_JN74` (the face
  model, the tube lemma, regularity of the face function) with `C₂ ∩ U = {b ≥ 0}` from
  `mem_cbase_iff_disk_JN74`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (hK : 5 ≤ K)
  (edge : EDP04WholeDiskExitU74 (S.stagesAtZ_OCL B hT hεr A))
  (final : FDC03ActualRemainderU74 (S.stagesAtZ_OCL B hT hεr A))

/-- **The face equation of any residual face containing the end disk.** -/
theorem exists_faceEq_JN74 (e : (S.rows3_JN74 B hT hεr A hK edge final).edge.EdgeEnd)
    (Fl : (S.rows3_JN74 B hT hεr A hK edge final).slimPieces.ResidualFace)
    (hdisk : (S.rows3_JN74 B hT hεr A hK edge final).edge.disk e.1 ⊆
      (S.rows3_JN74 B hT hεr A hK edge final).slimPieces.residualSet Fl) :
    let _ := A.edgeChartedSpace1
    ∃ (b : (S.rows3_JN74 B hT hεr A hK edge final).edge.Base → ℝ)
      (U₀ : TopologicalSpace.Opens (S.rows3_JN74 B hT hεr A hK edge final).edge.Base),
      e.1 ∈ U₀ ∧ ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U₀ ∧
      ∀ x (hx : x ∈ (S.rows3_JN74 B hT hεr A hK edge final).edge.source),
        x ∈ ((S.rows3_JN74 B hT hεr A hK edge final).slimPieces.residualNear Fl :
          Set W.Carrier) →
        (S.rows3_JN74 B hT hεr A hK edge final).slimPieces.residualFn Fl x =
          b ((S.rows3_JN74 B hT hεr A hK edge final).edge.proj ⟨x, hx⟩) := by
  intro _
  rcases Fl with ⟨F' | F', hF'⟩ | en
  · rcases F' with ⟨i, Fm⟩
    exact S.exists_zeroEq_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr)
      (S.rows3_JN74 B hT hεr A hK edge final) e i Fm hdisk
  · obtain ⟨b, -⟩ := F'
    exact (IsEmpty.false b).elim
  · obtain ⟨Ne, ee, z, hzc, hNo, hee, hz, -, heq⟩ :=
      S.slim_label_data_JN74 B hT hεr A hK edge final en e hdisk
    obtain ⟨U₀, heU, hsm⟩ := S.slim_smooth_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr)
      (S.rows3_JN74 B hT hεr A hK edge final).edgeFacts hNo hee e.1 z hzc hz
    refine ⟨fun c => ee (S.stageQ2_JN74 (S.edgeVal_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr)
      (S.rows3_JN74 B hT hεr A hK edge final).edgeFacts c)), U₀, heU, hsm, fun x hx hn => ?_⟩
    exact (heq x hn).trans (S.slim_eq_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr)
      (S.rows3_JN74 B hT hεr A hK edge final).edgeFacts ee x hx)

/-- **`hprim` at `D_R`, produced**: for the face facts `facesAt3_JN74` and every endpoint `e` of
the edge base of the rows `rows3At_JN74`, the EDP05 primitives (the hypothesis `hprim` of
`closed_rows_gate7_JN74`). -/
theorem hprim_at_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    ∀ e : (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).edge.EdgeEnd,
      ∃ (b : (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).edge.Base → ℝ)
        (U : TopologicalSpace.Opens (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).edge.Base),
        e.1 ∈ U ∧ ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U ∧ mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0 ∧
        (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).edge.cbase ∩ U =
          {c | c ∈ U ∧ 0 ≤ b c} ∧
        ∃ N' : Set W.Carrier, IsOpen N' ∧
          (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).edge.rim e.1 ⊆ N' ∧ ∀ x ∈ N',
          ∃ hx : x ∈ (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).edge.source,
            (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).slimPieces.residualFn
              ((S.facesAt3_JN74 B hT hεr A hK hNb hcw Htail).facts.horizontal e) x =
              b ((S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).edge.proj ⟨x, hx⟩) := by
  intro e
  have hdisk := (S.facesAt3_JN74 B hT hεr A hK hNb hcw Htail).facts.horizontal_disk e
  obtain ⟨b, U₀, heU, hb, hEq⟩ := S.exists_faceEq_JN74 B hT hεr A hK
    (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
    (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail
      (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw)) e
    ((S.facesAt3_JN74 B hT hεr A hK hNb hcw Htail).facts.horizontal e) hdisk
  obtain ⟨U, heU', hb', hreg, hCU, N', hN'o, hrim, hN'eq⟩ :=
    StageCutRows74.hprim_of_eq_JN74 (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail)
      (S.facesAt3_JN74 B hT hεr A hK hNb hcw Htail).facts
      (S.zeroFace_slim_relInt_at_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr))
      (fun c => mem_cbase_iff_disk_JN74 (S := S) (B := B) (hT := hT) (hεr := hεr) (A := A)
        (zero := S.zsp02SmoothExit74 hεr) hNb hcw (c := c))
      e b U₀ heU hb hEq
  exact ⟨b, U, heU', hb', hreg, hCU, N', hN'o, hrim, hN'eq⟩

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse

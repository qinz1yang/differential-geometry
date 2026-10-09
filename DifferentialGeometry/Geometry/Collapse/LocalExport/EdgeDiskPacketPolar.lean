import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeDiskPacket
import DifferentialGeometry.Topology.Manifold.DiskPolarRemodel
import DifferentialGeometry.Topology.Manifold.RegularLevel.RegularSublevelBoundaryRegular

/-!
# R1 item (4): the raw-`H` polar edge disk packet

Review 44 (rim-product clause for L1), item 3(b) R1, lane LFR28-ROW3. The packet structure
`EdgeDiskPacket` is frozen; the polar clause is added as theorems about packets.

* `EdgeDiskPacket.exists_polar`: every packet `P` has a re-modelled packet `P'` with the SAME edge
  chart and slab (all fields but `diskModel` are those of `P`) whose disk model is polar for the raw
  height `H = edgeRowHeight Δ F ρ` near the rim: `H (D z) = 4Δ + κ (‖z‖ - 1)` for `‖z‖ > 1 - δ`,
  `D = P.diskModel` on the rim circle and on `‖z‖ ≤ 1 - η` (polar re-modelling
  `exists_diskDiffeomorph_polar_of_boundaryDefining` with `T = -(4Δ - H)`, regular on the rim by
  `regularSublevel_mfderiv_ne_zero`).
* `EdgeDiskPacket.height_polar_of_trivial` (the GH clause): any trivialization `Θ'` of the packet's
  `trivial` field preserves `H` on `{4Δ - H < r'}`, so near the rim
  `H (Θ' (D z, t)) = 4Δ + κ (‖z‖ - 1)` while `η_p (Θ' (D z, t)) = t` for every `t ∈ (a₀, b₀)`:
  the handle side of the rim product in packet form (the flow of `trivial` is defined on an open set
  on BOTH sides of `H = 4Δ`, and the time interval `(a₀, b₀)` is arbitrary inside `(-4Δ, 4Δ)`, which
  gives the time margin).
* `exists_edgeDiskPacket_polar_of_exists`: transfer to any producer of the form
  `∃ P, P.toEdgeChart = c` (`exists_edgeDiskPacket_threshold`,
  `exists_edgeDiskPacket_comparison_threshold`, `exists_edgeDiskPackets_of_strong_edge_family`);
  `exists_edgeDiskPacket_polar_threshold` is the threshold form.
-/

set_option autoImplicit false
noncomputable section
open Bundle Set Function Filter Metric Manifold WithLp
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open DifferentialGeometry.Manifold DifferentialGeometry.Manifold.RegularLevel
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

local instance nezero_finrank_euclidean_three_packetpolar_LFR28ROW3 :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

section Packet

variable {M : Type*} [mM : MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M} {hEnorm : IsMetricNorm g}
  {Δ σ μ b γ β : ℝ} {A : Set M} {ρ F : M → ℝ}

/-- **R1 item (4): the raw-`H` polar packet.** Every edge disk packet can be re-modelled (same
edge chart, same slab, all other fields unchanged) so that near the rim of the fibre the height is
radial in the disk model: `H (D z) = 4Δ + κ (‖z‖ - 1)` for `‖z‖ > 1 - δ`; the new disk model agrees
with the old one on the rim circle and on `‖z‖ ≤ 1 - η`. -/
theorem EdgeDiskPacket.exists_polar (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F)
    {κ η : ℝ} (hκ : 0 < κ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ P' : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F,
      P'.toEdgeChart = P.toEdgeChart ∧ P'.slabOpen = P.slabOpen ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < η ∧
        (∀ z : ClosedCell 2, 1 - δ < ‖(z : E2)‖ →
          edgeRowHeight Δ F ρ ((P'.diskModel z).1 : M) = 4 * Δ + κ * (‖(z : E2)‖ - 1)) ∧
        (∀ z : ClosedCell 2, ‖(z : E2)‖ = 1 →
          ((P'.diskModel z).1 : M) = ((P.diskModel z).1 : M)) ∧
        (∀ z : ClosedCell 2, ‖(z : E2)‖ ≤ 1 - η →
          ((P'.diskModel z).1 : M) = ((P.diskModel z).1 : M)) := by
  let _ := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
  let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo P.contMDiff_coord_slab
    P.contMDiff_height_slab P.regular_fibre P.regular_boundary
  have hbd : ∀ y : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y},
      (𝓡∂ (1 + 1)).IsBoundaryPoint y → 4 * Δ - edgeRowHeight Δ F ρ y = 0 := fun y hy => by
    rw [P.boundary_level.1 y hy, sub_self]
  have hT : ContMDiff (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ) ∞
      (fun y : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} =>
        -(4 * Δ - edgeRowHeight Δ F ρ y)) :=
    (P.contMDiff_height_slab.comp (regularSublevel_contMDiff_val finrank_real_prod_euclideanTwo
      P.contMDiff_coord_slab P.contMDiff_height_slab P.regular_fibre P.regular_boundary)).neg
  have hreg : ∀ y : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y},
      (𝓡∂ (1 + 1)).IsBoundaryPoint y →
      mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ)
        (fun y : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} =>
          -(4 * Δ - edgeRowHeight Δ F ρ y)) y ≠ 0 := by
    intro y hy h0
    have hne := regularSublevel_mfderiv_ne_zero finrank_real_prod_euclideanTwo
      P.contMDiff_coord_slab P.contMDiff_height_slab P.regular_fibre P.regular_boundary y (hbd y hy)
    apply hne
    have h1 := mfderiv_neg (I := 𝓡∂ (1 + 1)) (x := y)
      (f := fun y : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} =>
        4 * Δ - edgeRowHeight Δ F ρ y)
    ext v
    have h2 : (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ) (-fun y : {y : P.slabOpen // P.coord y = 0 ∧
        0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} => 4 * Δ - edgeRowHeight Δ F ρ y) y) v = 0 := by
      change (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ)
        (fun y : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} =>
          -(4 * Δ - edgeRowHeight Δ F ρ y)) y) v = 0
      rw [h0]
      rfl
    rw [h1] at h2
    have h3 : -((mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ)
        (fun y : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} =>
          4 * Δ - edgeRowHeight Δ F ρ y) y) v) = 0 := h2
    change (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ)
        (fun y : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} =>
          4 * Δ - edgeRowHeight Δ F ρ y) y) v = 0
    exact neg_eq_zero.mp h3
  obtain ⟨δ, hδ0, hδη, D, hD, hDS, hDη⟩ := Topology.Manifold.exists_diskDiffeomorph_polar_of_boundaryDefining
    (m := 1) P.diskModel isOpen_univ (fun _ _ => mem_univ _) hT.contMDiffOn (c := 0)
    (fun y hy => by rw [hbd y hy, neg_zero]) (fun y _ => by linarith [y.2.2]) hreg hκ hη0 hη1
  refine ⟨{ P with diskModel := D }, rfl, rfl, δ, hδ0, hδη, ?_, ?_, ?_⟩
  · intro z hz
    have h := (hD z hz).2
    change -(4 * Δ - edgeRowHeight Δ F ρ ((D z).1 : M)) = 0 + κ * (‖(z : E2)‖ - 1) at h
    change edgeRowHeight Δ F ρ ((D z).1 : M) = 4 * Δ + κ * (‖(z : E2)‖ - 1)
    linarith
  · intro z hz
    change ((D z).1 : M) = ((P.diskModel z).1 : M)
    rw [hDS z hz]
  · intro z hz
    change ((D z).1 : M) = ((P.diskModel z).1 : M)
    rw [hDη z hz]

/-- **The GH clause with the polar clause.** If the disk model of a packet is polar near the rim,
every map `Θ'` preserving `H` on `{4Δ - H < r'}` (as the trivializations of the packet's `trivial`
field do) is polar on the rim collar: `H (Θ' (D z, q)) = 4Δ + κ (‖z‖ - 1)` for `‖z‖ > 1 - δ'`. -/
theorem EdgeDiskPacket.height_polar_of_trivial (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F)
    {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ)
    (hpol : ∀ z : ClosedCell 2, 1 - δ < ‖(z : E2)‖ →
      edgeRowHeight Δ F ρ ((P.diskModel z).1 : M) = 4 * Δ + κ * (‖(z : E2)‖ - 1))
    {Q : Type*}
    (Θ' : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} × Q → P.slabOpen)
    {r' : ℝ} (hr' : 0 < r')
    (hpres : ∀ p : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} × Q,
      4 * Δ - edgeRowHeight Δ F ρ p.1 < r' →
        edgeRowHeight Δ F ρ (Θ' p) = edgeRowHeight Δ F ρ p.1) :
    ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧ ∀ (z : ClosedCell 2) (q : Q), 1 - δ' < ‖(z : E2)‖ →
      edgeRowHeight Δ F ρ ((Θ' (P.diskModel z, q) : P.slabOpen) : M) =
        4 * Δ + κ * (‖(z : E2)‖ - 1) := by
  refine ⟨min δ (r' / (2 * κ)), lt_min hδ (by positivity), min_le_left _ _, ?_⟩
  intro z q hz
  have hzδ : 1 - δ < ‖(z : E2)‖ := lt_of_le_of_lt (by linarith [min_le_left δ (r' / (2 * κ))]) hz
  have hzr : 1 - r' / (2 * κ) < ‖(z : E2)‖ :=
    lt_of_le_of_lt (by linarith [min_le_right δ (r' / (2 * κ))]) hz
  have hz1 : ‖(z : E2)‖ ≤ 1 := z.2
  have hH := hpol z hzδ
  have hκr : κ * (1 - ‖(z : E2)‖) < r' := by
    have h1 : 1 - ‖(z : E2)‖ < r' / (2 * κ) := by linarith
    have h2 : κ * (1 - ‖(z : E2)‖) < κ * (r' / (2 * κ)) := mul_lt_mul_of_pos_left h1 hκ
    have h3 : κ * (r' / (2 * κ)) = r' / 2 := by field_simp
    linarith
  rw [hpres (P.diskModel z, q) (by
    change 4 * Δ - edgeRowHeight Δ F ρ ((P.diskModel z).1 : M) < r'
    rw [hH]
    linarith)]
  exact hH

/-- **Transfer to the producers.** Whenever an edge chart extends to a packet, it extends to one
whose disk model is polar for the raw height near the rim. -/
theorem exists_edgeDiskPacket_polar_of_exists {c : EdgeChart g hEnorm Δ σ μ b γ β A ρ F}
    (h : ∃ P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F, P.toEdgeChart = c)
    {κ η : ℝ} (hκ : 0 < κ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F, P.toEdgeChart = c ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < η ∧ ∀ z : ClosedCell 2, 1 - δ < ‖(z : E2)‖ →
        edgeRowHeight Δ F ρ ((P.diskModel z).1 : M) = 4 * Δ + κ * (‖(z : E2)‖ - 1) := by
  obtain ⟨P, hP⟩ := h
  obtain ⟨P', hP', -, δ, hδ0, hδη, hpol, -, -⟩ := P.exists_polar hκ hη0 hη1
  exact ⟨P', hP'.trans hP, δ, hδ0, hδη, hpol⟩

end Packet

/-- **LC84's producer, threshold form, with the polar clause (R1 item (4)).** For `b` below the
threshold of `exists_edgeDiskPacket_threshold`, every edge chart with LFR28's data extends to an
edge disk packet whose disk model is polar for the raw height near the rim. -/
theorem exists_edgeDiskPacket_polar_threshold {Δ σ ε μ τ : ℝ} {Λ : ℝ≥0} (hΔ : 1 ≤ Δ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 10 ^ 10) (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 10 ^ 8) (hμ : 0 < μ)
    (hμ1 : μ ≤ 1 / 10 ^ 8) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 10 ^ 30)
    (hΛ : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (K : ℕ) (hK : 5 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) {κ η : ℝ} (hκ : 0 < κ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b < b₀ →
      ∀ (M : Type) [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
        [SigmaCompactSpace M] [T2Space (TangentBundle 𝓘(ℝ, E3) M)] [CompleteSpace M]
        [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        [IsRiemannianManifold 𝓘(ℝ, E3) M]
        [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (hEnorm : IsMetricNorm g),
        ManifoldOrientation (𝓡 3) M 3 → ∀ p : M,
        ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) M g (ball p r) →
        (∀ R, 0 < R → R < b⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k g y ≤ A R) →
        (∀ y ∈ ball p b⁻¹, SectionalBoundedBelowAt g y (-b ^ 2)) →
        ∀ (γ β : ℝ) (E : Set M) (ρ F : M → ℝ) (c : EdgeChart g hEnorm Δ σ μ b γ β E ρ F)
          (OF : Set M), c.center = p → c.Qn p = 0 →
        (∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
          |dist (c.Qn x) (c.Qn y) - dist x y| ≤ τ * Δ) →
        (∀ x ∈ ball p (200 * Δ), 0 ≤ (c.Qn x).snd) →
        (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
          ∃ x ∈ ball p (200 * Δ), dist (c.Qn x) z ≤ τ * Δ) →
        IsClosed E →
        (∀ a ∈ E ∩ ball p (190 * Δ), (c.Qn a).snd ≤ τ * Δ) →
        (∀ t : ℝ, |t| ≤ 100 * Δ →
          ∃ a ∈ E ∩ ball p (190 * Δ), dist (c.Qn a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) →
        (∀ x, |F x - infDist x E| < μ * Δ) →
        IsOpen OF →
        closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y E ∧ infDist y E ≤ 21 / 2 * Δ} ⊆ OF →
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ F OF →
        (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y E ∧ infDist y E ≤ 21 / 2 * Δ},
          ∀ u ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo g E y,
            Real.sqrt (g.inner y (gradFun g F y + u) (gradFun g F y + u)) < ε) →
        (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y E ∧ infDist y E ≤ 21 / 2 * Δ},
          Real.sqrt (g.inner y (gradFun g (fun z => F z / ρ z) y - gradFun g F y)
            (gradFun g (fun z => F z / ρ z) y - gradFun g F y)) ≤ 100 * Δ * Λ) →
        (∀ x ∈ ball p (20 * Δ), infDist x E < 41 / 4 * Δ →
          ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (edgeRowHeight Δ F ρ) x) →
        LipschitzWith Λ ρ → ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ρ (ball p (100 * Δ)) →
        ∃ P : EdgeDiskPacket g hEnorm Δ σ μ b γ β E ρ F, P.toEdgeChart = c ∧
          ∃ δ : ℝ, 0 < δ ∧ δ < η ∧ ∀ z : ClosedCell 2, 1 - δ < ‖(z : E2)‖ →
            edgeRowHeight Δ F ρ ((P.diskModel z).1 : M) = 4 * Δ + κ * (‖(z : E2)‖ - 1) := by
  obtain ⟨b₀, hb₀, hmain⟩ := exists_edgeDiskPacket_threshold hΔ hσ hσ1 hε hε1 hμ hμ1 hτ hτ1 hΛ K
    hK hr hv A
  refine ⟨b₀, hb₀, fun b hb hbb₀ M _ _ _ _ _ _ _ _ _ _ g hEnorm o p hvol hcurv hsec γ β E ρ F c OF
    hcp hQp hQdist hheight hQcover hEc hborder hbordercover hF hOF hCO hFs hFgrad hquot hHs hρL
    hρs => ?_⟩
  exact exists_edgeDiskPacket_polar_of_exists (hmain b hb hbb₀ M g hEnorm o p hvol hcurv hsec γ β E
    ρ F c OF hcp hQp hQdist hheight hQcover hEc hborder hbordercover hF hOF hCO hFs hFgrad hquot hHs
    hρL hρs) hκ hη0 hη1

end DifferentialGeometry.Geometry.Collapse

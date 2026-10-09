import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeChart
import DifferentialGeometry.Geometry.Collapse.EdgeRowThresholdHpreserving
import DifferentialGeometry.Geometry.Collapse.EdgeSourceCutoff

/-!
# LC84: the edge disk packet (an edge chart with LFR28.1's proper disk bundle)

Blueprint LC84 (`def:collapse-edge-packet`, master207A:30874), item 4–5 and the local output: the
proper disk bundle `η_p : {|η_p| < 4Δ, η_{E'} ≤ 4Δ} → (-4Δ, 4Δ)`, fibre `D²`, boundary exactly the
level `η_{E'} = 4Δ`. `EdgeDiskPacket extends EdgeChart` (F7-LFR20b's `EdgeChart`, LC84 items 1–3,
normalized scale) with, for the height `H = edgeRowHeight Δ F ρ = Δψ((F/ρ)/Δ)`:

* `slabOpen`: an open `O ⊆ B(center, 20Δ)` containing the whole closed slab
  `{y ∈ B(center, 100Δ) : |η_p y| ≤ 4Δ, H y ≤ 4Δ}`; on `O` (re-charted on `ModelProd ℝ E2` along
  `E3 ≃ ℝ × E2`) `η_p` and `4Δ - H` are smooth and regular on the fibre (rank two of `(η_p, H)` on
  its boundary), which defines the regular-sublevel structure of the fibre `{η_p = 0, H ≤ 4Δ}`;
* `diskModel`: a diffeomorphism `ClosedCell 2 ≃ₘ` fibre (DATA, so that it can be re-modelled), and
  `boundary_level`: the boundary of the fibre is exactly `{H = 4Δ}` (both inclusions);
* `trivial`: over every `(a₀, b₀) ∋ 0` inside `(-4Δ, 4Δ)` a smooth injective trivialization `Θ'`
  with `η_p ∘ Θ' = pr₂` (so the end disks are the slices), a smooth retraction, and the rim
  product clause R2 (lane ASM-L1b): `H ∘ Θ' = H` near the rim, `Θ'` the restriction of a smooth
  flow `D` translating `η_p` on `{η_p = 0, H ≤ 4Δ + r'}` and preserving `H` on `{|H - 4Δ| < r'}`;
* `tsupport_cutoff_subset` (LC87's domain margin): the edge cutoff of the chart is supported in
  `B̄(center, 12.9Δ)`, well inside the coordinate domain `⊇ B̄(center, 100Δ)`.

Producer: `exists_edgeDiskPacket_threshold` (threshold form, LFR28 row with the `H`-preserving
trivialization + (LFR28.6) with `9` for the margin): for `b` below the threshold, every edge
chart at an oriented manifold point with the noncollapse, curvature and LFR27 data extends to a
packet.
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

local instance nezero_finrank_euclidean_three_packet_LFR28ROW2 : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

section Packet

variable {M : Type*} [mM : MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]

/-- **LC84 edge disk packet.** An edge chart with LFR28.1's proper disk bundle, the rim product
clause R2 and LC87's domain margin. See the module docstring. -/
structure EdgeDiskPacket (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (hEnorm : IsMetricNorm g)
    (Δ σ μ b γ β : ℝ) (A : Set M) (ρ F : M → ℝ)
    extends EdgeChart g hEnorm Δ σ μ b γ β A ρ F where
  /-- The open set carrying the slab. -/
  slabOpen : TopologicalSpace.Opens M
  slabOpen_subset : (slabOpen : Set M) ⊆ ball center (20 * Δ)
  /-- The whole closed slab of `B(center, 100Δ)` lies in `slabOpen`. -/
  slab_subset : ∀ y ∈ ball center (100 * Δ), |coord y| ≤ 4 * Δ →
    edgeRowHeight Δ F ρ y ≤ 4 * Δ → y ∈ slabOpen
  contMDiff_coord_slab :
    letI := chartedSpaceTransHomeomorph (M := slabOpen) euclideanThreeProdHomeomorph
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (fun y : slabOpen => coord y)
  contMDiff_height_slab :
    letI := chartedSpaceTransHomeomorph (M := slabOpen) euclideanThreeProdHomeomorph
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (fun y : slabOpen => 4 * Δ - edgeRowHeight Δ F ρ y)
  regular_fibre :
    letI := chartedSpaceTransHomeomorph (M := slabOpen) euclideanThreeProdHomeomorph
    ∀ y : slabOpen, coord y = 0 → 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y →
      Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) (fun y : slabOpen => coord y) y)
  regular_boundary :
    letI := chartedSpaceTransHomeomorph (M := slabOpen) euclideanThreeProdHomeomorph
    ∀ y : slabOpen, coord y = 0 → 4 * Δ - edgeRowHeight Δ F ρ y = 0 →
      Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
        (fun y : slabOpen => ((coord y, 4 * Δ - edgeRowHeight Δ F ρ y) : ℝ × ℝ)) y)
  /-- The disk model of the fibre `{coord = 0, H ≤ 4Δ}` (regular-sublevel structure). -/
  diskModel :
    letI := chartedSpaceTransHomeomorph (M := slabOpen) euclideanThreeProdHomeomorph
    letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ slabOpen := edgeSource_isManifold
    letI := regularSublevelChartedSpace finrank_real_prod_euclideanTwo contMDiff_coord_slab
      contMDiff_height_slab regular_fibre regular_boundary
    ClosedCell 2 ≃ₘ⟮𝓡∂ (1 + 1), 𝓡∂ (1 + 1)⟯
      {y : slabOpen // coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y}
  /-- The boundary of the fibre is exactly `{H = 4Δ}` (both inclusions). -/
  boundary_level :
    letI := chartedSpaceTransHomeomorph (M := slabOpen) euclideanThreeProdHomeomorph
    letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ slabOpen := edgeSource_isManifold
    letI := regularSublevelChartedSpace finrank_real_prod_euclideanTwo contMDiff_coord_slab
      contMDiff_height_slab regular_fibre regular_boundary
    (∀ y : {y : slabOpen // coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y},
      (𝓡∂ (1 + 1)).IsBoundaryPoint y → edgeRowHeight Δ F ρ y = 4 * Δ) ∧
    ∀ y : {y : slabOpen // coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y},
      edgeRowHeight Δ F ρ y = 4 * Δ → (𝓡∂ (1 + 1)).IsBoundaryPoint y
  /-- Triviality over every `(a₀, b₀) ∋ 0` in `(-4Δ, 4Δ)`, with the rim product clause R2. -/
  trivial :
    letI := chartedSpaceTransHomeomorph (M := slabOpen) euclideanThreeProdHomeomorph
    letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ slabOpen := edgeSource_isManifold
    letI := regularSublevelChartedSpace finrank_real_prod_euclideanTwo contMDiff_coord_slab
      contMDiff_height_slab regular_fibre regular_boundary
    ∀ (a₀ b₀ : ℝ), -(4 * Δ) < a₀ → ∀ (h0 : (0 : ℝ) ∈ Ioo a₀ b₀), b₀ < 4 * Δ →
    let Q₀ : TopologicalSpace.Opens ℝ := ⟨Ioo a₀ b₀, isOpen_Ioo⟩
      ∃ Θ' : {y : slabOpen // coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} × Q₀ → slabOpen,
        ContMDiff ((𝓡∂ (1 + 1)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ Θ' ∧
        (∀ p, coord (Θ' p) = p.2 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ (Θ' p)) ∧
        (∀ x, Θ' (x, ⟨0, h0⟩) = x) ∧ Injective Θ' ∧
        (∃ r' : ℝ, 0 < r' ∧ (∀ p, 4 * Δ - edgeRowHeight Δ F ρ p.1 < r' → edgeRowHeight Δ F ρ (Θ' p) = edgeRowHeight Δ F ρ p.1) ∧
          ∃ (U : Set slabOpen) (hU : IsOpen U),
          ∃ D : ℝ → (⟨U, hU⟩ : TopologicalSpace.Opens slabOpen) ≃ₘ⟮𝓘(ℝ, ℝ).prod (𝓡 2), 𝓘(ℝ, ℝ).prod (𝓡 2)⟯
              (⟨U, hU⟩ : TopologicalSpace.Opens slabOpen),
            ContMDiff (𝓘(ℝ).prod (𝓘(ℝ, ℝ).prod (𝓡 2))) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
              (fun q : ℝ × (⟨U, hU⟩ : TopologicalSpace.Opens slabOpen) => D q.1 q.2) ∧
            D 0 = Diffeomorph.refl _ _ ∞ ∧ (∀ s t, (D s).trans (D t) = D (s + t)) ∧
            (∀ p, ∃ hp : (p.1 : slabOpen) ∈ U, Θ' p = (D (p.2 : ℝ) ⟨p.1, hp⟩ : slabOpen)) ∧
            (∀ z : (⟨U, hU⟩ : TopologicalSpace.Opens slabOpen), coord (z : slabOpen) = 0 →
              -r' ≤ 4 * Δ - edgeRowHeight Δ F ρ (z : slabOpen) → ∀ t ∈ Ioo a₀ b₀, coord (D t z : slabOpen) = t) ∧
            ∀ (z : (⟨U, hU⟩ : TopologicalSpace.Opens slabOpen)) (t : ℝ), |4 * Δ - edgeRowHeight Δ F ρ (z : slabOpen)| < r' →
              edgeRowHeight Δ F ρ (D t z : slabOpen) = edgeRowHeight Δ F ρ (z : slabOpen)) ∧
        ∃ O' : Set slabOpen, IsOpen O' ∧
          (∀ y : slabOpen, coord y ∈ Ioo a₀ b₀ → 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y → y ∈ O') ∧
          ∃ R : slabOpen → slabOpen, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ R O' ∧
            ∀ (y : slabOpen) (hy : coord y ∈ Ioo a₀ b₀),
              0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y →
              ∃ hR : coord (R y) = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ (R y),
                Θ' (⟨R y, hR⟩, ⟨coord y, hy⟩) = y
  /-- LC87's domain margin: the edge cutoff is supported in `B̄(center, 12.9Δ)`. -/
  tsupport_cutoff_subset : tsupport ((Subtype.val : ball center (100 * Δ) → M).extend
    (fun x => edgeCoordinateProfile (coord x.val / Δ) *
      edgeHeightProfile (F x.val / (Δ * ρ x.val))) 0) ⊆ closedBall center (129 / 10 * Δ)

end Packet

/-- **LC84's producer, threshold form.** For `b` below the threshold, every edge chart at an
oriented manifold point with LFR28's data extends to an edge disk packet. -/
theorem exists_edgeDiskPacket_threshold {Δ σ ε μ τ : ℝ} {Λ : ℝ≥0} (hΔ : 1 ≤ Δ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 10 ^ 10) (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 10 ^ 8) (hμ : 0 < μ)
    (hμ1 : μ ≤ 1 / 10 ^ 8) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 10 ^ 30)
    (hΛ : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (K : ℕ) (hK : 5 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) :
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
        ∃ P : EdgeDiskPacket g hEnorm Δ σ μ b γ β E ρ F, P.toEdgeChart = c := by
  obtain ⟨b₀, hb₀, hmain⟩ := edgeSourceSlab_disk_bundle_threshold_Hpreserving hΔ hσ hσ1 hε hε1 hμ
    hμ1 hτ hτ1 hΛ K hK hr hv A
  refine ⟨b₀, hb₀, fun b hb hbb₀ M _ _ _ _ _ _ _ _ _ _ g hEnorm o p hvol hcurv hsec γ β E ρ F c OF
    hcp hQp hQdist hheight hQcover hEc hborder hbordercover hF hOF hCO hFs hFgrad hquot hHs hρL
    hρs => ?_⟩
  have hΔ0 : 0 < Δ := by linarith
  subst hcp
  let _ := c.instY
  obtain ⟨O, hOsub, hslab, hrow⟩ := hmain b hb hbb₀ M g hEnorm o c.center hvol hcurv hsec c.Y c.q
    c.split c.Qn E F c.coord ρ OF c.domain c.Qn_fst hQp hQdist hheight hQcover hEc c.center_mem
    hborder hbordercover hF hOF hCO hFs hFgrad hquot hHs hρL c.rho_center hρs c.isOpen_domain
    c.closedBall_subset_domain c.contMDiffOn_coord c.lipschitz c.value c.test
  have hr0 := hrow (-(2 * Δ)) (2 * Δ) (by linarith) ⟨by linarith, by linarith⟩ (by linarith)
  obtain ⟨hΨ, hB, hreg, hregb, hrest⟩ := hr0
  let _ := chartedSpaceTransHomeomorph (M := O) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ O := edgeSource_isManifold
  let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo hΨ hB hreg hregb
  obtain ⟨hdisk, -, -, -, hbd⟩ := hrest
  -- the scale on `B(p, 100Δ)`
  have hρb : ∀ x ∈ ball c.center (100 * Δ), 0 < ρ x ∧ ρ x ≤ 1 + 1 / 10 ^ 6 := by
    intro x hx
    have h1 := hρL.dist_le_mul x c.center
    rw [Real.dist_eq, c.rho_center] at h1
    have h2 : (Λ : ℝ) * dist x c.center ≤ Λ * (100 * Δ) :=
      mul_le_mul_of_nonneg_left (mem_ball.mp hx).le Λ.coe_nonneg
    have h3 := abs_le.mp h1
    constructor <;> linarith [h3.1, h3.2]
  -- LC87's margin: the edge cutoff is supported in `B̄(p, 12.9Δ)`
  have hnine : ∀ x ∈ ball c.center (100 * Δ), |c.coord x| ≤ 9 * Δ → F x / ρ x ≤ 9 * Δ →
      dist x c.center < 129 / 10 * Δ := fun x hx hfx hηx =>
    coarseBorder_source_slab_nine_subset_ball hΔ0 (by linarith) (by linarith)
      (by norm_num : (1 / 10 ^ 6 : ℝ) ≤ 1 / 100) hQp hQdist hheight c.center_mem hborder
      (fun y hy => by rw [c.Qn_fst]; exact (c.value y hy).le) (fun y _ => (hF y).le) hρb hx hfx
      hηx
  have hsupp : support ((Subtype.val : ball c.center (100 * Δ) → M).extend
      (fun x => edgeCoordinateProfile (c.coord x.val / Δ) *
        edgeHeightProfile (F x.val / (Δ * ρ x.val))) 0) ⊆ ball c.center (129 / 10 * Δ) := by
    intro y hy
    by_cases hyr : ∃ x : ball c.center (100 * Δ), (x : M) = y
    · obtain ⟨x, rfl⟩ := hyr
      rw [mem_support, Subtype.val_injective.extend_apply] at hy
      have h1 : edgeCoordinateProfile (c.coord x.val / Δ) ≠ 0 := left_ne_zero_of_mul hy
      have h2 : edgeHeightProfile (F x.val / (Δ * ρ x.val)) ≠ 0 := right_ne_zero_of_mul hy
      have hρx := hρb x.val x.2
      have hf9 : |c.coord x.val| ≤ 9 * Δ := by
        have hle : |c.coord x.val / Δ| ≤ 9 := by
          by_contra hcon
          push Not at hcon
          rcases lt_abs.mp hcon with h | h
          · exact h1 (intervalPlateauProfile_zero_right (by norm_num) h.le)
          · exact h1 (intervalPlateauProfile_zero_left (by norm_num) (by linarith))
        rw [abs_div, abs_of_pos hΔ0, div_le_iff₀ hΔ0] at hle
        exact hle
      have hF9 : F x.val / ρ x.val ≤ 9 * Δ := by
        have hle : F x.val / (Δ * ρ x.val) ≤ 9 := by
          by_contra hcon
          push Not at hcon
          exact h2 (descendingIntervalProfile_zero (by norm_num) hcon.le)
        rw [mul_comm Δ, ← div_div, div_le_iff₀ hΔ0] at hle
        exact hle
      exact mem_ball.mpr (hnine x.val x.2 hf9 hF9)
    · rw [mem_support, extend_apply' _ _ _ (by
        rintro ⟨x, hx⟩
        exact hyr ⟨x, hx⟩)] at hy
      exact absurd rfl hy
  refine ⟨{ c with
    slabOpen := O
    slabOpen_subset := hOsub
    slab_subset := hslab
    contMDiff_coord_slab := hΨ
    contMDiff_height_slab := hB
    regular_fibre := hreg
    regular_boundary := hregb
    diskModel := Classical.choice hdisk
    boundary_level := ⟨fun y => (hbd y).1, fun y => (hbd y).2⟩
    trivial := fun a₀ b₀ ha₀ h0 hb₀ => by
      obtain ⟨hΨ', hB', hreg', hregb', hrest'⟩ := hrow a₀ b₀ ha₀ h0 hb₀
      let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo hΨ' hB' hreg' hregb'
      obtain ⟨-, -, -, htriv, -⟩ := hrest'
      exact htriv
    tsupport_cutoff_subset := (closure_mono hsupp).trans closure_ball_subset_closedBall }, rfl⟩

end DifferentialGeometry.Geometry.Collapse

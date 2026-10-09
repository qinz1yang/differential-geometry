import DifferentialGeometry.Geometry.Fibration.ActualStageFirstPruning
import DifferentialGeometry.Geometry.Fibration.ActualStageFirstTest

/-!
# FC27's first-cloud test with the small-marker rule (PP)

Blueprint `master207B.tex`, FC27 (B:1658, the first cloud from TCP06) with CFS27's rule (PP)
(B:3626–3686): TCP06's planes are built from the PRUNED graphs of `tcp05_pruned_GAF5`, so that at
every preimage `q` of a core point `x` every retained marker with `ρ(c_a) < ρ(q)/5` annihilates
`plane x` (`q` lies in the chart domain of the witness centre `i`, so `ρ(q) ≤ 5ρ(i)/4` and
`ρ(c_a) < ρ(i)/4` is a deleted block).

* `tcp06_centre_pp_GAF5`, `tcp06_point_of_mem_pp_GAF5`, `tcp06_planes_pp_GAF5`: TCP06's per-centre,
  per-point and chosen planes from pruned data, with the (PP) clause.
* `fc27_first_test_pp_GAF5`: `fc27_first_test_GAF4` (stage `0`, TCP06's thresholds and hypotheses
  verbatim) with (PP) as a fourth conjunct, in the form of `gafStage_hnear_GAF4`'s `hpp`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Packets

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_GAF5t
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF5t
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF5t
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **TCP06 at one circle centre, with (PP).** As `tcp06_centre_KA8`, for a model `Φ` whose
derivative is annihilated by every retained marker with `ρ(c_a) ≤ ρ(j)/2`: the plane
`W = im DΦ(η_j p)` has in addition `W ≤ ker v_a` for every preimage `q` of `x` and every retained
marker with `ρ(c_a) < ρ(q)/5`. -/
theorem tcp06_centre_pp_GAF5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΛ200 : Λ * 200 ≤ 1 / 4) (hβ : β 2 ≤ 1 / 10000000) (hγβ : γ + β 2 ≤ 1 / 10)
    {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100) (j : P.toLocalChartFamily.circle.finite_centres.toFinset)
    (Φ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm : ContDiff ℝ ∞ Φ) (hown : ∀ a, Φ a (.inl j) = WithLp.toLp 2 (a, 1))
    (hb : ∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ tcpGraphConst)
    (hTG : ∀ x ∈ ball j.1 (200 * ρ j.1),
      ‖cgpCircleCoord P.toLocalChartFamily j.1 ((Set.Finite.mem_toFinset _).mp j.2) x‖ ≤ 8 →
      ‖(ρ j.1)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
          Φ (cgpCircleCoord P.toLocalChartFamily j.1 ((Set.Finite.mem_toFinset _).mp j.2) x)‖ <
        eg ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ j.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
            fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily j.1
              ((Set.Finite.mem_toFinset _).mp j.2) x)
              (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j.1
                ((Set.Finite.mem_toFinset _).mp j.2)) x w)‖ ≤
          eg * Real.sqrt ((ρ j.1)⁻¹ ^ 2 * g.inner x w w))
    (hprune : ∀ a : CGPMarkerIndex P.toLocalChartFamily,
      ρ (cgpMarkerCentre P.toLocalChartFamily a) ≤ ρ j.1 / 2 → ∀ u v,
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (fderiv ℝ Φ u v) = 0)
    {p : X} (hp : p ∈ ball j.1 (200 * ρ j.1))
    (hηp : ‖cgpCircleCoord P.toLocalChartFamily j.1 ((Set.Finite.mem_toFinset _).mp j.2) p‖ ≤
      7) {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpGlobalMap P.toLocalChartFamily P.zero p = x) :
    ∃ W : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      Module.finrank ℝ W = 2 ∧
      hausdorffEDist (cgpGlobalMap P.toLocalChartFamily P.zero ''
          fc04Set P.toLocalChartFamily P.zero 8 ∩
          ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / Γ))
        ((AffineSubspace.mk' x W :
            Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
          ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / Γ)) ≤
        ENNReal.ofReal (Γ * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x) ∧
      (∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
      let Pq := W.orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (cgpGlobalMap P.toLocalChartFamily P.zero) q)
      Function.Surjective Pq ∧
      (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
          (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
      ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
          W ≤ LinearMap.ker ((blockMarkerCLM
            (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (cgpMarkerTag P.toLocalChartFamily P.zero a) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  subst hpx
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hC : 0 < tcpGraphConst := lt_of_lt_of_le one_pos one_le_tcpGraphConst
  have hsm2 : ContDiff ℝ 2 Φ := hsm.of_le (by simp)
  have hpoint := tcp06_point_KA8 P hΛ hΛ200 hj j rfl Φ hsm2 hown (fun a => (hb a).2) hΓ hΓ1 hsg
    hsgΓ hC hsgC heg hegΓ (fun y hy hyη => (hTG y hy hyη).1) hp hηp
  have hrank := fun q (hq : cgpGlobalMap P.toLocalChartFamily P.zero q =
      cgpGlobalMap P.toLocalChartFamily P.zero p) =>
    tcp06_rank_point_KA8 P hβ hγβ hj j rfl Φ hsm2 hown (fun a => (hb a).1) heg1
      (fun y hy hyη => (hTG y hy hyη).2) hp hηp hq
  refine ⟨_, hpoint.1, hpoint.2, ⟨j, hrank⟩, fun q hq a ha => ?_⟩
  have hfm := tcp06_full_marker_KA8 P hj j rfl hp (le_trans hηp (by norm_num)) hq
  have hsc := scale_mem_of_dist_lt_KC P.lipschitz_scale hΛ (hρ j.1) (mem_ball.mp hfm.1) hΛ200
  have hrj := hρ j.1
  have hsa : ρ (cgpMarkerCentre P.toLocalChartFamily a) ≤ ρ j.1 / 2 := by linarith [hsc.2]
  intro w hw
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hw
  rw [LinearMap.mem_ker]
  exact hprune a hsa _ u

/-- **TCP06 at one point of the core image, with (PP)**, from pruned TCP05 data at every circle
centre (`tcp05_pruned_GAF5`'s conclusion). -/
theorem tcp06_point_of_mem_pp_GAF5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΛ200 : Λ * 200 ≤ 1 / 4) (hβ : β 2 ≤ 1 / 10000000) (hγβ : γ + β 2 ≤ 1 / 10)
    {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100)
    (hTCP : ∀ i (hi : i ∈ P.circle.centres),
      ∃ Φ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiff ℝ ∞ Φ ∧
        (∀ j : P.circle.finite_centres.toFinset, j.1 = i → ∀ a,
          Φ a (.inl j) = WithLp.toLp 2 (a, 1)) ∧
        (∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ tcpGraphConst) ∧
        (∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8 →
          ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
              Φ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < eg ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
                fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily i hi x)
                  (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) ≤ ρ i / 2 → ∀ u v,
          blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (fderiv ℝ Φ u v) = 0)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7) :
    ∃ W : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      Module.finrank ℝ W = 2 ∧
      hausdorffEDist (cgpGlobalMap P.toLocalChartFamily P.zero ''
          fc04Set P.toLocalChartFamily P.zero 8 ∩
          ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / Γ))
        ((AffineSubspace.mk' x W :
            Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
          ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / Γ)) ≤
        ENNReal.ofReal (Γ * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x) ∧
      (∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
      let Pq := W.orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (cgpGlobalMap P.toLocalChartFamily P.zero) q)
      Function.Surjective Pq ∧
      (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
          (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
      ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
          W ≤ LinearMap.ker ((blockMarkerCLM
            (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (cgpMarkerTag P.toLocalChartFamily P.zero a) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  refine Exists.elim hx (fun p hp => ?_)
  refine Exists.elim hp.1 (fun j hj' => ?_)
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  refine Exists.elim (hTCP j.1 hj) (fun Φ hΦ => ?_)
  exact tcp06_centre_pp_GAF5 P hΛ hΛ200 hβ hγβ hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ j Φ hΦ.1
    (hΦ.2.1 j rfl) hΦ.2.2.1 hΦ.2.2.2.1 hΦ.2.2.2.2 hj'.1 hj'.2 hp.2

/-- **TCP06 on the whole core image, with (PP)**: the planes of `tcp06_point_of_mem_pp_GAF5`,
chosen over `S₁`. -/
theorem tcp06_planes_pp_GAF5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΛ200 : Λ * 200 ≤ 1 / 4) (hβ : β 2 ≤ 1 / 10000000) (hγβ : γ + β 2 ≤ 1 / 10)
    {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100)
    (hTCP : ∀ i (hi : i ∈ P.circle.centres),
      ∃ Φ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiff ℝ ∞ Φ ∧
        (∀ j : P.circle.finite_centres.toFinset, j.1 = i → ∀ a,
          Φ a (.inl j) = WithLp.toLp 2 (a, 1)) ∧
        (∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ tcpGraphConst) ∧
        (∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8 →
          ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
              Φ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < eg ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
                fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily i hi x)
                  (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) ≤ ρ i / 2 → ∀ u v,
          blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (fderiv ℝ Φ u v) = 0) :
    ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
        Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        Module.finrank ℝ (plane x) = 2) ∧
      (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        hausdorffEDist (cgpGlobalMap P.toLocalChartFamily P.zero ''
            fc04Set P.toLocalChartFamily P.zero 8 ∩
            ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / Γ))
          ((AffineSubspace.mk' x (plane x) :
              Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
            ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / Γ)) ≤
          ENNReal.ofReal (Γ * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x)) ∧
      (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
        ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
        let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (cgpGlobalMap P.toLocalChartFamily P.zero) q)
        Function.Surjective Pq ∧
        (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
            (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
        (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
          1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
        ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      ∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
          plane x ≤ LinearMap.ker ((blockMarkerCLM
            (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (cgpMarkerTag P.toLocalChartFamily P.zero a) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  have hpt := fun x (hx : x ∈ cgpGlobalMap P.toLocalChartFamily P.zero ''
      fc04Set P.toLocalChartFamily P.zero 7) =>
    tcp06_point_of_mem_pp_GAF5 P hΛ hΛ200 hβ hγβ hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ hTCP hx
  choose! plane hplane using hpt
  exact ⟨plane, fun x hx => (hplane x hx).1, fun x hx => (hplane x hx).2.1,
    fun x hx => (hplane x hx).2.2.1, fun x hx => (hplane x hx).2.2.2⟩

end Packets

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_GAF5t {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF5t {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF5t {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FC27's first-cloud test with (PP)** (stage `0`): `fc27_first_test_GAF4` (TCP06's thresholds
and hypotheses verbatim) with the planes built from CFS27-pruned TCP05 graphs, and in addition the
small-marker rule (PP): for every `x ∈ S₁`, preimage `q` of `x` and retained marker with
`ρ(c_a) < ρ(q)/5`, `plane x ≤ ker v_a`. -/
theorem fc27_first_test_pp_GAF5 {ν Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg)
    (hsgΓ : sg < Γ / 200) (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst)) (heg : 0 < eg)
    (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θ : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θ ∧
    θ < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
      (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
        e T V vs ζ Λz),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θ ^ 2 / 1000 → μ * Δ ≤ θ / 100 →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc →
      b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θ ^ 2 / 1000 → vs ≤ θ / 100 → 0 < ζ →
      ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      1000 * tcpGraphConst * Δ * Λ < eg →
      ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
          Module.finrank ℝ (plane x) = gafStageDim 0 ∧
            plane x ≤ gafStageQ P.toLocalChartFamily P.zero 0) ∧
        (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
          (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
            cgpProjMap P.toLocalChartFamily P.zero
              (gafStageTags P.toLocalChartFamily P.zero 0) (sel x) = x) →
          ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
            hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 0 ∩
                ball x (sg * ρ (sel x) / Γ))
              ((AffineSubspace.mk' x (plane x) :
                  Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) ∧
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
          ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
          ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
          let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (cgpGlobalMap P.toLocalChartFamily P.zero) q)
          Function.Surjective Pq ∧
          (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
              (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
          (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
            1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
          ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
        ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ q,
          cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) q =
            x →
          ∀ a : CGPMarkerIndex P.toLocalChartFamily,
            ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
            plane x ≤ LinearMap.ker ((blockMarkerCLM
              (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
              (cgpMarkerTag P.toLocalChartFamily P.zero a) :
                BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  obtain ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θ, hη₂, hγ₀, hηc, hθ, hθ1, hrow⟩ := tcp05_row heg heg1 hν hν1
  refine ⟨σ, hσ, hσ1, min η₂ (1 / 10000000), min γ₀ (1 / 20), ηc, θ, lt_min hη₂ (by norm_num),
    lt_min hγ₀ (by norm_num), hηc, hθ, hθ1, fun Δ hΔ => ?_⟩
  obtain ⟨η₁, hη₁, h⟩ := hrow Δ hΔ
  refine ⟨η₁, hη₁, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
    h26 h27 h28 h29 h30 h31
  have hTCP := h P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    (h16.trans (min_le_left _ _)) (h17.trans (min_le_left _ _)) h18
    (h19.trans (min_le_left _ _)) h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  have hnum := tcp06_numbers_KA8 hΔ h1 h4 (h17.trans (min_le_right _ _))
    (h16.trans (min_le_right _ _))
  have hΔ1 : 1 ≤ Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by
    have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
    linarith
  have hTCP' := tcp05_pruned_GAF5 P.toLocalChartPackets hΔ1 h1 hsmall hnum.1 hTCP
  have hT := tcp06_planes_pp_GAF5 P.toLocalChartPackets h1 hnum.1 (h16.trans (min_le_right _ _))
    hnum.2 hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ hTCP'
  refine hT.elim fun plane hp => ?_
  have hconv := fc27_first_of_tcp06_GAF4 P.toLocalChartFamily P.zero plane hsg.le hp.1 hp.2.1
  refine ⟨plane, hconv.1, hconv.2, fun x hx => ?_, fun x hx q hq a ha => ?_⟩
  · rw [gafCloud_zero_GAF4] at hx
    exact hp.2.2.1 x hx
  · rw [gafCloud_zero_GAF4] at hx
    have hq' : cgpGlobalMap P.toLocalChartFamily P.zero q = x := by
      rw [← cgpProjMap_univ_GAF P.toLocalChartFamily P.zero]
      exact hq
    exact hp.2.2.2 x hx q hq' a ha

end DifferentialGeometry.Geometry.Collapse

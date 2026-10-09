import DifferentialGeometry.Geometry.Fibration.ActualFirstCloudCoverage
import DifferentialGeometry.Geometry.Fibration.ActualFirstGraph

/-!
# TCP06: the actual first cloudy packet, with all-preimage rank (the row)

Blueprint `master207B.tex`, TCP06 (`thm:fibration-actual-first-cloud`, B:5600–5670): for `0 < Γ < 1`
and (TP) `0 < Σ < min{Γ/200, Γ³/(100C)}`, `0 < e < min{1/100, ΓΣ/100}`, with TCP05 and FC04/FC07's
ORIGINAL core `S₁ = F(A₁)` (`fc04Set 7`) and enlargement `S̃₁ = F(Ã₁)` (`fc04Set 8`), the exact
radius `r(x) = Σx_ρ` (`scaleRadius (cgpScaleTag …) Σ`) and the planes `A_x = x + im T_x`,
`T_x = DΦ_i(η_i(p))` at an original core witness `i, p`: `(S₁, S̃₁, r)` passes the open-ball cloud
test (`cfs08_first_cloud`'s `hcloud` with `δc = Γ`), the planes are two-dimensional, and at EVERY
`q` with `F(q) = x` the projected derivative is onto, with singular values in `[1/2, 3C]` (on the
orthogonal complement of its kernel) and normal error `≤ eν`.

`tcp06_row` is stated on THE chapter-14 family `LocalChartPacketsC14` with exactly TCP05's
thresholds and hypotheses; the outputs `η₂`, `γ₀` are shrunk (`β₂ ≤ 10⁻⁷`, `γ ≤ 1/20`) so that
TCP01's Gram margin `γ + β₂ ≤ 1/10` holds (a choice before `Δ`, as in the blueprint).

* `tcp06_numbers_KA8`: `Λ·200 ≤ 1/4` and `γ + β₂ ≤ 1/10` from the hypotheses.
* `tcp06_centre_KA8`: the per-point statement for one circle centre, from TCP05's data;
  `tcp06_point_of_mem_KA8` at a point of `S₁`; `tcp06_planes_KA8` (the planes chosen over `S₁`).
* `tcp06_row`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_TCP06_KA8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_TCP06_KA8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_TCP06_KA8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- TCP06's numerical inputs: FC07's `10⁶ΔΛ < 10⁻⁵` (`Δ ≥ 1200`) gives `Λ·200 ≤ 1/4`, and the
shrunk early outputs `β₂ ≤ 10⁻⁷`, `γ ≤ 1/20` give TCP01's Gram margin `γ + β₂ ≤ 1/10`. -/
theorem tcp06_numbers_KA8 {Δ Λ γ β₂ : ℝ} (hΔ : 1200 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hγ : γ ≤ 1 / 20) (hβ : β₂ ≤ 1 / 10000000) :
    Λ * 200 ≤ 1 / 4 ∧ γ + β₂ ≤ 1 / 10 := by
  refine ⟨?_, by linarith⟩
  have h1 : Λ * 200 ≤ 1000000 * Δ * Λ := by nlinarith
  linarith

/-- **TCP06 at one circle centre** (from TCP05's data for the centre `j.1`): for every core witness
`p` of `j` (`p ∈ B(j, 200ρ(j))`, `‖η_j(p)‖ ≤ 7`) and `x = F(p)`, the plane `W = im DΦ_j(η_j p)` has
dimension two, passes the open cloud test at `x` with radius `Σx_ρ`, and gives the rank at every
preimage of `x`, in the units of `j`. -/
theorem tcp06_centre_KA8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
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
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
      let Pq := W.orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (cgpGlobalMap P.toLocalChartFamily P.zero) q)
      Function.Surjective Pq ∧
      (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
          (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
      ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) := by
  subst hpx
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hC : 0 < tcpGraphConst := lt_of_lt_of_le one_pos one_le_tcpGraphConst
  have hsm2 : ContDiff ℝ 2 Φ := hsm.of_le (by simp)
  have hpoint := tcp06_point_KA8 P.toLocalChartPackets hΛ hΛ200 hj j rfl Φ hsm2 hown
    (fun a => (hb a).2) hΓ hΓ1 hsg hsgΓ hC hsgC heg hegΓ (fun y hy hyη => (hTG y hy hyη).1) hp
    hηp
  obtain ⟨hfin, hcl⟩ := hpoint
  have hrank := fun q (hq : cgpGlobalMap P.toLocalChartFamily P.zero q =
      cgpGlobalMap P.toLocalChartFamily P.zero p) =>
    tcp06_rank_point_KA8 P.toLocalChartPackets hβ hγβ hj j rfl Φ hsm2 hown (fun a => (hb a).1)
      heg1 (fun y hy hyη => (hTG y hy hyη).2) hp hηp hq
  exact ⟨_, hfin, hcl, j, hrank⟩

/-- **TCP06 at one point of the core image** `x ∈ S₁ = F(A₁)`, from TCP05's data at every circle
centre: a two-dimensional plane `W` with the open cloud test at `x` (radius `Σx_ρ`) and the rank at
every preimage of `x`. -/
theorem tcp06_point_of_mem_KA8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
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
        ∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8 →
          ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
              Φ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < eg ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
                fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily i hi x)
                  (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
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
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
      let Pq := W.orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (cgpGlobalMap P.toLocalChartFamily P.zero) q)
      Function.Surjective Pq ∧
      (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
          (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
      ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) := by
  refine Exists.elim hx (fun p hp => ?_)
  refine Exists.elim hp.1 (fun j hj' => ?_)
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  refine Exists.elim (hTCP j.1 hj) (fun Φ hΦ => ?_)
  exact tcp06_centre_KA8 P hΛ hΛ200 hβ hγβ hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ j Φ hΦ.1
    (hΦ.2.1 j rfl) hΦ.2.2.1 hΦ.2.2.2 hj'.1 hj'.2 hp.2

/-- **TCP06 on the whole core image**, from TCP05's data at every circle centre: the planes of
`tcp06_point_of_mem_KA8`, chosen over `S₁`. -/
theorem tcp06_planes_KA8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
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
        ∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8 →
          ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
              Φ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < eg ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
                fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily i hi x)
                  (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
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
      ∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
        ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
        let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (cgpGlobalMap P.toLocalChartFamily P.zero) q)
        Function.Surjective Pq ∧
        (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
            (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
        (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
          1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
        ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) := by
  have hpt := fun x (hx : x ∈ cgpGlobalMap P.toLocalChartFamily P.zero ''
      fc04Set P.toLocalChartFamily P.zero 7) =>
    tcp06_point_of_mem_KA8 P hΛ hΛ200 hβ hγβ hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ hTCP hx
  choose! plane hplane using hpt
  exact ⟨plane, fun x hx => (hplane x hx).1, fun x hx => (hplane x hx).2.1,
    fun x hx => (hplane x hx).2.2⟩

/-- **TCP06** (`thm:fibration-actual-first-cloud`, B:5600) on `LocalChartPacketsC14`: for
`0 < Γ < 1`, (TP) `0 < Σ < min(Γ/200, Γ³/(100C))`, `0 < e < min(1/100, ΓΣ/100)` (`C =
tcpGraphConst`) and the exclusion quality `ν`, there are TCP05's early `σ`, `η₂`, `γ₀`, `η_c`, `θ`
and for every `Δ ≥ 1200` a later `η₁` such that on every actual family with TCP05's hypotheses
there are planes `plane x` over `S₁ = F(A₁)` with (1) `dim plane x = 2`; (2) the open-ball cloud
test at FC04's exact radius `r(x) = Σx_ρ`:
`hausdorffEDist (S̃₁ ∩ B(x, r/Γ)) ((x + plane x) ∩ B(x, r/Γ)) ≤ Γr` (exactly `cfs08_first_cloud`'s
`hcloud`, `δc = Γ`); (3) at EVERY preimage `q` of `x`, in the units of a circle centre `i`: the
projection of `ρ(i)⁻¹dF_q` onto `plane x` is onto, its normal error is `≤ eν`, and
`ν/2 ≤ ‖P_q v‖` on the `g`-orthogonal complement of the kernel, `‖P_q v‖ ≤ 3Cν`
(`ν = √(ρ(i)⁻²g)`). -/
theorem tcp06_row {ν Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg)
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
        ∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
          ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
          ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
          let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (cgpGlobalMap P.toLocalChartFamily P.zero) q)
          Function.Surjective Pq ∧
          (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
              (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
          (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
            1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
          ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) := by
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
  exact tcp06_planes_KA8 P h1 hnum.1 (h16.trans (min_le_right _ _)) hnum.2 hΓ hΓ1 hsg hsgΓ hsgC
    heg heg1 hegΓ hTCP

end DifferentialGeometry.Geometry.Collapse

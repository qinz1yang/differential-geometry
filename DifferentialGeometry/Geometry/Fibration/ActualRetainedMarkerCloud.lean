import DifferentialGeometry.Geometry.Fibration.ActualGlobalDerivativeApplications
import DifferentialGeometry.Geometry.Metric.ActualCloudSupportScale

/-!
# FC26 and CFS07 on the actual retained-marker cloud of `𝓔⁰`

Blueprint `master207B.tex`, FC26 (`lem:fibration-projected-radii`, B:1625) and CFS07
(`lem:fibration-cloud-marker-scale-comparison`, B:2188), bound to CGP01's actual map
`𝓔⁰ = cgpGlobalMap L Z` (`L : LocalChartFamily`, `Z` the zero family).

* The retained constant-radius markers: the index type `CGPMarkerIndex L` (circle, slim, edge
  centres), `cgpMarkerTag` (their tags in `𝓔⁰`), `cgpMarker` (`y ↦ (y_i).snd`, the block's scalar
  component; `1`-Lipschitz, `lipschitzWith_cgpMarker`), centre radius `ρ(c_i)`, smooth-domain radius
  `cgpMarkerDomain` (`200`, `10⁶Δ`, `100Δ`), original cores `cgpMarkerCore` (`B(j, 2ρ)`,
  `B(j, 2Δρ)`, `B(j, 3Δρ)`: the LC87 plateaux) and the cloud `cgpRetainedCloud` (their union).
* `cgpMarker_globalMap`: on `𝓔⁰`, `marker_i = ρ(c_i) ζ_i` with the actual cutoff `ζ_i`, which is the
  zero extension of its restriction to the smooth domain.
* `fc26_row`: (AS) every preimage `q` of an image point with positive `i` marker has
  `3ρ(c_i)/4 ≤ ρ(q) ≤ 5ρ(c_i)/4`; every cloud point has a full marker; and for EVERY pair of cloud
  preimages and `0 ≤ Σ ≤ 1/2`: `|Σρ(q) − Σρ(p)| ≤ 2(|𝓔⁰p − 𝓔⁰q| + Σρ(p))` (FC26 for every choice of
  preimages).
* `cfs07_row`: (MC) for every pair of cloud preimages and for every selection of preimages over the
  image of the cloud, with `LΣ ≤ 1/5`; FC04's exact radius (the scale block) gives the stronger
  ratio `4/5 … 5/4`.
* `exhaustion_cgpRetainedCloud`: every point outside the zero stratum lies in the cloud.
Parameter ranges: `Δ ≥ 1`, `0 ≤ σ_s ≤ 1/100`, `Λ ≥ 0`, `Λ·10⁶Δ ≤ 1/4`.
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

section Marker

variable {κ : Type*} {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]

/-- The scalar component of one block is `1`-Lipschitz on the block space. -/
theorem lipschitzWith_blockSnd_KA2 [Fintype κ] (t : κ) :
    LipschitzWith 1 (fun y : BlockSpace V => (y t).snd) :=
  LipschitzWith.of_dist_le_mul fun y y' => by
    rw [NNReal.coe_one, one_mul]
    exact (WithLp.dist_snd_le (y t) (y' t)).trans (PiLp.dist_apply_le y y' t)

/-- A function vanishing off a set is the zero extension of its restriction. -/
theorem extend_val_restrict_eq_KA2 {Y : Type*} {S : Set Y} {f : Y → ℝ}
    (hf : ∀ p, f p ≠ 0 → p ∈ S) (p : Y) :
    (Subtype.val : S → Y).extend (fun z => f z.1) 0 p = f p := by
  by_cases hp : p ∈ S
  · exact Subtype.val_injective.extend_apply (fun z => f z.1) 0 ⟨p, hp⟩
  · rw [Function.extend_apply' _ _ _ (fun ⟨z, hz⟩ => hp (hz ▸ z.2))]
    by_contra h
    exact hp (hf p (Ne.symm h))

end Marker

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- The retained constant-radius markers of `𝓔⁰` used by FC26/CFS07: circle, slim and edge
centres (the zero blocks, of radius `≥ Tρ`, are not among them). -/
abbrev CGPMarkerIndex (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) :
    Type :=
  L.circle.finite_centres.toFinset ⊕ L.slim.finite_centres.toFinset ⊕
    L.edge.finite_centres.toFinset

/-- The tag of a retained marker in `𝓔⁰`. -/
def cgpMarkerTag (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) :
    CGPMarkerIndex L → CGPTag L Z
  | .inl j => .inl j
  | .inr (.inl j) => .inr (.inl j)
  | .inr (.inr j) => .inr (.inr (.inl j))

/-- The centre of a retained marker. -/
def cgpMarkerCentre (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) :
    CGPMarkerIndex L → X
  | .inl j => j.1
  | .inr (.inl j) => j.1
  | .inr (.inr j) => j.1

/-- The normalized smooth-domain radius of a retained marker (`200`, `10⁶Δ`, `100Δ`). -/
def cgpMarkerDomain (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) :
    CGPMarkerIndex L → ℝ
  | .inl _ => 200
  | .inr (.inl _) => 1000000 * Δ
  | .inr (.inr _) => 100 * Δ

/-- The original core (LC87 plateau) of a retained marker: `B(j, 2ρ)`, `B(j, 2Δρ)`, `B(j, 3Δρ)`. -/
def cgpMarkerCore (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) :
    CGPMarkerIndex L → Set X
  | .inl j => ball j.1 (2 * ρ j.1)
  | .inr (.inl j) => ball j.1 (2 * (Δ * ρ j.1))
  | .inr (.inr j) => ball j.1 (3 * Δ * ρ j.1)

/-- The actual cutoff of a retained marker. -/
def cgpMarkerCutoff (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) :
    CGPMarkerIndex L → X → ℝ
  | .inl j => L.circle.cutoff j
  | .inr (.inl j) => L.slim.cutoff j
  | .inr (.inr j) => L.edge.cutoff j

/-- The retained marker `y ↦ (y_i).snd` of the block space of `𝓔⁰`. -/
def cgpMarker (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : CGPMarkerIndex L)
    (y : BlockSpace (fun _ : CGPTag L Z => ℝ²)) : ℝ :=
  (y (cgpMarkerTag L Z i)).snd

/-- The retained cloud: the union of the original cores of the retained markers. -/
def cgpRetainedCloud (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) :
    Set X :=
  {p | ∃ i, p ∈ cgpMarkerCore L i}

theorem lipschitzWith_cgpMarker
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : CGPMarkerIndex L) :
    LipschitzWith 1 (cgpMarker L Z i) :=
  lipschitzWith_blockSnd_KA2 (cgpMarkerTag L Z i)

/-- Every actual retained cutoff vanishes off its smooth domain `B(c_i, D_i ρ(c_i))`. -/
theorem cgpMarkerCutoff_ne_zero
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ)
    (i : CGPMarkerIndex L) (p : X) (hp : cgpMarkerCutoff L i p ≠ 0) :
    p ∈ ball (cgpMarkerCentre L i) (cgpMarkerDomain L i * ρ (cgpMarkerCentre L i)) := by
  rcases i with j | j | j
  · have hj := (Set.Finite.mem_toFinset _).mp j.2
    have h1 : (ρ j.1)⁻¹ * dist p j.1 < 200 := (L.circle.coord_lt_of_cutoff_ne_zero j.1 hj p hp).1
    rw [inv_mul_lt_iff₀ (hρ j.1)] at h1
    change dist p j.1 < 200 * ρ j.1
    linarith
  · have hj := (Set.Finite.mem_toFinset _).mp j.2
    obtain ⟨h1, h2, h3, -⟩ := fc18_slim_row L hΔ hj
    have h := h3 (h2 (h1 (subset_tsupport _ hp)))
    change p ∈ ball j.1 (1000000 * Δ * ρ j.1)
    convert h using 2
    norm_num
  · obtain ⟨-, hball, -, -⟩ := L.edge.mem_of_cutoff_ne_zero hΔ hp
    rw [inv_mul_lt_iff₀ (hρ j.1)] at hball
    change dist p j.1 < 100 * Δ * ρ j.1
    linarith

/-- **The retained markers of `𝓔⁰`**: `marker_i(𝓔⁰ p) = ρ(c_i) ζ_i(p)`, `ζ_i` the zero extension of
the actual cutoff's restriction to the smooth domain. -/
theorem cgpMarker_globalMap
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 0 < Δ)
    (i : CGPMarkerIndex L) (p : X) :
    cgpMarker L Z i (cgpGlobalMap L Z p) = ρ (cgpMarkerCentre L i) *
      (Subtype.val : ball (cgpMarkerCentre L i)
        (cgpMarkerDomain L i * ρ (cgpMarkerCentre L i)) → X).extend
        (fun z => cgpMarkerCutoff L i z.1) 0 p := by
  rw [extend_val_restrict_eq_KA2 (cgpMarkerCutoff_ne_zero L hΔ i) p]
  rcases i with j | j | j <;> rfl

/-- The retained cutoffs are one on their original cores (LC87 plateaux). -/
theorem cgpMarkerCutoff_core
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ)
    (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) (i : CGPMarkerIndex L) {p : X}
    (hp : p ∈ cgpMarkerCore L i) : cgpMarkerCutoff L i p = 1 := by
  rcases i with j | j | j
  · exact L.circle.plateau j.1 ((Set.Finite.mem_toFinset _).mp j.2) p hp
  · have hj := (Set.Finite.mem_toFinset _).mp j.2
    change L.slim.cutoff j.1 p = 1
    rw [slimFamily_cutoff_eq_KA2 L hj]
    exact (L.slim.centre j.1 hj).cutoff_eq_one hΔ hσs hσs1 hp
  · exact L.edge.cutoff_eq_one ((Set.Finite.mem_toFinset _).mp j.2) (mem_ball.mp hp)

/-- The original cores lie in the smooth domains. -/
theorem cgpMarkerCore_subset
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 1 ≤ Δ)
    (i : CGPMarkerIndex L) :
    cgpMarkerCore L i ⊆
      ball (cgpMarkerCentre L i) (cgpMarkerDomain L i * ρ (cgpMarkerCentre L i)) := by
  rcases i with j | j | j <;> refine ball_subset_ball ?_
  · change 2 * ρ j.1 ≤ 200 * ρ j.1
    linarith [hρ j.1]
  · change 2 * (Δ * ρ j.1) ≤ 1000000 * Δ * ρ j.1
    nlinarith [hρ j.1]
  · change 3 * Δ * ρ j.1 ≤ 100 * Δ * ρ j.1
    nlinarith [hρ j.1]

/-- Every point outside the zero stratum lies in the retained cloud (LC87's exhaustion). -/
theorem exhaustion_cgpRetainedCloud
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ) {p : X}
    (hp : p ∉ scaledSplittingStratum.{0, 0} ρ hρ β 0) : p ∈ cgpRetainedCloud L := by
  rcases L.exhaustion p with h0 | ⟨j, hj, hpj⟩ | ⟨j, hj, hpj⟩ | ⟨j, hj, hpj⟩
  · exact absurd h0 hp
  · exact ⟨.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩, hpj⟩
  · exact ⟨.inr (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩), hpj⟩
  · refine ⟨.inr (.inr ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩), ?_⟩
    change p ∈ ball j (3 * Δ * ρ j)
    rw [mem_ball]
    nlinarith [mul_pos hΔ (hρ j)]

/-- **FC26** (`lem:fibration-projected-radii`) on the actual retained cloud of `𝓔⁰`: (AS) for every
preimage of an image point with a positive retained marker, a full marker at every cloud point, and
for EVERY pair of cloud preimages `|Σρ(q) − Σρ(p)| ≤ 2(|𝓔⁰p − 𝓔⁰q| + Σρ(p))`, `0 ≤ Σ ≤ 1/2`. -/
theorem fc26_row (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) :
    (∀ i p, 0 < cgpMarker L Z i (cgpGlobalMap L Z p) →
      3 * ρ (cgpMarkerCentre L i) / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ (cgpMarkerCentre L i) / 4) ∧
    (∀ p ∈ cgpRetainedCloud L, ∃ i,
      cgpMarker L Z i (cgpGlobalMap L Z p) = ρ (cgpMarkerCentre L i)) ∧
    ∀ sg : ℝ, 0 ≤ sg → sg ≤ 1 / 2 → ∀ p ∈ cgpRetainedCloud L, ∀ q ∈ cgpRetainedCloud L,
      |sg * ρ q - sg * ρ p| ≤ 2 * (dist (cgpGlobalMap L Z p) (cgpGlobalMap L Z q) + sg * ρ p) := by
  have hΔ0 : 0 < Δ := by linarith
  have hD : ∀ i, cgpMarkerDomain L i = 200 ∨ cgpMarkerDomain L i = 100 * Δ ∨
      cgpMarkerDomain L i = 1000000 * Δ := by
    rintro (j | j | j)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  have hsmall' : ((Real.toNNReal Λ : NNReal) : ℝ) * (1000000 * Δ) ≤ 1 / 4 := by
    rw [Real.coe_toNNReal _ hΛ]
    exact hsmall
  obtain ⟨hs, hf, -⟩ := original_packet_marker_scale_binding (cgpGlobalMap L Z) ρ
    L.lipschitz_scale (cgpMarkerCentre L) (cgpMarkerDomain L) Δ hΔ hD hsmall'
    (fun i => hρ _) (fun i z => cgpMarkerCutoff L i z.1) (cgpMarker L Z)
    (cgpMarker_globalMap L Z hΔ0) (cgpMarkerCore L) (cgpMarkerCore_subset L hΔ)
    (fun i p hp => cgpMarkerCutoff_core L hΔ0 hσs hσs1 i hp) (cgpRetainedCloud L)
    (fun p hp => hp)
  refine ⟨hs, hf, fun sg hsg hsg1 p hp q hq => ?_⟩
  exact radius_control_of_retained_markers (P := cgpRetainedCloud L)
    (fun z => cgpGlobalMap L Z z.1) (fun z => ρ z.1) (cgpMarker L Z)
    (fun i => ρ (cgpMarkerCentre L i)) (fun i => hρ _) (lipschitzWith_cgpMarker L Z)
    (fun z => hf z.1 z.2) (fun i z hz => hs i z.1 hz) hsg hsg1 ⟨p, hp⟩ ⟨q, hq⟩

/-- **CFS07** (`lem:fibration-cloud-marker-scale-comparison`) on the actual retained cloud of `𝓔⁰`:
for `L' ≥ 0`, `0 ≤ Σ` with `L'Σ ≤ 1/5`, (MC) for every pair of cloud preimages and for every
selection of preimages over the image of the cloud; FC04's exact radius (the scale block of `𝓔⁰`)
is `1`-Lipschitz on the image and gives the stronger ratio `4/5 … 5/4`. -/
theorem cfs07_row (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) {L' sg : ℝ}
    (hL' : 0 ≤ L') (hsg : 0 ≤ sg) (hLsg : L' * sg ≤ 1 / 5) :
    (∀ p ∈ cgpRetainedCloud L, ∀ q ∈ cgpRetainedCloud L,
      dist (cgpGlobalMap L Z p) (cgpGlobalMap L Z q) ≤ L' * max (sg * ρ p) (sg * ρ q) →
      (3 / 5 : ℝ) * ρ p ≤ ρ q ∧ ρ q ≤ (5 / 3 : ℝ) * ρ p) ∧
    (∀ select : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X,
      (∀ x ∈ cgpGlobalMap L Z '' cgpRetainedCloud L,
        select x ∈ cgpRetainedCloud L ∧ cgpGlobalMap L Z (select x) = x) →
      ∀ x ∈ cgpGlobalMap L Z '' cgpRetainedCloud L, ∀ y ∈ cgpGlobalMap L Z '' cgpRetainedCloud L,
        dist y x ≤ L' * max (sg * ρ (select y)) (sg * ρ (select x)) →
        sg * ρ (select x) / (5 / 3) ≤ sg * ρ (select y) ∧
          sg * ρ (select y) ≤ (5 / 3) * (sg * ρ (select x))) ∧
    (∀ p q : X, |ρ p - ρ q| ≤ dist (cgpGlobalMap L Z p) (cgpGlobalMap L Z q)) ∧
    (∀ p q : X, dist (cgpGlobalMap L Z p) (cgpGlobalMap L Z q) ≤ L' * max (sg * ρ p) (sg * ρ q) →
      (4 / 5 : ℝ) * ρ p ≤ ρ q ∧ ρ q ≤ (5 / 4 : ℝ) * ρ p) := by
  have hΔ0 : 0 < Δ := by linarith
  have hD : ∀ i, cgpMarkerDomain L i = 200 ∨ cgpMarkerDomain L i = 100 * Δ ∨
      cgpMarkerDomain L i = 1000000 * Δ := by
    rintro (j | j | j)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  have hsmall' : ((Real.toNNReal Λ : NNReal) : ℝ) * (1000000 * Δ) ≤ 1 / 4 := by
    rw [Real.coe_toNNReal _ hΛ]
    exact hsmall
  obtain ⟨h1, h2⟩ := actualCloud_support_scale_all_preimages (cgpGlobalMap L Z) ρ
    L.lipschitz_scale (cgpMarkerCentre L) (cgpMarkerDomain L) Δ hΔ hD hsmall'
    (fun i => hρ _) (fun i z => cgpMarkerCutoff L i z.1) (cgpMarker L Z)
    (lipschitzWith_cgpMarker L Z) (cgpMarker_globalMap L Z hΔ0) (cgpMarkerCore L)
    (cgpMarkerCore_subset L hΔ) (fun i p hp => cgpMarkerCutoff_core L hΔ0 hσs hσs1 i hp)
    (cgpRetainedCloud L) (fun p hp => hp) hsg hL' hLsg
  have hscale : ∀ p q : X, |ρ p - ρ q| ≤ dist (cgpGlobalMap L Z p) (cgpGlobalMap L Z q) := by
    intro p q
    have h := (lipschitzWith_blockSnd_KA2 (V := fun _ : CGPTag L Z => ℝ²)
      (cgpScaleTag L Z)).dist_le_mul (cgpGlobalMap L Z p) (cgpGlobalMap L Z q)
    rw [NNReal.coe_one, one_mul, Real.dist_eq, cgpGlobalMap_scale, cgpGlobalMap_scale] at h
    exact h
  refine ⟨h1, h2, hscale, fun p q hd => ?_⟩
  have hp := hρ p
  have hq := hρ q
  have hd' := (hscale p q).trans hd
  have hmax : max (sg * ρ p) (sg * ρ q) ≤ sg * max (ρ p) (ρ q) := by
    rw [mul_max_of_nonneg _ _ hsg]
  have hb : |ρ p - ρ q| ≤ L' * sg * max (ρ p) (ρ q) := by
    calc |ρ p - ρ q| ≤ L' * max (sg * ρ p) (sg * ρ q) := hd'
      _ ≤ L' * (sg * max (ρ p) (ρ q)) := mul_le_mul_of_nonneg_left hmax hL'
      _ = L' * sg * max (ρ p) (ρ q) := by ring
  have hb' : |ρ p - ρ q| ≤ max (ρ p) (ρ q) / 5 := by
    have := mul_le_mul_of_nonneg_right hLsg (le_max_of_le_left hp.le : 0 ≤ max (ρ p) (ρ q))
    linarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp hb'
  rcases le_total (ρ p) (ρ q) with hpq | hqp
  · rw [max_eq_right hpq] at hlo hhi
    constructor <;> linarith
  · rw [max_eq_left hqp] at hlo hhi
    constructor <;> linarith

end DifferentialGeometry.Geometry.Collapse

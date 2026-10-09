import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroBlock
import DifferentialGeometry.Geometry.Fibration.ActualZeroDomainEstimates
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroFaces

/-!
# ZSP03 on the chain object: the zero faces descend through every `Q_j` (class-(b) clauses)

Lane C14-ZSP35. Blueprint `master207B.tex`, ZSP03 (`prop:fibration-zero-faces-saturated`,
B:6481–6529): "Every `Q_j` retains `Q₄`, so equality of `π_jE` preserves the `u_i, v_i` equations
in (ZF)"; "use the smooth base function `b_i(w) = u_i(w)/v_i(w) − .4`. The marker has a positive
buffer. Its pullback is the defining function in ZSP02". On `C : Gaf02Chain P.toLocalChartPackets …`
(`P : LocalChartPacketsC14`), with `π_j = (gafStageQ j).starProjection` and the zero block
`J_k z = z (.inr (.inr (.inr (.inl k))))` (`u_k = (J_k z)_vec 0`, `v_k = (J_k z)_mark`):

* `Gaf02Chain.zero_face_saturated_ZSP35`: `π_jE p = π_jE q` forces `J_k E p = J_k E q`; hence every
  whole fibre of `π_jE` meeting the (ZF) set `E⁻¹{v_k ≥ .9R_k, u_k = .4v_k}` (or the marker
  sublevel `E⁻¹{v_k ≥ .9R_k, u_k ≤ .4v_k}`) lies in it;
* `zero_base_function_smooth_ZSP35`: `b_k(w) = u_k(w)/v_k(w) − 2/5` is smooth at every `w` with
  `v_k(w) ≠ 0`; `Gaf02Chain.zero_base_function_ZSP35`: `b_k ∘ π_j ∘ E = b_k ∘ E` and it is smooth
  on `M` wherever `v_k(E) ≠ 0`;
* original side (`𝓔⁰ = cgpGlobalMap`): `zero_face_original_ZSP35` (`𝓔⁰⁻¹` of the (ZF) set is
  exactly the original face `{η_k = 2/5}`) and `zero_block_band_ZSP35` (on `3/10 ≤ η_k ≤ 4/5` the
  zero block is `(R_kη_k, R_k)` and `b_k ∘ 𝓔⁰ = η_k − 2/5`).

Consumer: `zsp03_zero_face_inactive_C14Z_ZSP35` (final family, inactive branch `E = 𝓔⁰`): the
actual (ZF) set is the original face, it is empty / `S²` / `T²` (connected if nonempty), and it is
saturated for every `π_jE`. The adjusted (ZF) set of an active chain is ZSP02's boundary only after
ZSP01's stage half (class (c)); `X_j`, `B_j`, `C_j` are GAF07's.
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- **The descended base function is smooth on the marker-positive region**: on any block space,
`b_t(w) = u_t(w)/v_t(w) − 2/5` (`u_t = (w_t)_vec 0`, `v_t = (w_t)_mark`) is smooth at every `w`
with `v_t(w) ≠ 0`. -/
theorem zero_base_function_smooth_ZSP35 {κ : Type} [Fintype κ] (t : κ)
    (w : BlockSpace (fun _ : κ => ℝ²)) (hw : (w t).snd ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : BlockSpace (fun _ : κ => ℝ²) => ((z t).fst : ℝ²) 0 / (z t).snd - 2 / 5)
      w := by
  have hu : ContDiffAt ℝ ∞ (fun z : BlockSpace (fun _ : κ => ℝ²) => ((z t).fst : ℝ²) 0) w :=
    (((EuclideanSpace.proj (0 : Fin 2)).comp
      (blockVectorCLM (V := fun _ : κ => ℝ²) t)).contDiff).contDiffAt
  have hv : ContDiffAt ℝ ∞ (fun z : BlockSpace (fun _ : κ => ℝ²) => (z t).snd) w :=
    ((blockMarkerCLM (V := fun _ : κ => ℝ²) t).contDiff).contDiffAt
  exact (hu.div hv hw).sub contDiffAt_const

section C14

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **The original zero block on the face band** (ZSP02's "on `η ∈ (.3, .5)` the original block is
`(Rη, R)`", here on `3/10 ≤ η_k ≤ 4/5` where `ζ_k = 1`): `u_k(𝓔⁰) = R_kη_k`, `v_k(𝓔⁰) = R_k` and
`b_k ∘ 𝓔⁰ = η_k − 2/5`. -/
theorem zero_block_band_ZSP35
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (k : P.zero.finite_centres.toFinset) {p : X}
    (hp : (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p ∈
      Icc (3 / 10 : ℝ) (4 / 5)) :
    ((cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 =
        (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius *
          (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p ∧
      (cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl k))))).snd =
        (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ∧
      ((cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
          (cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 =
        (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p - 2 / 5 := by
  have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hone, -⟩ :=
    (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial_spec
  obtain ⟨h1, h2⟩ := cgpGlobalMap_zeroBlock_GAF2 P.toLocalChartFamily P.zero k p
  rw [hone p hp, mul_one] at h1 h2
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2, mul_div_cancel_left₀ _ hR.ne']

/-- **The original preimage of the (ZF) set is the original face**: for every `p`,
`v_k(𝓔⁰ p) ≥ .9R_k ∧ u_k(𝓔⁰ p) = .4v_k(𝓔⁰ p)` exactly when `η_k(p) = 2/5`. -/
theorem zero_face_original_ZSP35
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {k : P.zero.finite_centres.toFinset} {p : X} :
    (9 / 10 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
        (cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl k))))).snd ∧
      ((cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 =
        2 / 5 * (cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl k))))).snd) ↔
    (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p = 2 / 5 := by
  have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨h1, h2⟩ := cgpGlobalMap_zeroBlock_GAF2 P.toLocalChartFamily P.zero k p
  rw [h1, h2]
  constructor
  · rintro ⟨hv, hu⟩
    have hζ : 0 < Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p) := by
      by_contra hneg
      push Not at hneg
      nlinarith
    have hRζ : 0 < (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius *
        Calculus.annularCutoff Calculus.cutoffProfile
          ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p) := mul_pos hR hζ
    have := mul_left_cancel₀ hRζ.ne' (hu.trans (mul_comm _ _))
    exact this
  · intro hη
    obtain ⟨h1', h2', -⟩ := zero_block_band_ZSP35 P k (p := p) (by rw [hη]; norm_num)
    rw [h1] at h1'
    rw [h2] at h2'
    rw [h1', h2', hη]
    exact ⟨by nlinarith, by ring⟩

variable {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **ZSP03, zero faces are saturated** (B:6496: "Every `Q_j` retains `Q₄`, so equality of `π_jE`
preserves the `u_i, v_i` equations in (ZF)"): if `π_jE p = π_jE q` then `J_k E p = J_k E q`, so
`p` lies in the (ZF) set `{v_k(E) ≥ .9R_k, u_k(E) = .4v_k(E)}` (resp. the marker sublevel
`{v_k(E) ≥ .9R_k, u_k(E) ≤ .4v_k(E)}`) exactly when `q` does. -/
theorem Gaf02Chain.zero_face_saturated_ZSP35
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (st : Fin 3)
    (k : P.zero.finite_centres.toFinset) {p q : X}
    (hpq : (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) =
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E q)) :
    C.E p (.inr (.inr (.inr (.inl k)))) = C.E q (.inr (.inr (.inr (.inl k)))) ∧
    ((9 / 10 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
          (C.E p (.inr (.inr (.inr (.inl k))))).snd ∧
        ((C.E p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 =
          2 / 5 * (C.E p (.inr (.inr (.inr (.inl k))))).snd) ↔
      (9 / 10 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
          (C.E q (.inr (.inr (.inr (.inl k))))).snd ∧
        ((C.E q (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 =
          2 / 5 * (C.E q (.inr (.inr (.inr (.inl k))))).snd)) ∧
    ((9 / 10 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
          (C.E p (.inr (.inr (.inr (.inl k))))).snd ∧
        ((C.E p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 ≤
          2 / 5 * (C.E p (.inr (.inr (.inr (.inl k))))).snd) ↔
      (9 / 10 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
          (C.E q (.inr (.inr (.inr (.inl k))))).snd ∧
        ((C.E q (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 ≤
          2 / 5 * (C.E q (.inr (.inr (.inr (.inl k))))).snd)) := by
  have hk : C.E p (.inr (.inr (.inr (.inl k)))) = C.E q (.inr (.inr (.inr (.inl k)))) := by
    have := congrArg (fun z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) =>
      z (.inr (.inr (.inr (.inl k))))) hpq
    simp only [gafStageQ_starProjection_zeroTag_GAF8 P st k] at this
    exact this
  rw [hk]
  exact ⟨rfl, Iff.rfl, Iff.rfl⟩

/-- **ZSP03, the boundary equation descends** (B:6512–6517): `b_k ∘ π_j ∘ E = b_k ∘ E` with
`b_k(w) = u_k(w)/v_k(w) − 2/5`, and this pullback is smooth on `M` at every point with
`v_k(E p) ≠ 0`. -/
theorem Gaf02Chain.zero_base_function_ZSP35
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (st : Fin 3)
    (k : P.zero.finite_centres.toFinset) :
    (∀ p, (((gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p)
          (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        ((gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p)
          (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 =
      ((C.E p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (C.E p (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) ∧
    ∀ p, (C.E p (.inr (.inr (.inr (.inl k))))).snd ≠ 0 →
      ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun q => ((C.E q (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (C.E q (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) p := by
  refine ⟨fun p => by rw [gafStageQ_starProjection_zeroTag_GAF8 P st k], fun p hp => ?_⟩
  have hE := C.stage_smooth.2.2
  have hu : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (fun q => ((C.E q (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0) p :=
    (((EuclideanSpace.proj (0 : Fin 2)).comp (blockVectorCLM
      (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inr (.inl k)))))).contDiff.comp_contMDiff hE).contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (fun q => (C.E q (.inr (.inr (.inr (.inl k))))).snd) p :=
    ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inr (.inr (.inl k))))).contDiff.comp_contMDiff hE).contMDiffAt
  exact (hu.div₀ hv hp).sub contMDiffAt_const

end C14

section Final

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **Consumer: ZSP03's zero face on the final family, inactive branch.** For a chain on
`LocalChartPacketsC14Z` whose circle, edge and slim families are empty (`E = 𝓔⁰`), the actual (ZF)
set `{v_k(E) ≥ .9R_k, u_k(E) = .4v_k(E)}` is the original face `{η_k = 2/5}`; it is empty with
`{η_k ≤ 2/5} = univ`, or `≃ₜ S²`, or `≃ₜ ℝ²/ℤ²`; if nonempty it is compact and connected; and it is
saturated for every `π_jE`. -/
theorem zsp03_zero_face_inactive_C14Z_ZSP35
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM} (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (h0 : P.circle.centres = ∅) (h1 : P.edge.centres = ∅) (h2 : P.slim.centres = ∅)
    (k : P.zero.finite_centres.toFinset) :
    {p | 9 / 10 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
        (C.E p (.inr (.inr (.inr (.inl k))))).snd ∧
      ((C.E p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 =
        2 / 5 * (C.E p (.inr (.inr (.inr (.inl k))))).snd} =
      {p | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p = 2 / 5} ∧
    (({x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5} = univ ∧
        {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x = 2 / 5} = ∅) ∨
      Nonempty ({x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x = 2 / 5} ≃ₜ
        Metric.sphere (0 : E3) 1) ∨
      Nonempty ({x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x = 2 / 5} ≃ₜ
        (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) ∧
    ({x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x = 2 / 5}.Nonempty →
      IsCompact {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x = 2 / 5} ∧
      IsConnected {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x = 2 / 5}) ∧
    ∀ st : Fin 3, ∀ p q : X,
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) =
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E q) →
      ((9 / 10 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
            (C.E p (.inr (.inr (.inr (.inl k))))).snd ∧
          ((C.E p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 =
            2 / 5 * (C.E p (.inr (.inr (.inr (.inl k))))).snd) ↔
        (9 / 10 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
            (C.E q (.inr (.inr (.inr (.inl k))))).snd ∧
          ((C.E q (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 =
            2 / 5 * (C.E q (.inr (.inr (.inr (.inl k))))).snd)) := by
  obtain ⟨k0, k1, k2⟩ := C.empty_family_stage_id
  have hE : C.E = cgpGlobalMap P.toLocalChartFamily P.zero := by
    funext p
    simp only [Gaf02Chain.E, Gaf02Chain.g₂, Gaf02Chain.g₁, Function.comp_apply, k0 h0, k1 h1,
      k2 h2, id]
  have ha : (2 / 5 : ℝ) ∈ Icc (1 / 5 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  have hc := (Set.Finite.mem_toFinset _).mp k.2
  refine ⟨?_, P.zero_face_type_ZSP35 hc ha, fun hne => ?_, fun st p q hpq =>
    (C.zero_face_saturated_ZSP35 st k hpq).2.1⟩
  · ext p
    rw [hE]
    exact zero_face_original_ZSP35 (P := P.toLocalChartPacketsC14D.toLocalChartPacketsC14) (k := k)
      (p := p)
  · obtain ⟨h1', h2', -⟩ := P.zero_face_connected_ZSP35 hc ha hne
    exact ⟨h1', h2'⟩

end Final

end DifferentialGeometry.Geometry.Collapse

import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4Staged

/-!
# Register V4: the three `δ`'s and TCP02's raw circle buffer at the `β₂` stage
(lane FC39-V4C; review 57, §3.5 and dispositions item 3)

Three different errors live in the closed chain and are kept apart here:

* `δ_raw = R.later.circle.δ` — PR11's raw circle reference error (TCP02/TCP03, B:5313, B:10126;
  register display `δ_raw < min (θ₂²/10⁸) circleUp`), a field of the circle prefix
  `ClosedCirclePrefixV4`, fixed BEFORE `β₂`;
* `δ'_cone` — the prefix witness of the validity record (`ClosedFamilyOnTailC14DV4`'s `δ'`, a
  producer OUTPUT read before `T₀`);
* `δ_cone < δ'_cone` — LPA02's cone error of the ONE realization call; it is the `δ` argument of
  the final family `LocalChartPacketsC14D … δ_cone εr …` and of the joint witness.

`Tcp02OutV2` (the registered `tcp02_row`) exports the alignment (TR) on the radius-`1000` ball at
the accuracy `E`; it does NOT export TCP02's raw buffer clause (B:5326–5328): "the original circle
raw balls contain radius `5000` and have distortion less than `δ` there, with actual coverage to
error less than `δ` on buffered target balls". This file adds that clause as a native `Out`:

* `klRawBufferV4C f δ`: for one KL map, distortion `< δ` on `B(p, 5000)` and every
  target of radius `< 5000` has an ACTUAL witness within error `< δ` at radius `< |target| + δ`;
  `kl_raw_buffer_V4C`: it holds for any KL `β`-map with `3β < δ`, `β ≤ 10⁻⁶`;
* `Tcp02RawBufferOutV4C P δ`: at every circle centre `i`, in `i`'s normalization, the ORIGINAL
  circle raw map (the centre's `(2, β₂)`-splitting `(P.circleAdapted i hi).split`, the same map
  whose first factor is `circleRaw_KA3`) meets `klRawBufferV4C` at `δ`;
* `ClosedThresholdsV4.withRawβ₂_V4C`: the request `β₂ < δ_raw/3` as a `β₂` cap read at the circle
  prefix (PRE-`β_c`, so the merge order of `StaticRegisterV4Order` is kept);
* `ClosedFamilyInstanceV4.tcp02_raw_buffer_V4C`, `ClosedFamilyInstanceC14DV4.tcp02_raw_buffer_V4C`:
  the `Out` at `δ_raw` on every instance of a register of a strategy below the cap;
* `ClosedFamilyAtC14DV4.three_deltas_V4C`: on the strong C14D realization, at every register, the
  three errors with their separate roles in ONE statement;
* `exists_closed_realization_rawBuffer_V4C` (consumer): the C14D realization of any strategy with
  the raw cap merged in gives that statement at every register.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ### The kernel -/

/-- **TCP02's raw buffer clause for one KL map** (B:5326–5328): distortion `< δ` on `B(p, 5000)`,
and every target of radius `< 5000` about `q` has an ACTUAL witness of image error `< δ` at radius
`< |target| + δ`. The metric instances are implicit arguments, so the predicate applies to a map
whose source carries a rescaled metric (as the circle raw maps do). -/
def klRawBufferV4C {X Y : Type*} {iX : MetricSpace X} {iY : MetricSpace Y}
    {p : X} {q : Y} {β : ℝ} (f : @KleinerLottApprox X Y iX iY p q β) (δ : ℝ) : Prop :=
  (∀ x ∈ ball p 5000, ∀ x' ∈ ball p 5000, |dist (f.toFun x) (f.toFun x') - dist x x'| < δ) ∧
    ∀ y : Y, dist y q < 5000 → ∃ x, dist x p < dist y q + δ ∧ dist (f.toFun x) y < δ

/-- **Raw buffer of a KL map** (TCP02's raw clause, kernel): a pointed KL `β`-approximation with
`3β < δ` and `β ≤ 10⁻⁶` meets `klRawBufferV4C` at `δ`. -/
theorem kl_raw_buffer_V4C {X Y : Type*} {iX : MetricSpace X} {iY : MetricSpace Y}
    {p : X} {q : Y} {β δ : ℝ} (f : @KleinerLottApprox X Y iX iY p q β) (hβδ : 3 * β < δ)
    (hβs : β ≤ 1 / 10 ^ 6) : klRawBufferV4C f δ := by
  have hβ := f.error_pos
  have hβ1 := f.error_lt_one
  have hβR : (5003 : ℝ) ≤ β⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hβ]
    exact hβs.trans (by norm_num)
  have hsub : ball p 5000 ⊆ ball p β⁻¹ := ball_subset_ball (by linarith)
  refine ⟨fun x hx x' hx' => (f.distortion x (hsub hx) x' (hsub hx')).trans_lt (by linarith),
    fun y hy => ?_⟩
  obtain ⟨x, hx, hxy⟩ := f.coverage_witness y (by linarith)
  have hrad := (abs_le.mp (f.radial_error x hx)).1
  have htri : dist (f.toFun x) q ≤ dist (f.toFun x) y + dist y q := dist_triangle _ _ _
  rw [dist_comm] at hxy
  exact ⟨x, by linarith, by linarith⟩

/-! ### The native `Out` -/

section Out

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- **TCP02's raw circle buffer** (B:5326–5328, native): at every circle centre `i`, the ORIGINAL
circle raw map (the centre's `(2, β₂)`-splitting, normalized by `ρ(i)⁻¹`, whose first factor is
`circleRaw_KA3`) meets `klRawBufferV4C` at `δraw`: distortion `< δraw` on the `i`-normalized ball
`B(i, 5000)`, and every target of radius `< 5000` about the basepoint `(0, a)` has an actual witness
of image error `< δraw` at radius `< |target| + δraw`. -/
def Tcp02RawBufferOutV4C
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (δraw : ℝ) : Prop :=
  ∀ i (hi : i ∈ P.circle.centres), klRawBufferV4C (P.circleAdapted i hi).split δraw

/-- **The raw buffer from the splitting quality**: on every family with `3 β₂ < δraw` and
`β₂ ≤ 10⁻⁶`, TCP02's raw circle buffer holds at `δraw`. -/
theorem tcp02_raw_buffer_of_β_V4C
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {δraw : ℝ} (h3 : 3 * β 2 < δraw) (hβ : β 2 ≤ 1 / 10 ^ 6) : Tcp02RawBufferOutV4C P δraw := by
  intro i hi
  exact kl_raw_buffer_V4C (P.circleAdapted i hi).split h3 hβ

end Out

/-! ### The request at the `β₂` stage -/

/-- **TCP02's raw request `β₂ < δ_raw/3` as a strategy cap** (review 57, §3.5): `U` with `β₂`'s slot
capped by `δ_raw/3`, read at the circle prefix (before `β_c`). -/
def ClosedThresholdsV4.withRawβ₂_V4C {D : ClosedEarlyData} (U : ClosedThresholdsV4 D) :
    ClosedThresholdsV4 D :=
  { U with
    β₂Up := fun st cp β₃ => min (U.β₂Up st cp β₃) (posOr_VAL3 (cp.δ / 3))
    β₂Up_pos := fun st cp β₃ => lt_min (U.β₂Up_pos st cp β₃) (posOr_pos_VAL3 _) }

/-- The raw cap only lowers `β₂`'s slot. -/
theorem ClosedThresholdsV4.withRawβ₂_below_V4C {D : ClosedEarlyData} (U : ClosedThresholdsV4 D) :
    ClosedStrategyBelowV4 U.withRawβ₂_V4C U where
  lc18_le := le_rfl
  circleUp_le := fun _ _ _ _ _ => le_rfl
  β₂Up_le := fun _ _ _ => min_le_left _ _
  ΔLow_ge := fun _ _ _ _ => le_rfl
  errorsUp_le := fun _ _ _ => le_rfl
  sectionUp_le := fun _ _ _ _ => le_rfl
  lfr29W_le := fun _ _ _ _ _ => le_rfl
  endpointUp_le := fun _ _ _ _ _ _ => le_rfl
  σcolUp_le := fun _ _ _ _ _ _ _ => le_rfl
  scaleUp_le := fun _ _ _ _ => le_rfl
  wUp_le := fun _ _ _ _ _ => le_rfl
  splitUp_le := fun _ _ _ _ _ => le_rfl
  β₁Up_le := fun _ _ _ _ _ _ => le_rfl
  T₀Low_ge := fun _ _ _ _ _ _ _ => le_rfl
  LmaxLow_ge := fun _ _ _ _ _ _ => le_rfl
  tailLow_ge := fun _ _ _ _ _ _ _ => le_rfl

/-- **`3β₂ < δ_raw` at every register of a strategy below the raw cap.** -/
theorem ClosedRegisterV4.three_mul_β₂_lt_δ_of_below_V4C {D : ClosedEarlyData}
    {T U : ClosedThresholdsV4 D} (h : ClosedStrategyBelowV4 T U.withRawβ₂_V4C)
    (R : ClosedRegisterV4 D T) : 3 * R.later.excl.β₂ < R.later.circle.δ := by
  have h1 := (R.later.β₂_lt.trans_le (min_le_left _ _)).trans_le (h.β₂Up_le _ _ _)
  have hδ := R.later.δ_pos
  have h2 : U.withRawβ₂_V4C.β₂Up R.stage R.later.circle.toPrefixV4 R.later.excl.β₃ ≤
      R.later.circle.δ / 3 := by
    change min _ (posOr_VAL3 (R.later.circle.δ / 3)) ≤ _
    rw [posOr_eq_VAL3 (by positivity)]
    exact min_le_right _ _
  have := h1.trans_le h2
  linarith

/-- **TCP02's raw buffer on every C14 instance** at a register of a strategy below the raw cap: the
family's circle raw maps meet the clause at `δ_raw = R.later.circle.δ`. -/
theorem ClosedFamilyInstanceV4.tcp02_raw_buffer_V4C {K : ℕ} {D : ClosedEarlyData}
    {T U : ClosedThresholdsV4 D} (h : ClosedStrategyBelowV4 T U.withRawβ₂_V4C)
    {R : ClosedRegisterV4 D T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (F : ClosedFamilyInstanceV4 K R M δ εr Λz) :
    Tcp02RawBufferOutV4C F.family.toLocalChartPackets R.later.circle.δ := by
  refine tcp02_raw_buffer_of_β_V4C _ ?_ ?_
  · rw [R.β_two_VAL6]
    exact R.three_mul_β₂_lt_δ_of_below_V4C h
  · rw [R.β_two_VAL6]
    exact R.later.β₂_lt_audit_VAL6.le

/-- The same on every C14D instance. -/
theorem ClosedFamilyInstanceC14DV4.tcp02_raw_buffer_V4C {K : ℕ} {D : ClosedEarlyData}
    {T U : ClosedThresholdsV4 D} (h : ClosedStrategyBelowV4 T U.withRawβ₂_V4C)
    {R : ClosedRegisterV4 D T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (F : ClosedFamilyInstanceC14DV4 K R M δ εr Λz) :
    Tcp02RawBufferOutV4C F.family.toLocalChartPackets R.later.circle.δ :=
  F.toC14_VAL6.tcp02_raw_buffer_V4C h

/-! ### The three errors on the strong realization -/

/-- **The three `δ`'s at every register of the strong C14D realization** (review 57, §3.5): below
the raw cap, at every register `R`, `δ_raw = R.later.circle.δ` is PR11's raw reference error
(`0 < δ_raw < θ₂²/10⁸`, `3β₂ < δ_raw`); the record's prefix witness `δ'_cone` and ONE cone error
`δ_cone < δ'_cone` are separate numbers; on every member of the tail the final family
`LocalChartPacketsC14D` is taken at `δ_cone` (its `δ` argument and LPA02's witness), and its circle
raw maps meet TCP02's raw buffer at `δ_raw`. -/
theorem ClosedFamilyAtC14DV4.three_deltas_V4C {K : ℕ} {Wseq : ℕ → CompactCarrier.{u}}
    {gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier} {D : ClosedEarlyData}
    {T U : ClosedThresholdsV4 D} (hfam : ClosedFamilyAtC14DV4 K Wseq gseq T)
    (h : ClosedStrategyBelowV4 T U.withRawβ₂_V4C) (R : ClosedRegisterV4 D T) :
    (0 < R.later.circle.δ ∧ R.later.circle.δ < R.later.circle.θ₂ ^ 2 / 10 ^ 8 ∧
      3 * R.later.excl.β₂ < R.later.circle.δ) ∧
    ∃ εr δ'cone Λz : ℝ, 0 < δ'cone ∧ 0 < εr ∧ εr < R.later.err.co.ε₀ ∧ 0 < Λz ∧
      ∃ δcone : ℝ, 0 < δcone ∧ δcone < δ'cone ∧ ∀ m, R.later.tail ≤ m →
        ∃ M : ClosedModel (Wseq m) (gseq m), ∃ F : ClosedFamilyInstanceC14DV4 K R M δcone εr Λz,
          Tcp02RawBufferOutV4C F.family.toLocalChartPackets R.later.circle.δ := by
  refine ⟨⟨R.later.δ_pos, R.later.δ_lt.trans_le (min_le_left _ _),
    R.three_mul_β₂_lt_δ_of_below_V4C h⟩, ?_⟩
  obtain ⟨εrF, δ'F, ΛzF, hF⟩ := hfam
  obtain ⟨hεr, -, hεr₀, hδ', hΛz, -, δc, hδc, hδcδ', ht⟩ := hF R
  refine ⟨_, _, _, hδ', hεr, hεr₀, hΛz, δc, hδc, hδcδ', fun m hm => ?_⟩
  obtain ⟨M, ⟨F⟩, -, -⟩ := ht m hm
  exact ⟨M, F, F.tcp02_raw_buffer_V4C h⟩

/-- **Consumer: the raw cap realized** (review 57, §3.5). For every threshold strategy `U`, the
complete C14D realization of `U` with TCP02's raw request `β₂ < δ_raw/3` merged into `β₂`'s slot
(before `β_c`) gives a common strategy `T` at which every register keeps the three errors apart
and the final family's circle raw maps meet TCP02's raw buffer at `δ_raw` on every member of the
tail. -/
theorem exists_closed_realization_rawBuffer_V4C (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2)))
    {D : ClosedEarlyData} (U : ClosedThresholdsV4 D) :
    ∃ T : ClosedThresholdsV4 D, ClosedStrategyRefinesV4 T U.withRawβ₂_V4C ∧
      ClosedStrategyBelowV4 T U ∧ ClosedFamilyAtC14DV4 K Wseq gseq T ∧
      ∀ R : ClosedRegisterV4 D T,
        (0 < R.later.circle.δ ∧ R.later.circle.δ < R.later.circle.θ₂ ^ 2 / 10 ^ 8 ∧
          3 * R.later.excl.β₂ < R.later.circle.δ) ∧
        ∃ εr δ'cone Λz : ℝ, 0 < δ'cone ∧ 0 < εr ∧ εr < R.later.err.co.ε₀ ∧ 0 < Λz ∧
          ∃ δcone : ℝ, 0 < δcone ∧ δcone < δ'cone ∧ ∀ m, R.later.tail ≤ m →
            ∃ M : ClosedModel (Wseq m) (gseq m),
              ∃ F : ClosedFamilyInstanceC14DV4 K R M δcone εr Λz,
                Tcp02RawBufferOutV4C F.family.toLocalChartPackets R.later.circle.δ := by
  obtain ⟨T, hTU, -, -, hfam⟩ :=
    exists_closed_realization_C14D_VAL6 K hK A hA Wseq gseq hf hg U.withRawβ₂_V4C
  have hb : ClosedStrategyBelowV4 T U.withRawβ₂_V4C := hTU.below_VAL6
  exact ⟨T, hTU, hb.trans_VAL6 U.withRawβ₂_below_V4C, hfam,
    fun R => hfam.three_deltas_V4C hb R⟩

end DifferentialGeometry.Geometry.Collapse

import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4NbBinding

/-!
# Register V4: the `I₁` slot's volume exit — `v_* ≤ vol B(p, ρ(p))/ρ(p)³` on the final family
(lane FC39-V4C(b); review 57, §4.1 row `I₁`, dispositions item 4)

Review 57: "`I₁`: the integral identity and the `v_*` formula are done; the actual volume comparison
still needs a callable exit; equality of formulas is not a volume lower bound." PR20 (B:10180–10183)
defines `w' = w/(2(1 + 2Λ⁻¹)³)` and `v_* = w'/(24 I(1))`; BSA06/LPA01 (B:8010) use it as the
volume lower bound `Vol_{ρ⁻²g} B(p, 1) = vol_g B(p, ρ(p))/ρ(p)³ ≥ v_*` at every centre.

* `ClosedFamilyInstanceV4.volume_exit_V4C`: for a strategy with the record's `I₁ = ∫₀¹ sinh²`
  (`PartialClosedThresholdValidityV4.I₁_eq`), on every instance of the final family at every
  register and at EVERY point `p` of the model, the instance's own scale `ρ` (in LPA01's window,
  `ρ(p) < 2 r_p(w')`) satisfies `0 < v_* ≤ vol B(p, ρ(p))/ρ(p)³` with the register's
  `v_* = closedVStarV4 T R.later.scale`. Route: `volume_lower_at_modified_scale_of_pos`
  (BoundaryScale/VolumeLowerEverywhere: first-scale attainment and monotonicity, `24 I(1) ≥ 8`;
  no comparison geometry).
* the same on every C14D instance; `PartialClosedThresholdValidityV4.volume_exit_on_tail_V4C`: the
  exit on every member of every register's tail (the record's own family package).
* Consumer `exists_partialClosedThresholdValidityV4Rows_volume_V4C` (the inhabited record with
  PR10's maxima, G3, and the volume exit on every tail).
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- `w' > 0` at every register. -/
theorem ClosedRegisterV4.wPrime_pos_V4C {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
    (R : ClosedRegisterV4 D T) : 0 < closedWPrime R.later.scale := by
  have hw := R.later.w_pos
  have hΛ := R.later.Λ_pos
  unfold closedWPrime
  positivity

/-- **The volume exit on one instance**: with `I₁ = ∫₀¹ sinh²`, at every point `p` the instance's
scale satisfies `0 < v_* ≤ vol B(p, ρ(p))/ρ(p)³`. -/
theorem ClosedFamilyInstanceV4.volume_exit_V4C {K : ℕ} {A : ℝ → ℝ}
    {Wseq : ℕ → CompactCarrier.{u}}
    {gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier} {D : ClosedEarlyData}
    {T : ClosedThresholdsV4 D} (hv : PartialClosedThresholdValidityV4 K A Wseq gseq D T)
    {R : ClosedRegisterV4 D T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (F : ClosedFamilyInstanceV4 K R M δ εr Λz) (p : M.X) :
    0 < closedVStarV4 T R.later.scale ∧
      closedVStarV4 T R.later.scale ≤ (ballVolume M.gX p (F.ρ p)).toReal / F.ρ p ^ 3 := by
  have h := volume_lower_at_modified_scale_of_pos M.gX p R.wPrime_pos_V4C (F.ρ_pos p)
    (F.ρ_bounds p).2.le
  have he : closedVStarV4 T R.later.scale =
      closedWPrime R.later.scale / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) := by
    rw [closedVStarV4, hv.I₁_eq]
  rw [he]
  exact h

/-- The same on every C14D instance. -/
theorem ClosedFamilyInstanceC14DV4.volume_exit_V4C {K : ℕ} {A : ℝ → ℝ}
    {Wseq : ℕ → CompactCarrier.{u}}
    {gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier} {D : ClosedEarlyData}
    {T : ClosedThresholdsV4 D} (hv : PartialClosedThresholdValidityV4 K A Wseq gseq D T)
    {R : ClosedRegisterV4 D T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (F : ClosedFamilyInstanceC14DV4 K R M δ εr Λz) (p : M.X) :
    0 < closedVStarV4 T R.later.scale ∧
      closedVStarV4 T R.later.scale ≤ (ballVolume M.gX p (F.ρ p)).toReal / F.ρ p ^ 3 :=
  F.toC14_VAL6.volume_exit_V4C hv p

/-- **The volume exit on every tail** (the record's own family package): at every register there is
one cone error `δ` and prefix witnesses such that on every member of the register's tail a model
carries an instance of the final family whose scale meets `v_* ≤ vol B(p, ρ(p))/ρ(p)³` at every
point. -/
theorem PartialClosedThresholdValidityV4.volume_exit_on_tail_V4C {K : ℕ} {A : ℝ → ℝ}
    {Wseq : ℕ → CompactCarrier.{u}}
    {gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier} {D : ClosedEarlyData}
    {T : ClosedThresholdsV4 D} (hv : PartialClosedThresholdValidityV4 K A Wseq gseq D T)
    (hf : ∀ m, ClosedMemberFacts (Wseq m)) (R : ClosedRegisterV4 D T) :
    ∃ δ εr Λz : ℝ, ∀ m, R.later.tail ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m),
      ∃ F : ClosedFamilyInstanceV4 K R M δ εr Λz, ∀ p : M.X,
        0 < closedVStarV4 T R.later.scale ∧
          closedVStarV4 T R.later.scale ≤ (ballVolume M.gX p (F.ρ p)).toReal / F.ρ p ^ 3 := by
  obtain ⟨εrF, δ'F, ΛzF, h⟩ := hv.family hf
  obtain ⟨-, -, -, -, -, -, δ, -, -, ht⟩ := h R
  refine ⟨δ, εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
    R.later.split.β₁, ΛzF R.stage R.later.circle R.later.excl R.later.err R.later.scale
    R.later.split.b R.later.split.β₁, fun m hm => ?_⟩
  obtain ⟨M, ⟨F⟩, -⟩ := ht m hm
  exact ⟨M, F, fun p => F.volume_exit_V4C hv p⟩

/-- **Consumer: the inhabited record with the volume exit.** At the early data
`earlyDataSharedV4 K`, on every closed standing sequence, one strategy `T` at which the record
`PartialClosedThresholdValidityV4Rows` holds with PR10's maxima `N_b, c_w` (G3), and at every
register the volume exit `v_* ≤ vol B(p, ρ(p))/ρ(p)³` holds at every point of an instance of the
final family on every member of the tail. -/
theorem exists_partialClosedThresholdValidityV4Rows_volume_V4C (K : ℕ) (hK : 10 ≤ K)
    (A : ℝ → ℝ) (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T,
        ∃ δ εr Λz : ℝ, ∀ m, R.later.tail ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m),
          ∃ F : ClosedFamilyInstanceV4 K R M δ εr Λz, ∀ p : M.X,
            0 < closedVStarV4 T R.later.scale ∧
              closedVStarV4 T R.later.scale ≤ (ballVolume M.gX p (F.ρ p)).toReal / F.ρ p ^ 3 := by
  obtain ⟨T, hv, hNb, hcw, -⟩ :=
    exists_partialClosedThresholdValidityV4Rows_nbmax_V4C K hK A hA Wseq gseq hf hg
  exact ⟨T, hv, hNb, hcw,
    fun R => hv.toPartialClosedThresholdValidityV4.volume_exit_on_tail_V4C hf R⟩

end DifferentialGeometry.Geometry.Collapse

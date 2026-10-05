import DifferentialGeometry.Analysis.Calculus.Cutoff.BufferedEdgeCutoff
import DifferentialGeometry.Geometry.Metric.RetainedMarkerBindings
import DifferentialGeometry.Analysis.Calculus.ContDiff.ClosedSupportNeighborhood
import DifferentialGeometry.Analysis.InnerProductSpace.AdjustmentFactorization
import DifferentialGeometry.Analysis.ParameterSelection.ThreeStageAdjustmentChoice

/-!
# CFS25: the uniform cutoff consumer

Blueprint `master207B.tex`, CFS25 (`cor:fibration-uniform-cutoff-consumer`, lines 3522–3568).
The row composes the uniform cutoffs CFS23 (edge, `cfs23_row`) and CFS22 (slim, `cfs22_row`)
with CFS16 (`retained_marker_projected_half_buffer`), CFS18
(`exists_contDiffOn_closedSupport_adjustment`), FC32 (`starProjection_adjustmentMap_of_le`) and
the CFS20/GAF01 budget (`exists_three_stage_adjustment_choice`). Kernel statements:

* `cfs25_edge_consumer`: FC30's support, exact plateau and derivative requirements for the edge
  cutoff with `C₀ = 10⁴ (N+1)² P⁴` (independent of `Δ`) when the preceding value error is at most
  `e ρ` with `e ≤ 4κ/5` and `e ≤ 3σ/10`; on the closed support the projected perturbed input is in
  the half-tube of the ORIGINAL centre (CFS16). The full marker needed by CFS16 at every original
  core point is produced from the edge identity (no extra hypothesis).
* `cfs25_slim_consumer`: the same for the slim cutoff; here the full marker at every point of the
  threshold-`7ℓ` core is FC26 data (explicit hypothesis `hfull`).
* `cfs25_closedSupport_neighborhood`, `cfs25_edge_neighborhood`, `cfs25_slim_neighborhood`: CFS18
  then gives a smooth adjustment on an open neighbourhood of the actual image `f(X)` for any
  smoothing field on the projected tube `cfsProjectedTube`.
* `cfsUniformAxisCutoff_comp_of_factor`, `cfs25_slim_adjustment_factor`: a slim cutoff built from
  `Q₂`-coordinates factors over `π_{Q₂}`, hence so does the stage-three adjustment (FC32).
* `cfs25_parameter_choice`: CFS20 with `b_j = C₀` and `4κ/5` added to the preceding-error minimum,
  in the retained order (`C₀`, `κ` depend only on `N`, `P`).
* `starProjection_adjustmentMap_eq_zero`, `cfs25_zero_marker_of_locality`: the sufficient (ZL)
  route — every stage keeps an originally zero marker zero, so (ZM) holds.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff BigOperators

namespace GC.MetricGeometry

section Tube

variable {X H Hq : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup Hq] [NormedSpace ℝ Hq]

/-- The projected tube `{z | ∃ p ∈ A, π z ∈ B(π F(p), r(p))}` around the original centres. -/
def cfsProjectedTube (π : H →L[ℝ] Hq) (F : X → H) (A : Set X) (r : X → ℝ) : Set H :=
  {z | ∃ p ∈ A, π z ∈ ball (π (F p)) (r p)}

theorem isOpen_cfsProjectedTube (π : H →L[ℝ] Hq) (F : X → H) (A : Set X) (r : X → ℝ) :
    IsOpen (cfsProjectedTube π F A r) := by
  have h : cfsProjectedTube π F A r = ⋃ p ∈ A, π ⁻¹' ball (π (F p)) (r p) := by
    ext z
    simp [cfsProjectedTube]
  rw [h]
  exact isOpen_biUnion fun p _ => isOpen_ball.preimage π.continuous

/-- CFS18 on the actual image: if the closed support of `ψ` meets `f(X)` only at points `f p`
with `p ∈ A` and `π f(p) ∈ B(π F(p), r(p))`, the closed-support adjustment by any field `h`
smooth on `O ∩ T` is smooth on an open neighbourhood `V ⊆ O` of `f(X)`. -/
theorem cfs25_closedSupport_neighborhood (π : H →L[ℝ] Hq) (F f : X → H) (A : Set X)
    (r : X → ℝ) {O : Set H} (hO : IsOpen O) (hfO : ∀ p, f p ∈ O) {ψ : H → ℝ}
    (hψ : ContDiffOn ℝ ∞ ψ O)
    (hloc : ∀ p, f p ∈ tsupport ψ → p ∈ A ∧ π (f p) ∈ ball (π (F p)) (r p)) {h : H → H}
    [∀ z, Decidable (z ∈ cfsProjectedTube π F A r)]
    (hh : ContDiffOn ℝ ∞ h (O ∩ cfsProjectedTube π F A r)) :
    ∃ V : Set H, IsOpen V ∧ range f ⊆ V ∧ V ⊆ O ∧
      closure (Function.support ψ ∩ V) ∩ V ⊆ cfsProjectedTube π F A r ∧
      ContDiffOn ℝ ∞ ((cfsProjectedTube π F A r).piecewise (fun z => z + ψ z • h z) id) V ∧
      (∀ z ∈ V, z ∉ cfsProjectedTube π F A r → ψ z = 0) ∧
      EqOn ((cfsProjectedTube π F A r).piecewise (fun z => z + ψ z • h z) id) id
        (V \ cfsProjectedTube π F A r) := by
  have hKO : range f ⊆ O := by
    rintro _ ⟨p, rfl⟩
    exact hfO p
  have hsupp : range f ∩ (closure (Function.support ψ ∩ O) ∩ O) ⊆ cfsProjectedTube π F A r := by
    rintro _ ⟨⟨p, rfl⟩, hcl, -⟩
    have hts : f p ∈ tsupport ψ := closure_mono inter_subset_left hcl
    obtain ⟨hpA, hball⟩ := hloc p hts
    exact ⟨p, hpA, hball⟩
  obtain ⟨V, hV, hKV, hVO, hVsupp, hsmooth, hzero, hid, -⟩ :=
    DifferentialGeometry.Analysis.exists_contDiffOn_closedSupport_adjustment hO
      (isOpen_cfsProjectedTube π F A r) hKO hψ hh hsupp
  exact ⟨V, hV, hKV, hVO, hVsupp, hsmooth, hzero, hid⟩

end Tube

section Consumers

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {I : Type*} [Fintype I] {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  {Hq : Type*} [NormedAddCommGroup Hq] [NormedSpace ℝ Hq]

/-- CFS25, edge family: the CFS23 cutoff meets FC30's requirements with `C₀ = 10⁴ (N+1)² P⁴`
when the preceding value error is at most `e ρ`, `e ≤ 4κ/5`, `e ≤ 3σ/10`; on its closed support
the original point is in the threshold-`7Δ` core and the projected input `π f(p)` lies in the
half-tube of the original centre `π F(p)` of radius `σ ρ(sel p)` (CFS16). -/
theorem cfs25_edge_consumer {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (hχmono : Monotone χ)
    {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ) (u : ∀ i, H →L[ℝ] E i)
    (v : I → H →L[ℝ] ℝ) (xρ : H →L[ℝ] ℝ) (x1 : H →L[ℝ] E') (x2 : H →L[ℝ] ℝ)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) (hxρ : ‖xρ‖ ≤ 1) (hx1 : ‖x1‖ ≤ 1)
    (hx2 : ‖x2‖ ≤ 1) {X : Type*} {Δ : ℝ} (hΔ : 1 ≤ Δ) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (U : I → Set X) (η : ∀ i, X → E i) (ζ : I → X → ℝ)
    (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1) (F f : X → H) (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i ∧ ‖η i p‖ ≤ 9 * Δ)
    (π : H →L[ℝ] Hq) (hπ : ‖π‖ ≤ 1) (m : I → Hq →L[ℝ] ℝ) (hm : ∀ i z, m i (π z) = v i z)
    (sel : X → X) (hsel : ∀ p, π (F (sel p)) = π (F p)) {σ e : ℝ} (hσ : 0 < σ)
    (he4 : e ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5) (he3 : e ≤ 3 * σ / 10)
    (herr : ∀ p, ‖f p - F p‖ ≤ e * ρ p)
    (hZM : ∀ i p, ζ i p = 0 → |v i (f p)| ≤ R i / 32)
    (t : X → ℝ) (h : ℝ → ℝ) (hhI : ∀ s, h s ∈ Icc (0 : ℝ) 1)
    (hhg : ∀ s, 3 / 10 ≤ s → h s = 1 - cfsRamp χ 8 9 s) (hxρF : ∀ p, xρ (F p) = ρ p)
    (hedgeblock : ∀ p, (∃ i, p ∈ U i) →
      ‖x1 (F p)‖ = ρ p * t p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)) ∧
      x2 (F p) = ρ p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)))
    (hedge : ∀ i p, p ∈ U i → ‖η i p‖ < 8 * Δ → ζ i p = 1 - cfsRamp χ 8 9 (t p / Δ)) :
    ContDiffOn ℝ ∞ (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) {z | 0 < xρ z} ∧
      (∀ z, cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ i, p ∈ U i ∧ ‖η i p‖ < 6 * Δ ∧ t p < 6 * Δ) →
        cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 (f p) = 1) ∧
      (∀ p, ∀ s ∈ Icc (0 : ℝ) 1, 0 < xρ ((1 - s) • F p + s • f p) ∧
        ‖fderiv ℝ (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) ((1 - s) • F p + s • f p)‖ ≤
          10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p) ∧
      (∀ p, f p ∈ tsupport (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) →
        (∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * Δ ∧ t p < 7 * Δ) ∧
        (3 / 5 : ℝ) * (σ * ρ p) ≤ σ * ρ (sel p) ∧ σ * ρ (sel p) ≤ (5 / 3 : ℝ) * (σ * ρ p) ∧
        ‖π (f p) - π (F p)‖ ≤ σ * ρ (sel p) / 2 ∧
        ball (π (f p)) (σ * ρ (sel p) / 2) ⊆ ball (π (F p)) (σ * ρ (sel p)) ∧
        segment ℝ (π (F p)) (π (f p)) ⊆ ball (π (F p)) (σ * ρ (sel p))) := by
  have hpert : ∀ p, ‖f p - F p‖ ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 * ρ p :=
    fun p => (herr p).trans (mul_le_mul_of_nonneg_right he4 (hρ p).le)
  obtain ⟨hsmooth, hval, hplat, hsupp, hseg⟩ := cfs23_row R u v xρ x1 x2 hχ hχ0 hχ1 hχI hχmono
    hP1 hP N hu hv hxρ hx1 hx2 hΔ hR ρ hρ U η ζ hζI F f hζU hblock hcount hcomp hpert hZM t h
    hhI hhg hxρF hedgeblock hedge
  refine ⟨hsmooth, hval, hplat, hseg, fun p hp => ?_⟩
  obtain ⟨i, hpU, hη7, ht7⟩ := hsupp p hp
  have hΔ0 : 0 < Δ := by linarith
  have hζ1 : ζ i p = 1 := by
    rw [hedge i p hpU (by linarith), cfsRamp_eq_zero hχ0 (by norm_num) ?_, sub_zero]
    rw [div_le_iff₀ hΔ0]
    linarith
  have hfull : m i (π (F p)) = R i := by
    rw [hm, (hblock i p).2, hζ1, mul_one]
  have hsupport : ∀ j q, 0 < m j (π (F q)) → 3 * R j / 4 ≤ ρ q ∧ ρ q ≤ 5 * R j / 4 := by
    intro j q hq
    rw [hm, (hblock j q).2] at hq
    have hζq : 0 < ζ j q := pos_of_mul_pos_right hq (hR j).le
    obtain ⟨h1, h2, -⟩ := hcomp j q hζq
    constructor <;> linarith
  have hbuf := retained_marker_projected_half_buffer π hπ F f ρ (fun j y => m j y) R hR
    hsupport p (sel p) (hsel p).symm i hfull σ e hσ he3 (herr p)
  exact ⟨⟨i, hpU, hη7, ht7⟩, hbuf.2.1, hbuf.2.2.1, hbuf.2.2.2.1, hbuf.2.2.2.2.1,
    hbuf.2.2.2.2.2⟩

/-- CFS25 + CFS18, edge family: a smooth adjustment on an open neighbourhood of `f(X)` inside
`O = {x_ρ > 0}`, for any smoothing field `k` smooth on `O ∩ T`, `T` the projected tube around
the original threshold-`7Δ` centres with radii `σ ρ(sel p)`. -/
theorem cfs25_edge_neighborhood {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (hχmono : Monotone χ)
    {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ) (u : ∀ i, H →L[ℝ] E i)
    (v : I → H →L[ℝ] ℝ) (xρ : H →L[ℝ] ℝ) (x1 : H →L[ℝ] E') (x2 : H →L[ℝ] ℝ)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) (hxρ : ‖xρ‖ ≤ 1) (hx1 : ‖x1‖ ≤ 1)
    (hx2 : ‖x2‖ ≤ 1) {X : Type*} {Δ : ℝ} (hΔ : 1 ≤ Δ) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (U : I → Set X) (η : ∀ i, X → E i) (ζ : I → X → ℝ)
    (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1) (F f : X → H) (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i ∧ ‖η i p‖ ≤ 9 * Δ)
    (π : H →L[ℝ] Hq) (hπ : ‖π‖ ≤ 1) (m : I → Hq →L[ℝ] ℝ) (hm : ∀ i z, m i (π z) = v i z)
    (sel : X → X) (hsel : ∀ p, π (F (sel p)) = π (F p)) {σ e : ℝ} (hσ : 0 < σ)
    (he4 : e ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5) (he3 : e ≤ 3 * σ / 10)
    (herr : ∀ p, ‖f p - F p‖ ≤ e * ρ p)
    (hZM : ∀ i p, ζ i p = 0 → |v i (f p)| ≤ R i / 32)
    (t : X → ℝ) (h : ℝ → ℝ) (hhI : ∀ s, h s ∈ Icc (0 : ℝ) 1)
    (hhg : ∀ s, 3 / 10 ≤ s → h s = 1 - cfsRamp χ 8 9 s) (hxρF : ∀ p, xρ (F p) = ρ p)
    (hedgeblock : ∀ p, (∃ i, p ∈ U i) →
      ‖x1 (F p)‖ = ρ p * t p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)) ∧
      x2 (F p) = ρ p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)))
    (hedge : ∀ i p, p ∈ U i → ‖η i p‖ < 8 * Δ → ζ i p = 1 - cfsRamp χ 8 9 (t p / Δ))
    {k : H → H}
    [∀ z, Decidable (z ∈ cfsProjectedTube π F {p | ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * Δ ∧ t p < 7 * Δ}
      (fun p => σ * ρ (sel p)))]
    (hk : ContDiffOn ℝ ∞ k ({z | 0 < xρ z} ∩ cfsProjectedTube π F
      {p | ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * Δ ∧ t p < 7 * Δ} (fun p => σ * ρ (sel p)))) :
    ∃ V : Set H, IsOpen V ∧ range f ⊆ V ∧ V ⊆ {z | 0 < xρ z} ∧
      closure (Function.support (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) ∩ V) ∩ V ⊆
        cfsProjectedTube π F {p | ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * Δ ∧ t p < 7 * Δ}
          (fun p => σ * ρ (sel p)) ∧
      ContDiffOn ℝ ∞ ((cfsProjectedTube π F {p | ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * Δ ∧ t p < 7 * Δ}
        (fun p => σ * ρ (sel p))).piecewise
          (fun z => z + cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 z • k z) id) V ∧
      (∀ z ∈ V, z ∉ cfsProjectedTube π F {p | ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * Δ ∧ t p < 7 * Δ}
        (fun p => σ * ρ (sel p)) → cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 z = 0) ∧
      EqOn ((cfsProjectedTube π F {p | ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * Δ ∧ t p < 7 * Δ}
        (fun p => σ * ρ (sel p))).piecewise
          (fun z => z + cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 z • k z) id) id
        (V \ cfsProjectedTube π F {p | ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * Δ ∧ t p < 7 * Δ}
          (fun p => σ * ρ (sel p))) := by
  obtain ⟨hsmooth, -, -, hseg, hloc⟩ := cfs25_edge_consumer hχ hχ0 hχ1 hχI hχmono hP1 hP N u v
    xρ x1 x2 hu hv hxρ hx1 hx2 hΔ R hR ρ hρ U η ζ hζI F f hζU hblock hcount hcomp π hπ m hm sel
    hsel hσ he4 he3 herr hZM t h hhI hhg hxρF hedgeblock hedge
  have hfO : ∀ p, f p ∈ {z | 0 < xρ z} := fun p => by
    simpa using (hseg p 1 ⟨zero_le_one, le_rfl⟩).1
  refine cfs25_closedSupport_neighborhood π F f _ _ (isOpen_lt continuous_const xρ.continuous)
    hfO hsmooth (fun p hp => ?_) hk
  obtain ⟨hcore, -, -, hd, -, -⟩ := hloc p hp
  have hr : 0 < σ * ρ (sel p) := mul_pos hσ (hρ (sel p))
  refine ⟨hcore, ?_⟩
  rw [mem_ball, dist_eq_norm]
  linarith

/-- CFS25, slim family: the CFS22 cutoff meets FC30's requirements with `C₀` when the preceding
value error is at most `e ρ`, `e ≤ 4κ/5`, `e ≤ 3σ/10`; given FC26's full marker at every point of
the threshold-`7ℓ` core (`hfull`), the projected input on the closed support lies in the
half-tube of the original centre (CFS16). -/
theorem cfs25_slim_consumer {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) {P : ℝ} (hP1 : 1 ≤ P)
    (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ) (u : ∀ i, H →L[ℝ] E i) (v : I → H →L[ℝ] ℝ)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) {X : Type*} {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (R : I → ℝ)
    (hR : ∀ i, 0 < R i) (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (U : I → Set X) (η : ∀ i, X → E i)
    (ζ : I → X → ℝ) (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1) (F f : X → H)
    (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i ∧ ‖η i p‖ ≤ 9 * ℓ)
    (hplateau : ∀ i p, p ∈ U i → ‖η i p‖ < 6 * ℓ → ζ i p = 1)
    (π : H →L[ℝ] Hq) (hπ : ‖π‖ ≤ 1) (m : I → Hq →L[ℝ] ℝ) (hm : ∀ i z, m i (π z) = v i z)
    (hfull : ∀ p, (∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * ℓ) → ∃ j, v j (F p) = R j)
    (sel : X → X) (hsel : ∀ p, π (F (sel p)) = π (F p)) {σ e : ℝ} (hσ : 0 < σ)
    (he4 : e ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5) (he3 : e ≤ 3 * σ / 10)
    (herr : ∀ p, ‖f p - F p‖ ≤ e * ρ p)
    (hZM : ∀ i p, ζ i p = 0 → |v i (f p)| ≤ R i / 32) :
    ContDiff ℝ ∞ (cfsUniformAxisCutoff χ ℓ R u v) ∧
      (∀ z, cfsUniformAxisCutoff χ ℓ R u v z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ i, p ∈ U i ∧ ‖η i p‖ < 6 * ℓ) → cfsUniformAxisCutoff χ ℓ R u v (f p) = 1) ∧
      (∀ p, ∀ s ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (cfsUniformAxisCutoff χ ℓ R u v) ((1 - s) • F p + s • f p)‖ ≤
          10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p) ∧
      (∀ p, f p ∈ tsupport (cfsUniformAxisCutoff χ ℓ R u v) →
        (∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * ℓ) ∧
        (3 / 5 : ℝ) * (σ * ρ p) ≤ σ * ρ (sel p) ∧ σ * ρ (sel p) ≤ (5 / 3 : ℝ) * (σ * ρ p) ∧
        ‖π (f p) - π (F p)‖ ≤ σ * ρ (sel p) / 2 ∧
        ball (π (f p)) (σ * ρ (sel p) / 2) ⊆ ball (π (F p)) (σ * ρ (sel p)) ∧
        segment ℝ (π (F p)) (π (f p)) ⊆ ball (π (F p)) (σ * ρ (sel p))) := by
  have hpert : ∀ p, ‖f p - F p‖ ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 * ρ p :=
    fun p => (herr p).trans (mul_le_mul_of_nonneg_right he4 (hρ p).le)
  obtain ⟨hsmooth, hval, hplat, hsupp, hseg⟩ := cfs22_row hχ hχ0 hχ1 hχI hP1 hP N u v hu hv hℓ
    R hR ρ hρ U η ζ hζI F f hζU hblock hcount hcomp hplateau hpert hZM
  refine ⟨hsmooth, hval, hplat, hseg, fun p hp => ?_⟩
  have hcore := hsupp p hp
  obtain ⟨j, hj⟩ := hfull p hcore
  have hfullj : m j (π (F p)) = R j := by rw [hm, hj]
  have hsupport : ∀ i q, 0 < m i (π (F q)) → 3 * R i / 4 ≤ ρ q ∧ ρ q ≤ 5 * R i / 4 := by
    intro i q hq
    rw [hm, (hblock i q).2] at hq
    have hζq : 0 < ζ i q := pos_of_mul_pos_right hq (hR i).le
    obtain ⟨h1, h2, -⟩ := hcomp i q hζq
    constructor <;> linarith
  have hbuf := retained_marker_projected_half_buffer π hπ F f ρ (fun i y => m i y) R hR
    hsupport p (sel p) (hsel p).symm j hfullj σ e hσ he3 (herr p)
  exact ⟨hcore, hbuf.2.1, hbuf.2.2.1, hbuf.2.2.2.1, hbuf.2.2.2.2.1, hbuf.2.2.2.2.2⟩

/-- CFS25 + CFS18, slim family: a smooth adjustment on an open neighbourhood of `f(X)` for any
smoothing field `k` smooth on the projected tube around the threshold-`7ℓ` centres. -/
theorem cfs25_slim_neighborhood {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) {P : ℝ} (hP1 : 1 ≤ P)
    (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ) (u : ∀ i, H →L[ℝ] E i) (v : I → H →L[ℝ] ℝ)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) {X : Type*} {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (R : I → ℝ)
    (hR : ∀ i, 0 < R i) (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (U : I → Set X) (η : ∀ i, X → E i)
    (ζ : I → X → ℝ) (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1) (F f : X → H)
    (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i ∧ ‖η i p‖ ≤ 9 * ℓ)
    (hplateau : ∀ i p, p ∈ U i → ‖η i p‖ < 6 * ℓ → ζ i p = 1)
    (π : H →L[ℝ] Hq) (hπ : ‖π‖ ≤ 1) (m : I → Hq →L[ℝ] ℝ) (hm : ∀ i z, m i (π z) = v i z)
    (hfull : ∀ p, (∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * ℓ) → ∃ j, v j (F p) = R j)
    (sel : X → X) (hsel : ∀ p, π (F (sel p)) = π (F p)) {σ e : ℝ} (hσ : 0 < σ)
    (he4 : e ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5) (he3 : e ≤ 3 * σ / 10)
    (herr : ∀ p, ‖f p - F p‖ ≤ e * ρ p)
    (hZM : ∀ i p, ζ i p = 0 → |v i (f p)| ≤ R i / 32) {k : H → H}
    [∀ z, Decidable (z ∈ cfsProjectedTube π F {p | ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * ℓ}
      (fun p => σ * ρ (sel p)))]
    (hk : ContDiffOn ℝ ∞ k (univ ∩ cfsProjectedTube π F {p | ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * ℓ}
      (fun p => σ * ρ (sel p)))) :
    ∃ V : Set H, IsOpen V ∧ range f ⊆ V ∧ V ⊆ univ ∧
      closure (Function.support (cfsUniformAxisCutoff χ ℓ R u v) ∩ V) ∩ V ⊆
        cfsProjectedTube π F {p | ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * ℓ} (fun p => σ * ρ (sel p)) ∧
      ContDiffOn ℝ ∞ ((cfsProjectedTube π F {p | ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * ℓ}
        (fun p => σ * ρ (sel p))).piecewise
          (fun z => z + cfsUniformAxisCutoff χ ℓ R u v z • k z) id) V ∧
      (∀ z ∈ V, z ∉ cfsProjectedTube π F {p | ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * ℓ}
        (fun p => σ * ρ (sel p)) → cfsUniformAxisCutoff χ ℓ R u v z = 0) ∧
      EqOn ((cfsProjectedTube π F {p | ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * ℓ}
        (fun p => σ * ρ (sel p))).piecewise
          (fun z => z + cfsUniformAxisCutoff χ ℓ R u v z • k z) id) id
        (V \ cfsProjectedTube π F {p | ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * ℓ}
          (fun p => σ * ρ (sel p))) := by
  obtain ⟨hsmooth, -, -, -, hloc⟩ := cfs25_slim_consumer hχ hχ0 hχ1 hχI hP1 hP N u v hu hv hℓ R
    hR ρ hρ U η ζ hζI F f hζU hblock hcount hcomp hplateau π hπ m hm hfull sel hsel hσ he4 he3
    herr hZM
  refine cfs25_closedSupport_neighborhood π F f _ _ isOpen_univ (fun _ => mem_univ _)
    hsmooth.contDiffOn (fun p hp => ?_) hk
  obtain ⟨hcore, -, -, hd, -, -⟩ := hloc p hp
  have hr : 0 < σ * ρ (sel p) := mul_pos hσ (hρ (sel p))
  refine ⟨hcore, ?_⟩
  rw [mem_ball, dist_eq_norm]
  linarith

end Consumers

section Factorization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {I : Type*} [Fintype I] {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]

/-- A slim cutoff built from coordinates that factor through `π` is unchanged by precomposition
with `π`. -/
theorem cfsUniformAxisCutoff_comp_of_factor (χ : ℝ → ℝ) (ℓ : ℝ) (R : I → ℝ)
    (u : ∀ i, H →L[ℝ] E i) (v : I → H →L[ℝ] ℝ) (π : H → H)
    (hu : ∀ i z, u i (π z) = u i z) (hv : ∀ i z, v i (π z) = v i z) :
    cfsUniformAxisCutoff χ ℓ R u v ∘ π = cfsUniformAxisCutoff χ ℓ R u v := by
  funext z
  simp only [Function.comp_apply, cfsUniformAxisCutoff, cfsAxisGate, hu, hv]

/-- CFS25 (FC32 clause): when the slim blocks are `Q₂`-coordinates, the stage-three adjustment by
the slim cutoff factors over `π_{Q₂}` for any `Q₃ ≤ Q₂`. -/
theorem cfs25_slim_adjustment_factor (Q₃ Q₂ : Submodule ℝ H) [Q₃.HasOrthogonalProjection]
    [Q₂.HasOrthogonalProjection] (h32 : Q₃ ≤ Q₂) {Pm : H → H} (hPm : ∀ z, Pm z ∈ Q₃)
    (χ : ℝ → ℝ) (ℓ : ℝ) (R : I → ℝ) (u : ∀ i, H →L[ℝ] E i) (v : I → H →L[ℝ] ℝ)
    (hu : ∀ i z, u i (Q₂.starProjection z) = u i z)
    (hv : ∀ i z, v i (Q₂.starProjection z) = v i z) (x : H) :
    Q₂.starProjection
        (DifferentialGeometry.Analysis.adjustmentMap Q₃ Pm (cfsUniformAxisCutoff χ ℓ R u v) x) =
      DifferentialGeometry.Analysis.adjustmentMap Q₃ Pm (cfsUniformAxisCutoff χ ℓ R u v)
        (Q₂.starProjection x) := by
  have hfac := cfsUniformAxisCutoff_comp_of_factor χ ℓ R u v Q₂.starProjection hu hv
  have h := DifferentialGeometry.Analysis.starProjection_adjustmentMap_of_le Q₃ h32 hPm
    (cfsUniformAxisCutoff χ ℓ R u v) x
  rw [hfac] at h
  exact h

/-- One adjustment stage keeps a zero `V`-coordinate: either `V ≤ Q` and the smoothing output has
zero `V`-coordinate wherever the cutoff is nonzero (the CFS24 conclusion under (ZL)), or `V ≤ Q⊥`
(FC32: a coordinate outside the adjusted summand is unchanged). -/
theorem starProjection_adjustmentMap_eq_zero (Q V : Submodule ℝ H) [Q.HasOrthogonalProjection]
    [Qᗮ.HasOrthogonalProjection] [V.HasOrthogonalProjection] {Pm : H → H}
    (hPm : ∀ z, Pm z ∈ Q) (ψ : H → ℝ) {z : H} (hz : V.starProjection z = 0)
    (hcase : (V ≤ Q ∧ (ψ z ≠ 0 → V.starProjection (Pm (Q.starProjection z)) = 0)) ∨
      V ≤ Qᗮ) :
    V.starProjection (DifferentialGeometry.Analysis.adjustmentMap Q Pm ψ z) = 0 := by
  rcases hcase with ⟨hVQ, hP0⟩ | hVQ
  · have hVQz : V.starProjection (Q.starProjection z) = V.starProjection z := by
      have := congrArg (fun L : H →L[ℝ] H => L z)
        (Submodule.starProjection_comp_starProjection_of_le hVQ)
      simpa using this
    rw [DifferentialGeometry.Analysis.adjustmentMap_apply, map_add, map_smul, map_sub, hVQz, hz,
      sub_zero, zero_add]
    by_cases hψ : ψ z = 0
    · rw [hψ, zero_smul]
    · rw [hP0 hψ, smul_zero]
  · have hVQ' : ∀ y, V.starProjection (Qᗮ.starProjection y) = V.starProjection y := fun y => by
      have := congrArg (fun L : H →L[ℝ] H => L y)
        (Submodule.starProjection_comp_starProjection_of_le hVQ)
      simpa using this
    rw [← hVQ', DifferentialGeometry.Analysis.starProjection_orthogonal_adjustmentMap Q hPm ψ z,
      hVQ', hz]

/-- CFS25, the sufficient (ZL) route: along stages `g (k+1) = Ψ_k ∘ g k` (FC32 adjustments), if at
every stage and every point with zero `V`-coordinate the alternative of
`starProjection_adjustmentMap_eq_zero` holds (CFS24 under (ZL), or `V ⊥ Q_k`), an originally zero
`V`-coordinate stays zero; for a marker `J` factoring through `V` this gives (ZM). -/
theorem cfs25_zero_marker_of_locality (V : Submodule ℝ H) [V.HasOrthogonalProjection]
    (Q : ℕ → Submodule ℝ H) [∀ k, (Q k).HasOrthogonalProjection]
    [∀ k, (Q k)ᗮ.HasOrthogonalProjection] (Pm : ℕ → H → H) (hPm : ∀ k z, Pm k z ∈ Q k)
    (ψ : ℕ → H → ℝ) {X : Type*} (g : ℕ → X → H)
    (hg : ∀ k p, g (k + 1) p = DifferentialGeometry.Analysis.adjustmentMap (Q k) (Pm k) (ψ k)
      (g k p))
    (hZL : ∀ k p, V.starProjection (g k p) = 0 →
      (V ≤ Q k ∧ (ψ k (g k p) ≠ 0 →
        V.starProjection (Pm k ((Q k).starProjection (g k p))) = 0)) ∨ V ≤ (Q k)ᗮ)
    (J : H →L[ℝ] ℝ) (hJ : ∀ z, J z = J (V.starProjection z)) {r : ℝ} (hr : 0 ≤ r) (p : X)
    (h0 : V.starProjection (g 0 p) = 0) :
    ∀ k, V.starProjection (g k p) = 0 ∧ |J (g k p)| ≤ r / 32 := by
  have hzero : ∀ k, V.starProjection (g k p) = 0 := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      rw [hg k p]
      exact starProjection_adjustmentMap_eq_zero (Q k) V (hPm k) (ψ k) ih (hZL k p ih)
  intro k
  refine ⟨hzero k, ?_⟩
  rw [hJ, hzero k, map_zero, abs_zero]
  positivity

end Factorization

section Parameters

open DifferentialGeometry.Analysis in
/-- CFS25 numerical clause: CFS20 with the cutoff constant `b_j = C₀ = 10⁴ (N+1)² P⁴` and
`4κ/5`, `κ = 1/(1000 (N+1) P²)`, added to the preceding-error minimum, in the retained order
(GAF01 kernel). `C₀` and `κ` depend only on `N`, `P`, so they are fixed before every `Γ_j`, `Σ_j`
and `Δ`. The preceding error of stages two and three is then at most `4κ/5` and `3 Σ_j/10`, as
`cfs25_edge_consumer` / `cfs25_slim_consumer` require. -/
theorem cfs25_parameter_choice (Ξ : Fin 3 → ℝ → ℝ) (hΞpos : ∀ j Γ, 0 < Γ → 0 < Ξ j Γ)
    (hΞ : ∀ j, Tendsto (Ξ j) (𝓝[>] 0) (𝓝 0)) {cadj L₀ Ω P : ℝ} (N : ℕ) (C : Fin 3 → ℝ)
    (hcadj : 0 < cadj) (hP1 : 1 ≤ P) (hL : 0 ≤ L₀) (hΩ : 1 ≤ Ω) (hC : ∀ j, 0 < C j) :
    ∃ c Γ S : Fin 3 → ℝ,
      (c 0 ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 ∧ c 0 ≤ 3 * S 1 / 10) ∧
      (c 1 ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 ∧ c 1 ≤ 3 * S 2 / 10) ∧
      ∀ j, 0 < c j ∧ c j ≤ 1 ∧ 0 < Γ j ∧ 0 < S j ∧ S j < 1 / 2 ∧
        ∀ E H ν σ : ℝ, 0 ≤ E →
          E ≤ min (3 * S j / 10) (min (min (c j / (16 * (1 + 10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4) *
            (1 + L₀))) ((1 / 2) / (8 * (1 + L₀)))) 1) → 0 ≤ H →
          H ≤ min (3 * S j / 10) (min (min (c j / (16 * (1 + 10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4) *
            (1 + L₀))) ((1 / 2) / (8 * (1 + L₀)))) 1) → ν ≤ Γ j → σ ≤ 1 / 2 →
          E + ((5 / 3 : ℝ) * Ξ j (Γ j) * σ + (1 + Ξ j (Γ j)) * E) < c j ∧
          ((5 / 3 : ℝ) * Ξ j (Γ j) * σ + (1 + Ξ j (Γ j)) * E) *
              (10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4) * (L₀ + H) +
            Ξ j (Γ j) * (L₀ + H) + ν + 2 * H < c j ∧
          Ξ j (Γ j) * (L₀ + H) + H < 1 / 2 := by
  obtain ⟨hκ, -, -⟩ := cfs_kappa_facts hP1 N
  have hb : (0 : ℝ) ≤ 10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 := by positivity
  obtain ⟨c, Γ, S, e, h⟩ := exists_three_stage_adjustment_choice Ξ hΞpos hΞ C hcadj hb hκ hL hΩ hC
  obtain ⟨-, ⟨-, hc1t, hc1k, -, -⟩, ⟨-, hc0t, hc0k, -, -⟩, hstage⟩ := h
  refine ⟨c, Γ, S, ⟨hc0k, hc0t.trans (min_le_left _ _)⟩, ⟨hc1k, hc1t.trans (min_le_left _ _)⟩,
    fun j => ?_⟩
  obtain ⟨⟨hcj, hcj1, hΓj, -, -, -, -, hSj, hSj2, -⟩, hbud⟩ := hstage j
  exact ⟨hcj, hcj1, hΓj, hSj, hSj2, fun E H ν σ hE hEt hH hHt hν hσ =>
    hbud E H ν σ hE hEt hH hHt hν hσ⟩

end Parameters

end GC.MetricGeometry

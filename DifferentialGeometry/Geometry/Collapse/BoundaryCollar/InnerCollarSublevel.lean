import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.InnerCollarHeight
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarHeightApproximation

/-!
# The closed inner collar cut by a level of the smoothed height is `T² × [a, 90]` (F-e, E6)

Row E6 (BCP01.c, blueprint 207B:8146–8153) for a cusp embedding `e : CuspEmbedding W g K δ X`
with `K ≥ 1`, `ζ = z ∘ e⁻¹` the collar height.

* `CuspEmbedding.exists_innerCollar_height` (E6(i)): for every `ε > 0` there are a smooth `η`
  satisfying the Z contract on `2 ≤ z ≤ 98` (as in `exists_smooth_height_C2`) and a smooth `F` on
  `W` with `F = a` on `X`, `F = η` on `2 ≤ z ≤ 95`, regular on `{F ≤ 90}`, with
  `∂W ∩ {F ≤ 90} ⊆ X` and `{F ≤ 90} = e {z ≤ 2 ∨ (z ≤ 98 ∧ η ≤ 90)}`.
* `CuspEmbedding.exists_innerCollar_diffeomorph_torus_Icc` (E6): this inner collar is a compact
  smooth manifold with boundary `X ∪ {F = 90}`, diffeomorphic as a pair to
  `(T² × [a, 90], T² × {a})` with `F` the second coordinate (E6 kernel
  `CuspEmbedding.exists_sublevel_diffeomorph_torus_Icc`).

Construction of `F` (no smoothing of `z` is needed: every ingredient is smooth on `W`):
`ρ`, `V` a defining function of `∂W` and an inward field with `dρ(V) = 1` near `∂W`
(`CompactCarrier.exists_boundary_definingFunction`); `dz(V) ≥ m > 0` on a uniform collar
`z ≤ s₀` inside that neighbourhood (`mfderiv_height_pos_of_mem`, `exists_collar_subset`);
`ρ ≥ 2τ₂` on `s₀ ≤ z ≤ 98`, `ρ < τ₁` on `z ≤ σ`; `η` the `C²` approximation of `ζ` on
`σ ≤ z ≤ 98` (`exists_smooth_approx_C2_on_compact`) with `|dη(V) - dz(V)| < m`;
`F_mid = η + φ(ρ) (ρ - c - η)` (`φ = 1` below `τ₁`, `0` above `τ₂`), regular along `V` on the
transition (`mfderiv_cutoffBlend_pos`); `F = F_mid + Θ (94 - F_mid)`, `Θ = (1 - φ(ρ)) ψ(η)` on
`e (z < 98)`, `F = 94` elsewhere — the two pieces agree on `97.5 < z < 98`, and `e (z < 98)` is
open including height `0` (B-5a's `CuspEmbedding.isOpen_image`, built on
`CuspEmbedding.image_mem_nhds_of_height_zero`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

theorem cusp_mem_cuspDomain_of_le {p : CuspHalfSpace} {b : ℝ} (hb : b < cuspDepth)
    (hp : p.2.val 0 ≤ b) : p ∈ cuspDomain :=
  hp.trans_lt hb

theorem cusp_eq_halfZero_of_height_eq_zero {p : CuspHalfSpace} (hp : p.2.val 0 = 0) :
    p = (p.1, halfZero) := by
  refine Prod.ext rfl ?_
  rw [← halfSpaceOneLift_val_zero_self p.2, hp]
  apply Subtype.ext
  ext i
  fin_cases i
  simp [halfSpaceOneLift_val_zero, halfZero, halfPoint]


/-! ### The cutoffs and the height function of the inner collar -/

/-- The lower cutoff of the inner collar: `1` below `τ₁`, `0` above `τ₂`. -/
def innerCollarCutoff (τ₁ τ₂ t : ℝ) : ℝ := Real.smoothTransition ((τ₂ - t) / (τ₂ - τ₁))

/-- The upper cutoff of the inner collar: `0` below `96`, `1` above `97`. -/
def innerCollarTopCutoff (t : ℝ) : ℝ := Real.smoothTransition (t - 96)

theorem innerCollarCutoff_of_le {τ₁ τ₂ t : ℝ} (h : τ₁ < τ₂) (ht : t ≤ τ₁) :
    innerCollarCutoff τ₁ τ₂ t = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (sub_pos.mpr h)]; linarith)

theorem innerCollarCutoff_of_ge {τ₁ τ₂ t : ℝ} (h : τ₁ < τ₂) (ht : τ₂ ≤ t) :
    innerCollarCutoff τ₁ τ₂ t = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.mpr h).le)

theorem innerCollarCutoff_mem (τ₁ τ₂ t : ℝ) :
    0 ≤ innerCollarCutoff τ₁ τ₂ t ∧ innerCollarCutoff τ₁ τ₂ t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem antitone_innerCollarCutoff {τ₁ τ₂ : ℝ} (h : τ₁ < τ₂) :
    Antitone (innerCollarCutoff τ₁ τ₂) := fun a b hab =>
  Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) (sub_pos.mpr h).le)

theorem contDiff_innerCollarCutoff (τ₁ τ₂ : ℝ) : ContDiff ℝ ∞ (innerCollarCutoff τ₁ τ₂) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

theorem innerCollarTopCutoff_of_le {t : ℝ} (ht : t ≤ 96) : innerCollarTopCutoff t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem innerCollarTopCutoff_of_ge {t : ℝ} (ht : 97 ≤ t) : innerCollarTopCutoff t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem innerCollarTopCutoff_mem (t : ℝ) :
    0 ≤ innerCollarTopCutoff t ∧ innerCollarTopCutoff t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem contDiff_innerCollarTopCutoff : ContDiff ℝ ∞ innerCollarTopCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

section Generic

variable {M : Type*}

/-- The blend of `η` with `ρ - c` through the lower cutoff of `ρ`. -/
def innerCollarBlend (ρ η : M → ℝ) (τ₁ τ₂ c : ℝ) (y : M) : ℝ :=
  η y + innerCollarCutoff τ₁ τ₂ (ρ y) * (ρ y - c - η y)

/-- The height function of the inner collar: on `O` the blend, pushed to `94` by the upper
cutoff; `94` off `O`. -/
def innerCollarLevelFun (O : Set M) (ρ η : M → ℝ) (τ₁ τ₂ c : ℝ) (y : M) : ℝ :=
  open Classical in
  if y ∈ O then innerCollarBlend ρ η τ₁ τ₂ c y +
    (1 - innerCollarCutoff τ₁ τ₂ (ρ y)) * innerCollarTopCutoff (η y) *
      (94 - innerCollarBlend ρ η τ₁ τ₂ c y)
  else 94

variable {O : Set M} {ρ η : M → ℝ} {τ₁ τ₂ c : ℝ} {y : M}

theorem innerCollarBlend_of_cutoff_one (h : innerCollarCutoff τ₁ τ₂ (ρ y) = 1) :
    innerCollarBlend ρ η τ₁ τ₂ c y = ρ y - c := by
  rw [innerCollarBlend, h]
  ring

theorem innerCollarBlend_of_cutoff_zero (h : innerCollarCutoff τ₁ τ₂ (ρ y) = 0) :
    innerCollarBlend ρ η τ₁ τ₂ c y = η y := by
  rw [innerCollarBlend, h, zero_mul, add_zero]

theorem innerCollarLevelFun_of_mem (hy : y ∈ O) :
    innerCollarLevelFun O ρ η τ₁ τ₂ c y = innerCollarBlend ρ η τ₁ τ₂ c y +
      (1 - innerCollarCutoff τ₁ τ₂ (ρ y)) * innerCollarTopCutoff (η y) *
        (94 - innerCollarBlend ρ η τ₁ τ₂ c y) := by
  simp [innerCollarLevelFun, hy]

theorem innerCollarLevelFun_of_notMem (hy : y ∉ O) : innerCollarLevelFun O ρ η τ₁ τ₂ c y = 94 := by
  simp [innerCollarLevelFun, hy]

theorem innerCollarLevelFun_of_mem_of_factor_zero (hy : y ∈ O)
    (h : (1 - innerCollarCutoff τ₁ τ₂ (ρ y)) * innerCollarTopCutoff (η y) = 0) :
    innerCollarLevelFun O ρ η τ₁ τ₂ c y = innerCollarBlend ρ η τ₁ τ₂ c y := by
  rw [innerCollarLevelFun_of_mem hy, h, zero_mul, add_zero]

theorem innerCollarLevelFun_of_mem_of_top (hy : y ∈ O) (h0 : innerCollarCutoff τ₁ τ₂ (ρ y) = 0)
    (h1 : innerCollarTopCutoff (η y) = 1) : innerCollarLevelFun O ρ η τ₁ τ₂ c y = 94 := by
  rw [innerCollarLevelFun_of_mem hy, h0, h1]
  ring

end Generic

/-! ### The inner collar height on a cusp collar -/

section Cusp

variable (e : CuspEmbedding W g K δ X) {O : Set W.Carrier} {ρ η : W.Carrier → ℝ}
  {s₀ σ τ₁ τ₂ c : ℝ}

include e in
theorem innerCollarLevelFun_eq_blend (hO : ∀ p : CuspHalfSpace, p.2.val 0 < 98 → e.toFun p ∈ O)
    (hτ : τ₁ < τ₂) (hρσ : ∀ p : CuspHalfSpace, p.2.val 0 ≤ σ → ρ (e.toFun p) < τ₁)
    (hηz : ∀ p : CuspHalfSpace, σ ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      |η (e.toFun p) - p.2.val 0| < 1 / 2)
    {p : CuspHalfSpace} (hp : p.2.val 0 ≤ 95) :
    innerCollarLevelFun O ρ η τ₁ τ₂ c (e.toFun p) = innerCollarBlend ρ η τ₁ τ₂ c (e.toFun p) := by
  refine innerCollarLevelFun_of_mem_of_factor_zero (hO p (by linarith)) ?_
  rcases le_or_gt (p.2.val 0) σ with h | h
  · rw [innerCollarCutoff_of_le hτ (hρσ p h).le, sub_self, zero_mul]
  · have h1 := (abs_lt.mp (hηz p h.le (by linarith))).2
    rw [innerCollarTopCutoff_of_le (by linarith), mul_zero]

include e in
theorem innerCollarLevelFun_eq_of_mid
    (hO : ∀ p : CuspHalfSpace, p.2.val 0 < 98 → e.toFun p ∈ O)
    (hτ : τ₁ < τ₂) (hρσ : ∀ p : CuspHalfSpace, p.2.val 0 ≤ σ → ρ (e.toFun p) < τ₁)
    (hρs₀ : ∀ p : CuspHalfSpace, s₀ ≤ p.2.val 0 → p.2.val 0 ≤ 98 → τ₂ < ρ (e.toFun p))
    (hηz : ∀ p : CuspHalfSpace, σ ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      |η (e.toFun p) - p.2.val 0| < 1 / 2)
    {p : CuspHalfSpace} (h1 : s₀ ≤ p.2.val 0) (h2 : p.2.val 0 ≤ 95) :
    innerCollarLevelFun O ρ η τ₁ τ₂ c (e.toFun p) = η (e.toFun p) := by
  rw [innerCollarLevelFun_eq_blend e hO hτ hρσ hηz h2,
    innerCollarBlend_of_cutoff_zero (innerCollarCutoff_of_ge hτ (hρs₀ p h1 (by linarith)).le)]

include e in
theorem innerCollarLevelFun_lt_of_low
    (hO : ∀ p : CuspHalfSpace, p.2.val 0 < 98 → e.toFun p ∈ O)
    (hs₀ : s₀ ≤ 1) (hτ : τ₁ < τ₂)
    (hρσ : ∀ p : CuspHalfSpace, p.2.val 0 ≤ σ → ρ (e.toFun p) < τ₁)
    (hρc : ∀ y, ρ y ≤ c - 2)
    (hηz : ∀ p : CuspHalfSpace, σ ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      |η (e.toFun p) - p.2.val 0| < 1 / 2)
    {p : CuspHalfSpace} (hp : p.2.val 0 ≤ s₀) :
    innerCollarLevelFun O ρ η τ₁ τ₂ c (e.toFun p) < 90 := by
  rw [innerCollarLevelFun_eq_blend e hO hτ hρσ hηz (by linarith)]
  have hρc' := hρc (e.toFun p)
  rcases le_or_gt (p.2.val 0) σ with h | h
  · rw [innerCollarBlend_of_cutoff_one (innerCollarCutoff_of_le hτ (hρσ p h).le)]
    linarith
  · have hη1 := (abs_lt.mp (hηz p h.le (by linarith))).2
    obtain ⟨hφa, hφb⟩ := innerCollarCutoff_mem τ₁ τ₂ (ρ (e.toFun p))
    rw [innerCollarBlend]
    nlinarith

include e in
theorem lt_innerCollarLevelFun_of_high
    (hO : ∀ p : CuspHalfSpace, p.2.val 0 < 98 → e.toFun p ∈ O)
    (hσs₀ : σ < s₀) (hs₀ : s₀ ≤ 1) (hτ : τ₁ < τ₂)
    (hρs₀ : ∀ p : CuspHalfSpace, s₀ ≤ p.2.val 0 → p.2.val 0 ≤ 98 → τ₂ < ρ (e.toFun p))
    (hηz : ∀ p : CuspHalfSpace, σ ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      |η (e.toFun p) - p.2.val 0| < 1 / 2)
    {p : CuspHalfSpace} (h1 : 95 < p.2.val 0) (h2 : p.2.val 0 < 98) :
    90 < innerCollarLevelFun O ρ η τ₁ τ₂ c (e.toFun p) := by
  have hφ := innerCollarCutoff_of_ge hτ (hρs₀ p (by linarith) h2.le).le
  rw [innerCollarLevelFun_of_mem (hO p h2), innerCollarBlend_of_cutoff_zero hφ, hφ, sub_zero,
    one_mul]
  have hη1 := (abs_lt.mp (hηz p (by linarith) h2.le)).1
  obtain ⟨hψa, hψb⟩ := innerCollarTopCutoff_mem (η (e.toFun p))
  nlinarith

include e in
theorem innerCollarLevelFun_eq_of_top
    (hO : ∀ p : CuspHalfSpace, p.2.val 0 < 98 → e.toFun p ∈ O)
    (hσs₀ : σ < s₀) (hs₀ : s₀ ≤ 1) (hτ : τ₁ < τ₂)
    (hρs₀ : ∀ p : CuspHalfSpace, s₀ ≤ p.2.val 0 → p.2.val 0 ≤ 98 → τ₂ < ρ (e.toFun p))
    (hηz : ∀ p : CuspHalfSpace, σ ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      |η (e.toFun p) - p.2.val 0| < 1 / 2)
    {p : CuspHalfSpace} (h1 : 97.5 < p.2.val 0) (h2 : p.2.val 0 < 98) :
    innerCollarLevelFun O ρ η τ₁ τ₂ c (e.toFun p) = 94 := by
  have hη1 := (abs_lt.mp (hηz p (by linarith) h2.le)).1
  exact innerCollarLevelFun_of_mem_of_top (hO p h2)
    (innerCollarCutoff_of_ge hτ (hρs₀ p (by linarith) h2.le).le)
    (innerCollarTopCutoff_of_ge (by linarith))

include e in
theorem contMDiff_innerCollarLevelFun (hρ : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ρ)
    (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) (hOo : IsOpen O)
    (hO : ∀ p : CuspHalfSpace, p.2.val 0 < 98 → e.toFun p ∈ O)
    (hOsub : ∀ y ∈ O, ∃ p : CuspHalfSpace, p.2.val 0 < 98 ∧ e.toFun p = y)
    (hσs₀ : σ < s₀) (hs₀ : s₀ ≤ 1) (hτ : τ₁ < τ₂)
    (hρs₀ : ∀ p : CuspHalfSpace, s₀ ≤ p.2.val 0 → p.2.val 0 ≤ 98 → τ₂ < ρ (e.toFun p))
    (hηz : ∀ p : CuspHalfSpace, σ ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      |η (e.toFun p) - p.2.val 0| < 1 / 2) :
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (innerCollarLevelFun O ρ η τ₁ τ₂ c) := by
  have hb : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (innerCollarBlend ρ η τ₁ τ₂ c) :=
    hη.add (((contDiff_innerCollarCutoff τ₁ τ₂).contMDiff.comp hρ).mul
      ((hρ.sub contMDiff_const).sub hη))
  have ht : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (fun y => innerCollarBlend ρ η τ₁ τ₂ c y +
      (1 - innerCollarCutoff τ₁ τ₂ (ρ y)) * innerCollarTopCutoff (η y) *
        (94 - innerCollarBlend ρ η τ₁ τ₂ c y)) :=
    hb.add (((contMDiff_const.sub ((contDiff_innerCollarCutoff τ₁ τ₂).contMDiff.comp hρ)).mul
      (contDiff_innerCollarTopCutoff.contMDiff.comp hη)).mul (contMDiff_const.sub hb))
  have hCc : IsCompact
      (e.toFun '' {p : CuspHalfSpace | 0 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 97.5}) :=
    e.isCompact_image_band (by norm_num [cuspDepth])
  intro y
  by_cases hy : y ∈ O
  · exact (ht y).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hOo.mem_nhds hy) fun y' hy' => innerCollarLevelFun_of_mem hy')
  · have hyC : y ∉ e.toFun '' {p : CuspHalfSpace | 0 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 97.5} := by
      rintro ⟨p, hp, rfl⟩
      exact hy (hO p (by linarith [hp.2]))
    refine (contMDiffAt_const (c := (94 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hCc.isClosed.isOpen_compl.mem_nhds hyC] with y' hy'
    by_cases hy'O : y' ∈ O
    · obtain ⟨p, hp98, rfl⟩ := hOsub y' hy'O
      have hp975 : 97.5 < p.2.val 0 := by
        by_contra hle
        exact hy' ⟨p, ⟨p.2.2, not_lt.mp hle⟩, rfl⟩
      exact innerCollarLevelFun_eq_of_top e hO hσs₀ hs₀ hτ hρs₀ hηz hp975 hp98
    · exact innerCollarLevelFun_of_notMem hy'O

end Cusp

/-- Bounds in `g`-norms at `e p` for `η - ζ` give the Z-contract bounds in `H`-norms, with the
constant multiplied by `1 + |δ|`. -/
theorem CuspEmbedding.height_bounds_of_inner_bounds (e : CuspEmbedding W g K δ X)
    {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) {ε' : ℝ} (hε' : 0 < ε')
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (h0 : |η (e.toFun p) - (invFunOn e.toFun cuspDomain (e.toFun p)).2.val 0| < ε')
    (h1 : ∀ X' : TangentSpace W.model (e.toFun p),
      |mvfderiv W.model (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
          X'| ≤ ε' * Real.sqrt (g.inner (e.toFun p) X' X'))
    (h2 : ∀ X' Y' : TangentSpace W.model (e.toFun p),
      |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
          (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) X' Y'| ≤
        ε' * Real.sqrt (g.inner (e.toFun p) X' X') * Real.sqrt (g.inner (e.toFun p) Y' Y')) :
    |η (e.toFun p) - p.2.val 0| < ε' * (1 + |δ|) ∧
      (∀ v : TangentSpace halfCollarModel p,
        |(show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p v) -
            (show ℝ from v.2 0)| ≤
          ε' * (1 + |δ|) * Real.sqrt (e.cusp.metric.inner p v v)) ∧
      ∀ v w : TangentSpace halfCollarModel p,
        |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
            (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
            (mfderiv halfCollarModel W.model e.toFun p v)
            (mfderiv halfCollarModel W.model e.toFun p w)| ≤
          ε' * (1 + |δ|) * Real.sqrt (e.cusp.metric.inner p v v) *
            Real.sqrt (e.cusp.metric.inner p w w) := by
  set ζ : W.Carrier → ℝ := fun y => (invFunOn e.toFun cuspDomain y).2.val 0 with hζ
  have hδ1 : 1 ≤ 1 + |δ| := by linarith [abs_nonneg δ]
  set c : ℝ := Real.sqrt (1 + |δ|) with hc
  have hcc : c * c = 1 + |δ| := Real.mul_self_sqrt (by positivity)
  have hc1 : 1 ≤ c := by rw [hc, Real.one_le_sqrt]; exact hδ1
  have hgH : ∀ v : TangentSpace halfCollarModel p,
      Real.sqrt (g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p v)) ≤
        c * Real.sqrt (e.cusp.metric.inner p v v) := by
    intro v
    rw [hc, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ((e.pullback_inner_le_one_add_mul hp v).trans ?_)
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self δ])
      (metric_inner_self_nonneg _ _ _)
  have hζp : ζ (e.toFun p) = p.2.val 0 := e.height_apply hp
  refine ⟨?_, fun v => ?_, fun v w => ?_⟩
  · rw [← hζp]
    exact h0.trans_le (le_mul_of_one_le_right hε'.le hδ1)
  · have hed : MDifferentiableAt halfCollarModel W.model e.toFun p :=
      (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hp)).mdifferentiableAt (by simp)
    have hηd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) η (e.toFun p) :=
      (hη _).mdifferentiableAt (by simp)
    have hζd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) ζ (e.toFun p) :=
      (e.contMDiffOn_height.contMDiffAt
        (e.isOpen_image_cuspDomain.mem_nhds (mem_image_of_mem _ hp))).mdifferentiableAt
          one_ne_zero
    have hchain : mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p v =
        mfderiv W.model 𝓘(ℝ, ℝ) η (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v) := by
      rw [mfderiv_comp p hηd hed]
      rfl
    have hz := e.mfderiv_height_invFunOn_mfderiv hp v
    have key : (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p v) -
        (show ℝ from v.2 0) =
        mvfderiv W.model (fun y => η y - ζ y) (e.toFun p)
          (mfderiv halfCollarModel W.model e.toFun p v) := by
      rw [mvfderiv_fun_sub hηd hζd, sub_apply]
      change _ = (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) η (e.toFun p)
          (mfderiv halfCollarModel W.model e.toFun p v)) -
        (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) ζ (e.toFun p)
          (mfderiv halfCollarModel W.model e.toFun p v))
      rw [hz, ← hchain]
    rw [key]
    calc _ ≤ ε' * Real.sqrt (g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
          (mfderiv halfCollarModel W.model e.toFun p v)) := h1 _
      _ ≤ ε' * (c * Real.sqrt (e.cusp.metric.inner p v v)) :=
          mul_le_mul_of_nonneg_left (hgH v) hε'.le
      _ ≤ ε' * (c * c) * Real.sqrt (e.cusp.metric.inner p v v) := by
          have hs := Real.sqrt_nonneg (e.cusp.metric.inner p v v)
          have hc0 : 0 ≤ c := by linarith
          nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hε'.le hc0) hs) (sub_nonneg.mpr hc1)]
      _ = _ := by rw [hcc]
  · calc _ ≤ ε' * Real.sqrt (g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
          (mfderiv halfCollarModel W.model e.toFun p v)) *
          Real.sqrt (g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p w)
            (mfderiv halfCollarModel W.model e.toFun p w)) := h2 _ _
      _ ≤ ε' * (c * Real.sqrt (e.cusp.metric.inner p v v)) *
          (c * Real.sqrt (e.cusp.metric.inner p w w)) := by
          gcongr
          · exact hgH v
          · exact hgH w
      _ = ε' * (c * c) * Real.sqrt (e.cusp.metric.inner p v v) *
          Real.sqrt (e.cusp.metric.inner p w w) := by ring
      _ = _ := by rw [hcc]

/-- The analytic data of the inner collar (inputs of E6(i)). -/
theorem CuspEmbedding.exists_innerCollar_data (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ρ η : W.Carrier → ℝ) (V : (y : W.Carrier) → TangentSpace W.model y)
      (s₀ σ τ₁ τ₂ c ε' : ℝ),
      ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ρ ∧ ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      0 < σ ∧ σ < s₀ ∧ s₀ ≤ 1 ∧ 0 < τ₁ ∧ τ₁ < τ₂ ∧ 0 < ε' ∧ ε' * (1 + |δ|) ≤ ε ∧
      (∀ x ∈ X, ρ x = 0) ∧
      (∀ p : CuspHalfSpace, p.2.val 0 ≤ σ → ρ (e.toFun p) < τ₁) ∧
      (∀ p : CuspHalfSpace, s₀ ≤ p.2.val 0 → p.2.val 0 ≤ 98 → τ₂ < ρ (e.toFun p)) ∧
      (∀ y, ρ y ≤ c - 2) ∧
      (∀ p : CuspHalfSpace, σ ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        |η (e.toFun p) - p.2.val 0| < 1 / 2) ∧
      (∀ p : CuspHalfSpace, p.2.val 0 ≤ s₀ →
        (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) ρ (e.toFun p) (V (e.toFun p))) = 1) ∧
      (∀ p : CuspHalfSpace, σ ≤ p.2.val 0 → p.2.val 0 ≤ s₀ →
        0 < (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) η (e.toFun p) (V (e.toFun p)))) ∧
      (∀ p : CuspHalfSpace, σ ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        mfderiv W.model 𝓘(ℝ, ℝ) η (e.toFun p) ≠ 0) ∧
      ∀ p : CuspHalfSpace, σ ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        |η (e.toFun p) - (invFunOn e.toFun cuspDomain (e.toFun p)).2.val 0| < ε' ∧
        (∀ X' : TangentSpace W.model (e.toFun p),
          |mvfderiv W.model (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0)
              (e.toFun p) X'| ≤ ε' * Real.sqrt (g.inner (e.toFun p) X' X')) ∧
        ∀ X' Y' : TangentSpace W.model (e.toFun p),
          |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
              (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) X' Y'| ≤
            ε' * Real.sqrt (g.inner (e.toFun p) X' X') *
              Real.sqrt (g.inner (e.toFun p) Y' Y') := by
  classical
  set ζ : W.Carrier → ℝ := fun y => (invFunOn e.toFun cuspDomain y).2.val 0 with hζ
  have hζe : ∀ p ∈ cuspDomain, ζ (e.toFun p) = p.2.val 0 := fun p hp => e.height_apply hp
  have hζd : ∀ p ∈ cuspDomain, MDifferentiableAt W.model 𝓘(ℝ, ℝ) ζ (e.toFun p) := fun p hp =>
    (e.contMDiffOn_height.contMDiffAt
      (e.isOpen_image_cuspDomain.mem_nhds (mem_image_of_mem _ hp))).mdifferentiableAt
        one_ne_zero
  obtain ⟨t₀⟩ := (inferInstance : Nonempty Torus)
  have h0dom : ((t₀, halfZero) : CuspHalfSpace) ∈ cuspDomain := by
    change (0 : ℝ) < cuspDepth
    norm_num [cuspDepth]
  have hXb : ∀ x ∈ X, W.model.IsBoundaryPoint x := by
    intro x hx
    rw [← e.boundary_image] at hx
    obtain ⟨t, rfl⟩ := hx
    exact (e.boundary_preimage (p := (t, halfZero)) (by
      change (0 : ℝ) < cuspDepth
      norm_num [cuspDepth])).mpr rfl
  have hX0 : e.toFun (t₀, halfZero) ∈ X := (Set.ext_iff.mp e.boundary_image _).mp ⟨t₀, rfl⟩
  -- the defining function and the inward field
  obtain ⟨ρ, O, hO, hρ, hρ0, hρiff, hBO, V, hV, hρV, hVin⟩ :=
    CompactCarrier.exists_boundary_definingFunction W ⟨_, hXb _ hX0⟩
  set Gz : W.Carrier → ℝ := fun y => (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) ζ y (V y)) with hGz
  have hGzc : ContinuousOn Gz (e.toFun '' cuspDomain) := e.continuousOn_mfderiv_height_apply hV
  have hGzX : ∀ x ∈ X, 0 < Gz x := fun x hx => e.mfderiv_height_pos_of_mem hx (hVin x (hXb x hx))
  set Ω₀ : Set W.Carrier := O ∩ (e.toFun '' cuspDomain ∩ Gz ⁻¹' Ioi 0) with hΩ₀
  have hΩ₀o : IsOpen Ω₀ :=
    hO.inter (hGzc.isOpen_inter_preimage e.isOpen_image_cuspDomain isOpen_Ioi)
  have hXΩ₀ : X ⊆ Ω₀ := by
    intro x hx
    refine ⟨hBO x (hXb x hx), ?_, hGzX x hx⟩
    rw [← e.boundary_image] at hx
    obtain ⟨t, rfl⟩ := hx
    exact mem_image_of_mem _ (by change (0 : ℝ) < cuspDepth; norm_num [cuspDepth])
  obtain ⟨s₀, hs₀, hs₀1, hs₀Ω⟩ := e.exists_collar_subset hΩ₀o hXΩ₀
  -- a lower bound for `dz(V)` on the collar `z ≤ s₀`
  set A₀ : Set W.Carrier := e.toFun '' {p : CuspHalfSpace | 0 ≤ p.2.val 0 ∧ p.2.val 0 ≤ s₀}
    with hA₀
  have hA₀c : IsCompact A₀ := e.isCompact_image_band (by norm_num [cuspDepth]; linarith)
  have hA₀sub : A₀ ⊆ e.toFun '' cuspDomain := image_mono fun p hp =>
    cusp_mem_cuspDomain_of_le (by norm_num [cuspDepth]; linarith) hp.2
  obtain ⟨y_m, hy_m, hmin⟩ := hA₀c.exists_isMinOn ⟨_, ⟨(t₀, halfZero), ⟨le_rfl, hs₀.le⟩, rfl⟩⟩
    (hGzc.mono hA₀sub)
  set m : ℝ := Gz y_m with hm
  have hm0 : 0 < m := by
    obtain ⟨p, hp, rfl⟩ := hy_m
    exact (hs₀Ω p hp.2).2.2
  have hGzm : ∀ p : CuspHalfSpace, p.2.val 0 ≤ s₀ → m ≤ Gz (e.toFun p) := fun p hp =>
    hmin ⟨p, ⟨p.2.2, hp⟩, rfl⟩
  -- bounds for `|V|_g` and `ρ`
  obtain ⟨Cv, hCv⟩ := exists_sqrt_inner_le_of_contMDiff g hV
  have hCv0 : 0 ≤ Cv := (Real.sqrt_nonneg _).trans (hCv (e.toFun (t₀, halfZero)))
  obtain ⟨Cρ, hCρ⟩ := isCompact_univ.exists_bound_of_continuousOn hρ.continuous.continuousOn
  have hρle : ∀ y, ρ y ≤ Cρ := fun y =>
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hCρ y (mem_univ y)))
  set c : ℝ := Cρ + 2 with hc
  -- `ρ` is bounded below on the band `s₀ ≤ z ≤ 98`
  have hlift : ∀ s : ℝ, 0 ≤ s → (halfSpaceOneLift s).1 0 = s := fun s hs => by
    rw [halfSpaceOneLift_val_zero, max_eq_left hs]
  set A₁ : Set W.Carrier := e.toFun '' {p : CuspHalfSpace | s₀ ≤ p.2.val 0 ∧ p.2.val 0 ≤ 98}
    with hA₁
  have hA₁c : IsCompact A₁ := e.isCompact_image_band (by norm_num [cuspDepth])
  have hA₁ne : A₁.Nonempty := ⟨_, ⟨(t₀, halfSpaceOneLift s₀),
    ⟨(hlift s₀ hs₀.le).ge, (hlift s₀ hs₀.le).le.trans (by linarith)⟩, rfl⟩⟩
  obtain ⟨y_ρ, hy_ρ, hminρ⟩ := hA₁c.exists_isMinOn hA₁ne hρ.continuous.continuousOn
  set mρ : ℝ := ρ y_ρ with hmρdef
  have hmρ : 0 < mρ := by
    obtain ⟨p, hp, rfl⟩ := hy_ρ
    have hpd : p ∈ cuspDomain := cusp_mem_cuspDomain_of_le (by norm_num [cuspDepth]) hp.2
    have hnb : ¬ W.model.IsBoundaryPoint (e.toFun p) := fun hb => by
      have h0 := (e.boundary_preimage hpd).mp hb
      linarith [hp.1]
    rcases (hρ0 (e.toFun p)).lt_or_eq with h | h
    · exact h
    · exact absurd ((hρiff _).mp h.symm) hnb
  have hρA₁ : ∀ p : CuspHalfSpace, s₀ ≤ p.2.val 0 → p.2.val 0 ≤ 98 → mρ ≤ ρ (e.toFun p) :=
    fun p h1 h2 => hminρ ⟨p, ⟨h1, h2⟩, rfl⟩
  set τ₂ : ℝ := mρ / 2 with hτ₂
  set τ₁ : ℝ := mρ / 4 with hτ₁
  have hτ₁₂ : τ₁ < τ₂ := by rw [hτ₁, hτ₂]; linarith
  have hτ₁0 : 0 < τ₁ := by rw [hτ₁]; positivity
  -- a collar on which `ρ < τ₁`
  obtain ⟨σ₀, hσ₀, -, hσ₀ρ⟩ := e.exists_collar_subset (O := {y | ρ y < τ₁})
    (isOpen_lt hρ.continuous continuous_const) (fun x hx => by
      change ρ x < τ₁
      rw [(hρiff x).mpr (hXb x hx)]
      exact hτ₁0)
  set σ : ℝ := min σ₀ (s₀ / 2) with hσdef
  have hσ : 0 < σ := lt_min hσ₀ (half_pos hs₀)
  have hσs₀ : σ < s₀ := (min_le_right _ _).trans_lt (half_lt_self hs₀)
  have hσρ : ∀ p : CuspHalfSpace, p.2.val 0 ≤ σ → ρ (e.toFun p) < τ₁ := fun p hp =>
    hσ₀ρ p (hp.trans (min_le_left _ _))
  -- the approximation parameter
  set μ : ℝ := min (min (1 / 2) ε) (m / (2 * (1 + Cv))) with hμ
  have hμ0 : 0 < μ := lt_min (lt_min (by norm_num) hε) (by positivity)
  have hδ1 : 1 ≤ 1 + |δ| := by linarith [abs_nonneg δ]
  set ε' : ℝ := μ / (1 + |δ|) with hε'
  have hε'0 : 0 < ε' := div_pos hμ0 (by positivity)
  have hε'μ : ε' * (1 + |δ|) = μ := div_mul_cancel₀ μ (by positivity)
  have hε'le : ε' ≤ μ := div_le_self hμ0.le hδ1
  have hμhalf : μ ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hμε : μ ≤ ε := (min_le_left _ _).trans (min_le_right _ _)
  have hε'm : ε' * Cv < m := by
    have h1 : μ ≤ m / (2 * (1 + Cv)) := min_le_right _ _
    have h2 : ε' * Cv ≤ m / (2 * (1 + Cv)) * Cv :=
      mul_le_mul_of_nonneg_right (hε'le.trans h1) hCv0
    have h3 : m / (2 * (1 + Cv)) * Cv < m := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  -- `η`: the `C²` approximation of `ζ` on `σ ≤ z ≤ 98`
  set S₁ : Set CuspHalfSpace := {p | σ / 2 < p.2.val 0 ∧ p.2.val 0 < 99} with hS₁
  have hS₁d : S₁ ⊆ cuspDomain := fun p hp => by
    change p.2.val 0 < cuspDepth
    exact hp.2.trans (by norm_num [cuspDepth])
  have hS₁o : IsOpen S₁ := by
    change IsOpen ((fun p : CuspHalfSpace => p.2.val 0) ⁻¹' Ioo (σ / 2) 99)
    exact isOpen_Ioo.preimage (by fun_prop)
  have hUo : IsOpen (e.toFun '' S₁) :=
    e.isOpen_image_of_pos hS₁o hS₁d fun p hp => (half_pos hσ).trans hp.1
  have hUi : e.toFun '' S₁ ⊆ W.model.interior W.Carrier := by
    rintro _ ⟨p, hp, rfl⟩
    refine (W.model.isInteriorPoint_iff_not_isBoundaryPoint _).mpr fun hb => ?_
    have h0 := (e.boundary_preimage (hS₁d hp)).mp hb
    linarith [hp.1, half_pos hσ]
  have hζ2 : ContMDiffOn W.model 𝓘(ℝ, ℝ) 2 ζ (e.toFun '' S₁) := by
    rintro _ ⟨p, hp, rfl⟩
    have h := e.contMDiffAt_height_of_pos (hS₁d hp) ((half_pos hσ).trans hp.1)
    exact (h.of_le (by exact_mod_cast Nat.succ_le_succ hK)).contMDiffWithinAt
  have hBhc : IsCompact (e.toFun '' {p : CuspHalfSpace | σ ≤ p.2.val 0 ∧ p.2.val 0 ≤ 98}) :=
    e.isCompact_image_band (by norm_num [cuspDepth])
  have hBhU : e.toFun '' {p : CuspHalfSpace | σ ≤ p.2.val 0 ∧ p.2.val 0 ≤ 98} ⊆
      e.toFun '' S₁ :=
    image_mono fun p hp => ⟨by linarith [hp.1, half_lt_self hσ], by linarith [hp.2]⟩
  obtain ⟨η, hη, hηB⟩ := exists_smooth_approx_C2_on_compact g hUo hUi hζ2 hBhc hBhU hε'0
  have hηb : ∀ p : CuspHalfSpace, σ ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      |η (e.toFun p) - ζ (e.toFun p)| < ε' ∧
      (∀ X : TangentSpace W.model (e.toFun p),
        |mvfderiv W.model (fun y => η y - ζ y) (e.toFun p) X| ≤
          ε' * Real.sqrt (g.inner (e.toFun p) X X)) ∧
      ∀ X Y : TangentSpace W.model (e.toFun p),
        |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
            (fun y => η y - ζ y) (e.toFun p) X Y| ≤
          ε' * Real.sqrt (g.inner (e.toFun p) X X) * Real.sqrt (g.inner (e.toFun p) Y Y) :=
    fun p h1 h2 => hηB _ ⟨p, ⟨h1, h2⟩, rfl⟩
  have hdom : ∀ p : CuspHalfSpace, p.2.val 0 ≤ 98 → p ∈ cuspDomain := fun p hp =>
    cusp_mem_cuspDomain_of_le (by norm_num [cuspDepth]) hp
  have hηz : ∀ p : CuspHalfSpace, σ ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      |η (e.toFun p) - p.2.val 0| < 1 / 2 := fun p h1 h2 => by
    rw [← hζe p (hdom p h2)]
    exact ((hηb p h1 h2).1.trans_le hε'le).trans_le hμhalf
  have hηd : ∀ y, MDifferentiableAt W.model 𝓘(ℝ, ℝ) η y := fun y =>
    (hη y).mdifferentiableAt (by simp)
  have hsplit : ∀ p ∈ cuspDomain, ∀ X : TangentSpace W.model (e.toFun p),
      (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) η (e.toFun p) X) =
        (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) ζ (e.toFun p) X) +
          mvfderiv W.model (fun y => η y - ζ y) (e.toFun p) X := by
    intro p hp X
    rw [mvfderiv_fun_sub (hηd _) (hζd p hp), sub_apply]
    change _ = _ + ((show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) η (e.toFun p) X) -
      (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) ζ (e.toFun p) X))
    ring
  -- `dη(V) > 0` on the transition collar
  have hηV : ∀ p : CuspHalfSpace, σ ≤ p.2.val 0 → p.2.val 0 ≤ s₀ →
      0 < (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) η (e.toFun p) (V (e.toFun p))) := by
    intro p h1 h2
    have h98 : p.2.val 0 ≤ 98 := by linarith
    rw [hsplit p (hdom p h98)]
    have hb := (hηb p h1 h98).2.1 (V (e.toFun p))
    have hGp := hGzm p h2
    have hV' : ε' * Real.sqrt (g.inner (e.toFun p) (V (e.toFun p)) (V (e.toFun p))) ≤ ε' * Cv :=
      mul_le_mul_of_nonneg_left (hCv _) hε'0.le
    have habs := neg_abs_le (mvfderiv W.model (fun y => η y - ζ y) (e.toFun p) (V (e.toFun p)))
    change 0 < Gz (e.toFun p) + _
    linarith
  -- `η` is regular on `σ ≤ z ≤ 98` (vertical direction)
  have hηreg : ∀ p : CuspHalfSpace, σ ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      mfderiv W.model 𝓘(ℝ, ℝ) η (e.toFun p) ≠ 0 := by
    intro p h1 h2 h0
    have hpd := hdom p h2
    set v₀ : TangentSpace halfCollarModel p := ((0, 0), EuclideanSpace.single 0 1) with hv₀
    have hv₁ : v₀.1 = 0 := rfl
    have hv₂ : v₀.2 0 = 1 := by simp [hv₀]
    have hH : e.cusp.metric.inner p v₀ v₀ = 1 := by
      rw [cusp_inner_vertical e.cusp p v₀ hv₁, hv₂, one_pow]
    have hz1 := e.mfderiv_height_invFunOn_mfderiv hpd v₀
    rw [hv₂] at hz1
    have hs := hsplit p hpd (mfderiv halfCollarModel W.model e.toFun p v₀)
    rw [h0] at hs
    change (0 : ℝ) = _ + _ at hs
    have hb := (hηb p h1 h2).2.1 (mfderiv halfCollarModel W.model e.toFun p v₀)
    have hg : Real.sqrt (g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v₀)
        (mfderiv halfCollarModel W.model e.toFun p v₀)) ≤ 1 + |δ| := by
      have h1 : g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v₀)
          (mfderiv halfCollarModel W.model e.toFun p v₀) ≤ 1 + |δ| := by
        have h := e.pullback_inner_le_one_add_mul hpd v₀
        rw [hH, mul_one] at h
        linarith [le_abs_self δ]
      exact (Real.sqrt_le_sqrt h1).trans (Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩)
    have hb' := hb.trans (mul_le_mul_of_nonneg_left hg hε'0.le)
    rw [hε'μ] at hb'
    have habs := neg_abs_le (mvfderiv W.model (fun y => η y - ζ y) (e.toFun p)
      (mfderiv halfCollarModel W.model e.toFun p v₀))
    change (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) ζ (e.toFun p)
      (mfderiv halfCollarModel W.model e.toFun p v₀)) = 1 at hz1
    linarith
  refine ⟨ρ, η, V, s₀, σ, τ₁, τ₂, c, ε', hρ, hη, hσ, hσs₀, hs₀1, hτ₁0, hτ₁₂, hε'0,
    hε'μ.le.trans hμε, fun x hx => (hρiff x).mpr (hXb x hx), hσρ,
    fun p h1 h2 => (by rw [hτ₂]; linarith : τ₂ < mρ).trans_le (hρA₁ p h1 h2),
    fun y => by rw [hc]; linarith [hρle y], hηz, fun p hp => hρV _ (hs₀Ω p hp).1, hηV,
    hηreg, hηb⟩

/-- **E6(i).** A smooth height `F` with exact level `X`, regular on the sublevel `{F ≤ 90}`,
which is the inner collar cut by the level `η = 90` of a `C²` smoothing `η` of the height (`η`
satisfies the Z contract on `2 ≤ z ≤ 98`). -/
theorem CuspEmbedding.exists_innerCollar_height (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (η F : W.Carrier → ℝ) (a : ℝ), a < 90 ∧ ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        |η (e.toFun p) - p.2.val 0| < ε ∧
        (∀ v : TangentSpace halfCollarModel p,
          |(show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p v) -
              (show ℝ from v.2 0)| ≤
            ε * Real.sqrt (e.cusp.metric.inner p v v)) ∧
        ∀ v w : TangentSpace halfCollarModel p,
          |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
              (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
              (mfderiv halfCollarModel W.model e.toFun p v)
              (mfderiv halfCollarModel W.model e.toFun p w)| ≤
            ε * Real.sqrt (e.cusp.metric.inner p v v) *
              Real.sqrt (e.cusp.metric.inner p w w)) ∧
      (∀ x ∈ X, F x = a) ∧
      (∀ p : CuspHalfSpace, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 95 → F (e.toFun p) = η (e.toFun p)) ∧
      (∀ y, F y ≤ 90 ↔ ∃ p ∈ cuspDomain, e.toFun p = y ∧
        (p.2.val 0 ≤ 2 ∨ (p.2.val 0 ≤ 98 ∧ η y ≤ 90))) ∧
      (∀ x, F x ≤ 90 → mfderiv W.model 𝓘(ℝ, ℝ) F x ≠ 0) ∧ (∃ x, F x = 90) ∧
      (∀ x, W.model.IsBoundaryPoint x → F x ≤ 90 → x ∈ X) := by
  obtain ⟨ρ, η, V, s₀, σ, τ₁, τ₂, c, ε', hρ, hη, hσ, hσs₀, hs₀, hτ₁0, hτ, hε'0, hε'ε, hρX, hρσ,
    hρs₀, hρc, hηz, hρV, hηV, hηreg, hηb⟩ := e.exists_innerCollar_data hK hε
  have hOo : IsOpen (e.toFun '' {p : CuspHalfSpace | p.2.val 0 < 98}) := by
    refine e.isOpen_image ?_ fun p hp =>
      cusp_mem_cuspDomain_of_le (by norm_num [cuspDepth]) (le_of_lt hp)
    change IsOpen ((fun p : CuspHalfSpace => p.2.val 0) ⁻¹' Iio 98)
    exact isOpen_Iio.preimage (by fun_prop)
  have hO : ∀ p : CuspHalfSpace, p.2.val 0 < 98 →
      e.toFun p ∈ e.toFun '' {p : CuspHalfSpace | p.2.val 0 < 98} := fun p hp => ⟨p, hp, rfl⟩
  have hOsub : ∀ y ∈ e.toFun '' {p : CuspHalfSpace | p.2.val 0 < 98},
      ∃ p : CuspHalfSpace, p.2.val 0 < 98 ∧ e.toFun p = y := fun y hy => hy
  set F := innerCollarLevelFun (e.toFun '' {p : CuspHalfSpace | p.2.val 0 < 98}) ρ η τ₁ τ₂ c
    with hF
  have hFs : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F :=
    contMDiff_innerCollarLevelFun e hρ hη hOo hO hOsub hσs₀ hs₀ hτ hρs₀ hηz
  have hdom : ∀ p : CuspHalfSpace, p.2.val 0 ≤ 98 → p ∈ cuspDomain := fun p hp =>
    cusp_mem_cuspDomain_of_le (by norm_num [cuspDepth]) hp
  have hmid : ∀ p : CuspHalfSpace, s₀ ≤ p.2.val 0 → p.2.val 0 ≤ 95 →
      F (e.toFun p) = η (e.toFun p) := fun p h1 h2 =>
    innerCollarLevelFun_eq_of_mid e hO hτ hρσ hρs₀ hηz h1 h2
  have hchar : ∀ y, F y ≤ 90 ↔ ∃ p ∈ cuspDomain, e.toFun p = y ∧
      (p.2.val 0 ≤ 2 ∨ (p.2.val 0 ≤ 98 ∧ η y ≤ 90)) := by
    intro y
    constructor
    · intro hFy
      by_cases hy : y ∈ e.toFun '' {p : CuspHalfSpace | p.2.val 0 < 98}
      · obtain ⟨p, hp98, rfl⟩ := hy
        refine ⟨p, hdom p (le_of_lt hp98), rfl, ?_⟩
        by_cases h2 : p.2.val 0 ≤ 2
        · exact Or.inl h2
        · by_cases h95 : p.2.val 0 ≤ 95
          · rw [hmid p (by linarith) h95] at hFy
            exact Or.inr ⟨le_of_lt hp98, hFy⟩
          · exact absurd hFy (not_le.mpr
              (lt_innerCollarLevelFun_of_high e hO hσs₀ hs₀ hτ hρs₀ hηz (not_le.mp h95) hp98))
      · rw [hF, innerCollarLevelFun_of_notMem hy] at hFy
        norm_num at hFy
    · rintro ⟨p, hpd, rfl, h⟩
      by_cases hs : p.2.val 0 ≤ s₀
      · exact (innerCollarLevelFun_lt_of_low e hO hs₀ hτ hρσ hρc hηz hs).le
      · replace hs := not_le.mp hs
        rcases h with h2 | ⟨h98, hη90⟩
        · have hη1 := (abs_lt.mp (hηz p (by linarith) (by linarith))).2
          rw [hmid p hs.le (by linarith)]
          linarith
        · have hη1 := (abs_lt.mp (hηz p (by linarith) h98)).1
          rw [hmid p hs.le (by linarith)]
          exact hη90
  have hlow : ∀ y, F y ≤ 90 → ∃ p : CuspHalfSpace, p.2.val 0 ≤ 95 ∧ e.toFun p = y := by
    intro y hy
    obtain ⟨p, -, rfl, h⟩ := (hchar y).mp hy
    refine ⟨p, ?_, rfl⟩
    rcases h with h2 | ⟨h98, hη90⟩
    · linarith
    · by_contra h95
      have hη1 := (abs_lt.mp (hηz p (by linarith) h98)).1
      linarith
  obtain ⟨t₀⟩ := (inferInstance : Nonempty Torus)
  have hX0 : e.toFun (t₀, halfZero) ∈ X := (Set.ext_iff.mp e.boundary_image _).mp ⟨t₀, rfl⟩
  refine ⟨η, F, -c, ?_, hη, hFs, fun p hp h2 h98 => ?_, fun x hx => ?_, fun p h2 h95 =>
    hmid p (by linarith) h95, hchar, fun x hx => ?_, ?_, fun x hx hFx => ?_⟩
  · have := hρc (e.toFun (t₀, halfZero))
    rw [hρX _ hX0] at this
    linarith
  · obtain ⟨h0, h1, h2'⟩ := e.height_bounds_of_inner_bounds hη hε'0 hp
      (hηb p (by linarith) h98).1 (hηb p (by linarith) h98).2.1 (hηb p (by linarith) h98).2.2
    refine ⟨h0.trans_le hε'ε, fun v => (h1 v).trans ?_, fun v w => (h2' v w).trans ?_⟩
    · exact mul_le_mul_of_nonneg_right hε'ε (Real.sqrt_nonneg _)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hε'ε (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
  · rw [← e.boundary_image] at hx
    obtain ⟨t, rfl⟩ := hx
    have hzt : ((t, halfZero) : CuspHalfSpace).2.val 0 = 0 := rfl
    rw [hF, innerCollarLevelFun_eq_blend e hO hτ hρσ hηz (by rw [hzt]; norm_num),
      innerCollarBlend_of_cutoff_one (innerCollarCutoff_of_le hτ
        (hρσ _ (by rw [hzt]; exact hσ.le)).le),
      hρX _ ((Set.ext_iff.mp e.boundary_image _).mp ⟨t, rfl⟩), zero_sub]
  · -- regularity
    obtain ⟨p, hp95, rfl⟩ := hlow x hx
    have hxO : e.toFun p ∈ e.toFun '' {p : CuspHalfSpace | p.2.val 0 < 98} := hO p (by linarith)
    have hN : F =ᶠ[𝓝 (e.toFun p)] innerCollarBlend ρ η τ₁ τ₂ c := by
      have hNo : IsOpen ({y | ρ y < τ₁} ∪ {y | η y < 96}) :=
        (isOpen_lt hρ.continuous continuous_const).union (isOpen_lt hη.continuous continuous_const)
      have hmem : e.toFun p ∈ {y | ρ y < τ₁} ∪ {y | η y < 96} := by
        rcases le_or_gt (p.2.val 0) σ with h | h
        · exact Or.inl (hρσ p h)
        · right
          have hη1 := (abs_lt.mp (hηz p h.le (by linarith))).2
          change η (e.toFun p) < 96
          linarith
      filter_upwards [hOo.mem_nhds hxO, hNo.mem_nhds hmem] with y hy1 hy2
      refine innerCollarLevelFun_of_mem_of_factor_zero hy1 ?_
      rcases hy2 with h | h
      · rw [innerCollarCutoff_of_le hτ (le_of_lt h), sub_self, zero_mul]
      · rw [innerCollarTopCutoff_of_le (le_of_lt h), mul_zero]
    intro h0
    rcases le_or_gt (p.2.val 0) σ with h | h
    · -- near the boundary: `F` is `ρ - c`
      have hρd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) ρ (e.toFun p) :=
        (hρ _).mdifferentiableAt (by simp)
      have hloc : innerCollarBlend ρ η τ₁ τ₂ c =ᶠ[𝓝 (e.toFun p)] fun y => ρ y - c := by
        filter_upwards [(isOpen_lt hρ.continuous continuous_const).mem_nhds (hρσ p h)]
          with y hy
        exact innerCollarBlend_of_cutoff_one (innerCollarCutoff_of_le hτ (le_of_lt hy))
      have hd := ((hρd.hasMFDerivAt.sub (hasMFDerivAt_const c _)).congr_of_eventuallyEq
        (hN.trans hloc)).mfderiv
      rw [h0] at hd
      have h1 := hρV p (by linarith)
      have h2 : (0 : ℝ) =
          (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) ρ (e.toFun p) (V (e.toFun p))) - 0 :=
        congrArg (fun L : TangentSpace W.model (e.toFun p) →L[ℝ] ℝ => L (V (e.toFun p))) hd
      rw [sub_zero, h1] at h2
      norm_num at h2
    · rcases le_or_gt (p.2.val 0) s₀ with h' | h'
      · -- the transition: the blend increases along `V`
        have hbd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (innerCollarBlend ρ η τ₁ τ₂ c)
            (e.toFun p) :=
          ((hη _).add ((((contDiff_innerCollarCutoff τ₁ τ₂).contMDiff.comp hρ) _).mul
            (((hρ _).sub contMDiffAt_const).sub (hη _)))).mdifferentiableAt (by simp)
        have hd := (hbd.hasMFDerivAt.congr_of_eventuallyEq hN).mfderiv
        rw [h0] at hd
        have hpos := mfderiv_cutoffBlend_pos (I := W.model) (h := η) (ρ := ρ)
          (φ := innerCollarCutoff τ₁ τ₂) (c := c) (y := e.toFun p) (v := V (e.toFun p))
          ((hη _).mdifferentiableAt (by simp)) ((hρ _).mdifferentiableAt (by simp))
          (((contDiff_innerCollarCutoff τ₁ τ₂).differentiable (by simp)).differentiableAt)
          (innerCollarCutoff_mem _ _ _).1 (innerCollarCutoff_mem _ _ _).2
          ((antitone_innerCollarCutoff hτ).deriv_nonpos)
          (by
            have hη1 := (abs_lt.mp (hηz p h.le (by linarith))).1
            have := hρc (e.toFun p)
            linarith)
          (hηV p h.le h') (by rw [hρV p h']; exact one_pos)
        have hz : mfderiv W.model 𝓘(ℝ, ℝ)
            (fun y => η y + innerCollarCutoff τ₁ τ₂ (ρ y) * (ρ y - c - η y)) (e.toFun p) = 0 :=
          hd.symm
        rw [hz] at hpos
        exact lt_irrefl _ hpos
      · -- the middle: `F` is `η`
        have hloc : innerCollarBlend ρ η τ₁ τ₂ c =ᶠ[𝓝 (e.toFun p)] η := by
          filter_upwards [(isOpen_lt continuous_const hρ.continuous).mem_nhds
            (hρs₀ p h'.le (by linarith))] with y hy
          exact innerCollarBlend_of_cutoff_zero (innerCollarCutoff_of_ge hτ (le_of_lt hy))
        have hd := (((hη _).mdifferentiableAt (by simp)).hasMFDerivAt.congr_of_eventuallyEq
          (hN.trans hloc)).mfderiv
        rw [h0] at hd
        exact hηreg p h.le (by linarith) hd.symm
  · -- a point of the level `90`, on a vertical
    have hlift : ∀ s : ℝ, 0 ≤ s → (halfSpaceOneLift s).1 0 = s := fun s hs => by
      rw [halfSpaceOneLift_val_zero, max_eq_left hs]
    set f : ℝ → ℝ := fun s => F (e.toFun (t₀, halfSpaceOneLift s)) with hf
    have hfc : ContinuousOn f (Icc 3 95) := by
      refine hFs.continuous.comp_continuousOn (e.contMDiffOn.continuousOn.comp ?_ ?_)
      · exact continuousOn_const.prodMk
          (contMDiffOn_halfSpaceOneLift.continuousOn.mono fun s hs => (by linarith [hs.1] :
            (0 : ℝ) ≤ s))
      · intro s hs
        change (halfSpaceOneLift s).1 0 < cuspDepth
        rw [hlift s (by linarith [hs.1])]
        norm_num [cuspDepth]
        linarith [hs.2]
    have hf3 : f 3 < 90 := by
      have h3 : ((t₀, halfSpaceOneLift 3) : CuspHalfSpace).2.val 0 = 3 := hlift 3 (by norm_num)
      have hη1 := (abs_lt.mp (hηz (t₀, halfSpaceOneLift 3) (by rw [h3]; linarith)
        (by rw [h3]; norm_num))).2
      change F (e.toFun (t₀, halfSpaceOneLift 3)) < 90
      rw [hmid _ (by rw [h3]; linarith) (by rw [h3]; norm_num)]
      rw [h3] at hη1
      linarith
    have hf95 : 90 < f 95 := by
      have h3 : ((t₀, halfSpaceOneLift 95) : CuspHalfSpace).2.val 0 = 95 :=
        hlift 95 (by norm_num)
      have hη1 := (abs_lt.mp (hηz (t₀, halfSpaceOneLift 95) (by rw [h3]; linarith)
        (by rw [h3]; norm_num))).1
      change 90 < F (e.toFun (t₀, halfSpaceOneLift 95))
      rw [hmid _ (by rw [h3]; linarith) (by rw [h3])]
      rw [h3] at hη1
      linarith
    obtain ⟨s, -, hs⟩ := intermediate_value_Icc (by norm_num : (3 : ℝ) ≤ 95) hfc
      ⟨hf3.le, hf95.le⟩
    exact ⟨_, hs⟩
  · -- boundary points of the sublevel lie on `X`
    obtain ⟨p, hp95, rfl⟩ := hlow x hFx
    have hp0 := (e.boundary_preimage (hdom p (by linarith))).mp hx
    rw [cusp_eq_halfZero_of_height_eq_zero hp0]
    exact (Set.ext_iff.mp e.boundary_image _).mp ⟨p.1, rfl⟩

/-- **E6 (BCP01.c).** The inner collar cut by the level `90` of the smoothed height is a compact
smooth manifold with boundary `X ∪ {F = 90}`, diffeomorphic as a pair to
`(T² × [a, 90], T² × {a})`. -/
theorem CuspEmbedding.exists_innerCollar_diffeomorph_torus_Icc (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (η F : W.Carrier → ℝ) (a : ℝ) (har : a < 90), ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        |η (e.toFun p) - p.2.val 0| < ε ∧
        (∀ v : TangentSpace halfCollarModel p,
          |(show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p v) -
              (show ℝ from v.2 0)| ≤
            ε * Real.sqrt (e.cusp.metric.inner p v v)) ∧
        ∀ v w : TangentSpace halfCollarModel p,
          |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
              (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
              (mfderiv halfCollarModel W.model e.toFun p v)
              (mfderiv halfCollarModel W.model e.toFun p w)| ≤
            ε * Real.sqrt (e.cusp.metric.inner p v v) *
              Real.sqrt (e.cusp.metric.inner p w w)) ∧
      (∀ p : CuspHalfSpace, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 95 → F (e.toFun p) = η (e.toFun p)) ∧
      (∀ y, F y ≤ 90 ↔ ∃ p ∈ cuspDomain, e.toFun p = y ∧
        (p.2.val 0 ≤ 2 ∨ (p.2.val 0 ≤ 98 ∧ η y ≤ 90))) ∧
      ∃ cs : ChartedSpace (EuclideanHalfSpace 3) {x : W.Carrier // F x ≤ 90},
        letI := cs
        IsManifold (𝓡∂ 3) ∞ {x : W.Carrier // F x ≤ 90} ∧
        ContMDiff (𝓡∂ 3) W.model ∞ (fun x : {x : W.Carrier // F x ≤ 90} => x.1) ∧
        (∀ y : {x : W.Carrier // F x ≤ 90}, (𝓡∂ 3).IsBoundaryPoint y ↔
          (y.1 ∈ X ∨ F y.1 = 90)) ∧
        haveI : Fact (a < 90) := ⟨har⟩
        ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc a 90)
            {x : W.Carrier // F x ≤ 90} ∞,
          (∀ p, F (D p).1 = p.2.1) ∧ ∀ p, (D p).1 ∈ X ↔ p.2.1 = a := by
  obtain ⟨η, F, a, har, hη, hF, hZ, hXa, hmid, hchar, hreg, hr, hbd⟩ :=
    e.exists_innerCollar_height hK hε
  exact ⟨η, F, a, har, hη, hF, hZ, hmid, hchar,
    e.exists_sublevel_diffeomorph_torus_Icc har hF hreg hr hXa hbd⟩

end DifferentialGeometry.Geometry.Collapse

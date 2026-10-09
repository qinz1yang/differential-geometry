import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.SupportListsCollar

/-!
# BCG01 on actual data: zero supports never meet a reference domain that meets a boundary support

Blueprint 207B, BCG01 (`B:8727–8773`): "No zero support then meets `D_a`" — the inclusion
`D_a ⊂ {19 < η_b < 91} ⊂ B_b⁺` (BCG01.b, `BoundaryCollarPacket.bcg01_reference_domain`) together
with BCP05 (every zero ball misses every enlarged collar `B_b⁺ = e_b{z < 92}`, the T3 clause of
LC88). Here, for the LC88 collar blocks (`BoundaryCollarPacket.block`):

* `BoundaryCollarPacket.disjoint_referenceDomain_of_disjoint_enlargedCollar_BCG1`: a reference
  domain `D_a = B_g(p, C ρ(p))` meeting the `b`th closed boundary support misses every set that
  misses `e_b{z < 92}`;
* `BoundaryCollarPacket.bcg01_zero_exclusion_BCG1`: with a family of zero balls `B_g(c_k, R_k)`
  missing `e_b{z < 92}` (BCP05): `ρ(p) < 2 r_∂`, `D_a ⊂ e_b{19 < z < 91} ∩ {19 < η_b < 91}` and
  `D_a` misses every zero ball (the zero supports lie in the zero balls);
* `bcg01_parameters_BCG1`: the parameter side conditions of the reference-domain lemma for
  `r_∂ = β₁³/1000`, `L = 10⁶Δ`, `C ≤ .95L`, from `100ΔΛ ≤ 10⁻⁶` and `β₁³·10⁶Δ < 1`.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

namespace BoundaryCollarPacket

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
  {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- **BCG01, the reference domain misses everything that misses `B_b⁺`.** Under the hypotheses of
`bcg01_reference_domain`, a reference domain `D_a = B_g(p, C ρ(p))` meeting the `b`th closed boundary
support is disjoint from every set `Z` that misses the enlarged collar `e_b{z < 92}`. -/
theorem disjoint_referenceDomain_of_disjoint_enlargedCollar_BCG1
    (P : BoundaryCollarPacket W g K A w₀ ε) (hε : ε ≤ 1 / 4)
    {ρ : W.Carrier → ℝ} (hρ : ∀ x, 0 < ρ x) {Λ r C L : ℝ} (hΛ : 0 ≤ Λ)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hsmall : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) < r)
    (hL : 0 < L) (hC : C ≤ 95 / 100 * L) (hΛC : Λ * C ≤ 1 / 2) (hr : r * (1000 * L) < 1)
    {p : W.Carrier} {b : Fin P.cusp.count}
    (hmeet : ∃ x ∈ tsupport (P.block b), riemannianEDistOf g p x < ENNReal.ofReal (C * ρ p))
    {Z : Set W.Carrier}
    (hZ : Disjoint Z ((P.cusp.collar b).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) :
    Disjoint (riemannianBallOf g p (C * ρ p)) Z := by
  rw [Set.disjoint_left]
  intro y hy hyZ
  obtain ⟨q, -, hqy, -, hq91, -⟩ :=
    (P.bcg01_reference_domain hε hρ hΛ hlip hsmall hL hC hΛC hr hmeet).2 y hy
  exact Set.disjoint_left.mp hZ hyZ ⟨q, show q.2.val 0 < 92 by linarith, hqy⟩

/-- **BCG01 with the zero exclusion (BCP05).** Under the hypotheses of `bcg01_reference_domain`,
for a family of zero balls `B_g(c_k, R_k)` that all miss the enlarged collar `e_b{z < 92}`: a
reference domain `D_a = B_g(p, C ρ(p))` meeting the `b`th closed boundary support has
`ρ(p) < 2 r_∂`, lies in `e_b{19 < z < 91}` and in `{19 < η_b < 91}`, and misses every zero ball. -/
theorem bcg01_zero_exclusion_BCG1 (P : BoundaryCollarPacket W g K A w₀ ε) (hε : ε ≤ 1 / 4)
    {ρ : W.Carrier → ℝ} (hρ : ∀ x, 0 < ρ x) {Λ r C L : ℝ} (hΛ : 0 ≤ Λ)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hsmall : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) < r)
    (hL : 0 < L) (hC : C ≤ 95 / 100 * L) (hΛC : Λ * C ≤ 1 / 2) (hr : r * (1000 * L) < 1)
    {p : W.Carrier} {b : Fin P.cusp.count}
    (hmeet : ∃ x ∈ tsupport (P.block b), riemannianEDistOf g p x < ENNReal.ofReal (C * ρ p))
    {ι : Type*} (c : ι → W.Carrier) (R : ι → ℝ)
    (hsep : ∀ k, Disjoint (riemannianBallOf g (c k) (R k))
      ((P.cusp.collar b).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) :
    ρ p < 2 * r ∧
      (∀ y ∈ riemannianBallOf g p (C * ρ p), ∃ q ∈ cuspDomain, (P.cusp.collar b).toFun q = y ∧
        19 < q.2.val 0 ∧ q.2.val 0 < 91 ∧ 19 < P.height b y ∧ P.height b y < 91) ∧
      ∀ k, Disjoint (riemannianBallOf g p (C * ρ p)) (riemannianBallOf g (c k) (R k)) := by
  obtain ⟨h1, h2⟩ := P.bcg01_reference_domain hε hρ hΛ hlip hsmall hL hC hΛC hr hmeet
  exact ⟨h1, fun y hy => h2 y hy, fun k =>
    P.disjoint_referenceDomain_of_disjoint_enlargedCollar_BCG1 hε hρ hΛ hlip hsmall hL hC hΛC hr
      hmeet (hsep k)⟩

end BoundaryCollarPacket

/-- **The parameter side conditions of BCG01 for `r_∂ = β₁³/1000`, `L = 10⁶Δ`.** From
`100ΔΛ ≤ 10⁻⁶`, `C ≤ .95L` and the request `β₁³·10⁶Δ < 1`: `0 < L`, `ΛC ≤ 1/2`,
`r_∂ (1000 L) < 1`, and the collar smallness `ρ ≤ β₁³/2000` gives `ρ < r_∂`. -/
theorem bcg01_parameters_BCG1 {Λ Δ β₁ C ρc : ℝ} (hΛ : 0 < Λ) (hΔ : 0 < Δ) (hβ₁ : 0 < β₁)
    (hΛΔ : 100 * Δ * Λ ≤ 1 / 1000000) (hC : C ≤ 95 / 100 * (1000000 * Δ))
    (hreq : β₁ ^ 3 * (1000000 * Δ) < 1) (hρc : ρc ≤ β₁ ^ 3 / 2000) :
    0 < 1000000 * Δ ∧ Λ * C ≤ 1 / 2 ∧ β₁ ^ 3 / 1000 * (1000 * (1000000 * Δ)) < 1 ∧
      ρc < β₁ ^ 3 / 1000 := by
  have hβ3 : 0 < β₁ ^ 3 := pow_pos hβ₁ 3
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rcases le_or_gt C 0 with hC0 | hC0
    · have : Λ * C ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hΛ.le hC0
      linarith
    · have h1 : Λ * C ≤ Λ * (95 / 100 * (1000000 * Δ)) := mul_le_mul_of_nonneg_left hC hΛ.le
      nlinarith
  · have h : β₁ ^ 3 / 1000 * (1000 * (1000000 * Δ)) = β₁ ^ 3 * (1000000 * Δ) := by ring
    rw [h]
    exact hreq
  · linarith

end DifferentialGeometry.Geometry.Collapse

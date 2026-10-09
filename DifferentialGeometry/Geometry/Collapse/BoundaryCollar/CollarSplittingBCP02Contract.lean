import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarSplittingBCP02

/-!
# Row BCP02 for a given height with the Z contract

`CuspEmbedding.bcp02` (BCP23) proves BCP02 for the height `η` it chooses through BCP01. The LC88
collar packet (`LocalExport/BoundaryCollarPacket.lean`) fixes its own smoothed depth coordinate,
with the Z contract of B-5b's E8 / E6 (value, differential and Hessian `ε`-close to the collar
height in the reference norms on `2 ≤ z ≤ 98`). This module proves BCP02 for EVERY such height:

* `CuspEmbedding.bcp01_band_of_contract`: the BCP01 band clauses in `g`-norms from the Z contract
  (the conversion steps of `CuspEmbedding.bcp01`);
* `CuspEmbedding.bcp02_of_contract`: the conclusion of `CuspEmbedding.bcp02` (BCP02.a, BCP02.b with
  buffer, the adapted clauses of quality `γ`) for the given `η`. The proof is that of
  `CuspEmbedding.bcp02` with the given height in place of the BCP01 choice.
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.MetricGeometry
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Connection
  DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Manifold ENNReal ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

/-- The BCP01 band clauses in `g`-norms for any height with the Z contract (tolerance
`ε ≤ 1/1000`, `K ≥ 1`, `0 ≤ δ ≤ 1/1000`). -/
theorem CuspEmbedding.bcp01_band_of_contract (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000)
    {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η)
    (hZ : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
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
          ε * Real.sqrt (e.cusp.metric.inner p v v) * Real.sqrt (e.cusp.metric.inner p w w))
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (h2 : 2 ≤ p.2.val 0) (h98 : p.2.val 0 ≤ 98) :
      |η (e.toFun p) - p.2.val 0| < ε ∧
        (∀ u : TangentSpace W.model (e.toFun p),
          |mvfderiv W.model (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0)
              (e.toFun p) u| ≤ ε * (1 - δ)⁻¹ * Real.sqrt (g.inner (e.toFun p) u u)) ∧
        (∀ u w : TangentSpace W.model (e.toFun p),
          |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
              (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) u w| ≤
            ε * (1 - δ)⁻¹ * Real.sqrt (g.inner (e.toFun p) u u) *
              Real.sqrt (g.inner (e.toFun p) w w)) ∧
        (∀ u : TangentSpace W.model (e.toFun p),
          |mvfderiv W.model η (e.toFun p) u| ≤
            (1 + 1 / 200) * Real.sqrt (g.inner (e.toFun p) u u)) ∧
        (∃ u : TangentSpace W.model (e.toFun p), 0 < mvfderiv W.model η (e.toFun p) u ∧
          199 / 200 * Real.sqrt (g.inner (e.toFun p) u u) ≤ mvfderiv W.model η (e.toFun p) u) ∧
        (∀ u w : TangentSpace W.model (e.toFun p),
          |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) η
              (e.toFun p) u w| ≤
            3 / 2 * Real.sqrt (g.inner (e.toFun p) u u) * Real.sqrt (g.inner (e.toFun p) w w)) ∧
        99 / 100 < (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p
            ((0, 0), EuclideanSpace.single 0 1)) ∧
          (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p
            ((0, 0), EuclideanSpace.single 0 1)) < 101 / 100 := by
  obtain ⟨h0, h1, h2'⟩ := hZ p hp h2 h98
  obtain ⟨ha1, ha2⟩ := e.bcp01a_of_contract hδ0 (by linarith) hη hε.le hp h1 h2'
  obtain ⟨hb1, hb2, hb3⟩ := e.bcp01b_differential_of_contract hδ hη hε.le hε1 hp h1
  have hz : 0 < p.2.val 0 := by linarith
  have hH := e.bcp01b_hessian_le_of_contract hK hδ hη hε.le hε1 (by linarith) (by linarith) hp hz
    h2' (e.abs_hessian_height_le hK hδ0 (by linarith) hp)
  exact ⟨h0, ha1, ha2, hb1, hb2, hH, hb3⟩

/-- **Row BCP02 for a given height.** For any smooth `η` with the Z contract at tolerance
`0 < ε ≤ 1/1000` (`K ≥ 1`, `0 ≤ δ ≤ 1/1000`), the conclusion of `CuspEmbedding.bcp02` holds for
this `η`: BCP02.a, BCP02.b on the buffer ball and the adapted clauses of quality `γ`. -/
theorem CuspEmbedding.bcp02_of_contract [ConnectedSpace W.Carrier] (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000)
    {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η)
    (hZ : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
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
          ε * Real.sqrt (e.cusp.metric.inner p v v) * Real.sqrt (e.cusp.metric.inner p w w)) :
    ∀ (β γ L r : ℝ) (q₀ : CuspHalfSpace) (hr : 0 < r), 0 < β → β < γ → γ < 1 → 0 ≤ L →
      δ ≤ β ^ 2 / 1000 → ε ≤ β ^ 2 / 1000 → r ≤ β ^ 3 / (2000 * (1 + L)) →
      2 ≤ q₀.2.val 0 → q₀.2.val 0 ≤ 98 → 5 ≤ η (e.toFun q₀) → η (e.toFun q₀) ≤ 95 →
      @HasEuclideanSplitting.{u, 0} W.Carrier
          ((inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr)) (e.toFun q₀) 1 β ∧
      (∀ x x' : W.Carrier,
        r⁻¹ * (riemannianEDistOf g x (e.toFun q₀)).toReal ≤ β⁻¹ + β + L →
        r⁻¹ * (riemannianEDistOf g x' (e.toFun q₀)).toReal ≤ β⁻¹ + β + L →
        (1 - β ^ 2 / 20) * (r⁻¹ * (riemannianEDistOf g x x').toReal) ≤
            Real.sqrt (((η x - η (e.toFun q₀)) / r - (η x' - η (e.toFun q₀)) / r) ^ 2 +
              (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2) * (riemannianEDistOf e.cusp.torusMetric
                (invFunOn e.toFun cuspDomain x).1
                (invFunOn e.toFun cuspDomain x').1).toReal) ^ 2) ∧
          Real.sqrt (((η x - η (e.toFun q₀)) / r - (η x' - η (e.toFun q₀)) / r) ^ 2 +
              (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2) * (riemannianEDistOf e.cusp.torusMetric
                (invFunOn e.toFun cuspDomain x).1
                (invFunOn e.toFun cuspDomain x').1).toReal) ^ 2) ≤
            (1 + β ^ 2 / 20) * (r⁻¹ * (riemannianEDistOf g x x').toReal)) ∧
      (∀ x x' : W.Carrier, r⁻¹ * (riemannianEDistOf g x (e.toFun q₀)).toReal < 1 →
        r⁻¹ * (riemannianEDistOf g x' (e.toFun q₀)).toReal < 1 →
        |(η x - η (e.toFun q₀)) / r - (η x' - η (e.toFun q₀)) / r| ≤
          (1 + γ / 2) * (r⁻¹ * (riemannianEDistOf g x x').toReal)) ∧
      (∀ (c : ℝ → W.Carrier) (x₀ ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 + γ⁻¹ →
        (∀ t ∈ Icc x₀ (x₀ + ℓ), ContMDiffAt 𝓘(ℝ, ℝ) W.model 2 c t) →
        (∀ t ∈ Icc x₀ (x₀ + ℓ), HasGeodesicEquationAt g c t) →
        (∀ t ∈ Icc x₀ (x₀ + ℓ), ∃ p ∈ cuspDomain, 2 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 98 ∧
          e.toFun p = c t) →
        (∀ t ∈ Icc x₀ (x₀ + ℓ), g.inner (c t)
          (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1))
          (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1)) ≤ r ^ 2) →
        |deriv (fun t => (η (c t) - η (e.toFun q₀)) / r) x₀ -
          ((η (c (x₀ + ℓ)) - η (e.toFun q₀)) / r - (η (c x₀) - η (e.toFun q₀)) / r) / ℓ| <
          γ) ∧
      (∃ xp xm : W.Carrier, r⁻¹ * (riemannianEDistOf g xp (e.toFun q₀)).toReal < 1 ∧
        r⁻¹ * (riemannianEDistOf g xm (e.toFun q₀)).toReal < 1 ∧
        |(η xp - η (e.toFun q₀)) / r - 1| < γ ∧ |(η xm - η (e.toFun q₀)) / r + 1| < γ) ∧
      ∀ x : W.Carrier, r⁻¹ * (riemannianEDistOf g x (e.toFun q₀)).toReal < 1 →
        |(η x - η (e.toFun q₀)) / r| < 1 + γ := by
  have hb := fun p (hp : p ∈ cuspDomain) (h2 : 2 ≤ p.2.val 0) (h98 : p.2.val 0 ≤ 98) =>
    e.bcp01_band_of_contract hK hδ0 hδ hε hε1 hη hZ hp h2 h98
  intro β γ L r q₀ hr hβ hβγ hγ1 hL hδβ hεβ hrβ hz2 hz98 hη5 hη95
  obtain ⟨hρ, hε'0, hε'b, hrγ3, hrγ, hδγ, hε'γ, hδ34, hinvβ⟩ :=
    bcp02_parameters hβ hβγ hγ1 hL hδβ hε hεβ hr hrβ
  have hβ1 : β < 1 := hβγ.trans hγ1
  have hγ0 : 0 < γ := hβ.trans hβγ
  have hq₀ : q₀ ∈ cuspDomain := cusp_mem_cuspDomain_of_le (by norm_num [cuspDepth]) hz98
  have hηz₀ := (hb q₀ hq₀ hz2 hz98).1
  set z₀ : ℝ := q₀.2.val 0 with hz₀
  set p₀ : W.Carrier := e.toFun q₀ with hp₀
  have hz4 : 4 < z₀ := by linarith only [(abs_lt.mp hηz₀).2, hη5, hεβ, hε1]
  have hz96 : z₀ < 96 := by linarith only [(abs_lt.mp hηz₀).1, hη95, hε1]
  set R₁ : ℝ := β⁻¹ + β + L with hR₁
  have hR₁0 : 0 < R₁ := by positivity
  set ρ₁ : ℝ := r * R₁ with hρ₁
  have hρ0 : 0 < ρ₁ := mul_pos hr hR₁0
  have hb1 : β ^ 2 < 1 := by nlinarith only [hβ, hβ1]
  have hρ1 : ρ₁ ≤ 1 / 1000 := le_trans hρ (by linarith only [hb1])
  set ε' : ℝ := ε * (1 - δ)⁻¹ with hε'
  have hε'40 : ε' ≤ β ^ 2 / 40 := le_trans hε'b (by linarith only [sq_nonneg β])
  have hΔ := e.bcp02_slab_derivative hη (fun p hp h2 h98 => (hb p hp h2 h98).2.1) hz4 hz96 hρ1
  have hinv : ∀ p ∈ cuspDomain, invFunOn e.toFun cuspDomain (e.toFun p) = p :=
    fun p hp => e.injOn_cuspDomain.leftInvOn_invFunOn hp
  have hs0 : 1 / 2 < Real.sqrt (1 - δ) := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith only [hδ34])
  have hball : ∀ y : W.Carrier, r⁻¹ * (riemannianEDistOf g y p₀).toReal ≤ R₁ →
      riemannianEDistOf g p₀ y < ENNReal.ofReal (Real.sqrt (1 - δ) * (4 * ρ₁ / 2)) := by
    intro y hy
    have hle : (riemannianEDistOf g y p₀).toReal ≤ ρ₁ := by
      rw [hρ₁]
      have := (inv_mul_le_iff₀ hr).mp hy
      linarith only [this]
    rw [riemannianEDistOf_comm, ← ENNReal.ofReal_toReal (riemannianEDistOf_ne_top g _ _)]
    refine (ENNReal.ofReal_lt_ofReal_iff (by nlinarith only [hs0, hρ0])).mpr ?_
    nlinarith only [hs0, hρ0, hle]
  have hup16 : z₀ + 16 * ρ₁ < cuspDepth := by
    have : z₀ + 16 * ρ₁ < 100 := by linarith only [hz96, hρ1]
    simpa [cuspDepth] using this
  have hΔlip : ∀ x x' : W.Carrier, r⁻¹ * (riemannianEDistOf g x p₀).toReal ≤ R₁ →
      r⁻¹ * (riemannianEDistOf g x' p₀).toReal ≤ R₁ →
      |(η x - (invFunOn e.toFun cuspDomain x).2.val 0) -
          (η x' - (invFunOn e.toFun cuspDomain x').2.val 0)| ≤
        ε' * (riemannianEDistOf g x x').toReal := fun x x' hx hx' =>
    e.abs_sub_le_mul_of_mvfderiv_le (f := fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0)
      hup16 hδ34 hε'0 hΔ (hball x hx) (hball x' hx')
  have hp₀R : r⁻¹ * (riemannianEDistOf g p₀ p₀).toReal ≤ R₁ := by
    rw [riemannianEDistOf_self, ENNReal.toReal_zero, mul_zero]
    exact hR₁0.le
  -- BCP02.b with the buffer
  have hbuf := fun x x' (hx : r⁻¹ * (riemannianEDistOf g x p₀).toReal ≤ R₁)
      (hx' : r⁻¹ * (riemannianEDistOf g x' p₀).toReal ≤ R₁) =>
    e.bcp02_distortion (η := η) hβ hβ1 hδβ hr hR₁0 hρ hz4 hz96 hε'0 hε'40 hΔ hx hx'
  -- the Lipschitz clause on the unit ball
  have hlip : ∀ x x' : W.Carrier, r⁻¹ * (riemannianEDistOf g x p₀).toReal < 1 →
      r⁻¹ * (riemannianEDistOf g x' p₀).toReal < 1 →
      |(η x - η p₀) / r - (η x' - η p₀) / r| ≤
        (1 + γ / 2) * (r⁻¹ * (riemannianEDistOf g x x').toReal) := by
    intro x x' hx hx'
    have hR1 : 1 ≤ R₁ := by linarith only [hinvβ, hβ, hL]
    obtain ⟨-, hup⟩ := hbuf x x' (hx.le.trans hR1) (hx'.le.trans hR1)
    have habs := Real.abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg (r⁻¹ *
      Real.exp (-z₀ / 2) * (riemannianEDistOf e.cusp.torusMetric (invFunOn e.toFun cuspDomain x).1
        (invFunOn e.toFun cuspDomain x').1).toReal)) :
      ((η x - η p₀) / r - (η x' - η p₀) / r) ^ 2 ≤ _)
    have hd0 : 0 ≤ r⁻¹ * (riemannianEDistOf g x x').toReal :=
      mul_nonneg (inv_pos.mpr hr).le ENNReal.toReal_nonneg
    have hβγ' : β ^ 2 / 20 ≤ γ / 2 := by nlinarith only [hβ, hβ1, hβγ]
    calc _ ≤ _ := habs
      _ ≤ (1 + β ^ 2 / 20) * (r⁻¹ * (riemannianEDistOf g x x').toReal) := hup
      _ ≤ (1 + γ / 2) * (r⁻¹ * (riemannianEDistOf g x x').toReal) := by gcongr
  refine ⟨?_, hbuf, hlip, ?_, ?_, ?_⟩
  · -- BCP02.a: the splitting
    have hc : 0 < r⁻¹ * Real.exp (-z₀ / 2) := mul_pos (inv_pos.mpr hr) (Real.exp_pos _)
    have hinv₀ : invFunOn e.toFun cuspDomain p₀ = q₀ := hinv q₀ hq₀
    have hRle : β⁻¹ + β ≤ R₁ := by linarith only [hL]
    refine @hasEuclideanSplitting_of_coordinate_bounds W.Carrier
      ((inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr)) p₀ β (β ^ 2 / 20)
      (r⁻¹ * Real.exp (-z₀ / 2)) hβ hβ1 (by positivity) (by linarith only [hb1]) ?_ Torus
      (fun x => (η x - η p₀) / r) (fun x => (invFunOn e.toFun cuspDomain x).1)
      (fun t t' => (riemannianEDistOf e.cusp.torusMetric t t').toReal) (by simp) ?_ ?_ Torus
      ((inducedMetricSpace e.cusp.torusMetric).rescale _ hc) id surjective_id (fun _ _ => rfl)
    · have hinvβ' : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
      have h3 : β ^ 3 < β := by nlinarith only [hβ, hβ1, hb1]
      calc 2 * (β ^ 2 / 20) * (β⁻¹ + β) = β / 10 * (β * β⁻¹) + β ^ 3 / 10 := by ring
        _ = β / 10 + β ^ 3 / 10 := by rw [hinvβ', mul_one]
        _ < β / 4 := by linarith only [h3, hβ]
    · intro x x' hx hx'
      change r⁻¹ * (riemannianEDistOf g x p₀).toReal ≤ β⁻¹ + β at hx
      change r⁻¹ * (riemannianEDistOf g x' p₀).toReal ≤ β⁻¹ + β at hx'
      exact hbuf x x' (hx.trans hRle) (hx'.trans hRle)
    · intro s t hst
      change Real.sqrt (s ^ 2 + (r⁻¹ * Real.exp (-z₀ / 2) * (riemannianEDistOf e.cusp.torusMetric
        t (invFunOn e.toFun cuspDomain p₀).1).toReal) ^ 2) ≤ β⁻¹ + β - β / 4 at hst
      rw [hinv₀] at hst
      exact e.bcp02_coverage hq₀ hβ hβ1 hr hδ0 hδβ hρ0 hρ
        (mul_le_mul_of_nonneg_left hRle hr.le) hRle hz4 hz96 hε'0.le hε'b hΔlip s t hst
  · -- the chord test
    exact fun c x₀ ℓ hℓ hℓγ hc hgeo hband hspeed => e.bcp02_chord hη
      (fun p hp h2 h98 => (hb p hp h2 h98).2.2.2.2.2.1) hγ0 hγ1 hr hrγ3 c x₀ ℓ hℓ hℓγ hc hgeo
      hband hspeed
  · -- the image clause
    exact e.bcp02_image hq₀ hγ0 hγ1 hr hrγ hδ0 hδγ hz4 hz96 hε'0.le hε'γ
      (by linarith only [hinvβ, hβ, hL]) hΔlip
  · intro x hx
    have h := hlip x p₀ hx (by
      rw [riemannianEDistOf_self, ENNReal.toReal_zero, mul_zero]
      exact zero_lt_one)
    rw [sub_self, zero_div, sub_zero] at h
    have hd0 : 0 ≤ r⁻¹ * (riemannianEDistOf g x p₀).toReal :=
      mul_nonneg (inv_pos.mpr hr).le ENNReal.toReal_nonneg
    have : (1 + γ / 2) * (r⁻¹ * (riemannianEDistOf g x p₀).toReal) < 1 + γ := by
      nlinarith only [hd0, hx, hγ0]
    linarith only [h, this]

end DifferentialGeometry.Geometry.Collapse

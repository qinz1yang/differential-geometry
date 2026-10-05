import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarSplittingBCP02KL
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCollarAlternative
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottProductCoordinates

/-!
# B3: the actual cusp splitting with BOTH coordinates on the one physical height (lane BCUSP-1, G2)

Review 51, item B3 (`docs/geometrization/chapter14/out/dispositions-task51-boundary-family-enrichment.md`);
blueprint BCP02 (`B:8212–8320`) and BCG02's use of it (`B:8847–8852`): at every band point the actual
pointed `(1, β∂)`-splitting of `(M, r⁻²g, p)` has Euclidean coordinate EXACTLY
`U = (η_i − η_i(p))/r` on all its tested balls, its complete residual factor is the frozen flat torus
`(T², r⁻¹ e^{−z(p)/2} d_{g_T})` (not a point), and the same height is an adapted coordinate of quality
`γ∂` with the additional buffer `L`.

Exists (BCG-1): `BoundaryCollarPacket.exists_kleinerLott_height_BCG1` (Kleiner–Lott map with first
coordinate `U` everywhere; the second coordinate was not recorded) and `BoundaryExportPacket.adapted`
(BCP02.a/b with buffer `L`, adapted clauses of quality `γ`). New here:

* `CuspEmbedding.exists_kleinerLott_product_of_contract_BCUSP1`: the Kleiner–Lott map with first
  coordinate `U` EVERYWHERE and second coordinate the ACTUAL torus coordinate
  `(e⁻¹ x).1` on the whole closed test ball of radius `β⁻¹ + β`; model point `(0, t₀)` with `t₀` the
  torus coordinate of the basepoint;
* `BoundaryCollarPacket.exists_kleinerLott_product_BCUSP1`: the same for the packet's own height;
* `BoundaryExportPacket.cusp_splitting_BCUSP1` (B3): at quality `β = β∂`, adapted quality `γ = γ∂`,
  buffer `L` and scale `r ≤ β∂³/(2000(1+L))`: the product Kleiner–Lott map AND the full BCP02
  conclusion (`adapted`) for the SAME `U`;
* consumer `lc88_cusp_splitting_req_BCUSP1`: B3 on the packet returned by the requested T3
  (`lc88_boundary_collapse_packet_req_BCUSP1`), `r = ρ(e_i q₀)`, every late `L`, `γ∂`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.MetricGeometry
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Connection
  DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Manifold ENNReal ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

/-- **BCP02.a with both coordinates.** For a height `η` with the Z contract, at a band point `q₀`
and a scale `0 < r ≤ β³/2000` (`δ, ε ≤ β²/1000`): a Kleiner–Lott `β`-approximation of
`(W, r⁻¹ d_g, e q₀)` to `ℝ ×₂ (T², r⁻¹ e^{−z₀/2} d_{g_T})` with model point `(0, t₀)`, `t₀ = q₀.1`,
whose real coordinate is `(η − η(e q₀))/r` everywhere and whose torus coordinate is the actual
torus coordinate `(e⁻¹ x).1` on the closed test ball of radius `β⁻¹ + β`. -/
theorem CuspEmbedding.exists_kleinerLott_product_of_contract_BCUSP1 [ConnectedSpace W.Carrier]
    (e : CuspEmbedding W g K δ X)
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
          ε * Real.sqrt (e.cusp.metric.inner p v v) * Real.sqrt (e.cusp.metric.inner p w w))
    {β r : ℝ} (q₀ : CuspHalfSpace) (hr : 0 < r) (hβ : 0 < β) (hβ1 : β < 1)
    (hδβ : δ ≤ β ^ 2 / 1000) (hεβ : ε ≤ β ^ 2 / 1000) (hrβ : r ≤ β ^ 3 / 2000)
    (hz2 : 2 ≤ q₀.2.val 0) (hz98 : q₀.2.val 0 ≤ 98) (hη5 : 5 ≤ η (e.toFun q₀))
    (hη95 : η (e.toFun q₀) ≤ 95) :
    letI := (inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr)
    letI := (inducedMetricSpace e.cusp.torusMetric).rescale (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2))
      (mul_pos (inv_pos.mpr hr) (Real.exp_pos _))
    ∃ t₀ : Torus, t₀ = q₀.1 ∧ ∃ f : KleinerLottApprox (e.toFun q₀) (WithLp.toLp 2 ((0 : ℝ), t₀)) β,
      (∀ x, (f.toFun x).fst = (η x - η (e.toFun q₀)) / r) ∧
      ∀ x, r⁻¹ * (riemannianEDistOf g x (e.toFun q₀)).toReal ≤ β⁻¹ + β →
        (f.toFun x).snd = (invFunOn e.toFun cuspDomain x).1 := by
  have hb := fun p (hp : p ∈ cuspDomain) (h2 : 2 ≤ p.2.val 0) (h98 : p.2.val 0 ≤ 98) =>
    e.bcp01_band_of_contract hK hδ0 hδ hε hε1 hη hZ hp h2 h98
  have hβγ : β < (β + 1) / 2 := by linarith
  have hγ1 : (β + 1) / 2 < 1 := by linarith
  have hrβ' : r ≤ β ^ 3 / (2000 * (1 + 0)) := by rw [add_zero, mul_one]; exact hrβ
  obtain ⟨hρ, hε'0, hε'b, -, -, -, -, hδ34, hinvβ⟩ :=
    bcp02_parameters hβ hβγ hγ1 le_rfl hδβ hε hεβ hr hrβ'
  have hq₀ : q₀ ∈ cuspDomain := cusp_mem_cuspDomain_of_le (by norm_num [cuspDepth]) hz98
  have hηz₀ := (hb q₀ hq₀ hz2 hz98).1
  set z₀ : ℝ := q₀.2.val 0 with hz₀
  set p₀ : W.Carrier := e.toFun q₀ with hp₀
  have hz4 : 4 < z₀ := by linarith only [(abs_lt.mp hηz₀).2, hη5, hεβ, hε1]
  have hz96 : z₀ < 96 := by linarith only [(abs_lt.mp hηz₀).1, hη95, hε1]
  set R₁ : ℝ := β⁻¹ + β + 0 with hR₁
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
  have hbuf := fun x x' (hx : r⁻¹ * (riemannianEDistOf g x p₀).toReal ≤ R₁)
      (hx' : r⁻¹ * (riemannianEDistOf g x' p₀).toReal ≤ R₁) =>
    e.bcp02_distortion (η := η) hβ hβ1 hδβ hr hR₁0 hρ hz4 hz96 hε'0 hε'40 hΔ hx hx'
  have hc : 0 < r⁻¹ * Real.exp (-z₀ / 2) := mul_pos (inv_pos.mpr hr) (Real.exp_pos _)
  have hinv₀ : invFunOn e.toFun cuspDomain p₀ = q₀ := hinv q₀ hq₀
  have hRle : β⁻¹ + β ≤ R₁ := by rw [hR₁, add_zero]
  have herr : 2 * (β ^ 2 / 20) * (β⁻¹ + β) < β / 4 := by
    have hinvβ' : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
    have h3 : β ^ 3 < β := by nlinarith only [hβ, hβ1, hb1]
    calc 2 * (β ^ 2 / 20) * (β⁻¹ + β) = β / 10 * (β * β⁻¹) + β ^ 3 / 10 := by ring
      _ = β / 10 + β ^ 3 / 10 := by rw [hinvβ', mul_one]
      _ < β / 4 := by linarith only [h3, hβ]
  obtain ⟨f, hf, hsnd⟩ := @PointedBallApprox.exists_kleinerLott_with_product_coordinates_BCUSP1 W.Carrier
    ((inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr)) p₀ β (β ^ 2 / 20)
    (r⁻¹ * Real.exp (-z₀ / 2)) hβ hβ1 (by positivity) (by linarith only [hb1]) herr Torus
    (fun x => (η x - η p₀) / r) (fun x => (invFunOn e.toFun cuspDomain x).1)
    (fun t t' => (riemannianEDistOf e.cusp.torusMetric t t').toReal) (by simp)
    (fun x x' hx hx' => by
      change r⁻¹ * (riemannianEDistOf g x p₀).toReal ≤ β⁻¹ + β at hx
      change r⁻¹ * (riemannianEDistOf g x' p₀).toReal ≤ β⁻¹ + β at hx'
      exact hbuf x x' (hx.trans hRle) (hx'.trans hRle))
    (fun s t hst => by
      change Real.sqrt (s ^ 2 + (r⁻¹ * Real.exp (-z₀ / 2) * (riemannianEDistOf e.cusp.torusMetric
        t (invFunOn e.toFun cuspDomain p₀).1).toReal) ^ 2) ≤ β⁻¹ + β - β / 4 at hst
      rw [hinv₀] at hst
      exact e.bcp02_coverage hq₀ hβ hβ1 hr hδ0 hδβ hρ0 hρ
        (mul_le_mul_of_nonneg_left hRle hr.le) hRle hz4 hz96 hε'0.le hε'b hΔlip s t hst)
    Torus ((inducedMetricSpace e.cusp.torusMetric).rescale _ hc) id surjective_id
    (fun _ _ => rfl)
  exact ⟨_, by rw [hinv₀]; rfl, f, hf, fun x hx => hsnd x hx⟩

namespace BoundaryCollarPacket

variable {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- **The packet's own height and the actual torus coordinate as the two coordinates of a BCP02
splitting** (`1 ≤ K`, tolerance `ε ≤ 1/1000`, band point `q₀`, `0 < r ≤ β³/2000`,
`w₀, ε ≤ β²/1000`). -/
theorem exists_kleinerLott_product_BCUSP1 [ConnectedSpace W.Carrier]
    (P : BoundaryCollarPacket W g K A w₀ ε) (hK : 1 ≤ K) (hε : ε ≤ 1 / 1000)
    (i : Fin P.cusp.count) {β r : ℝ} (q₀ : CuspHalfSpace) (hr : 0 < r) (hβ : 0 < β)
    (hβ1 : β < 1) (hwβ : w₀ ≤ β ^ 2 / 1000) (hεβ : ε ≤ β ^ 2 / 1000) (hrβ : r ≤ β ^ 3 / 2000)
    (hz2 : 2 ≤ q₀.2.val 0) (hz98 : q₀.2.val 0 ≤ 98)
    (hη5 : 5 ≤ P.height i ((P.cusp.collar i).toFun q₀))
    (hη95 : P.height i ((P.cusp.collar i).toFun q₀) ≤ 95) :
    letI := (inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr)
    letI := (inducedMetricSpace (P.cusp.collar i).cusp.torusMetric).rescale
      (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2)) (mul_pos (inv_pos.mpr hr) (Real.exp_pos _))
    ∃ t₀ : Torus, t₀ = q₀.1 ∧ ∃ f : KleinerLottApprox ((P.cusp.collar i).toFun q₀)
        (WithLp.toLp 2 ((0 : ℝ), t₀)) β,
      (∀ x, (f.toFun x).fst = (P.height i x - P.height i ((P.cusp.collar i).toFun q₀)) / r) ∧
      ∀ x, r⁻¹ * (riemannianEDistOf g x ((P.cusp.collar i).toFun q₀)).toReal ≤ β⁻¹ + β →
        (f.toFun x).snd = (invFunOn (P.cusp.collar i).toFun cuspDomain x).1 :=
  (P.cusp.collar i).exists_kleinerLott_product_of_contract_BCUSP1 hK (P.cusp.collar i).delta_nonneg
    (by linarith [P.threshold]) P.tolerance_pos hε (P.contMDiff_height i) (P.height_contract i)
    q₀ hr hβ hβ1 hwβ hεβ hrβ hz2 hz98 hη5 hη95

end BoundaryCollarPacket

namespace BoundaryExportPacket

variable {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- **B3: the actual cusp splitting on the one physical height.** For the export packet
(`1 ≤ K`, tolerance `ε ≤ 1/1000`) at a band point `e_i q₀` (`2 ≤ z ≤ 98`, `5 ≤ η_i ≤ 95`), cusp
splitting quality `β = β∂`, adapted quality `γ = γ∂` (`β < γ < 1`), buffer `L ≥ 0`, scale
`0 < r ≤ β³/(2000(1+L))` and `w₀, ε ≤ β²/1000`, with `U = (η_i − η_i(e_i q₀))/r`:
(1) a Kleiner–Lott `β`-approximation of `(W, r⁻¹ d_g, e_i q₀)` to `ℝ ×₂` the frozen flat torus
`(T², r⁻¹ e^{−z₀/2} d_{g_T})`, model point `(0, q₀.1)`, real coordinate `U` everywhere, torus
coordinate the actual one on the closed test ball of radius `β⁻¹ + β`, with its coverage;
(2) the full BCP02 conclusion (`adapted`) for the SAME `U`: the splitting, the bi-Lipschitz product
comparison on the buffer ball of radius `β⁻¹ + β + L`, and the adapted clauses of quality `γ`. -/
theorem cusp_splitting_BCUSP1 [ConnectedSpace W.Carrier]
    (P : BoundaryExportPacket W g K A w₀ ε) (hK : 1 ≤ K) (hε : ε ≤ 1 / 1000)
    (i : Fin P.cusp.count) (β γ L r : ℝ) (q₀ : CuspHalfSpace) (hr : 0 < r) (hβ : 0 < β)
    (hβγ : β < γ) (hγ1 : γ < 1) (hL : 0 ≤ L) (hwβ : w₀ ≤ β ^ 2 / 1000)
    (hεβ : ε ≤ β ^ 2 / 1000) (hrβ : r ≤ β ^ 3 / (2000 * (1 + L)))
    (hz2 : 2 ≤ q₀.2.val 0) (hz98 : q₀.2.val 0 ≤ 98)
    (hη5 : 5 ≤ P.height i ((P.cusp.collar i).toFun q₀))
    (hη95 : P.height i ((P.cusp.collar i).toFun q₀) ≤ 95) :
    (letI := (inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr);
    letI := (inducedMetricSpace (P.cusp.collar i).cusp.torusMetric).rescale
      (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2)) (mul_pos (inv_pos.mpr hr) (Real.exp_pos _));
    ∃ t₀ : Torus, t₀ = q₀.1 ∧ ∃ f : KleinerLottApprox ((P.cusp.collar i).toFun q₀)
        (WithLp.toLp 2 ((0 : ℝ), t₀)) β,
      (∀ x, (f.toFun x).fst = (P.height i x - P.height i ((P.cusp.collar i).toFun q₀)) / r) ∧
      ∀ x, r⁻¹ * (riemannianEDistOf g x ((P.cusp.collar i).toFun q₀)).toReal ≤ β⁻¹ + β →
        (f.toFun x).snd = (invFunOn (P.cusp.collar i).toFun cuspDomain x).1) ∧
        @HasEuclideanSplitting.{u, 0} W.Carrier
            ((inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr)) ((P.cusp.collar i).toFun q₀) 1 β ∧
        (∀ x x' : W.Carrier,
          r⁻¹ * (riemannianEDistOf g x ((P.cusp.collar i).toFun q₀)).toReal ≤ β⁻¹ + β + L →
          r⁻¹ * (riemannianEDistOf g x' ((P.cusp.collar i).toFun q₀)).toReal ≤ β⁻¹ + β + L →
          (1 - β ^ 2 / 20) * (r⁻¹ * (riemannianEDistOf g x x').toReal) ≤
              Real.sqrt (((P.height i x - P.height i ((P.cusp.collar i).toFun q₀)) / r -
                  (P.height i x' - P.height i ((P.cusp.collar i).toFun q₀)) / r) ^ 2 +
                (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2) *
                    (riemannianEDistOf (P.cusp.collar i).cusp.torusMetric
                  (invFunOn (P.cusp.collar i).toFun cuspDomain x).1
                  (invFunOn (P.cusp.collar i).toFun cuspDomain x').1).toReal) ^ 2) ∧
            Real.sqrt (((P.height i x - P.height i ((P.cusp.collar i).toFun q₀)) / r -
                (P.height i x' - P.height i ((P.cusp.collar i).toFun q₀)) / r) ^ 2 +
                (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2) *
                    (riemannianEDistOf (P.cusp.collar i).cusp.torusMetric
                  (invFunOn (P.cusp.collar i).toFun cuspDomain x).1
                  (invFunOn (P.cusp.collar i).toFun cuspDomain x').1).toReal) ^ 2) ≤
              (1 + β ^ 2 / 20) * (r⁻¹ * (riemannianEDistOf g x x').toReal)) ∧
        (∀ x x' : W.Carrier, r⁻¹ * (riemannianEDistOf g x ((P.cusp.collar i).toFun q₀)).toReal < 1 →
          r⁻¹ * (riemannianEDistOf g x' ((P.cusp.collar i).toFun q₀)).toReal < 1 →
          |(P.height i x - P.height i ((P.cusp.collar i).toFun q₀)) / r - (P.height i x' - P.height i
              ((P.cusp.collar i).toFun q₀)) / r| ≤
            (1 + γ / 2) * (r⁻¹ * (riemannianEDistOf g x x').toReal)) ∧
        (∀ (c : ℝ → W.Carrier) (x₀ ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 + γ⁻¹ →
          (∀ t ∈ Icc x₀ (x₀ + ℓ), ContMDiffAt 𝓘(ℝ, ℝ) W.model 2 c t) →
          (∀ t ∈ Icc x₀ (x₀ + ℓ), HasGeodesicEquationAt g c t) →
          (∀ t ∈ Icc x₀ (x₀ + ℓ), ∃ p ∈ cuspDomain, 2 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 98 ∧
            (P.cusp.collar i).toFun p = c t) →
          (∀ t ∈ Icc x₀ (x₀ + ℓ), g.inner (c t)
            (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1))
            (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1)) ≤ r ^ 2) →
          |deriv (fun t => (P.height i (c t) - P.height i ((P.cusp.collar i).toFun q₀)) / r) x₀ -
            ((P.height i (c (x₀ +
                ℓ)) - P.height i ((P.cusp.collar i).toFun q₀)) / r - (P.height i (c x₀) - P.height i
                    ((P.cusp.collar i).toFun q₀)) / r) / ℓ| <
            γ) ∧
        (∃ xp xm : W.Carrier, r⁻¹ * (riemannianEDistOf g xp ((P.cusp.collar i).toFun q₀)).toReal < 1 ∧
          r⁻¹ * (riemannianEDistOf g xm ((P.cusp.collar i).toFun q₀)).toReal < 1 ∧
          |(P.height i xp - P.height i ((P.cusp.collar i).toFun q₀)) / r - 1| < γ ∧
              |(P.height i xm - P.height i ((P.cusp.collar i).toFun q₀)) / r + 1| < γ) ∧
        ∀ x : W.Carrier, r⁻¹ * (riemannianEDistOf g x ((P.cusp.collar i).toFun q₀)).toReal < 1 →
          |(P.height i x - P.height i ((P.cusp.collar i).toFun q₀)) / r| < 1 + γ := by
  have hL1 : 1 ≤ 1 + L := by linarith
  have hrβ' : r ≤ β ^ 3 / 2000 := by
    refine hrβ.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h3 : 0 ≤ β ^ 3 := by positivity
    nlinarith
  exact ⟨P.toBoundaryCollarPacket.exists_kleinerLott_product_BCUSP1 hK hε i q₀ hr hβ
      (hβγ.trans hγ1) hwβ hεβ hrβ' hz2 hz98 hη5 hη95,
    P.adapted i β γ L r q₀ hr hβ hβγ hγ1 hL hwβ hεβ hrβ hz2 hz98 hη5 hη95⟩

end BoundaryExportPacket

end DifferentialGeometry.Geometry.Collapse

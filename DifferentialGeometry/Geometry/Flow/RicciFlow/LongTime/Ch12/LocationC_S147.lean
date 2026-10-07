import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SmoothFirstExit_CX2

set_option autoImplicit false

/-!
# CH12-S147 G2a: (C) location arithmetic

After the forward trace exists, `d(q, yf) ≤ e^{9Kτ} · c θ'ρ` (product of the per-slab factors of
`slab_forward_ball_S147`, total elapsed time `≤ τ (θ'ρ)²` with tube `K/(θ'ρ)²`), and `9Kτ ≤ 1`, `e < 3`,
`3 c θ' ≤ 1` give `d(q, yf) ≤ ρ`, hence `yf ∈ B(p, 2ρ)` when `q ∈ B(p, ρ)`.
-/

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- (C) location: a point within `e^{9Kτ} (c θ' ρ)` of `q ∈ B(p,ρ)` lies in `B(p, 2ρ)`. -/
theorem location_of_forward_dist_S147 {P : OrientedThreeStage.{u}} (g : P.Metric)
    {p q yf : P.Carrier} {ρ θ' K τ c : ℝ} (hρ : 0 < ρ) (hθ' : 0 < θ') (hc : 0 ≤ c)
    (hθc : 3 * c * θ' ≤ 1) (hτK : 9 * K * τ ≤ 1) (hq : q ∈ riemannianBallOf g p ρ)
    (hyf : riemannianEDistOf g q yf ≤
      ENNReal.ofReal (Real.exp (9 * K * τ) * (c * (θ' * ρ)))) :
    yf ∈ riemannianBallOf g p (2 * ρ) := by
  have he : Real.exp (9 * K * τ) ≤ 3 :=
    ((Real.exp_le_exp.mpr hτK).trans (Real.exp_one_lt_d9.le)).trans (by norm_num)
  have hnn : 0 ≤ c * (θ' * ρ) := by positivity
  have hd : Real.exp (9 * K * τ) * (c * (θ' * ρ)) ≤ ρ := by
    calc Real.exp (9 * K * τ) * (c * (θ' * ρ)) ≤ 3 * (c * (θ' * ρ)) :=
          mul_le_mul_of_nonneg_right he hnn
      _ = (3 * c * θ') * ρ := by ring
      _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right hθc hρ.le
      _ = ρ := one_mul ρ
  have h1 : riemannianEDistOf g q yf ≤ ENNReal.ofReal ρ := hyf.trans (ENNReal.ofReal_le_ofReal hd)
  have htri := riemannianEDistOf_triangle g p q yf
  have hsum : riemannianEDistOf g p yf < ENNReal.ofReal ρ + ENNReal.ofReal ρ :=
    htri.trans_lt (ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1) hq h1)
  change riemannianEDistOf g p yf < ENNReal.ofReal (2 * ρ)
  rwa [two_mul, ENNReal.ofReal_add hρ.le hρ.le]

/-- `c = 20`, `θ' ≤ 1/60`. -/
theorem location_of_forward_dist20_S147 {P : OrientedThreeStage.{u}} (g : P.Metric)
    {p q yf : P.Carrier} {ρ θ' K τ : ℝ} (hρ : 0 < ρ) (hθ' : 0 < θ') (hθ60 : θ' ≤ 1 / 60)
    (hτK : 9 * K * τ ≤ 1) (hq : q ∈ riemannianBallOf g p ρ)
    (hyf : riemannianEDistOf g q yf ≤
      ENNReal.ofReal (Real.exp (9 * K * τ) * (20 * (θ' * ρ)))) :
    yf ∈ riemannianBallOf g p (2 * ρ) :=
  location_of_forward_dist_S147 g hρ hθ' (by norm_num) (by linarith only [hθ60]) hτK hq hyf

end GC.LongTime.Ch12

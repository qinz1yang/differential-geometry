import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MapConvergence
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Derivative-closure for `MapCInfConvOnCompacts` (Euclidean analysis layer)

`MapCInfConvOnCompacts U Φ Φinf` retains the FULL Fréchet-derivative data of the
MSM135 `C^∞`-convergence definition: `mapDerivNorm r Φₖ Φinf = ‖∇ʳ(Φₖ - Φ_∞)‖`
is controlled uniformly on compacts for every order `r`.  Hence the notion is
closed under taking a directional derivative: if `Φₖ → Φ_∞` in `C^∞`-on-compacts
(with all maps `C^∞`), then

  `z ↦ fderiv ℝ (Φₖ) z v  →  z ↦ fderiv ℝ Φ_∞ z v`

again in `C^∞`-on-compacts.  This is the analytic producer the covariant-tower
bridge `componentConv_covDeriv_of_chartCInf` (Gap B, order `a ≥ 1`) needs to push
the order-0 chart-component convergence through one covariant-derivative step
(`fderiv … v` is the coordinate directional derivative entering
`nabla0SFun_two_eval_coordFrame`).

This file is `MapConvergence.lean`-adjacent Euclidean analysis (no manifold
content).  It lives here rather than in `MapConvergence.lean` only because that
file is currently owned by another session.
-/

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology
open scoped ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pointwise bound: the order-`r` Euclidean derivative norm of the difference of
directional derivatives `z ↦ fderiv ℝ (·) z v` is `≤ ‖v‖` times the order-`(r+1)`
derivative norm of the difference of the maps.  (`fderiv` is linear, so the
difference of directional derivatives is the directional derivative of the
difference; then `clm_apply_const` peels off `· v` and `norm_iteratedFDeriv_fderiv`
raises the order by one.) -/
theorem mapDerivNorm_fderivApply_le (r : ℕ) (v : E) {Φk Φinf : E → F} {x : E}
    (hk : ContDiff ℝ (∞ : WithTop ℕ∞) Φk) (hinf : ContDiff ℝ (∞ : WithTop ℕ∞) Φinf) :
    mapDerivNorm r (fun z => fderiv ℝ Φk z v) (fun z => fderiv ℝ Φinf z v) x
      ≤ ‖v‖ * mapDerivNorm (r + 1) Φk Φinf x := by
  have hfun : (fun z => fderiv ℝ Φk z v - fderiv ℝ Φinf z v)
      = (fun z => fderiv ℝ (fun y => Φk y - Φinf y) z v) := by
    funext z
    have hd : fderiv ℝ (fun y => Φk y - Φinf y) z = fderiv ℝ Φk z - fderiv ℝ Φinf z :=
      fderiv_sub (hk.differentiable (by simp)).differentiableAt
        (hinf.differentiable (by simp)).differentiableAt
    rw [hd, ContinuousLinearMap.sub_apply]
  rw [mapDerivNorm, hfun]
  set g : E → F := fun y => Φk y - Φinf y with hg
  have hgcd : ContDiff ℝ (∞ : WithTop ℕ∞) g := hk.sub hinf
  have hfd : ContDiffAt ℝ (r : WithTop ℕ∞) (fderiv ℝ g) x :=
    (hgcd.fderiv_right (m := (r : WithTop ℕ∞)) (by exact_mod_cast le_top)).contDiffAt
  calc ‖iteratedFDeriv ℝ r (fun z => fderiv ℝ g z v) x‖
      ≤ ‖v‖ * ‖iteratedFDeriv ℝ r (fderiv ℝ g) x‖ :=
        norm_iteratedFDeriv_clm_apply_const hfd le_rfl
    _ = ‖v‖ * ‖iteratedFDeriv ℝ (r + 1) g x‖ := by rw [norm_iteratedFDeriv_fderiv]
    _ = ‖v‖ * mapDerivNorm (r + 1) Φk Φinf x := by rw [mapDerivNorm, hg]

/-- **Derivative-closure of `C^∞`-on-compacts convergence.**  If `Φₖ → Φ_∞` in
`C^∞`-on-compacts on `U` (all maps `C^∞`), then the directional derivatives
`z ↦ fderiv ℝ (Φₖ) z v` converge to `z ↦ fderiv ℝ Φ_∞ z v` in `C^∞`-on-compacts.
At order `p`/`K` it consumes the order-`(p+1)` content of the hypothesis. -/
theorem MapCInfConvOnCompacts.fderivApply {U : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCInfConvOnCompacts U Φ Φinf)
    (hΦ : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (Φ k))
    (hΦinf : ContDiff ℝ (∞ : WithTop ℕ∞) Φinf) (v : E) :
    MapCInfConvOnCompacts U (fun k z => fderiv ℝ (Φ k) z v) (fun z => fderiv ℝ Φinf z v) := by
  intro K hK hKU p ε hε
  obtain ⟨k0, hk0⟩ := h K hK hKU (p + 1) (ε / (‖v‖ + 1)) (by positivity)
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  calc mapDerivNorm r (fun z => fderiv ℝ (Φ k) z v) (fun z => fderiv ℝ Φinf z v) x
      ≤ ‖v‖ * mapDerivNorm (r + 1) (Φ k) Φinf x :=
        mapDerivNorm_fderivApply_le r v (hΦ k) hΦinf
    _ ≤ ‖v‖ * (ε / (‖v‖ + 1)) := by
        gcongr
        exact hk0 k hk (r + 1) (by omega) x hx
    _ ≤ ε := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0:ℝ) < ‖v‖ + 1)]
        nlinarith [norm_nonneg v, hε.le]

/-- **Additivity of `C^∞`-on-compacts convergence.**  Sums of `C^∞`-on-compacts
convergent families (all `C^∞`) converge `C^∞`-on-compacts to the sum of the
limits. -/
theorem MapCInfConvOnCompacts.add {U : Set E} {Φ Ψ : ℕ → E → F} {Φinf Ψinf : E → F}
    (hΦ : MapCInfConvOnCompacts U Φ Φinf) (hΨ : MapCInfConvOnCompacts U Ψ Ψinf)
    (hΦc : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (Φ k)) (hΦic : ContDiff ℝ (∞ : WithTop ℕ∞) Φinf)
    (hΨc : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (Ψ k)) (hΨic : ContDiff ℝ (∞ : WithTop ℕ∞) Ψinf) :
    MapCInfConvOnCompacts U (fun k z => Φ k z + Ψ k z) (fun z => Φinf z + Ψinf z) := by
  intro K hK hKU p ε hε
  obtain ⟨k1, hk1⟩ := hΦ K hK hKU p (ε / 2) (by positivity)
  obtain ⟨k2, hk2⟩ := hΨ K hK hKU p (ε / 2) (by positivity)
  refine ⟨max k1 k2, fun k hk r hr x hx => ?_⟩
  have hsplit : mapDerivNorm r (fun z => Φ k z + Ψ k z) (fun z => Φinf z + Ψinf z) x
      ≤ mapDerivNorm r (Φ k) Φinf x + mapDerivNorm r (Ψ k) Ψinf x := by
    have hfun : (fun y => (Φ k y + Ψ k y) - (Φinf y + Ψinf y))
        = (fun y => Φ k y - Φinf y) + (fun y => Ψ k y - Ψinf y) := by
      funext y
      change (Φ k y + Ψ k y) - (Φinf y + Ψinf y) = (Φ k y - Φinf y) + (Ψ k y - Ψinf y)
      abel
    have heq : mapDerivNorm r (fun z => Φ k z + Ψ k z) (fun z => Φinf z + Ψinf z) x
        = ‖iteratedFDeriv ℝ r ((fun y => Φ k y - Φinf y) + (fun y => Ψ k y - Ψinf y)) x‖ := by
      rw [show mapDerivNorm r (fun z => Φ k z + Ψ k z) (fun z => Φinf z + Ψinf z) x
          = ‖iteratedFDeriv ℝ r (fun y => (Φ k y + Ψ k y) - (Φinf y + Ψinf y)) x‖ from rfl, hfun]
    rw [heq, iteratedFDeriv_add_apply
      (((hΦc k).sub hΦic).contDiffAt.of_le (by exact_mod_cast le_top))
      (((hΨc k).sub hΨic).contDiffAt.of_le (by exact_mod_cast le_top))]
    exact norm_add_le _ _
  calc mapDerivNorm r (fun z => Φ k z + Ψ k z) (fun z => Φinf z + Ψinf z) x
      ≤ mapDerivNorm r (Φ k) Φinf x + mapDerivNorm r (Ψ k) Ψinf x := hsplit
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        · exact hk1 k (le_trans (le_max_left _ _) hk) r hr x hx
        · exact hk2 k (le_trans (le_max_right _ _) hk) r hr x hx
    _ = ε := by ring

/-- **`C^∞`-on-compacts convergence is closed under subtraction.**  Lets the
covariant-tower induction extract `s_{p+1} = towerStep − Σ corrections` from the
directional step and the (lower-level) correction convergences. -/
theorem MapCInfConvOnCompacts.sub {U : Set E} {Φ Ψ : ℕ → E → F} {Φinf Ψinf : E → F}
    (hΦ : MapCInfConvOnCompacts U Φ Φinf) (hΨ : MapCInfConvOnCompacts U Ψ Ψinf)
    (hΦc : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (Φ k)) (hΦic : ContDiff ℝ (∞ : WithTop ℕ∞) Φinf)
    (hΨc : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (Ψ k)) (hΨic : ContDiff ℝ (∞ : WithTop ℕ∞) Ψinf) :
    MapCInfConvOnCompacts U (fun k z => Φ k z - Ψ k z) (fun z => Φinf z - Ψinf z) := by
  intro K hK hKU p ε hε
  obtain ⟨k1, hk1⟩ := hΦ K hK hKU p (ε / 2) (by positivity)
  obtain ⟨k2, hk2⟩ := hΨ K hK hKU p (ε / 2) (by positivity)
  refine ⟨max k1 k2, fun k hk r hr x hx => ?_⟩
  have hsplit : mapDerivNorm r (fun z => Φ k z - Ψ k z) (fun z => Φinf z - Ψinf z) x
      ≤ mapDerivNorm r (Φ k) Φinf x + mapDerivNorm r (Ψ k) Ψinf x := by
    have hfun : (fun y => (Φ k y - Ψ k y) - (Φinf y - Ψinf y))
        = (fun y => Φ k y - Φinf y) - (fun y => Ψ k y - Ψinf y) := by
      funext y
      change (Φ k y - Ψ k y) - (Φinf y - Ψinf y) = (Φ k y - Φinf y) - (Ψ k y - Ψinf y)
      abel
    have heq : mapDerivNorm r (fun z => Φ k z - Ψ k z) (fun z => Φinf z - Ψinf z) x
        = ‖iteratedFDeriv ℝ r ((fun y => Φ k y - Φinf y) - (fun y => Ψ k y - Ψinf y)) x‖ := by
      rw [show mapDerivNorm r (fun z => Φ k z - Ψ k z) (fun z => Φinf z - Ψinf z) x
          = ‖iteratedFDeriv ℝ r (fun y => (Φ k y - Ψ k y) - (Φinf y - Ψinf y)) x‖ from rfl, hfun]
    rw [heq, iteratedFDeriv_sub_apply
      (((hΦc k).sub hΦic).contDiffAt.of_le (by exact_mod_cast le_top))
      (((hΨc k).sub hΨic).contDiffAt.of_le (by exact_mod_cast le_top))]
    exact norm_sub_le _ _
  calc mapDerivNorm r (fun z => Φ k z - Ψ k z) (fun z => Φinf z - Ψinf z) x
      ≤ mapDerivNorm r (Φ k) Φinf x + mapDerivNorm r (Ψ k) Ψinf x := hsplit
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        · exact hk1 k (le_trans (le_max_left _ _) hk) r hr x hx
        · exact hk2 k (le_trans (le_max_right _ _) hk) r hr x hx
    _ = ε := by ring

/-- **`C^∞`-on-compacts convergence is closed under multiplication by a fixed
smooth scalar field.**  If `Φₖ → Φ_∞` in `C^∞`-on-compacts (scalar, all `C^∞`) and
`g` is `C^∞`, then `g · Φₖ → g · Φ_∞` in `C^∞`-on-compacts.  This is the closure
the covariant-tower induction needs for the (fixed `gRef`-Christoffel) correction
terms.  Proof: Leibniz (`norm_iteratedFDeriv_mul_le`) bounds `mapDerivNorm r
(g·Φₖ) (g·Φ_∞)` by `∑_{i≤r} C(r,i)‖∇ⁱg‖·mapDerivNorm (r-i) Φₖ Φ_∞`, then the fixed
`‖∇ⁱg‖` are bounded on the compact and the difference norms vanish. -/
theorem MapCInfConvOnCompacts.mulLeft {U : Set E} {Φ : ℕ → E → ℝ} {Φlim : E → ℝ}
    (h : MapCInfConvOnCompacts U Φ Φlim) {g : E → ℝ} (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hΦc : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (Φ k)) (hΦic : ContDiff ℝ (∞ : WithTop ℕ∞) Φlim) :
    MapCInfConvOnCompacts U (fun k z => g z * Φ k z) (fun z => g z * Φlim z) := by
  intro K hK hKU p ε hε
  obtain ⟨Bg, hBg0, hBg⟩ : ∃ Bg : ℝ, 0 ≤ Bg ∧ ∀ i ≤ p, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i g x‖ ≤ Bg := by
    have hbd : ∀ i : ℕ, ∃ B : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i g x‖ ≤ B := by
      intro i
      obtain ⟨B, hB⟩ := hK.bddAbove_image
        (hg.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)).norm.continuousOn
      exact ⟨B, fun x hx => hB ⟨x, hx, rfl⟩⟩
    choose B hB using hbd
    refine ⟨∑ i ∈ Finset.range (p + 1), |B i|, Finset.sum_nonneg (fun _ _ => abs_nonneg _),
      fun i hi x hx => ?_⟩
    calc ‖iteratedFDeriv ℝ i g x‖ ≤ B i := hB i x hx
      _ ≤ |B i| := le_abs_self _
      _ ≤ ∑ j ∈ Finset.range (p + 1), |B j| :=
          Finset.single_le_sum (f := fun j => |B j|) (fun j _ => abs_nonneg (B j))
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  obtain ⟨k0, hk0⟩ := h K hK hKU p (ε / (2 ^ p * Bg + 1)) (by positivity)
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  have hle : mapDerivNorm r (fun z => g z * Φ k z) (fun z => g z * Φlim z) x
      ≤ ∑ i ∈ Finset.range (r + 1),
        (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i g x‖ * mapDerivNorm (r - i) (Φ k) Φlim x := by
    have hfun : (fun y => g y * Φ k y - g y * Φlim y) = (fun y => g y * (Φ k y - Φlim y)) := by
      funext y; ring
    have hfeq : mapDerivNorm r (fun z => g z * Φ k z) (fun z => g z * Φlim z) x
        = ‖iteratedFDeriv ℝ r (fun y => g y * (Φ k y - Φlim y)) x‖ := by
      rw [show mapDerivNorm r (fun z => g z * Φ k z) (fun z => g z * Φlim z) x
          = ‖iteratedFDeriv ℝ r (fun y => g y * Φ k y - g y * Φlim y) x‖ from rfl, hfun]
    rw [hfeq]
    exact norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := g) (g := fun y => Φ k y - Φlim y)
      hg ((hΦc k).sub hΦic) x (by exact_mod_cast le_top)
  refine hle.trans ?_
  have hstep : ∀ i ∈ Finset.range (r + 1),
      (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i g x‖ * mapDerivNorm (r - i) (Φ k) Φlim x
        ≤ (r.choose i : ℝ) * (Bg * (ε / (2 ^ p * Bg + 1))) := by
    intro i hi
    have hi' : i ≤ p := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hr
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul (hBg i hi' x hx) (hk0 k hk (r - i) (by omega) x hx)
      (mapDerivNorm_nonneg _ _ _ _) hBg0
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_mul,
    (by exact_mod_cast Nat.sum_range_choose r :
      (∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ)) = 2 ^ r)]
  have hD : (0:ℝ) < 2 ^ p * Bg + 1 := by positivity
  have h2r : (2:ℝ) ^ r ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hr
  rw [show (2:ℝ) ^ r * (Bg * (ε / (2 ^ p * Bg + 1)))
      = 2 ^ r * Bg * ε / (2 ^ p * Bg + 1) from by ring, div_le_iff₀ hD]
  nlinarith [mul_nonneg (mul_nonneg hε.le (sub_nonneg.mpr h2r)) hBg0, hε.le]

/-- **Finite sums of `C^∞`-on-compacts convergent families converge.**  The
`Finset` fold of `MapCInfConvOnCompacts.add` — the form the covariant-tower
induction uses for the Christoffel correction sums (over the slot index and the
frame index). -/
theorem MapCInfConvOnCompacts.sum {ι : Type*} {U : Set E} (s : Finset ι)
    {Φ : ι → ℕ → E → F} {Φinf : ι → E → F}
    (h : ∀ i, MapCInfConvOnCompacts U (Φ i) (Φinf i))
    (hc : ∀ i k, ContDiff ℝ (∞ : WithTop ℕ∞) (Φ i k))
    (hic : ∀ i, ContDiff ℝ (∞ : WithTop ℕ∞) (Φinf i)) :
    MapCInfConvOnCompacts U (fun k z => ∑ i ∈ s, Φ i k z) (fun z => ∑ i ∈ s, Φinf i z) := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro K hK hKU p ε hε
    refine ⟨0, fun k _ r _ x _ => ?_⟩
    simp only [Finset.sum_empty, mapDerivNorm, sub_self, iteratedFDeriv_fun_zero,
      Pi.zero_apply, norm_zero]
    exact hε.le
  | insert a t hat ih =>
    rw [show (fun k z => ∑ i ∈ insert a t, Φ i k z)
          = (fun k z => Φ a k z + ∑ i ∈ t, Φ i k z) from by
            funext k z; rw [Finset.sum_insert hat],
      show (fun z => ∑ i ∈ insert a t, Φinf i z)
          = (fun z => Φinf a z + ∑ i ∈ t, Φinf i z) from by
            funext z; rw [Finset.sum_insert hat]]
    exact MapCInfConvOnCompacts.add (h a) ih (fun k => hc a k) (hic a)
      (fun k => ContDiff.sum (fun i _ => hc i k)) (ContDiff.sum (fun i _ => hic i))

/-- **Locality of `C^∞`-on-compacts convergence.**  Convergence on an OPEN set `U`
depends only on the maps' restriction to `U`: replacing each `Φ k` and `Φinf` by
maps agreeing with them on `U` preserves `MapCInfConvOnCompacts U`.  (`mapDerivNorm`
is built from `iteratedFDeriv`, which is local, so on a compact `K ⊆ U` the
order-`r` norms are unchanged.)  This is what lets the covariant-tower induction
transfer convergence across a step recursion that only holds where the chosen
global sections agree with the local coordinate frame. -/
theorem MapCInfConvOnCompacts.congr {U : Set E} {Φ Φ' : ℕ → E → F} {Φinf Φ'inf : E → F}
    (h : MapCInfConvOnCompacts U Φ Φinf) (hU : IsOpen U)
    (hΦ : ∀ k, Set.EqOn (Φ' k) (Φ k) U) (hΦinf : Set.EqOn Φ'inf Φinf U) :
    MapCInfConvOnCompacts U Φ' Φ'inf := by
  intro K hK hKU p ε hε
  obtain ⟨k0, hk0⟩ := h K hK hKU p ε hε
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have heq : (fun y => Φ' k y - Φ'inf y) =ᶠ[nhds x] (fun y => Φ k y - Φinf y) := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    rw [hΦ k hy, hΦinf hy]
  have hval : mapDerivNorm r (Φ' k) Φ'inf x = mapDerivNorm r (Φ k) Φinf x := by
    simp only [mapDerivNorm]
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ heq r).eq_of_nhds]
  rw [hval]
  exact hk0 k hk r hr x hx

/-- **Eventual locality of `C^∞`-on-compacts convergence.**  Replacing the
sequence maps by maps that agree on the open convergence set from some index
onward preserves the same limit.  This is the tail-stable form needed when a
finite slot is eventually live or eventually dead. -/
theorem MapCInfConvOnCompacts.congr_eventually
    {U : Set E} {Φ Φ' : ℕ → E → F} {Φinf Φ'inf : E → F}
    (h : MapCInfConvOnCompacts U Φ Φinf) (hU : IsOpen U)
    (hΦ : ∀ᶠ k in Filter.atTop, Set.EqOn (Φ' k) (Φ k) U)
    (hΦinf : Set.EqOn Φ'inf Φinf U) :
    MapCInfConvOnCompacts U Φ' Φ'inf := by
  intro K hK hKU p ε hε
  obtain ⟨k0, hk0⟩ := h K hK hKU p ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hΦ
  refine ⟨max k0 N, fun k hk r hr x hx => ?_⟩
  have hk0k : k0 ≤ k := (Nat.le_max_left k0 N).trans hk
  have hNk : N ≤ k := (Nat.le_max_right k0 N).trans hk
  have hxU : x ∈ U := hKU hx
  have heq : (fun y => Φ' k y - Φ'inf y) =ᶠ[nhds x]
      (fun y => Φ k y - Φinf y) := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    rw [hN k hNk hy, hΦinf hy]
  have hval : mapDerivNorm r (Φ' k) Φ'inf x = mapDerivNorm r (Φ k) Φinf x := by
    simp only [mapDerivNorm]
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ heq r).eq_of_nhds]
  rw [hval]
  exact hk0 k hk0k r hr x hx

end HCGCompactness
end DifferentialGeometry

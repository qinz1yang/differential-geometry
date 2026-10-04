import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarLevelTorus
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspBoundaryInverse
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspHeightDifferential
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspMetricEquivalence
import DifferentialGeometry.Geometry.Connection.Hessian.SmoothApproximation

/-!
# `C²` smoothing of the collar height (F-e, row E8, the Z contract of the review, D9)

For a cusp embedding `e : CuspEmbedding W g K δ X` with `K ≥ 1` let `ζ = z ∘ e⁻¹` be the collar
height (`ζ y = (invFunOn e.toFun cuspDomain y).2.val 0`).

* `CuspEmbedding.contMDiffAt_height_of_pos`: `ζ` is `C^{K+1}` at every point `e p` of positive
  height (Codex X87's finite inverse patches).
* `CuspEmbedding.exists_smooth_height_C2` (row E8 in the Z contract): for every `ε > 0` there is a
  smooth `η : W → ℝ` such that on the compact band `2 ≤ z ≤ 98` the SAME `η` satisfies
  `|η - ζ| < ε`, `|d(η ∘ e)(v) - dz(v)| ≤ ε |v|_H` and
  `|Hess_g(η - ζ)(de v, de w)| ≤ ε |v|_H |w|_H`, with the EXISTING Hessian
  `(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)`
  (`Geometry/Connection/Hessian.lean`). It is a `C²` approximation of the scalar `ζ`; neither `e`
  nor `g` is smoothed. The first two clauses are BDY-FILL's `Z_smooth_height_C1`.

Proof: `exists_smooth_approx_C2_on_compact` on `U = e (1 < z < 99)` and `B = e (2 ≤ z ≤ 98)`, then
`|de v|_g ≤ √(1 + |δ|) |v|_H` (`CuspEmbedding.pullback_inner_le_one_add_mul`) and
`dζ (de v) = dz(v)` (`CuspEmbedding.mfderiv_height_invFunOn_mfderiv`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

/-- The collar height is `C^{K+1}` at every point of positive height. -/
theorem CuspEmbedding.contMDiffAt_height_of_pos (e : CuspEmbedding W g K δ X)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (hz : 0 < p.2.val 0) :
    ContMDiffAt W.model 𝓘(ℝ, ℝ) (K + 1) (fun y => (invFunOn e.toFun cuspDomain y).2.val 0)
      (e.toFun p) := by
  obtain ⟨Φ, hpΦ, hΦU, heq, -, -⟩ := e.exists_finiteInteriorPatch hp hz
  have htarget : e.toFun p ∈ Φ.target := by
    rw [heq hpΦ]
    exact Φ.map_source' hpΦ
  have hinv : ∀ y ∈ Φ.target, invFunOn e.toFun cuspDomain y = Φ.invFun y := by
    intro y hy
    have hs : Φ.invFun y ∈ Φ.source := Φ.map_target' hy
    have hey : e.toFun (Φ.invFun y) = y := (heq hs).trans (Φ.right_inv' hy)
    calc invFunOn e.toFun cuspDomain y
        = invFunOn e.toFun cuspDomain (e.toFun (Φ.invFun y)) := by rw [hey]
      _ = Φ.invFun y := e.injOn_cuspDomain.leftInvOn_invFunOn (hΦU hs)
  have hsymm : ContMDiffAt W.model halfCollarModel (K + 1) Φ.invFun (e.toFun p) :=
    Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds htarget)
  have hheight : ContMDiff halfCollarModel 𝓘(ℝ, ℝ) (K + 1)
      (fun q : CuspHalfSpace => q.2.val 0) :=
    (contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd).of_le (by exact_mod_cast le_top)
  refine ((hheight _).comp _ hsymm).congr_of_eventuallyEq ?_
  filter_upwards [Φ.open_target.mem_nhds htarget] with y hy
  change (invFunOn e.toFun cuspDomain y).2.val 0 = (Φ.invFun y).2.val 0
  rw [hinv y hy]

/-- **Row E8 in the Z contract (D9).** A smooth `η` whose restriction to the compact band
`2 ≤ z ≤ 98` is `C⁰`-, `C¹`- and Hessian-close to the collar height, all with the same `η`. -/
theorem CuspEmbedding.exists_smooth_height_C2 (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ η
        (e.toFun '' {p : CuspHalfSpace | 1 < p.2.val 0 ∧ p.2.val 0 < 99}) ∧
      ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
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
              Real.sqrt (e.cusp.metric.inner p w w) := by
  set ζ : W.Carrier → ℝ := fun y => (invFunOn e.toFun cuspDomain y).2.val 0 with hζ
  set S : Set CuspHalfSpace := {p | 1 < p.2.val 0 ∧ p.2.val 0 < 99} with hS
  have hSd : S ⊆ cuspDomain := fun p hp => by
    change p.2.val 0 < cuspDepth
    exact hp.2.trans (by norm_num [cuspDepth])
  have hSo : IsOpen S := by
    change IsOpen ((fun p : CuspHalfSpace => p.2.val 0) ⁻¹' Ioo 1 99)
    exact isOpen_Ioo.preimage (by fun_prop)
  have hUo : IsOpen (e.toFun '' S) :=
    e.isOpen_image_of_pos hSo hSd fun p hp => one_pos.trans hp.1
  have hUi : e.toFun '' S ⊆ W.model.interior W.Carrier := by
    rintro _ ⟨p, hp, rfl⟩
    refine (W.model.isInteriorPoint_iff_not_isBoundaryPoint _).mpr fun hb => ?_
    have h0 := (e.boundary_preimage (hSd hp)).mp hb
    linarith [hp.1]
  have hζ2 : ContMDiffOn W.model 𝓘(ℝ, ℝ) 2 ζ (e.toFun '' S) := by
    rintro _ ⟨p, hp, rfl⟩
    have h := e.contMDiffAt_height_of_pos (hSd hp) (one_pos.trans hp.1)
    exact (h.of_le (by exact_mod_cast Nat.succ_le_succ hK)).contMDiffWithinAt
  set B : Set W.Carrier := e.toFun '' {p : CuspHalfSpace | 2 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 98}
    with hB
  have hBc : IsCompact B := e.isCompact_image_band (by norm_num [cuspDepth])
  have hBU : B ⊆ e.toFun '' S :=
    image_mono fun p hp => ⟨by linarith [hp.1], by linarith [hp.2]⟩
  set c : ℝ := Real.sqrt (1 + |δ|) with hc
  have hc1 : 1 ≤ c := by
    rw [hc, Real.one_le_sqrt]
    linarith [abs_nonneg δ]
  have hcc : c * c = 1 + |δ| := Real.mul_self_sqrt (by positivity)
  set ε' : ℝ := ε / (1 + |δ|) with hε'
  have hε'0 : 0 < ε' := div_pos hε (by positivity)
  have hεcc : ε' * c * c = ε := by
    rw [mul_assoc, hcc, hε']
    exact div_mul_cancel₀ ε (by positivity)
  have hεc : ε' * c ≤ ε := by
    calc ε' * c = ε' * c * 1 := (mul_one _).symm
      _ ≤ ε' * c * c := mul_le_mul_of_nonneg_left hc1 (by positivity)
      _ = ε := hεcc
  obtain ⟨η, hη, hηB⟩ := exists_smooth_approx_C2_on_compact g hUo hUi hζ2 hBc hBU hε'0
  refine ⟨η, hη, hη.contMDiffOn, fun p hp hz2 hz98 => ?_⟩
  obtain ⟨h0, h1, h2⟩ := hηB _ ⟨p, ⟨hz2, hz98⟩, rfl⟩
  have hζp : ζ (e.toFun p) = p.2.val 0 := by
    simp only [hζ]
    rw [e.injOn_cuspDomain.leftInvOn_invFunOn hp]
  have hgH : ∀ v : TangentSpace halfCollarModel p,
      Real.sqrt (g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p v)) ≤
        c * Real.sqrt (e.cusp.metric.inner p v v) := by
    intro v
    rw [hc, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ((e.pullback_inner_le_one_add_mul hp v).trans ?_)
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self δ])
      (metric_inner_self_nonneg _ _ _)
  refine ⟨?_, fun v => ?_, fun v w => ?_⟩
  · rw [← hζp]
    exact h0.trans_le (div_le_self hε.le (by linarith [abs_nonneg δ]))
  · have hed : MDifferentiableAt halfCollarModel W.model e.toFun p :=
      (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hp)).mdifferentiableAt (by simp)
    have hηd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) η (e.toFun p) :=
      (hη _).mdifferentiableAt (by simp)
    have hζd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) ζ (e.toFun p) :=
      (e.contMDiffOn_height_invFunOn.contMDiffAt
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
          mul_le_mul_of_nonneg_left (hgH v) hε'0.le
      _ = (ε' * c) * Real.sqrt (e.cusp.metric.inner p v v) := by ring
      _ ≤ ε * Real.sqrt (e.cusp.metric.inner p v v) :=
          mul_le_mul_of_nonneg_right hεc (Real.sqrt_nonneg _)
  · calc _ ≤ ε' * Real.sqrt (g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
          (mfderiv halfCollarModel W.model e.toFun p v)) *
          Real.sqrt (g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p w)
            (mfderiv halfCollarModel W.model e.toFun p w)) := h2 _ _
      _ ≤ ε' * (c * Real.sqrt (e.cusp.metric.inner p v v)) *
          (c * Real.sqrt (e.cusp.metric.inner p w w)) := by
          gcongr
          · exact hgH v
          · exact hgH w
      _ = (ε' * c * c) * Real.sqrt (e.cusp.metric.inner p v v) *
          Real.sqrt (e.cusp.metric.inner p w w) := by ring
      _ = ε * Real.sqrt (e.cusp.metric.inner p v v) *
          Real.sqrt (e.cusp.metric.inner p w w) := by rw [hεcc]

end DifferentialGeometry.Geometry.Collapse

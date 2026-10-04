import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFirstExit
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspProductLowerApplications

/-!
# Slab first exit and the lower distortion of a cusp collar (F-f.L), boundary allowed

For a cusp embedding `e : CuspEmbedding W g K δ X`, a height `z₀` and `a` with `z₀ + a < 100`
(no lower bound on `z₀ - a`: the slab may contain the boundary `z = 0`):

* `CuspEmbedding.exists_slab_lift_of_pathELength_lt` (first exit, state-B-2b item (c)): a `C¹`
  curve starting in `e{|z - z₀| ≤ a/2}` with `g`-length `< √(1 - δ) a / 2` stays in
  `e{|z - z₀| < a}` and is `e ∘ c` with `c` a `C¹` curve of the cusp domain;
* `CuspEmbedding.frozen_le_riemannianEDistOf` (F-f.L): for heights within `a/2` of `z₀` and
  `d_g(e p, e p') < √(1 - δ) a / 2`,
  `d_g(e p, e p') ≥ √(1 - δ) e^{-a/2} √((z' - z)² + e^{-z₀} d_q(t, t')²)`.

Proof of the first exit: if the curve left `e{|z - z₀| < a}` at a time `t₁`, the reparametrized
curve on `[0, t₁]` would cost at least `√(1 - δ) a / 2`
(`CuspEmbedding.exists_exit_le_pathELength`).
F-f.L then applies the frozen lower length bound `CuspEmbedding.frozen_le_pathELength_comp` to the
lifts of almost minimizing curves.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Slab first exit.** A `C¹` curve starting at `e p`, `|z(p) - z₀| ≤ a/2`, `z₀ + a < 100`, of
`g`-length `< √(1 - δ) a / 2`, stays in `e{|z - z₀| < a}` and lifts to a `C¹` curve of the cusp
domain. -/
theorem CuspEmbedding.exists_slab_lift_of_pathELength_lt {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {γ : ℝ → W.Carrier}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) W.model 1 γ (Icc 0 1)) {z₀ a : ℝ} (hup : z₀ + a < cuspDepth)
    {p : CuspHalfSpace} (hp : |p.2.val 0 - z₀| ≤ a / 2) (h0 : γ 0 = e.toFun p) :
    letI : RiemannianBundle (fun x : W.Carrier => TangentSpace W.model x) :=
      ⟨g.toRiemannianMetric⟩
    pathELength W.model γ 0 1 < ENNReal.ofReal (Real.sqrt (1 - δ) * (a / 2)) →
    ∃ c : ℝ → CuspHalfSpace, ContMDiffOn 𝓘(ℝ, ℝ) halfCollarModel 1 c (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, c t ∈ cuspDomain ∧ |(c t).2.val 0 - z₀| < a) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, e.toFun (c t) = γ t := by
  let : RiemannianBundle (fun x : W.Carrier => TangentSpace W.model x) := ⟨g.toRiemannianMetric⟩
  intro hlen
  have hapos : 0 < a := by
    by_contra hle
    push Not at hle
    have : Real.sqrt (1 - δ) * (a / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (by linarith)
    rw [ENNReal.ofReal_of_nonpos this] at hlen
    exact absurd hlen (not_lt.mpr bot_le)
  set V : Set CuspHalfSpace := {q | z₀ - a < q.2.val 0 ∧ q.2.val 0 < z₀ + a} with hV
  have hVd : V ⊆ cuspDomain := fun q hq => lt_trans hq.2 hup
  obtain ⟨hpl, hpu⟩ := abs_le.mp hp
  have hpV : z₀ - a < p.2.val 0 ∧ p.2.val 0 < z₀ + a := ⟨by linarith, by linarith⟩
  have hin : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ e.toFun '' V := by
    intro t₁ ht₁
    by_contra hout
    have ht₁0 : 0 < t₁ := by
      rcases ht₁.1.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        rw [← heq, h0] at hout
        exact hout ⟨p, hpV, rfl⟩
    -- the curve reparametrized on `[0, t₁]`
    let f : ℝ → ℝ := fun t => t₁ * t
    have hfmaps : MapsTo f (Icc 0 1) (Icc 0 1) := fun t ht =>
      ⟨mul_nonneg ht₁0.le ht.1, by nlinarith [ht.2, ht₁.2, ht.1]⟩
    have hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 f := (contDiff_const.mul contDiff_id).contMDiff
    have hγf : ContMDiffOn 𝓘(ℝ, ℝ) W.model 1 (γ ∘ f) (Icc 0 1) :=
      hγ.comp hf.contMDiffOn hfmaps
    have hf0 : (γ ∘ f) 0 = e.toFun p := by simp [f, h0]
    have hf1 : (γ ∘ f) 1 ∉ e.toFun '' V := by simpa [f] using hout
    obtain ⟨q, -, hqside, hq⟩ := e.exists_exit_le_pathELength hγf hup hpV.1 hpV.2 hf0 hf1
    have hlenf : pathELength W.model (γ ∘ f) 0 1 ≤ pathELength W.model γ 0 1 := by
      have hmono : MonotoneOn f (Icc 0 1) := fun x _ y _ hxy => mul_le_mul_of_nonneg_left hxy
        ht₁0.le
      have hdiff : DifferentiableOn ℝ f (Icc 0 1) :=
        ((differentiable_id.const_mul t₁ : Differentiable ℝ fun t : ℝ => t₁ * t)).differentiableOn
      have hmd : MDifferentiableOn 𝓘(ℝ, ℝ) W.model γ (Icc (f 0) (f 1)) := by
        refine (hγ.mono ?_).mdifferentiableOn one_ne_zero
        simp only [f, mul_zero, mul_one]
        exact Icc_subset_Icc le_rfl ht₁.2
      rw [pathELength_comp_of_monotoneOn zero_le_one hmono hdiff hmd]
      simp only [f, mul_zero, mul_one]
      exact pathELength_mono le_rfl ht₁.2
    have hcost : Real.sqrt (1 - δ) * (a / 2) ≤
        Real.sqrt (1 - δ) * |q.2.val 0 - p.2.val 0| := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      rcases hqside with hq1 | hq2
      · rw [hq1, abs_of_neg (by linarith)]
        linarith
      · rw [hq2, abs_of_pos (by linarith)]
        linarith
    have := (ENNReal.ofReal_le_ofReal hcost).trans (hq.trans hlenf)
    exact absurd hlen (not_lt.mpr this)
  obtain ⟨c, hc, hcd, hce⟩ := e.exists_lift hγ fun t ht => image_mono hVd (hin t ht)
  refine ⟨c, hc, fun t ht => ⟨hcd ht, ?_⟩, hce⟩
  obtain ⟨q, hqV, hqγ⟩ := hin t ht
  have hcq : c t = q := e.injOn_cuspDomain (hcd ht) (hVd hqV) ((hce t ht).trans hqγ.symm)
  rw [hcq]
  exact abs_lt.mpr ⟨by linarith [hqV.1], by linarith [hqV.2]⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **F-f.L: lower distortion of a cusp collar against the frozen product, boundary allowed.**
For heights within `a/2` of `z₀`, `z₀ + a < 100`, and `d_g(e p, e p') < √(1 - δ) a / 2`:
`d_g(e p, e p') ≥ √(1 - δ) e^{-a/2} √((z' - z)² + e^{-z₀} d_q(t, t')²)`. -/
theorem CuspEmbedding.frozen_le_riemannianEDistOf {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {p p' : CuspHalfSpace} {z₀ a : ℝ} (hup : z₀ + a < cuspDepth)
    (hp : |p.2.val 0 - z₀| ≤ a / 2) (hp' : |p'.2.val 0 - z₀| ≤ a / 2)
    (hd : riemannianEDistOf g (e.toFun p) (e.toFun p') <
      ENNReal.ofReal (Real.sqrt (1 - δ) * (a / 2))) :
    ENNReal.ofReal (Real.sqrt (1 - δ) * (Real.exp (-a / 2) *
        Real.sqrt ((p'.2.val 0 - p.2.val 0) ^ 2 +
          Real.exp (-z₀) * (riemannianEDistOf e.cusp.torusMetric p.1 p'.1).toReal ^ 2))) ≤
      riemannianEDistOf g (e.toFun p) (e.toFun p') := by
  let : RiemannianBundle (fun x : W.Carrier => TangentSpace W.model x) := ⟨g.toRiemannianMetric⟩
  refine le_of_forall_gt fun r hr => ?_
  have hr' : riemannianEDistOf g (e.toFun p) (e.toFun p') <
      min r (ENNReal.ofReal (Real.sqrt (1 - δ) * (a / 2))) := lt_min hr hd
  change Manifold.riemannianEDist W.model (e.toFun p) (e.toFun p') < _ at hr'
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr'
  obtain ⟨c, hc, hcd, hce⟩ := e.exists_slab_lift_of_pathELength_lt hγ hup hp hγ0
    (hlen.trans_le (min_le_right _ _))
  have hc0 : c 0 = p := e.injOn_cuspDomain (hcd 0 ⟨le_rfl, zero_le_one⟩).1
    (lt_of_le_of_lt (by have := abs_le.mp hp; linarith) hup)
    ((hce 0 ⟨le_rfl, zero_le_one⟩).trans hγ0)
  have hc1 : c 1 = p' := e.injOn_cuspDomain (hcd 1 ⟨zero_le_one, le_rfl⟩).1
    (lt_of_le_of_lt (by have := abs_le.mp hp'; linarith) hup)
    ((hce 1 ⟨zero_le_one, le_rfl⟩).trans hγ1)
  have hlow := e.frozen_le_pathELength_comp hc (fun t ht => (hcd t ht).1)
    (fun t ht => (hcd t ht).2.le)
  rw [hc0, hc1] at hlow
  calc _ ≤ pathELength W.model (e.toFun ∘ c) 0 1 := hlow
    _ = pathELength W.model γ 0 1 := pathELength_congr fun t ht => hce t ht
    _ < min r _ := hlen
    _ ≤ r := min_le_left _ _

end DifferentialGeometry.Geometry.Collapse

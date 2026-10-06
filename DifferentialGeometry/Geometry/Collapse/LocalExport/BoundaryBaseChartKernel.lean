import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# G17 kernel (a): a base chart `ℝᵏ → H` of a marked base piece from the record of one chart
(S-BAUG-D2)

The whole-fibre layer `BoundaryWholeFiberSpecV2` asks, at every point `y` of a base `B`, a smooth
immersed topological embedding `σ : ℝᵏ → H` onto a relatively open piece `B ∩ O` of `B` with
`σ 0 = y`. Closed twin: `Gaf02CircleBasesSpec_BAS.base_chart`. The record of ONE marked chart `i`
of a stage is `(κ, σ₀, Wb, Mk)`: the coordinate `κ = κ_i : H →L ℝᵏ` (linear), the marked open set
`Mk = Mk_i`, the BIG final base `Wb` and the smooth chart inverse `σ₀ = Θ ∘ φ_i` on `ball 0 r`
with `σ₀(b) ∈ Wb ∩ Mk`, `κ(σ₀ b) = b`, and `σ₀(κ w) = w` for `w ∈ Wb ∩ Mk` (so `κ` maps
`Wb ∩ Mk` into `ball 0 r`). The stage base is `B = Wb ∩ O'` with `O'` open in `H`.

* `univBall_data_BAUGD`: `univBall c ε` parametrizes the ball `ball c ε` by the whole space `ℝᵏ`
  (smooth embedding with injective differential, `0 ↦ c`);
* `exists_radius_baseChart_BAUGD`: a radius `ε` with `ball (κ y) ε ⊆ ball 0 r` on which `σ₀` stays
  in `O'`;
* `baseChart_of_record_BAUGD`: for `y ∈ B ∩ Mk` (`B = Wb ∩ O'`) and any such radius,
  `σ := σ₀ ∘ univBall (κ y) ε` is smooth, an embedding with injective differential, `σ 0 = y`,
  `κ ∘ σ = univBall (κ y) ε`, and its range is exactly `B ∩ (Mk ∩ κ⁻¹ ball (κ y) ε)`, a
  relatively open piece of `B`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Topology
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Collapse

/-- **The whole space parametrizes a ball**: `univBall c ε` is smooth, an embedding with
injective differential, sends `0` to `c` and has range `ball c ε`. -/
theorem univBall_data_BAUGD {k : ℕ} (c : EuclideanSpace ℝ (Fin k)) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (OpenPartialHomeomorph.univBall c ε) ∧
      IsEmbedding (OpenPartialHomeomorph.univBall c ε) ∧
      range (OpenPartialHomeomorph.univBall c ε) = ball c ε ∧
      OpenPartialHomeomorph.univBall c ε 0 = c ∧
      ∀ x, Injective (fderiv ℝ (OpenPartialHomeomorph.univBall c ε) x) := by
  set e := OpenPartialHomeomorph.univBall c ε with he
  have hsrc : e.source = univ := OpenPartialHomeomorph.univBall_source _ _
  have htgt : e.target = ball c ε := OpenPartialHomeomorph.univBall_target _ hε
  have hrange : range e = ball c ε := by
    rw [← image_univ, ← hsrc, e.image_source_eq_target, htgt]
  have hesm : ContDiff ℝ ∞ e := OpenPartialHomeomorph.contDiff_univBall
  have heb : ∀ x, e x ∈ ball c ε := fun x => hrange ▸ mem_range_self x
  have hesymm : ContDiffOn ℝ ∞ e.symm (ball c ε) :=
    OpenPartialHomeomorph.contDiffOn_univBall_symm
  refine ⟨hesm, (OpenPartialHomeomorph.isOpenEmbedding e hsrc).toIsEmbedding, hrange,
    OpenPartialHomeomorph.univBall_apply_zero _ _, fun x => ?_⟩
  have hde : DifferentiableAt ℝ e x := (hesm.differentiable (by simp)) x
  have hs : DifferentiableAt ℝ e.symm (e x) :=
    (hesymm.differentiableOn (by simp) (e x) (heb x)).differentiableAt
      (isOpen_ball.mem_nhds (heb x))
  have h2 : HasFDerivAt (e.symm ∘ e) ((fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x)) x :=
    (hs.hasFDerivAt).comp x hde.hasFDerivAt
  have h3 : (e.symm ∘ e) = id := funext fun z => e.left_inv (by rw [hsrc]; trivial)
  rw [h3] at h2
  have hinv : (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) = ContinuousLinearMap.id ℝ _ :=
    h2.fderiv.symm.trans fderiv_id
  intro u v huv
  have h4 := congrArg (fun L => L u) hinv
  have h5 := congrArg (fun L => L v) hinv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h4 h5
  rw [← h4, ← h5]
  exact congrArg (fderiv ℝ e.symm (e x)) huv

/-- **A radius for the chart at `y`**: a ball around `κ y` inside `ball 0 r` on which `σ₀` stays
in `O'`. -/
theorem exists_radius_baseChart_BAUGD {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {k : ℕ} (σ₀ : EuclideanSpace ℝ (Fin k) → H) (O' : Set H) {r : ℝ} (hO' : IsOpen O')
    (ha : ContDiffOn ℝ ∞ σ₀ (ball (0 : EuclideanSpace ℝ (Fin k)) r))
    {b₀ : EuclideanSpace ℝ (Fin k)} (hb₀ : b₀ ∈ ball (0 : EuclideanSpace ℝ (Fin k)) r)
    (hO : σ₀ b₀ ∈ O') :
    ∃ ε : ℝ, 0 < ε ∧ ball b₀ ε ⊆ ball (0 : EuclideanSpace ℝ (Fin k)) r ∧
      ∀ b ∈ ball b₀ ε, σ₀ b ∈ O' := by
  have hcont : ContinuousAt σ₀ b₀ := ha.continuousOn.continuousAt (isOpen_ball.mem_nhds hb₀)
  have hpre : σ₀ ⁻¹' O' ∈ nhds b₀ := hcont.preimage_mem_nhds (hO'.mem_nhds hO)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hpre
    (isOpen_ball.mem_nhds hb₀))
  exact ⟨ε, hε, fun b hb' => (hball hb').2, fun b hb' => (hball hb').1⟩

/-- **A base chart from the record of one marked chart** (see the module docstring), at any radius
`ε` for which `ball (κ y) ε ⊆ ball 0 r` and `σ₀` stays in `O'` on the ball. -/
theorem baseChart_of_record_BAUGD {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {k : ℕ} (κ : H →L[ℝ] EuclideanSpace ℝ (Fin k)) (σ₀ : EuclideanSpace ℝ (Fin k) → H)
    (Wb Mk O' : Set H) {r : ℝ}
    (ha : ContDiffOn ℝ ∞ σ₀ (ball (0 : EuclideanSpace ℝ (Fin k)) r))
    (hb : ∀ b ∈ ball (0 : EuclideanSpace ℝ (Fin k)) r, σ₀ b ∈ Wb ∩ Mk ∧ κ (σ₀ b) = b)
    (hc : ∀ y ∈ Wb ∩ Mk,
      κ y ∈ ball (0 : EuclideanSpace ℝ (Fin k)) r ∧ σ₀ (κ y) = y)
    {y : H} (hy : y ∈ Wb ∩ O' ∩ Mk) {ε : ℝ} (hε : 0 < ε)
    (hsub : ball (κ y) ε ⊆ ball (0 : EuclideanSpace ℝ (Fin k)) r)
    (hO : ∀ b ∈ ball (κ y) ε, σ₀ b ∈ O') :
    σ₀ (OpenPartialHomeomorph.univBall (κ y) ε 0) = y ∧
      ContDiff ℝ ∞ (σ₀ ∘ OpenPartialHomeomorph.univBall (κ y) ε) ∧
      IsEmbedding (σ₀ ∘ OpenPartialHomeomorph.univBall (κ y) ε) ∧
      (∀ x, Injective (fderiv ℝ (σ₀ ∘ OpenPartialHomeomorph.univBall (κ y) ε) x)) ∧
      (∀ x, κ (σ₀ (OpenPartialHomeomorph.univBall (κ y) ε x)) =
        OpenPartialHomeomorph.univBall (κ y) ε x) ∧
      range (σ₀ ∘ OpenPartialHomeomorph.univBall (κ y) ε) =
        (Wb ∩ O') ∩ (Mk ∩ κ ⁻¹' ball (κ y) ε) := by
  obtain ⟨⟨hyW, hyO⟩, hyM⟩ := hy
  obtain ⟨hκy, hσy⟩ := hc y ⟨hyW, hyM⟩
  obtain ⟨hesm, hemb, hrange, he0, hde⟩ := univBall_data_BAUGD (κ y) hε
  set e := OpenPartialHomeomorph.univBall (κ y) ε with he
  have heb : ∀ x, e x ∈ ball (κ y) ε := fun x => hrange ▸ mem_range_self x
  have hκσ : ∀ x, κ (σ₀ (e x)) = e x := fun x => (hb _ (hsub (heb x))).2
  have hσsm : ContDiff ℝ ∞ (σ₀ ∘ e) :=
    contDiffOn_univ.mp (ha.comp (hesm.contDiffOn (s := univ)) (fun x _ => hsub (heb x)))
  refine ⟨by rw [he0, hσy], hσsm, ?_, ?_, fun x => hκσ x, ?_⟩
  · -- embedding: `κ ∘ (σ₀ ∘ e) = e` is an embedding
    refine IsEmbedding.of_comp hσsm.continuous κ.continuous ?_
    have : (⇑κ ∘ σ₀ ∘ ⇑e) = ⇑e := funext hκσ
    rw [this]
    exact hemb
  · -- injective differential: `κ ∘ D(σ₀ ∘ e) = De` and `De` is injective
    intro x u v huv
    have hdσ : DifferentiableAt ℝ (σ₀ ∘ e) x := (hσsm.differentiable (by simp)) x
    have hcomp : HasFDerivAt (κ ∘ (σ₀ ∘ e)) (κ.comp (fderiv ℝ (σ₀ ∘ e) x)) x :=
      κ.hasFDerivAt.comp x hdσ.hasFDerivAt
    have hκe : (κ ∘ (σ₀ ∘ e)) = e := funext hκσ
    rw [hκe] at hcomp
    have h1 : fderiv ℝ e x = κ.comp (fderiv ℝ (σ₀ ∘ e) x) := hcomp.fderiv
    apply hde x
    rw [h1]
    exact congrArg κ huv
  · -- range
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      have hx := heb x
      have hmem := hb _ (hsub hx)
      refine ⟨⟨hmem.1.1, hO _ hx⟩, hmem.1.2, ?_⟩
      change κ (σ₀ (e x)) ∈ ball (κ y) ε
      rw [hκσ]
      exact hx
    · rintro ⟨⟨hwW, hwO⟩, hwM, hwκ⟩
      obtain ⟨-, hw⟩ := hc w ⟨hwW, hwM⟩
      have hκw : κ w ∈ range e := by rw [hrange]; exact hwκ
      obtain ⟨x, hx⟩ := hκw
      refine ⟨x, ?_⟩
      change σ₀ (e x) = w
      rw [hx, hw]

end DifferentialGeometry.Geometry.Collapse

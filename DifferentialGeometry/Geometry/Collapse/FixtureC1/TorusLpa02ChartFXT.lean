import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusEll
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# LPA02 on the flat torus, part 1: small balls of the lattice torus (S-LPA02-TOR, G1)

Lane S-LPA02-TOR (suffix `_FXT`). Let `Λ` be a rectangular period lattice all of whose periods are
at least `f > 0`. Then the covering map `π : ℝ³ → T³_Λ` is injective on every Euclidean ball of
radius `≤ f/2` and a local isometry there. This file packages the facts needed to bind LPA02's
joint witness at a scale `s r` below the shortest period (regime S of
`TorusLpa02AtScaleFXT`):

* `latticeVec_norm_ge_FXT`, `torPi_inj_of_close_FXT`: nonzero translations are `≥ f` long and two
  points closer than `f` with the same image coincide;
* `dist_torPi_eq_FXT`: `‖y - y'‖ < f/2` gives `d(π y, π y') = ‖y - y'‖`;
* `torPi_image_ball_FXT`, `torPi_injOn_ball_FXT`: `π '' B(pt, R) = B(π pt, R)`, `R ≤ f/2`;
* `torChart_FXT`: `π` restricted to `B(pt, R)` as a `C^∞` partial diffeomorphism
  `E3 → T³_Λ` (the inverse is smooth because `π` is a local diffeomorphism);
* `euclidBallChart_FXT`, `exists_ballDiffeo_FXT`: `B(π pt, R) ≅ E3` by a partial diffeomorphism
  with source exactly the metric ball and target `univ` (LPA02's `Ψ` with `Ns = E3`);
* `klSmall_FXT`: a Kleiner–Lott `δ`-map `(T³_Λ, R⁻¹ d, π pt) → (E3, 0)` when `R ≤ δ f/4`
  (the ball of radius `R/δ` is isometric to a Euclidean ball: the map is the inverse lift).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric GC.MetricGeometry
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

section Chart

variable (Λ : TorusPeriods_FXC1) {f : ℝ} (hf0 : 0 < f) (hf : ∀ i, f ≤ Λ.L i)

include hf0 hf in
/-- A nontrivial lattice translation is at least `f` long. -/
theorem latticeVec_norm_ge_FXT (n : TorusGroup_FXC1 Λ) (hn : n ≠ 1) :
    f ≤ ‖latticeVec_FXC1 Λ n‖ := by
  by_contra hlt0
  have hlt := not_le.mp hlt0
  apply hn
  apply latticeVec_injective_FXC1 Λ
  rw [latticeVec_one_FXC1]
  ext i
  have h1 := abs_toInts_mul_le_norm_FXC1 Λ n i
  by_contra hne
  have hz : (n.toInts i : ℤ) ≠ 0 := by
    intro h0
    apply hne
    simp [latticeVec_apply_FXC1, h0]
  have h2 : (1 : ℝ) ≤ |((n.toInts i : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hz
  have h3 := hf i
  nlinarith [Λ.pos i]

include hf0 hf in
/-- Two points of `ℝ³` closer than `f` with the same image in the torus coincide. -/
theorem torPi_inj_of_close_FXT {y y' : E3} (h : ‖y - y'‖ < f)
    (he : torPi_FXC1 Λ y = torPi_FXC1 Λ y') : y = y' := by
  obtain ⟨n, hn⟩ := torPi_eq_iff_FXC1.mp he
  by_cases h1 : n = 1
  · subst h1
    rw [latticeVec_one_FXC1, add_zero] at hn
    exact hn.symm
  · exfalso
    have h2 := latticeVec_norm_ge_FXT Λ hf0 hf n h1
    have h3 : latticeVec_FXC1 Λ n = y' - y := by rw [hn]; abel
    rw [h3, ← norm_neg, neg_sub] at h2
    linarith

include hf0 hf in
/-- **Local isometry**: for `‖y - y'‖ < f/2` the torus distance is the Euclidean one. -/
theorem dist_torPi_eq_FXT {y y' : E3} (h : ‖y - y'‖ < f / 2) :
    dist (torPi_FXC1 Λ y) (torPi_FXC1 Λ y') = ‖y - y'‖ := by
  refine le_antisymm (dist_le_of_edist_le_FXC1 Λ _ _ _ (norm_nonneg _)
    (edist_torPi_le_FXC1 Λ y y')) ?_
  refine le_dist_of_ofReal_le_FXC1 Λ _ _ _ (le_edist_torPi_FXC1 Λ y y' _ fun n => ?_)
  by_cases h1 : n = 1
  · subst h1
    rw [latticeVec_one_FXC1, add_zero]
  · have h2 := latticeVec_norm_ge_FXT Λ hf0 hf n h1
    have e : latticeVec_FXC1 Λ n = (y - y') - (y - (y' + latticeVec_FXC1 Λ n)) := by abel
    have h3 := norm_sub_le (y - y') (y - (y' + latticeVec_FXC1 Λ n))
    rw [← e] at h3
    linarith


include hf0 hf in
theorem torPi_image_ball_FXT (pt : E3) {R : ℝ} (hRf : R ≤ f / 2) :
    torPi_FXC1 Λ '' ball pt R = ball (torPi_FXC1 Λ pt) R := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_ball] at hy ⊢
    rw [dist_eq_norm] at hy
    rw [dist_comm, dist_torPi_eq_FXT Λ hf0 hf (by rw [norm_sub_rev]; linarith)]
    rwa [norm_sub_rev]
  · intro hx
    rw [mem_ball, dist_comm] at hx
    obtain ⟨y, hy, hyn⟩ := exists_lift_of_dist_lt_FXC1 Λ pt x hx
    exact ⟨y, by rwa [mem_ball, dist_eq_norm, norm_sub_rev], hy⟩

include hf0 hf in
theorem torPi_injOn_ball_FXT (pt : E3) {R : ℝ} (hRf : R ≤ f / 2) :
    InjOn (torPi_FXC1 Λ) (ball pt R) := by
  intro y hy y' hy' he
  rw [mem_ball, dist_eq_norm] at hy hy'
  refine torPi_inj_of_close_FXT Λ hf0 hf ?_ he
  calc ‖y - y'‖ = ‖(y - pt) - (y' - pt)‖ := by congr 1; abel
    _ ≤ ‖y - pt‖ + ‖y' - pt‖ := norm_sub_le _ _
    _ < f := by linarith

include hf0 hf in
/-- **The chart of the torus on a small Euclidean ball**: the covering map restricted to
`B(pt, R)`, `R ≤ f/2`, as a partial diffeomorphism. -/
def torChart_FXT (pt : E3) {R : ℝ} (hRf : R ≤ f / 2) :
    PartialDiffeomorph I3 I3 E3 (Tor_FXC1 Λ) ∞ where
  toPartialEquiv := (torPi_injOn_ball_FXT Λ hf0 hf pt hRf).toPartialEquiv (torPi_FXC1 Λ) (ball pt R)
  open_source := isOpen_ball
  open_target := (torPi_isLocalDiffeomorph_FXC1 Λ).isOpenMap _ isOpen_ball
  contMDiffOn_toFun := (contMDiff_torPi_FXC1 Λ).contMDiffOn
  contMDiffOn_invFun := by
    rintro x ⟨y₀, hy₀, rfl⟩
    obtain ⟨Φ, hΦ, heq⟩ := (torPi_isLocalDiffeomorph_FXC1 Λ) y₀
    have hx₀ : torPi_FXC1 Λ y₀ ∈ Φ.target := by
      rw [heq hΦ]; exact Φ.map_source hΦ
    have hW : IsOpen {x | x ∈ Φ.target ∧ Φ.symm x ∈ ball pt R} := by
      have := Φ.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_target
        (isOpen_ball (x := pt) (ε := R))
      simpa only [PartialDiffeomorph.symm_source, inter_def, mem_preimage] using this
    have hxW : torPi_FXC1 Λ y₀ ∈ {x | x ∈ Φ.target ∧ Φ.symm x ∈ ball pt R} := by
      refine ⟨hx₀, ?_⟩
      have : Φ.symm (torPi_FXC1 Λ y₀) = y₀ := by
        rw [heq hΦ]; exact Φ.symm_apply_apply hΦ
      rwa [this]
    have hat : ContMDiffAt I3 I3 ∞ Φ.symm (torPi_FXC1 Λ y₀) :=
      (Φ.symm.contMDiffOn_toFun).contMDiffAt (Φ.open_target.mem_nhds hx₀)
    refine ContMDiffAt.contMDiffWithinAt (hat.congr_of_eventuallyEq ?_)
    filter_upwards [hW.mem_nhds hxW] with x hx
    have hy' : Φ.symm x ∈ ball pt R := hx.2
    have hmem : Φ.symm x ∈ Φ.source := Φ.map_target hx.1
    have h1 : torPi_FXC1 Λ (Φ.symm x) = x := by
      rw [heq hmem]; exact Φ.apply_symm_apply hx.1
    have h2 : ((torPi_injOn_ball_FXT Λ hf0 hf pt hRf).toPartialEquiv (torPi_FXC1 Λ)
        (ball pt R)).symm (torPi_FXC1 Λ (Φ.symm x)) = Φ.symm x :=
      PartialEquiv.left_inv _ hy'
    rw [h1] at h2
    exact h2

/-- The diffeomorphism of the open ball `B(pt, R) ⊂ E3` onto `E3`, as a partial diffeomorphism
(`R` positive). -/
def euclidBallChart_FXT (pt : E3) {R : ℝ} (hR : 0 < R) : PartialDiffeomorph I3 I3 E3 E3 ∞ where
  toPartialEquiv := (OpenPartialHomeomorph.univBall pt R).symm.toPartialEquiv
  open_source := (OpenPartialHomeomorph.univBall pt R).open_target
  open_target := (OpenPartialHomeomorph.univBall pt R).open_source
  contMDiffOn_toFun := by
    rw [OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.univBall_target pt hR]
    exact OpenPartialHomeomorph.contDiffOn_univBall_symm.contMDiffOn
  contMDiffOn_invFun := OpenPartialHomeomorph.contDiff_univBall.contDiffOn.contMDiffOn

theorem euclidBallChart_source_FXT (pt : E3) {R : ℝ} (hR : 0 < R) :
    (euclidBallChart_FXT pt hR).source = ball pt R :=
  OpenPartialHomeomorph.univBall_target pt hR

theorem euclidBallChart_target_FXT (pt : E3) {R : ℝ} (hR : 0 < R) :
    (euclidBallChart_FXT pt hR).target = univ :=
  OpenPartialHomeomorph.univBall_source pt R

include hf0 hf in
/-- **Small balls are cells**: `B(π pt, R)`, `R ≤ f/2`, is diffeomorphic to `E3`. -/
theorem exists_ballDiffeo_FXT (pt : E3) {R : ℝ} (hR : 0 < R) (hRf : R ≤ f / 2) :
    ∃ Ψ : PartialDiffeomorph I3 I3 (Tor_FXC1 Λ) E3 ∞,
      Ψ.source = ball (torPi_FXC1 Λ pt) R ∧ Ψ.target = univ := by
  refine ⟨(torChart_FXT Λ hf0 hf pt hRf).symm.trans (euclidBallChart_FXT pt hR), ?_, ?_⟩
  · have himg : (torChart_FXT Λ hf0 hf pt hRf).target = ball (torPi_FXC1 Λ pt) R :=
      torPi_image_ball_FXT Λ hf0 hf pt hRf
    change ((torChart_FXT Λ hf0 hf pt hRf).toPartialEquiv.symm.trans
      (euclidBallChart_FXT pt hR).toPartialEquiv).source = _
    rw [PartialEquiv.trans_source]
    ext x
    simp only [mem_inter_iff, PartialEquiv.symm_source, mem_preimage]
    refine ⟨fun h => himg ▸ h.1, fun h => ⟨himg ▸ h, ?_⟩⟩
    have hx : x ∈ (torChart_FXT Λ hf0 hf pt hRf).target := himg ▸ h
    have := (torChart_FXT Λ hf0 hf pt hRf).map_target hx
    rw [euclidBallChart_source_FXT pt hR]
    exact this
  · change ((torChart_FXT Λ hf0 hf pt hRf).toPartialEquiv.symm.trans
      (euclidBallChart_FXT pt hR).toPartialEquiv).target = _
    rw [PartialEquiv.trans_target]
    ext z
    simp only [mem_inter_iff, mem_preimage]
    have hz : z ∈ (euclidBallChart_FXT pt hR).target := by
      rw [euclidBallChart_target_FXT pt hR]; exact mem_univ z
    refine ⟨fun _ => mem_univ z, fun _ => ⟨hz, ?_⟩⟩
    have := (euclidBallChart_FXT pt hR).map_target hz
    rw [euclidBallChart_source_FXT pt hR] at this
    exact this

include hf0 hf in
/-- **Regime S: the Kleiner–Lott map of the rescaled torus to `E3`** when the ball of radius
`R/δ` is Euclidean (`R/δ ≤ f/4`). -/
theorem klSmall_FXT (p : Tor_FXC1 Λ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hRδ : R ≤ δ * (f / 4)) :
    Nonempty (@KleinerLottApprox (Tor_FXC1 Λ) E3
      ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)) _ p 0 δ) := by
  classical
  obtain ⟨pt, rfl⟩ := torPi_surjective_FXC1 Λ p
  have hRd : R / δ ≤ f / 4 := by rw [div_le_iff₀ hδ]; linarith
  let lift : Tor_FXC1 Λ → E3 := fun x =>
    if h : ∃ y, torPi_FXC1 Λ y = x ∧ ‖pt - y‖ < R / δ then h.choose else pt
  have hlift : ∀ x : Tor_FXC1 Λ, dist x (torPi_FXC1 Λ pt) < R / δ →
      torPi_FXC1 Λ (lift x) = x ∧ ‖pt - lift x‖ < R / δ := by
    intro x hx
    have h : ∃ y, torPi_FXC1 Λ y = x ∧ ‖pt - y‖ < R / δ :=
      exists_lift_of_dist_lt_FXC1 Λ pt x (by rwa [dist_comm] at hx)
    simp only [lift, h, ↓reduceDIte]
    exact h.choose_spec
  have hbase : lift (torPi_FXC1 Λ pt) = pt := by
    have h := hlift (torPi_FXC1 Λ pt) (by rw [dist_self]; positivity)
    refine torPi_inj_of_close_FXT Λ hf0 hf ?_ h.1
    have := h.2
    rw [norm_sub_rev] at this
    linarith
  have hmem : ∀ x : Tor_FXC1 Λ, x ∈ @Metric.ball (Tor_FXC1 Λ)
      ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace (torPi_FXC1 Λ pt) δ⁻¹ →
      dist x (torPi_FXC1 Λ pt) < R / δ := by
    intro x hx
    have h1 : R⁻¹ * dist x (torPi_FXC1 Λ pt) < δ⁻¹ := by
      have := (@Metric.mem_ball (Tor_FXC1 Λ)
        ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace _ _ _).mp hx
      rwa [MetricSpace.rescale_dist] at this
    rw [lt_div_iff₀ hδ]
    have h2 := mul_lt_mul_of_pos_left h1 hR
    rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] at h2
    rw [inv_eq_one_div, mul_one_div] at h2
    rw [lt_div_iff₀ hδ] at h2
    linarith
  have hdist : ∀ x x' : Tor_FXC1 Λ, dist x (torPi_FXC1 Λ pt) < R / δ →
      dist x' (torPi_FXC1 Λ pt) < R / δ →
      dist x x' = ‖lift x - lift x'‖ := by
    intro x x' hx hx'
    obtain ⟨h1, h2⟩ := hlift x hx
    obtain ⟨h1', h2'⟩ := hlift x' hx'
    have := dist_torPi_eq_FXT Λ hf0 hf (y := lift x) (y' := lift x') (by
      calc ‖lift x - lift x'‖ = ‖(pt - lift x') - (pt - lift x)‖ := by congr 1; abel
        _ ≤ ‖pt - lift x'‖ + ‖pt - lift x‖ := norm_sub_le _ _
        _ < f / 2 := by linarith)
    rwa [h1, h1'] at this
  refine ⟨@KleinerLottApprox.mk (Tor_FXC1 Λ) E3 ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)) _
    (torPi_FXC1 Λ pt) 0 δ hδ hδ1 (fun x => R⁻¹ • (lift x - pt)) ?_ ?_ ?_⟩
  · simp [hbase]
  · intro x hx x' hx'
    rw [MetricSpace.rescale_dist, hdist x x' (hmem x hx) (hmem x' hx'), dist_eq_norm,
      ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hR).le]
    have e : lift x - pt - (lift x' - pt) = lift x - lift x' := by abel
    rw [e, sub_self, abs_zero]
    exact hδ.le
  · intro z hz
    have hz' : ‖z‖ < δ⁻¹ - δ := by rwa [dist_zero_right] at hz
    have hRz : R * ‖z‖ < R / δ := by
      have : ‖z‖ < δ⁻¹ := by linarith
      rw [div_eq_mul_inv]
      exact mul_lt_mul_of_pos_left this hR
    have hxd : dist (torPi_FXC1 Λ (pt + R • z)) (torPi_FXC1 Λ pt) = R * ‖z‖ := by
      rw [dist_torPi_eq_FXT Λ hf0 hf (by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hR.le]; linarith)]
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hR.le]
    obtain ⟨h1, h2⟩ := hlift (torPi_FXC1 Λ (pt + R • z)) (by rw [hxd]; exact hRz)
    have hl : lift (torPi_FXC1 Λ (pt + R • z)) = pt + R • z := by
      refine torPi_inj_of_close_FXT Λ hf0 hf ?_ h1
      have e : lift (torPi_FXC1 Λ (pt + R • z)) - (pt + R • z) =
          -(pt - lift (torPi_FXC1 Λ (pt + R • z))) - R • z := by abel
      rw [e]
      calc ‖-(pt - lift (torPi_FXC1 Λ (pt + R • z))) - R • z‖
          ≤ ‖-(pt - lift (torPi_FXC1 Λ (pt + R • z)))‖ + ‖R • z‖ := norm_sub_le _ _
        _ < f := by
          rw [norm_neg, norm_smul, Real.norm_of_nonneg hR.le]
          linarith
    have hmemx : torPi_FXC1 Λ (pt + R • z) ∈ @Metric.ball (Tor_FXC1 Λ)
        ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace (torPi_FXC1 Λ pt)
          δ⁻¹ := by
      rw [@Metric.mem_ball (Tor_FXC1 Λ)
        ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace _ _ _,
        MetricSpace.rescale_dist, hxd, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
      linarith
    have hz0 : z ∈ (fun x => R⁻¹ • (lift x - pt)) '' @Metric.ball (Tor_FXC1 Λ)
        ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace (torPi_FXC1 Λ pt)
          δ⁻¹ := by
      refine ⟨torPi_FXC1 Λ (pt + R • z), hmemx, ?_⟩
      simp only [hl, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
    rw [Metric.infDist_zero_of_mem hz0]
    exact hδ.le

end Chart

end DifferentialGeometry.Geometry.Collapse

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ChartC0L1_O58
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.InverseJets_S126

/-!
# CH12-O62 G1: the single-chart step of L1

`[FROZEN v2] CH12-O62` (`chart_step_O62`, statement in `build-logs/ch12/scratch/FrozenO62.lean`
without the `hRE` binder, which is discharged by `inverse_jets_S126`).  In one chart at `c`, for a
compact `Kc ⊆ target` lying over the open set `W'` on which `Ψ` is `C⁰`-close to the identity
(and `Ψ` has small `ckErr` on the open `W ⊇ W'`):

* R-B (`chart_C0_of_dist_O58`) makes the displacement `u = chartDisplacement_CX3 c Ψ` `C⁰`-small on
  `Kz = cthickening τ₀ Kc`, R-C (`chart_small_jets_O58`, order `k + 1`) makes its jets small on
  `thickening (4τ) Kc`, so `‖Du‖ ≤ 1/2` there;
* R-D (`exists_preimage_of_small_O58`) gives chart preimages on `thickening (3τ) Kc`, which by
  injectivity are the values of `Function.invFunOn Ψ U`;
* R-E (`inverse_jets_S126`) on small balls gives smoothness and small jets of the chart inverse.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open Set Metric Filter
open scoped Manifold ContDiff Topology NNReal

namespace GC.LongTime.Ch12

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Thickening arithmetic: a point within `b` of a point of `thickening a K` lies in
`thickening c' K` once `a + b ≤ c'`. -/
theorem mem_thickening_of_O62 {K : Set E3} {a b c' : ℝ} {y z : E3} (hy : y ∈ thickening a K)
    (hz : dist z y ≤ b) (h : a + b ≤ c') : z ∈ thickening c' K := by
  obtain ⟨w, hw, hyw⟩ := mem_thickening_iff.1 hy
  exact mem_thickening_iff.2 ⟨w, hw, (dist_triangle z y w).trans_lt (by linarith)⟩

/-- **Single-chart step of L1** (`[FROZEN v2] CH12-O62`). -/
theorem chart_step_O62 (H : FiniteVolumeHyperbolicModel.{u}) (c : H.Carrier)
    {W W' : Set H.Carrier} (hW : IsOpen W) (hW' : IsOpen W') (hWW : W' ⊆ W)
    {Kc : Set E3} (hKc : IsCompact Kc) (hKct : Kc ⊆ (extChartAt (𝓡 3) c).target)
    (hKW : Kc ⊆ (extChartAt (𝓡 3) c).symm ⁻¹' W') (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ θ : ℝ, 0 < θ ∧ ∃ N : Set E3, IsOpen N ∧ Kc ⊆ N ∧
      N ⊆ (extChartAt (𝓡 3) c).target ∧
      ∀ (U : Set H.Carrier) (Ψ : H.Carrier → H.Carrier), W ⊆ U →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ Ψ U → Set.InjOn Ψ U →
        (∀ j : ℕ, j ≤ k + 2 → ∀ p ∈ W, ckErr_O19 H H.metric 1 Ψ j p < δ) →
        (∀ p ∈ W', riemannianEDistOf H.metric p (Ψ p) < ENNReal.ofReal θ) →
        (∀ x ∈ Kc, Ψ ((extChartAt (𝓡 3) c).symm x) ∈ (extChartAt (𝓡 3) c).source ∧
          ∀ j ≤ k, ‖iteratedFDeriv ℝ j (chartDisplacement_CX3 (I := 𝓡 3) c Ψ) x‖ < ε) ∧
        (∀ x ∈ Kc, Function.invFunOn Ψ U ((extChartAt (𝓡 3) c).symm x) ∈
            (extChartAt (𝓡 3) c).source ∧
          ∀ j ≤ k, ‖iteratedFDeriv ℝ j
            (chartDisplacement_CX3 (I := 𝓡 3) c (Function.invFunOn Ψ U)) x‖ < ε) ∧
        (∀ x ∈ N, Function.invFunOn Ψ U ((extChartAt (𝓡 3) c).symm x) ∈ W' ∧
          Ψ (Function.invFunOn Ψ U ((extChartAt (𝓡 3) c).symm x)) = (extChartAt (𝓡 3) c).symm x ∧
          ContMDiffAt (𝓡 3) (𝓡 3) ∞ (Function.invFunOn Ψ U) ((extChartAt (𝓡 3) c).symm x)) := by
  -- Step A: the compact chart neighbourhood `Kz` of `Kc` over `W'`.
  have hT : IsOpen (extChartAt (𝓡 3) c).target := isOpen_extChartAt_target c
  have hG : IsOpen ((extChartAt (𝓡 3) c).target ∩ (extChartAt (𝓡 3) c).symm ⁻¹' W') :=
    (continuousOn_extChartAt_symm c).isOpen_inter_preimage hT hW'
  obtain ⟨τ₀, hτ₀, hτ₀G⟩ :=
    hKc.exists_cthickening_subset_open hG (fun x hx => ⟨hKct hx, hKW hx⟩)
  set τ : ℝ := τ₀ / 6 with hτdef
  have hτ : 0 < τ := by positivity
  have hKz : IsCompact (cthickening τ₀ Kc) := hKc.cthickening
  have hKzW : cthickening τ₀ Kc ⊆
      (extChartAt (𝓡 3) c).target ∩ (extChartAt (𝓡 3) c).symm ⁻¹' W :=
    fun y hy => ⟨(hτ₀G hy).1, hWW (hτ₀G hy).2⟩
  have hthK : ∀ a : ℝ, a ≤ 6 * τ → thickening a Kc ⊆ cthickening τ₀ Kc := fun a ha =>
    (thickening_subset_cthickening _ _).trans (cthickening_mono (by linarith) _)
  -- Step B: constants.
  obtain ⟨η, hη, hRE⟩ := inverse_jets_S126 (E := E3) k ε hε
  set ε₁ : ℝ := min (min ε (1 / 2)) η with hε₁def
  have hε₁ : 0 < ε₁ := lt_min (lt_min hε (by norm_num)) hη
  obtain ⟨δ, hδ, θ₀, hθ₀, hsmall⟩ := chart_small_jets_O58 H c hW hKz hKzW (k + 1) hτ hε₁
  have hθ₀' : 0 < min θ₀ (τ / 2) := lt_min hθ₀ (by positivity)
  have hKimg : IsCompact ((extChartAt (𝓡 3) c).symm '' cthickening τ₀ Kc) :=
    hKz.image_of_continuousOn ((continuousOn_extChartAt_symm c).mono fun y hy => (hKzW hy).1)
  have hKs : (extChartAt (𝓡 3) c).symm '' cthickening τ₀ Kc ⊆ (extChartAt (𝓡 3) c).source := by
    rintro _ ⟨y, hy, rfl⟩
    exact (extChartAt (𝓡 3) c).map_target (hKzW hy).1
  obtain ⟨θ, hθ, hC0⟩ := chart_C0_of_dist_O58 H c hKimg hKs hθ₀'
  refine ⟨δ, hδ, θ, hθ, thickening (2 * τ) Kc, isOpen_thickening,
    self_subset_thickening (by positivity) _, fun y hy => (hKzW (hthK _ (by linarith) hy)).1, ?_⟩
  intro U Ψ hWU hΨ hinj herr hdist
  set u := chartDisplacement_CX3 (I := 𝓡 3) c Ψ with hu_def
  -- Step C: `C⁰` smallness of `u` on `Kz` (R-B).
  have hu0 : ∀ y ∈ cthickening τ₀ Kc, Ψ ((extChartAt (𝓡 3) c).symm y) ∈
      (extChartAt (𝓡 3) c).source ∧ ‖u y‖ < min θ₀ (τ / 2) := by
    intro y hy
    obtain ⟨h1, h2⟩ := hC0 _ ⟨y, hy, rfl⟩ _ (hdist _ (hτ₀G hy).2)
    refine ⟨h1, ?_⟩
    rw [(extChartAt (𝓡 3) c).right_inv (hKzW hy).1] at h2
    exact h2
  have hV5 : ∀ y ∈ thickening (5 * τ) Kc, Ψ ((extChartAt (𝓡 3) c).symm y) ∈
      (extChartAt (𝓡 3) c).source ∧ y + u y ∈ cthickening τ₀ Kc ∧ ‖u y‖ ≤ θ₀ := by
    intro y hy
    obtain ⟨h1, h2⟩ := hu0 y (hthK _ (by linarith) hy)
    refine ⟨h1, hthK (6 * τ) le_rfl (mem_thickening_of_O62 hy (b := τ) ?_ (by linarith)),
      h2.le.trans (min_le_left _ _)⟩
    rw [dist_eq_norm, add_sub_cancel_left]
    exact (h2.trans_le (min_le_right _ _)).le.trans (by linarith)
  -- Step D: small jets on `thickening (4τ) Kc` (R-C at order `k + 1`).
  have hΨW : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Ψ W := hΨ.mono hWU
  have hjet := hsmall Ψ hΨW (fun j hj p hp => herr j (by omega) p hp) _ isOpen_thickening
    (hthK _ (by linarith)) hV5
  have hJ4 : ∀ j : ℕ, j ≤ k + 1 → ∀ y ∈ thickening (4 * τ) Kc,
      ‖iteratedFDeriv ℝ j u y‖ < ε₁ := fun j hj y hy =>
    hjet j hj y fun z hz => mem_thickening_of_O62 hy (mem_closedBall.1 hz) (by linarith)
  have huC : ContDiffOn ℝ ∞ u (thickening (5 * τ) Kc) :=
    displacement_contDiffOn_O58 c hW hΨW (fun y hy => hKzW (hthK _ (by linarith) hy))
      (fun y hy => (hV5 y hy).1)
  have hD4 : ∀ y ∈ thickening (4 * τ) Kc, DifferentiableAt ℝ u y ∧ ‖fderiv ℝ u y‖ ≤ 1 / 2 := by
    intro y hy
    refine ⟨(huC.contDiffAt (isOpen_thickening.mem_nhds
      (thickening_mono (by linarith) _ hy))).differentiableAt (by simp), ?_⟩
    rw [← norm_iteratedFDeriv_one]
    exact (hJ4 1 (by omega) y hy).le.trans ((min_le_left _ _).trans (min_le_right _ _))
  -- Step E: chart preimages and `invFunOn` (R-D + injectivity).
  have hinv : ∀ x ∈ thickening (3 * τ) Kc, ∃ y ∈ closedBall x τ, y + u y = x ∧
      y ∈ thickening (4 * τ) Kc ∧
      Function.invFunOn Ψ U ((extChartAt (𝓡 3) c).symm x) = (extChartAt (𝓡 3) c).symm y ∧
      Ψ (Function.invFunOn Ψ U ((extChartAt (𝓡 3) c).symm x)) = (extChartAt (𝓡 3) c).symm x := by
    intro x hx
    have hball : ∀ y ∈ closedBall x τ, y ∈ thickening (4 * τ) Kc := fun y hy =>
      mem_thickening_of_O62 hx (mem_closedBall.1 hy) (by linarith)
    obtain ⟨y, hy, hyx⟩ := exists_preimage_of_small_O58 hτ (fun y hy => (hD4 y (hball y hy)).1)
      (fun y hy => (hD4 y (hball y hy)).2)
      (((hu0 x (hthK _ (by linarith) hx)).2.trans_le (min_le_right _ _)).le)
    have hy4 := hball y hy
    have hyz : y ∈ cthickening τ₀ Kc := hthK _ (by linarith) hy4
    have hsrc := (hu0 y hyz).1
    have hext : extChartAt (𝓡 3) c (Ψ ((extChartAt (𝓡 3) c).symm y)) = x := by
      rw [← hyx, hu_def]
      simp only [chartDisplacement_CX3]
      abel
    have hΨy : Ψ ((extChartAt (𝓡 3) c).symm y) = (extChartAt (𝓡 3) c).symm x := by
      rw [← hext, (extChartAt (𝓡 3) c).left_inv hsrc]
    have hyU : (extChartAt (𝓡 3) c).symm y ∈ U := hWU (hWW (hτ₀G hyz).2)
    have hex : ∃ a ∈ U, Ψ a = (extChartAt (𝓡 3) c).symm x := ⟨_, hyU, hΨy⟩
    refine ⟨y, hy, hyx, hy4, hinj (Function.invFunOn_mem hex) hyU ?_, Function.invFunOn_eq hex⟩
    rw [Function.invFunOn_eq hex, hΨy]
  -- the chart inverse `Φ x = ext (invFunOn Ψ U (symm x))`
  set Φ : E3 → E3 := fun z =>
    extChartAt (𝓡 3) c (Function.invFunOn Ψ U ((extChartAt (𝓡 3) c).symm z)) with hΦ_def
  have hΦy : ∀ x ∈ thickening (3 * τ) Kc, ∃ y ∈ closedBall x τ, y + u y = x ∧
      y ∈ thickening (4 * τ) Kc ∧ Φ x = y ∧
      Function.invFunOn Ψ U ((extChartAt (𝓡 3) c).symm x) = (extChartAt (𝓡 3) c).symm y ∧
      Ψ (Function.invFunOn Ψ U ((extChartAt (𝓡 3) c).symm x)) = (extChartAt (𝓡 3) c).symm x := by
    intro x hx
    obtain ⟨y, hy, hyx, hy4, hinvy, hΨinv⟩ := hinv x hx
    refine ⟨y, hy, hyx, hy4, ?_, hinvy, hΨinv⟩
    rw [hΦ_def]
    simp only
    rw [hinvy, (extChartAt (𝓡 3) c).right_inv (hKzW (hthK _ (by linarith) hy4)).1]
  -- Step F: R-E on the ball `ball x₀ (2τ)`.
  have hloc : ∀ x₀ ∈ thickening (2 * τ) Kc, ContDiffAt ℝ ∞ Φ x₀ ∧
      ∀ j : ℕ, j ≤ k → ‖iteratedFDeriv ℝ j (fun z => Φ z - z) x₀‖ < ε := by
    intro x₀ hx₀
    have hV : ball x₀ (2 * τ) ⊆ thickening (4 * τ) Kc := fun z hz =>
      mem_thickening_of_O62 hx₀ (mem_ball.1 hz).le (by linarith)
    have hWs : ball x₀ τ ⊆ thickening (3 * τ) Kc := fun z hz =>
      mem_thickening_of_O62 hx₀ (mem_ball.1 hz).le (by linarith)
    have hA := approximatesLinearOn_of_fderiv_O58 (convex_ball x₀ (2 * τ))
      (fun y hy => (hD4 y (hV hy)).1) (fun y hy => (hD4 y (hV hy)).2)
    have hmaps : ∀ x ∈ ball x₀ τ, Φ x ∈ ball x₀ (2 * τ) ∧ Φ x + u (Φ x) = x := by
      intro x hx
      obtain ⟨y, hy, hyx, -, hΦx, -, -⟩ := hΦy x (hWs hx)
      rw [hΦx]
      refine ⟨?_, hyx⟩
      rw [mem_ball]
      calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
        _ < τ + τ := add_lt_add_of_le_of_lt (mem_closedBall.1 hy) (mem_ball.1 hx)
        _ = 2 * τ := by ring
    obtain ⟨hΦC, hΦj⟩ := hRE u Φ (ball x₀ (2 * τ)) (ball x₀ τ) isOpen_ball isOpen_ball
      (huC.mono (hV.trans (thickening_mono (by linarith) _))) hA
      (fun j hj y hy => (hJ4 j (by omega) y (hV hy)).le.trans (min_le_right _ _)) hmaps
    exact ⟨hΦC.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hτ)),
      fun j hj => hΦj j hj x₀ (mem_ball_self hτ)⟩
  have hK2 : ∀ x ∈ Kc, x ∈ thickening (2 * τ) Kc := fun x hx =>
    self_subset_thickening (by positivity) _ hx
  refine ⟨fun x hx => ⟨(hu0 x (hthK _ (by linarith) (hK2 x hx))).1, fun j hj =>
    (hJ4 j (by omega) x (thickening_mono (by linarith) _ (hK2 x hx))).trans_le
      ((min_le_left _ _).trans (min_le_left _ _))⟩, fun x hx => ⟨?_, fun j hj => ?_⟩,
    fun x hx => ?_⟩
  · obtain ⟨y, -, -, hy4, -, hinvy, -⟩ := hΦy x (thickening_mono (by linarith) _ (hK2 x hx))
    rw [hinvy]
    exact (extChartAt (𝓡 3) c).map_target (hKzW (hthK _ (by linarith) hy4)).1
  · exact (hloc x (hK2 x hx)).2 j hj
  · -- membership, image, and smoothness of `invFunOn` near `symm x`
    have hx3 : x ∈ thickening (3 * τ) Kc := thickening_mono (by linarith) _ hx
    obtain ⟨y, -, -, hy4, -, hinvy, hΨinv⟩ := hΦy x hx3
    have hyz : y ∈ cthickening τ₀ Kc := hthK _ (by linarith) hy4
    refine ⟨by rw [hinvy]; exact (hτ₀G hyz).2, hΨinv, ?_⟩
    have hxt : x ∈ (extChartAt (𝓡 3) c).target := (hKzW (hthK _ (by linarith) hx)).1
    have hsrc : Function.invFunOn Ψ U ((extChartAt (𝓡 3) c).symm x) ∈
        (extChartAt (𝓡 3) c).source := by
      rw [hinvy]; exact (extChartAt (𝓡 3) c).map_target (hKzW hyz).1
    have hps : (extChartAt (𝓡 3) c).symm x ∈ (extChartAt (𝓡 3) c).source :=
      (extChartAt (𝓡 3) c).map_target hxt
    have hpx : extChartAt (𝓡 3) c ((extChartAt (𝓡 3) c).symm x) = x :=
      (extChartAt (𝓡 3) c).right_inv hxt
    have hSo : IsOpen ((extChartAt (𝓡 3) c).source ∩
        extChartAt (𝓡 3) c ⁻¹' thickening (2 * τ) Kc) :=
      isOpen_extChartAt_preimage' c isOpen_thickening
    have hpS : (extChartAt (𝓡 3) c).symm x ∈ (extChartAt (𝓡 3) c).source ∩
        extChartAt (𝓡 3) c ⁻¹' thickening (2 * τ) Kc := ⟨hps, by rw [mem_preimage, hpx]; exact hx⟩
    have heq : Function.invFunOn Ψ U =ᶠ[𝓝 ((extChartAt (𝓡 3) c).symm x)]
        ((extChartAt (𝓡 3) c).symm ∘ Φ ∘ extChartAt (𝓡 3) c) := by
      refine Filter.eventuallyEq_of_mem (hSo.mem_nhds hpS) fun q hq => ?_
      obtain ⟨y', -, -, hy'4, -, hinvy', -⟩ := hΦy _ (thickening_mono (by linarith) _ hq.2)
      have hq' : (extChartAt (𝓡 3) c).symm (extChartAt (𝓡 3) c q) = q :=
        (extChartAt (𝓡 3) c).left_inv hq.1
      rw [hq'] at hinvy'
      have hsrc' : Function.invFunOn Ψ U q ∈ (extChartAt (𝓡 3) c).source := by
        rw [hinvy']
        exact (extChartAt (𝓡 3) c).map_target (hKzW (hthK _ (by linarith) hy'4)).1
      simp only [Function.comp_apply, hΦ_def, hq']
      exact ((extChartAt (𝓡 3) c).left_inv hsrc').symm
    have hext : ContMDiffAt (𝓡 3) 𝓘(ℝ, E3) ∞ (extChartAt (𝓡 3) c)
        ((extChartAt (𝓡 3) c).symm x) :=
      contMDiffAt_extChartAt' (by rw [← extChartAt_source (I := 𝓡 3)]; exact hps)
    have hΦp : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ Φ
        (extChartAt (𝓡 3) c ((extChartAt (𝓡 3) c).symm x)) := by
      rw [hpx]; exact (hloc x hx).1.contMDiffAt
    have hΦt : Φ (extChartAt (𝓡 3) c ((extChartAt (𝓡 3) c).symm x)) ∈
        (extChartAt (𝓡 3) c).target := by
      rw [hpx]; exact (extChartAt (𝓡 3) c).map_source hsrc
    have hsym : ContMDiffAt 𝓘(ℝ, E3) (𝓡 3) ∞ (extChartAt (𝓡 3) c).symm
        (Φ (extChartAt (𝓡 3) c ((extChartAt (𝓡 3) c).symm x))) :=
      (contMDiffOn_extChartAt_symm c).contMDiffAt (hT.mem_nhds hΦt)
    have hcomp : ContMDiffAt (𝓡 3) (𝓡 3) ∞
        ((extChartAt (𝓡 3) c).symm ∘ Φ ∘ extChartAt (𝓡 3) c) ((extChartAt (𝓡 3) c).symm x) :=
      hsym.comp ((extChartAt (𝓡 3) c).symm x) (hΦp.comp ((extChartAt (𝓡 3) c).symm x) hext)
    exact hcomp.congr_of_eventuallyEq heq

end GC.LongTime.Ch12

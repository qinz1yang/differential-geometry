import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ChartStepL1_O62
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HPS01Reduction_O26

/-!
# CH12-O62 G2: `L1_O62` (single-model near-isometry rigidity) and `hps01_O62 : hHPS01 v3`

`[FROZEN v2] CH12-O62`.  `L1_O62` is `[FROZEN] CH12-O26` L1 verbatim (the `hSM` binder of
`hps01_of_single_O26`), proved by `chart_step_O62` in each chart of the atlas with
`Kc_i = closedBall_i ∩ symm_i ⁻¹' D2`, `W = ball(o, 2R)`, `W' = ball(o, R)` (`D2 ⊆ ball(o, R)`),
`δ, θ` = minima over the finitely many charts, `m = k + 2`, and
`O = ball(o, R) ∩ ⋃ i, (source_i ∩ ext_i ⁻¹' N_i)`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime GC.LongTime.Ch12
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12

universe u

/-- A positive lower bound of a finite positive family. -/
theorem exists_pos_le_fin_O62 {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ a : ℝ, 0 < a ∧ ∀ i, a ≤ f i := by
  obtain ⟨a, ha, hle⟩ := exists_pos_le_forall_le_O58 n
    (fun j _ => if h : j < n then f ⟨j, h⟩ else 1)
    (fun j _ => by
      split_ifs
      · exact hf _
      · exact one_pos)
  refine ⟨a, ha, fun i => ?_⟩
  simpa [i.2] using hle i.1 i.2.le

/-- **L1** (`[FROZEN] CH12-O26` L1 verbatim; `[FROZEN v2] CH12-O62`, no binder). -/
theorem L1_O62 :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier)
      (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D2 : Set H.Carrier), IsCompact D2 → D2 ⊆ A.cover →
      ∀ (k : ℕ) (ρ ε : ℝ), 0 < ρ → 0 < ε →
      ∃ R θ δ : ℝ, 0 < R ∧ 0 < θ ∧ 0 < δ ∧ ∃ m : ℕ, ∃ O : Set H.Carrier, IsOpen O ∧ D2 ⊆ O ∧
        O ⊆ riemannianBallOf H.metric o R ∧
        ∀ (U : TopologicalSpace.Opens H.Carrier) (Ψ : H.Carrier → H.Carrier),
          riemannianBallOf H.metric o (2 * R) ⊆ U → ContMDiffOn (𝓡 3) (𝓡 3) ∞ Ψ U →
          Set.InjOn Ψ U →
          (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H.metric o (2 * R),
            ckErr_O19 H H.metric 1 Ψ j p < δ) →
          (∀ p ∈ riemannianBallOf H.metric o R,
            riemannianEDistOf H.metric p (Ψ p) < ENNReal.ofReal θ) →
          (∀ p ∈ O, riemannianEDistOf H.metric p (Ψ p) < ENNReal.ofReal ρ) ∧
          CkCloseInAtlas_CX3 A D2 k ε Ψ ∧
          O ⊆ Ψ '' (U : Set H.Carrier) ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Function.invFunOn Ψ U) O ∧
          (∀ p ∈ O, riemannianEDistOf H.metric p (Function.invFunOn Ψ U p) < ENNReal.ofReal ρ) ∧
          CkCloseInAtlas_CX3 A D2 k ε (Function.invFunOn Ψ U) := by
  intro H o A D2 hD2 hD2A k ρ ε hρ hε
  have : LocallyCompactSpace H.Carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) H.Carrier
  have : RegularSpace H.Carrier := inferInstance
  let _ : PseudoMetricSpace H.Carrier := H.metric.toPseudoMetricSpace
  have hball : ∀ r : ℝ, riemannianBallOf H.metric o r = Metric.ball o r := by
    intro r
    ext y
    change riemannianEDistOf H.metric o y < ENNReal.ofReal r ↔ dist y o < r
    rw [dist_comm, ← edist_lt_ofReal]
    rfl
  -- Step 1: `R` with `D2 ⊆ ball(o, R)`; `W = ball(o, 2R)`, `W' = ball(o, R)`.
  have hD2' : IsCompact D2 := by exact hD2
  obtain ⟨r, hr⟩ := hD2'.isBounded.subset_ball o
  set R : ℝ := max r 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hD2R : D2 ⊆ riemannianBallOf H.metric o R := by
    rw [hball]; exact hr.trans (Metric.ball_subset_ball (le_max_left _ _))
  have hW : IsOpen (riemannianBallOf H.metric o (2 * R)) := by
    rw [hball]; exact Metric.isOpen_ball
  have hW' : IsOpen (riemannianBallOf H.metric o R) := by
    rw [hball]; exact Metric.isOpen_ball
  have hWW : riemannianBallOf H.metric o R ⊆ riemannianBallOf H.metric o (2 * R) := by
    rw [hball, hball]; exact Metric.ball_subset_ball (by linarith)
  -- Step 2: the compact chart pieces `Kc_i = closedBall_i ∩ symm_i ⁻¹' D2`.
  have hKc : ∀ i : Fin A.n, IsCompact (Metric.closedBall (extChartAt (𝓡 3) (A.ctr i) (A.ctr i))
      (A.rad i) ∩ (extChartAt (𝓡 3) (A.ctr i)).symm ⁻¹' D2) := fun i =>
    (isCompact_closedBall _ _).of_isClosed_subset
      (((continuousOn_extChartAt_symm (A.ctr i)).mono (A.closedBall_sub i)).preimage_isClosed_of_isClosed
        Metric.isClosed_closedBall hD2.isClosed) inter_subset_left
  have hKct : ∀ i : Fin A.n, Metric.closedBall (extChartAt (𝓡 3) (A.ctr i) (A.ctr i)) (A.rad i) ∩
      (extChartAt (𝓡 3) (A.ctr i)).symm ⁻¹' D2 ⊆ (extChartAt (𝓡 3) (A.ctr i)).target :=
    fun i x hx => A.closedBall_sub i hx.1
  have hKW : ∀ i : Fin A.n, Metric.closedBall (extChartAt (𝓡 3) (A.ctr i) (A.ctr i)) (A.rad i) ∩
      (extChartAt (𝓡 3) (A.ctr i)).symm ⁻¹' D2 ⊆
      (extChartAt (𝓡 3) (A.ctr i)).symm ⁻¹' riemannianBallOf H.metric o R :=
    fun i x hx => hD2R hx.2
  choose δi hδi θi hθi Ni hNo hKN hNt hstep using fun i : Fin A.n =>
    chart_step_O62 H (A.ctr i) hW hW' hWW (hKc i) (hKct i) (hKW i) k hε
  -- Step 3: global constants and the open set `O`.
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_fin_O62 δi hδi
  obtain ⟨θ₀, hθ₀, hθle⟩ := exists_pos_le_fin_O62 θi hθi
  refine ⟨R, min ρ θ₀, δ, hR, lt_min hρ hθ₀, hδ, k + 2,
    riemannianBallOf H.metric o R ∩ ⋃ i, ((extChartAt (𝓡 3) (A.ctr i)).source ∩
      extChartAt (𝓡 3) (A.ctr i) ⁻¹' Ni i),
    hW'.inter (isOpen_iUnion fun i => isOpen_extChartAt_preimage' _ (hNo i)), ?_,
    inter_subset_left, ?_⟩
  · intro p hp
    refine ⟨hD2R hp, ?_⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hD2A hp)
    have hi' : p ∈ (extChartAt (𝓡 3) (A.ctr i)).source ∩ extChartAt (𝓡 3) (A.ctr i) ⁻¹'
        Metric.ball (extChartAt (𝓡 3) (A.ctr i) (A.ctr i)) (A.rad i) := hi
    refine mem_iUnion.2 ⟨i, hi'.1, hKN i ⟨Metric.ball_subset_closedBall hi'.2, ?_⟩⟩
    change (extChartAt (𝓡 3) (A.ctr i)).symm (extChartAt (𝓡 3) (A.ctr i) p) ∈ D2
    rw [(extChartAt (𝓡 3) (A.ctr i)).left_inv hi'.1]
    exact hp
  -- Step 4: the conclusions.
  intro U Ψ hWU hΨ hinj herr hdist
  have hS := fun i : Fin A.n => hstep i U Ψ hWU hΨ hinj
    (fun j hj p hp => (herr j hj p hp).trans_le (hδle i))
    (fun p hp => (hdist p hp).trans_le
      (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (hθle i))))
  have hO : ∀ p ∈ riemannianBallOf H.metric o R ∩ ⋃ i, ((extChartAt (𝓡 3) (A.ctr i)).source ∩
      extChartAt (𝓡 3) (A.ctr i) ⁻¹' Ni i),
      Function.invFunOn Ψ U p ∈ riemannianBallOf H.metric o R ∧
        Ψ (Function.invFunOn Ψ U p) = p ∧
        ContMDiffAt (𝓡 3) (𝓡 3) ∞ (Function.invFunOn Ψ U) p := by
    rintro p ⟨-, hp⟩
    obtain ⟨i, hpi⟩ := mem_iUnion.1 hp
    have h := (hS i).2.2 _ hpi.2
    rwa [(extChartAt (𝓡 3) (A.ctr i)).left_inv hpi.1] at h
  refine ⟨fun p hp => (hdist p hp.1).trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _)),
    fun i x hx hxD => (hS i).1 x ⟨hx, hxD⟩, fun p hp => ?_,
    fun p hp => (hO p hp).2.2.contMDiffWithinAt, fun p hp => ?_,
    fun i x hx hxD => (hS i).2.1 x ⟨hx, hxD⟩⟩
  · exact ⟨_, hWU (hWW (hO p hp).1), (hO p hp).2.1⟩
  · obtain ⟨h1, h2, -⟩ := hO p hp
    have h := hdist _ h1
    rw [h2, riemannianEDistOf_comm] at h
    exact h.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))

/-- **hHPS01 v3** with no binder: `hps01_of_single_O26 L1_O62` (`[FROZEN v2] CH12-O62`). -/
theorem hps01_O62 :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier)
    (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D2 : Set H.Carrier), IsCompact D2 → D2 ⊆ A.cover →
    ∀ (k : ℕ) (ρ ε : ℝ), 0 < ρ → 0 < ε →
    ∃ R θ δ : ℝ, 0 < R ∧ 0 < θ ∧ 0 < δ ∧ ∃ m : ℕ, ∃ O : Set H.Carrier, IsOpen O ∧ D2 ⊆ O ∧
      O ⊆ riemannianBallOf H.metric o R ∧
      ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (e : H.Carrier ≃ H'.Carrier),
        ContMDiff (𝓡 3) (𝓡 3) ∞ e → ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm →
        (∀ p, localPullInner H'.metric e p = H.metric.inner p) →
      ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
        riemannianBallOf H.metric o (2 * R) ⊆ U → ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
        (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H.metric o (2 * R),
          ckErr_O19 H H'.metric 1 f j p < δ) →
        (∀ p ∈ riemannianBallOf H.metric o R,
          riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal θ) →
        (∀ p ∈ O, riemannianEDistOf H.metric p (e.symm (f p)) < ENNReal.ofReal ρ) ∧
        CkCloseInAtlas_CX3 A D2 k ε (fun p => e.symm (f p)) ∧
        e '' O ⊆ f '' (U : Set H.Carrier) ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => Function.invFunOn f U (e p)) O ∧
        (∀ p ∈ O, riemannianEDistOf H.metric p (Function.invFunOn f U (e p)) <
          ENNReal.ofReal ρ) ∧
        CkCloseInAtlas_CX3 A D2 k ε (fun p => Function.invFunOn f U (e p)) :=
  hps01_of_single_O26 L1_O62

end GC.LongTime.Ch12

import DifferentialGeometry.Topology.Handle.HalfBallCylinderCollar

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Handle

theorem exists_flat_cap_collar_rounding_scale
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F) (v : sphere (0 : E) 1)
    (c : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) (E × ℝ) F ∞)
    (e : PartialDiffeomorph 𝓘(ℝ, F) ((𝓡 n).prod 𝓘(ℝ, ℝ × ℝ))
      F (sphere (0 : E) 1 × (ℝ × ℝ)) ∞)
    {σ δ : ℝ} (hσ : σ ≠ 0) (hδ : 0 < δ)
    (hK : closedBall (0 : E) 1 ×ˢ {(0 : ℝ)} ⊆ c.source)
    (hc : ∀ p, c p = Ψ ((EuclideanGeometry.halfBallCylinderMap p).1, σ⁻¹ * p.2))
    (hsource : Ψ '' (sphere (0 : E) 1 ×ˢ {(0 : ℝ)}) ⊆ e.source)
    (he : ∀ p : E × ℝ, e (Ψ p) =
      (DifferentialGeometry.Topology.Manifold.sphereDirection v p.1,
        (1 - ‖p.1‖ ^ 2, σ * p.2))) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε < 1 / 8 ∧
      {q : sphere (0 : E) 1 × (ℝ × ℝ) | |q.2.1| ≤ ε ∧ |q.2.2| ≤ ε} ⊆
        (c.symm.toOpenPartialHomeomorph.trans (OpenPartialHomeomorph.halfBallCorner 1 v)).target ∧
      {q : sphere (0 : E) 1 × (ℝ × ℝ) | |q.2.1| ≤ ε ∧ |q.2.2| ≤ ε} ⊆ e.target ∧
      ∀ q : sphere (0 : E) 1 × (ℝ × ℝ), |q.2.1| ≤ ε → |q.2.2| ≤ ε →
        e.toOpenPartialHomeomorph.symm q = c ((OpenPartialHomeomorph.halfBallCorner 1 v).symm q) := by
  let _ : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [(Fact.out : Module.finrank ℝ E = n + 1)]
    omega)
  let e₀ := OpenPartialHomeomorph.halfBallCorner 1 v
  let d := c.symm.toOpenPartialHomeomorph.trans e₀
  let N := (d.target ∩ d.symm ⁻¹' e.source) ∩ e.target
  have hN : IsOpen N :=
    (d.continuousOn_symm.isOpen_inter_preimage d.open_target e.open_source).inter e.open_target
  have hzero : univ ×ˢ {(0 : ℝ × ℝ)} ⊆ N := by
    rintro ⟨θ, q⟩ ⟨_, hq⟩
    have hq' : q = 0 := hq
    subst q
    have h₀ : e₀.symm (θ, 0) = (θ.val, 0) := by
      simp [e₀, OpenPartialHomeomorph.halfBallCorner_symm_apply]
    have hdt : (θ, (0 : ℝ × ℝ)) ∈ d.target := by
      refine ⟨?_, ?_⟩
      · change 0 < (1 : ℝ) ^ 2 - 0 - 0 ^ 2
        norm_num
      · change e₀.symm (θ, 0) ∈ c.source
        rw [h₀]
        exact hK ⟨sphere_subset_closedBall θ.property, rfl⟩
    have hds : d.symm (θ, 0) = Ψ (θ.val, 0) := by
      change c (e₀.symm (θ, 0)) = _
      rw [h₀, hc, EuclideanGeometry.halfBallCylinderMap_apply_zero, mul_zero]
    have hes : Ψ (θ.val, 0) ∈ e.source := hsource ⟨(θ.val, 0), ⟨θ.property, rfl⟩, rfl⟩
    have hezero : e (Ψ (θ.val, 0)) = (θ, (0 : ℝ × ℝ)) := by
      rw [he]
      have hdir : DifferentialGeometry.Topology.Manifold.sphereDirection v θ.val = θ := by
        simpa only [one_smul] using
          DifferentialGeometry.Topology.Manifold.sphereDirection_pos_smul v θ zero_lt_one
      simp only [hdir, norm_eq_of_mem_sphere, one_pow, sub_self, mul_zero]
      rfl
    refine ⟨⟨hdt, ?_⟩, hezero ▸ e.map_source hes⟩
    change d.symm (θ, 0) ∈ e.source
    rw [hds]
    exact hes
  obtain ⟨A, B, _, hB, hA, hBzero, hAB⟩ :=
    generalized_tube_lemma (isCompact_univ (X := sphere (0 : E) 1))
      (isCompact_singleton (x := (0 : ℝ × ℝ))) hN hzero
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.mp hB 0 (hBzero (mem_singleton _))
  let ε := min (δ / 2) (min (r / 2) (1 / 16))
  have hε : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  have hεr : ε < r := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hεsmall : ε < 1 / 8 := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num)
  have hbox : {q : sphere (0 : E) 1 × (ℝ × ℝ) | |q.2.1| ≤ ε ∧ |q.2.2| ≤ ε} ⊆ N := by
    intro q hq
    apply hAB
    refine ⟨hA (mem_univ _), hrB ?_⟩
    rw [mem_ball_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (max_le hq.1 hq.2).trans_lt hεr
  refine ⟨ε, hε, hεδ, hεsmall, fun q hq => (hbox hq).1.1,
    fun q hq => (hbox hq).2, ?_⟩
  intro q hu hv
  have hq := hbox ⟨hu, hv⟩
  have hq₀ : q ∈ e₀.target := hq.1.1.1
  let p := e₀.symm q
  have hp : 3 / 4 ≤ ‖p.1‖ ^ 2 := by
    have heq := OpenPartialHomeomorph.halfBallCorner_symm_norm_sq_add_sq 1 v hq₀
    have ht : p.2 = q.2.2 := rfl
    change ‖p.1‖ ^ 2 + p.2 ^ 2 = 1 ^ 2 - q.2.1 at heq
    rw [ht] at heq
    obtain ⟨hl, hh⟩ := abs_le.mp hv
    have hu' := (le_abs_self q.2.1).trans hu
    nlinarith
  have hcompare : e (c p) = q := by
    rw [hc, he]
    change (_, 1 - ‖(EuclideanGeometry.halfBallCylinderMap p).1‖ ^ 2,
      σ * (σ⁻¹ * p.2)) = q
    rw [mul_inv_cancel_left₀ hσ]
    calc
      _ = PartialDiffeomorph.cylinderCorner (n := n) 1 v
          (EuclideanGeometry.halfBallCylinderMap p) := by
            rw [PartialDiffeomorph.cylinderCorner_apply]
            simp only [one_pow]
            rfl
      _ = PartialDiffeomorph.halfBallCorner (n := n) 1 v p :=
        EuclideanGeometry.cylinderCorner_halfBallCylinderMap v hp
      _ = q := e₀.right_inv hq₀
  have hcp : c p ∈ e.source := hq.1.2
  calc
    e.toOpenPartialHomeomorph.symm q = e.toOpenPartialHomeomorph.symm (e (c p)) := by rw [hcompare]
    _ = c p := e.toOpenPartialHomeomorph.left_inv hcp

theorem exists_flat_cap_collar_rounding_eq
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F) (v : sphere (0 : E) 1)
    (c : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) (E × ℝ) F ∞)
    (e : PartialDiffeomorph 𝓘(ℝ, F) ((𝓡 n).prod 𝓘(ℝ, ℝ × ℝ))
      F (sphere (0 : E) 1 × (ℝ × ℝ)) ∞)
    {A : Set F} {σ δ : ℝ} (hσ : σ ≠ 0) (hδ : 0 < δ)
    (hK : closedBall (0 : E) 1 ×ˢ {(0 : ℝ)} ⊆ c.source)
    (hc : ∀ p, c p = Ψ ((EuclideanGeometry.halfBallCylinderMap p).1, σ⁻¹ * p.2))
    (hsource : Ψ '' (sphere (0 : E) 1 ×ˢ {(0 : ℝ)}) ⊆ e.source)
    (he : ∀ p : E × ℝ, e (Ψ p) =
      (DifferentialGeometry.Topology.Manifold.sphereDirection v p.1,
        (1 - ‖p.1‖ ^ 2, σ * p.2)))
    (hcA : c.toOpenPartialHomeomorph.IsImage
      {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} A)
    (hraw : ∀ q ∈ e.target, e.toOpenPartialHomeomorph.symm q ∈ A ↔ 0 ≤ q.2.1 ∧ 0 ≤ q.2.2) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε < 1 / 8 ∧
      {q : sphere (0 : E) 1 × (ℝ × ℝ) | |q.2.1| ≤ ε ∧ |q.2.2| ≤ ε} ⊆
        (c.symm.toOpenPartialHomeomorph.trans (OpenPartialHomeomorph.halfBallCorner 1 v)).target ∧
      {q : sphere (0 : E) 1 × (ℝ × ℝ) | |q.2.1| ≤ ε ∧ |q.2.2| ≤ ε} ⊆ e.target ∧
      ∀ η : ℝ, 0 < η → η ≤ ε →
        e.toOpenPartialHomeomorph.smoothAbsQuadrantSet A η =
          (c.symm.toOpenPartialHomeomorph.trans
            (OpenPartialHomeomorph.halfBallCorner 1 v)).smoothAbsQuadrantSet A η ∧
        c.toOpenPartialHomeomorph.IsImage
          {p : E × ℝ | Real.smoothMax η (‖p.1‖ ^ 2 + p.2 ^ 2 - 1) (-p.2) ≤ 0}
          (e.toOpenPartialHomeomorph.smoothAbsQuadrantSet A η) := by
  obtain ⟨ε, hε, hεδ, hεsmall, hboxd, hboxe, hinv⟩ :=
    exists_flat_cap_collar_rounding_scale Ψ v c e hσ hδ hK hc hsource he
  let e₀ := OpenPartialHomeomorph.halfBallCorner 1 v
  let d := c.symm.toOpenPartialHomeomorph.trans e₀
  have hrawd : ∀ q ∈ d.target, d.symm q ∈ A ↔ 0 ≤ q.2.1 ∧ 0 ≤ q.2.2 := by
    intro q hq
    change c (e₀.symm q) ∈ A ↔ _
    apply (hcA hq.2).trans
    simpa only [e₀, mem_ofPred_eq, one_pow] using
      OpenPartialHomeomorph.halfBallCorner_symm_mem_halfBall 1 v hq.1
  refine ⟨ε, hε, hεδ, hεsmall, hboxd, hboxe, ?_⟩
  intro η hη hηε
  have hstrip : {q : sphere (0 : E) 1 × (ℝ × ℝ) |
      0 ≤ q.2.1 ∧ 0 ≤ q.2.2 ∧ q.2.1 + q.2.2 ≤ η} ⊆
      {q | |q.2.1| ≤ ε ∧ |q.2.2| ≤ ε} := by
    intro q hq
    change |q.2.1| ≤ ε ∧ |q.2.2| ≤ ε
    rw [abs_of_nonneg hq.1, abs_of_nonneg hq.2.1]
    constructor <;> linarith [hq.1, hq.2.1, hq.2.2]
  have heq : e.toOpenPartialHomeomorph.smoothAbsQuadrantSet A η = d.smoothAbsQuadrantSet A η := by
    apply OpenPartialHomeomorph.smoothAbsQuadrantSet_eq_of_eqOn_symm e.toOpenPartialHomeomorph d
      hη hraw hrawd (hstrip.trans hboxe) (hstrip.trans hboxd)
    intro q hq
    exact hinv q (hstrip hq).1 (hstrip hq).2
  refine ⟨heq, ?_⟩
  have himage := hcA.smoothAbsQuadrantSet e₀ η
  have hmodel := OpenPartialHomeomorph.smoothAbsQuadrantSet_halfBallCorner 1 v hη
    (show η < min 1 ((1 : ℝ) ^ 2) by norm_num; linarith)
  simp only [one_pow] at hmodel
  change c.toOpenPartialHomeomorph.IsImage _ (d.smoothAbsQuadrantSet A η) at himage
  rw [← heq] at himage
  simpa only [e₀, one_pow, hmodel] using himage

end DifferentialGeometry.Topology.Handle

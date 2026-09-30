import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem derivWithin_slice_eq_fderivWithin_apply
    {F : ℝ × ℝ → G} {J : Set ℝ} {x t : ℝ} (ht : t ∈ J)
    {F' : (ℝ × ℝ) →L[ℝ] G} (hF : HasFDerivWithinAt F F' (univ ×ˢ J) (x, t)) :
    derivWithin (fun y : ℝ => F (y, t)) univ x = F' (1, 0) := by
  have hγ : HasFDerivWithinAt (fun y : ℝ => (y, t)) ((1 : ℝ →L[ℝ] ℝ).prod 0) univ x :=
    (hasFDerivWithinAt_id x univ).prodMk (hasFDerivWithinAt_const t x univ)
  have hst : Set.MapsTo (fun y : ℝ => (y, t)) univ ((univ : Set ℝ) ×ˢ J) :=
    fun y _ => ⟨mem_univ y, ht⟩
  have hcomp : HasDerivWithinAt (fun y : ℝ => F (y, t))
      ((F'.comp ((1 : ℝ →L[ℝ] ℝ).prod 0)) 1) univ x := (hF.comp x hγ hst).hasDerivWithinAt
  rw [hcomp.derivWithin uniqueDiffWithinAt_univ]
  simp

theorem iteratedDerivWithin_slice_eq_iteratedFDerivWithin_apply
    {F : ℝ × ℝ → G} {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ J)) :
    ∀ (n : ℕ) (x t : ℝ), t ∈ J →
      iteratedDerivWithin n (fun y : ℝ => F (y, t)) univ x =
        (iteratedFDerivWithin ℝ n F (univ ×ˢ J) (x, t)) (fun _ : Fin n => (1, 0)) := by
  intro n
  induction n with
  | zero =>
    intro x t ht
    simp
  | succ n IH =>
    intro x t ht
    rw [iteratedDerivWithin_succ]
    have hfun : iteratedDerivWithin n (fun y' : ℝ => F (y', t)) univ =
        fun y : ℝ => (iteratedFDerivWithin ℝ n F (univ ×ˢ J) (y, t))
          (fun _ : Fin n => (1, 0)) := by
      funext y
      exact IH y t ht
    rw [hfun]
    have hsJ : UniqueDiffOn ℝ ((univ : Set ℝ) ×ˢ J) := UniqueDiffOn.prod uniqueDiffOn_univ hJ
    have hnum : ((n : ℕ) : ℕ∞ω) < ∞ := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)
    have hmt : (x, t) ∈ (univ : Set ℝ) ×ˢ J := ⟨mem_univ x, ht⟩
    have hins : UniqueDiffOn ℝ (insert (x, t) (univ ×ˢ J)) := by
      rw [insert_eq_of_mem hmt]
      exact hsJ
    have hdiff : HasFDerivWithinAt (iteratedFDerivWithin ℝ n F (univ ×ˢ J))
        (fderivWithin ℝ (iteratedFDerivWithin ℝ n F (univ ×ˢ J)) (univ ×ˢ J) (x, t))
        (univ ×ˢ J) (x, t) :=
      ((hF (x, t) ⟨mem_univ x, ht⟩).differentiableWithinAt_iteratedFDerivWithin hnum hins)
        |>.hasFDerivWithinAt
    have happ := hdiff.continuousMultilinear_apply_const (fun _ : Fin n => (1, 0))
    rw [derivWithin_slice_eq_fderivWithin_apply ht happ]
    have htail : (Fin.tail (fun _ : Fin (n + 1) => ((1 : ℝ), (0 : ℝ))) : Fin n → ℝ × ℝ) =
        fun _ => ((1 : ℝ), (0 : ℝ)) := by
      funext i
      rfl
    simp only [ContinuousLinearMap.flipMultilinear_apply_apply, iteratedFDerivWithin_succ_apply_left,
      htail]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem norm_sub_apply_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (L₁ L₂ : (ℝ × ℝ) [×m]→L[ℝ] G) (u : Fin m → ℝ × ℝ) (hu : ‖u‖ ≤ 1) :
    ‖L₁ u - L₂ u‖ ≤ ‖L₁ - L₂‖ := by
  have h : (L₁ - L₂) u = L₁ u - L₂ u := sub_apply L₁ L₂ u
  rw [← h]
  calc ‖(L₁ - L₂) u‖ ≤ ‖L₁ - L₂‖ * ∏ i, ‖u i‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ ‖L₁ - L₂‖ * 1 := by
        have hprod : ∏ i, ‖u i‖ ≤ ∏ _ : Fin m, (1 : ℝ) :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
            (fun i _ => (norm_le_pi_norm u i).trans hu)
        simpa using mul_le_mul_of_nonneg_left hprod (norm_nonneg (L₁ - L₂))
    _ = ‖L₁ - L₂‖ := mul_one _

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem contDiffOn_liftMap {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {c : CurveMap M} {J : Set ℝ} (hc : c.SmoothOn (I := I) J) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => e.map (c.lift q.1 q.2)) (univ ×ˢ J) :=
  (e.smooth.comp_contMDiffOn hc).contDiffOn

theorem exists_pos_le_of_continuousOn_pos {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < f x) :
    ∃ η > 0, ∀ x ∈ Icc (0 : ℝ) 1, η ≤ f x := by
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, le_rfl, zero_le_one⟩ hf
  refine ⟨f x₀ / 2, half_pos (hpos x₀ hx₀), fun x hx => ?_⟩
  exact (by linarith [hpos x₀ hx₀] : f x₀ / 2 ≤ f x₀).trans (hmin hx)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem exists_nhds_slice_jet_variation {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {a d : ℝ} (had : a < d) {c : CurveMap M} (hc : c.SmoothOn (I := I) (Icc a d))
    (m : ℕ) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a d) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Icc a d, |t - t₀| < δ → ∀ x ∈ Icc (0 : ℝ) 1,
      ‖(iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (c.lift q.1 q.2)) (univ ×ˢ Icc a d)
            (x, t)) (fun _ : Fin m => (1, 0)) -
        (iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (c.lift q.1 q.2)) (univ ×ˢ Icc a d)
            (x, t₀)) (fun _ : Fin m => (1, 0))‖ < ε := by
  let F : ℝ × ℝ → EuclideanSpace ℝ (Fin N) := fun q => e.map (c.lift q.1 q.2)
  have hF : ContDiffOn ℝ ∞ F (univ ×ˢ Icc a d) := contDiffOn_liftMap e hc
  have hJ : UniqueDiffOn ℝ ((univ : Set ℝ) ×ˢ Icc a d) :=
    UniqueDiffOn.prod (uniqueDiffOn_univ (E := ℝ)) (uniqueDiffOn_Icc had)
  have hjet_cont : Continuous (fun L : ((ℝ × ℝ) [×m]→L[ℝ] EuclideanSpace ℝ (Fin N)) =>
      L (fun _ : Fin m => ((1 : ℝ), (0 : ℝ)))) := continuous_eval_const _
  have hjet : ContinuousOn
      (fun q : ℝ × ℝ => (iteratedFDerivWithin ℝ m F (univ ×ˢ Icc a d) q) (fun _ : Fin m => (1, 0)))
      ((univ : Set ℝ) ×ˢ Icc a d) := by
    have hf : ContinuousOn (fun q : ℝ × ℝ => iteratedFDerivWithin ℝ m F (univ ×ˢ Icc a d) q)
        ((univ : Set ℝ) ×ˢ Icc a d) :=
      hF.continuousOn_iteratedFDerivWithin (WithTop.coe_le_coe.mpr le_top) hJ
    exact (ContinuousOn.comp
        (g := fun L : ((ℝ × ℝ) [×m]→L[ℝ] EuclideanSpace ℝ (Fin N)) =>
          L (fun _ : Fin m => ((1 : ℝ), (0 : ℝ))))
        (s := (univ : Set ℝ) ×ˢ Icc a d) (t := univ)
        hjet_cont.continuousOn hf (fun _ _ => mem_univ _)).congr (fun q _ => rfl)
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc a d) := isCompact_Icc.prod isCompact_Icc
  have hKsub : Icc (0 : ℝ) 1 ×ˢ Icc a d ⊆ (univ : Set ℝ) ×ˢ Icc a d :=
    fun q hq => ⟨mem_univ _, hq.2⟩
  obtain ⟨δ, hδ, hδb⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous (hjet.mono hKsub)) ε hε
  refine ⟨δ, hδ, fun t ht hlt x hx => ?_⟩
  have hdist : dist ((x, t) : ℝ × ℝ) (x, t₀) = |t - t₀| := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg (t - t₀))]
  have hmem₁ : ((x, t) : ℝ × ℝ) ∈ Icc (0 : ℝ) 1 ×ˢ Icc a d := ⟨hx, ht⟩
  have hmem₂ : ((x, t₀) : ℝ × ℝ) ∈ Icc (0 : ℝ) 1 ×ˢ Icc a d := ⟨hx, ht₀⟩
  have := hδb _ hmem₁ _ hmem₂ (by rw [hdist]; exact hlt)
  rwa [dist_eq_norm] at this

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem slice_jet_eq_jet_component {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {a d : ℝ} (had : a < d) {c : CurveMap M} (hc : c.SmoothOn (I := I) (Icc a d))
    (m : ℕ) {x t : ℝ} (ht : t ∈ Icc a d) :
    iteratedDeriv m (fun y : ℝ => e.map (c.lift y t)) x =
      (iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (c.lift q.1 q.2)) (univ ×ˢ Icc a d)
        (x, t)) (fun _ : Fin m => (1, 0)) := by
  rw [← iteratedDerivWithin_univ]
  exact iteratedDerivWithin_slice_eq_iteratedFDerivWithin_apply (uniqueDiffOn_Icc had)
    (contDiffOn_liftMap e hc) m x t ht

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem continuousOn_iteratedDeriv_embedding {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (d : SmoothImmersion (I := I) (M := M)) (m : ℕ) :
    ContinuousOn (fun x : ℝ => iteratedDeriv m (fun y : ℝ => e.map (d.map (y : AddCircle (1 : ℝ)))) x)
      (Icc (0 : ℝ) 1) :=
  ((e.smooth.comp (d.smooth (I := I))).contDiff.continuous_iteratedDeriv m
    (WithTop.coe_le_coe.mpr le_top)).continuousOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem exists_nhds_slice_jet_close {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {a d : ℝ} (had : a < d) {P : Type*} [TopologicalSpace P] {c : P → CurveMap M}
    (hc : @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) c)
    (hs : ∀ p, (c p).SmoothOn (I := I) (Icc a d))
    (m : ℕ) (q₀ : P × Icc a d) {η : ℝ} (hη : 0 < η) :
    ∃ O ∈ 𝓝 q₀, ∀ q ∈ O, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv m (fun y : ℝ => e.map ((c q.1).lift y q.2.1)) x -
       iteratedDeriv m (fun y : ℝ => e.map ((c q₀.1).lift y q₀.2.1)) x‖ < η :=
  letI : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc a d)
  by
    have hW : c ⁻¹' {r : CurveMap M | ∃ ρ : ℝ, ρ < η / 2 ∧
        ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc a d,
          ‖iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map (r.lift s.1 s.2))
              (univ ×ˢ Icc a d) q -
            iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q₀.1).lift s.1 s.2))
              (univ ×ˢ Icc a d) q‖ ≤ ρ} ∈ 𝓝 q₀.1 := by
      have hcat : ContinuousAt c q₀.1 := hc.continuousAt
      simp only [ContinuousAt, TopologicalSpace.tendsto_nhds_generateFrom_iff] at hcat
      exact hcat _
        ⟨c q₀.1, m, η / 2, by linarith, rfl⟩
        ⟨0, by linarith, fun q _ => by simp⟩
    obtain ⟨δ, hδpos, hδb⟩ := exists_nhds_slice_jet_variation e had (hs q₀.1) m q₀.2.2
      (by linarith : 0 < η / 2)
    refine ⟨{q : P × Icc a d | c q.1 ∈ {r : CurveMap M | ∃ ρ : ℝ, ρ < η / 2 ∧
        ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc a d,
          ‖iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map (r.lift s.1 s.2))
              (univ ×ˢ Icc a d) q -
            iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q₀.1).lift s.1 s.2))
              (univ ×ˢ Icc a d) q‖ ≤ ρ} ∧ |q.2.1 - q₀.2.1| < δ}, ?_, ?_⟩
    · refine Filter.inter_mem ?_ ?_
      · exact continuous_fst.continuousAt.preimage_mem_nhds hW
      · exact (continuous_subtype_val.continuousAt.comp continuous_snd.continuousAt).preimage_mem_nhds
          (Metric.ball_mem_nhds q₀.2.1 hδpos)
    · intro q hq x hx
      obtain ⟨ρ, hρ, hρb⟩ := hq.1
      have hu : ‖(fun _ : Fin m => ((1 : ℝ), (0 : ℝ)))‖ ≤ 1 := by
        calc ‖(fun _ : Fin m => ((1 : ℝ), (0 : ℝ)))‖
            ≤ ‖(((1 : ℝ), (0 : ℝ)) : ℝ × ℝ)‖ := pi_norm_const_le (((1 : ℝ), (0 : ℝ)))
          _ = 1 := by simp
      have heq : iteratedDeriv m (fun y : ℝ => e.map ((c q.1).lift y q.2.1)) x =
          (iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q.1).lift s.1 s.2))
            (univ ×ˢ Icc a d) (x, q.2.1)) (fun _ : Fin m => (1, 0)) :=
        slice_jet_eq_jet_component e had (hs q.1) m q.2.2
      have heq₀ : iteratedDeriv m (fun y : ℝ => e.map ((c q₀.1).lift y q₀.2.1)) x =
          (iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q₀.1).lift s.1 s.2))
            (univ ×ˢ Icc a d) (x, q₀.2.1)) (fun _ : Fin m => (1, 0)) :=
        slice_jet_eq_jet_component e had (hs q₀.1) m q₀.2.2
      rw [heq, heq₀]
      have hsplit : ‖(iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q.1).lift s.1 s.2))
              (univ ×ˢ Icc a d) (x, q.2.1)) (fun _ : Fin m => (1, 0)) -
            (iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q₀.1).lift s.1 s.2))
              (univ ×ˢ Icc a d) (x, q₀.2.1)) (fun _ : Fin m => (1, 0))‖ ≤
          ‖(iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q.1).lift s.1 s.2))
              (univ ×ˢ Icc a d) (x, q.2.1)) (fun _ : Fin m => (1, 0)) -
            (iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q₀.1).lift s.1 s.2))
              (univ ×ˢ Icc a d) (x, q.2.1)) (fun _ : Fin m => (1, 0))‖ +
          ‖(iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q₀.1).lift s.1 s.2))
              (univ ×ˢ Icc a d) (x, q.2.1)) (fun _ : Fin m => (1, 0)) -
            (iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q₀.1).lift s.1 s.2))
              (univ ×ˢ Icc a d) (x, q₀.2.1)) (fun _ : Fin m => (1, 0))‖ := by
        simpa only [dist_eq_norm] using dist_triangle
          ((iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q.1).lift s.1 s.2))
            (univ ×ˢ Icc a d) (x, q.2.1)) (fun _ : Fin m => (1, 0)))
          ((iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q₀.1).lift s.1 s.2))
            (univ ×ˢ Icc a d) (x, q.2.1)) (fun _ : Fin m => (1, 0)))
          ((iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q₀.1).lift s.1 s.2))
            (univ ×ˢ Icc a d) (x, q₀.2.1)) (fun _ : Fin m => (1, 0)))
      have hb1 : ‖(iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q.1).lift s.1 s.2))
              (univ ×ˢ Icc a d) (x, q.2.1)) (fun _ : Fin m => (1, 0)) -
            (iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q₀.1).lift s.1 s.2))
              (univ ×ˢ Icc a d) (x, q.2.1)) (fun _ : Fin m => (1, 0))‖ ≤ ρ :=
        (norm_sub_apply_le _ _ _ hu).trans (hρb (x, q.2.1) ⟨hx, q.2.2⟩)
      have hb2 : ‖(iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q₀.1).lift s.1 s.2))
              (univ ×ˢ Icc a d) (x, q.2.1)) (fun _ : Fin m => (1, 0)) -
            (iteratedFDerivWithin ℝ m (fun s : ℝ × ℝ => e.map ((c q₀.1).lift s.1 s.2))
              (univ ×ˢ Icc a d) (x, q₀.2.1)) (fun _ : Fin m => (1, 0))‖ < η / 2 :=
        hδb q.2.1 q.2.2 hq.2 x hx
      linarith

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem continuousAt_slice_smoothImmersion {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {a d : ℝ} (had : a < d) {P : Type*} [TopologicalSpace P] {c : P → CurveMap M}
    (hc : @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) c)
    (hs : ∀ p, (c p).SmoothOn (I := I) (Icc a d))
    (hi : ∀ p, (c p).ImmersedOn (I := I) (Icc a d)) (q₀ : P × Icc a d) :
    @ContinuousAt (P × Icc a d) (SmoothImmersion (I := I) (M := M)) inferInstance
      (smoothImmersionTopology e)
      (fun q => SmoothImmersion.slice (c q.1) (hs q.1) (hi q.1) q.2.1 q.2.2) q₀ :=
  letI : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  by
    rw [ContinuousAt, TopologicalSpace.tendsto_nhds_generateFrom_iff]
    rintro V ⟨c₁, m, ε, hε, rfl⟩ hV
    have hgbase : ContinuousOn (fun x : ℝ =>
        iteratedDeriv m (fun y : ℝ => e.map ((c q₀.1).lift y q₀.2.1)) x) (Icc (0 : ℝ) 1) :=
      continuousOn_iteratedDeriv_embedding e
        (SmoothImmersion.slice (c q₀.1) (hs q₀.1) (hi q₀.1) q₀.2.1 q₀.2.2) m
    have hgc₁ : ContinuousOn (fun x : ℝ =>
        iteratedDeriv m (fun y : ℝ => e.map (c₁.map (y : AddCircle (1 : ℝ)))) x) (Icc (0 : ℝ) 1) :=
      continuousOn_iteratedDeriv_embedding e c₁ m
    have hgap : ContinuousOn (fun x : ℝ => ε -
        ‖iteratedDeriv m (fun y : ℝ => e.map ((c q₀.1).lift y q₀.2.1)) x -
          iteratedDeriv m (fun y : ℝ => e.map (c₁.map (y : AddCircle (1 : ℝ)))) x‖)
        (Icc (0 : ℝ) 1) :=
      continuousOn_const.sub (hgbase.sub hgc₁).norm
    obtain ⟨η, hηpos, hη⟩ := exists_pos_le_of_continuousOn_pos hgap
      (fun x hx => sub_pos.mpr (hV x hx))
    obtain ⟨O, hO, hOb⟩ := exists_nhds_slice_jet_close e had hc hs m q₀
      (by linarith : 0 < η / 2)
    refine Filter.mem_of_superset hO ?_
    intro q hq x hx
    change ‖iteratedDeriv m (fun y : ℝ => e.map ((c q.1).lift y q.2.1)) x -
        iteratedDeriv m (fun y : ℝ => e.map (c₁.map (y : AddCircle (1 : ℝ)))) x‖ < ε
    have h1 := hOb q hq x hx
    have h2 : ‖iteratedDeriv m (fun y : ℝ => e.map ((c q₀.1).lift y q₀.2.1)) x -
        iteratedDeriv m (fun y : ℝ => e.map (c₁.map (y : AddCircle (1 : ℝ)))) x‖ ≤ ε - η := by
      linarith [hη x hx]
    have h3 : ‖iteratedDeriv m (fun y : ℝ => e.map ((c q.1).lift y q.2.1)) x -
          iteratedDeriv m (fun y : ℝ => e.map (c₁.map (y : AddCircle (1 : ℝ)))) x‖ ≤
        ‖iteratedDeriv m (fun y : ℝ => e.map ((c q.1).lift y q.2.1)) x -
          iteratedDeriv m (fun y : ℝ => e.map ((c q₀.1).lift y q₀.2.1)) x‖ +
        ‖iteratedDeriv m (fun y : ℝ => e.map ((c q₀.1).lift y q₀.2.1)) x -
          iteratedDeriv m (fun y : ℝ => e.map (c₁.map (y : AddCircle (1 : ℝ)))) x‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (iteratedDeriv m (fun y : ℝ => e.map ((c q.1).lift y q.2.1)) x)
        (iteratedDeriv m (fun y : ℝ => e.map ((c q₀.1).lift y q₀.2.1)) x)
        (iteratedDeriv m (fun y : ℝ => e.map (c₁.map (y : AddCircle (1 : ℝ)))) x)
    linarith



namespace CurveMap


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem X_congr {c d : CurveMap M} {t : ℝ} (h : ∀ z : ℝ, c.lift z t = d.lift z t) (x : ℝ) :
    c.X (I := I) x t = d.X (I := I) x t := by
  unfold CurveMap.X
  rw [funext h]
  rfl

omit [CompleteSpace E] in
theorem curvatureVector_congr {c d : CurveMap M} {g : ℝ → SmoothRiemannianMetric I M}
    {t : ℝ} (h : ∀ z : ℝ, c.lift z t = d.lift z t) (x : ℝ) :
    c.curvatureVector g x t = d.curvatureVector g x t := by
  have hX : ∀ y : ℝ, c.X (I := I) y t = d.X (I := I) y t := fun y => X_congr h y
  have hspeed : ∀ y : ℝ, c.speed g y t = d.speed g y t := by
    intro y
    unfold CurveMap.speed
    rw [h y, hX y]
  simp only [CurveMap.curvatureVector, CurveMap.Ds, CurveMap.unitTangent, CurveMap.Dx]
  rw [funext h]
  simp only [hX, hspeed]
  rfl

omit [CompleteSpace E] in
theorem IsSolutionOn.mono {g : ℝ → SmoothRiemannianMetric I M} {J K : Set ℝ}
    {c : CurveMap M}
    (hK : K ⊆ J) (huniq : ∀ t ∈ K, UniqueMDiffWithinAt 𝓘(ℝ, ℝ) K t)
    (h : CurveMap.IsSolutionOn (I := I) c g J) :
    CurveMap.IsSolutionOn (I := I) c g K where
  smooth := h.smooth.mono (Set.prod_mono Subset.rfl hK)
  immersed := fun x t ht => h.immersed x t (hK ht)
  equation := by
    intro x t ht
    have hMD : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => c.lift x s) J t :=
      (c.time_slice_contMDiffWithinAt (I := I) J h.smooth x t (hK ht)).mdifferentiableWithinAt
        (by simp)
    have hmem : J ∈ 𝓝[K] t := Filter.mem_of_superset self_mem_nhdsWithin hK
    rw [CurveMap.velocity,
      hMD.mfderivWithin_mono_of_mem_nhdsWithin (huniq t ht) hmem, ← CurveMap.velocity]
    exact h.equation x t (hK ht)

omit [CompleteSpace E] in
theorem IsSolutionOn.mono_Icc {g : ℝ → SmoothRiemannianMetric I M} {a a' b' b : ℝ}
    (ha : a ≤ a') (hb : b' ≤ b) (hab : a' < b') {c : CurveMap M}
    (h : CurveMap.IsSolutionOn (I := I) c g (Icc a b)) :
    CurveMap.IsSolutionOn (I := I) c g (Icc a' b') :=
  h.mono (Icc_subset_Icc ha hb)
    (fun t ht => ((uniqueDiffOn_Icc hab) t ht).uniqueMDiffWithinAt)

omit [CompleteSpace E] in
theorem IsSolutionOn.glue {g : ℝ → SmoothRiemannianMetric I M} {a t₀ T u : ℝ}
    (hat₀ : a ≤ t₀) (ht₀T : t₀ < T) (hTu : T < u)
    {c₁ c₂ : CurveMap M}
    (h₁ : CurveMap.IsSolutionOn (I := I) c₁ g (Icc a T))
    (h₂ : CurveMap.IsSolutionOn (I := I) c₂ g (Icc t₀ u))
    (hagree : ∀ z t, t ∈ Icc t₀ T → c₁ z t = c₂ z t) :
    CurveMap.IsSolutionOn (I := I) (fun z t => if t ≤ T then c₁ z t else c₂ z t) g
      (Icc a u) := by
  set cJ : CurveMap M := fun z t => if t ≤ T then c₁ z t else c₂ z t with hcJ
  have heq₁ : ∀ z t, t ≤ T → cJ z t = c₁ z t := by
    intro z t ht
    simp only [hcJ, ite_eq_left ht]
  have heq₂ : ∀ z t, t₀ < t → cJ z t = c₂ z t := by
    intro z t ht
    by_cases h : t ≤ T
    · simp only [hcJ, ite_eq_left h, hagree z t ⟨le_of_lt ht, h⟩]
    · simp only [hcJ, ite_eq_right h]
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, t⟩ := p
    rcases lt_trichotomy t T with hlt | heq | hgt
    · have hV : (univ : Set ℝ) ×ˢ Iio T ∈ 𝓝 (x, t) :=
        (isOpen_univ.prod isOpen_Iio).mem_nhds
          (by simp only [Set.mem_prod, mem_univ, true_and, Set.mem_Iio]; exact hlt)
      have hsub : ((univ : Set ℝ) ×ˢ Iio T) ∩ (univ ×ˢ Icc a u) ⊆
          univ ×ˢ Icc a T := by
        rintro ⟨y, s⟩ ⟨⟨-, hs⟩, ⟨-, hsa, hsu⟩⟩
        exact ⟨mem_univ _, hsa, le_of_lt hs⟩
      have hmem : (univ ×ˢ Icc a T) ∈ 𝓝[univ ×ˢ Icc a u] (x, t) :=
        mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨univ ×ˢ Iio T, hV, hsub⟩
      have h₁s : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun q : ℝ × ℝ => c₁.lift q.1 q.2)
          (univ ×ˢ Icc a T) (x, t) :=
        h₁.smooth (x, t) ⟨mem_univ _, hp.2.1, le_of_lt hlt⟩
      have hVT : (univ ×ˢ Iio T) ∈ 𝓝[univ ×ˢ Icc a u] (x, t) :=
        mem_nhdsWithin_iff_eventually.mpr (by filter_upwards [hV] with q hq _; exact hq)
      refine (h₁s.mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [hVT] with q hq
        exact heq₁ q.1 q.2 (le_of_lt hq.2)
      · exact heq₁ x t (le_of_lt hlt)
    · have htT : t₀ < t := by rw [heq]; exact ht₀T
      have htu : t < u := by rw [heq]; exact hTu
      have hmemU : (univ ×ˢ Icc t₀ u) ∈ 𝓝 (x, t) :=
        mem_of_superset
          ((isOpen_univ.prod isOpen_Ioo).mem_nhds
            (by simp only [Set.mem_prod, mem_univ, true_and, Set.mem_Ioo]
                exact ⟨htT, htu⟩))
          (Set.prod_mono Subset.rfl Ioo_subset_Icc_self)
      have hV : (univ : Set ℝ) ×ˢ Ioi t₀ ∈ 𝓝 (x, t) :=
        (isOpen_univ.prod isOpen_Ioi).mem_nhds
          (by simp only [Set.mem_prod, mem_univ, true_and, Set.mem_Ioi]; exact htT)
      have h₂s : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun q : ℝ × ℝ => c₂.lift q.1 q.2)
          (univ ×ˢ Icc t₀ u) (x, t) :=
        h₂.smooth (x, t) ⟨mem_univ _, le_of_lt htT, le_of_lt htu⟩
      have hevAt : (fun q : ℝ × ℝ => cJ.lift q.1 q.2) =ᶠ[𝓝 (x, t)]
          (fun q : ℝ × ℝ => c₂.lift q.1 q.2) := by
        filter_upwards [hV] with q hq
        exact heq₂ q.1 q.2 hq.2
      exact ((h₂s.contMDiffAt hmemU).congr_of_eventuallyEq hevAt).contMDiffWithinAt
    · have ht₀t : t₀ < t := lt_trans ht₀T hgt
      have hV : (univ : Set ℝ) ×ˢ Ioi T ∈ 𝓝 (x, t) :=
        (isOpen_univ.prod isOpen_Ioi).mem_nhds
          (by simp only [Set.mem_prod, mem_univ, true_and, Set.mem_Ioi]; exact hgt)
      have hsub : ((univ : Set ℝ) ×ˢ Ioi T) ∩ (univ ×ˢ Icc a u) ⊆
          univ ×ˢ Icc t₀ u := by
        rintro ⟨y, s⟩ ⟨⟨-, hs⟩, ⟨-, hsa, hsu⟩⟩
        exact ⟨mem_univ _, le_of_lt (lt_trans ht₀T hs), hsu⟩
      have hmem : (univ ×ˢ Icc t₀ u) ∈ 𝓝[univ ×ˢ Icc a u] (x, t) :=
        mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨univ ×ˢ Ioi T, hV, hsub⟩
      have h₂s : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun q : ℝ × ℝ => c₂.lift q.1 q.2)
          (univ ×ˢ Icc t₀ u) (x, t) :=
        h₂.smooth (x, t) ⟨mem_univ _, le_of_lt ht₀t, hp.2.2⟩
      have hVT : (univ ×ˢ Ioi T) ∈ 𝓝[univ ×ˢ Icc a u] (x, t) :=
        mem_nhdsWithin_iff_eventually.mpr (by filter_upwards [hV] with q hq _; exact hq)
      refine (h₂s.mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [hVT] with q hq
        exact heq₂ q.1 q.2 (lt_trans ht₀T hq.2)
      · exact heq₂ x t (lt_trans ht₀T hgt)
  · intro x t ht
    rcases lt_trichotomy t T with hlt | heq | hgt
    · rw [X_congr (I := I) (c := cJ) (d := c₁) (fun z => heq₁ z t (le_of_lt hlt)) x]
      exact h₁.immersed x t ⟨ht.1, le_of_lt hlt⟩
    · have ht₁ : a ≤ T := heq ▸ ht.1
      rw [heq]
      rw [X_congr (I := I) (c := cJ) (d := c₁) (fun z => heq₁ z T le_rfl) x]
      exact h₁.immersed x T ⟨ht₁, le_rfl⟩
    · have ht₀t : t₀ < t := lt_trans ht₀T hgt
      rw [X_congr (I := I) (c := cJ) (d := c₂) (fun z => heq₂ z t ht₀t) x]
      exact h₂.immersed x t ⟨le_of_lt ht₀t, ht.2⟩
  · intro x t ht
    rcases lt_trichotomy t T with hlt | heq | hgt
    · have hset : Icc a u =ᶠ[𝓝 t] Icc a T := by
        rw [Filter.eventuallyEqSet_iff]
        filter_upwards [isOpen_Iio.mem_nhds hlt] with s hs
        exact ⟨fun h => ⟨h.1, le_of_lt hs⟩, fun h => ⟨h.1, le_trans h.2 hTu.le⟩⟩
      have hev : (cJ.lift x) =ᶠ[𝓝[Icc a u] t] (c₁.lift x) := by
        filter_upwards [mem_nhdsWithin_iff_eventually.mpr
          (by filter_upwards [isOpen_Iio.mem_nhds hlt] with s hs _; exact hs)] with s hs
        exact heq₁ x s (le_of_lt hs)
      have hA : mfderivWithin 𝓘(ℝ, ℝ) I (cJ.lift x) (Icc a u) t =
          mfderivWithin 𝓘(ℝ, ℝ) I (c₁.lift x) (Icc a u) t :=
        hev.mfderivWithin_eq (heq₁ x t (le_of_lt hlt))
      have hB : mfderivWithin 𝓘(ℝ, ℝ) I (c₁.lift x) (Icc a u) t =
          mfderivWithin 𝓘(ℝ, ℝ) I (c₁.lift x) (Icc a T) t :=
        mfderivWithin_congr_set hset
      have hvel : cJ.velocity (I := I) (Icc a u) x t = c₁.velocity (I := I) (Icc a T) x t := by
        unfold CurveMap.velocity
        rw [hA, hB]
        rfl
      rw [hvel, h₁.equation x t ⟨ht.1, le_of_lt hlt⟩]
      exact (curvatureVector_congr (c := cJ) (d := c₁) (g := g) (t := t)
        (fun z => heq₁ z t (le_of_lt hlt)) x).symm
    · have htT : t₀ < t := by rw [heq]; exact ht₀T
      have htu : t < u := by rw [heq]; exact hTu
      have hat : max a t₀ < t := by rw [max_eq_right hat₀]; exact htT
      have hset : Icc a u =ᶠ[𝓝 t] Icc t₀ u := by
        rw [Filter.eventuallyEqSet_iff]
        filter_upwards [isOpen_Ioo.mem_nhds ⟨hat, htu⟩] with s hs
        exact ⟨fun _ => ⟨le_of_lt (lt_of_le_of_lt (le_max_right a t₀) hs.1), hs.2.le⟩,
          fun _ => ⟨le_trans hat₀ (le_of_lt (lt_of_le_of_lt (le_max_right a t₀) hs.1)), hs.2.le⟩⟩
      have hev : (cJ.lift x) =ᶠ[𝓝[Icc a u] t] (c₂.lift x) := by
        filter_upwards [mem_nhdsWithin_iff_eventually.mpr
          (by filter_upwards [isOpen_Ioi.mem_nhds htT] with s hs _; exact hs)] with s hs
        exact heq₂ x s hs
      have hA : mfderivWithin 𝓘(ℝ, ℝ) I (cJ.lift x) (Icc a u) t =
          mfderivWithin 𝓘(ℝ, ℝ) I (c₂.lift x) (Icc a u) t :=
        hev.mfderivWithin_eq (heq₂ x t htT)
      have hB : mfderivWithin 𝓘(ℝ, ℝ) I (c₂.lift x) (Icc t₀ u) t =
          mfderivWithin 𝓘(ℝ, ℝ) I (c₂.lift x) (Icc a u) t :=
        mfderivWithin_congr_set hset.symm
      have hvel : cJ.velocity (I := I) (Icc a u) x t = c₂.velocity (I := I) (Icc t₀ u) x t := by
        unfold CurveMap.velocity
        rw [hA, hB]
        rfl
      rw [hvel, h₂.equation x t ⟨le_of_lt htT, le_of_lt htu⟩]
      exact (curvatureVector_congr (c := cJ) (d := c₂) (g := g) (t := t)
        (fun z => heq₂ z t htT) x).symm
    · have ht₀t : t₀ < t := lt_trans ht₀T hgt
      have hset : Icc a u =ᶠ[𝓝 t] Icc t₀ u := by
        rw [Filter.eventuallyEqSet_iff]
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with s hs
        exact ⟨fun h => ⟨le_of_lt (lt_trans ht₀T hs), h.2⟩,
          fun h => ⟨le_trans hat₀ (le_of_lt (lt_trans ht₀T hs)), h.2⟩⟩
      have hev : (cJ.lift x) =ᶠ[𝓝[Icc a u] t] (c₂.lift x) := by
        filter_upwards [mem_nhdsWithin_iff_eventually.mpr
          (by filter_upwards [isOpen_Ioi.mem_nhds ht₀t] with s hs _; exact hs)] with s hs
        exact heq₂ x s hs
      have hA : mfderivWithin 𝓘(ℝ, ℝ) I (cJ.lift x) (Icc a u) t =
          mfderivWithin 𝓘(ℝ, ℝ) I (c₂.lift x) (Icc a u) t :=
        hev.mfderivWithin_eq (heq₂ x t ht₀t)
      have hB : mfderivWithin 𝓘(ℝ, ℝ) I (c₂.lift x) (Icc t₀ u) t =
          mfderivWithin 𝓘(ℝ, ℝ) I (c₂.lift x) (Icc a u) t :=
        mfderivWithin_congr_set hset.symm
      have hvel : cJ.velocity (I := I) (Icc a u) x t = c₂.velocity (I := I) (Icc t₀ u) x t := by
        unfold CurveMap.velocity
        rw [hA, hB]
        rfl
      rw [hvel, h₂.equation x t ⟨le_of_lt ht₀t, ht.2⟩]
      exact (curvatureVector_congr (c := cJ) (d := c₂) (g := g) (t := t)
        (fun z => heq₂ z t ht₀t) x).symm

omit [CompleteSpace E] in
theorem tendsto_slice_of_terminalClosure {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {a T : ℝ} (haT : a < T) {g : ℝ → SmoothRiemannianMetric I M}
    {c closed : CurveMap M}
    (hsol : CurveMap.IsSolutionOn (I := I) closed g (Icc a T))
    (hagr : ∀ z t, t ∈ Ico a T → closed z t = c z t)
    (hc : c.SmoothOn (I := I) (Ico a T)) (hi : c.ImmersedOn (I := I) (Ico a T)) :
    letI := smoothImmersionTopology e
    Tendsto
      (fun t : {t : ℝ // t ∈ Ico a T} => SmoothImmersion.slice c hc hi t.1 t.2)
      (Filter.comap Subtype.val (𝓝[<] T))
      (𝓝 (SmoothImmersion.slice closed hsol.smooth hsol.immersed T ⟨haT.le, le_rfl⟩)) := by
  set cT : SmoothImmersion (I := I) (M := M) :=
    SmoothImmersion.slice closed hsol.smooth hsol.immersed T ⟨haT.le, le_rfl⟩ with hcT
  rw [TopologicalSpace.tendsto_nhds_generateFrom_iff]
  rintro V ⟨d₀, m, ε, hε, rfl⟩ hV
  have hcontT : ContinuousOn (fun x : ℝ => iteratedDeriv m
      (fun y : ℝ => e.map (cT.map (y : AddCircle (1 : ℝ)))) x) (Icc (0 : ℝ) 1) :=
    continuousOn_iteratedDeriv_embedding e cT m
  have hcont₀ : ContinuousOn (fun x : ℝ => iteratedDeriv m
      (fun y : ℝ => e.map (d₀.map (y : AddCircle (1 : ℝ)))) x) (Icc (0 : ℝ) 1) :=
    continuousOn_iteratedDeriv_embedding e d₀ m
  have hgap : ContinuousOn (fun x : ℝ => ε -
      ‖iteratedDeriv m (fun y : ℝ => e.map (cT.map (y : AddCircle (1 : ℝ)))) x -
        iteratedDeriv m (fun y : ℝ => e.map (d₀.map (y : AddCircle (1 : ℝ)))) x‖)
      (Icc (0 : ℝ) 1) :=
    continuousOn_const.sub (hcontT.sub hcont₀).norm
  obtain ⟨η, hηpos, hη⟩ := exists_pos_le_of_continuousOn_pos hgap
    (fun x hx => sub_pos.mpr (hV x hx))
  obtain ⟨δ, hδpos, hδb⟩ := exists_nhds_slice_jet_variation e haT hsol.smooth m
    ⟨haT.le, le_rfl⟩ (by linarith : (0 : ℝ) < η / 2)
  have hminpos : 0 < min δ (T - a) := lt_min hδpos (by linarith)
  have hmem : Ioo (T - min δ (T - a)) T ∈ 𝓝[<] T :=
    mem_nhdsWithin_iff_eventually.mpr (by
      filter_upwards [isOpen_Ioi.mem_nhds (by linarith [hminpos] : T - min δ (T - a) < T)]
        with t ht htlt
      exact ⟨ht, htlt⟩)
  refine Filter.mem_comap.mpr ⟨Ioo (T - min δ (T - a)) T, hmem, ?_⟩
  rintro ⟨t, ht⟩ htI
  intro x hx
  simp only [SmoothImmersion.slice]
  have hdist : |t - T| < δ := by
    rw [abs_of_neg (by linarith [htI.2] : t - T < 0)]
    have : t > T - min δ (T - a) := htI.1
    linarith [min_le_left δ (T - a)]
  have hjet : (fun y : ℝ => e.map (c (y : AddCircle (1 : ℝ)) t)) =
      (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) t)) :=
    funext (fun y => congrArg e.map ((hagr (y : AddCircle (1 : ℝ)) t ht).symm))
  rw [hjet]
  have hcomp_t : iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) t)) x =
      (iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (closed.lift q.1 q.2))
        (univ ×ˢ Icc a T) (x, t)) (fun _ : Fin m => (1, 0)) := by
    simpa only [CurveMap.lift] using
      slice_jet_eq_jet_component e haT hsol.smooth m ⟨ht.1, le_of_lt ht.2⟩
  have hcomp_T : iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) T)) x =
      (iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (closed.lift q.1 q.2))
        (univ ×ˢ Icc a T) (x, T)) (fun _ : Fin m => (1, 0)) := by
    simpa only [CurveMap.lift] using
      slice_jet_eq_jet_component e haT hsol.smooth m ⟨haT.le, le_rfl⟩
  have h1 : ‖iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) t)) x -
      iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) T)) x‖ < η / 2 :=
    (by
      rw [hcomp_t, hcomp_T]
      exact
        hδb t ⟨ht.1, le_of_lt ht.2⟩ hdist x hx)
  have h2 : ‖iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) T)) x -
      iteratedDeriv m (fun y : ℝ => e.map (d₀.map (y : AddCircle (1 : ℝ)))) x‖ ≤ ε - η :=
    (by
      have h := hη x hx
      simp only [hcT, SmoothImmersion.slice] at h
      linarith)
  have htri : ‖iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) t)) x -
        iteratedDeriv m (fun y : ℝ => e.map (d₀.map (y : AddCircle (1 : ℝ)))) x‖ ≤
      ‖iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) t)) x -
        iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) T)) x‖ +
      ‖iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) T)) x -
        iteratedDeriv m (fun y : ℝ => e.map (d₀.map (y : AddCircle (1 : ℝ)))) x‖ := by
    simpa only [dist_eq_norm] using dist_triangle
      (iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) t)) x)
      (iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) T)) x)
      (iteratedDeriv m (fun y : ℝ => e.map (d₀.map (y : AddCircle (1 : ℝ)))) x)
  linarith

end CurveMap

variable [SigmaCompactSpace M] [t2M : T2Space M] [compactM : CompactSpace M] [nonemptyM : Nonempty M]
  [hBoundary : I.Boundaryless]
include t2M compactM nonemptyM hBoundary
variable {D : RealTimeInterval} {a b : ℝ}

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] t2M compactM nonemptyM
  hBoundary [SigmaCompactSpace M] in
theorem smoothCylinderTopology_continuousAt_congr {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] {J : Set ℝ} {f g : P → CurveMap M} {p : P}
    (h : ∀ p z t, t ∈ J → f p z t = g p z t)
    (hf : @ContinuousAt P (CurveMap M) inferInstance (smoothCylinderTopology e J) f p) :
    @ContinuousAt P (CurveMap M) inferInstance (smoothCylinderTopology e J) g p := by
  simp only [ContinuousAt, TopologicalSpace.tendsto_nhds_generateFrom_iff] at hf ⊢
  rintro s ⟨c₀, m, ε, hε, rfl⟩ hgs
  have hiff : ∀ d d' : CurveMap M, (∀ z t, t ∈ J → d z t = d' z t) →
      ((∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
          ‖iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (d.lift r.1 r.2)) (univ ×ˢ J) q -
           iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (c₀.lift r.1 r.2))
            (univ ×ˢ J) q‖ ≤ ρ) ↔
       (∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
          ‖iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (d'.lift r.1 r.2)) (univ ×ˢ J) q -
           iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (c₀.lift r.1 r.2))
            (univ ×ˢ J) q‖ ≤ ρ)) := by
    intro d d' hdd
    have hkey : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
        iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (d.lift r.1 r.2)) (univ ×ˢ J) q =
        iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (d'.lift r.1 r.2)) (univ ×ˢ J) q :=
      fun q hq => smoothCylinderJets_eq_of_eqOn e hdd m q ⟨mem_univ _, hq.2⟩
    constructor <;> rintro ⟨ρ, hρ, hb⟩ <;> refine ⟨ρ, hρ, fun q hq => ?_⟩
    · rw [← hkey q hq]; exact hb q hq
    · rw [hkey q hq]; exact hb q hq
  have hfp : f p ∈ {d : CurveMap M | ∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (d.lift r.1 r.2)) (univ ×ˢ J) q -
       iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (c₀.lift r.1 r.2))
        (univ ×ˢ J) q‖ ≤ ρ} :=
    (hiff (g p) (f p) (fun z t ht => (h p z t ht).symm)).mp hgs
  have hpre : g ⁻¹' {d : CurveMap M | ∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (d.lift r.1 r.2)) (univ ×ˢ J) q -
       iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (c₀.lift r.1 r.2))
        (univ ×ˢ J) q‖ ≤ ρ} =
    f ⁻¹' {d : CurveMap M | ∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (d.lift r.1 r.2)) (univ ×ˢ J) q -
       iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (c₀.lift r.1 r.2))
        (univ ×ˢ J) q‖ ≤ ρ} := by
    ext q
    exact hiff (g q) (f q) (fun z t ht => (h q z t ht).symm)
  rw [hpre]
  exact hf _ ⟨c₀, m, ε, hε, rfl⟩ hfp


def curveShorteningLocalWindow (B : SmoothMetricWindow (I := I) (M := M) D a b) : Prop :=
  ∀ (t₀ : {t : ℝ // t ∈ Ico a b}) (c₀ : SmoothImmersion (I := I) (M := M))
    (N : ℕ) (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
    letI : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
    ∃ τ > 0, ∃ U : Set ({t : ℝ // t ∈ Ico a b} × SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ (t₀, c₀) ∈ U ∧
      ∃ solutions : U → CurveMap M,
        (@Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a b)) solutions) ∧
        ∀ p : U, (p.1.1 : ℝ) + τ ≤ b ∧
          CurveMap.IsSolutionOn (I := I) (solutions p) B.family.metric
            (Icc (p.1.1 : ℝ) ((p.1.1 : ℝ) + τ)) ∧
          ∀ z, solutions p z (p.1.1 : ℝ) = p.1.2.map z


omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem exists_extension_of_localWindow
    (B : SmoothMetricWindow (I := I) (M := M) D a b) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {T : ℝ} (haT : a < T) (hTb : T < b) {c : CurveMap M}
    (hc : CurveMap.IsSolutionOn (I := I) c B.family.metric (Ico a T))
    (hclose : ∃ closed : CurveMap M,
      CurveMap.IsSolutionOn (I := I) closed B.family.metric (Icc a T) ∧
      ∀ z t, t ∈ Ico a T → closed z t = c z t)
    (hwin : curveShorteningLocalWindow (I := I) (M := M) B)
    (huniq : curveShorteningLocalUniqueness (I := I) (M := M) B) :
    ∃ τ > 0, T + τ ≤ b ∧ ∃ extended : CurveMap M,
      CurveMap.IsSolutionOn (I := I) extended B.family.metric (Icc a (T + τ)) ∧
      ∀ z t, t ∈ Ico a T → extended z t = c z t :=
  letI instImm : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  by
  classical
  obtain ⟨closed, hsol, hagr⟩ := hclose
  let cT : SmoothImmersion (I := I) (M := M) :=
    SmoothImmersion.slice closed hsol.smooth hsol.immersed T ⟨haT.le, le_rfl⟩
  let t₀ : {t : ℝ // t ∈ Ico a b} := ⟨T, haT.le, hTb⟩
  obtain ⟨τ, hτpos, U, hUopen, hmemU, sols, hcont, hprop⟩ := hwin t₀ cT N e
  have htend : Tendsto (fun t : {t : ℝ // t ∈ Ico a T} =>
      SmoothImmersion.slice c hc.smooth hc.immersed t.1 t.2)
      (Filter.comap Subtype.val (𝓝[<] T)) (𝓝 cT) :=
    CurveMap.tendsto_slice_of_terminalClosure e haT hsol hagr hc.smooth hc.immersed
  have hfirst : Tendsto (fun t : {t : ℝ // t ∈ Ico a T} =>
      (⟨t.1, ⟨t.2.1, lt_trans t.2.2 hTb⟩⟩ : {t : ℝ // t ∈ Ico a b}))
      (Filter.comap Subtype.val (𝓝[<] T)) (𝓝 t₀) := by
    rw [nhds_subtype]
    rw [tendsto_comap_iff]
    exact Filter.tendsto_comap.mono_right nhdsWithin_le_nhds
  have hprod : Tendsto (fun t : {t : ℝ // t ∈ Ico a T} =>
      ((⟨t.1, ⟨t.2.1, lt_trans t.2.2 hTb⟩⟩ : {t : ℝ // t ∈ Ico a b}),
        SmoothImmersion.slice c hc.smooth hc.immersed t.1 t.2))
      (Filter.comap Subtype.val (𝓝[<] T)) (𝓝 (t₀, cT)) := by
    rw [nhds_prod_eq]
    exact hfirst.prodMk htend
  have hevent : ∀ᶠ t in Filter.comap Subtype.val (𝓝[<] T),
      ((⟨t.1, ⟨t.2.1, lt_trans t.2.2 hTb⟩⟩ : {t : ℝ // t ∈ Ico a b}),
        SmoothImmersion.slice c hc.smooth hc.immersed t.1 t.2) ∈ U :=
    hprod.eventually (hUopen.mem_nhds hmemU)
  obtain ⟨A, hA, hAsub⟩ := Filter.mem_comap.mp hevent
  obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hA
  obtain ⟨ε, hεpos, hεball⟩ := Metric.mem_nhds_iff.mp hV
  set ρ : ℝ := min (min ε τ) (T - a) with hρ
  have hρpos : 0 < ρ := by
    rw [hρ]
    exact lt_min (lt_min hεpos hτpos) (by linarith)
  have hρε : ρ / 3 < ε := by
    have h1 : ρ ≤ ε := by
      rw [hρ]
      exact (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hρτ : ρ / 3 < τ := by
    have h1 : ρ ≤ τ := by
      rw [hρ]
      exact (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hρa : ρ / 3 < T - a := by
    have h1 : ρ ≤ T - a := by rw [hρ]; exact min_le_right _ _
    linarith
  have ht'mem : T - ρ / 3 ∈ Ico a T := ⟨by linarith, by linarith⟩
  set t' : {t : ℝ // t ∈ Ico a T} := ⟨T - ρ / 3, ht'mem⟩ with ht'def
  have ht'val : (t' : ℝ) = T - ρ / 3 := rfl
  have ht'ltT : (t' : ℝ) < T := by
    rw [ht'val]
    linarith [hρpos]
  have ht'ball : |(t' : ℝ) - T| < ε := by
    have hsubρ : T - ρ / 3 - T = -(ρ / 3) := by ring
    rw [ht'val, hsubρ, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < ρ / 3)]
    exact hρε
  have ht'A : (t' : ℝ) ∈ A := hVsub ⟨hεball ht'ball, ht'ltT⟩
  have hmemUt' : ((⟨(t' : ℝ), ⟨t'.2.1, lt_trans t'.2.2 hTb⟩⟩ : {t : ℝ // t ∈ Ico a b}),
      SmoothImmersion.slice c hc.smooth hc.immersed (t' : ℝ) t'.2) ∈ U :=
    hAsub ht'A
  obtain ⟨hτb, hsolU, hinitU⟩ := hprop ⟨_, hmemUt'⟩
  have hmin : min T ((t' : ℝ) + τ) = T := by
    rw [min_eq_left_iff, ht'val]
    linarith
  have hagree : ∀ z t, t ∈ Icc (t' : ℝ) T →
      closed z t = sols ⟨_, hmemUt'⟩ z t := by
    intro z t ht
    refine huniq (t' : ℝ) T ((t' : ℝ) + τ) t'.2.1 ht'ltT (by linarith)
      hTb.le hτb closed
      (sols ⟨_, hmemUt'⟩)
      (hsol.mono_Icc t'.2.1 le_rfl ht'ltT) hsolU ?_ z t ?_
    · intro z'
      have h1 : closed z' (t' : ℝ) = c z' (t' : ℝ) := hagr z' (t' : ℝ) t'.2
      have h2 : sols ⟨_, hmemUt'⟩ z' (t' : ℝ) =
          (SmoothImmersion.slice c hc.smooth hc.immersed (t' : ℝ) t'.2).map z' := hinitU z'
      rw [h1, h2]
      rfl
    · rw [hmin]
      exact ht
  have hglue : CurveMap.IsSolutionOn (I := I)
      (fun z t => if t ≤ T then closed z t else sols ⟨_, hmemUt'⟩ z t)
      B.family.metric (Icc a ((t' : ℝ) + τ)) :=
    CurveMap.IsSolutionOn.glue (g := B.family.metric) t'.2.1 ht'ltT
      (by linarith) hsol hsolU hagree
  have hhorizon : T + (τ - ρ / 3) = (t' : ℝ) + τ := by
    rw [ht'val]
    ring
  refine ⟨τ - ρ / 3, by linarith, ?_, ?_⟩
  · rw [ht'val] at hτb
    linarith
  · refine ⟨fun z t => if t ≤ T then closed z t else sols ⟨_, hmemUt'⟩ z t, ?_, ?_⟩
    · rw [hhorizon]
      exact hglue
    · intro z t ht
      simp only [ite_eq_left (le_of_lt ht.2)]
      exact hagr z t ht

def curveShorteningTerminalClosure (B : RicciBackground (I := I) (M := M) D a b) : Prop :=
  ∀ (T : ℝ), a < T → T ≤ b → ∀ (c : CurveMap M) (K : ℝ), 0 ≤ K →
    CurveMap.IsSolutionOn (I := I) c B.family.metric (Ico a T) →
    (∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K) →
    ∃ closed : CurveMap M,
      CurveMap.IsSolutionOn (I := I) closed B.family.metric (Icc a T) ∧
      ∀ z t, t ∈ Ico a T → closed z t = c z t


omit compactM nonemptyM hBoundary in
def curveShorteningContinuation (B : RicciBackground (I := I) (M := M) D a b) : Prop :=
  ∀ (T : ℝ), a < T → T ≤ b → ∀ (c : CurveMap M)
    (hc : CurveMap.IsSolutionOn (I := I) c B.family.metric (Ico a T)) (K : ℝ), 0 ≤ K →
    (∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K) →
    ∃ cT : SmoothImmersion (I := I) (M := M),
      (∀ (N : ℕ) (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
        letI := smoothImmersionTopology e
        Tendsto
          (fun t : {t : ℝ // t ∈ Ico a T} =>
            SmoothImmersion.slice c hc.smooth hc.immersed t.1 t.2)
          (Filter.comap Subtype.val (𝓝[<] T)) (𝓝 cT)) ∧
      (∃ closed : CurveMap M, closed.IsSolutionOn B.family.metric (Icc a T) ∧
        (∀ z t, t ∈ Ico a T → closed z t = c z t) ∧ (∀ z, closed z T = cT.map z)) ∧
      (T < b → ∃ τ > 0, T + τ ≤ b ∧ ∃ extended : CurveMap M,
        extended.IsSolutionOn B.family.metric (Icc a (T + τ)) ∧
        (∀ z t, t ∈ Ico a T → extended z t = c z t))

omit compactM nonemptyM hBoundary in
def curveShorteningExtension (B : RicciBackground (I := I) (M := M) D a b) : Prop :=
  ∀ (T : ℝ), a < T → T < b → ∀ (c : CurveMap M) (K : ℝ), 0 ≤ K →
    CurveMap.IsSolutionOn (I := I) c B.family.metric (Ico a T) →
    (∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K) →
    ∃ τ > 0, T + τ ≤ b ∧ ∃ extended : CurveMap M,
      CurveMap.IsSolutionOn (I := I) extended B.family.metric (Icc a (T + τ)) ∧
      ∀ z t, t ∈ Ico a T → extended z t = c z t

omit [SigmaCompactSpace M] compactM nonemptyM hBoundary in
def curveShorteningUniformLocalWindow
    (B : SmoothMetricWindow (I := I) (M := M) D a b) : Prop :=
  ∃ τ > 0, ∀ (t₀ : {t : ℝ // t ∈ Ico a b})
    (c₀ : SmoothImmersion (I := I) (M := M)) (N : ℕ)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
    letI : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
    ∃ U : Set ({t : ℝ // t ∈ Ico a b} × SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ (t₀, c₀) ∈ U ∧
      ∃ solutions : U → CurveMap M,
        (@Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a b)) solutions) ∧
        ∀ p : U, CurveMap.IsSolutionOn (I := I) (solutions p) B.family.metric
            (Icc (p.1.1 : ℝ) (min b ((p.1.1 : ℝ) + τ))) ∧
          ∀ z, solutions p z (p.1.1 : ℝ) = p.1.2.map z

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}

private theorem eventually_cylinder_jets_close
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] {J : Set ℝ} {f : P → CurveMap M} {p : P}
    (hf : @ContinuousAt P (CurveMap M) inferInstance (smoothCylinderTopology e J) f p)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in 𝓝 p, ∃ ρ : ℝ, ρ < ε ∧ ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map ((f q).lift r.1 r.2))
        (univ ×ˢ J) z -
        iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map ((f p).lift r.1 r.2))
          (univ ×ˢ J) z‖ ≤ ρ := by
  simp only [ContinuousAt, TopologicalSpace.tendsto_nhds_generateFrom_iff] at hf
  exact hf _ ⟨f p, m, ε, hε, rfl⟩ ⟨0, hε, fun z _ => by simp⟩

private theorem continuousAt_cylinder_of_eventually_jets_close
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] {J : Set ℝ} {f : P → CurveMap M} {p : P}
    (hf : ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∀ᶠ q in 𝓝 p, ∃ ρ : ℝ, ρ < ε ∧ ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ J,
        ‖iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map ((f q).lift r.1 r.2))
          (univ ×ˢ J) z -
          iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map ((f p).lift r.1 r.2))
            (univ ×ˢ J) z‖ ≤ ρ) :
    @ContinuousAt P (CurveMap M) inferInstance (smoothCylinderTopology e J) f p := by
  simp only [ContinuousAt, TopologicalSpace.tendsto_nhds_generateFrom_iff]
  rintro V ⟨c, m, ε, _, rfl⟩ ⟨ρ, hρε, hρ⟩
  filter_upwards [hf m (ε - ρ) (sub_pos.mpr hρε)] with q hq
  obtain ⟨δ, hδ, hδbound⟩ := hq
  refine ⟨δ + ρ, by linarith, ?_⟩
  intro z hz
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add (hδbound z hz) (hρ z hz))

private theorem cylinder_jets_eq_of_restriction
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {J K : Set ℝ} (hJK : J ⊆ K) (hJ : UniqueDiffOn ℝ J) (hK : UniqueDiffOn ℝ K)
    {f g : CurveMap M} (hf : f.SmoothOn (I := I) K)
    (heq : ∀ z t, t ∈ J → f z t = g z t)
    (m : ℕ) (z : ℝ × ℝ) (hz : z ∈ univ ×ˢ J) :
    iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (f.lift r.1 r.2)) (univ ×ˢ K) z =
      iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (g.lift r.1 r.2)) (univ ×ˢ J) z := by
  rw [← iteratedFDerivWithin_subset (prod_mono Subset.rfl hJK)
    (uniqueDiffOn_univ.prod hJ) (uniqueDiffOn_univ.prod hK)
    ((contDiffOn_liftMap e hf).of_le (by exact_mod_cast le_top)) hz]
  exact smoothCylinderJets_eq_of_eqOn e heq m z hz

theorem smoothCylinderTopology_continuous_mono
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] {J K : Set ℝ} {f : P → CurveMap M}
    (hJK : J ⊆ K) (hJ : UniqueDiffOn ℝ J) (hK : UniqueDiffOn ℝ K)
    (hf : @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e K) f)
    (hs : ∀ p, (f p).SmoothOn (I := I) K) :
    @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e J) f := by
  let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e J
  apply continuous_iff_continuousAt.mpr
  intro p
  have hfp : @ContinuousAt P (CurveMap M) inferInstance (smoothCylinderTopology e K) f p := by
    let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e K
    exact hf.continuousAt
  apply continuousAt_cylinder_of_eventually_jets_close e
  intro m ε hε
  filter_upwards [eventually_cylinder_jets_close e hfp m hε] with q hq
  obtain ⟨ρ, hρ, hρbound⟩ := hq
  refine ⟨ρ, hρ, ?_⟩
  intro z hz
  have heq (p : P) := cylinder_jets_eq_of_restriction e hJK hJ hK (hs p)
    (fun _ _ _ => rfl) m z ⟨mem_univ _, hz.2⟩
  rw [← heq q, ← heq p]
  exact hρbound z ⟨hz.1, hJK hz.2⟩

theorem smoothCylinderTopology_continuous_of_union
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] {J K : Set ℝ} {f g h : P → CurveMap M}
    (hJ : UniqueDiffOn ℝ J) (hK : UniqueDiffOn ℝ K)
    (hf : @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e J) f)
    (hg : @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e K) g)
    (hh : ∀ p, (h p).SmoothOn (I := I) (J ∪ K))
    (hhf : ∀ p z v, v ∈ J → h p z v = f p z v)
    (hhg : ∀ p z v, v ∈ K → h p z v = g p z v) :
    @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (J ∪ K)) h := by
  have hJK : UniqueDiffOn ℝ (J ∪ K) := by
    intro x hx
    rcases hx with hx | hx
    · exact (hJ x hx).mono subset_union_left
    · exact (hK x hx).mono subset_union_right
  have hleft (p : P) (m : ℕ) (z : ℝ × ℝ) (hz : z ∈ univ ×ˢ J) :=
    cylinder_jets_eq_of_restriction e subset_union_left hJ hJK (hh p) (hhf p) m z hz
  have hright (p : P) (m : ℕ) (z : ℝ × ℝ) (hz : z ∈ univ ×ˢ K) :=
    cylinder_jets_eq_of_restriction e subset_union_right hK hJK (hh p) (hhg p) m z hz
  let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (J ∪ K)
  apply continuous_iff_continuousAt.mpr
  intro p
  apply continuousAt_cylinder_of_eventually_jets_close e
  intro m ε hε
  have hfp : @ContinuousAt P (CurveMap M) inferInstance (smoothCylinderTopology e J) f p := by
    let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e J
    exact hf.continuousAt
  have hgp : @ContinuousAt P (CurveMap M) inferInstance (smoothCylinderTopology e K) g p := by
    let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e K
    exact hg.continuousAt
  filter_upwards [eventually_cylinder_jets_close e hfp m hε,
    eventually_cylinder_jets_close e hgp m hε] with q hqf hqg
  obtain ⟨ρ, hρ, hρbound⟩ := hqf
  obtain ⟨δ, hδ, hδbound⟩ := hqg
  refine ⟨max ρ δ, max_lt hρ hδ, ?_⟩
  intro z hz
  rcases hz.2 with hzl | hzr
  · rw [hleft q m z ⟨mem_univ _, hzl⟩, hleft p m z ⟨mem_univ _, hzl⟩]
    exact (hρbound z ⟨hz.1, hzl⟩).trans (le_max_left _ _)
  · rw [hright q m z ⟨mem_univ _, hzr⟩, hright p m z ⟨mem_univ _, hzr⟩]
    exact (hδbound z ⟨hz.1, hzr⟩).trans (le_max_right _ _)

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

theorem continuous_solution_family_glue
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] {a s t b : ℝ}
    (has : a ≤ s) (hst : s < t) (htb : t < b)
    {g : ℝ → SmoothRiemannianMetric I M} {f h : P → CurveMap M}
    (hf : @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a t)) f)
    (hh : @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc s b)) h)
    (hfsol : ∀ p, (f p).IsSolutionOn (I := I) g (Icc a t))
    (hhsol : ∀ p, (h p).IsSolutionOn (I := I) g (Icc s b))
    (heq : ∀ p z v, v ∈ Icc s t → f p z v = h p z v) :
    let solutions : P → CurveMap M := fun p z v => if v ≤ t then f p z v else h p z v
    @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a b)) solutions ∧
      (∀ p, (solutions p).IsSolutionOn (I := I) g (Icc a b)) ∧
      (∀ p z v, v ∈ Icc a t → solutions p z v = f p z v) ∧
      ∀ p z, solutions p z a = f p z a := by
  intro solutions
  have hsol (p : P) : (solutions p).IsSolutionOn (I := I) g (Icc a b) :=
    CurveMap.IsSolutionOn.glue has hst htb (hfsol p) (hhsol p) (heq p)
  have hleft (p : P) (z : AddCircle (1 : ℝ)) (v : ℝ) (hv : v ∈ Icc a t) :
      solutions p z v = f p z v := by
    exact ite_eq_left hv.2
  have hright (p : P) (z : AddCircle (1 : ℝ)) (v : ℝ) (hv : v ∈ Icc s b) :
      solutions p z v = h p z v := by
    by_cases hvt : v ≤ t
    · exact (ite_eq_left hvt).trans (heq p z v ⟨hv.1, hvt⟩)
    · exact ite_eq_right hvt
  have hcover : Icc a t ∪ Icc s b = Icc a b := by
    ext v
    constructor
    · rintro (hv | hv)
      · exact ⟨hv.1, hv.2.trans htb.le⟩
      · exact ⟨has.trans hv.1, hv.2⟩
    · intro hv
      by_cases hvt : v ≤ t
      · exact Or.inl ⟨hv.1, hvt⟩
      · exact Or.inr ⟨hst.le.trans (le_of_not_ge hvt), hv.2⟩
  have hcont := smoothCylinderTopology_continuous_of_union e
    (uniqueDiffOn_Icc (has.trans_lt hst)) (uniqueDiffOn_Icc (hst.trans htb))
    hf hh (fun p => by rw [hcover]; exact (hsol p).smooth) hleft hright
  rw [hcover] at hcont
  exact ⟨hcont, hsol, hleft, fun p z => hleft p z a ⟨le_rfl, has.trans hst.le⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
open Set
open scoped Pointwise

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private theorem smoothCylinderJets_time_translate {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (c : CurveMap M) (a b s : ℝ) (m : ℕ) (q : ℝ × ℝ) :
    iteratedFDerivWithin ℝ m
        (fun r : ℝ × ℝ => e.map (c.lift r.1 (r.2 + s))) (univ ×ˢ Icc a b) q =
      iteratedFDerivWithin ℝ m
        (fun r : ℝ × ℝ => e.map (c.lift r.1 r.2))
        (univ ×ˢ Icc (a + s) (b + s)) (q.1, q.2 + s) := by
  have hset : ((0, s) : ℝ × ℝ) +ᵥ ((univ : Set ℝ) ×ˢ Icc a b) =
      univ ×ˢ Icc (a + s) (b + s) := by
    ext r
    simp only [Set.mem_vadd_set, vadd_eq_add, Set.mem_prod, Set.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩
      change a + s ≤ s + v.2 ∧ s + v.2 ≤ b + s
      exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
    · intro hr
      refine ⟨(r.1, r.2 - s), ⟨?_, ?_⟩, ?_⟩
      · linarith [hr.1]
      · linarith [hr.2]
      · ext <;> simp
  have hq : q + (0, s) = (q.1, q.2 + s) := by ext <;> simp
  simpa only [hset, hq, Prod.fst_add, Prod.snd_add, add_zero] using
    (iteratedFDerivWithin_comp_add_right (𝕜 := ℝ)
      (f := fun r : ℝ × ℝ => e.map (c.lift r.1 r.2))
      (s := univ ×ˢ Icc a b) m ((0, s) : ℝ × ℝ) q)

theorem smoothCylinderTopology_continuous_time_translate {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] {f : P → CurveMap M} (a b s : ℝ)
    (hf : @Continuous P (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc (a + s) (b + s))) f) :
    @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a b))
      (fun p z t => f p z (t + s)) := by
  simp only [continuous_generateFrom_iff] at hf ⊢
  rintro V ⟨c₀, m, ε, hε, rfl⟩
  let c₁ : CurveMap M := fun z t => c₀ z (t - s)
  have hcenter (q : ℝ × ℝ) :
      iteratedFDerivWithin ℝ m
          (fun r : ℝ × ℝ => e.map (c₀.lift r.1 r.2)) (univ ×ˢ Icc a b) q =
        iteratedFDerivWithin ℝ m
          (fun r : ℝ × ℝ => e.map (c₁.lift r.1 r.2))
          (univ ×ˢ Icc (a + s) (b + s)) (q.1, q.2 + s) := by
    simpa only [c₁, CurveMap.lift, add_sub_cancel_right] using
      smoothCylinderJets_time_translate e c₁ a b s m q
  have hopen := hf _ ⟨c₁, m, ε, hε, rfl⟩
  convert hopen using 1
  ext p
  change (∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc a b,
    ‖iteratedFDerivWithin ℝ m
        (fun r : ℝ × ℝ => e.map ((f p).lift r.1 (r.2 + s))) (univ ×ˢ Icc a b) q -
      iteratedFDerivWithin ℝ m
        (fun r : ℝ × ℝ => e.map (c₀.lift r.1 r.2)) (univ ×ˢ Icc a b) q‖ ≤ ρ) ↔
    (∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (a + s) (b + s),
      ‖iteratedFDerivWithin ℝ m
          (fun r : ℝ × ℝ => e.map ((f p).lift r.1 r.2))
          (univ ×ˢ Icc (a + s) (b + s)) q -
        iteratedFDerivWithin ℝ m
          (fun r : ℝ × ℝ => e.map (c₁.lift r.1 r.2))
          (univ ×ˢ Icc (a + s) (b + s)) q‖ ≤ ρ)
  constructor
  · rintro ⟨ρ, hρ, hbound⟩
    refine ⟨ρ, hρ, ?_⟩
    intro q hq
    have hqt : (q.1, q.2 - s) ∈ Icc (0 : ℝ) 1 ×ˢ Icc a b :=
      ⟨hq.1, by constructor <;> linarith [hq.2.1, hq.2.2]⟩
    have h := hbound (q.1, q.2 - s) hqt
    rw [smoothCylinderJets_time_translate, hcenter] at h
    simpa only [sub_add_cancel, Prod.eta] using h
  · rintro ⟨ρ, hρ, hbound⟩
    refine ⟨ρ, hρ, ?_⟩
    intro q hq
    rw [smoothCylinderJets_time_translate, hcenter]
    exact hbound (q.1, q.2 + s)
      ⟨hq.1, by constructor <;> linarith [hq.2.1, hq.2.2]⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

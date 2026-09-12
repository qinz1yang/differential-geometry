import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem continuousAt_of_eq_subtype_val {X α : Type*} [TopologicalSpace X]
    [TopologicalSpace α] {s : Set α} (hs : IsOpen s) (sol : s → X) (hcont : Continuous sol)
    {y : α} (hy : y ∈ s) {F : α → X} (hFy : F y = sol ⟨y, hy⟩)
    (hFs : ∀ (x : α) (hx : x ∈ s), F x = sol ⟨x, hx⟩) : ContinuousAt F y := by
  rw [ContinuousAt, Filter.tendsto_def]
  intro W hW
  rw [hFy] at hW
  have h1 : sol ⁻¹' W ∈ 𝓝 (⟨y, hy⟩ : s) := hcont.continuousAt.preimage_mem_nhds hW
  rw [nhds_subtype] at h1
  obtain ⟨Z, hZ, hZsub⟩ := Filter.mem_comap.mp h1
  refine Filter.mem_of_superset (Filter.inter_mem hZ (hs.mem_nhds hy)) ?_
  intro z hz
  simp only [Set.mem_preimage] at hz ⊢
  rw [hFs z hz.2]
  exact hZsub (a := ⟨z, hz.2⟩) hz.1

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
          Finset.prod_le_prod (fun i _ => norm_nonneg _)
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

omit [FiniteDimensional ℝ E] [CompleteSpace E] t2M compactM nonemptyM hBoundary
  [SigmaCompactSpace M] in
theorem compact_family_regular_homotopy_at_start
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P]
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hinit : @Continuous P _ inferInstance (smoothImmersionTopology e) initial)
    (h : immersionContinuityIntoRegularLoops (I := I) (M := M)) :
    ∃ homotopy : C(P × Icc a a, Width.RegularLoop I M),
      ∀ (p : P) (t : Icc a a) z, homotopy (p, t) z = (initial p).map z := by
  obtain ⟨loops, hloops⟩ := smooth_immersion_regular_family e initial hinit h
  exact ⟨loops.comp ⟨Prod.fst, continuous_fst⟩, fun p _ z => hloops p z⟩

theorem rfs_csf_continuation (B : RicciBackground (I := I) (M := M) D a b)
    {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Ico a T))
    (K : ℝ) (hK : 0 ≤ K)
    (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K) :
    ∃ cT : SmoothImmersion (I := I) (M := M),
      (∀ (N : ℕ) (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
        letI := smoothImmersionTopology e
        Tendsto
          (fun t : {t : ℝ // t ∈ Ico a T} => SmoothImmersion.slice c hc.smooth hc.immersed t.1 t.2)
          (Filter.comap Subtype.val (𝓝[<] T)) (𝓝 cT)) ∧
      (∃ closed : CurveMap M, closed.IsSolutionOn B.family.metric (Icc a T) ∧
        (∀ z t, t ∈ Ico a T → closed z t = c z t) ∧ (∀ z, closed z T = cT.map z)) ∧
      (T < b → ∃ τ > 0, T + τ ≤ b ∧ ∃ extended : CurveMap M,
        extended.IsSolutionOn B.family.metric (Icc a (T + τ)) ∧
        (∀ z t, t ∈ Ico a T → extended z t = c z t)) := by
  sorry

theorem maximal_curvature_unbounded (B : RicciBackground (I := I) (M := M) D a b)
    {T : ℝ} (haT : a < T) (hTb : T < b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Ico a T))
    (hmax : ∀ u : ℝ, T < u → u ≤ b →
      ¬∃ extended : CurveMap M, extended.IsSolutionOn B.family.metric (Icc a u) ∧
        ∀ z t, t ∈ Ico a T → extended z t = c z t) :
    ∀ K : ℝ, ∃ x t, t ∈ Ico a T ∧ K < c.curvature B.family.metric x t := by
  intro K
  by_contra! hbound
  have hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ max K 0 := by
    intro x t ht
    exact (hbound x t ht).trans (le_max_left K 0)
  obtain ⟨cT, hlimit, hclosed, hextend⟩ :=
    rfs_csf_continuation B haT hTb.le c hc (max K 0) (le_max_right K 0) hcurv
  obtain ⟨τ, hτ, hτb, extended, hsol, heq⟩ := hextend hTb
  exact hmax (T + τ) (lt_add_of_pos_right T hτ) hτb ⟨extended, hsol, heq⟩

theorem rfs_csf_family_dependence (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (had : a < d) (hdb : d ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc a d))
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    letI := smoothImmersionTopology e
    ∃ U : Set (SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩ ∈ U ∧
      ∃ solutions : U → CurveMap M,
        (@Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions) ∧
        ∀ p : U, (solutions p).IsSolutionOn B.family.metric (Icc a d) ∧
          ∀ z, solutions p z a = p.1.map z := by
  sorry

theorem compact_family_solution_continuous
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (had : a < d) (hdb : d ≤ b)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hinit : @Continuous P _ inferInstance (smoothImmersionTopology e) initial)
    (solutions : P → CurveMap M)
    (hsol : ∀ p, (solutions p).IsSolutionOn B.family.metric (Icc a d))
    (htrace : ∀ p z, solutions p z a = (initial p).map z)
    (huniq : curveShorteningLocalUniqueness (I := I) (M := M) B) :
    @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions :=
  letI instImm : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  letI instCyl : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc a d)
  by
    classical
    let φ : P → SmoothImmersion (I := I) (M := M) := fun p =>
      SmoothImmersion.slice (solutions p) (hsol p).smooth (hsol p).immersed a ⟨le_rfl, had.le⟩
    have hφinit : φ = initial := by
      funext p
      exact (SmoothImmersion.mk.injEq _ _ _ _ _ _).mpr (funext fun z => htrace p z)
    have hφcont : Continuous φ := hφinit ▸ hinit
    rw [continuous_iff_continuousAt]
    intro p₀
    obtain ⟨U, hUopen, hmem, sols, hcont, hprop⟩ :=
      rfs_csf_family_dependence B had hdb (solutions p₀) (hsol p₀) e
    have hmem0 : φ p₀ ∈ U := hmem
    let T : SmoothImmersion (I := I) (M := M) → CurveMap M := fun x =>
      if h : x ∈ U then sols ⟨x, h⟩ else sols ⟨φ p₀, hmem0⟩
    let T' : P → CurveMap M := fun p => if h : φ p ∈ U then T (φ p) else solutions p
    have hTat : ContinuousAt T (φ p₀) :=
      continuousAt_of_eq_subtype_val hUopen sols hcont hmem0 (F := T)
        (by simp only [T, dif_pos hmem0]) (fun x hx => by simp only [T, dif_pos hx])
    have hT'at : ContinuousAt T' p₀ := by
      have hbase : ContinuousAt (fun p : P => T (φ p)) p₀ := hTat.comp hφcont.continuousAt
      have hev : ∀ᶠ p in 𝓝 p₀, T (φ p) = T' p := by
        filter_upwards [hφcont.continuousAt.preimage_mem_nhds (hUopen.mem_nhds hmem0)]
          with p hp
        have hp' : φ p ∈ U := hp
        simp only [T', dif_pos hp']
      exact hbase.congr hev
    have hagree : ∀ p z t, t ∈ Icc a d → T' p z t = solutions p z t := by
      intro p z t ht
      by_cases h : φ p ∈ U
      · have hTp : T' p = sols ⟨φ p, h⟩ := by
          simp only [T', T, dif_pos h]
        rw [hTp]
        refine local_solution_unique B (le_refl a) had had hdb hdb (sols ⟨φ p, h⟩) (solutions p)
          (hprop ⟨φ p, h⟩).1 (hsol p) (fun z => (hprop ⟨φ p, h⟩).2 z) huniq z t ?_
        simpa only [min_self] using ht
      · simp only [T', dif_neg h]
    exact smoothCylinderTopology_continuousAt_congr e hagree hT'at

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem compact_family_regular_homotopy
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (had : a < d)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (solutions : P → CurveMap M)
    (hsol : ∀ p, (solutions p).IsSolutionOn B.family.metric (Icc a d))
    (hcont : @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions)
    (hreg : immersionContinuityIntoRegularLoops (I := I) (M := M)) :
    ∃ homotopy : C(P × Icc a d, Width.RegularLoop I M),
      ∀ (p : P) (t : Icc a d) z, homotopy (p, t) z = solutions p z t :=
  letI : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  by
    have hbridge : Continuous (fun q : P × Icc a d => SmoothImmersion.slice (solutions q.1)
        (hsol q.1).smooth (hsol q.1).immersed q.2.1 q.2.2) :=
      continuous_iff_continuousAt.mpr fun q =>
        continuousAt_slice_smoothImmersion e had hcont (fun p => (hsol p).smooth)
          (fun p => (hsol p).immersed) q
    refine ⟨⟨fun q => regularLoopOfImmersion (SmoothImmersion.slice (solutions q.1) (hsol q.1).smooth
      (hsol q.1).immersed q.2.1 q.2.2), ?_⟩, ?_⟩
    · exact (@Continuous.comp (P × Icc a d) (SmoothImmersion (I := I) (M := M))
        (Width.RegularLoop I M) inferInstance (smoothImmersionTopology e)
        (Width.regularLoopTopologicalSpace (I := I) (Q := M))
        (fun q : P × Icc a d => SmoothImmersion.slice (solutions q.1) (hsol q.1).smooth
          (hsol q.1).immersed q.2.1 q.2.2) (regularLoopOfImmersion (I := I) (M := M)) (hreg N e)
        hbridge)
    · intro p t z
      rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

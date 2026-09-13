import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Ramps

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace ProductCurve.IsSolutionOn

omit [CompleteSpace E] in
theorem mono {g : ℝ → SmoothRiemannianMetric I M} {lambda : ℝ} {J K : Set ℝ}
    {c : ProductCurve M} (hK : K ⊆ J)
    (huniq : ∀ t ∈ K, UniqueMDiffWithinAt 𝓘(ℝ, ℝ) K t)
    (h : c.IsSolutionOn g lambda J) :
    c.IsSolutionOn g lambda K where
  smooth := ⟨h.smooth.1.mono (Set.prod_mono Subset.rfl hK),
    h.smooth.2.mono (Set.prod_mono Subset.rfl hK)⟩
  immersed := fun x t ht => h.immersed x t (hK ht)
  equation := by
    intro x t ht
    have hy : DifferentiableWithinAt ℝ (c.y x) J t := by
      have hz : ContDiffWithinAt ℝ ∞ (fun s : ℝ => ((x, s) : ℝ × ℝ)) J t := by fun_prop
      exact ((h.smooth.2 (x, t) ⟨mem_univ x, hK ht⟩).comp t hz
        (fun s hs' => ⟨mem_univ x, hs'⟩)).differentiableWithinAt (by simp)
    have hMD : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => c.projection.lift x s) J t :=
      (c.projection.time_slice_contMDiffWithinAt (I := I) J h.smooth.1 x t
        (hK ht)).mdifferentiableWithinAt (by simp)
    have hmem : J ∈ 𝓝[K] t := Filter.mem_of_superset self_mem_nhdsWithin hK
    have h1 : mfderivWithin 𝓘(ℝ, ℝ) I (fun s : ℝ => c.projection.lift x s) K t
        = mfderivWithin 𝓘(ℝ, ℝ) I (fun s : ℝ => c.projection.lift x s) J t :=
      hMD.mfderivWithin_mono_of_mem_nhdsWithin (huniq t ht) hmem
    have h2 : derivWithin (c.y x) K t = derivWithin (c.y x) J t :=
      derivWithin_subset hK (huniq t ht).uniqueDiffWithinAt hy
    have hvel : c.velocity (I := I) K x t = c.velocity (I := I) J x t := by
      simp only [ProductCurve.velocity, CurveMap.velocity, h1, h2]
    rw [hvel]
    exact h.equation x t (hK ht)

omit [CompleteSpace E] in
theorem mono_Icc {g : ℝ → SmoothRiemannianMetric I M} {lambda : ℝ} {a a' b' b : ℝ}
    (ha : a ≤ a') (hb : b' ≤ b) (hab : a' < b') {c : ProductCurve M}
    (h : c.IsSolutionOn g lambda (Icc a b)) :
    c.IsSolutionOn g lambda (Icc a' b') :=
  mono (Icc_subset_Icc ha hb)
    (fun t ht => ((uniqueDiffOn_Icc hab) t ht).uniqueMDiffWithinAt) h

end ProductCurve.IsSolutionOn

namespace ProductCurve.IsRampOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem mono {g : ℝ → SmoothRiemannianMetric I M} {lambda : ℝ} {J K : Set ℝ}
    {c : ProductCurve M} (hK : K ⊆ J) (h : c.IsRampOn g lambda J) :
    c.IsRampOn g lambda K :=
  ⟨fun x t ht => h.1 x t (hK ht), fun x t ht => h.2 x t (hK ht)⟩

end ProductCurve.IsRampOn

variable [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]

variable {D : RealTimeInterval} {a b : ℝ}

structure RampUniformExtension
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) where
  local_time : ℝ
  local_time_pos : 0 < local_time
  exists_from_start : ∀ c₀ : ProductCurve M, c₀.SmoothOn (I := I) {a} →
    c₀.IsRampOn B.family.metric lambda {a} →
    ∃ c : ProductCurve M,
      c.IsSolutionOn B.family.metric lambda (Icc a (a + local_time)) ∧
      c.IsRampOn B.family.metric lambda (Icc a (a + local_time)) ∧
      (∀ z, c.map z a = c₀.map z a) ∧
      ∀ x t, t ∈ Icc a (min b (a + local_time)) →
        c.curvature B.family.metric lambda x t ≤
          c₀.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t
  extend : ∀ (T : ℝ) (c c₀ : ProductCurve M),
    a ≤ T → T < b → c₀.SmoothOn (I := I) {a} →
    c₀.IsRampOn B.family.metric lambda {a} →
    (∀ z, c.map z a = c₀.map z a) →
    c.IsSolutionOn B.family.metric lambda (Icc a T) →
    c.IsRampOn B.family.metric lambda (Icc a T) →
    (∀ x t, t ∈ Icc a T →
      c.curvature B.family.metric lambda x t ≤
        c₀.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t) →
    ∃ c' : ProductCurve M,
      c'.IsSolutionOn B.family.metric lambda (Icc a (T + local_time)) ∧
      c'.IsRampOn B.family.metric lambda (Icc a (T + local_time)) ∧
      (∀ z t, t ∈ Icc a T → c'.map z t = c.map z t) ∧
      ∀ x t, t ∈ Icc a (min b (T + local_time)) →
        c'.curvature B.family.metric lambda x t ≤
          c₀.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t

def RampLocalUniqueness
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) : Prop :=
  ∀ (s t₁ t₂ : ℝ), a ≤ s → s < t₁ → s < t₂ → t₁ ≤ b → t₂ ≤ b →
    ∀ c₁ c₂ : ProductCurve M,
      c₁.IsSolutionOn B.family.metric lambda (Icc s t₁) →
      c₂.IsSolutionOn B.family.metric lambda (Icc s t₂) →
      (∀ z, c₁.map z s = c₂.map z s) →
      ∀ z t, t ∈ Icc s (min t₁ t₂) → c₁.map z t = c₂.map z t

namespace RampExistenceInput

private theorem min_eq_right_of_lt (b x : ℝ) (h : min b x < b) : min b x = x := by
  rcases le_total b x with hbx | hxb
  · rw [min_eq_left hbx] at h
    exact absurd h (lt_irrefl b)
  · exact min_eq_right hxb

theorem of_uniformExtension_and_localUniqueness
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ)
    (H : RampUniformExtension (I := I) (M := M) (D := D) (a := a) (b := b) B lambda)
    (U : RampLocalUniqueness (I := I) (M := M) (D := D) (a := a) (b := b) B lambda) :
    RampExistenceInput (I := I) (M := M) (D := D) (a := a) (b := b) B lambda := by
  refine ⟨?_, ?_⟩
  · intro c₀ hsmooth hramp₀
    have hτ : 0 < H.local_time := H.local_time_pos
    have key : ∀ n : ℕ, 1 ≤ n → ∃ c : ProductCurve M,
        c.IsSolutionOn B.family.metric lambda (Icc a (min b (a + (n : ℝ) * H.local_time))) ∧
        c.IsRampOn B.family.metric lambda (Icc a (min b (a + (n : ℝ) * H.local_time))) ∧
        (∀ z, c.map z a = c₀.map z a) ∧
        ∀ x t, t ∈ Icc a (min b (a + (n : ℝ) * H.local_time)) →
          c.curvature B.family.metric lambda x t ≤
            c₀.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base =>
        obtain ⟨c, hsol, hramp, hdat, hcurv⟩ := H.exists_from_start c₀ hsmooth hramp₀
        have hgoal : min b (a + ((1 : ℕ) : ℝ) * H.local_time) = min b (a + H.local_time) := by
          norm_num
        rw [hgoal]
        exact ⟨c,
          ProductCurve.IsSolutionOn.mono_Icc le_rfl (min_le_right _ _)
            (lt_min B.lt (by linarith)) hsol,
          hramp.mono (Icc_subset_Icc le_rfl (min_le_right _ _)),
          hdat,
          hcurv⟩
      | succ n hn ih =>
        obtain ⟨c, hsol, hramp, hdat, hcurv⟩ := ih
        by_cases hb : min b (a + (n : ℝ) * H.local_time) = b
        · have hnext : min b (a + (((n + 1 : ℕ) : ℝ)) * H.local_time) =
              min b (a + (n : ℝ) * H.local_time) := by
            have hge : b ≤ a + (n : ℝ) * H.local_time := min_eq_left_iff.mp hb
            have hcast : a + (((n + 1 : ℕ) : ℝ)) * H.local_time =
                a + (n : ℝ) * H.local_time + H.local_time := by
              push_cast
              ring
            rw [hcast, min_eq_left (by linarith), hb]
          refine ⟨c, ?_, ?_, hdat, ?_⟩
          · rw [hnext]; exact hsol
          · rw [hnext]; exact hramp
          · intro x t ht
            rw [hnext] at ht
            exact hcurv x t ht
        · have hlt : min b (a + (n : ℝ) * H.local_time) < b :=
            lt_of_le_of_ne (min_le_left _ _) hb
          have hnonneg : (0 : ℝ) ≤ (n : ℝ) * H.local_time :=
            mul_nonneg (Nat.cast_nonneg n) hτ.le
          have hle : a ≤ min b (a + (n : ℝ) * H.local_time) := le_min B.lt.le (by linarith)
          have heq : min b (a + (n : ℝ) * H.local_time) = a + (n : ℝ) * H.local_time :=
            min_eq_right_of_lt b _ hlt
          obtain ⟨c', hsol', hramp', hagree, hcurv'⟩ :=
            H.extend (min b (a + (n : ℝ) * H.local_time)) c c₀ hle hlt hsmooth hramp₀
              hdat hsol hramp hcurv
          have hnext : min b (min b (a + (n : ℝ) * H.local_time) + H.local_time) =
              min b (a + (((n + 1 : ℕ) : ℝ)) * H.local_time) := by
            rw [heq]
            congr 1
            push_cast
            ring
          have hle' : min b (a + (((n + 1 : ℕ) : ℝ)) * H.local_time) ≤
              min b (a + (n : ℝ) * H.local_time) + H.local_time := by
            rw [← hnext]
            exact min_le_right _ _
          have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) * H.local_time :=
            mul_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) hτ
          refine ⟨c',
            ProductCurve.IsSolutionOn.mono_Icc le_rfl hle' (lt_min B.lt (by linarith)) hsol',
            hramp'.mono (Icc_subset_Icc le_rfl hle'), ?_, ?_⟩
          · intro z
            rw [hagree z a ⟨le_rfl, hle⟩]
            exact hdat z
          · intro x t ht
            rw [← hnext] at ht
            exact hcurv' x t ht
    obtain ⟨c, hsol, hramp, hdat, hcurv⟩ :=
      key (Nat.ceil ((b - a) / H.local_time))
        (Nat.succ_le_of_lt (Nat.ceil_pos.mpr (div_pos (sub_pos.mpr B.lt) hτ)))
    have hmul : (b - a) / H.local_time ≤ (Nat.ceil ((b - a) / H.local_time) : ℝ) :=
      Nat.le_ceil _
    rw [div_le_iff₀ hτ] at hmul
    have hmin : min b (a + (Nat.ceil ((b - a) / H.local_time) : ℝ) * H.local_time) = b :=
      min_eq_left (by linarith [hmul])
    rw [hmin] at hsol hramp hcurv
    exact ⟨c, hsol, hramp, hdat, hcurv⟩
  · intro c₀ c d hc hd hc₀ hd₀ z t ht
    exact (U a b b le_rfl B.lt B.lt le_rfl le_rfl c d hc hd
      (fun z => by rw [hc₀ z, hd₀ z]) z t (by simpa using ht)).symm

end RampExistenceInput

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

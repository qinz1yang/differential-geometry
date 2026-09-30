import DifferentialGeometry.Topology.Morse.Strip.StripFlow

namespace DifferentialGeometry.Topology

open Set _root_.Topology
open scoped Manifold ContDiff

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem exists_regular_band_homeomorph {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {a b c : ℝ} (hab : a < b) (hc : c ∈ Icc a b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x ∈ Icc a b → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) :
    ∃ Φ : (f ⁻¹' {c}) × Icc a b ≃ₜ (f ⁻¹' Icc a b),
      (∀ p, f (Φ p).1 = p.2.1) ∧
      ∀ x : f ⁻¹' {c}, (Φ (x, ⟨c, hc⟩)).1 = x.1 := by
  classical
  have hM : MorseStrip I f a b :=
    { smooth := hf
      lt := hab
      compact := hcompact
      regular := by
        intro x hx
        apply hreg x
        rcases hx with hx | hx <;> rw [hx]
        · exact ⟨le_rfl, hab.le⟩
        · exact ⟨hab.le, le_rfl⟩
      nondegenerate := fun x hx hcrit => (hreg x ⟨hx.1.le, hx.2.le⟩ hcrit).elim }
  obtain ⟨D, -, -, -⟩ := exists_gradientLikeStrip hM le_rfl hab le_rfl hM.regular
    (∅ : Finset M) (by
      intro x
      simp only [Finset.notMem_empty, false_iff, not_and]
      exact fun hx => hreg x ⟨hx.1.le, hx.2.le⟩) (R₀ := 1) zero_lt_one
  have htransport (x : M) (hx : f x ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) :
      f (D.flow (f x - t) x) = t := by
    have h := D.f_flow_eq_sub_of_levels hf (T := f x - t) hx
      (by simpa only [sub_sub_cancel] using ht)
      (by intro y hy p hp; exact (Finset.notMem_empty p hp).elim)
      (f x - t) right_mem_uIcc
    simpa only [sub_sub_cancel] using h
  let F : (f ⁻¹' {c}) × Icc a b → (f ⁻¹' Icc a b) := fun p =>
    ⟨D.flow (c - p.2.1) p.1.1, by
      have hx : f p.1.1 = c := p.1.2
      have ht := htransport p.1.1 (by rwa [hx]) p.2.1 p.2.2
      rw [hx] at ht
      change f (D.flow (c - p.2.1) p.1.1) ∈ Icc a b
      rw [ht]
      exact p.2.2⟩
  let G : (f ⁻¹' Icc a b) → (f ⁻¹' {c}) × Icc a b := fun x =>
    (⟨D.flow (f x.1 - c) x.1, htransport x.1 x.2 c hc⟩, ⟨f x.1, x.2⟩)
  have hF (p : (f ⁻¹' {c}) × Icc a b) : f (F p).1 = p.2.1 := by
    have hx : f p.1.1 = c := p.1.2
    have ht := htransport p.1.1 (by rwa [hx]) p.2.1 p.2.2
    simpa only [F, hx] using ht
  have hGF (p : (f ⁻¹' {c}) × Icc a b) : G (F p) = p := by
    apply Prod.ext
    · apply Subtype.ext
      change D.flow (f (F p).1 - c) (D.flow (c - p.2.1) p.1.1) = p.1.1
      rw [hF, D.flow_flow]
      simp only [sub_add_sub_cancel, sub_self, D.flow_zero]
    · exact Subtype.ext (hF p)
  have hFG (x : f ⁻¹' Icc a b) : F (G x) = x := by
    apply Subtype.ext
    change D.flow (c - f x.1) (D.flow (f x.1 - c) x.1) = x.1
    rw [D.flow_flow]
    simp only [sub_add_sub_cancel, sub_self, D.flow_zero]
  let Φ : (f ⁻¹' {c}) × Icc a b ≃ₜ (f ⁻¹' Icc a b) :=
    { toFun := F
      invFun := G
      left_inv := hGF
      right_inv := hFG
      continuous_toFun := by
        apply Continuous.subtype_mk
        change Continuous (fun p : (f ⁻¹' {c}) × Icc a b => D.flow (c - p.2.1) p.1.1)
        exact D.continuous_flow_joint.comp
          ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).prodMk
            (continuous_subtype_val.comp continuous_fst))
      continuous_invFun := by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          exact D.continuous_flow_joint.comp
            (((hf.continuous.comp continuous_subtype_val).sub continuous_const).prodMk
              continuous_subtype_val)
        · exact (hf.continuous.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨Φ, hF, ?_⟩
  intro x
  change D.flow (c - c) x.1 = x.1
  rw [sub_self, D.flow_zero]

theorem exists_regular_level_collar [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hreg : ∀ x, f x = c → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ Φ : (f ⁻¹' {c}) × Icc (c - δ) (c + δ) ≃ₜ
          (f ⁻¹' Icc (c - δ) (c + δ)),
        (∀ p, f (Φ p).1 = p.2.1) ∧
        ∀ (hmem : c ∈ Icc (c - δ) (c + δ)) (x : f ⁻¹' {c}),
          (Φ (x, ⟨c, hmem⟩)).1 = x.1 := by
  have hclosed : IsClosed {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} := by
    simpa only [Set.compl_ofPred, not_not] using (MorseExistence.isOpen_regular hf).isClosed_compl
  have hcritical : IsCompact (f '' {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}) :=
    hclosed.isCompact.image hf.continuous
  have hc : c ∉ f '' {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} := by
    rintro ⟨x, hx, hxc⟩
    exact hreg x hxc hx
  obtain ⟨ε, hε, hεreg⟩ := Metric.mem_nhds_iff.mp
    (hcritical.isClosed.isOpen_compl.mem_nhds hc)
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hband (x : M) (hx : f x ∈ Icc (c - δ) (c + δ)) : ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
    intro hcrit
    have hdist : f x ∈ Metric.ball c ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      dsimp [δ] at hx
      constructor <;> linarith [hx.1, hx.2]
    exact hεreg hdist ⟨x, hcrit, rfl⟩
  have hmem : c ∈ Icc (c - δ) (c + δ) := ⟨by linarith, by linarith⟩
  obtain ⟨Φ, hΦ, hΦc⟩ := exists_regular_band_homeomorph hf (by linarith) hmem
    ((isClosed_Icc.preimage hf.continuous).isCompact) hband
  exact ⟨δ, hδ, Φ, hΦ, fun _ x => hΦc x⟩

end DifferentialGeometry.Topology

import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.VelocityExtensionManifoldFrontier

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {a b : ℝ}

def smoothTimeWedge (u : ℝ) : ℝ := u + (1 - u) * Real.smoothTransition u

theorem contDiff_smoothTimeWedge : ContDiff ℝ ∞ smoothTimeWedge :=
  contDiff_id.add ((contDiff_const.sub contDiff_id).mul Real.smoothTransition.contDiff)

theorem smoothTimeWedge_eq_self_of_nonpos {u : ℝ} (hu : u ≤ 0) : smoothTimeWedge u = u := by
  rw [smoothTimeWedge, Real.smoothTransition.zero_of_nonpos hu]
  ring

theorem smoothTimeWedge_eq_one_of_one_le {u : ℝ} (hu : 1 ≤ u) : smoothTimeWedge u = 1 := by
  rw [smoothTimeWedge, Real.smoothTransition.one_of_one_le hu]
  ring

def loopTimeFold (a b α β : ℝ) (t : ℝ) : ℝ :=
  t - (t - α) * Real.smoothTransition ((a - t) / (a - α))
    + (β - t) * Real.smoothTransition ((t - b) / (β - b))

theorem contDiff_loopTimeFold (a b α β : ℝ) : ContDiff ℝ ∞ (loopTimeFold a b α β) := by
  unfold loopTimeFold
  fun_prop

theorem loopTimeFold_eq_self {a b α β t : ℝ} (hα : α < a) (hβ : b < β)
    (ht : t ∈ Icc a b) : loopTimeFold a b α β t = t := by
  have h1 : (a - t) / (a - α) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith [ht.1]) (by linarith)
  have h2 : (t - b) / (β - b) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith [ht.2]) (by linarith)
  rw [loopTimeFold, Real.smoothTransition.zero_of_nonpos h1,
    Real.smoothTransition.zero_of_nonpos h2]
  ring

theorem loopTimeFold_mem_Icc {a b α β t : ℝ} (hα : α < a) (hab : a ≤ b) (hβ : b < β) :
    loopTimeFold a b α β t ∈ Icc α β := by
  have ha : 0 < a - α := by linarith
  have hb : 0 < β - b := by linarith
  have hT1nn := Real.smoothTransition.nonneg ((a - t) / (a - α))
  have hT1le := Real.smoothTransition.le_one ((a - t) / (a - α))
  have hT2nn := Real.smoothTransition.nonneg ((t - b) / (β - b))
  have hT2le := Real.smoothTransition.le_one ((t - b) / (β - b))
  rcases le_total t α with ht | ht
  · have h2 : (t - b) / (β - b) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hb.le
    have h1 : 1 ≤ (a - t) / (a - α) := (le_div_iff₀ ha).mpr (by linarith)
    rw [loopTimeFold, Real.smoothTransition.zero_of_nonpos h2,
      Real.smoothTransition.one_of_one_le h1]
    exact ⟨by linarith, by linarith⟩
  · rcases le_total t a with hta | hta
    · have h2 : (t - b) / (β - b) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hb.le
      rw [loopTimeFold, Real.smoothTransition.zero_of_nonpos h2]
      exact ⟨by nlinarith, by nlinarith⟩
    · rcases le_total t b with htb | htb
      · have h1 : (a - t) / (a - α) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
        have h2 : (t - b) / (β - b) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) hb.le
        rw [loopTimeFold, Real.smoothTransition.zero_of_nonpos h1,
          Real.smoothTransition.zero_of_nonpos h2]
        exact ⟨by linarith, by linarith⟩
      · have h1 : (a - t) / (a - α) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
        rw [loopTimeFold, Real.smoothTransition.zero_of_nonpos h1]
        rcases le_total β t with hbt | hbt
        · have h2 : 1 ≤ (t - b) / (β - b) := (le_div_iff₀ hb).mpr (by linarith)
          rw [Real.smoothTransition.one_of_one_le h2]
          exact ⟨by linarith, by linarith⟩
        · exact ⟨by nlinarith, by nlinarith⟩

omit [FiniteDimensional ℝ E] in
theorem loopFamilyGlobalSmoothExtension_of_smoothOn_superwindow {α β : ℝ}
    (hα : α < a) (hab : a ≤ b) (hβ : b < β) {γ : ℝ → ContinuousFreeLoop E}
    (hγ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle))
      (Icc α β ×ˢ univ))
    (hemb : ∀ t ∈ Icc α β, Function.Injective (fun z : Surgery.Topology.Circle => γ t z))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) (Icc α β)) :
    LoopFamilyGlobalSmoothExtension a b γ := by
  have hmaps : MapsTo (fun q : ℝ × ℝ => (loopTimeFold a b α β q.1, q.2)) univ
      (Icc α β ×ˢ univ) :=
    fun q _ => ⟨by simpa using loopTimeFold_mem_Icc (t := q.1) hα hab hβ, trivial⟩
  have hfold : ContDiff ℝ ∞ (fun q : ℝ × ℝ => (loopTimeFold a b α β q.1, q.2)) :=
    ((contDiff_loopTimeFold a b α β).comp contDiff_fst).prodMk contDiff_snd
  have hsm : ContDiff ℝ ∞
      (fun q : ℝ × ℝ => γ (loopTimeFold a b α β q.1) (q.2 : Surgery.Topology.Circle)) := by
    have hcomp := hγ.comp hfold.contDiffOn hmaps
    rw [contDiffOn_univ] at hcomp
    exact hcomp
  refine ⟨fun t => γ (loopTimeFold a b α β t), ?_, hsm, ?_, ?_⟩
  · intro t ht
    change γ (loopTimeFold a b α β t) = γ t
    rw [loopTimeFold_eq_self hα hβ ht]
  · intro t
    change Function.Injective (fun z : Surgery.Topology.Circle => γ (loopTimeFold a b α β t) z)
    exact hemb _ (loopTimeFold_mem_Icc (t := t) hα hab hβ)
  · intro q
    have himm : (curveOfLoopFamily (fun t : ℝ => γ (loopTimeFold a b α β t))).ImmersedOn
        (I := 𝓘(ℝ, E)) univ :=
      fun x t _ => hi x _ (loopTimeFold_mem_Icc (t := t) hα hab hβ)
    exact injective_fderiv_graphLift_of_immersedOn hsm himm (mem_univ q)

theorem loopFamilyVelocityExtension_modelSpace_of_smoothOn_superwindow {α β : ℝ}
    (hα : α < a) (hab : a ≤ b) (hβ : b < β) {γ : ℝ → ContinuousFreeLoop E}
    (hγ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle))
      (Icc α β ×ˢ univ))
    (hemb : ∀ t ∈ Icc α β, Function.Injective (fun z : Surgery.Topology.Circle => γ t z))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) (Icc α β)) :
    LoopFamilyVelocityExtension (I := 𝓘(ℝ, E)) a b γ :=
  loopFamilyVelocityExtension_modelSpace_of_globalSmoothExtension
    (loopFamilyGlobalSmoothExtension_of_smoothOn_superwindow hα hab hβ hγ hemb hi)

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_loopFamily_swap {γ : ℝ → ContinuousFreeLoop E} {J : Set ℝ}
    (h : (curveOfLoopFamily γ).SmoothOn (I := 𝓘(ℝ, E)) J) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle))
      (J ×ˢ univ) := by
  have hbase : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => γ p.2 (p.1 : Surgery.Topology.Circle))
      (univ ×ˢ J) := by
    simpa only [CurveMap.SmoothOn, CurveMap.lift, curveOfLoopFamily] using h.contDiffOn
  have hswap : ContDiff ℝ ∞ (fun q : ℝ × ℝ => (q.2, q.1)) := by fun_prop
  have hmaps : MapsTo (fun q : ℝ × ℝ => (q.2, q.1)) (J ×ˢ univ) (univ ×ˢ J) :=
    fun q hq => ⟨trivial, hq.1⟩
  have hcomp := hbase.comp hswap.contDiffOn hmaps
  simpa only [Function.comp_def] using hcomp

section ModelSpaceHeadline

variable [CompactSpace E] [Nonempty E] [SigmaCompactSpace E]

omit [Nonempty E] in
theorem rfs_csf_boundary_isotopy_modelSpace_of_smoothOn_superwindow {α β : ℝ}
    (hα : α < a) (hab : a ≤ b) (hβ : b < β) {γ : ℝ → ContinuousFreeLoop E}
    (hγ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle))
      (Icc α β ×ˢ univ))
    (hemb : ∀ t ∈ Icc α β, Function.Injective (fun z : Surgery.Topology.Circle => γ t z))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) (Icc α β))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun p : E × ℝ => Φ p.2 p.1)
        (univ ×ˢ (Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z :=
  rfs_csf_boundary_isotopy_of_velocityExtension a b γ t₀ ht₀
    (loopFamilyVelocityExtension_modelSpace_of_smoothOn_superwindow hα hab hβ hγ hemb hi)

end ModelSpaceHeadline

section Manifold

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
  [hNonempty : Nonempty M] [SigmaCompactSpace M]

omit hNonempty in
theorem rfs_csf_boundary_isotopy_of_producerOnSuperwindow {α β : ℝ}
    (hα : α ≤ a) (hβ : b ≤ β)
    (h : ∀ γ : ℝ → ContinuousFreeLoop M,
      (curveOfLoopFamily γ).SmoothOn (I := I) (Icc α β) →
      (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc α β) →
      (∀ t ∈ Icc α β, Topology.IsEmbedding (γ t)) →
      LoopFamilyVelocityExtension (I := I) α β γ)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (γ t))
    (hγ' : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc α β))
    (hi' : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc α β))
    (hemb' : ∀ t ∈ Icc α β, Topology.IsEmbedding (γ t))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : M × ℝ => Φ p.2 p.1)
        (univ ×ˢ (Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z := by
  let _ := hγ
  let _ := hi
  let _ := hemb
  exact rfs_csf_boundary_isotopy_of_velocityExtension a b γ t₀ ht₀
    (loopFamilyVelocityExtension_of_subset hα hβ (h γ hγ' hi' hemb'))

end Manifold

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

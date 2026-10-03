import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.VelocityExtensionManifoldFrontier
import DifferentialGeometry.Topology.Diffeomorph.LocalFlowExtension

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
    (hα : α < a) (hab : a ≤ b) (hβ : b < β) {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
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
    (hα : α < a) (hab : a ≤ b) (hβ : b < β) {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hγ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle))
      (Icc α β ×ˢ univ))
    (hemb : ∀ t ∈ Icc α β, Function.Injective (fun z : Surgery.Topology.Circle => γ t z))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) (Icc α β)) :
    LoopFamilyVelocityExtension (I := 𝓘(ℝ, E)) a b γ :=
  loopFamilyVelocityExtension_modelSpace_of_globalSmoothExtension
    (loopFamilyGlobalSmoothExtension_of_smoothOn_superwindow hα hab hβ hγ hemb hi)

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_loopFamily_swap {γ : ℝ → DifferentialGeometry.Topology.freeLoop E} {J : Set ℝ}
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

theorem exists_compact_isotopy_of_smooth_loop_family {α β : ℝ}
    (hα : α < a) (hab : a ≤ b) (hβ : b < β) {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hγ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle))
      (Icc α β ×ˢ univ))
    (hemb : ∀ t ∈ Icc α β, Function.Injective (fun z : Surgery.Topology.Circle => γ t z))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) (Icc α β))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) :
    ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun p : E × ℝ => Φ p.2 p.1) ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun p : E × ℝ => (Φ p.2).symm p.1) ∧
      Φ t₀ = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∃ K : Set E, IsCompact K ∧ ∀ t : ℝ,
        EqOn (Φ t) id Kᶜ ∧ EqOn (Φ t).symm id Kᶜ) ∧
      (∀ t ∈ Icc a b, ∀ z : Surgery.Topology.Circle, Φ t (γ t₀ z) = γ t z) ∧
      (∀ t ∈ Icc a b, ∀ z : Surgery.Topology.Circle, (Φ t).symm (γ t z) = γ t₀ z) ∧
      (∀ t ∈ Icc a b,
        (Φ t) '' Set.range (fun z : Surgery.Topology.Circle => γ t₀ z) =
          Set.range (fun z : Surgery.Topology.Circle => γ t z)) ∧
      ∀ t ∈ Icc a b,
        (Φ t).symm '' Set.range (fun z : Surgery.Topology.Circle => γ t z) =
          Set.range (fun z : Surgery.Topology.Circle => γ t₀ z) := by
  obtain ⟨γ', hagree, hγ', hemb', hi'⟩ :=
    loopFamilyGlobalSmoothExtension_of_smoothOn_superwindow hα hab hβ hγ hemb hi
  obtain ⟨X, hX, hXeq⟩ := exists_contDiff_loopFamilyVelocity a b γ' hemb' hγ' hi'
  let C : Set (ℝ × E) := graphLift γ' '' (Icc a b ×ˢ Icc (0 : ℝ) 1)
  have hA : IsCompact (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hC : IsCompact C := hA.image (continuous_graphLift hγ')
  have hγcont (z : Surgery.Topology.Circle) :
      ContinuousOn (fun t : ℝ => γ' t z) (Icc a b) :=
    (contDiff_loopSlice hγ' z).continuous.continuousOn
  have hγderiv (z : Surgery.Topology.Circle) (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt (fun r : ℝ => γ' r z) (X t (γ' t z)) (Ici t) t := by
    have hd : DifferentiableAt ℝ (fun r : ℝ => γ' r z) t :=
      ((contDiff_loopSlice hγ' z).differentiable (by norm_num)).differentiableAt
    rw [hXeq t (Ico_subset_Icc_self ht) z]
    exact hd.hasDerivAt.hasDerivWithinAt
  have hγC (z : Surgery.Topology.Circle) (t : ℝ) (ht : t ∈ Icc a b) :
      (t, γ' t z) ∈ C := by
    obtain ⟨x, hx, hxz⟩ := exists_lift_mem_Icc z
    refine ⟨(t, x), ⟨ht, hx⟩, ?_⟩
    change (t, γ' t (x : Surgery.Topology.Circle)) = (t, γ' t z)
    rw [hxz]
  have hCU : C ⊆ (univ : Set (ℝ × E)) ∩ (univ ×ˢ (univ : Set E)) :=
    fun _ _ => ⟨trivial, trivial, trivial⟩
  obtain ⟨Φ, hΦ, hΦi, hΦt₀, htrack, K, hK, -, hfixed⟩ :=
    Diffeomorph.exists_contDiff_compact_isotopy_eqOn_integralCurve
      (V := E) (O := univ) isOpen_univ (U := univ) (C := C) isOpen_univ hC hCU
      (W := fun q : ℝ × E => X q.1 q.2) hX.contDiffOn
      (P := Surgery.Topology.Circle) (γ := fun z t => γ' t z)
      (c := fun _ => a) (d := fun _ => b) t₀ hγcont hγderiv hγC
  have hswap : ContDiff ℝ ∞ (fun p : E × ℝ => (p.2, p.1)) :=
    contDiff_snd.prodMk contDiff_fst
  have hΦsm : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : E × ℝ => Φ p.2 p.1) := by
    rw [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := E) (F := ℝ),
      chartedSpaceSelf_prod (H := E) (H' := ℝ)]
    exact (hΦ.comp hswap).contMDiff
  have hΦism : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : E × ℝ => (Φ p.2).symm p.1) := by
    rw [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := E) (F := ℝ),
      chartedSpaceSelf_prod (H := E) (H' := ℝ)]
    exact (hΦi.comp hswap).contMDiff
  have hbase (z : Surgery.Topology.Circle) : (Φ a).symm (γ' a z) = γ' t₀ z := by
    simpa only [hΦt₀, Diffeomorph.coe_refl, id_eq] using htrack z t₀ ht₀
  have htrackOriginal : ∀ t ∈ Icc a b, ∀ z : Surgery.Topology.Circle,
      Φ t (γ t₀ z) = γ t z := by
    intro t ht z
    have h := htrack z t ht
    rw [hbase z, hagree t₀ ht₀, hagree t ht] at h
    exact h
  have htrackInverse : ∀ t ∈ Icc a b, ∀ z : Surgery.Topology.Circle,
      (Φ t).symm (γ t z) = γ t₀ z := by
    intro t ht z
    rw [← htrackOriginal t ht z, Diffeomorph.symm_apply_apply]
  refine ⟨Φ, hΦsm, hΦism, hΦt₀, ⟨K, hK, hfixed⟩, htrackOriginal, htrackInverse, ?_, ?_⟩
  · intro t ht
    ext p
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, (htrackOriginal t ht z).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨γ t₀ z, ⟨z, rfl⟩, htrackOriginal t ht z⟩
  · intro t ht
    ext p
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, (htrackInverse t ht z).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨γ t z, ⟨z, rfl⟩, htrackInverse t ht z⟩

theorem rfs_csf_boundary_isotopy_modelSpace_of_smoothOn_superwindow {α β : ℝ}
    (hα : α < a) (hab : a ≤ b) (hβ : b < β) {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
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
      ∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z := by
  obtain ⟨Φ, hΦ, -, hΦt₀, -, htrack, -, -, -⟩ :=
    exists_compact_isotopy_of_smooth_loop_family hα hab hβ hγ hemb hi t₀ ht₀
  refine ⟨(1 / 2 : ℝ), by norm_num, Φ, hΦ.contMDiffOn, ?_, ?_⟩
  · intro p
    rw [hΦt₀]
    rfl
  · intro t ht z
    exact htrack t ht.1 z

end ModelSpaceHeadline

section Manifold

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
  [hNonempty : Nonempty M] [SigmaCompactSpace M]

omit hNonempty in
theorem rfs_csf_boundary_isotopy_of_producerOnSuperwindow {α β : ℝ}
    (hα : α ≤ a) (hβ : b ≤ β)
    (h : ∀ γ : ℝ → DifferentialGeometry.Topology.freeLoop M,
      (curveOfLoopFamily γ).SmoothOn (I := I) (Icc α β) →
      (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc α β) →
      (∀ t ∈ Icc α β, Topology.IsEmbedding (γ t)) →
      LoopFamilyVelocityExtension (I := I) α β γ)
    (γ : ℝ → DifferentialGeometry.Topology.freeLoop M)
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

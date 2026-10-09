import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.VelocityExtension

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem contMDiff_tangentSection_of_contDiff {X : ℝ → E → E}
    (hX : ContDiff ℝ ∞ (fun q : ℝ × E => X q.1 q.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × E => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle 𝓘(ℝ, E) E)) := by
  have hg : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun q : ℝ × E => X q.1 q.2) := by
    rw [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := E),
      chartedSpaceSelf_prod (H := ℝ) (H' := E)]
    exact hX.contMDiff
  intro q
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact (contMDiffAt_snd :
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => q.2) q)
  · refine hg.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [trivializationAt_model_space_apply]

omit [FiniteDimensional ℝ E] in
theorem hasMFDerivWithinAt_smulRight_of_hasDerivWithinAt {f : ℝ → E} {t : ℝ} {v : E}
    {s : Set ℝ} (h : HasDerivWithinAt f v s t) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) f s t ((1 : ℝ →L[ℝ] ℝ).smulRight v) :=
  h.hasFDerivWithinAt.hasMFDerivWithinAt

omit [FiniteDimensional ℝ E] in
theorem contDiff_loopSlice {γ : ℝ → ContinuousFreeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle)))
    (z : Surgery.Topology.Circle) : ContDiff ℝ ∞ (fun r : ℝ => γ r z) := by
  obtain ⟨x, -, hx⟩ := exists_lift_mem_Icc z
  have h : ContDiff ℝ ∞ (fun r : ℝ => γ r (x : Surgery.Topology.Circle)) :=
    hγ.comp (contDiff_id.prodMk contDiff_const)
  simpa only [hx] using h

omit [FiniteDimensional ℝ E] in
theorem hasMFDerivWithinAt_loopSlice_of_deriv_eq {γ : ℝ → ContinuousFreeLoop E}
    {X : ℝ → E → E} {t : ℝ} {z : Surgery.Topology.Circle} {s : Set ℝ}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle)))
    (hX : X t (γ t z) = deriv (fun r : ℝ => γ r z) t) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r : ℝ => γ r z) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t z))) := by
  have hdiff : DifferentiableAt ℝ (fun r : ℝ => γ r z) t :=
    ((contDiff_loopSlice hγ z).differentiable (by norm_num)).differentiableAt
  have hd : HasDerivAt (fun r : ℝ => γ r z) (deriv (fun r : ℝ => γ r z) t) t :=
    hdiff.hasDerivAt
  rw [hX]
  exact hasMFDerivWithinAt_smulRight_of_hasDerivWithinAt hd.hasDerivWithinAt

omit [FiniteDimensional ℝ E] in
theorem fderiv_graphLift_apply {γ : ℝ → ContinuousFreeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle)))
    (q : ℝ × ℝ) :
    fderiv ℝ (graphLift γ) q =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (fderiv ℝ (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) q) := by
  have hΓ : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) q :=
    (hγ.differentiable (by norm_num)).differentiableAt
  rw [show graphLift γ = fun p : ℝ × ℝ =>
    (p.1, γ p.1 (p.2 : Surgery.Topology.Circle)) from rfl]
  rw [(differentiableAt_fst (p := q)).fderiv_prodMk hΓ, fderiv_fst]

omit [FiniteDimensional ℝ E] in
theorem fderiv_slice_apply_zero_one_eq_deriv {γ : ℝ → ContinuousFreeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle)))
    (q : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) q (0, 1) =
      deriv (fun y : ℝ => γ q.1 (y : Surgery.Topology.Circle)) q.2 := by
  have hΓ : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) q :=
    (hγ.differentiable (by norm_num)).differentiableAt
  have hin : HasFDerivAt (fun y : ℝ => (q.1, y)) (ContinuousLinearMap.inr ℝ ℝ ℝ) q.2 :=
    hasFDerivAt_prodMk_right q.1 q.2
  have hcomp := hΓ.hasFDerivAt.comp q.2 hin
  have hslice : (fun y : ℝ => γ q.1 (y : Surgery.Topology.Circle)) =
      (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) ∘
        (fun y : ℝ => (q.1, y)) := rfl
  rw [← fderiv_apply_one_eq_deriv
    (f := fun y : ℝ => γ q.1 (y : Surgery.Topology.Circle)) (x := q.2), hslice, hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply]

omit [FiniteDimensional ℝ E] in
theorem injective_fderiv_graphLift_of_slice_deriv_ne {γ : ℝ → ContinuousFreeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle)))
    {q : ℝ × ℝ}
    (hne : deriv (fun y : ℝ => γ q.1 (y : Surgery.Topology.Circle)) q.2 ≠ 0) :
    Function.Injective (fderiv ℝ (graphLift γ) q) := by
  rw [fderiv_graphLift_apply hγ q]
  intro u v huv
  have h0 : ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (fderiv ℝ (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) q))
      (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have h1 : (u - v).1 = 0 := by
    have := congrArg Prod.fst h0
    simpa using this
  have h2 : fderiv ℝ (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) q
      (u - v) = 0 := by
    have := congrArg Prod.snd h0
    simpa using this
  have h3 : (u - v).2 = 0 := by
    have hsplit0 : u - v = (0, (u - v).2) := by
      rw [← Prod.eta (u - v), h1]
    have hsm : u - v = (u - v).2 • ((0, 1) : ℝ × ℝ) := by
      rw [hsplit0]
      simp
    have hsplit : fderiv ℝ (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) q
        (u - v) = (u - v).2 •
        fderiv ℝ (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) q (0, 1) := by
      conv_lhs => rw [hsm]
      rw [map_smul]
    have h4 : (u - v).2 •
        deriv (fun y : ℝ => γ q.1 (y : Surgery.Topology.Circle)) q.2 = 0 := by
      rw [← fderiv_slice_apply_zero_one_eq_deriv hγ q, ← hsplit, h2]
    exact (smul_eq_zero.mp h4).resolve_right hne
  have hz : u - v = 0 := Prod.ext h1 h3
  exact sub_eq_zero.mp hz

theorem loopFamilyVelocityExtension_modelSpace (a b : ℝ) (γ : ℝ → ContinuousFreeLoop E)
    (hemb : ∀ t, Function.Injective (fun z : Surgery.Topology.Circle => γ t z))
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle)))
    (hi : ∀ q : ℝ × ℝ, Function.Injective (fderiv ℝ (graphLift γ) q)) :
    LoopFamilyVelocityExtension (I := 𝓘(ℝ, E)) a b γ := by
  obtain ⟨X, hX, hXeq⟩ := exists_contDiff_loopFamilyVelocity a b γ hemb hγ hi
  refine ⟨fun t p => (X t p : TangentSpace 𝓘(ℝ, E) p), ?_, ?_, ?_⟩
  · exact contMDiff_tangentSection_of_contDiff hX
  · intro t ht z
    exact hasMFDerivWithinAt_loopSlice_of_deriv_eq hγ (hXeq t (Ico_subset_Icc_self ht) z)
  · intro t ht z
    exact hasMFDerivWithinAt_loopSlice_of_deriv_eq hγ (hXeq t (Ioc_subset_Icc_self ht) z)

omit [FiniteDimensional ℝ E] in
private theorem deriv_loopSlice_ne_zero_of_immersedOn {γ : ℝ → ContinuousFreeLoop E}
    {J : Set ℝ} {x t : ℝ} (ht : t ∈ J)
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) J) :
    deriv (fun y : ℝ => γ t (y : Surgery.Topology.Circle)) x ≠ 0 := by
  intro hzero
  refine hi x t ht ?_
  simp only [CurveMap.X, CurveMap.lift, curveOfLoopFamily, mfderiv_eq_fderiv]
  exact hzero

omit [FiniteDimensional ℝ E] in
theorem injective_fderiv_graphLift_of_immersedOn {γ : ℝ → ContinuousFreeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle)))
    {J : Set ℝ} (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) J)
    {x t : ℝ} (ht : t ∈ J) :
    Function.Injective (fderiv ℝ (graphLift γ) (t, x)) :=
  injective_fderiv_graphLift_of_slice_deriv_ne hγ (deriv_loopSlice_ne_zero_of_immersedOn ht hi)

omit [FiniteDimensional ℝ E] in
private theorem contDiff_translationLoops (v : E) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
      (ContinuousMap.const (Surgery.Topology.Circle) (q.1 • v))
        (q.2 : Surgery.Topology.Circle)) := by
  have h : ContDiff ℝ ∞ (fun q : ℝ × ℝ => q.1 • v) :=
    (contDiff_fst : ContDiff ℝ ∞ (fun q : ℝ × ℝ => q.1)).smul contDiff_const
  simpa only [ContinuousMap.const_apply] using h

omit [FiniteDimensional ℝ E] in
theorem loopFamilyVelocityExtension_translation (a b : ℝ) (v : E) :
    LoopFamilyVelocityExtension (I := 𝓘(ℝ, E)) a b
      (fun t : ℝ => ContinuousMap.const (Surgery.Topology.Circle) (t • v)) := by
  refine ⟨fun _ p => (v : TangentSpace 𝓘(ℝ, E) p), ?_, ?_, ?_⟩
  · exact contMDiff_tangentSection_of_contDiff (X := fun _ _ => v) contDiff_const
  · intro t ht z
    refine hasMFDerivWithinAt_smulRight_of_hasDerivWithinAt ?_
    simpa [ContinuousMap.const_apply] using
      ((hasDerivAt_id t).smul_const v).hasDerivWithinAt
  · intro t ht z
    refine hasMFDerivWithinAt_smulRight_of_hasDerivWithinAt ?_
    simpa [ContinuousMap.const_apply] using
      ((hasDerivAt_id t).smul_const v).hasDerivWithinAt

omit [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
theorem translation_velocity_eq {a b : ℝ} {v : E}
    {X : ℝ → (p : E) → TangentSpace 𝓘(ℝ, E) p}
    (hX : ∀ t ∈ Ico a b, ∀ z : Surgery.Topology.Circle,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        (fun s : ℝ => (ContinuousMap.const (Surgery.Topology.Circle) (s • v))
          (z : Surgery.Topology.Circle)) (Ici t) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (t • v)))) :
    ∀ t ∈ Ico a b, ∀ _z : Surgery.Topology.Circle, X t (t • v) = v := by
  intro t ht z
  have h1 : HasFDerivWithinAt (fun s : ℝ => s • v)
      ((1 : ℝ →L[ℝ] ℝ).smulRight v) (Ici t) t := by
    have hd : HasDerivWithinAt (fun s : ℝ => s • v) v (Ici t) t := by
      simpa using ((hasDerivAt_id t).smul_const v).hasDerivWithinAt
    simpa only [← ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using hd.hasFDerivWithinAt
  have h2 : HasFDerivWithinAt (fun s : ℝ => s • v)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (t • v))) (Ici t) t := by
    simpa [ContinuousMap.const_apply] using (hX t ht z).hasFDerivWithinAt
  have hval := congrArg (fun L : ℝ →L[ℝ] E => L 1) ((uniqueDiffWithinAt_Ici t).eq h2 h1)
  simpa [ContinuousLinearMap.smulRight_apply] using hval

theorem exists_contMDiff_tangentSection_eqOn_of_localCover {ι : Type*} {K : Set (ℝ × E)}
    (hK : IsCompact K) (s : Finset ι) (U : ι → Set (ℝ × E)) (hUo : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i ∈ s, U i) {g : ι → ℝ × E → E}
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i))
    (hcons : ∀ i ∈ s, ∀ j ∈ s, ∀ q ∈ (K ∩ U i) ∩ U j, g i q = g j q) :
    ∃ G : ℝ × E → E,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × E =>
          (TotalSpace.mk' E q.2 (G q) : TangentBundle 𝓘(ℝ, E) E)) ∧
      ∀ i ∈ s, ∀ q ∈ K ∩ U i, G q = g i q := by
  obtain ⟨G, hG, hGeq⟩ := exists_contDiff_eqOn_of_localCover hK s U hUo hcover hg hcons
  exact ⟨G, contMDiff_tangentSection_of_contDiff (X := fun t p => G (t, p))
    (by simpa using hG), hGeq⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

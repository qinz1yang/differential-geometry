import DifferentialGeometry.Topology.Ehresmann.SmoothCompletionCharts
import DifferentialGeometry.Topology.Manifold.SmoothOpenCover
import DifferentialGeometry.Geometry.Boundary.EndpointCollars

noncomputable section
open Set Filter Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

universe uE uH uM uQ

set_option backward.isDefEq.respectTransparency false in
private theorem three_patch_atlas
    {E F : Type uE} {H G : Type uH} {M N : Type uM} {Q : Type uQ}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N]
    [TopologicalSpace Q] [ChartedSpace H M] [ChartedSpace G N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [IsManifold I ∞ M] [IsManifold J ∞ N] [J.Boundaryless]
    (e : OpenPartialHomeomorph M Q) (l r : OpenPartialHomeomorph N Q)
    (L : F ≃L[ℝ] E) (hi : e.source ⊆ I.interior M)
    (hcover : ∀ q, q ∈ e.target ∨ q ∈ l.target ∨ q ∈ r.target)
    (hdis : Disjoint l.target r.target)
    (hel : ContMDiffOn I J ∞ (e.trans l.symm) (e.trans l.symm).source)
    (hle : ContMDiffOn J I ∞ (l.trans e.symm) (l.trans e.symm).source)
    (her : ContMDiffOn I J ∞ (e.trans r.symm) (e.trans r.symm).source)
    (hre : ContMDiffOn J I ∞ (r.trans e.symm) (r.trans e.symm).source) :
    ∃ C : ChartedSpace E Q, letI := C
      IsManifold 𝓘(ℝ, E) ∞ Q ∧
      (ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source ∧
        ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target) ∧
      (ContMDiffOn J 𝓘(ℝ, E) ∞ l l.source ∧
        ContMDiffOn 𝓘(ℝ, E) J ∞ l.symm l.target) ∧
      (ContMDiffOn J 𝓘(ℝ, E) ∞ r r.source ∧
        ContMDiffOn 𝓘(ℝ, E) J ∞ r.symm r.target) := by
  let V : Option Bool → Type _ := fun j ↦ match j with | none => E | some _ => F
  let W : Option Bool → Type _ := fun j ↦ match j with | none => H | some _ => G
  let P : Option Bool → Type _ := fun j ↦ match j with | none => M | some _ => N
  let vn (j) : NormedAddCommGroup (V j) := by cases j <;> dsimp [V] <;> infer_instance
  let vs (j) : NormedSpace ℝ (V j) := by cases j <;> dsimp [V, vn] <;> infer_instance
  let wt (j) : TopologicalSpace (W j) := by cases j <;> dsimp [W] <;> infer_instance
  let pt (j) : TopologicalSpace (P j) := by cases j <;> dsimp [P] <;> infer_instance
  let pc (j) : ChartedSpace (W j) (P j) := by
    cases j <;> dsimp [W, P, wt, pt] <;> infer_instance
  let K : ∀ j, ModelWithCorners ℝ (V j) (W j) := fun j ↦ match j with
    | none => I
    | some _ => J
  let pm (j) : IsManifold (K j) ∞ (P j) := by
    cases j <;> dsimp [K, P, pc] <;> infer_instance
  let f : ∀ j, OpenPartialHomeomorph (P j) Q := fun j ↦ match j with
    | none => e
    | some false => l
    | some true => r
  let A : ∀ j, V j ≃L[ℝ] E := fun j ↦ match j with
    | none => ContinuousLinearEquiv.refl ℝ E
    | some _ => L
  have hfcover : ∀ q, ∃ j, q ∈ (f j).target := by
    intro q
    rcases hcover q with h | h | h
    · exact ⟨none, h⟩
    · exact ⟨some false, h⟩
    · exact ⟨some true, h⟩
  have hfi : ∀ j, (f j).source ⊆ (K j).interior (P j) := by
    intro j x hx
    cases j with
    | none => exact hi hx
    | some b => exact BoundarylessManifold.isInteriorPoint
  have hfcompat : ∀ i j, ContMDiffOn (K i) (K j) ∞
      ((f i).trans (f j).symm) ((f i).trans (f j).symm).source := by
    intro i j
    cases i with
    | none =>
      cases j with
      | none => exact contMDiffOn_id.congr (fun x hx ↦ e.left_inv hx.1)
      | some b => cases b with | false => exact hel | true => exact her
    | some b =>
      cases j with
      | none => cases b with | false => exact hle | true => exact hre
      | some c =>
        cases b <;> cases c
        · exact contMDiffOn_id.congr (fun x hx ↦ l.left_inv hx.1)
        · intro x hx
          exact (disjoint_left.mp hdis (l.map_source hx.1) hx.2).elim
        · intro x hx
          exact (disjoint_left.mp hdis hx.2 (r.map_source hx.1)).elim
        · exact contMDiffOn_id.congr (fun x hx ↦ r.left_inv hx.1)
  obtain ⟨C, hm, hs⟩ := exists_smoothAtlas_of_openCover f hfcover hfi A hfcompat
  exact ⟨C, hm, hs none, hs (some false), hs (some true)⟩

private theorem smooth_function_in_patch
    {E F H G P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace P] [TopologicalSpace Q]
    [ChartedSpace H P] [ChartedSpace G Q]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    (d : OpenPartialHomeomorph P Q) (hd : ContMDiffOn J I ∞ d.symm d.target)
    {f : Q → ℝ} {g : P → ℝ} (hg : ContMDiffOn I 𝓘(ℝ) ∞ g d.source)
    (heq : ∀ x ∈ d.source, f (d x) = g x) : ContMDiffOn J 𝓘(ℝ) ∞ f d.target := by
  apply (hg.comp hd (fun _ hq ↦ d.map_target hq)).congr
  intro q hq
  have hh := heq (d.symm q) (d.map_target hq)
  rwa [d.right_inv hq] at hh

set_option backward.isDefEq.respectTransparency false in
private theorem smooth_inclusion_in_collar
    {E F H G B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace M]
    [ChartedSpace H B] [ChartedSpace G M]
    {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F G}
    {u : M → ℝ} {a b k : ℝ} [ChartedSpace F (IntervalCompletionSpace u a b)]
    (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (c : PartialDiffeomorph (J.prod (𝓡∂ 1)) I (B × EuclideanHalfSpace 1) M ∞)
    (d : OpenPartialHomeomorph (B × ℝ) (IntervalCompletionSpace u a b))
    (hdT : d.target = {q | q.1.1 ∈ c.target})
    (hdi : ∀ q ∈ d.target, d.symm q = ((c.symm q.1.1).1, q.1.2 - k))
    (hd : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ d d.source) :
    ContMDiffOn I 𝓘(ℝ, F) ∞ (intervalCompletionInclusion u a b) c.target := by
  let χ : M → B × ℝ := fun y ↦ ((c.symm y).1, u y - k)
  have hχ : ContMDiffOn I (J.prod 𝓘(ℝ)) ∞ χ c.target :=
    (contMDiff_fst.comp_contMDiffOn c.symm.contMDiffOn).prodMk
      (hu.contMDiffOn.sub contMDiffOn_const)
  have hmem (y : M) (hy : y ∈ c.target) : intervalCompletionInclusion u a b y ∈ d.target := by
    rw [hdT]
    exact hy
  have hχeq (y : M) (hy : y ∈ c.target) :
      d.symm (intervalCompletionInclusion u a b y) = χ y := hdi _ (hmem y hy)
  have hmap : MapsTo χ c.target d.source := by
    intro y hy
    rw [← hχeq y hy]
    exact d.map_target (hmem y hy)
  apply (hd.comp hχ hmap).congr
  intro y hy
  rw [Function.comp_apply, ← hχeq y hy, d.right_inv (hmem y hy)]

set_option backward.isDefEq.respectTransparency false in
private theorem injective_inclusion_in_collar
    {E F H G B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace M]
    [ChartedSpace H B] [ChartedSpace G M]
    {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F G}
    {u : M → ℝ} {a b k σ : ℝ} [ChartedSpace F (IntervalCompletionSpace u a b)]
    (hσ : σ ≠ 0)
    (c : PartialDiffeomorph (J.prod (𝓡∂ 1)) I (B × EuclideanHalfSpace 1) M ∞)
    (d : OpenPartialHomeomorph (B × ℝ) (IntervalCompletionSpace u a b))
    (hdT : d.target = {q | q.1.1 ∈ c.target})
    (hdi : ∀ q ∈ d.target, d.symm q = ((c.symm q.1.1).1, q.1.2 - k))
    (hh : ∀ z ∈ c.source, u (c z) = k + σ * z.2.1 0)
    (hd : ContMDiffOn 𝓘(ℝ, F) (J.prod 𝓘(ℝ)) ∞ d.symm d.target)
    (hi : ContMDiffOn I 𝓘(ℝ, F) ∞ (intervalCompletionInclusion u a b) c.target)
    {x : M} (hx : x ∈ c.target) :
    Function.Injective (mfderiv I 𝓘(ℝ, F) (intervalCompletionInclusion u a b) x) := by
  let f := intervalCompletionInclusion u a b
  let ψ : B × EuclideanHalfSpace 1 → B × ℝ := fun z ↦ (z.1, σ * z.2.1 0)
  have hψ : ContMDiff (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ)) ∞ ψ :=
    contMDiff_fst.prodMk (contMDiff_const.mul
      (contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd))
  have hfx : f x ∈ d.target := by rw [hdT]; exact hx
  have heq : d.symm ∘ f =ᶠ[𝓝 x] ψ ∘ c.symm := by
    filter_upwards [c.open_target.mem_nhds hx] with y hy
    have hfy : f y ∈ d.target := by rw [hdT]; exact hy
    change d.symm (f y) = ψ (c.symm y)
    rw [hdi _ hfy]
    change ((c.symm y).1, u y - k) = ((c.symm y).1, σ * (c.symm y).2.1 0)
    congr 1
    have hhy := hh (c.symm y) (c.map_target hy)
    have hr : c (c.symm y) = y := c.right_inv hy
    rw [hr] at hhy
    change u y - k = σ * (c.symm y).2.1 0
    linarith
  have hcinv := (c.symm.contMDiffOn.contMDiffAt (c.open_target.mem_nhds hx)).mdifferentiableAt
    (by simp)
  have hj : Function.Injective (mfderiv I (J.prod 𝓘(ℝ)) (ψ ∘ c.symm) x) := by
    rw [mfderiv_comp x (hψ.mdifferentiableAt (by simp)) hcinv]
    exact (injective_mfderiv_scaledHalfSpaceOneProductCoordinate J hσ (c.symm x)).comp
      ((PartialDiffeomorph.isLocalDiffeomorphAt I (J.prod (𝓡∂ 1)) ∞ c.symm hx).mfderivToContinuousLinearEquiv (by simp)).injective
  have heqd : mfderiv I (J.prod 𝓘(ℝ)) (d.symm ∘ f) x =
      mfderiv I (J.prod 𝓘(ℝ)) (ψ ∘ c.symm) x := by
    rw [heq.mfderiv_eq]
    rfl
  rw [← heqd, mfderiv_comp x
    ((hd.contMDiffAt (d.open_target.mem_nhds hfx)).mdifferentiableAt (by simp))
    ((hi.contMDiffAt (c.open_target.mem_nhds hx)).mdifferentiableAt (by simp))] at hj
  intro v w hvw
  apply hj
  exact congrArg (mfderiv 𝓘(ℝ, F) (J.prod 𝓘(ℝ)) d.symm (f x)) hvw

set_option backward.isDefEq.respectTransparency false in
private theorem regular_function_in_patch
    {E F H G P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace P] [TopologicalSpace Q]
    [ChartedSpace H P] [ChartedSpace G Q]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    (d : OpenPartialHomeomorph P Q) (hd : ContMDiffOn I J ∞ d d.source)
    {f : Q → ℝ} {g : P → ℝ} (hf : ContMDiffOn J 𝓘(ℝ) ∞ f d.target)
    (hg : ∀ x ∈ d.source, mfderiv I 𝓘(ℝ) g x ≠ 0)
    (heq : ∀ x ∈ d.source, f (d x) = g x) {q : Q} (hq : q ∈ d.target) :
    mfderiv J 𝓘(ℝ) f q ≠ 0 := by
  intro hz
  let x := d.symm q
  have hx : x ∈ d.source := d.map_target hq
  have hevent : g =ᶠ[𝓝 x] f ∘ d := by
    filter_upwards [d.open_source.mem_nhds hx] with y hy
    exact (heq y hy).symm
  apply hg x hx
  calc
    mfderiv I 𝓘(ℝ) g x = mfderiv I 𝓘(ℝ) (f ∘ d) x := hevent.mfderiv_eq
    _ = (mfderiv J 𝓘(ℝ) f (d x)).comp (mfderiv I J d x) :=
      mfderiv_comp x
        ((hf.contMDiffAt (d.open_target.mem_nhds (d.map_source hx))).mdifferentiableAt (by simp))
        ((hd.contMDiffAt (d.open_source.mem_nhds hx)).mdifferentiableAt (by simp))
    _ = 0 := by rw [show d x = q from d.right_inv hq, hz, ContinuousLinearMap.zero_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem regular_signed_height
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℝ E H) (k : ℝ) (z : B × ℝ) :
    mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) (fun p : B × ℝ ↦ k + p.2) z ≠ 0 := by
  have hh : mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) (fun p : B × ℝ ↦ k + p.2) z (0, (1 : ℝ)) = (1 : ℝ) := by
    change (mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) ((fun _ : B × ℝ ↦ k) + Prod.snd) z) (0, (1 : ℝ)) = (1 : ℝ)
    rw [mfderiv_add mdifferentiableAt_const mdifferentiableAt_snd]
    simp only [mfderiv_const, mfderiv_snd, zero_add]
    rfl
  intro hz
  rw [hz] at hh
  change (0 : ℝ) = 1 at hh
  exact zero_ne_one hh

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I]
  [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_smooth_intervalCompletion [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {a b : ℝ}
    (hab : a < b) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) u x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)
    (ha : a ∈ range u) (hb : b ∈ range u) :
    ∃ C : ChartedSpace E (IntervalCompletionSpace u a b), letI := C
      IsManifold 𝓘(ℝ, E) ∞ (IntervalCompletionSpace u a b) ∧
      ContMDiff I 𝓘(ℝ, E) ∞ (intervalCompletionInclusion u a b) ∧
      (∀ x, Function.Injective (mfderiv I 𝓘(ℝ, E) (intervalCompletionInclusion u a b) x)) ∧
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (intervalCompletionHeight u a b) ∧
      ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (intervalCompletionHeight u a b) q ≠ 0 := by
  have hbounds := fun x ↦ range_subset_Icc_of_boundary_values hab.le hreg hboundary (mem_range_self x)
  have hmin : ∀ x, u x = a → IsLocalMin u x := fun x hx ↦
    Eventually.of_forall (fun y ↦ by simpa only [hx] using (hbounds y).1)
  have hmax : ∀ x, u x = b → IsLocalMax u x := fun x hx ↦
    Eventually.of_forall (fun y ↦ by simpa only [hx] using (hbounds y).2)
  let B := BoundaryManifold I M
  have hK₀ := (isClopen_boundary_level_of_two_values (I := I) hab.ne hu.continuous hboundary).isOpen
  have hK₁ := (isClopen_boundary_level_of_two_values (I := I) hab.ne.symm hu.continuous
    (fun x hx ↦ (hboundary x hx).symm)).isOpen
  have hK₀ne : {x : B | u x.1 = a}.Nonempty := by
    obtain ⟨x, hx⟩ := ha
    exact ⟨⟨x, isBoundaryPoint_of_isLocalMin_of_mfderiv_ne_zero (hmin x hx) (hreg x)⟩, hx⟩
  have hK₁ne : {x : B | u x.1 = b}.Nonempty := by
    obtain ⟨x, hx⟩ := hb
    exact ⟨⟨x, isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero (hmax x hx) (hreg x)⟩, hx⟩
  obtain ⟨ε, hε, hgap, c₀, c₁, hc₀, hc₁, hz₀, hz₁, hh₀, hh₁, hct₀, hct₁, hcd, _, _⟩ :=
    exists_disjoint_adapted_endpoint_collars g hab hu hreg hboundary ha hb
  have hgap' : a + ε < b := by linarith
  obtain ⟨l, _, hlT, hlf, hli, hle, hel⟩ :=
    exists_lower_smooth_completionChart hu hK₀ hK₀ne hε hgap' c₀ hc₀ hz₀ hh₀
  obtain ⟨r, _, hrT, hrf, hri, hre, her⟩ :=
    exists_upper_smooth_completionChart hu hK₁ hK₁ne hε hgap' c₁ hc₁ hz₁ hh₁
  let e := intervalCompletionInterior hu.continuous a b
  have hi : e.source ⊆ I.interior M := by
    intro x hx
    apply (I.isInteriorPoint_iff_not_isBoundaryPoint x).2
    intro hbdy
    rcases hboundary x hbdy with hh | hh
    · exact (ne_of_gt hx.1) hh
    · exact (ne_of_lt hx.2) hh
  have hcover : ∀ q : IntervalCompletionSpace u a b,
      q ∈ e.target ∨ q ∈ l.target ∨ q ∈ r.target := by
    intro q
    have hl (h : u q.1.1 = a) : q ∈ l.target := by
      rw [hlT]
      exact hct₀ h
    have hr (h : u q.1.1 = b) : q ∈ r.target := by
      rw [hrT]
      exact hct₁ h
    rcases q.2 with h | ⟨h, _⟩ | ⟨h, _⟩
    · rcases (hbounds q.1.1).1.eq_or_lt with ha | ha
      · exact Or.inr (Or.inl (hl ha.symm))
      rcases (hbounds q.1.1).2.eq_or_lt with hb | hb
      · exact Or.inr (Or.inr (hr hb))
      exact Or.inl (show q.1.2 ∈ Ioo a b from h.symm ▸ ⟨ha, hb⟩)
    · exact Or.inr (Or.inl (hl h))
    · exact Or.inr (Or.inr (hr h))
  have hd : Disjoint l.target r.target := by
    rw [hlT, hrT]
    exact hcd.preimage (fun q : IntervalCompletionSpace u a b ↦ q.1.1)
  have hdim : Module.finrank ℝ (hI.boundaryE × ℝ) = Module.finrank ℝ E := by
    rw [Module.finrank_prod, Module.finrank_self]
    exact hI.finrank_boundaryE_succ
  let L : (hI.boundaryE × ℝ) ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hdim
  obtain ⟨C, hm, heS, hlS, hrS⟩ := three_patch_atlas e l r L hi hcover hd hel hle her hre
  let := C
  let := hm
  have hincl₀ := smooth_inclusion_in_collar hu c₀ l hlT hli hlS.1
  have hincl₁ := smooth_inclusion_in_collar hu c₁ r hrT hri hrS.1
  have hf₀ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (intervalCompletionHeight u a b) e.target :=
    smooth_function_in_patch e heS.2 hu.contMDiffOn (fun _ _ ↦ rfl)
  have hfl : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (intervalCompletionHeight u a b) l.target :=
    smooth_function_in_patch l hlS.2 (contMDiffOn_const.add contMDiffOn_snd)
      (fun z hz ↦ congrArg (fun p : M × ℝ ↦ p.2) (hlf z hz))
  have hfr : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (intervalCompletionHeight u a b) r.target :=
    smooth_function_in_patch r hrS.2 (contMDiffOn_const.add contMDiffOn_snd)
      (fun z hz ↦ congrArg (fun p : M × ℝ ↦ p.2) (hrf z hz))
  refine ⟨C, hm, ?_, ?_, ?_, ?_⟩
  · intro x
    rcases hcover (intervalCompletionInclusion u a b x) with hx | hx | hx
    · exact heS.1.contMDiffAt (e.open_source.mem_nhds hx)
    · rw [hlT] at hx
      exact hincl₀.contMDiffAt (c₀.open_target.mem_nhds hx)
    · rw [hrT] at hx
      exact hincl₁.contMDiffAt (c₁.open_target.mem_nhds hx)
  · intro x
    rcases hcover (intervalCompletionInclusion u a b x) with hx | hx | hx
    · have he : e.MDifferentiable I 𝓘(ℝ, E) :=
        ⟨heS.1.mdifferentiableOn (by simp), heS.2.mdifferentiableOn (by simp)⟩
      exact he.mfderiv_injective hx
    · rw [hlT] at hx
      apply injective_inclusion_in_collar (σ := 1) one_ne_zero c₀ l hlT hli _ hlS.2 hincl₀ hx
      intro z hz
      simpa only [one_mul] using hh₀ z hz
    · rw [hrT] at hx
      apply injective_inclusion_in_collar (σ := -1) (by norm_num) c₁ r hrT hri _ hrS.2 hincl₁ hx
      intro z hz
      simpa only [neg_one_mul, ← sub_eq_add_neg] using hh₁ z hz
  · intro q
    rcases hcover q with hq | hq | hq
    · exact hf₀.contMDiffAt (e.open_target.mem_nhds hq)
    · exact hfl.contMDiffAt (l.open_target.mem_nhds hq)
    · exact hfr.contMDiffAt (r.open_target.mem_nhds hq)
  · intro q
    rcases hcover q with hq | hq | hq
    · exact regular_function_in_patch e heS.1 hf₀ (fun x _ ↦ hreg x) (fun _ _ ↦ rfl) hq
    · exact regular_function_in_patch l hlS.1 hfl
        (fun z _ ↦ regular_signed_height hI.boundaryI a z)
        (fun z hz ↦ congrArg (fun p : M × ℝ ↦ p.2) (hlf z hz)) hq
    · exact regular_function_in_patch r hrS.1 hfr
        (fun z _ ↦ regular_signed_height hI.boundaryI b z)
        (fun z hz ↦ congrArg (fun p : M × ℝ ↦ p.2) (hrf z hz)) hq

end DifferentialGeometry.Topology.Ehresmann

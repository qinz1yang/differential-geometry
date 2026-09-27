import DifferentialGeometry.Topology.Double.ClosedCover
import DifferentialGeometry.Topology.Double.SeamPatch
import DifferentialGeometry.Topology.Manifold.BoundaryTransitionFlow
import DifferentialGeometry.Topology.VectorField.Pushforward

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology TopologicalSpace Bundle
open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Topology

private def partialDiffeomorphOfOpenPartialHomeomorph
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    (e : OpenPartialHomeomorph M₁ M₂) (h₁ : ContMDiffOn I₁ I₂ ∞ e e.source)
    (h₂ : ContMDiffOn I₂ I₁ ∞ e.symm e.target) :
    PartialDiffeomorph I₁ I₂ M₁ M₂ ∞ where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := h₁
  contMDiffOn_invFun := h₂

theorem frontier_range_doublePositive_subset
    {X : Type*} [TopologicalSpace X] (B : Set X) (r : C(X, ℝ))
    (hr : ∀ b : B, r b.val = 0) (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x) :
    frontier (range (doublePositive B)) ⊆ {z | doubleHeight B r hr z = 0} := by
  intro z hzfront
  by_contra hne
  have hS : range (doublePositive B) = {z | 0 ≤ doubleHeight B r hr z} :=
    range_doublePositive B r hr hn hz
  have hfront : z ∈ frontier {w | 0 ≤ doubleHeight B r hr w} := hS ▸ hzfront
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hsub : {w | doubleHeight B r hr w < 0} ⊆ {w | 0 ≤ doubleHeight B r hr w}ᶜ :=
      fun w hw => not_le.mpr (show doubleHeight B r hr w < 0 from hw)
    have hopen : IsOpen {w | doubleHeight B r hr w < 0} :=
      isOpen_lt (doubleHeight B r hr).continuous continuous_const
    have hzmem : z ∈ interior {w | 0 ≤ doubleHeight B r hr w}ᶜ :=
      (interior_mono hsub) (by rw [hopen.interior_eq]; exact hlt)
    have hfr : z ∈ frontier ({w | 0 ≤ doubleHeight B r hr w}ᶜ) := by
      rw [frontier_compl]; exact hfront
    exact (Set.disjoint_left.mp disjoint_interior_frontier hzmem) hfr
  · have hsub : {w | 0 < doubleHeight B r hr w} ⊆ {w | 0 ≤ doubleHeight B r hr w} :=
      fun w hw => le_of_lt (show 0 < doubleHeight B r hr w from hw)
    have hopen : IsOpen {w | 0 < doubleHeight B r hr w} :=
      isOpen_lt continuous_const (doubleHeight B r hr).continuous
    have hzmem : z ∈ interior {w | 0 ≤ doubleHeight B r hr w} :=
      (interior_mono hsub) (by rw [hopen.interior_eq]; exact hgt)
    exact (Set.disjoint_left.mp disjoint_interior_frontier hzmem) hfront

private theorem image_eq_self_of_mem_iff {α : Type*} {f g : α → α}
    (hgf : Function.LeftInverse f g) {S : Set α} (h : ∀ x, f x ∈ S ↔ x ∈ S) :
    f '' S = S := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact (h x).mpr hx
  · intro y hy
    exact ⟨g y, (h (g y)).mp (by rw [hgf y]; exact hy), hgf y⟩

theorem exists_doublePositive_frontier_chart
    {M E H F G : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    (B : Set M) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [ChartedSpace G B] (J : ModelWithCorners ℝ F G)
    [IsManifold J ∞ B] [BoundarylessManifold J B]
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0) (hz : ∀ x, r x = 0 → x ∈ B)
    (hn : ∀ x, 0 ≤ r x)
    {a : ℝ} (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val)
    (hsmall : ∀ x, r x ≤ a → x ∈ range c) (hc : IsEmbedding c) (ha : 0 < a)
    [ChartedSpace E (Double B)] [IsManifold 𝓘(ℝ, E) ∞ (Double B)] [T2Space (Double B)]
    (hseam : ∀ b : B,
      ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a} ∧
      ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
        {z | |doubleHeight B r hr z| < a})
    (b₀ : B)
    (X : (z : Double B) → TangentSpace 𝓘(ℝ, E) z)
    (htan : ∀ q : B × ℝ, q.2 = 0 →
      ((mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
          (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀) q).inverse
        (X (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q))).2 = 0) :
    ∀ p ∈ frontier (range (doublePositive B)),
      ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) (Double B) (ℝ × F) ∞,
        p ∈ e.source ∧
        e.toOpenPartialHomeomorph.IsImage (range (doublePositive B)) {z | 0 ≤ z.1} ∧
        ∀ x ∈ frontier (range (doublePositive B)) ∩ e.source,
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) e x (X x)).1 = 0 := by
  intro p hp
  have hp0 : doubleHeight B r hr p = 0 :=
    frontier_range_doublePositive_subset B r hr hz hn hp
  have hpa : |doubleHeight B r hr p| < a := by rw [hp0, abs_zero]; exact ha
  let S := doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀
  have hS₁ : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ S S.source := by
    rw [doubleSeamPatch_source]; exact (hseam b₀).1
  have hS₂ : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞ S.symm S.target := by
    rw [doubleSeamPatch_target]; exact (hseam b₀).2
  let e₁ : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (B × ℝ) (Double B) ∞ :=
    partialDiffeomorphOfOpenPartialHomeomorph (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) S hS₁ hS₂
  have hpt : p ∈ e₁.target := by
    change p ∈ S.target
    rw [doubleSeamPatch_target]
    exact hpa
  have hq₀src : e₁.symm p ∈ e₁.source := e₁.map_target hpt
  have hq₀a : |(e₁.symm p).2| < a := by
    have h := hq₀src
    change e₁.symm p ∈ S.source at h
    rwa [doubleSeamPatch_source] at h
  have hq₀zero : (e₁.symm p).2 = 0 := by
    have hh : (S.symm p).2 = doubleHeight B r hr p :=
      doubleSeamPatch_symm_height B r hr hz hn c hheight hsmall hc ha b₀ hpa
    rw [hp0] at hh
    exact hh
  let χ : PartialEquiv B F := extChartAt J (e₁.symm p).1
  have hχ : ContMDiffOn J 𝓘(ℝ, F) ∞ (fun b : B => χ b) χ.source := by
    change ContMDiffOn J 𝓘(ℝ, F) ∞
      (fun b : B => (extChartAt J (e₁.symm p).1) b) (extChartAt J (e₁.symm p).1).source
    rw [extChartAt_source]
    exact contMDiffOn_extChartAt (I := J) (x := (e₁.symm p).1) (n := ∞)
  let e₂ : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × F) (B × ℝ)
      (ℝ × F) ∞ :=
    { toFun := fun q => (q.2, χ q.1)
      invFun := fun y => (χ.symm y.2, y.1)
      source := {q | q.1 ∈ χ.source ∧ χ q.1 ∈ interior χ.target}
      target := {y | y.2 ∈ interior χ.target}
      map_source' := fun q hq => hq.2
      map_target' := fun y hy => ⟨χ.map_target (show y.2 ∈ χ.target from
          interior_subset (show y.2 ∈ interior χ.target from hy)), by
        rw [χ.right_inv (show y.2 ∈ χ.target from
          interior_subset (show y.2 ∈ interior χ.target from hy))]
        exact hy⟩
      left_inv' := fun q hq => Prod.ext (χ.left_inv hq.1) rfl
      right_inv' := fun y hy => Prod.ext rfl (χ.right_inv (show y.2 ∈ χ.target from
        interior_subset (show y.2 ∈ interior χ.target from hy)))
      open_source := (hχ.continuousOn.isOpen_inter_preimage
        (isOpen_extChartAt_source (I := J) (e₁.symm p).1) isOpen_interior).preimage continuous_fst
      open_target := isOpen_interior.preimage continuous_snd
      contMDiffOn_toFun := by
        have h₁ : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
            (fun q : B × ℝ => q.2) {q | q.1 ∈ χ.source ∧ χ q.1 ∈ interior χ.target} :=
          contMDiffOn_snd (I := J) (J := 𝓘(ℝ, ℝ))
        have h₂ : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞
            (fun q : B × ℝ => χ q.1)
            {q | q.1 ∈ χ.source ∧ χ q.1 ∈ interior χ.target} :=
          hχ.comp (contMDiffOn_fst (I := J) (J := 𝓘(ℝ, ℝ))) (fun q hq => hq.1)
        exact h₁.prodMk_space h₂
      contMDiffOn_invFun := by
        have h₁ : ContMDiffOn 𝓘(ℝ, ℝ × F) 𝓘(ℝ, ℝ) ∞
            (fun y : ℝ × F => y.1) {y | y.2 ∈ interior χ.target} :=
          (ContinuousLinearMap.fst ℝ ℝ F).contMDiff.contMDiffOn
        have h₂ : ContMDiffOn 𝓘(ℝ, ℝ × F) J ∞
            (fun y : ℝ × F => χ.symm y.2) {y | y.2 ∈ interior χ.target} :=
          (contMDiffOn_extChartAt_symm (I := J) (e₁.symm p).1).comp
            ((ContinuousLinearMap.snd ℝ ℝ F).contMDiff.contMDiffOn)
            (fun y hy => (interior_subset : interior χ.target ⊆ χ.target)
              (show y.2 ∈ interior χ.target from hy))
        exact h₂.prodMk h₁ }
  refine ⟨e₁.symm.trans e₂, ?_, ?_, ?_⟩
  · refine ⟨hpt, ?_⟩
    exact ⟨mem_extChartAt_source _,
      (ModelWithCorners.isInteriorPoint_iff).mp
        (BoundarylessManifold.isInteriorPoint (I := J) (x := (e₁.symm p).1))⟩
  · intro x hx
    have hxt : x ∈ e₁.target := hx.1
    have hSx : |doubleHeight B r hr x| < a := by
      have h := hxt
      change x ∈ S.target at h
      rwa [doubleSeamPatch_target] at h
    have hdx : (e₁.symm x).2 = doubleHeight B r hr x :=
      doubleSeamPatch_symm_height B r hr hz hn c hheight hsmall hc ha b₀ hSx
    have hval : ((e₁.symm.trans e₂) x).1 = doubleHeight B r hr x := by
      rw [show ((e₁.symm.trans e₂) x).1 = (e₁.symm x).2 from rfl, hdx]
    rw [show range (doublePositive B) = {z | 0 ≤ doubleHeight B r hr z} from
      range_doublePositive B r hr hn hz]
    change 0 ≤ ((e₁.symm.trans e₂) x).1 ↔ 0 ≤ doubleHeight B r hr x
    rw [hval]
  · intro x hx
    have hxsrc : x ∈ (e₁.symm.trans e₂).source := hx.2
    have hxt : x ∈ e₁.target := by
      have h := hxsrc.1
      change x ∈ e₁.symm.source at h
      exact h
    have hx0 : (e₁.symm x).2 = 0 := by
      have hSx : |doubleHeight B r hr x| < a := by
        rw [show doubleHeight B r hr x = 0 from
          frontier_range_doublePositive_subset B r hr hz hn hx.1, abs_zero]
        exact ha
      have h : (S.symm x).2 = doubleHeight B r hr x :=
        doubleSeamPatch_symm_height B r hr hz hn c hheight hsmall hc ha b₀ hSx
      exact h.trans (frontier_range_doublePositive_subset B r hr hz hn hx.1)
    have hev : (fun z : Double B => ((e₁.symm.trans e₂) z).1) =ᶠ[𝓝 x]
        (fun z : Double B => (e₁.symm z).2) := by
      filter_upwards [((e₁.symm.trans e₂).open_source.mem_nhds hxsrc)] with z _
      rfl
    have hcd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F)
        ((e₁.symm.trans e₂) : Double B → ℝ × F) x :=
      (e₁.symm.trans e₂).mdifferentiableAt (by norm_num) hxsrc
    have hfd : MDifferentiableAt 𝓘(ℝ, ℝ × F) 𝓘(ℝ, ℝ)
        (ContinuousLinearMap.fst ℝ ℝ F) ((e₁.symm.trans e₂) x) :=
      (ContinuousLinearMap.fst ℝ ℝ F).mdifferentiableAt
    have hcomp := mfderiv_comp (x := x) (g := (ContinuousLinearMap.fst ℝ ℝ F))
      (f := ((e₁.symm.trans e₂) : Double B → ℝ × F)) hfd hcd
    have hclm : mfderiv 𝓘(ℝ, ℝ × F) 𝓘(ℝ, ℝ) (ContinuousLinearMap.fst ℝ ℝ F)
        ((e₁.symm.trans e₂) x) = ContinuousLinearMap.fst ℝ ℝ F := by
      rw [mfderiv_eq_fderiv]
      exact ContinuousLinearMap.fderiv (ContinuousLinearMap.fst ℝ ℝ F)
    have hfirst : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) (e₁.symm.trans e₂) x (X x)).1 =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
          (fun z : Double B => ((e₁.symm.trans e₂) z).1) x (X x) := by
      rw [show (fun z : Double B => ((e₁.symm.trans e₂) z).1) =
          (ContinuousLinearMap.fst ℝ ℝ F) ∘
            ((e₁.symm.trans e₂) : Double B → ℝ × F) from rfl,
        hcomp, hclm]
      rfl
    have hmfsymm : mfderiv 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) e₁.symm x =
        (mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) e₁ (e₁.symm x)).inverse := by
      have h := DifferentialGeometry.VectorField.inverse_mfderiv_partialDiffeomorph e₁
        (by norm_num) (e₁.map_target hxt)
      rw [e₁.right_inv hxt] at h
      exact h.symm
    have hsecond : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z : Double B => (e₁.symm z).2) x (X x)
        = ((mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) e₁ (e₁.symm x)).inverse (X x)).2 := by
      have hsnd : mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd (e₁.symm x) =
          ContinuousLinearMap.snd ℝ F ℝ := mfderiv_snd
      have hcomp2 := mfderiv_comp (x := x) (g := Prod.snd)
        (f := ((e₁.symm) : Double B → B × ℝ))
        ((contMDiff_snd (I := J) (J := 𝓘(ℝ, ℝ))).mdifferentiableAt
          (by norm_num : (∞ : ℕ∞ω) ≠ 0))
        (e₁.symm.mdifferentiableAt (by norm_num : (∞ : ℕ∞ω) ≠ 0) hxt)
      have h1 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z : Double B => (e₁.symm z).2) x (X x) =
          (mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd (e₁.symm x))
            ((mfderiv 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) e₁.symm x) (X x)) := by
        change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
            (Prod.snd ∘ ((e₁.symm) : Double B → B × ℝ)) x (X x) = _
        rw [hcomp2]
        rfl
      rw [h1, hsnd, hmfsymm]
      rfl
    have hlast : ((mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) e₁ (e₁.symm x)).inverse (X x)).2
        = 0 := by
      have hxeq : S (e₁.symm x) = x := e₁.right_inv hxt
      have hX : X x = X (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ (e₁.symm x)) :=
        (congrArg X hxeq).symm
      have hA : mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) e₁ (e₁.symm x) =
          mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
            (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀) (e₁.symm x) := rfl
      rw [hA, hX]
      exact htan (e₁.symm x) hx0
    rw [hfirst]
    rw [hev.mfderiv_eq]
    exact hsecond.trans hlast

theorem compactSupportFlow_doublePositive_mem_iff
    {M E H F G : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    (B : Set M) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [ChartedSpace G B] (J : ModelWithCorners ℝ F G)
    [IsManifold J ∞ B] [BoundarylessManifold J B]
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0) (hz : ∀ x, r x = 0 → x ∈ B)
    (hn : ∀ x, 0 ≤ r x)
    {a : ℝ} (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val)
    (hsmall : ∀ x, r x ≤ a → x ∈ range c) (hc : IsEmbedding c) (ha : 0 < a)
    [ChartedSpace E (Double B)] [IsManifold 𝓘(ℝ, E) ∞ (Double B)] [T2Space (Double B)]
    (hseam : ∀ b : B,
      ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a} ∧
      ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
        {z | |doubleHeight B r hr z| < a})
    (b₀ : B)
    (X : (z : Double B) → TangentSpace 𝓘(ℝ, E) z)
    (hX : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun z => (⟨z, X z⟩ : TangentBundle 𝓘(ℝ, E) (Double B))))
    (hsupp : IsCompact (tsupport X))
    (htan : ∀ q : B × ℝ, q.2 = 0 →
      ((mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
          (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀) q).inverse
        (X (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q))).2 = 0) :
    let Φ := Diffeomorph.compactSupportFlow X hX hsupp
    ∀ (t : ℝ) (x : Double B),
      (Φ t x ∈ range (doublePositive B) ↔ x ∈ range (doublePositive B)) ∧
      ((Φ t).symm x ∈ range (doublePositive B) ↔ x ∈ range (doublePositive B)) := by
  intro Φ t x
  have hcharts : ∀ p ∈ frontier (range (doublePositive B)), X p ≠ 0 →
      ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) (Double B) (ℝ × F) ∞,
        p ∈ e.source ∧
        e.toOpenPartialHomeomorph.IsImage (range (doublePositive B)) {z | 0 ≤ z.1} ∧
        ∀ y ∈ frontier (range (doublePositive B)) ∩ e.source,
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) e y (X y)).1 = 0 :=
    fun p hp _ => exists_doublePositive_frontier_chart I B J r hr hz hn c hheight hsmall hc ha
      hseam b₀ X htan p hp
  have h := Diffeomorph.compactSupportFlow_mem_iff_of_boundary_tangent X hX hsupp
    (range (doublePositive B)) hcharts
  have h' := h t x
  exact ⟨h'.2.1, h'.2.2.2⟩

theorem compactSupportFlow_doublePositive_image_eq
    {M E H F G : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    (B : Set M) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [ChartedSpace G B] (J : ModelWithCorners ℝ F G)
    [IsManifold J ∞ B] [BoundarylessManifold J B]
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0) (hz : ∀ x, r x = 0 → x ∈ B)
    (hn : ∀ x, 0 ≤ r x)
    {a : ℝ} (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val)
    (hsmall : ∀ x, r x ≤ a → x ∈ range c) (hc : IsEmbedding c) (ha : 0 < a)
    [ChartedSpace E (Double B)] [IsManifold 𝓘(ℝ, E) ∞ (Double B)] [T2Space (Double B)]
    (hseam : ∀ b : B,
      ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a} ∧
      ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
        {z | |doubleHeight B r hr z| < a})
    (b₀ : B)
    (X : (z : Double B) → TangentSpace 𝓘(ℝ, E) z)
    (hX : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun z => (⟨z, X z⟩ : TangentBundle 𝓘(ℝ, E) (Double B))))
    (hsupp : IsCompact (tsupport X))
    (htan : ∀ q : B × ℝ, q.2 = 0 →
      ((mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
          (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀) q).inverse
        (X (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q))).2 = 0) :
    let Φ := Diffeomorph.compactSupportFlow X hX hsupp
    ∀ t : ℝ, Φ t '' range (doublePositive B) = range (doublePositive B) ∧
      (Φ t).symm '' range (doublePositive B) = range (doublePositive B) := by
  intro Φ t
  have hmem := compactSupportFlow_doublePositive_mem_iff I B J r hr hz hn c hheight hsmall hc ha
    hseam b₀ X hX hsupp htan
  have h' := hmem t
  exact ⟨image_eq_self_of_mem_iff (f := (Φ t : Double B → Double B))
      (g := ((Φ t).symm : Double B → Double B))
      (fun y => (Φ t).apply_symm_apply y) (fun z => (h' z).1),
    image_eq_self_of_mem_iff (f := ((Φ t).symm : Double B → Double B))
      (g := (Φ t : Double B → Double B))
      (fun y => (Φ t).symm_apply_apply y) (fun z => (h' z).2)⟩

end DifferentialGeometry.Topology

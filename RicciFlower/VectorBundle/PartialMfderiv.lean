import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.VectorField

/-!
# Partial derivative along the first factor of a product manifold

Auxiliary lemma for realized time-dependent calculus: the partial derivative in
the ℝ-factor of a jointly-`C^∞` real-valued function on `ℝ × M` is itself
jointly `C^∞`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Topology Manifold ContDiff

namespace RicciFlower

/-- The action of a concrete tangent vector field on a scalar function.

For `X : (x : M) -> TangentSpace I x`, `vderiv f X x` is `df_x (X_x)`.
This is the concrete manifold analogue of viewing a vector field as a
derivation on scalar functions. -/
noncomputable abbrev vderiv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> 𝕜) (X : (x : M) -> TangentSpace I x) : M -> 𝕜 :=
  fun x => extDerivFun (I := I) f x (X x)

@[simp] theorem vderiv_apply
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> 𝕜) (X : (x : M) -> TangentSpace I x) (x : M) :
    vderiv (I := I) f X x = extDerivFun (I := I) f x (X x) := by
  rfl

/- The concrete manifold Lie bracket acts on scalar functions by the
commutator of the vector-field action:
`[X,Y] f = X (Y f) - Y (X f)`.

This is the local RicciFlower form of the standard chart-transfer identity
`VectorField.fderivWithin_apply_lieBracket`. -/
set_option maxHeartbeats 250000 in
set_option backward.isDefEq.respectTransparency false in
theorem vderiv_mlieBracket
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    (X Y : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Y) x)
    (hf : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) f x) :
    vderiv (I := I) f (VectorField.mlieBracket I X Y) x =
      vderiv (I := I) (vderiv (I := I) f Y) X x -
        vderiv (I := I) (vderiv (I := I) f X) Y x := by
  simp only [vderiv, extDerivFun, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk,
    LinearEquiv.coe_mk]
  let φ := extChartAt I x
  let y₀ : E := φ x
  let s : Set E := Set.range I
  let g : E -> Real := f ∘ φ.symm
  let V' : E -> E := VectorField.mpullbackWithin 𝓘(Real, E) I φ.symm X s
  let W' : E -> E := VectorField.mpullbackWithin 𝓘(Real, E) I φ.symm Y s
  letI : NormedAddCommGroup (TangentSpace I x) := by
    change NormedAddCommGroup E
    infer_instance
  letI : NormedSpace Real (TangentSpace I x) := by
    change NormedSpace Real E
    infer_instance
  letI : NormedAddCommGroup (TangentSpace 𝓘(Real, E) y₀) := by
    change NormedAddCommGroup E
    infer_instance
  letI : NormedSpace Real (TangentSpace 𝓘(Real, E) y₀) := by
    change NormedSpace Real E
    infer_instance
  have hxmem : x ∈ φ.source := by
    simp [φ]
  have hy₀tgt : y₀ ∈ φ.target := by
    simpa [y₀] using φ.map_source hxmem
  have hy₀s : y₀ ∈ s := by
    simp [s, φ, y₀]
  have huniq : UniqueDiffOn Real s := by
    simpa [s] using I.uniqueDiffOn
  have hy₀closure : y₀ ∈ closure (interior s) := by
    exact I.range_subset_closure_interior (by simpa [s] using hy₀s)
  have hn_ne_top : (minSmoothness Real 2 : WithTop ℕ∞) ≠ ∞ := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_num
  have hn_ne_zero : (minSmoothness Real 2 : WithTop ℕ∞) ≠ 0 := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_num
  have h_one_add_le :
      (1 : WithTop ℕ∞) + 1 ≤ (minSmoothness Real 2 : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_num
  have h_two_le : minSmoothness Real 2 ≤ (minSmoothness Real 2 : WithTop ℕ∞) := le_rfl
  have mfderiv_eq :
      ∀ (h : M -> Real), MDifferentiableAt I 𝓘(Real, Real) h x ->
        mfderiv I 𝓘(Real, Real) h x =
          fderivWithin Real (h ∘ φ.symm) s y₀ := by
    intro h hh
    simp only [mfderiv, if_pos hh]
    congr 1
  have hf_diff : MDifferentiableAt I 𝓘(Real, Real) f x :=
    hf.mdifferentiableAt hn_ne_zero
  rw [mfderiv_eq f hf_diff]
  have bracket_eq :
      VectorField.mlieBracket I X Y x =
        VectorField.lieBracketWithin Real V' W' s y₀ := by
    have h1 : VectorField.mlieBracket I X Y x =
        (mfderiv I 𝓘(Real, E) φ x).inverse
          (VectorField.lieBracketWithin Real V' W'
            (φ.symm ⁻¹' Set.univ ∩ s) y₀) := by
      exact (VectorField.mlieBracketWithin_apply (I := I)
        (V := X) (W := Y) (s := Set.univ) (x₀ := x))
    rw [h1, mfderiv_extChartAt_self (I := I)]
    erw [ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply]
    simp only [Set.preimage_univ, Set.univ_inter]
  rw [bracket_eq]
  have hV'_y₀ : V' y₀ = X x := by
    simp only [V', VectorField.mpullbackWithin_apply, y₀]
    rw [φ.left_inv hxmem]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x) (X x)
  have hW'_y₀ : W' y₀ = Y x := by
    simp only [W', VectorField.mpullbackWithin_apply, y₀]
    rw [φ.left_inv hxmem]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x) (Y x)
  have hg_smooth : ContDiffWithinAt Real (minSmoothness Real 2) g s y₀ := by
    simpa [g, s, φ, y₀] using (contMDiffAt_iff.mp hf).2
  have hX_mdiff : MDifferentiableWithinAt I (I.prod 𝓘(Real, E))
      (fun x => (X x : TangentBundle I M)) Set.univ x := by
    exact (hX.mdifferentiableAt hn_ne_zero).mdifferentiableWithinAt
  have hY_mdiff : MDifferentiableWithinAt I (I.prod 𝓘(Real, E))
      (fun x => (Y x : TangentBundle I M)) Set.univ x := by
    exact (hY.mdifferentiableAt hn_ne_zero).mdifferentiableWithinAt
  have hV'_diff : DifferentiableWithinAt Real V' s y₀ := by
    have h := hX_mdiff.differentiableWithinAt_mpullbackWithin_vectorField (I := I)
    simpa [V', s, y₀] using h
  have hW'_diff : DifferentiableWithinAt Real W' s y₀ := by
    have h := hY_mdiff.differentiableWithinAt_mpullbackWithin_vectorField (I := I)
    simpa [W', s, y₀] using h
  have hg_event :
      ∀ᶠ y in 𝓝[s] y₀,
        ContDiffWithinAt Real (minSmoothness Real 2) g s y := by
    simpa [Set.insert_eq_of_mem hy₀s] using hg_smooth.eventually hn_ne_top
  have mfderiv_fderivWithin_chain :
      ∀ z ∈ φ.source, DifferentiableWithinAt Real g s (φ z) ->
        mfderiv I 𝓘(Real, Real) f z =
          (fderivWithin Real g s (φ z)).comp (mfderiv I 𝓘(Real, E) φ z) := by
    intro z hz hg_diffWithin
    have hφ_open : IsOpen φ.source := by
      simpa [φ] using isOpen_extChartAt_source (I := I) x
    have hz_chart : z ∈ (chartAt H x).source := by
      simpa [φ, extChartAt_source] using hz
    have hφz_tgt : φ z ∈ φ.target := φ.map_source hz
    have hf_eq : f =ᶠ[𝓝 z] g ∘ φ := by
      filter_upwards [hφ_open.mem_nhds hz] with w hw
      simp [g, φ.left_inv hw]
    rw [hf_eq.mfderiv_eq]
    have hφ_diff : MDifferentiableAt I 𝓘(Real, E) φ z := by
      simpa [φ] using mdifferentiableAt_extChartAt (I := I) (x := x) hz_chart
    have hφ_diffWithin : MDifferentiableWithinAt I 𝓘(Real, E) φ φ.source z :=
      hφ_diff.mdifferentiableWithinAt
    have hg_mdiffWithin : MDifferentiableWithinAt 𝓘(Real, E) 𝓘(Real, Real) g s (φ z) :=
      mdifferentiableWithinAt_iff_differentiableWithinAt.mpr hg_diffWithin
    have h_maps : φ.source ⊆ φ ⁻¹' s := fun w hw =>
      extChartAt_target_subset_range (I := I) x (by simpa [φ] using φ.map_source hw)
    have hUniq : UniqueMDiffWithinAt I φ.source z :=
      hφ_open.uniqueMDiffWithinAt hz
    have hchain := mfderivWithin_comp z hg_mdiffWithin hφ_diffWithin h_maps hUniq
    rw [mfderivWithin_eq_mfderiv hUniq hφ_diff] at hchain
    have hgφ_diff : MDifferentiableAt I 𝓘(Real, Real) (g ∘ φ) z := by
      have hcomp : MDifferentiableWithinAt I 𝓘(Real, Real) (g ∘ φ) φ.source z :=
        hg_mdiffWithin.comp z hφ_diffWithin h_maps
      exact hcomp.mdifferentiableAt (hφ_open.mem_nhds hz)
    rw [mfderivWithin_eq_mfderiv hUniq hgφ_diff] at hchain
    rw [mfderivWithin_eq_fderivWithin] at hchain
    exact hchain
  have W'_eq : ∀ y ∈ φ.target,
      W' y = mfderiv I 𝓘(Real, E) φ (φ.symm y) (Y (φ.symm y)) := by
    intro y hy
    simp only [W', VectorField.mpullbackWithin_apply]
    congr 1
    exact ContinuousLinearMap.inverse_eq
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) hy)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) hy)
  have V'_eq : ∀ y ∈ φ.target,
      V' y = mfderiv I 𝓘(Real, E) φ (φ.symm y) (X (φ.symm y)) := by
    intro y hy
    simp only [V', VectorField.mpullbackWithin_apply]
    congr 1
    exact ContinuousLinearMap.inverse_eq
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) hy)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) hy)
  have hYf_eq : ((fun p : M => mfderiv I 𝓘(Real, Real) f p (Y p)) ∘ φ.symm)
      =ᶠ[𝓝[s] y₀] (fun y => fderivWithin Real g s y (W' y)) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (I := I) hy₀tgt,
      hg_event] with y hy hgy
    have hy_src : φ.symm y ∈ φ.source := φ.map_target hy
    have hgy_diff :
        DifferentiableWithinAt Real g s (φ (φ.symm y)) := by
      simpa [φ.right_inv hy] using hgy.differentiableWithinAt hn_ne_zero
    have h1 := mfderiv_fderivWithin_chain (φ.symm y) hy_src hgy_diff
    have h2 : mfderiv I 𝓘(Real, Real) f (φ.symm y) (Y (φ.symm y)) =
        fderivWithin Real g s (φ (φ.symm y))
          (mfderiv I 𝓘(Real, E) φ (φ.symm y) (Y (φ.symm y))) := by
      rw [h1]
      rfl
    simp only [Function.comp_def]
    rw [h2, φ.right_inv hy]
    congr 1
    exact (W'_eq y hy).symm
  have hXf_eq : ((fun p : M => mfderiv I 𝓘(Real, Real) f p (X p)) ∘ φ.symm)
      =ᶠ[𝓝[s] y₀] (fun y => fderivWithin Real g s y (V' y)) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (I := I) hy₀tgt,
      hg_event] with y hy hgy
    have hy_src : φ.symm y ∈ φ.source := φ.map_target hy
    have hgy_diff :
        DifferentiableWithinAt Real g s (φ (φ.symm y)) := by
      simpa [φ.right_inv hy] using hgy.differentiableWithinAt hn_ne_zero
    have h1 := mfderiv_fderivWithin_chain (φ.symm y) hy_src hgy_diff
    have h2 : mfderiv I 𝓘(Real, Real) f (φ.symm y) (X (φ.symm y)) =
        fderivWithin Real g s (φ (φ.symm y))
          (mfderiv I 𝓘(Real, E) φ (φ.symm y) (X (φ.symm y))) := by
      rw [h1]
      rfl
    simp only [Function.comp_def]
    rw [h2, φ.right_inv hy]
    congr 1
    exact (V'_eq y hy).symm
  have hYf_eq_v : ((vderiv (I := I) f Y) ∘ φ.symm)
      =ᶠ[𝓝[s] y₀] (fun y => fderivWithin Real g s y (W' y)) := by
    filter_upwards [hYf_eq] with y hy
    simpa [vderiv, extDerivFun, NormedSpace.fromTangentSpace] using hy
  have hXf_eq_v : ((vderiv (I := I) f X) ∘ φ.symm)
      =ᶠ[𝓝[s] y₀] (fun y => fderivWithin Real g s y (V' y)) := by
    filter_upwards [hXf_eq] with y hy
    simpa [vderiv, extDerivFun, NormedSpace.fromTangentSpace] using hy
  have hmodelY_diff :
      DifferentiableWithinAt Real (fun y => fderivWithin Real g s y (W' y)) s y₀ := by
    have hderiv :
        DifferentiableWithinAt Real (fderivWithin Real g s) s y₀ := by
      exact (hg_smooth.fderivWithin_right huniq h_one_add_le hy₀s).differentiableWithinAt
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    exact hderiv.clm_apply hW'_diff
  have hmodelX_diff :
      DifferentiableWithinAt Real (fun y => fderivWithin Real g s y (V' y)) s y₀ := by
    have hderiv :
        DifferentiableWithinAt Real (fderivWithin Real g s) s y₀ := by
      exact (hg_smooth.fderivWithin_right huniq h_one_add_le hy₀s).differentiableWithinAt
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    exact hderiv.clm_apply hV'_diff
  have hYf_chart_diff :
      DifferentiableWithinAt Real
        ((vderiv (I := I) f Y) ∘ φ.symm)
        s y₀ :=
    (hYf_eq_v.differentiableWithinAt_iff_of_mem hy₀s).mpr hmodelY_diff
  have hXf_chart_diff :
      DifferentiableWithinAt Real
        ((vderiv (I := I) f X) ∘ φ.symm)
        s y₀ :=
    (hXf_eq_v.differentiableWithinAt_iff_of_mem hy₀s).mpr hmodelX_diff
  have hYf_diff : MDifferentiableAt I 𝓘(Real, Real)
      (vderiv (I := I) f Y) x := by
    rw [mdifferentiableAt_iff_source_of_mem_source (I := I) (I' := 𝓘(Real, Real))
      (x := x) (x' := x) (mem_chart_source H x)]
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
    simpa [writtenInExtChartAt, extChartAt, φ, y₀, s, Function.comp_def]
      using hYf_chart_diff
  have hXf_diff : MDifferentiableAt I 𝓘(Real, Real)
      (vderiv (I := I) f X) x := by
    rw [mdifferentiableAt_iff_source_of_mem_source (I := I) (I' := 𝓘(Real, Real))
      (x := x) (x' := x) (mem_chart_source H x)]
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
    simpa [writtenInExtChartAt, extChartAt, φ, y₀, s, Function.comp_def]
      using hXf_chart_diff
  rw [mfderiv_eq _ hYf_diff, mfderiv_eq _ hXf_diff]
  have hYf_fd :
      fderivWithin Real
          ((vderiv (I := I) f Y) ∘ φ.symm)
          s y₀ =
        fderivWithin Real (fun y => fderivWithin Real g s y (W' y)) s y₀ :=
    hYf_eq_v.fderivWithin_eq (hYf_eq_v.self_of_nhdsWithin hy₀s)
  have hXf_fd :
      fderivWithin Real
          ((vderiv (I := I) f X) ∘ φ.symm)
          s y₀ =
        fderivWithin Real (fun y => fderivWithin Real g s y (V' y)) s y₀ :=
    hXf_eq_v.fderivWithin_eq (hXf_eq_v.self_of_nhdsWithin hy₀s)
  rw [hYf_fd, hXf_fd, ← hV'_y₀, ← hW'_y₀]
  exact VectorField.fderivWithin_apply_lieBracket hg_smooth h_two_le huniq
    hy₀closure hy₀s hW'_diff hV'_diff

/-- Exterior-derivative form of `vderiv_mlieBracket`. -/
theorem extDerivFun_apply_mlieBracket
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    (X Y : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Y) x)
    (hf : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) f x) :
    extDerivFun (I := I) f x (VectorField.mlieBracket I X Y x) =
      extDerivFun (I := I)
          (fun y : M => extDerivFun (I := I) f y (Y y)) x (X x) -
        extDerivFun (I := I)
          (fun y : M => extDerivFun (I := I) f y (X y)) x (Y x) := by
  exact vderiv_mlieBracket (I := I) X Y f x hX hY hf

/-- The partial derivative along the first (real) factor of a jointly smooth
real-valued function on `ℝ × M` is itself jointly smooth. -/
theorem contMDiff_partial_deriv_fst
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (F : C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; ℝ⟯) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => deriv (fun t => F (t, p.2)) p.1) := by
  -- Rewrite `deriv` as `mfderiv ... 1`, so the result follows from the smoothness
  -- of `mfderiv` applied to a jointly smooth function.
  have hrw : (fun p : ℝ × M => deriv (fun t => F (t, p.2)) p.1) =
      fun p : ℝ × M => (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t => F (t, p.2)) p.1) (1 : ℝ) := by
    funext p
    rw [mfderiv_eq_fderiv]
    exact (fderiv_apply_one_eq_deriv (f := fun t => F (t, p.2)) (x := p.1)).symm
  rw [hrw]
  -- Reduce smoothness at `∞` to smoothness at every natural level.
  rw [contMDiff_infty]
  intro n p₀
  -- The composition `(q : (ℝ × M) × ℝ) ↦ F (q.2, q.1.2)` is jointly `C^∞`.
  have harg : ContMDiff ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : (ℝ × M) × ℝ => (q.2, q.1.2)) :=
    ContMDiff.prodMk contMDiff_snd contMDiff_fst.snd
  have hF : ContMDiff ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : (ℝ × M) × ℝ => F (q.2, q.1.2)) :=
    F.contMDiff.comp harg
  -- Apply `ContMDiffAt.mfderiv_apply` with `m = n`, `n' = n + 1` (inside `WithTop ℕ∞`).
  have h_apply :=
    ContMDiffAt.mfderiv_apply
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (f := fun (p : ℝ × M) (t : ℝ) => F (t, p.2))
      (g := fun p : ℝ × M => p.1)
      (g₁ := fun p : ℝ × M => p)
      (g₂ := fun _ : ℝ × M => (1 : ℝ))
      (x₀ := p₀)
      (m := (n : WithTop ℕ∞))
      ((hF.of_le (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ ∞)).contMDiffAt)
      contMDiffAt_fst
      contMDiffAt_id
      contMDiffAt_const
      le_rfl
  -- The source and target models are model spaces, so `inTangentCoordinates`
  -- collapses to the raw `mfderiv`.
  simpa [inTangentCoordinates_model_space] using h_apply

/-- Exterior derivative of a scalar multiple of a scalar function.

This is a small bridge for Ricci-flow component calculations, where
`partial_t g = -2 Ric` is differentiated once more in a frozen spatial
direction. -/
theorem extDerivFun_const_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (c : ℝ) {f : M -> ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    extDerivFun (I := I) (fun y : M => c * f y) x =
      c • extDerivFun (I := I) f x := by
  change extDerivFun (I := I) (c • f) x =
    c • extDerivFun (I := I) f x
  ext v
  have hmul := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := fun _ : M => c) (g := f)
    (by exact mdifferentiableAt_const (c := c)) hf v
  simpa [extDerivFun] using hmul

/-- Smoothness of the scalar exterior derivative applied to a smooth tangent field.

This packages the `ContMDiffAt.mfderiv_apply` theorem in the concrete form used
by tensor covariant-derivative smoothness proofs. -/
theorem extDerivFun_apply_contMDiff
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (f : M -> 𝕜) (hf : ContMDiff I 𝓘(𝕜, 𝕜) ∞ f)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M -> Type _)) :
    ContMDiff I 𝓘(𝕜, 𝕜) ∞
      (fun p : M => extDerivFun (I := I) f p (X p)) := by
  rw [contMDiff_infty]
  intro n x₀
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let Xcoord : M -> E := fun p => e.continuousLinearMapAt 𝕜 p (X p)
  have hXcoord :
      ContMDiffAt I 𝓘(𝕜, E) (n : WithTop ℕ∞) Xcoord x₀ := by
    have hXTop :
        ContMDiffAt I 𝓘(𝕜, E) ∞
          (fun p : M => (e ⟨p, X p⟩).2) x₀ := by
      simpa [e] using
        (e.contMDiffAt_section_iff
          (s := fun p : M => X p)
          (x₀ := x₀)
          (by
            simp [e])).mp
          (X.contMDiff.contMDiffAt)
    refine (hXTop.of_le
      (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞)).congr_of_eventuallyEq ?_
    · filter_upwards [e.open_baseSet.mem_nhds (by
        simp [e])] with p hp
      have hcoe : ⇑(e.linearMapAt 𝕜 p) = fun z => (e ⟨p, z⟩).2 :=
        e.coe_linearMapAt_of_mem (R := 𝕜) hp
      simp [Xcoord, Bundle.Trivialization.continuousLinearMapAt_apply, hcoe]
  have hF :
      ContMDiffAt (I.prod I) 𝓘(𝕜, 𝕜) ((n : WithTop ℕ∞) + 1)
        (fun q : M × M => f q.2) (x₀, x₀) := by
    exact (hf.contMDiffAt.comp (x₀, x₀) contMDiffAt_snd).of_le
      (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ ∞)
  have hApply :=
    ContMDiffAt.mfderiv_apply
      (I := I) (I' := 𝓘(𝕜, 𝕜))
      (f := fun (_ : M) (p : M) => f p)
      (g := fun p : M => p)
      (g₁ := fun p : M => p)
      (g₂ := Xcoord)
      (x₀ := x₀)
      (m := (n : WithTop ℕ∞))
      hF contMDiffAt_id contMDiffAt_id hXcoord le_rfl
  refine hApply.congr_of_eventuallyEq ?_
  · filter_upwards [e.open_baseSet.mem_nhds (by
        simp [e])] with p hp
    have hp_src : p ∈ (chartAt H x₀).source := by
      simpa [e, TangentBundle.trivializationAt_baseSet] using hp
    have hf_src : f p ∈ (chartAt 𝕜 (f x₀)).source := by
      simp
    rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(𝕜, 𝕜))
      (f := fun p : M => p) (g := f)
      (ϕ := fun p : M => mfderiv I 𝓘(𝕜, 𝕜) f p)
      hp_src hf_src]
    have htarget :
        (tangentBundleCore 𝓘(𝕜, 𝕜) 𝕜).coordChange
          (achart 𝕜 (f p)) (achart 𝕜 (f x₀)) (f p) = (1 : 𝕜 →L[𝕜] 𝕜) := by
      simp
    have hsource :
        (tangentBundleCore I M).coordChange (achart H x₀) (achart H p) p =
          e.symmL 𝕜 p := by
      simpa [e] using
        (TangentBundle.symmL_trivializationAt_eq_core
          (𝕜 := 𝕜) (I := I) (b₀ := x₀) (b := p) hp_src).symm
    have hcancel :
        e.symmL 𝕜 p (Xcoord p) = X p := by
      exact e.symmL_continuousLinearMapAt (R := 𝕜) hp (X p)
    rw [htarget, hsource]
    change (mfderiv I 𝓘(𝕜, 𝕜) f p) (X p) =
      (mfderiv I 𝓘(𝕜, 𝕜) f p) (e.symmL 𝕜 p (Xcoord p))
    rw [hcancel]

/-- Pointwise version of `extDerivFun_apply_contMDiff`.

If a scalar function is smooth at `x₀` and `X` is a smooth tangent section,
then `p |-> extDerivFun f p (X p)` is smooth at `x₀`. -/
theorem extDerivFun_apply_contMDiffAt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {f : M -> 𝕜} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(𝕜, 𝕜) ∞ f x₀)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M -> Type _)) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) ∞
      (fun p : M => extDerivFun (I := I) f p (X p)) x₀ := by
  rw [contMDiffAt_infty]
  intro n
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let Xcoord : M -> E := fun p => e.continuousLinearMapAt 𝕜 p (X p)
  have hXcoord :
      ContMDiffAt I 𝓘(𝕜, E) (n : WithTop ℕ∞) Xcoord x₀ := by
    have hXTop :
        ContMDiffAt I 𝓘(𝕜, E) ∞
          (fun p : M => (e ⟨p, X p⟩).2) x₀ := by
      simpa [e] using
        (e.contMDiffAt_section_iff
          (s := fun p : M => X p)
          (x₀ := x₀)
          (by
            simp [e])).mp
          (X.contMDiff.contMDiffAt)
    refine (hXTop.of_le
      (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds (by
        simp [e])] with p hp
    have hcoe : ⇑(e.linearMapAt 𝕜 p) = fun z => (e ⟨p, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := 𝕜) hp
    simp [Xcoord, Bundle.Trivialization.continuousLinearMapAt_apply, hcoe]
  have hF :
      ContMDiffAt (I.prod I) 𝓘(𝕜, 𝕜) ((n : WithTop ℕ∞) + 1)
        (fun q : M × M => f q.2) (x₀, x₀) := by
    exact (hf.comp (x₀, x₀) contMDiffAt_snd).of_le
      (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ ∞)
  have hApply :=
    ContMDiffAt.mfderiv_apply
      (I := I) (I' := 𝓘(𝕜, 𝕜))
      (f := fun (_ : M) (p : M) => f p)
      (g := fun p : M => p)
      (g₁ := fun p : M => p)
      (g₂ := Xcoord)
      (x₀ := x₀)
      (m := (n : WithTop ℕ∞))
      hF contMDiffAt_id contMDiffAt_id hXcoord le_rfl
  refine hApply.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds (by
        simp [e])] with p hp
  have hp_src : p ∈ (chartAt H x₀).source := by
    simpa [e, TangentBundle.trivializationAt_baseSet] using hp
  have hf_src : f p ∈ (chartAt 𝕜 (f x₀)).source := by
    simp
  rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(𝕜, 𝕜))
    (f := fun p : M => p) (g := f)
    (ϕ := fun p : M => mfderiv I 𝓘(𝕜, 𝕜) f p)
    hp_src hf_src]
  have htarget :
      (tangentBundleCore 𝓘(𝕜, 𝕜) 𝕜).coordChange
        (achart 𝕜 (f p)) (achart 𝕜 (f x₀)) (f p) = (1 : 𝕜 →L[𝕜] 𝕜) := by
    simp
  have hsource :
      (tangentBundleCore I M).coordChange (achart H x₀) (achart H p) p =
        e.symmL 𝕜 p := by
    simpa [e] using
      (TangentBundle.symmL_trivializationAt_eq_core
        (𝕜 := 𝕜) (I := I) (b₀ := x₀) (b := p) hp_src).symm
  have hcancel :
      e.symmL 𝕜 p (Xcoord p) = X p := by
    exact e.symmL_continuousLinearMapAt (R := 𝕜) hp (X p)
  rw [htarget, hsource]
  change (mfderiv I 𝓘(𝕜, 𝕜) f p) (X p) =
    (mfderiv I 𝓘(𝕜, 𝕜) f p) (e.symmL 𝕜 p (Xcoord p))
  rw [hcancel]

section ModelMixed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem model_spatial_fderiv_eq
    (F : ℝ -> E -> ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    (s : ℝ) (x V : E) :
    (fderiv ℝ (F s) x) V =
      (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (s, x)) (0, V) := by
  let G : ℝ × E -> ℝ := fun p => F p.1 p.2
  let L : E -> ℝ × E := fun y => (s, y)
  have hG : DifferentiableAt ℝ G (s, x) :=
    hF.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0) (s, x)
  have hL : DifferentiableAt ℝ L x := by
    fun_prop
  have hcomp := fderiv_comp (𝕜 := ℝ) (x := x) (f := L) (g := G) hG hL
  have hLderiv : (fderiv ℝ L x) V = (0, V) := by
    rw [DifferentiableAt.fderiv_prodMk]
    · simp
    · fun_prop
    · fun_prop
  change (fderiv ℝ (G ∘ L) x) V = (fderiv ℝ G (s, x)) (0, V)
  rw [hcomp]
  change (fderiv ℝ G (s, x)) ((fderiv ℝ L x) V) =
    (fderiv ℝ G (s, x)) (0, V)
  rw [hLderiv]

private theorem model_hasDerivAt_fixed_snd
    (A : ℝ × E -> ℝ) (t : ℝ) (x : E)
    (hA : DifferentiableAt ℝ A (t, x)) :
    HasDerivAt (fun s : ℝ => A (s, x))
      ((fderiv ℝ A (t, x)) (1, 0)) t := by
  let L : ℝ -> ℝ × E := fun s => (s, x)
  have hL : DifferentiableAt ℝ L t := by
    fun_prop
  have hcomp := (hA.hasFDerivAt.comp t hL.hasFDerivAt).hasDerivAt
  have hLderiv : deriv L t = (1, 0) := by
    rw [deriv]
    rw [DifferentiableAt.fderiv_prodMk]
    · simp
    · fun_prop
    · fun_prop
  simpa [hLderiv] using hcomp

/-- Model-space fixed-base mixed derivative.

This is the chart-level theorem behind
`∂t (d_x F_t(V)) = d_x(∂t F_t)(V)`.  The manifold version still needs the
coordinate transport from `extDerivFun` to chart derivatives, but the analytic
mixed-partial calculation itself is discharged here. -/
theorem fixedBaseFDerivTimeDerivativeAt_of_contDiff
    (F : ℝ -> E -> ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    (t : ℝ) (x V : E) :
    HasDerivAt
      (fun s : ℝ => (fderiv ℝ (F s) x) V)
      ((fderiv ℝ
        (fun y : E =>
          (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (t, y)) (1, 0))
        x) V)
      t := by
  let G : ℝ × E -> ℝ := fun p => F p.1 p.2
  let A : ℝ × E -> ℝ := fun p => (fderiv ℝ G p) (0, V)
  let B : ℝ × E -> ℝ := fun p => (fderiv ℝ G p) (1, 0)
  have hAcont : ContDiff ℝ 1 A := by
    have hDA := hF.contDiff_fderiv_apply (m := (1 : WithTop ℕ∞)) (by norm_num)
    exact hDA.comp (contDiff_id.prodMk contDiff_const)
  have hA : DifferentiableAt ℝ A (t, x) :=
    (ContDiff.differentiable hAcont (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) (t, x)
  have h0 := model_hasDerivAt_fixed_snd (E := E) A t x hA
  have hswap :
      (fderiv ℝ A (t, x)) (1, 0) =
        (fderiv ℝ (fun y : E => B (t, y)) x) V := by
    have hlie := VectorField.fderiv_apply_lieBracket
      (𝕜 := ℝ) (E := ℝ × E) (F := ℝ)
      (f := G)
      (V := fun _ : ℝ × E => (1, 0))
      (W := fun _ : ℝ × E => (0, V))
      (x := (t, x))
      hF.contDiffAt
      (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
      (by fun_prop)
      (by fun_prop)
    have hlie' :
        (fderiv ℝ A (t, x)) (1, 0) =
          (fderiv ℝ B (t, x)) (0, V) := by
      unfold A B
      simp [VectorField.lieBracket] at hlie
      linarith
    rw [hlie']
    symm
    have hBcont : ContDiff ℝ 1 B := by
      have hDB := hF.contDiff_fderiv_apply (m := (1 : WithTop ℕ∞)) (by norm_num)
      exact hDB.comp (contDiff_id.prodMk contDiff_const)
    have hBdiff : DifferentiableAt ℝ B (t, x) :=
      (ContDiff.differentiable hBcont (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) (t, x)
    let L : E -> ℝ × E := fun y => (t, y)
    have hL : DifferentiableAt ℝ L x := by
      fun_prop
    have hcomp := fderiv_comp (𝕜 := ℝ) (x := x) (f := L) (g := B) hBdiff hL
    have hLderiv : (fderiv ℝ L x) V = (0, V) := by
      rw [DifferentiableAt.fderiv_prodMk]
      · simp
      · fun_prop
      · fun_prop
    change (fderiv ℝ (B ∘ L) x) V = (fderiv ℝ B (t, x)) (0, V)
    rw [hcomp]
    change (fderiv ℝ B (t, x)) ((fderiv ℝ L x) V) =
      (fderiv ℝ B (t, x)) (0, V)
    rw [hLderiv]
  refine (h0.congr_deriv hswap).congr_of_eventuallyEq ?_
  filter_upwards with s
  exact model_spatial_fderiv_eq (E := E) F hF s x V

theorem fixedBaseFDerivTimeDerivativeWithinAt_of_contDiff
    (F : ℝ -> E -> ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    {timeSet : Set ℝ} {t : ℝ}
    (x V : E) :
    HasDerivWithinAt
      (fun s : ℝ => (fderiv ℝ (F s) x) V)
      ((fderiv ℝ
        (fun y : E =>
          (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (t, y)) (1, 0))
        x) V)
      timeSet
      t :=
  (fixedBaseFDerivTimeDerivativeAt_of_contDiff (E := E) F hF t x V).hasDerivWithinAt

end ModelMixed

/-- For real-valued scalar functions, `extDerivFun` is just `mfderiv` applied to
the supplied tangent vector. -/
theorem extDerivFun_real_eq_mfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners Real E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> Real) (x : M) (V : TangentSpace I x) :
    extDerivFun (I := I) f x V =
      mfderiv I 𝓘(Real, Real) f x V := by
  simp [extDerivFun, NormedSpace.fromTangentSpace]

/-- If a scalar function has a chart representative near the base point, then
its exterior derivative at the base point is the model `fderiv` of that
representative. -/
theorem extDerivFun_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f : M -> Real} {φ : E -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hφ :
      writtenInExtChartAt I 𝓘(Real, Real) x f
        =ᶠ[nhds (extChartAt I x x)] φ)
    (V : TangentSpace I x) :
    extDerivFun (I := I) f x V =
      fderiv Real φ (extChartAt I x x) V := by
  let z₀ : E := extChartAt I x x
  have hrange : Set.range I ∈ nhds z₀ := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
    exact Filter.univ_mem
  calc
    extDerivFun (I := I) f x V =
        mfderiv I 𝓘(Real, Real) f x V := by
          rw [extDerivFun_real_eq_mfderiv]
    _ = fderivWithin Real
          (writtenInExtChartAt I 𝓘(Real, Real) x f)
          (Set.range I) z₀ V := by
          simpa [z₀] using congrArg (fun L => L V) hf.mfderiv
    _ = fderiv Real
          (writtenInExtChartAt I 𝓘(Real, Real) x f) z₀ V := by
          rw [fderivWithin_of_mem_nhds hrange]
    _ = fderiv Real φ z₀ V := by
          rw [hφ.fderiv_eq]

/-- Fixed-base time derivative of a spatial exterior derivative.

This is the scalar mixed-partial frontier used by the Ricci-flow Christoffel
calculation.  It deliberately freezes the spatial base point and tangent vector:
the only varying parameter is the real time parameter.

The model-space analytic core is `fixedBaseFDerivTimeDerivativeAt_of_contDiff`.
To construct this predicate from manifold-level spacetime smoothness, the
remaining chart-local lemma should rewrite `extDerivFun` in a chart as the
model derivative and then apply that model-space theorem. -/
def FixedBaseExtDerivTimeDerivativeOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (timeSet : Set ℝ) (u : Set M)
    (F Ft : ℝ -> M -> ℝ) : Prop :=
  forall (t : ℝ) (x : M), x ∈ u ->
    forall V : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => extDerivFun (I := I) (F s) x V)
        (extDerivFun (I := I) (Ft t) x V)
      timeSet
      t

/-- Regular-time version of `FixedBaseExtDerivTimeDerivativeOn`.

This is the version suited to Ricci-flow intervals: the derivative is still
within the full time carrier, but it is required only at regular evolution
times. -/
def FixedBaseExtDerivTimeDerivativeOnRegular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (timeSet regularSet : Set ℝ) (u : Set M)
    (F Ft : ℝ -> M -> ℝ) : Prop :=
  forall (t : ℝ), t ∈ regularSet ->
    forall (x : M), x ∈ u ->
      forall V : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => extDerivFun (I := I) (F s) x V)
          (extDerivFun (I := I) (Ft t) x V)
          timeSet
          t

theorem fixedBaseExtDerivTimeDerivativeOn_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet : Set ℝ} {u : Set M}
    {F Ft : ℝ -> M -> ℝ}
    (h : FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet u F Ft)
    {t : ℝ} {x : M} (hx : x ∈ u) (V : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => extDerivFun (I := I) (F s) x V)
      (extDerivFun (I := I) (Ft t) x V)
      timeSet
      t :=
  h t x hx V

/-- Pointwise use of the regular-time fixed-base mixed derivative predicate. -/
theorem fixedBaseExtDerivTimeDerivativeOnRegular_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set ℝ} {u : Set M}
    {F Ft : ℝ -> M -> ℝ}
    (h :
      FixedBaseExtDerivTimeDerivativeOnRegular
        (I := I) timeSet regularSet u F Ft)
    {t : ℝ} (ht : t ∈ regularSet) {x : M} (hx : x ∈ u)
    (V : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => extDerivFun (I := I) (F s) x V)
      (extDerivFun (I := I) (Ft t) x V)
      timeSet
      t :=
  h t ht x hx V

/-- The all-times predicate immediately implies the regular-time predicate. -/
theorem FixedBaseExtDerivTimeDerivativeOn.toRegular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set ℝ} {u : Set M}
    {F Ft : ℝ -> M -> ℝ}
    (h : FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet u F Ft) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet u F Ft := by
  intro t _ht x hx V
  exact h t x hx V

/-- Chart-level constructor for fixed-base mixed derivatives on a singleton.

The model-space scalar family `Φ` supplies the jointly `C²` chart expression.
The two eventual-equality hypotheses identify the manifold scalar families
`F` and `Ft` with `Φ` and with the time derivative of `Φ`, respectively, near
the chart center. -/
theorem fixedBaseExtDerivTimeDerivativeOn_singleton_of_chart_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet : Set Real} {x₀ : M}
    {F Ft : Real -> M -> Real} {Φ : Real -> E -> Real}
    (hΦ : ContDiff Real 2 (fun p : Real × E => Φ p.1 p.2))
    (hFdiff :
      ∀ s : Real, MDifferentiableAt I 𝓘(Real, Real) (F s) x₀)
    (hFchart :
      ∀ s : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (F s)
          =ᶠ[nhds (extChartAt I x₀ x₀)] Φ s)
    (hFtdiff :
      ∀ t : Real, MDifferentiableAt I 𝓘(Real, Real) (Ft t) x₀)
    (hFtchart :
      ∀ t : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (Ft t)
          =ᶠ[nhds (extChartAt I x₀ x₀)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0)) :
    FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet ({x₀} : Set M) F Ft := by
  intro t x hx V
  rw [Set.mem_singleton_iff] at hx
  subst x
  let z₀ : E := extChartAt I x₀ x₀
  have hmodel :=
    fixedBaseFDerivTimeDerivativeWithinAt_of_contDiff
      (E := E) Φ hΦ (timeSet := timeSet) (t := t) z₀ V
  have hleft :
      ∀ s : Real,
        extDerivFun (I := I) (F s) x₀ V =
          fderiv Real (Φ s) z₀ V := by
    intro s
    exact
      extDerivFun_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := F s) (φ := Φ s)
        (hFdiff s) (hFchart s) V
  have hright :
      extDerivFun (I := I) (Ft t) x₀ V =
        fderiv Real
          (fun y : E =>
            (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
          z₀ V := by
    exact
      extDerivFun_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := Ft t)
        (φ := fun y : E =>
          (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
        (hFtdiff t) (hFtchart t) V
  exact
    (hmodel.congr
      (fun s _hs => hleft s)
      (hleft t)).congr_deriv hright.symm

/-- Chart-level constructor for regular-time fixed-base mixed derivatives on a
singleton.  This currently reuses the all-times chart constructor and then
restricts it to regular times. -/
theorem fixedBaseExtDerivTimeDerivativeOnRegular_singleton_of_chart_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {x₀ : M}
    {F Ft : Real -> M -> Real} {Φ : Real -> E -> Real}
    (hΦ : ContDiff Real 2 (fun p : Real × E => Φ p.1 p.2))
    (hFdiff :
      ∀ s : Real, MDifferentiableAt I 𝓘(Real, Real) (F s) x₀)
    (hFchart :
      ∀ s : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (F s)
          =ᶠ[nhds (extChartAt I x₀ x₀)] Φ s)
    (hFtdiff :
      ∀ t : Real, MDifferentiableAt I 𝓘(Real, Real) (Ft t) x₀)
    (hFtchart :
      ∀ t : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (Ft t)
          =ᶠ[nhds (extChartAt I x₀ x₀)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0)) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet ({x₀} : Set M) F Ft := by
  exact
    (fixedBaseExtDerivTimeDerivativeOn_singleton_of_chart_contDiff
      (I := I) (timeSet := timeSet) (x₀ := x₀)
      (F := F) (Ft := Ft) (Φ := Φ)
      hΦ hFdiff hFchart hFtdiff hFtchart).toRegular
      (I := I) (regularSet := regularSet)

/-- Chart-level constructor for regular-time fixed-base mixed derivatives on a
singleton, with chart equalities required only on the time carrier and regular
times. -/
theorem fixedBaseExtDerivTimeDerivativeOnRegular_singleton_of_chart_contDiffOnTime
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {x₀ : M}
    {F Ft : Real -> M -> Real} {Φ : Real -> E -> Real}
    (hregular_subset : regularSet ⊆ timeSet)
    (hΦ : ContDiff Real 2 (fun p : Real × E => Φ p.1 p.2))
    (hFdiff :
      ∀ s : Real, s ∈ timeSet ->
        MDifferentiableAt I 𝓘(Real, Real) (F s) x₀)
    (hFchart :
      ∀ s : Real, s ∈ timeSet ->
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (F s)
          =ᶠ[nhds (extChartAt I x₀ x₀)] Φ s)
    (hFtdiff :
      ∀ t : Real, t ∈ regularSet ->
        MDifferentiableAt I 𝓘(Real, Real) (Ft t) x₀)
    (hFtchart :
      ∀ t : Real, t ∈ regularSet ->
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (Ft t)
          =ᶠ[nhds (extChartAt I x₀ x₀)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0)) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet ({x₀} : Set M) F Ft := by
  intro t ht x hx V
  rw [Set.mem_singleton_iff] at hx
  subst x
  let z₀ : E := extChartAt I x₀ x₀
  have hmodel :=
    fixedBaseFDerivTimeDerivativeWithinAt_of_contDiff
      (E := E) Φ hΦ (timeSet := timeSet) (t := t) z₀ V
  have hleft :
      ∀ s : Real, s ∈ timeSet ->
        extDerivFun (I := I) (F s) x₀ V =
          fderiv Real (Φ s) z₀ V := by
    intro s hs
    exact
      extDerivFun_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := F s) (φ := Φ s)
        (hFdiff s hs) (hFchart s hs) V
  have hright :
      extDerivFun (I := I) (Ft t) x₀ V =
        fderiv Real
          (fun y : E =>
            (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
          z₀ V := by
    exact
      extDerivFun_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
        (I := I) (x := x₀) (f := Ft t)
        (φ := fun y : E =>
          (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0))
      (hFtdiff t ht) (hFtchart t ht) V
  exact
    (hmodel.congr
      (fun s hs => hleft s hs)
      (hleft t (hregular_subset ht))).congr_deriv hright.symm

end RicciFlower

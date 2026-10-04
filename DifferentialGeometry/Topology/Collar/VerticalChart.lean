import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.FiniteInteriorPatch
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.SmoothDiffeomorph
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# A level set crossed once by every vertical line of a chart is the base (F-e, E4)

Let `j : S × ℝ → M` be a `C^k` (`1 ≤ k`) injective immersion on `S × (a, b)` into a manifold of
one more dimension, `S` compact, and let `f : M → ℝ` be differentiable at the level `f⁻¹(c)`. If
`s ↦ f (j (x, s))` has positive derivative on `(a, b)` for every `x`, every vertical line meets the
level, and the whole level lies in the image of `S × (a, b)`, then every embedded smooth structure
on the level (a boundaryless manifold `L` of the dimension of `S` with an injective immersion
`ι : L → M` onto the level) is smoothly diffeomorphic to `S`.

The projection `q = fst ∘ j⁻¹ ∘ ι : L → S` is `C^k` (finite-order inverse patches of `j`), has
injective differential (a kernel vector would be vertical and tangent to the level, but `f`
increases along verticals), hence is a `C^k` local diffeomorphism; it is bijective because each
vertical line crosses the level exactly once. The smooth structure is obtained from W-1's
`nonempty_diffeomorph_of_diffeomorph` (compact boundaryless manifolds). Used by BCP01 (the levels
of the height in a cusp collar are tori) through the bindings in `BoundaryCollar/`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

variable {E F EL : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup EL] [NormedSpace ℝ EL] [FiniteDimensional ℝ EL]
  {H G HL : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace HL]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} {IL : ModelWithCorners ℝ EL HL}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {S : Type*} [TopologicalSpace S] [ChartedSpace G S] [IsManifold J ∞ S]
  {L : Type*} [TopologicalSpace L] [ChartedSpace HL L] [IsManifold IL ∞ L]

/-- A function with positive derivative on `(a, b)` is strictly increasing there. -/
theorem strictMonoOn_Ioo_of_deriv_pos {φ : ℝ → ℝ} {a b : ℝ}
    (hφ : ∀ s ∈ Ioo a b, 0 < deriv φ s) : StrictMonoOn φ (Ioo a b) := by
  have hd : ∀ s ∈ Ioo a b, DifferentiableAt ℝ φ s := fun s hs =>
    differentiableAt_of_deriv_ne_zero (hφ s hs).ne'
  apply strictMonoOn_of_deriv_pos (convex_Ioo a b)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
  intro s hs
  rw [interior_Ioo] at hs
  exact hφ s hs

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ S] in
/-- The derivative of `f ∘ j` at `(x, s)` in the vertical direction `(0, 1)` is the derivative of
`s ↦ f (j (x, s))`. -/
theorem mfderiv_comp_vertical_eq_deriv {f : M → ℝ} {j : S × ℝ → M} {p : S × ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (j p))
    (hj : MDifferentiableAt (J.prod 𝓘(ℝ, ℝ)) I j p) :
    mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ j) p ((0 : TangentSpace J p.1), (1 : ℝ)) =
      deriv (fun s : ℝ => f (j (p.1, s))) p.2 := by
  have hγ : HasMFDerivAt 𝓘(ℝ, ℝ) (J.prod 𝓘(ℝ, ℝ)) (fun s : ℝ => (p.1, s)) p.2
      ((0 : ℝ →L[ℝ] TangentSpace J p.1).prod (ContinuousLinearMap.id ℝ ℝ)) :=
    (hasMFDerivAt_const p.1 p.2).prodMk (hasMFDerivAt_id p.2)
  have hfj : HasMFDerivAt (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ j) p
      (mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ j) p) :=
    (hf.comp p hj).hasMFDerivAt
  have hfj' : HasMFDerivAt (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ j) (p.1, p.2)
      (mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ j) p) := hfj
  have h1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ((f ∘ j) ∘ fun s : ℝ => (p.1, s)) p.2 =
      (mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ j) p).comp
        ((0 : ℝ →L[ℝ] TangentSpace J p.1).prod (ContinuousLinearMap.id ℝ ℝ)) :=
    (hfj'.comp p.2 hγ).mfderiv
  have h2 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ((f ∘ j) ∘ fun s : ℝ => (p.1, s)) p.2 =
      fderiv ℝ (fun s : ℝ => f (j (p.1, s))) p.2 := mfderiv_eq_fderiv
  rw [← fderiv_apply_one_eq_deriv, ← h2, h1]
  rfl

variable [J.Boundaryless] [IL.Boundaryless]

/-- **E4 (kernel).** A boundaryless manifold `L` embedded by an injective immersion `ι` onto the
level `f⁻¹(c)` is smoothly diffeomorphic to the compact base `S` of a `C^k` vertical chart `j` of
`M` along which `f` strictly increases, provided every vertical line meets the level and the
level lies in the chart. -/
theorem nonempty_diffeomorph_of_vertical_chart [Nonempty S] [CompactSpace S] [T2Space S]
    (hdimL : Module.finrank ℝ EL = Module.finrank ℝ F)
    (hdimM : Module.finrank ℝ (F × ℝ) = Module.finrank ℝ E)
    {ι : L → M} (hι : ContMDiff IL I ∞ ι) (hιd : ∀ y, Injective (mfderiv IL I ι y))
    (hιinj : Injective ι) {f : M → ℝ} {c : ℝ} (hfι : ∀ y, f (ι y) = c)
    (hrange : ∀ z, f z = c → z ∈ range ι)
    (hf : ∀ z, f z = c → MDifferentiableAt I 𝓘(ℝ, ℝ) f z)
    {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} {j : S × ℝ → M}
    (hj : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) I k j (univ ×ˢ Ioo a b))
    (hjinj : InjOn j (univ ×ˢ Ioo a b))
    (hjd : ∀ p ∈ (univ : Set S) ×ˢ Ioo a b, Injective (mfderiv (J.prod 𝓘(ℝ, ℝ)) I j p))
    (hjint : ∀ p ∈ (univ : Set S) ×ˢ Ioo a b, I.IsInteriorPoint (j p))
    (hvert : ∀ x : S, ∀ s ∈ Ioo a b, 0 < deriv (fun s : ℝ => f (j (x, s))) s)
    (hcross : ∀ x : S, ∃ s ∈ Ioo a b, f (j (x, s)) = c)
    (hlevel : ∀ z, f z = c → z ∈ j '' (univ ×ˢ Ioo a b)) :
    Nonempty (L ≃ₘ⟮IL, J⟯ S) := by
  classical
  set D : Set (S × ℝ) := univ ×ˢ Ioo a b with hDdef
  have hDo : IsOpen D := isOpen_univ.prod isOpen_Ioo
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk)
  let r : M → S × ℝ := invFunOn j D
  have hr : ∀ p ∈ D, r (j p) = p := fun p hp => hjinj.leftInvOn_invFunOn hp
  have hιD : ∀ y, ∃ p ∈ D, j p = ι y := fun y => hlevel (ι y) (hfι y)
  have hrD : ∀ y, r (ι y) ∈ D ∧ j (r (ι y)) = ι y := fun y => invFunOn_pos (hιD y)
  let q : L → S := fun y => (r (ι y)).1
  have hιc : Continuous ι := hι.continuous
  -- local description of `q` through an inverse patch of `j`
  have hloc : ∀ y₀ : L, ∃ Φ : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) I (S × ℝ) M k,
      r (ι y₀) ∈ Φ.source ∧ Φ.source ⊆ D ∧ EqOn j Φ Φ.source ∧
      ∀ y ∈ ι ⁻¹' Φ.target, r (ι y) = Φ.symm (ι y) := by
    intro y₀
    obtain ⟨hp₀D, -⟩ := hrD y₀
    obtain ⟨Φ, hpΦ, hΦD, hjΦ, -, -⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_finiteInteriorPatch hk hDo hj hp₀D
        BoundarylessManifold.isInteriorPoint (hjint _ hp₀D) hdimM (hjd _ hp₀D)
    refine ⟨Φ, hpΦ, hΦD, hjΦ, fun y hy => ?_⟩
    have hs : Φ.symm (ι y) ∈ Φ.source := Φ.map_target hy
    have hjs : j (Φ.symm (ι y)) = ι y := (hjΦ hs).trans (Φ.right_inv hy)
    calc r (ι y) = r (j (Φ.symm (ι y))) := by rw [hjs]
      _ = Φ.symm (ι y) := hr _ (hΦD hs)
  have hqloc : ∀ y₀ : L, ∃ V : Set L, IsOpen V ∧ y₀ ∈ V ∧
      ContMDiffOn IL J k q V ∧ Injective (mfderiv IL J q y₀) := by
    intro y₀
    obtain ⟨Φ, hpΦ, hΦD, hjΦ, hrΦ⟩ := hloc y₀
    obtain ⟨-, hjr⟩ := hrD y₀
    set p₀ := r (ι y₀) with hp₀
    have hp₀D : p₀ ∈ D := hΦD hpΦ
    have hιt : ι y₀ ∈ Φ.target := by
      rw [← hjr, hjΦ hpΦ]
      exact Φ.map_source hpΦ
    set V : Set L := ι ⁻¹' Φ.target with hV
    have hVo : IsOpen V := Φ.open_target.preimage hιc
    have hy₀V : y₀ ∈ V := hιt
    have hqV : EqOn q (Prod.fst ∘ Φ.symm ∘ ι) V := fun y hy => by
      change (r (ι y)).1 = (Φ.symm (ι y)).1
      rw [hrΦ y hy]
    have hsymm : ContMDiffOn I (J.prod 𝓘(ℝ, ℝ)) k Φ.symm Φ.target := Φ.symm.contMDiffOn
    have hcomp : ContMDiffOn IL J k (Prod.fst ∘ Φ.symm ∘ ι) V :=
      contMDiff_fst.comp_contMDiffOn
        (hsymm.comp (hι.of_le (by exact_mod_cast le_top)).contMDiffOn fun y hy => hy)
    refine ⟨V, hVo, hy₀V, hcomp.congr hqV, ?_⟩
    -- the differential
    have hevq : q =ᶠ[𝓝 y₀] Prod.fst ∘ Φ.symm ∘ ι :=
      Filter.eventuallyEq_of_mem (hVo.mem_nhds hy₀V) hqV
    have hιdiff : MDifferentiableAt IL I ι y₀ := (hι y₀).mdifferentiableAt (by simp)
    have hsdiff : MDifferentiableAt I (J.prod 𝓘(ℝ, ℝ)) Φ.symm (ι y₀) :=
      (hsymm.contMDiffAt (Φ.open_target.mem_nhds hιt)).mdifferentiableAt hk0
    have hsι : Φ.symm (ι y₀) = p₀ := by
      rw [← hjr, hjΦ hpΦ]
      exact Φ.left_inv hpΦ
    have hjdiff : MDifferentiableAt (J.prod 𝓘(ℝ, ℝ)) I j p₀ :=
      (hj.contMDiffAt (hDo.mem_nhds hp₀D)).mdifferentiableAt hk0
    have hfdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) f (j p₀) := hf _ (by rw [hjr]; exact hfι y₀)
    -- `j ∘ Φ.symm = id` near `ι y₀`
    have hjs : mfderiv I I (j ∘ Φ.symm) (ι y₀) = ContinuousLinearMap.id ℝ _ := by
      have hev : j ∘ Φ.symm =ᶠ[𝓝 (ι y₀)] id :=
        Filter.eventuallyEq_of_mem (Φ.open_target.mem_nhds hιt) fun z hz =>
          (hjΦ (Φ.map_target hz)).trans (Φ.right_inv hz)
      exact ((hasMFDerivAt_id (ι y₀)).congr_of_eventuallyEq_abuse hev).mfderiv
    have hjdiff' : MDifferentiableAt (J.prod 𝓘(ℝ, ℝ)) I j (Φ.symm (ι y₀)) := hsι ▸ hjdiff
    have hchain_js := mfderiv_comp (ι y₀) hjdiff' hsdiff
    -- `f ∘ ι` is constant
    have hfιd : mfderiv IL 𝓘(ℝ, ℝ) (f ∘ ι) y₀ = 0 := by
      have : f ∘ ι = fun _ => c := funext hfι
      rw [this, mfderiv_const]
    have hfdiff' : MDifferentiableAt I 𝓘(ℝ, ℝ) f (ι y₀) := hjr ▸ hfdiff
    have hchain_fι := mfderiv_comp y₀ hfdiff' hιdiff
    have hchain_fj := mfderiv_comp p₀ hfdiff hjdiff
    have hvpos := hvert p₀.1 p₀.2 hp₀D.2
    have hvert_eq := mfderiv_comp_vertical_eq_deriv hfdiff hjdiff
    rw [hevq.mfderiv_eq]
    intro v w hvw
    rw [← sub_eq_zero]
    set u := v - w
    have hu : mfderiv IL J (Prod.fst ∘ Φ.symm ∘ ι) y₀ u = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hvw
    apply hιd y₀
    rw [map_zero]
    have hchain_q : mfderiv IL J (Prod.fst ∘ Φ.symm ∘ ι) y₀ =
        (ContinuousLinearMap.fst ℝ (TangentSpace J (Φ.symm (ι y₀)).1)
          (TangentSpace 𝓘(ℝ, ℝ) (Φ.symm (ι y₀)).2)).comp
          ((mfderiv I (J.prod 𝓘(ℝ, ℝ)) Φ.symm (ι y₀)).comp (mfderiv IL I ι y₀)) := by
      rw [mfderiv_comp y₀ mdifferentiableAt_fst (hsdiff.comp y₀ hιdiff), mfderiv_fst,
        mfderiv_comp y₀ hsdiff hιdiff]
      rfl
    set U := mfderiv I (J.prod 𝓘(ℝ, ℝ)) Φ.symm (ι y₀) (mfderiv IL I ι y₀ u) with hU
    have hU1 : U.1 = 0 := by
      rw [hchain_q] at hu
      exact hu
    -- `dι u = dj U`
    have hdj : mfderiv (J.prod 𝓘(ℝ, ℝ)) I j (Φ.symm (ι y₀)) U = mfderiv IL I ι y₀ u := by
      have h := congrArg (fun T : TangentSpace I (ι y₀) →L[ℝ] TangentSpace I (ι y₀) =>
        T (mfderiv IL I ι y₀ u)) (hchain_js.symm.trans hjs)
      exact h
    -- `df (dι u) = 0`
    have hf0 : mfderiv I 𝓘(ℝ, ℝ) f (ι y₀) (mfderiv IL I ι y₀ u) = 0 := by
      have h := congrArg (fun T : TangentSpace IL y₀ →L[ℝ] ℝ => T u) (hchain_fι.symm.trans hfιd)
      exact h
    -- so `U.2 * ∂_s (f ∘ j) = 0`
    have hUeq : U = U.2 • (((0 : TangentSpace J p₀.1), (1 : ℝ)) :
        TangentSpace (J.prod 𝓘(ℝ, ℝ)) p₀) := by
      refine Prod.ext ?_ ?_
      · change U.1 = U.2 • (0 : TangentSpace J p₀.1)
        rw [smul_zero]
        exact hU1
      · change U.2 = U.2 * 1
        rw [mul_one]
    have hlin : mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ j) p₀ U =
        U.2 * deriv (fun s : ℝ => f (j (p₀.1, s))) p₀.2 := by
      let Lfj : F × ℝ →L[ℝ] ℝ := mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ j) p₀
      have hU' : (U : F × ℝ) = U.2 • ((0 : F), (1 : ℝ)) := hUeq
      have h01 : Lfj ((0 : F), (1 : ℝ)) = deriv (fun s : ℝ => f (j (p₀.1, s))) p₀.2 := hvert_eq
      change Lfj U = _
      rw [congrArg Lfj hU', Lfj.map_smul, h01, smul_eq_mul]
    have hzero : mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ j) p₀ U = 0 := by
      rw [hchain_fj]
      change mfderiv I 𝓘(ℝ, ℝ) f (j p₀) (mfderiv (J.prod 𝓘(ℝ, ℝ)) I j p₀ U) = 0
      have hdj' : mfderiv (J.prod 𝓘(ℝ, ℝ)) I j p₀ U = mfderiv IL I ι y₀ u := by
        rw [← hdj, hsι]
      rw [hdj']
      have key : ∀ z, z = ι y₀ → mfderiv I 𝓘(ℝ, ℝ) f z (mfderiv IL I ι y₀ u) = 0 := by
        rintro z rfl
        exact hf0
      exact key _ hjr
    have hU2 : U.2 = 0 := by
      rw [hlin] at hzero
      rcases (mul_eq_zero (M₀ := ℝ)).mp hzero with h | h
      · exact h
      · exact absurd h hvpos.ne'
    have hU0 : (U : F × ℝ) = 0 := Prod.ext hU1 hU2
    rw [← hdj, hU0, map_zero]
    rfl
  -- `q` is a `C^k` local diffeomorphism
  have hqdiff : IsLocalDiffeomorph IL J k q := by
    intro y₀
    obtain ⟨V, hVo, hy₀V, hqV, hqinj⟩ := hqloc y₀
    obtain ⟨Ψ, hyΨ, -, hqΨ, -, -⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_finiteInteriorPatch hk hVo hqV hy₀V
        BoundarylessManifold.isInteriorPoint BoundarylessManifold.isInteriorPoint hdimL hqinj
    exact ⟨Ψ, hyΨ, hqΨ⟩
  -- `q` is bijective
  have hqbij : Bijective q := by
    constructor
    · intro y₁ y₂ h12
      obtain ⟨h1D, h1j⟩ := hrD y₁
      obtain ⟨h2D, h2j⟩ := hrD y₂
      have hmono := strictMonoOn_Ioo_of_deriv_pos (hvert (r (ι y₁)).1)
      have hv1 : f (j ((r (ι y₁)).1, (r (ι y₁)).2)) = c := by rw [Prod.mk.eta, h1j, hfι]
      have hv2 : f (j ((r (ι y₁)).1, (r (ι y₂)).2)) = c := by
        change (r (ι y₁)).1 = (r (ι y₂)).1 at h12
        rw [h12, Prod.mk.eta, h2j, hfι]
      have hs : (r (ι y₁)).2 = (r (ι y₂)).2 :=
        hmono.injOn h1D.2 h2D.2 (hv1.trans hv2.symm)
      have hp : r (ι y₁) = r (ι y₂) := Prod.ext h12 hs
      apply hιinj
      rw [← h1j, ← h2j, hp]
    · intro x
      obtain ⟨s, hs, hfs⟩ := hcross x
      obtain ⟨y, hy⟩ := hrange _ hfs
      refine ⟨y, ?_⟩
      change (r (ι y)).1 = x
      rw [hy, hr (x, s) ⟨mem_univ x, hs⟩]
  let d : L ≃ₘ^k⟮IL, J⟯ S := hqdiff.diffeomorphOfBijective hqbij
  obtain ⟨d'⟩ := Manifold.SmoothApproximation.nonempty_diffeomorph_of_diffeomorph k hk d.symm
  exact ⟨d'.symm⟩

end DifferentialGeometry.Topology

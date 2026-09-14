import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LoopFamilyVelocityExtension
import DifferentialGeometry.Topology.Diffeomorph.Flow
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Global.InteriorInterval
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hNonempty : Nonempty M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
private theorem cutoffLift_contMDiff (X : ℝ → (p : M) → TangentSpace I p)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
      (fun p : ℝ × M =>
        (⟨p, χ p.1 • LiftLoopFamily (I := I) X p.1 p⟩ :
          TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) := by
  have hV := liftLoopFamily_contMDiff (I := I) X hX
  have hsmul : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => χ p.1) :=
    hχ.contMDiff.comp contMDiff_fst
  exact hsmul.smul_section hV

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] hBoundary hT2 hNonempty
  [SigmaCompactSpace M] in
private theorem cutoffLift_isCompactSupport (X : ℝ → (p : M) → TangentSpace I p)
    (χ : ℝ → ℝ) (hχc : HasCompactSupport χ) :
    IsCompact (tsupport fun q : ℝ × M =>
      χ q.1 • LiftLoopFamily (I := I) X q.1 q) := by
  have hsub : Function.support (fun q : ℝ × M =>
      χ q.1 • LiftLoopFamily (I := I) X q.1 q) ⊆
      Function.support (fun q : ℝ × M => χ q.1) := by
    intro q hq h0
    exact hq (by simp only [h0, zero_smul]; rfl)
  have hts : tsupport (fun q : ℝ × M => χ q.1) ⊆ tsupport χ ×ˢ univ := by
    apply closure_minimal _ (isClosed_tsupport _ |>.prod isClosed_univ)
    intro q hq
    exact ⟨subset_tsupport χ hq, mem_univ _⟩
  exact (hχc.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport _)
    ((closure_mono hsub).trans hts)

private noncomputable def phaseFlow (X : ℝ → (p : M) → TangentSpace I p)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) :
    ℝ → Diffeomorph (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (ℝ × M) (ℝ × M) ∞ :=
  Diffeomorph.compactSupportFlow (I := 𝓘(ℝ, ℝ).prod I) (M := ℝ × M)
    (fun q : ℝ × M => χ q.1 • LiftLoopFamily (I := I) X q.1 q)
    (cutoffLift_contMDiff (I := I) X hX χ hχ)
    (cutoffLift_isCompactSupport (I := I) X χ hχc)

omit [CompleteSpace E] hNonempty [SigmaCompactSpace M] in
private theorem phaseFlow_fst_eq (X : ℝ → (p : M) → TangentSpace I p)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (t₀ r : ℝ) (hr : 0 < r)
    (hχ1 : ∀ s : ℝ, s ∈ Ioo (t₀ - r) (t₀ + r) → χ s = 1)
    (x : M) {u : ℝ} (hu : dist u 0 < r) :
    (phaseFlow (I := I) X hX χ hχ hχc u (t₀, x)).1 = t₀ + u := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hχc hχ
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  set Ψ := phaseFlow (I := I) X hX χ hχ hχc with hΨdef
  have hv : ContMDiff (𝓘(ℝ, ℝ).prod I)
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
      (fun p : ℝ × M =>
        (⟨p, χ p.1 • LiftLoopFamily (I := I) X p.1 p⟩ :
          TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
    cutoffLift_contMDiff (I := I) X hX χ hχ
  have hsupp : IsCompact (tsupport fun q : ℝ × M =>
      χ q.1 • LiftLoopFamily (I := I) X q.1 q) :=
    cutoffLift_isCompactSupport (I := I) X χ hχc
  have hzero : Ψ 0 = Diffeomorph.refl (𝓘(ℝ, ℝ).prod I) (ℝ × M) ∞ := by
    rw [hΨdef]
    exact Diffeomorph.compactSupportFlow_zero _ hv hsupp
  have h0 : Ψ 0 (t₀, x) = (t₀, x) := by
    rw [DFunLike.congr_fun hzero (t₀, x)]
    rfl
  have hderiv (u : ℝ) :
      HasDerivAt (fun s : ℝ => (Ψ s (t₀, x)).1) (χ ((Ψ u (t₀, x)).1)) u := by
    have hcurve : IsMIntegralCurve (fun s : ℝ => Ψ s (t₀, x))
        (fun q : ℝ × M => χ q.1 • LiftLoopFamily (I := I) X q.1 q) := by
      rw [hΨdef]
      exact Diffeomorph.isMIntegralCurve_compactSupportFlow _ hv hsupp (t₀, x)
    have hraw : HasFDerivAt (fun s : ℝ => (Ψ s (t₀, x)).1)
        ((ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ℝ) (Ψ u (t₀, x)).1)
          (TangentSpace I (Ψ u (t₀, x)).2)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (χ (Ψ u (t₀, x)).1 •
              LiftLoopFamily (I := I) X (Ψ u (t₀, x)).1 (Ψ u (t₀, x))))) u :=
      ((hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (Ψ u (t₀, x))).comp u
        ((hcurve.isMIntegralCurveAt u).hasMFDerivAt)).hasFDerivAt
    have hmap : ((ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ℝ) (Ψ u (t₀, x)).1)
          (TangentSpace I (Ψ u (t₀, x)).2)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (χ (Ψ u (t₀, x)).1 •
              LiftLoopFamily (I := I) X (Ψ u (t₀, x)).1 (Ψ u (t₀, x))))) =
        ContinuousLinearMap.toSpanSingleton ℝ (χ (Ψ u (t₀, x)).1) := by
      apply ContinuousLinearMap.ext
      intro s
      change (s • (χ (Ψ u (t₀, x)).1 •
        ((1 : ℝ), X (Ψ u (t₀, x)).1 (Ψ u (t₀, x)).2))).1 = s • χ ((Ψ u (t₀, x)).1)
      simp
    change HasDerivAt (fun s : ℝ => (Ψ s (t₀, x)).1) (χ ((Ψ u (t₀, x)).1)) u
    exact hasDerivAt_iff_hasFDerivAt.mpr (hraw.congr_fderiv hmap)
  have heq : (fun s : ℝ => (Ψ s (t₀, x)).1) 0 = (fun s : ℝ => t₀ + s) 0 := by
    change (Ψ 0 (t₀, x)).1 = t₀ + 0
    rw [h0]
    norm_num
  have hσeq : EqOn (fun s : ℝ => (Ψ s (t₀, x)).1) (fun s : ℝ => t₀ + s) (Ioo (-r) r) :=
    ODE_solution_unique_of_mem_Ioo (v := fun _ : ℝ => χ) (s := fun _ => univ) (K := K)
      (a := -r) (b := r) (t₀ := 0)
      (fun _ _ => hK.lipschitzOnWith)
      (by simp only [mem_Ioo]; exact ⟨by linarith, hr⟩)
      (fun t _ => ⟨hderiv t, mem_univ _⟩)
      (fun t ht => by
        refine ⟨?_, mem_univ _⟩
        have hdist : dist (t₀ + t) t₀ < r := by
          rw [dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs]
          exact abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
        rw [hχ1 _ (by rw [mem_Ioo]; constructor <;> linarith [ht.1, ht.2])]
        exact ((hasFDerivAt_id t).const_add t₀).hasDerivAt)
      heq
  have hu' : u ∈ Ioo (-r) r := by
    rw [Real.dist_eq, sub_zero, abs_lt] at hu
    exact ⟨hu.1, hu.2⟩
  exact hσeq hu'

omit [CompleteSpace E] hNonempty in
private theorem phaseFlow_trajectory_eq (X : ℝ → (p : M) → TangentSpace I p)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    {r : ℝ} (hr : 0 < r) {a b : ℝ} {γ : ℝ → ContinuousFreeLoop M}
    (hvelIci : ∀ t ∈ Ico a b, ∀ z : Surgery.Topology.Circle,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ s z) (Ici t) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t z))))
    (hvelIic : ∀ t ∈ Ioc a b, ∀ z : Surgery.Topology.Circle,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ s z) (Iic t) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t z))))
    {τ u : ℝ} (hτ : τ ∈ Icc a b) (hτu : τ + u ∈ Icc a b) (hu : 0 ≤ u)
    (hur : u < r) (hχ1 : ∀ s : ℝ, s ∈ Ioo (τ - r) (τ + r) → χ s = 1)
    (z : Surgery.Topology.Circle) :
    (phaseFlow (I := I) X hX χ hχ hχc u (τ, γ τ z)).2 = γ (τ + u) z := by
  rcases eq_or_lt_of_le hu with h0 | hpos
  · subst h0
    have hzero : phaseFlow (I := I) X hX χ hχ hχc 0 =
        Diffeomorph.refl (𝓘(ℝ, ℝ).prod I) (ℝ × M) ∞ :=
      Diffeomorph.compactSupportFlow_zero _ _ _
    rw [DFunLike.congr_fun hzero (τ, γ τ z)]
    rw [add_zero]
    rfl
  · set Ψ := phaseFlow (I := I) X hX χ hχ hχc with hΨdef
    have hv : ContMDiff (𝓘(ℝ, ℝ).prod I)
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
        (fun p : ℝ × M =>
          (⟨p, χ p.1 • LiftLoopFamily (I := I) X p.1 p⟩ :
            TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
      cutoffLift_contMDiff (I := I) X hX χ hχ
    have hsupp : IsCompact (tsupport fun q : ℝ × M =>
        χ q.1 • LiftLoopFamily (I := I) X q.1 q) :=
      cutoffLift_isCompactSupport (I := I) X χ hχc
    have htraj : IsMIntegralCurve (fun s : ℝ => Ψ s (τ, γ τ z))
        (fun q : ℝ × M => χ q.1 • LiftLoopFamily (I := I) X q.1 q) := by
      rw [hΨdef]
      exact Diffeomorph.isMIntegralCurve_compactSupportFlow _ hv hsupp (τ, γ τ z)
    have hA : ∀ t ∈ Icc (0 : ℝ) u,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u' : ℝ => (Ψ u' (τ, γ τ z)).2) (Ici 0) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X (τ + t) (Ψ t (τ, γ τ z)).2)) := by
      intro t ht
      have ht0 : dist t 0 < r := by
        rw [Real.dist_eq, sub_zero]
        exact abs_lt.mpr ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hur⟩
      have hσ : (Ψ t (τ, γ τ z)).1 = τ + t := by
        rw [hΨdef]
        exact phaseFlow_fst_eq (I := I) X hX χ hχ hχc τ r hr hχ1 (γ τ z) ht0
      have hχτ : χ (τ + t) = 1 := hχ1 _ (by
        rw [mem_Ioo]; constructor <;> linarith [ht.1, ht.2, hur])
      have hraw := ((hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I) (Ψ t (τ, γ τ z))).comp t
        ((htraj.isMIntegralCurveAt t).hasMFDerivAt))
      have hL : ((ContinuousLinearMap.snd ℝ (TangentSpace 𝓘(ℝ, ℝ) (Ψ t (τ, γ τ z)).1)
            (TangentSpace I (Ψ t (τ, γ τ z)).2)).comp
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (χ (Ψ t (τ, γ τ z)).1 •
                LiftLoopFamily (I := I) X (Ψ t (τ, γ τ z)).1 (Ψ t (τ, γ τ z))))) =
          (1 : ℝ →L[ℝ] ℝ).smulRight (X (τ + t) (Ψ t (τ, γ τ z)).2) := by
        apply ContinuousLinearMap.ext
        intro c
        change (c • (χ (Ψ t (τ, γ τ z)).1 •
          ((1 : ℝ), X (Ψ t (τ, γ τ z)).1 (Ψ t (τ, γ τ z)).2))).2 =
            c • X (τ + t) (Ψ t (τ, γ τ z)).2
        rw [hσ, hχτ]
        simp only [one_smul, Prod.smul_snd]
      exact (hraw.congr_mfderiv hL).hasMFDerivWithinAt
    have hB : ∀ t ∈ Ico (0 : ℝ) u,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u' : ℝ => γ (τ + u') z) (Ici 0) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X (τ + t) (γ (τ + t) z))) := by
      intro t ht
      have hpl : a ≤ τ + t := le_trans hτ.1 (by linarith [ht.1])
      have hpr : τ + t < b := by linarith [ht.2, hτu.2]
      have houter : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun r' : ℝ => γ r' z) (Ici τ) (τ + t)
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X (τ + t) (γ (τ + t) z))) := by
        by_cases hpa : a < τ + t
        · have h1 := hvelIci (τ + t) ⟨hpl, hpr⟩ z
          have h2 := hvelIic (τ + t) ⟨hpa, le_of_lt hpr⟩ z
          exact (h1.union h2).mono (by
            intro r' hr'
            simp only [mem_Ici, mem_union, mem_Iic] at hr' ⊢
            rcases le_total (τ + t) r' with h | h
            · exact Or.inl h
            · exact Or.inr h)
        · have hpa' : τ + t = a := le_antisymm (le_of_not_gt hpa) hpl
          exact (hvelIci (τ + t) ⟨hpl, hpr⟩ z).mono (by
            intro r' hr'
            simp only [mem_Ici] at hr' ⊢
            linarith [hr', hpa', hτ.1])
      have hinner : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
          (fun u' : ℝ => τ + u') (Ici 0) t
          (1 : ℝ →L[ℝ] ℝ) :=
        (((hasFDerivAt_id t).const_add τ)).hasMFDerivAt.hasMFDerivWithinAt
      have hmt : MapsTo (fun u' : ℝ => τ + u') (Ici (0 : ℝ)) (Ici τ) := by
        intro u' hu'
        simp only [mem_Ici] at hu' ⊢
        linarith
      have hcomp := houter.comp t hinner hmt
      have hclm : ((1 : ℝ →L[ℝ] ℝ).smulRight (X (τ + t) (γ (τ + t) z))).comp
          (1 : ℝ →L[ℝ] ℝ) =
          (1 : ℝ →L[ℝ] ℝ).smulRight (X (τ + t) (γ (τ + t) z)) := by
        apply ContinuousLinearMap.ext
        intro c
        change c • X (τ + t) (γ (τ + t) z) = c • X (τ + t) (γ (τ + t) z)
        rfl
      exact hcomp.congr_mfderiv hclm
    have hXtil : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X (τ + q.1) q.2) : TangentBundle I M)) :=
      hX.comp ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
    have hsmoothIcc : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M =>
          (TotalSpace.mk' E q.2 (X (τ + q.1) q.2) : TangentBundle I M))
        (Icc (0 : ℝ) u ×ˢ univ) :=
      hXtil.contMDiffOn.mono (subset_univ _)
    have hsmoothIoo : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M =>
          (TotalSpace.mk' E q.2 (X (τ + q.1) q.2) : TangentBundle I M))
        (Ioo (0 : ℝ) (u + 1) ×ˢ univ) :=
      hXtil.contMDiffOn.mono (subset_univ _)
    have hstart : (fun _ : M => (Ψ 0 (τ, γ τ z)).2) (γ τ z) =
        (fun _ : M => γ (τ + 0) z) (γ τ z) := by
      have hzeroΨ : Ψ 0 = Diffeomorph.refl (𝓘(ℝ, ℝ).prod I) (ℝ × M) ∞ := by
        rw [hΨdef]
        exact Diffeomorph.compactSupportFlow_zero _ hv hsupp
      change (Ψ 0 (τ, γ τ z)).2 = γ (τ + 0) z
      rw [DFunLike.congr_fun hzeroΨ (τ, γ τ z)]
      rw [add_zero]
      rfl
    have hIco : ∀ t ∈ Ico (0 : ℝ) u,
        (fun p : M => (Ψ t (τ, p)).2) (γ τ z) = (fun _ : M => γ (τ + t) z) (γ τ z) :=
      DifferentialGeometry.Analysis.ODE.integral_curves_eqOn_Ico_of_smooth
        (X := fun u' : ℝ => fun p : M => X (τ + u') p) u hpos hsmoothIcc
        (fun t : ℝ => fun p : M => (Ψ t (τ, p)).2) (fun t : ℝ => fun _ : M => γ (τ + t) z)
        (γ τ z) (γ τ z) (fun t ht => hA t ⟨ht.1, ht.2.le⟩)
        hB hstart
    have hhalf : (Ψ (u / 2) (τ, γ τ z)).2 = γ (τ + u / 2) z :=
      hIco (u / 2) ⟨by linarith, by linarith⟩
    have hsub : Icc (u / 2) u ⊆ Ici (0 : ℝ) := by
      intro r hr
      exact le_trans (by linarith [hpos]) hr.1
    have hA' : ∀ t ∈ Icc (u / 2) u,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u' : ℝ => (Ψ u' (τ, γ τ z)).2)
          (Icc (u / 2) u) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X (τ + t) (Ψ t (τ, γ τ z)).2)) :=
      fun t ht => (hA t ⟨by linarith [ht.1, hpos], ht.2⟩).mono hsub
    have hB' : ∀ t ∈ Icc (u / 2) u,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u' : ℝ => γ (τ + u') z) (Icc (u / 2) u) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X (τ + t) (γ (τ + t) z))) := by
      intro t ht
      have hpl : a < τ + t := by linarith [ht.1, hpos, hτ.1]
      have hpr : τ + t ≤ b := by linarith [ht.2, hτu.2]
      have hinner : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
          (fun u' : ℝ => τ + u') (Icc (u / 2) u) t
          (1 : ℝ →L[ℝ] ℝ) :=
        (((hasFDerivAt_id t).const_add τ)).hasMFDerivAt.hasMFDerivWithinAt
      have hclm : ((1 : ℝ →L[ℝ] ℝ).smulRight (X (τ + t) (γ (τ + t) z))).comp
          (1 : ℝ →L[ℝ] ℝ) =
          (1 : ℝ →L[ℝ] ℝ).smulRight (X (τ + t) (γ (τ + t) z)) := by
        apply ContinuousLinearMap.ext
        intro c
        change c • X (τ + t) (γ (τ + t) z) = c • X (τ + t) (γ (τ + t) z)
        rfl
      by_cases hpb : τ + t < b
      · have h1 := hvelIci (τ + t) ⟨hpl.le, hpb⟩ z
        have h2 := hvelIic (τ + t) ⟨hpl, hpr⟩ z
        have houter : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun r' : ℝ => γ r' z)
            (Icc a b) (τ + t)
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X (τ + t) (γ (τ + t) z))) :=
          (h1.union h2).mono (by
            intro r' hr'
            simp only [mem_Icc] at hr' ⊢
            rcases le_total (τ + t) r' with h | h
            · exact Or.inl h
            · exact Or.inr h)
        have hmt : MapsTo (fun u' : ℝ => τ + u') (Icc (u / 2) u) (Icc a b) := by
          intro u' hu'
          simp only [mem_Icc] at hu' ⊢
          exact ⟨by linarith [hu'.1, hpos, hτ.1], by linarith [hu'.2, hτu.2]⟩
        exact (houter.comp t hinner hmt).congr_mfderiv hclm
      · have hpb' : τ + t = b := le_antisymm hpr (le_of_not_gt hpb)
        have houter : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun r' : ℝ => γ r' z)
            (Iic (τ + t)) (τ + t)
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X (τ + t) (γ (τ + t) z))) :=
          hvelIic (τ + t) ⟨hpl, hpr⟩ z
        have hmt : MapsTo (fun u' : ℝ => τ + u') (Icc (u / 2) u) (Iic (τ + t)) := by
          intro u' hu'
          simp only [mem_Iic] at hu' ⊢
          linarith [hu'.2, hτu.2, hpb']
        exact (houter.comp t hinner hmt).congr_mfderiv hclm
    exact DifferentialGeometry.Analysis.ODE.integralCurves_eqOn_Icc_of_agree_at_left
      (X := fun u' : ℝ => fun p : M => X (τ + u') p) (u + 1) hsmoothIoo
      (fun t : ℝ => fun p : M => (Ψ t (τ, p)).2) (fun t : ℝ => fun _ : M => γ (τ + t) z)
      (γ τ z) (γ τ z) (a := u / 2) (b := u) (by linarith) (by linarith) (by linarith)
      hA' hB' hhalf u ⟨by linarith, le_rfl⟩

omit [CompleteSpace E] hNonempty [SigmaCompactSpace M] in
private theorem phaseFlow_eq_compactSupportFlow (X : ℝ → (p : M) → TangentSpace I p)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hv : ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
      (fun p : ℝ × M =>
        (⟨p, χ p.1 • LiftLoopFamily (I := I) X p.1 p⟩ :
          TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))))
    (hsupp : IsCompact (tsupport fun q : ℝ × M =>
      χ q.1 • LiftLoopFamily (I := I) X q.1 q)) :
    phaseFlow (I := I) X hX χ hχ hχc =
      Diffeomorph.compactSupportFlow
        (fun q : ℝ × M => χ q.1 • LiftLoopFamily (I := I) X q.1 q) hv hsupp := rfl

private noncomputable def phaseSliceEquiv (X : ℝ → (p : M) → TangentSpace I p)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (t₀ R r : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hRr : R - r ≤ r)
    (hχR : ∀ s : ℝ, s ∈ Ioo (t₀ - R) (t₀ + R) → χ s = 1)
    (t : ℝ) (ht : dist t t₀ < R - r) : M ≃ M where
  toFun := fun x => (phaseFlow (I := I) X hX χ hχ hχc (t - t₀) (t₀, x)).2
  invFun := fun y => (phaseFlow (I := I) X hX χ hχ hχc (t₀ - t) (t, y)).2
  left_inv := by
    intro x
    set Ψ := phaseFlow (I := I) X hX χ hχ hχc with hΨdef
    have hv : ContMDiff (𝓘(ℝ, ℝ).prod I)
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
        (fun p : ℝ × M =>
          (⟨p, χ p.1 • LiftLoopFamily (I := I) X p.1 p⟩ :
            TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
      cutoffLift_contMDiff (I := I) X hX χ hχ
    have hsupp : IsCompact (tsupport fun q : ℝ × M =>
        χ q.1 • LiftLoopFamily (I := I) X q.1 q) :=
      cutoffLift_isCompactSupport (I := I) X χ hχc
    have hΨeq : Ψ = Diffeomorph.compactSupportFlow
        (fun q : ℝ × M => χ q.1 • LiftLoopFamily (I := I) X q.1 q) hv hsupp := by
      rw [hΨdef]; rfl
    have hd : dist (t - t₀) 0 < r := by
      rw [Real.dist_eq, sub_zero, ← Real.dist_eq]
      linarith [ht, hRr]
    have h1 : (Ψ (t - t₀) (t₀, x)).1 = t := by
      rw [phaseFlow_fst_eq (I := I) X hX χ hχ hχc t₀ r hr
        (fun s hs => hχR s (Ioo_subset_Ioo (by linarith) (by linarith) hs)) x hd]
      ring
    have hpt : (t, (Ψ (t - t₀) (t₀, x)).2) = Ψ (t - t₀) (t₀, x) := Prod.ext h1.symm rfl
    have hgroup : (Ψ (t - t₀)).trans (Ψ (t₀ - t)) =
        Diffeomorph.refl (𝓘(ℝ, ℝ).prod I) (ℝ × M) ∞ := by
      have h := Diffeomorph.compactSupportFlow_add
        (v := fun q : ℝ × M => χ q.1 • LiftLoopFamily (I := I) X q.1 q) (hv := hv)
        (hsupp := hsupp) (t - t₀) (t₀ - t)
      have hz : (t - t₀) + (t₀ - t) = 0 := by ring
      rw [hz, Diffeomorph.compactSupportFlow_zero] at h
      rw [hΨeq]
      exact h.symm
    have hc := DFunLike.congr_fun hgroup (t₀, x)
    change (Ψ (t₀ - t) (t, (Ψ (t - t₀) (t₀, x)).2)).2 = x
    rw [hpt]
    simp only [Diffeomorph.coe_trans, Function.comp_apply] at hc
    rw [hc]
    rfl
  right_inv := by
    intro y
    set Ψ := phaseFlow (I := I) X hX χ hχ hχc with hΨdef
    have hv : ContMDiff (𝓘(ℝ, ℝ).prod I)
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
        (fun p : ℝ × M =>
          (⟨p, χ p.1 • LiftLoopFamily (I := I) X p.1 p⟩ :
            TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
      cutoffLift_contMDiff (I := I) X hX χ hχ
    have hsupp : IsCompact (tsupport fun q : ℝ × M =>
        χ q.1 • LiftLoopFamily (I := I) X q.1 q) :=
      cutoffLift_isCompactSupport (I := I) X χ hχc
    have hΨeq : Ψ = Diffeomorph.compactSupportFlow
        (fun q : ℝ × M => χ q.1 • LiftLoopFamily (I := I) X q.1 q) hv hsupp := by
      rw [hΨdef]; rfl
    have hd : dist (t₀ - t) 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_sub_comm, ← Real.dist_eq]
      linarith [ht, hRr]
    have h1 : (Ψ (t₀ - t) (t, y)).1 = t₀ := by
      rw [phaseFlow_fst_eq (I := I) X hX χ hχ hχc t r hr
        (fun s hs => hχR s (by
          rw [mem_Ioo] at hs ⊢
          have hlt : t - t₀ < R - r := (abs_lt.mp (by rw [← Real.dist_eq]; exact ht)).2
          have hgt : -(R - r) < t - t₀ := (abs_lt.mp (by rw [← Real.dist_eq]; exact ht)).1
          constructor <;> linarith [hs.1, hs.2])) y hd]
      ring
    have hpt : (t₀, (Ψ (t₀ - t) (t, y)).2) = Ψ (t₀ - t) (t, y) := Prod.ext h1.symm rfl
    have hgroup : (Ψ (t₀ - t)).trans (Ψ (t - t₀)) =
        Diffeomorph.refl (𝓘(ℝ, ℝ).prod I) (ℝ × M) ∞ := by
      have h := Diffeomorph.compactSupportFlow_add
        (v := fun q : ℝ × M => χ q.1 • LiftLoopFamily (I := I) X q.1 q) (hv := hv)
        (hsupp := hsupp) (t₀ - t) (t - t₀)
      have hz : (t₀ - t) + (t - t₀) = 0 := by ring
      rw [hz, Diffeomorph.compactSupportFlow_zero] at h
      rw [hΨeq]
      exact h.symm
    have hc := DFunLike.congr_fun hgroup (t, y)
    change (Ψ (t - t₀) (t₀, (Ψ (t₀ - t) (t, y)).2)).2 = y
    rw [hpt]
    simp only [Diffeomorph.coe_trans, Function.comp_apply] at hc
    rw [hc]
    rfl

private noncomputable def phaseSlice (X : ℝ → (p : M) → TangentSpace I p)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (t₀ R r : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hRr : R - r ≤ r)
    (hχR : ∀ s : ℝ, s ∈ Ioo (t₀ - R) (t₀ + R) → χ s = 1)
    (t : ℝ) (ht : dist t t₀ < R - r) : Diffeomorph I I M M ∞ where
  toEquiv := phaseSliceEquiv (I := I) X hX χ hχ hχc t₀ R r hr hrR hRr hχR t ht
  contMDiff_toFun := by
    have hv : ContMDiff (𝓘(ℝ, ℝ).prod I)
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
        (fun p : ℝ × M =>
          (⟨p, χ p.1 • LiftLoopFamily (I := I) X p.1 p⟩ :
            TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
      cutoffLift_contMDiff (I := I) X hX χ hχ
    have hsupp : IsCompact (tsupport fun q : ℝ × M =>
        χ q.1 • LiftLoopFamily (I := I) X q.1 q) :=
      cutoffLift_isCompactSupport (I := I) X χ hχc
    have hcomp : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
        (fun y : ℝ × M =>
          (phaseFlow (I := I) X hX χ hχ hχc (t - t₀) y).2) := by
      rw [phaseFlow_eq_compactSupportFlow X hX χ hχ hχc hv hsupp]
      exact contMDiff_snd.comp
        ((Diffeomorph.contMDiff_compactSupportFlow _ hv hsupp).comp
          (contMDiff_const.prodMk contMDiff_id))
    exact hcomp.comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun := by
    have hv : ContMDiff (𝓘(ℝ, ℝ).prod I)
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
        (fun p : ℝ × M =>
          (⟨p, χ p.1 • LiftLoopFamily (I := I) X p.1 p⟩ :
            TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
      cutoffLift_contMDiff (I := I) X hX χ hχ
    have hsupp : IsCompact (tsupport fun q : ℝ × M =>
        χ q.1 • LiftLoopFamily (I := I) X q.1 q) :=
      cutoffLift_isCompactSupport (I := I) X χ hχc
    have hcomp : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
        (fun y : ℝ × M =>
          (phaseFlow (I := I) X hX χ hχ hχc (t₀ - t) y).2) := by
      rw [phaseFlow_eq_compactSupportFlow X hX χ hχ hχc hv hsupp]
      exact contMDiff_snd.comp
        ((Diffeomorph.contMDiff_compactSupportFlow _ hv hsupp).comp
          (contMDiff_const.prodMk contMDiff_id))
    exact hcomp.comp (contMDiff_const.prodMk contMDiff_id)

omit [CompleteSpace E] hNonempty in
theorem rfs_csf_boundary_isotopy_of_velocityExtension (a b : ℝ)
    (γ : ℝ → ContinuousFreeLoop M) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b)
    (hvel : LoopFamilyVelocityExtension (I := I) a b γ) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : M × ℝ => Φ p.2 p.1)
        (univ ×ˢ (Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z := by
  obtain ⟨X, hX, hvelIci, hvelIic⟩ := hvel
  let bmp : ContDiffBump (t₀ : ℝ) := ⟨2, 3, by norm_num, by norm_num⟩
  let χ : ℝ → ℝ := ⇑bmp
  have hχ : ContDiff ℝ ∞ χ := bmp.contDiff
  have hχc : HasCompactSupport χ := bmp.hasCompactSupport
  have hχR : ∀ s : ℝ, s ∈ Ioo (t₀ - 2) (t₀ + 2) → χ s = 1 := by
    intro s hs
    exact bmp.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, Real.dist_eq]
      exact (abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩).le)
  have hwin : ∀ t : ℝ, t ∈ Ioo (t₀ - (1 / 2 : ℝ)) (t₀ + 1 / 2) →
      dist t t₀ < 2 - 3 / 2 := by
    intro t ht
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨1 / 2, by norm_num, fun t =>
    if ht : dist t t₀ < 2 - 3 / 2 then
      phaseSlice (I := I) X hX χ hχ hχc t₀ 2 (3 / 2) (by norm_num) (by norm_num)
        (by norm_num) hχR t ht
    else Diffeomorph.refl I M ∞, ?_, ?_, ?_⟩
  · have hv : ContMDiff (𝓘(ℝ, ℝ).prod I)
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
        (fun p : ℝ × M =>
          (⟨p, χ p.1 • LiftLoopFamily (I := I) X p.1 p⟩ :
            TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
      cutoffLift_contMDiff (I := I) X hX χ hχ
    have hsupp : IsCompact (tsupport fun q : ℝ × M =>
        χ q.1 • LiftLoopFamily (I := I) X q.1 q) :=
      cutoffLift_isCompactSupport (I := I) X χ hχc
    have hjoint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞
        (fun p : M × ℝ =>
          (phaseFlow (I := I) X hX χ hχ hχc (p.2 - t₀) (t₀, p.1)).2) := by
      have hj : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, ℝ).prod I) ∞
          (fun q : ℝ × (ℝ × M) => phaseFlow (I := I) X hX χ hχ hχc q.1 q.2) := by
        rw [phaseFlow_eq_compactSupportFlow X hX χ hχ hχc hv hsupp]
        exact Diffeomorph.contMDiff_compactSupportFlow _ hv hsupp
      have hinner : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I))
          ∞
          (fun p : M × ℝ => (p.2 - t₀, (t₀, p.1))) :=
        (contMDiff_snd.sub contMDiff_const).prodMk (contMDiff_const.prodMk contMDiff_fst)
      exact contMDiff_snd.comp (hj.comp hinner)
    refine (hjoint.contMDiffOn.mono (subset_univ _)).congr ?_
    intro p hp
    obtain ⟨-, htw⟩ := hp
    dsimp only
    rw [dif_pos (hwin p.2 htw.2)]
    rfl
  · intro p
    have hd : dist t₀ t₀ < 2 - 3 / 2 := by
      rw [Real.dist_eq, sub_self, abs_zero]
      norm_num
    dsimp only
    rw [dif_pos hd]
    change (phaseFlow (I := I) X hX χ hχ hχc (t₀ - t₀) (t₀, p)).2 = p
    have hzero : phaseFlow (I := I) X hX χ hχ hχc 0 =
        Diffeomorph.refl (𝓘(ℝ, ℝ).prod I) (ℝ × M) ∞ :=
      Diffeomorph.compactSupportFlow_zero _ _ _
    rw [sub_self, DFunLike.congr_fun hzero (t₀, p)]
    rfl
  · intro t ht z
    obtain ⟨hta, htw⟩ := ht
    have hd : dist t t₀ < 2 - 3 / 2 := hwin t htw
    dsimp only
    rw [dif_pos hd]
    change (phaseFlow (I := I) X hX χ hχ hχc (t - t₀) (t₀, γ t₀ z)).2 = γ t z
    set Ψ := phaseFlow (I := I) X hX χ hχ hχc with hΨdef
    have hv : ContMDiff (𝓘(ℝ, ℝ).prod I)
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
        (fun p : ℝ × M =>
          (⟨p, χ p.1 • LiftLoopFamily (I := I) X p.1 p⟩ :
            TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
      cutoffLift_contMDiff (I := I) X hX χ hχ
    have hsupp : IsCompact (tsupport fun q : ℝ × M =>
        χ q.1 • LiftLoopFamily (I := I) X q.1 q) :=
      cutoffLift_isCompactSupport (I := I) X χ hχc
    have hχsub : ∀ s : ℝ, s ∈ Ioo (t₀ - (3 / 2)) (t₀ + 3 / 2) → χ s = 1 :=
      fun s hs => hχR s (Ioo_subset_Ioo (by linarith) (by linarith) hs)
    rcases le_or_gt t₀ t with hle | hlt
    · have hdA : |t - t₀| < 2 - 3 / 2 := by rw [← Real.dist_eq]; exact hd
      have hur0 : t - t₀ < 3 / 2 := by
        have := (abs_lt.mp hdA).2
        linarith
      have htu : t₀ + (t - t₀) = t := by ring
      have htraj := phaseFlow_trajectory_eq (I := I) X hX χ hχ hχc (r := (3 : ℝ) / 2)
        (by norm_num) (hvelIci := hvelIci) (hvelIic := hvelIic) (hτ := ht₀)
        (hτu := by rw [htu]; exact hta)
        (hu := by linarith) (hur := hur0) (hχ1 := hχsub) (z := z)
      rw [htu] at htraj
      exact htraj
    · have hdA : |t - t₀| < 2 - 3 / 2 := by rw [← Real.dist_eq]; exact hd
      have hur1 : t₀ - t < 3 / 2 := by
        have := (abs_lt.mp hdA).1
        linarith
      have htu : t + (t₀ - t) = t₀ := by ring
      have hχt : ∀ s : ℝ, s ∈ Ioo (t - (3 / 2)) (t + 3 / 2) → χ s = 1 := by
        intro s hs
        refine hχR s ?_
        rw [mem_Ioo] at hs ⊢
        have hd2 : |t - t₀| < 2 - 3 / 2 := by rw [← Real.dist_eq]; exact hd
        have hlt2 : t - t₀ < 2 - 3 / 2 := (abs_lt.mp hd2).2
        have hgt2 : -(2 - 3 / 2) < t - t₀ := (abs_lt.mp hd2).1
        constructor <;> linarith [hs.1, hs.2]
      have htraj := phaseFlow_trajectory_eq (I := I) X hX χ hχ hχc (r := (3 : ℝ) / 2)
        (by norm_num) (hvelIci := hvelIci) (hvelIic := hvelIic) (hτ := hta)
        (hτu := by rw [htu]; exact ht₀)
        (hu := by linarith) (hur := hur1) (hχ1 := hχt) (z := z)
      rw [htu] at htraj
      have hd1 : dist (t₀ - t) 0 < 3 / 2 := by
        rw [Real.dist_eq, sub_zero, abs_sub_comm, ← Real.dist_eq]
        linarith [hd]
      have h1 : (Ψ (t₀ - t) (t, γ t z)).1 = t₀ := by
        rw [hΨdef, phaseFlow_fst_eq (I := I) X hX χ hχ hχc t (3 / 2) (by norm_num) hχt
          (γ t z) hd1]
        ring
      have hpt : (t₀, γ t₀ z) = Ψ (t₀ - t) (t, γ t z) := Prod.ext h1.symm htraj.symm
      have hgroup : (Ψ (t₀ - t)).trans (Ψ (t - t₀)) =
          Diffeomorph.refl (𝓘(ℝ, ℝ).prod I) (ℝ × M) ∞ := by
        have h := Diffeomorph.compactSupportFlow_add
          (v := fun q : ℝ × M => χ q.1 • LiftLoopFamily (I := I) X q.1 q) (hv := hv)
          (hsupp := hsupp) (t₀ - t) (t - t₀)
        have hz : (t₀ - t) + (t - t₀) = 0 := by ring
        rw [hz, Diffeomorph.compactSupportFlow_zero] at h
        rw [hΨdef, phaseFlow_eq_compactSupportFlow X hX χ hχ hχc hv hsupp]
        exact h.symm
      have hc := DFunLike.congr_fun hgroup (t, γ t z)
      simp only [Diffeomorph.coe_trans, Function.comp_apply] at hc
      rw [hpt]
      rw [hc]
      rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

import DifferentialGeometry.Analysis.Elliptic.EndomorphismKernel
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Reaction
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.Spacetime
import DifferentialGeometry.Bundle.SmoothSubbundle.KernelMotion
import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative Filter
open scoped Manifold ContDiff Topology InnerProductSpace BigOperators

namespace PositiveSystem

open DifferentialGeometry
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

private theorem kernel_covariantDerivatives_mem_and_reaction_inner_eq_zero
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    {t : ℝ} {x : M}
    (hA : ∀ y, (A t y : V y →ₗ[ℝ] V y).IsSymmetric)
    (hApos : (A t x).IsPositive)
    (Z : TangentSpace I x) (w : Cₛ^∞⟮I; F, V⟯)
    (B : V x →L[ℝ] V x) (hB : 0 ≤ inner ℝ (B (w x)) (w x))
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U)
    (hw : ∀ y ∈ U, A t y (w y) = 0)
    (htime : inner ℝ (deriv (fun s => A s x) t (w x)) (w x) = 0)
    (hevolution :
      deriv (fun s => A s x) t =
        rawBundleEndomorphismConnLap (I := I) g cov (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V cov cov (fun y => A t y) x Z + B) :
    (∀ i : Fin (Module.finrank ℝ E),
      cov (fun y => w y) x (smoothOrthoFrame (I := I) g x i x) ∈
        (A t x).ker) ∧
      inner ℝ (B (w x)) (w x) = 0 := by
  have hdrift :
      inner ℝ
          ((HomConnectionGen.homBundleCovariantDerivativeGen
              I M F V F V cov cov (fun y => A t y) x Z) (w x))
          (w x) = 0 :=
    HomConnectionGen.inner_homBundleCovariantDerivativeGen_apply_of_eventually_mem_ker
      cov (A t) hA w hU hxU hw Z
  have hlap :=
    inner_rawBundleEndomorphismConnLap_apply_of_eventually_mem_ker
      g cov hcov (A t) hA w hU hxU hw
  have heval := congrArg
    (fun Q : V x →L[ℝ] V x => inner ℝ (Q (w x)) (w x)) hevolution
  simp only [add_apply, inner_add_left] at heval
  rw [htime, hlap, hdrift] at heval
  simp only [add_zero] at heval
  have hidentity :
      2 * ∑ i : Fin (Module.finrank ℝ E),
          inner ℝ
            (A t x (cov (fun y => w y) x
              (smoothOrthoFrame (I := I) g x i x)))
            (cov (fun y => w y) x
              (smoothOrthoFrame (I := I) g x i x)) +
        inner ℝ (B (w x)) (w x) = 0 := by
    linarith
  exact kernel_derivatives_mem_and_reaction_inner_eq_zero
    hApos
    (fun i => cov (fun y => w y) x
      (smoothOrthoFrame (I := I) g x i x))
    (w x) hB hidentity

theorem kernel_isCovariantlyInvariant_of_deriv_inner_eq_zero
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    {t : ℝ}
    (hApos : ∀ x, (A t x).IsPositive)
    (Z : ∀ x, TangentSpace I x) (B : ∀ x, V x →L[ℝ] V x)
    (htime : ∀ x v, A t x v = 0 →
      inner ℝ (deriv (fun s => A s x) t v) v = 0)
    (hB : ∀ x v, A t x v = 0 → 0 ≤ inner ℝ (B x v) v)
    (hevolution : ∀ x,
      deriv (fun s => A s x) t =
        rawBundleEndomorphismConnLap (I := I) g cov (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V cov cov (fun y => A t y) x (Z x) + B x) :
    IsCovariantlyInvariantSubmoduleFamily cov (fun x => (A t x).ker) := by
  apply DifferentialGeometry.Analysis.Elliptic.kernel_isCovariantlyInvariant_of_laplacian_add_drift_nonpos_on_kernel
    g cov hcov (A t) hApos Z
  intro x v hv
  have heval := congrArg (fun Q : V x →L[ℝ] V x => inner ℝ (Q v) v) (hevolution x)
  simp only [add_apply, inner_add_left] at heval
  rw [htime x v hv] at heval
  have hn := hB x v hv
  simp only [add_apply, inner_add_left]
  linarith

theorem local_kernel_section_covariantDerivative_mem_and_reaction_inner_eq_zero
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    {t : ℝ} {x : M}
    (hA : ∀ y, (A t y : V y →ₗ[ℝ] V y).IsSymmetric)
    (hApos : (A t x).IsPositive)
    (Z : TangentSpace I x) (B : V x →L[ℝ] V x)
    (w : (p : ℝ × M) → V p.2) {U : Set (ℝ × M)}
    (hU : IsOpen U) (htxU : (t, x) ∈ U)
    (hw : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
      (fun p => TotalSpace.mk' F p (w p) : ℝ × M →
        TotalSpace F ((ContMDiffMap.snd :
          C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯) *ᵖ V)) U)
    (hwker : ∀ p ∈ U, A p.1 p.2 (w p) = 0)
    (hAt : DifferentiableAt ℝ (fun s => A s x) t)
    (hB : 0 ≤ inner ℝ (B (w (t, x))) (w (t, x)))
    (hevolution :
      deriv (fun s => A s x) t =
        rawBundleEndomorphismConnLap (I := I) g cov (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V cov cov (fun y => A t y) x Z + B) :
    (∀ Y : TangentSpace I x,
      cov (fun y => w (t, y)) x Y ∈ (A t x).ker) ∧
      inner ℝ (B (w (t, x))) (w (t, x)) = 0 := by
  let S : Set M := (fun y : M => (t, y)) ⁻¹' U
  have hS : IsOpen S := hU.preimage (continuous_const.prodMk continuous_id)
  have hxS : x ∈ S := htxU
  have hwslice : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
      (fun y => TotalSpace.mk' F y (w (t, y))) S :=
    contMDiffOn_fixed_time_of_contMDiffOn_pullback_section hw
      (fun y hy => hy)
  obtain ⟨w', hw'⟩ := exists_contMDiffSection_eqOn_nhd
    (I := I) (F := F) (V := V) (n := (⊤ : ℕ∞))
    (s := fun _ : Unit => fun y => w (t, y))
    (u := S) (fun _ => hwslice) hS hxS
  let w₀ : Cₛ^∞⟮I; F, V⟯ := w' ()
  have hw₀eq : ∀ᶠ y in 𝓝 x, w₀ y = w (t, y) := by
    filter_upwards [hw'] with y hy
    exact hy ()
  obtain ⟨O, hOSub, hO, hxO⟩ := mem_nhds_iff.mp hw₀eq
  let W := O ∩ S
  have hW : IsOpen W := hO.inter hS
  have hxW : x ∈ W := ⟨hxO, hxS⟩
  have hw₀ker : ∀ y ∈ W, A t y (w₀ y) = 0 := by
    intro y hy
    rw [hOSub hy.1]
    exact hwker (t, y) hy.2
  let J : Set ℝ := (fun s : ℝ => (s, x)) ⁻¹' U
  have hJ : IsOpen J := hU.preimage (continuous_id.prodMk continuous_const)
  have htJ : t ∈ J := htxU
  have hwtime : ContDiffOn ℝ ∞ (fun s : ℝ => (show V x from w (s, x))) J :=
    contDiffOn_fixed_spatial_of_contMDiffOn_pullback_section hU hw
      (fun s hs => hs)
  have hv : DifferentiableAt ℝ (fun s : ℝ => (show V x from w (s, x))) t :=
    (hwtime.contDiffAt (hJ.mem_nhds htJ)).differentiableAt (by simp)
  have hvker : ∀ᶠ s in 𝓝 t, A s x (w (s, x)) = 0 := by
    filter_upwards [hJ.mem_nhds htJ] with s hs
    exact hwker (s, x) hs
  have hv_eq : w (t, x) = w₀ x := (hw₀eq.self_of_nhds).symm
  have hB' : 0 ≤ inner ℝ (B (w₀ x)) (w₀ x) := by
    rwa [← hv_eq]
  have htime := inner_deriv_apply_eq_zero_of_eventually_mem_ker
    hAt hv hvker (hA x)
  rw [hv_eq] at htime
  have hmain := kernel_covariantDerivatives_mem_and_reaction_inner_eq_zero
    g cov hcov A hA hApos Z w₀ B hB' hW hxW hw₀ker htime hevolution
  have hcovEq : cov (fun y => w₀ y) x = cov (fun y => w (t, y)) x := by
    have hlocalDiff : MDiffAt (T% fun y : M => w (t, y)) x :=
      ((hwslice x hxS).contMDiffAt (hS.mem_nhds hxS)).mdifferentiableAt (by simp)
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      w₀.mdifferentiableAt hlocalDiff Filter.univ_mem hw₀eq
  constructor
  · intro Y
    by_cases hdim : Module.finrank ℝ E = 0
    · have hY : Y = 0 :=
        (finrank_zero_iff_forall_zero.mp (show
          Module.finrank ℝ (TangentSpace I x) = 0 by exact hdim)) Y
      rw [hY, map_zero]
      exact Submodule.zero_mem _
    let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    let e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
      fun i => smoothOrthoFrame (I := I) g x i x
    let P : Submodule ℝ (TangentSpace I x) :=
      (A t x).ker.comap (cov (fun y => w (t, y)) x).toLinearMap
    have he : ⊤ ≤ Submodule.span ℝ (Set.range e) :=
      (smoothOrtho_isLocal (I := I) g x).generating
        (mem_smoothOrthoFrameNeighborhood_self (I := I) (M := M) x)
    have hrange : Set.range e ⊆ P := by
      intro Z hZ
      obtain ⟨i, rfl⟩ := hZ
      change cov (fun y => w (t, y)) x (e i) ∈ (A t x).ker
      rw [← hcovEq]
      exact hmain.1 i
    have hspan : Submodule.span ℝ (Set.range e) ≤ P :=
      Submodule.span_le.mpr hrange
    exact hspan (he Submodule.mem_top)
  · simpa only [hv_eq] using hmain.2

private theorem exists_local_kernel_frame_covariantDerivative_mem_and_reaction_inner_eq_zero
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    {W : Set (ℝ × M)} (hW : IsOpen W)
    (hAspace : ContMDiffOnSpacetimeEndomorphism
      (I := I) (F := F) (V := V) (n := ∞)
      (fun t x => A t x) W)
    (k : ℕ) (hker : ∀ p ∈ W, Module.finrank ℝ (A p.1 p.2).ker = k)
    {t : ℝ} {x : M} (htxW : (t, x) ∈ W)
    (hA : ∀ y, (A t y : V y →ₗ[ℝ] V y).IsSymmetric)
    (hApos : (A t x).IsPositive)
    (Z : TangentSpace I x) (B : V x →L[ℝ] V x)
    (hAt : DifferentiableAt ℝ (fun s => A s x) t)
    (hB : ∀ v, A t x v = 0 → 0 ≤ inner ℝ (B v) v)
    (hevolution :
      deriv (fun s => A s x) t =
        rawBundleEndomorphismConnLap (I := I) g cov (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V cov cov (fun y => A t y) x Z + B) :
    ∃ (U : Set (ℝ × M)) (w : Fin k → (p : ℝ × M) → V p.2),
      IsOpen U ∧ (t, x) ∈ U ∧ U ⊆ W ∧
      (∀ p ∈ U, LinearIndependent ℝ (w · p)) ∧
      (∀ p ∈ U,
        Submodule.span ℝ (Set.range (w · p)) = (A p.1 p.2).ker) ∧
      (∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I)
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
        (fun p => TotalSpace.mk' F p (w i p) : ℝ × M →
          TotalSpace F ((ContMDiffMap.snd :
            C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯) *ᵖ V)) U) ∧
      ∀ i,
        (∀ Y : TangentSpace I x,
          cov (fun y => w i (t, y)) x Y ∈ (A t x).ker) ∧
        inner ℝ (B (w i (t, x))) (w i (t, x)) = 0 := by
  let c : C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯ := ContMDiffMap.snd
  let _ : TopologicalSpace (TotalSpace F (fun p : ℝ × M => V p.2)) := by
    change TopologicalSpace (TotalSpace F (c *ᵖ V)); infer_instance
  let _ : FiberBundle F (fun p : ℝ × M => V p.2) := by
    change FiberBundle F (c *ᵖ V); infer_instance
  let _ : VectorBundle ℝ F (fun p : ℝ × M => V p.2) := by
    change VectorBundle ℝ F (c *ᵖ V); infer_instance
  let _ : ContMDiffVectorBundle ∞ F (fun p : ℝ × M => V p.2)
      (𝓘(ℝ, ℝ).prod I) := by
    change ContMDiffVectorBundle ∞ F (c *ᵖ V) (𝓘(ℝ, ℝ).prod I); infer_instance
  have hAspace' : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p => TotalSpace.mk' (F →L[ℝ] F) p (A p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F)
          (fun p => V p.2 →L[ℝ] V p.2)) W := by
    simpa only [ContMDiffOnSpacetimeEndomorphism] using hAspace
  obtain ⟨U, w, hU, htxU, hUW, hw⟩ :=
    ContMDiffVectorSubbundle.exists_kernel_frameOn
      (I := 𝓘(ℝ, ℝ).prod I) (F₁ := F) (F₂ := F)
      (V₁ := fun p : ℝ × M => V p.2)
      (V₂ := fun p : ℝ × M => V p.2)
      (fun p : ℝ × M => A p.1 p.2) W hW hAspace' k hker
      (t, x) htxW
  refine ⟨U, w, hU, htxU, hUW, ?_, ?_, ?_, ?_⟩
  · exact fun p hp => hw.linearIndependent hp
  · exact fun p hp => hw.spans hp
  · exact hw.contMDiffOn
  · intro i
    have hwker : ∀ p ∈ U, A p.1 p.2 (w i p) = 0 := by
      intro p hp
      apply LinearMap.mem_ker.mp
      rw [← hw.spans hp]
      exact Submodule.subset_span (Set.mem_range_self i)
    exact local_kernel_section_covariantDerivative_mem_and_reaction_inner_eq_zero
      g cov hcov A hA hApos Z B (w i) hU htxU (hw.contMDiffOn i)
      hwker hAt (hB _ (hwker (t, x) htxU)) hevolution

theorem kernel_reaction_inner_eq_zero_of_constant_rank
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    {W : Set (ℝ × M)} (hW : IsOpen W)
    (hAspace : ContMDiffOnSpacetimeEndomorphism
      (I := I) (F := F) (V := V) (n := ∞)
      (fun t x => A t x) W)
    (k : ℕ) (hker : ∀ p ∈ W, Module.finrank ℝ (A p.1 p.2).ker = k)
    {t : ℝ} {x : M} (htxW : (t, x) ∈ W)
    (hA : ∀ y, (A t y : V y →ₗ[ℝ] V y).IsSymmetric)
    (hApos : (A t x).IsPositive)
    (Z : TangentSpace I x) (B : V x →L[ℝ] V x)
    (hAt : DifferentiableAt ℝ (fun s => A s x) t)
    (hB : ∀ v, A t x v = 0 → 0 ≤ inner ℝ (B v) v)
    (hevolution :
      deriv (fun s => A s x) t =
        rawBundleEndomorphismConnLap (I := I) g cov (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V cov cov (fun y => A t y) x Z + B) :
    ∀ v, A t x v = 0 → inner ℝ (B v) v = 0 := by
  let c : C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯ := ContMDiffMap.snd
  let _ : TopologicalSpace (TotalSpace F (fun p : ℝ × M => V p.2)) := by
    change TopologicalSpace (TotalSpace F (c *ᵖ V)); infer_instance
  let _ : FiberBundle F (fun p : ℝ × M => V p.2) := by
    change FiberBundle F (c *ᵖ V); infer_instance
  let _ : VectorBundle ℝ F (fun p : ℝ × M => V p.2) := by
    change VectorBundle ℝ F (c *ᵖ V); infer_instance
  let _ : ContMDiffVectorBundle ∞ F (fun p : ℝ × M => V p.2)
      (𝓘(ℝ, ℝ).prod I) := by
    change ContMDiffVectorBundle ∞ F (c *ᵖ V) (𝓘(ℝ, ℝ).prod I); infer_instance
  obtain ⟨U, w, hU, htxU, _, _, hwspan, hwsmooth, _⟩ :=
    exists_local_kernel_frame_covariantDerivative_mem_and_reaction_inner_eq_zero
      g cov hcov A hW hAspace k hker htxW hA hApos Z B hAt hB hevolution
  intro v hv
  have hvspan : v ∈ Submodule.span ℝ (Set.range (w · (t, x))) := by
    rw [hwspan (t, x) htxU]
    exact LinearMap.mem_ker.mpr hv
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hvspan
  let z : (p : ℝ × M) → V p.2 := fun p => ∑ i, a i • w i p
  have hzsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
      (fun p => TotalSpace.mk' F p (z p) : ℝ × M →
        TotalSpace F (fun p : ℝ × M => V p.2)) U := by
    refine ContMDiffOn.sum_section (V := fun p : ℝ × M => V p.2)
      (s := Finset.univ) ?_
    intro i hi
    have hwi : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
        (fun p => TotalSpace.mk' F p (w i p) : ℝ × M →
          TotalSpace F (fun p : ℝ × M => V p.2)) U := hwsmooth i
    exact hwi.const_smul_section
  have hzker : ∀ p ∈ U, A p.1 p.2 (z p) = 0 := by
    intro p hp
    change A p.1 p.2 (∑ i, a i • w i p) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [map_smul]
    have hiKer : w i p ∈ (A p.1 p.2).ker := by
      rw [← hwspan p hp]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hiZero := LinearMap.mem_ker.mp hiKer
    change A p.1 p.2 (w i p) = 0 at hiZero
    rw [hiZero, smul_zero]
  have hzpoint : z (t, x) = v := ha
  have hzrigid :=
    local_kernel_section_covariantDerivative_mem_and_reaction_inner_eq_zero
      g cov hcov A hA hApos Z B z hU htxU hzsmooth hzker hAt
      (hB _ (hzker (t, x) htxU)) hevolution
  simpa only [hzpoint] using hzrigid.2

theorem kernel_isCovariantlyInvariant_of_constant_rank
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    {W : Set (ℝ × M)} (hW : IsOpen W)
    (hAspace : ContMDiffOnSpacetimeEndomorphism
      (I := I) (F := F) (V := V) (n := ∞)
      (fun t x => A t x) W)
    (k : ℕ) (hker : ∀ p ∈ W, Module.finrank ℝ (A p.1 p.2).ker = k)
    {t : ℝ} (htW : ∀ x, (t, x) ∈ W)
    (hA : ∀ x, (A t x : V x →ₗ[ℝ] V x).IsSymmetric)
    (hApos : ∀ x, (A t x).IsPositive)
    (Z : ∀ x, TangentSpace I x) (B : ∀ x, V x →L[ℝ] V x)
    (hAt : ∀ x, DifferentiableAt ℝ (fun s => A s x) t)
    (hB : ∀ x v, A t x v = 0 → 0 ≤ inner ℝ (B x v) v)
    (hevolution : ∀ x,
      deriv (fun s => A s x) t =
        rawBundleEndomorphismConnLap (I := I) g cov (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V cov cov (fun y => A t y) x (Z x) + B x) :
    IsCovariantlyInvariantSubmoduleFamily cov (fun x => (A t x).ker) := by
  have hderivKer : ∀ (x : M) (Y : TangentSpace I x) (v : V x),
      v ∈ (A t x).ker →
        (HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov (fun y => A t y) x Y) v = 0 := by
    intro x Y v hv
    obtain ⟨U, w, hU, htxU, _, _, hwspan, hwsmooth, hwderiv⟩ :=
      exists_local_kernel_frame_covariantDerivative_mem_and_reaction_inner_eq_zero
        g cov hcov A hW hAspace k hker (htW x) hA (hApos x)
          (Z x) (B x) (hAt x) (hB x) (hevolution x)
    have hvspan : v ∈ Submodule.span ℝ (Set.range (w · (t, x))) := by
      rw [hwspan (t, x) htxU]
      exact hv
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hvspan
    rw [← ha, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [map_smul]
    suffices (HomConnectionGen.homBundleCovariantDerivativeGen
        I M F V F V cov cov (fun y => A t y) x Y) (w i (t, x)) = 0 by
      rw [this, smul_zero]
    let S : Set M := (fun y : M => (t, y)) ⁻¹' U
    have hS : IsOpen S := hU.preimage (continuous_const.prodMk continuous_id)
    have hxS : x ∈ S := htxU
    have hwslice : ContMDiffOn I (I.prod (modelWithCornersSelf ℝ F)) ∞
        (fun y => TotalSpace.mk' F y (w i (t, y))) S :=
      contMDiffOn_fixed_time_of_contMDiffOn_pullback_section (hwsmooth i)
        (fun y hy => hy)
    obtain ⟨w', hw'⟩ := exists_contMDiffSection_eqOn_nhd
      (I := I) (F := F) (V := V) (n := (⊤ : ℕ∞))
      (s := fun _ : Unit => fun y => w i (t, y))
      (u := S) (fun _ => hwslice) hS hxS
    let w₀ : Cₛ^∞⟮I; F, V⟯ := w' ()
    have hw₀eq : ∀ᶠ y in nhds x, w₀ y = w i (t, y) := by
      filter_upwards [hw'] with y hy
      exact hy ()
    obtain ⟨O, hOSub, hO, hxO⟩ := mem_nhds_iff.mp hw₀eq
    let Q := O ∩ S
    have hQ : IsOpen Q := hO.inter hS
    have hxQ : x ∈ Q := ⟨hxO, hxS⟩
    have hw₀ker : ∀ y ∈ Q, A t y (w₀ y) = 0 := by
      intro y hy
      rw [hOSub hy.1]
      apply LinearMap.mem_ker.mp
      rw [← hwspan (t, y) hy.2]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hcovEq : cov (fun y => w₀ y) x = cov (fun y => w i (t, y)) x := by
      have hlocalDiff : MDiffAt (T% fun y : M => w i (t, y)) x :=
        ((hwslice x hxS).contMDiffAt (hS.mem_nhds hxS)).mdifferentiableAt (by simp)
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        w₀.mdifferentiableAt hlocalDiff Filter.univ_mem hw₀eq
    have happly :=
      HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_eventually_mem_ker
        cov (A t) w₀ hQ hxQ hw₀ker Y
    have hcovmem : cov (fun y => w₀ y) x Y ∈ (A t x).ker := by
      rw [hcovEq]
      exact (hwderiv i).1 Y
    have hcovzero : A t x (cov (w₀ : (y : M) → V y) x Y) = 0 :=
      LinearMap.mem_ker.mp hcovmem
    rw [hcovzero, neg_zero] at happly
    simpa only [hw₀eq.self_of_nhds] using happly
  intro s U hU hs x hx Y
  have hsKer : ∀ y ∈ U, A t y (s y) = 0 := by
    intro y hy
    exact LinearMap.mem_ker.mp (hs y hy)
  have happly :=
    HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_eventually_mem_ker
      cov (A t) s hU hx hsKer Y
  have hzero := hderivKer x Y (s x) (hs x hx)
  rw [hzero] at happly
  apply LinearMap.mem_ker.mpr
  exact neg_eq_zero.mp happly.symm

omit [IsContMDiffRiemannianBundle I 1 F V] in
theorem kernel_motion_of_isCovariantlyInvariant
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞]
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (S : ∀ x, Submodule ℝ (V x))
    {t : ℝ}
    (hS : IsCovariantlyInvariantSubmoduleFamily cov S)
    (hSker : ∀ y, S y = (A t y).ker)
    (hAk : ∀ y v, v ∈ S y → A t y v = 0)
    (w : (p : ℝ × M) → V p.2) {U : Set (ℝ × M)}
    (hU : IsOpen U) {x : M} (htxU : (t, x) ∈ U)
    (hw : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
      (fun p => TotalSpace.mk' F p (w p) : ℝ × M →
        TotalSpace F ((ContMDiffMap.snd :
          C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯) *ᵖ V)) U)
    (hwker : ∀ p ∈ U, A p.1 p.2 (w p) = 0)
    (hAt : DifferentiableAt ℝ (fun s => A s x) t)
    (Z : TangentSpace I x) (B : V x →L[ℝ] V x)
    (hevolution :
      deriv (fun s => A s x) t =
        rawBundleEndomorphismConnLap (I := I) g cov (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V cov cov (fun y => A t y) x Z + B) :
    A t x (deriv (fun s => w (s, x)) t) = -B (w (t, x)) ∧
      deriv (fun s => A s x) t (w (t, x)) = B (w (t, x)) := by
  let Sx : Set M := (fun y : M => (t, y)) ⁻¹' U
  have hSx : IsOpen Sx := hU.preimage (continuous_const.prodMk continuous_id)
  have hxSx : x ∈ Sx := htxU
  have hwslice : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
      (fun y => TotalSpace.mk' F y (w (t, y)) : M → TotalSpace F V) Sx :=
    contMDiffOn_fixed_time_of_contMDiffOn_pullback_section hw
      (fun y hy => hy)
  obtain ⟨w₀, hw₀⟩ := exists_contMDiffSection_eqOn_nhd
    (I := I) (F := F) (V := V) (n := (⊤ : ℕ∞))
    (s := fun _ : Unit => fun y => w (t, y))
    (u := Sx) (fun _ => hwslice) hSx hxSx
  let w₁ : Cₛ^∞⟮I; F, V⟯ := w₀ ()
  have hw₁eq : ∀ᶠ y in 𝓝 x, w₁ y = w (t, y) := by
    filter_upwards [hw₀] with y hy
    exact hy ()
  obtain ⟨O, hOSub, hO, hxO⟩ := mem_nhds_iff.mp hw₁eq
  let U₁ := O ∩ Sx
  have hU₁ : IsOpen U₁ := hO.inter hSx
  have hxU₁ : x ∈ U₁ := ⟨hxO, hxSx⟩
  have hw₁ker : ∀ y ∈ U₁, w₁ y ∈ S y := by
    intro y hy
    have hyzero : A t y (w₁ y) = 0 := by
      rw [hOSub hy.1]
      exact hwker (t, y) hy.2
    rw [hSker y]
    exact LinearMap.mem_ker.mpr hyzero
  have hLapw : rawBundleConnLap (I := I) g cov (fun y => w₁ y) x ∈ S x :=
    rawBundleConnLap_mem_of_isCovariantlyInvariant g cov S hS w₁ hU₁ hxU₁ hw₁ker
  have hAlapw : A t x
      (rawBundleConnLap (I := I) g cov (fun y => w₁ y) x) = 0 :=
    hAk x _ hLapw
  have hAw : ∀ y ∈ U₁, A t y (w₁ y) = 0 := by
    intro y hy
    exact hAk y (w₁ y) (hw₁ker y hy)
  have hLapA : rawBundleEndomorphismConnLap (I := I) g cov
      (fun y => A t y) x (w₁ x) = 0 :=
    rawBundleEndomorphismConnLap_apply_eq_zero_of_isCovariantlyInvariant
      g cov (A := A t) w₁ S hS hAk hU₁ hxU₁ hw₁ker
  have hdrift :
      (HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov (A t) x
          Z) (w₁ x) = 0 := by
    rw [HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_eventually_mem_ker
      cov (A t) w₁ hU₁ hxU₁ hAw]
    have hcovwS : cov (fun y => w₁ y) x Z ∈ S x :=
      hS.covariantDerivative_mem w₁ hU₁ hw₁ker hxU₁ Z
    have hAcov : A t x (cov (fun y => w₁ y) x Z) = 0 :=
      hAk x _ hcovwS
    rw [hAcov]
    simp
  have hwtime0 := contDiffOn_fixed_spatial_of_contMDiffOn_pullback_section
      (w := w) (x := x) (s := (fun s : ℝ => (s, x)) ⁻¹' U) hU hw
      (fun s hs => hs)
  have hwtime : ContDiffOn ℝ ∞
      (fun s : ℝ => (show V x from w (s, x)))
      ((fun s : ℝ => (s, x)) ⁻¹' U) := by
    simpa [Set.preimage] using hwtime0
  have htJ : t ∈ (fun s : ℝ => (s, x)) ⁻¹' U := htxU
  have hwderiv : DifferentiableAt ℝ
      (fun s : ℝ => (show V x from w (s, x))) t :=
    (hwtime.contDiffAt
      ((hU.preimage (continuous_id.prodMk continuous_const)).mem_nhds htxU)
      |>.differentiableAt (by simp))
  have hzero : ∀ᶠ s in 𝓝 t, A s x (w (s, x)) = 0 := by
    filter_upwards [((hU.preimage (continuous_id.prodMk continuous_const)).mem_nhds htxU)]
      with s hs
    exact hwker (s, x) hs
  have hprod := hasDerivAt_apply_eq_zero_of_eventually_eq_zero
    hAt.hasDerivAt hwderiv.hasDerivAt hzero
  have hw₀eq : w₁ x = w (t, x) := hw₁eq.self_of_nhds
  have hderivA : deriv (fun s => A s x) t (w (t, x)) = B (w (t, x)) := by
    have hev := congrArg (fun Q : V x →L[ℝ] V x => Q (w (t, x))) hevolution
    rw [← hw₀eq] at hev
    have hev' : deriv (fun s => A s x) t (w₁ x) = B (w₁ x) := by
      simpa only [map_add, add_apply, hLapA, hdrift, zero_apply, zero_add,
        add_zero] using hev
    simpa only [hw₀eq] using hev'
  constructor
  · rw [← hw₀eq]
    have hprod' := hprod
    rw [hderivA] at hprod'
    simpa only [hw₀eq] using eq_neg_of_add_eq_zero_right hprod'
  · exact hderivA

end PositiveSystem

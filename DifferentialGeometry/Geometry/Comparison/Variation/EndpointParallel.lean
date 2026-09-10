import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Construction.Endpoint
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Construction.Smoothness

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
lemma chartRepAt_differentiableAt_of_total_contMDiffAt
    {gamma : ℝ → M} {V : ∀ t, TangentSpace I (gamma t)} {t : ℝ}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2
      (fun s : ℝ ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma s) (V s) : TangentBundle I M)) t) :
    DifferentiableAt ℝ (chartRepAt (I := I) gamma V t) t := by
  let F : ℝ → TangentBundle I M := fun s ↦
    TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (gamma s) (V s)
  have hAt := Bundle.contMDiffAt_totalSpace.mp hV
  have hbase := hAt.1
  have hfiber := hAt.2
  have hmem :
      gamma t ∈ (trivializationAt E (TangentSpace I) (gamma t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (gamma t)
  have hpre :
      gamma ⁻¹' (trivializationAt E (TangentSpace I) (gamma t)).baseSet ∈ 𝓝 t :=
    hbase.continuousAt.preimage_mem_nhds
      ((trivializationAt E (TangentSpace I) (gamma t)).open_baseSet.mem_nhds hmem)
  have heq :
      (fun s : ℝ ↦
        ((trivializationAt E (TangentSpace I) (gamma t)) (F s)).2)
        =ᶠ[𝓝 t] chartRepAt (I := I) gamma V t := by
    filter_upwards [hpre] with s hs
    rw [chartRepAt_apply]
    simp only [F, TotalSpace.mk']
    rw [(trivializationAt E (TangentSpace I) (gamma t)).continuousLinearMapAt_apply
      (R := ℝ)]
    rw [(trivializationAt E (TangentSpace I) (gamma t)).coe_linearMapAt_of_mem hs]
  have hcoord : ContDiffAt ℝ 2
      (fun s : ℝ ↦
        ((trivializationAt E (TangentSpace I) (gamma t)) (F s)).2) t :=
    contMDiffAt_iff_contDiffAt.mp hfiber
  exact (hcoord.differentiableAt (by norm_num)).congr_of_eventuallyEq heq.symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
lemma ContMDiffAt.smul_tangentBundleAlong
    {gamma : ℝ → M} {a : ℝ → ℝ}
    {V : ∀ t, TangentSpace I (gamma t)} {t : ℝ} {n : WithTop ℕ∞}
    (ha : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n a t)
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n
      (fun s : ℝ ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma s) (V s) : TangentBundle I M)) t) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n
      (fun s : ℝ ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma s) (a s • V s) : TangentBundle I M)) t := by
  rw [Bundle.contMDiffAt_totalSpace] at hV ⊢
  refine ⟨hV.1, ?_⟩
  let e := trivializationAt E (TangentSpace I) (gamma t)
  apply (ha.smul hV.2).congr_of_eventuallyEq
  have he : ∀ᶠ s in 𝓝 t, gamma s ∈ e.baseSet := by
    apply hV.1.continuousAt
    exact e.open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (gamma t))
  filter_upwards [he] with s hs
  change (e ⟨gamma s, a s • V s⟩).2 = a s • (e ⟨gamma s, V s⟩).2
  exact (e.linear ℝ hs).map_smul (a s) (V s)

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_smooth_parallel_unit_field_with_terminal
    (g : SmoothRiemannianMetric I M)
    (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    (L : ℝ) (hL : 0 < L)
    (vL : TangentSpace I (gamma L))
    (hvL : g.inner (gamma L) vL vL = 1) :
    ∃ (Gamma : ℝ → M) (V : ∀ t, TangentSpace I (Gamma t)),
      ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
        (fun t ↦ (TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _)) (Gamma t) (V t) :
            TangentBundle I M)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, Gamma t = gamma t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, Gamma =ᶠ[𝓝 t] gamma) ∧
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (Gamma L) (V L) : TangentBundle I M) =
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma L) vL : TangentBundle I M) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) Gamma V t) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g Gamma V t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L,
        g.inner (Gamma t) (V t) (V t) = 1) ∧
      ∃ W : ∀ t, TangentSpace I (Gamma t),
        ContMDiff 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
          (fun t ↦ (TotalSpace.mk' E
            (E := (TangentSpace I : M → Type _)) (Gamma t) (W t) :
              TangentBundle I M)) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) L, W t = (t / L) • V t) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) L,
          covDerivAlong (I := I) g Gamma W t = (1 / L) • V t) ∧
        ∃ K : Set (TangentBundle I M), IsCompact K ∧
          ∀ t : ℝ,
            (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
              (Gamma t) (W t) : TangentBundle I M) ∈ K := by
  classical
  let hgamma2 : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma :=
    hgamma.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  let e := parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma2 hL
  let v0 : TangentSpace I (gamma 0) := e.symm vL
  obtain ⟨delta, hdelta, P, hP0, hPdiff, hPpar, hPsmooth⟩ :=
    parallelTransport_section_contMDiffOn_Ioo (I := I) g gamma hgamma hL v0
  have hIcc_sub : Set.Icc (0 : ℝ) L ⊆ Set.Ioo (-delta) (L + delta) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  let Q : ∀ t, TangentSpace I (gamma t) :=
    parallelTransportSectionOnIcc (I := I) g gamma hgamma2 hL v0
  have hPQ : ∀ t ∈ Set.Icc (0 : ℝ) L, P t = Q t := by
    apply parallel_transport_unique_of_eq_at_point (I := I) g gamma
      (N := 2) le_rfl hgamma2 P Q
    · intro t ht
      exact hPdiff t (hIcc_sub ht)
    · intro t ht
      exact parallelTransportSectionOnIcc_differentiableAt
        (I := I) g gamma hgamma2 hL v0 ht
    · intro t ht
      exact hPpar t (hIcc_sub ht)
    · intro t ht
      exact parallelTransportSectionOnIcc_covDerivAlong
        (I := I) g gamma hgamma2 hL v0 ht
    · exact ⟨le_rfl, hL.le⟩
    · exact hP0.trans
        (parallelTransportSectionOnIcc_initial
          (I := I) g gamma hgamma2 hL v0).symm
  have hPL : P L = vL := by
    rw [hPQ L ⟨hL.le, le_rfl⟩]
    change e v0 = vL
    exact e.apply_symm_apply vL
  have hPunit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (gamma t) (P t) (P t) = 1 := by
    intro t ht
    have hconst := parallel_transport_preserves_inner_product
      (I := I) g gamma (N := 2) le_rfl hgamma2 P P
      (fun s hs ↦ hPdiff s (hIcc_sub hs))
      (fun s hs ↦ hPdiff s (hIcc_sub hs))
      (fun s hs ↦ hPpar s (hIcc_sub hs))
      (fun s hs ↦ hPpar s (hIcc_sub hs))
    have ht0 := hconst t ht
    have hL0 := hconst L ⟨hL.le, le_rfl⟩
    have hinit : g.inner (gamma 0) (P 0) (P 0) = 1 := by
      rw [← hL0, hPL, hvL]
    exact ht0.trans hinit
  obtain ⟨rho, hrho, hrho_id, hrho_deriv, hrho_range⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp
      (-delta / 4) (L + delta / 4) (delta / 4)
      (by linarith) (by positivity)
  have hrho_mem : ∀ t : ℝ, rho t ∈ Set.Ioo (-delta) (L + delta) := by
    intro t
    have ht := hrho_range t
    constructor <;> linarith [ht.1, ht.2, hdelta]
  have hcore : Set.Icc (0 : ℝ) L ⊆
      Set.Icc (-delta / 4) (L + delta / 4) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2, hdelta]
  let Gamma : ℝ → M := fun t ↦ gamma (rho t)
  let V : ∀ t, TangentSpace I (Gamma t) := fun t ↦ P (rho t)
  have hrhoM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ rho := by
    rwa [contMDiff_iff_contDiff]
  have htotal : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (Gamma t) (V t) :
          TangentBundle I M)) := by
    have hcomp := hPsmooth.comp (s := Set.univ) hrhoM.contMDiffOn
      (fun t _ht ↦ hrho_mem t)
    rw [contMDiffOn_univ] at hcomp
    change ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      ((fun t ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (gamma t) (P t) :
          TangentBundle I M)) ∘ rho)
    exact hcomp
  have hGamma : ∀ t ∈ Set.Icc (0 : ℝ) L, Gamma t = gamma t := by
    intro t ht
    simp only [Gamma, hrho_id t (hcore ht)]
  have hGammaGerm : ∀ t ∈ Set.Icc (0 : ℝ) L, Gamma =ᶠ[𝓝 t] gamma := by
    intro t ht
    have htOpen : t ∈ Set.Ioo (-delta / 4) (L + delta / 4) := by
      constructor <;> linarith [ht.1, ht.2, hdelta]
    filter_upwards [isOpen_Ioo.mem_nhds htOpen] with s hs
    change gamma (rho s) = gamma s
    rw [hrho_id s ⟨hs.1.le, hs.2.le⟩]
  have hterminal :
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (Gamma L) (V L) : TangentBundle I M) =
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma L) vL : TangentBundle I M) := by
    change
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma (rho L)) (P (rho L)) : TangentBundle I M) =
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma L) vL : TangentBundle I M)
    rw [show rho L = L from hrho_id L (hcore ⟨hL.le, le_rfl⟩)]
    exact congrArg
      (fun w : TangentSpace I (gamma L) ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma L) w : TangentBundle I M)) hPL
  have hVdiff : ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) Gamma V t) t := by
    intro t _ht
    exact chartRepAt_differentiableAt_of_total_contMDiffAt (I := I)
      ((htotal.contMDiffAt (x := t)).of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
  have hVpar : ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g Gamma V t = 0 := by
    intro t ht
    have hcomp := covDerivAlong_comp (I := I) g gamma P rho t
      (hgamma.mdifferentiableAt (by simp))
      (hPdiff (rho t) (hrho_mem t))
      ((hrho.differentiable (by simp)) t)
    have hPzero := hPpar (rho t) (hrho_mem t)
    rw [hPzero, smul_zero] at hcomp
    simpa only [Gamma, V] using hcomp
  have hVunit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (Gamma t) (V t) (V t) = 1 := by
    intro t ht
    change g.inner (gamma (rho t)) (P (rho t)) (P (rho t)) = 1
    rw [show rho t = t from hrho_id t (hcore ht)]
    exact hPunit t ht
  let scalar : ℝ → ℝ := fun t ↦ rho t / L
  let W : ∀ t, TangentSpace I (Gamma t) := fun t ↦ scalar t • V t
  have hscalar : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ scalar := by
    exact hrhoM.div_const L
  have hWtotalInf : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (Gamma t) (W t) :
          TangentBundle I M)) := by
    exact hscalar.smul_bundle htotal
  have hWtotal : ContMDiff 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      (fun t ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (Gamma t) (W t) :
          TangentBundle I M)) :=
    hWtotalInf.of_le
      (WithTop.coe_le_coe.mpr (le_top : (8 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hWradial : ∀ t ∈ Set.Icc (0 : ℝ) L, W t = (t / L) • V t := by
    intro t ht
    change (rho t / L) • V t = (t / L) • V t
    rw [hrho_id t (hcore ht)]
  have hWcov : ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g Gamma W t = (1 / L) • V t := by
    intro t ht
    have hscalarDeriv : HasDerivAt scalar (1 / L) t := by
      change HasDerivAt (fun s : ℝ ↦ rho s / L) (1 / L) t
      convert (hrho_deriv t (hcore ht)).div_const L using 1
    have hcov := covDerivAlong_smulFun (I := I) g Gamma scalar V t
      hscalarDeriv.differentiableAt (hVdiff t ht)
    rw [hscalarDeriv.deriv, hVpar t ht, smul_zero, add_zero] at hcov
    simpa only [W] using hcov
  let carrierMap : ℝ → TangentBundle I M := fun s ↦
    (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
      (gamma s) ((s / L) • P s) : TangentBundle I M)
  let carrier : Set (TangentBundle I M) :=
    carrierMap '' Set.Icc (-delta / 2) (L + delta / 2)
  have hcarrierSub :
      Set.Icc (-delta / 2) (L + delta / 2) ⊆
        Set.Ioo (-delta) (L + delta) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2, hdelta]
  have hcarrierSmooth : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞ carrierMap
      (Set.Icc (-delta / 2) (L + delta / 2)) := by
    have hcoeff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun s : ℝ ↦ s / L) :=
      contMDiff_id.div_const L
    intro s hs
    have hPat := (hPsmooth s (hcarrierSub hs)).contMDiffAt
      (isOpen_Ioo.mem_nhds (hcarrierSub hs))
    exact ContMDiffAt.smul_tangentBundleAlong (I := I)
      hcoeff.contMDiffAt hPat |>.contMDiffWithinAt
  have hcarrierCompact : IsCompact carrier :=
    isCompact_Icc.image_of_continuousOn hcarrierSmooth.continuousOn
  have hWmem : ∀ t : ℝ,
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (Gamma t) (W t) : TangentBundle I M) ∈ carrier := by
    intro t
    refine ⟨rho t, ?_, ?_⟩
    · have ht := hrho_range t
      constructor <;> linarith [ht.1, ht.2]
    rfl
  exact ⟨Gamma, V, htotal, hGamma, hGammaGerm, hterminal, hVdiff, hVpar, hVunit,
    W, hWtotal, hWradial, hWcov, carrier, hcarrierCompact, hWmem⟩

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

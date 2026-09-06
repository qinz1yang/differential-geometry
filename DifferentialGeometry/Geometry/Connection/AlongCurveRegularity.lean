import DifferentialGeometry.Geometry.Connection.AlongCurve
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem contMDiffAt_curve_velocity {γ : ℝ → M} {t₀ : ℝ} {m n : ℕ∞ω}
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t₀) (hmn : m + 1 ≤ n) :
    ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) m
      (fun t => (⟨γ t, mfderiv 𝓘(ℝ, ℝ) I γ t
        ((NormedSpace.fromTangentSpace t).symm 1)⟩ : TangentBundle I M)) t₀ := by
  have hD := hγ.mfderiv_const hmn
  have hv : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) m
      (fun t => (⟨t, (NormedSpace.fromTangentSpace t).symm 1⟩ :
        TangentBundle 𝓘(ℝ, ℝ) ℝ)) t₀ := by
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    convert (contMDiffAt_const (c := (1 : ℝ)) :
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) m (fun _ : ℝ => (1 : ℝ)) t₀) using 1
    funext t
    simp only [TangentBundle.trivializationAt_apply, mfld_simps, chartAt_self_eq,
      fderivWithin_univ, fderiv_id]
    rfl
  exact ContMDiffAt.clm_apply_of_inCoordinates
    (F₁ := ℝ) (E₁ := TangentSpace 𝓘(ℝ, ℝ))
    (F₂ := E) (E₂ := TangentSpace I)
    (b₁ := id) (b₂ := γ) (ϕ := fun t => mfderiv 𝓘(ℝ, ℝ) I γ t)
    hD hv (hγ.of_le (le_self_add.trans hmn))

theorem contMDiffAt_derivAlongWithin
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {s : Set ℝ} {t₀ : ℝ}
    {m : ℕ∞} {n : ℕ∞ω} (hs : s ∈ 𝓝 t₀)
    (hZ : ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) n
      (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) t₀)
    (hmn : (m : ℕ∞ω) + 1 ≤ n) :
    ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) m
      (fun t => (⟨γ t, cov.derivAlongWithin γ Z s t⟩ : TotalSpace F V)) t₀ := by
  have hm : (m : ℕ∞ω) ≤ n := le_self_add.trans hmn
  have hone : (1 : ℕ∞ω) ≤ n := (le_add_of_nonneg_left (show (0 : ℕ∞ω) ≤ m from zero_le)).trans hmn
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t₀ :=
    (contMDiff_proj V).contMDiffAt.comp t₀ hZ
  let e := trivializationAt F V (γ t₀)
  have he : γ t₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V (γ t₀)
  have hbase : ∀ᶠ t in 𝓝 t₀, γ t ∈ e.baseSet :=
    hγ.continuousAt (e.open_baseSet.mem_nhds he)
  let z : ℝ → F := fun t => e.continuousLinearMapAt ℝ (γ t) (Z t)
  have hmi : (m : ℕ∞ω) + 1 ≤ ∞ := by
    exact_mod_cast (le_top : m + 1 ≤ (⊤ : ℕ∞))
  have : ContMDiffVectorBundle ((m : ℕ∞ω) + 1) F V I :=
    ContMDiffVectorBundle.of_le hmi
  have hz : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ((m : ℕ∞ω) + 1) z t₀ := by
    have h := (e.contMDiffAt_iff (e.mem_source.mpr he)).mp (hZ.of_le hmn) |>.2
    apply h.congr_of_eventuallyEq
    filter_upwards [hbase] with t ht
    exact e.continuousLinearMapAt_apply_of_mem ℝ ht (Z t)
  have hdz : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) m (deriv z) t₀ :=
    (hz.contDiffAt.derivWithin le_rfl).contMDiffAt
  have hv := contMDiffAt_curve_velocity hγ hmn
  have hA : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F →L[ℝ] F) m
      (fun t => cov.connectionForm e (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t ((NormedSpace.fromTangentSpace t).symm 1))) t₀ :=
    ((cov.contMDiffOn_connectionForm hcov e).contMDiffAt
      ((e.open_baseSet.preimage
        (FiberBundle.continuous_proj E (TangentSpace I))).mem_nhds he)).of_le
        (by exact_mod_cast (le_top : m ≤ (⊤ : ℕ∞))) |>.comp t₀ hv
  have hsum := hdz.add (hA.clm_apply (hz.of_le le_self_add))
  have h := (e.contMDiffOn_symm.contMDiffAt
    (e.open_target.mem_nhds (e.mem_target.mpr he))).comp t₀ ((hγ.of_le hm).prodMk hsum)
  have hZnear : ∀ᶠ t in 𝓝 t₀, MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) t :=
    ((contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp (hZ.of_le hone)).mono
      (fun _ ht => ht.mdifferentiableAt (by simp))
  apply h.congr_of_eventuallyEq
  filter_upwards [hbase, hZnear, eventually_mem_nhds_iff.mpr hs] with t ht hZt hst
  rw [cov.derivAlongWithin_eq e ht hZt.mdifferentiableWithinAt,
    derivWithin_of_mem_nhds hst, mfderivWithin_of_mem_nhds hst]
  rw [e.symmL_apply ht, e.mk_symm ht]
  rfl

end CovariantDerivative

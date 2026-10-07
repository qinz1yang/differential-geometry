import DifferentialGeometry.Geometry.Comparison.Variation.Field.JointRealization
import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

/-- A common time clamp extends the whole linear family, preserving its joint
germ near the interval. Thus locally defined adapted fields need no additional
global extension hypothesis. -/
theorem exists_joint_variation_of_linear_fields_on
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (A : (t : ℝ) → P →L[ℝ] TangentSpace I (gamma t))
    {a b : ℝ} (hab : a < b) {J : Set ℝ} (hJ : IsOpen J)
    (hseg : Icc a b ⊆ J)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I (8 : ℕ) gamma J)
    (hA : ∀ z : P, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      (fun t => (⟨gamma t, A t z⟩ : TangentBundle I M)) J) :
    ∃ f : P × ℝ → M,
      ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) f ∧
      (∀ t ∈ Icc a b, (fun r => f (0, r)) =ᶠ[𝓝 t] gamma) ∧
      (∀ t ∈ Icc a b,
        Filter.EventuallyEq (β := P →L[ℝ] E) (𝓝 t)
          (fun r => (mfderiv 𝓘(ℝ, P) I (fun z => f (z, r)) 0 : P →L[ℝ] E))
          (fun r => (A r : P →L[ℝ] E))) ∧
      (∀ t ∈ Icc a b, A t = 0 → ∀ z, f (z, t) = gamma t) ∧
      ∀ t ∈ Icc a b, ∀ᶠ z in 𝓝 ((0 : P), t),
        A z.2 z.1 ∈ expDomain (I := I) g (gamma z.2) ∧
          f z = expMap (I := I) g (gamma z.2) (A z.2 z.1) := by
  obtain ⟨rho, lo, hi, hlo, hhi, hrho, hrhoId, _hrhoDeriv, hrange⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp_range_subset hJ hab hseg
  let gamma' : ℝ → M := gamma ∘ rho
  let A' : (t : ℝ) → P →L[ℝ] TangentSpace I (gamma' t) := fun t => A (rho t)
  have hrho8 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (8 : ℕ) rho :=
    (hrho.of_le (WithTop.coe_le_coe.mpr le_top)).contMDiff
  have hgamma' : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) gamma' :=
    hgamma.comp_contMDiff hrho8 hrange
  have hA' (z : P) : ContMDiff 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      (fun t => (⟨gamma' t, A' t z⟩ : TangentBundle I M)) :=
    (hA z).comp_contMDiff hrho8 hrange
  obtain ⟨f, U, hf, hUopen, hUzero, hfzero, hjet, hfix, hexp⟩ :=
    exists_joint_variation_of_linear_fields g gamma' A' lo hi hgamma' hA'
  have hlohi : lo ≤ hi := (hlo.trans (hab.trans hhi)).le
  have hmem (t : ℝ) (ht : t ∈ Icc a b) : t ∈ Ioo lo hi :=
    ⟨hlo.trans_le ht.1, ht.2.trans_lt hhi⟩
  have hrhoGerm (t : ℝ) (ht : t ∈ Icc a b) : rho =ᶠ[𝓝 t] id := by
    filter_upwards [isOpen_Ioo.mem_nhds (hmem t ht)] with r hr
    exact hrhoId (Ioo_subset_Icc_self hr)
  refine ⟨f, hf, ?_, ?_, ?_, ?_⟩
  · intro t ht
    filter_upwards [hrhoGerm t ht] with r hr
    rw [hfzero]
    change gamma (rho r) = gamma r
    simpa only [id_eq] using congrArg gamma hr
  · intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds (hmem t ht)] with r hr
    have hr' : r ∈ uIcc lo hi := by
      rw [uIcc_of_le hlohi]
      exact Ioo_subset_Icc_self hr
    rw [hjet r hr']
    change (A (rho r) : P →L[ℝ] E) = (A r : P →L[ℝ] E)
    let Amodel : ℝ → P →L[ℝ] E := fun s => A s
    exact congrArg Amodel (show rho r = r from hrhoId (Ioo_subset_Icc_self hr))
  · intro t ht hAt z
    have hrhot : rho t = t := (hrhoGerm t ht).self_of_nhds
    have hA't : A' t = 0 := by
      change A (rho t) = 0
      rw [hrhot]
      exact hAt
    rw [hfix t hA't z]
    change gamma (rho t) = gamma t
    rw [hrhot]
  · intro t ht
    have ht' : t ∈ uIcc lo hi := by
      rw [uIcc_of_le hlohi]
      exact Ioo_subset_Icc_self (hmem t ht)
    have hId := (hrhoGerm t ht).comp_tendsto
      (continuous_snd.continuousAt : ContinuousAt (Prod.snd : P × ℝ → ℝ) (0, t))
    filter_upwards [hUopen.mem_nhds (hUzero t ht'), hId] with z hz hr
    have hh := hexp z hz
    have hrho : rho z.2 = z.2 := hr
    let Pclock : ℝ → Prop := fun r =>
      A r z.1 ∈ expDomain (I := I) g (gamma r) ∧
        f z = expMap (I := I) g (gamma r) (A r z.1)
    have hh' : Pclock (rho z.2) := hh
    exact (congrArg Pclock hrho).mp hh'

end DifferentialGeometry.Geometry.Riemannian.Variation

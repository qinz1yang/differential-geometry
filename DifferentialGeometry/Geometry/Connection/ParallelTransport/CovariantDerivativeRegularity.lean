import DifferentialGeometry.Geometry.Connection.AlongCurveRegularity
import DifferentialGeometry.Geometry.Connection.LeviCivita.AlongCurve

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

open Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem contMDiffOn_connectionForm_leviCivita
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn I.tangent 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun p : TangentBundle I M =>
        (LeviCivita g).connectionForm (trivializationAt E (TangentSpace I) α) p.1 p.2)
      (TotalSpace.proj ⁻¹' chartLeviCivitaGoodSet (I := I) α) := by
  let e := trivializationAt E (TangentSpace I) α
  let U := chartLeviCivitaGoodSet (I := I) α
  have hσ (v : E) : ContMDiffOn I I.tangent ∞
      (fun y : M => (⟨y, e.symmL ℝ y v⟩ : TangentBundle I M)) U := by
    intro y hy
    have he : y ∈ e.baseSet := chartLeviCivitaGoodSet_mem_baseSet hy
    apply ContMDiffAt.contMDiffWithinAt
    rw [e.contMDiffAt_section_iff he]
    apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds he] with z hz
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hz]
    exact e.continuousLinearMapAt_symmL hz v
  have hD (v : E) : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y => (⟨y, (LeviCivita g) (fun z => e.symmL ℝ z v) y⟩ :
        TotalSpace (E →L[ℝ] E) (fun y => TangentSpace I y →L[ℝ] TangentSpace I y))) U := by
    have h := (chartLeviCivita_contMDiffCovariantDerivativeOn g α).contMDiff
      (by simpa using hσ v)
    apply h.congr
    intro y hy
    congr 1
    apply ContinuousLinearMap.ext
    intro X
    exact LeviCivita_chart_apply g α hy
      (((hσ v y hy).contMDiffAt
        ((chartLeviCivitaGoodSet_isOpen (I := I) α).mem_nhds hy)).mdifferentiableAt
          (by simp)) X
  have hA (v : E) : ContMDiffOn I.tangent I.tangent ∞
      (fun p : TangentBundle I M =>
        (⟨p.1, (LeviCivita g) (fun y => e.symmL ℝ y v) p.1 p.2⟩ : TangentBundle I M))
      (TotalSpace.proj ⁻¹' U) := by
    have h := (hD v).comp (contMDiffOn_proj (F := E) (TangentSpace I)) (fun _ h => h)
    exact h.clm_bundle_apply contMDiffOn_id
  intro p hp
  apply contMDiffWithinAt_clm_of_pointwise
  intro v
  have h := (e.contMDiffOn.comp (hA v)
    (fun q hq => e.mem_source.mpr (chartLeviCivitaGoodSet_mem_baseSet hq)) p hp).snd
  apply h.congr
  · intro q hq
    rw [CovariantDerivative.connectionForm_apply _ e
      (chartLeviCivitaGoodSet_mem_baseSet hq)]
    exact e.continuousLinearMapAt_apply_of_mem ℝ
      (chartLeviCivitaGoodSet_mem_baseSet hq) _
  · rw [CovariantDerivative.connectionForm_apply _ e
      (chartLeviCivitaGoodSet_mem_baseSet hp)]
    exact e.continuousLinearMapAt_apply_of_mem ℝ
      (chartLeviCivitaGoodSet_mem_baseSet hp) _

theorem contMDiffAt_covDerivAlong
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {Z : ∀ t, TangentSpace I (γ t)} {t₀ : ℝ}
    {m : ℕ∞} {n : ℕ∞ω}
    (hZ : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n
      (fun t => (⟨γ t, Z t⟩ : TangentBundle I M)) t₀)
    (hmn : (m : ℕ∞ω) + 1 ≤ n) (hint : I.IsInteriorPoint (γ t₀)) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent m
      (fun t => (⟨γ t, covDerivAlong g γ Z t⟩ : TangentBundle I M)) t₀ := by
  have hone : (1 : ℕ∞ω) ≤ n :=
    (le_add_of_nonneg_left (show (0 : ℕ∞ω) ≤ m from zero_le)).trans hmn
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t₀ :=
    (contMDiff_proj (TangentSpace I)).contMDiffAt.comp t₀ hZ
  have hgood : γ t₀ ∈ chartLeviCivitaGoodSet (I := I) (γ t₀) :=
    mem_chartLeviCivitaGoodSet_iff.mpr ⟨mem_extChartAt_source _,
      mem_baseSet_trivializationAt E (TangentSpace I) _, I.isInteriorPoint_iff.mp hint⟩
  have hA : ContMDiffAt I.tangent 𝓘(ℝ, E →L[ℝ] E) m
      (fun p : TangentBundle I M => (LeviCivita g).connectionForm
        (trivializationAt E (TangentSpace I) (γ t₀)) p.1 p.2)
      (⟨γ t₀, mfderiv 𝓘(ℝ, ℝ) I γ t₀
        ((NormedSpace.fromTangentSpace t₀).symm 1)⟩ : TangentBundle I M) :=
    ((contMDiffOn_connectionForm_leviCivita g (γ t₀)).contMDiffAt
    (((chartLeviCivitaGoodSet_isOpen (I := I) (γ t₀)).preimage
      (FiberBundle.continuous_proj E (TangentSpace I))).mem_nhds hgood)).of_le
        (show (m : ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : m ≤ (⊤ : ℕ∞)))
  have h := (LeviCivita g).contMDiffAt_derivAlongWithin_of_connectionForm
    (s := Set.univ) Filter.univ_mem hZ hmn (hA.comp t₀ (hγ.time_mfderiv hmn))
  have hnear : ∀ᶠ t in 𝓝 t₀, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    ((contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp (hγ.of_le hone)).mono
      (fun _ ht => ht.mdifferentiableAt (by simp))
  have hinterior : ∀ᶠ t in 𝓝 t₀, I.IsInteriorPoint (γ t) :=
    hγ.continuousAt ((I.isOpen_interior (n := ∞) (by simp)).mem_nhds hint)
  apply h.congr_of_eventuallyEq
  filter_upwards [hnear, hinterior] with t ht hit
  exact congrArg (fun v => (⟨γ t, v⟩ : TangentBundle I M))
    (derivAlongWithin_leviCivita_eq_covDerivAlong g γ Z Filter.univ_mem ht hit).symm

theorem contMDiff_covDerivAlong [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {Z : ∀ t, TangentSpace I (γ t)} {m : ℕ∞} {n : ℕ∞ω}
    (hZ : ContMDiff 𝓘(ℝ, ℝ) I.tangent n
      (fun t => (⟨γ t, Z t⟩ : TangentBundle I M)))
    (hmn : (m : ℕ∞ω) + 1 ≤ n) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent m
      (fun t => (⟨γ t, covDerivAlong g γ Z t⟩ : TangentBundle I M)) := by
  intro t
  exact contMDiffAt_covDerivAlong g hZ.contMDiffAt hmn
    BoundarylessManifold.isInteriorPoint

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

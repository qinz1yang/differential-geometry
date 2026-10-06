import DifferentialGeometry.Topology.Manifold.PairedHalfDiskCharts
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Geometry.MinimalSurface.Curvature.MeanCurvatureReparametrization
import DifferentialGeometry.Geometry.MinimalSurface.Variation.ImmersedDiskDivergence

set_option autoImplicit false
noncomputable section
open Set Filter Bundle _root_.Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry
open DifferentialGeometry.Topology (closedDisk freeLoop)
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

private theorem sheet_flux_from_harmonic_reparametrization
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U F : ℂ → M) (ψ : ℂ → ℂ)
    (p : ℝ) {r : ℝ} (hr : 0 < r)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (Metric.ball 0 1))
    (hconf : ∀ q ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U q)
    (htension : ∀ q ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U q = 0)
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun q : openHalfDisk p r => ψ q))
    (hmaps : Set.MapsTo ψ (openHalfDisk p r) (Metric.ball 0 1))
    (hbij : ∀ z : openHalfDisk p r, Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun q : openHalfDisk p r => ψ q) z))
    (heq : Set.EqOn F (U ∘ ψ) (openHalfDisk p r))
    (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 F (closedHalfDisk p r))
    (hiF : ∀ z ∈ closedHalfDisk p r,
      Function.Injective (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F (closedHalfDisk p r) z))
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (Y x)))
    (havoid : ∀ q ∈ upperClosed ∩ Metric.sphere (p : ℂ) r, F q ∉ tsupport Y) :
    (∫ z in (openHalfDisk p r : Set ℂ),
        ambientDivergenceWithin g F (closedHalfDisk p r) Y z) =
      ∫ s : ℝ, (Icc (p - r) (p + r)).indicator
        (fun s => Real.sqrt (gramWithin g F (closedHalfDisk p r) (s : ℂ) 1 1) *
          g.inner (F (s : ℂ)) (Y (F (s : ℂ)))
            (-inwardConormalWithin g F (closedHalfDisk p r) (s : ℂ))) s := by
  have hFinterior : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞
      (fun q : openHalfDisk p r => F q) :=
    (hU.comp_contMDiff hψ (fun q => hmaps q.property)).congr (fun q => heq q.property)
  have hiFinterior (z : openHalfDisk p r) : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : openHalfDisk p r => F q) z) := by
    rw [DifferentialGeometry.mfderiv_restrict_open]
    have hS : closedHalfDisk p r ∈ 𝓝 (z : ℂ) :=
      mem_of_superset ((openHalfDisk p r).isOpen.mem_nhds z.property)
        (fun q hq => ⟨(show 0 < q.im from hq.1).le, Metric.ball_subset_closedBall hq.2⟩)
    rw [← mfderivWithin_of_mem_nhds hS]
    exact hiF z (mem_of_mem_nhds hS)
  have hmean (z : openHalfDisk p r) :
      DifferentialGeometry.Geometry.ImmersedDiskDivergence.inducedMeanTrace (openHalfDisk p r) g F
        hFinterior hiFinterior z = 0 := by
    let II : ℂ →L[ℝ] ℂ →L[ℝ] E :=
      secondFundamentalFormAmbientAt
        (g.pullback (fun q : openHalfDisk p r => F q) hFinterior hiFinterior)
        g (fun q : openHalfDisk p r => F q) z
    let D : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z
    let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner (F z)
    change @Eq E
      ((G (D 1) (D 1) * G (D Complex.I) (D Complex.I) -
          G (D 1) (D Complex.I) ^ 2)⁻¹ •
        (G (D Complex.I) (D Complex.I) • II 1 1 +
          G (D 1) (D 1) • II Complex.I Complex.I -
          (2 * G (D 1) (D Complex.I)) • II 1 Complex.I)) (0 : E)
    exact DifferentialGeometry.Geometry.inverseGram_secondFundamental_trace_eq_zero_of_harmonic_reparametrization
      (openHalfDisk p r) g U F ψ hU hψ hmaps hbij hFinterior hiFinterior
      heq hconf htension z
  exact integral_actual_halfdisk_ambient_divergence_eq_outward_conormal_flux g F p hr
    hF hiF hFinterior hmean Y hY havoid


private theorem uniqueMDiffOn_closed_halfdisk {r : ℝ} (hr : 0 < r) :
    UniqueMDiffOn 𝓘(ℝ, ℂ) (closedHalfDisk 0 r) := by
  apply UniqueDiffOn.uniqueMDiffOn
  apply uniqueDiffOn_convex
    ((convex_halfSpace_im_ge 0).inter (convex_closedBall (0 : ℂ) r))
  have hinside : (openHalfDisk 0 r : Set ℂ) ⊆ interior (closedHalfDisk 0 r) := by
    intro z hz
    apply mem_interior_iff_mem_nhds.mpr
    exact mem_of_superset ((openHalfDisk 0 r).isOpen.mem_nhds hz)
      (fun q hq => ⟨(show 0 < q.im from hq.1).le, Metric.ball_subset_closedBall hq.2⟩)
  refine ⟨(r / 2 : ℂ) * Complex.I, hinside ?_⟩
  constructor
  · change 0 < ((r / 2 : ℂ) * Complex.I).im
    simp only [Complex.mul_I_im, Complex.div_ofNat_re, Complex.ofReal_re]
    positivity
  · rw [Metric.mem_ball, dist_eq_norm, Complex.ofReal_zero, sub_zero]
    simp only [norm_mul, Complex.norm_I, mul_one, norm_div,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
    rw [abs_of_pos hr]
    linarith

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
private theorem sheet_data_from_buffered_chart
    {u : C(closedDisk, M)}
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u) (Metric.ball 0 1))
    {r : ℝ} (hr : 0 < r) (ψ : OpenPartialHomeomorph ℂ ℂ)
    (hbuffer : Metric.closedBall (0 : ℂ) (2 * r) ⊆ ψ.source)
    (htarget : ψ.target ⊆ Metric.ball (0 : ℂ) 1)
    (hψsm : ContDiffOn ℝ ∞ ψ ψ.source)
    (hψism : ContDiffOn ℝ ∞ ψ.symm ψ.target)
    (hψbij : ∀ z ∈ ψ.source, Function.Bijective (fderiv ℝ ψ z))
    (hUinj : Set.InjOn (diskExtension u) ψ.target)
    (hUrank : ∀ z ∈ ψ.target, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)) :
    ContDiffOn ℝ ∞ ψ ψ.source ∧
    ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
    (∀ z ∈ ψ.source, Function.Bijective (fderiv ℝ ψ z)) ∧
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u ∘ ψ)
      (Metric.ball (0 : ℂ) (2 * r)) ∧
    Set.InjOn (diskExtension u ∘ ψ) (closedHalfDisk 0 r) ∧
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun q : openHalfDisk 0 r => ψ q) ∧
    Set.MapsTo ψ (openHalfDisk 0 r) (Metric.ball (0 : ℂ) 1) ∧
    (∀ z : openHalfDisk 0 r, Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun q : openHalfDisk 0 r => ψ q) z)) ∧
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u ∘ ψ) (closedHalfDisk 0 r) ∧
    (∀ z ∈ closedHalfDisk 0 r, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ ψ)
        (closedHalfDisk 0 r) z)) := by
  have hHs : closedHalfDisk 0 r ⊆ Metric.ball (0 : ℂ) (2 * r) :=
    fun _ hz => Metric.closedBall_subset_ball (by linarith only [hr]) hz.2
  have hos : (openHalfDisk 0 r : Set ℂ) ⊆ closedHalfDisk 0 r :=
    fun q hq => ⟨(show 0 < q.im from hq.1).le, Metric.ball_subset_closedBall hq.2⟩
  have hBs : Metric.ball (0 : ℂ) (2 * r) ⊆ ψ.source :=
    Metric.ball_subset_closedBall.trans hbuffer
  have hHs' : closedHalfDisk 0 r ⊆ ψ.source := hHs.trans hBs
  have hos' : (openHalfDisk 0 r : Set ℂ) ⊆ ψ.source := hos.trans hHs'
  have hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u ∘ ψ)
      (Metric.ball (0 : ℂ) (2 * r)) :=
    hU.comp (hψsm.contMDiffOn.mono hBs)
      (fun _ hz => htarget (ψ.map_source (hBs hz)))
  have hFinj : InjOn (diskExtension u ∘ ψ) (closedHalfDisk 0 r) := by
    intro z hz w hw hzw
    exact ψ.injOn (hHs' hz) (hHs' hw)
      (hUinj (ψ.map_source (hHs' hz)) (ψ.map_source (hHs' hw)) hzw)
  have hψsub : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (fun q : openHalfDisk 0 r => ψ q) :=
    hψsm.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun q => hos' q.property)
  have hmaps : MapsTo ψ (openHalfDisk 0 r) (Metric.ball (0 : ℂ) 1) :=
    fun _ hz => htarget (ψ.map_source (hos' hz))
  have hbij (z : openHalfDisk 0 r) : Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun q : openHalfDisk 0 r => ψ q) z) := by
    rw [DifferentialGeometry.mfderiv_restrict_open, mfderiv_eq_fderiv]
    exact hψbij z (hos' z.property)
  have hi (z : ℂ) (hz : z ∈ closedHalfDisk 0 r) : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ ψ) z) := by
    have hzψ := hHs' hz
    have hdz := (hψsm.contMDiffOn.contMDiffAt
      (ψ.open_source.mem_nhds hzψ)).mdifferentiableAt (by simp)
    have hdU := (hU.contMDiffAt
      (Metric.isOpen_ball.mem_nhds (htarget (ψ.map_source hzψ)))).mdifferentiableAt (by simp)
    rw [mfderiv_comp z hdU hdz]
    apply (hUrank (ψ z) (ψ.map_source hzψ)).comp
    rw [mfderiv_eq_fderiv]
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (ψ z)).symm.injective.comp
      ((hψbij z hzψ).1.comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).injective)
  refine ⟨hψsm, hψism, hψbij, hF, hFinj, hψsub, hmaps, hbij,
    (hF.mono hHs).of_le (by simp), ?_⟩
  intro z hz
  rw [mfderivWithin_eq_mfderiv (uniqueMDiffOn_closed_halfdisk hr z hz)
    ((hF.contMDiffAt (Metric.isOpen_ball.mem_nhds (hHs hz))).mdifferentiableAt (by simp))]
  exact hi z hz

/-- The same regular transverse double point of the original Morrey disk
has paired source charts with a common closed buffer, and both actual
reparameterized sheets satisfy the outward conormal flux identity. -/
theorem morrey_transverse_paired_halfdisk_flux
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (hdim : Module.finrank ℝ E = 3) {a b : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) (hb : b ∈ Metric.ball (0 : ℂ) 1)
    (hab : a ≠ b) (heq : diskExtension u a = diskExtension u b)
    (hia : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) a))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) b))
    (htrans : Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) a).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) b)))) :
    ∃ (r : ℝ) (ψ₁ ψ₂ : OpenPartialHomeomorph ℂ ℂ),
      0 < r ∧ ψ₁ 0 = a ∧ ψ₂ 0 = b ∧
      Metric.closedBall (0 : ℂ) (2 * r) ⊆ ψ₁.source ∩ ψ₂.source ∧
      ψ₁.target ⊆ Metric.ball (0 : ℂ) 1 ∧
      ψ₂.target ⊆ Metric.ball (0 : ℂ) 1 ∧ Disjoint ψ₁.target ψ₂.target ∧
      (∀ t ∈ Icc (-2 * r) (2 * r),
        diskExtension u (ψ₁ (t : ℂ)) = diskExtension u (ψ₂ (t : ℂ))) ∧
      (∀ ψ ∈ ({ψ₁, ψ₂} : Set (OpenPartialHomeomorph ℂ ℂ)),
        ContDiffOn ℝ ∞ ψ ψ.source ∧
        ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
        (∀ z ∈ ψ.source, Function.Bijective (fderiv ℝ ψ z)) ∧
        ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u ∘ ψ)
          (Metric.ball (0 : ℂ) (2 * r)) ∧
        Set.InjOn (diskExtension u ∘ ψ) (closedHalfDisk 0 r) ∧
        ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun q : openHalfDisk 0 r => ψ q) ∧
        Set.MapsTo ψ (openHalfDisk 0 r) (Metric.ball (0 : ℂ) 1) ∧
        (∀ z : openHalfDisk 0 r, Function.Bijective
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun q : openHalfDisk 0 r => ψ q) z)) ∧
        ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u ∘ ψ)
          (closedHalfDisk 0 r) ∧
        (∀ z ∈ closedHalfDisk 0 r, Function.Injective
          (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ ψ)
            (closedHalfDisk 0 r) z))) ∧
      (∀ (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x),
        ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
          (fun x => TotalSpace.mk' E x (Y x)) →
        (∀ ψ ∈ ({ψ₁, ψ₂} : Set (OpenPartialHomeomorph ℂ ℂ)),
          ∀ q ∈ upperClosed ∩ Metric.sphere (0 : ℂ) r,
            diskExtension u (ψ q) ∉ tsupport Y) →
        ∀ ψ ∈ ({ψ₁, ψ₂} : Set (OpenPartialHomeomorph ℂ ℂ)),
          (∫ z in (openHalfDisk 0 r : Set ℂ),
            ambientDivergenceWithin g (diskExtension u ∘ ψ) (closedHalfDisk 0 r) Y z) =
          ∫ s : ℝ, (Icc (-r) r).indicator
            (fun s => Real.sqrt
                (gramWithin g (diskExtension u ∘ ψ) (closedHalfDisk 0 r) (s : ℂ) 1 1) *
              g.inner (diskExtension u (ψ (s : ℂ)))
                (Y (diskExtension u (ψ (s : ℂ))))
                (-inwardConormalWithin g (diskExtension u ∘ ψ)
                  (closedHalfDisk 0 r) (s : ℂ))) s) := by
  obtain ⟨r, ψ₁, ψ₂, hr, hψ₁0, hψ₂0, hbuffer, htarget₁, htarget₂, hdisj,
    hsm₁, hism₁, hsm₂, hism₂, hbij₁, hbij₂, hinj₁, hinj₂, hrank₁, hrank₂, hseam⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_paired_halfdisk_charts_of_transverse_double_point
      Metric.isOpen_ball hu.smoothInterior ha hb hab heq hia hib htrans hdim
  have hdata : ∀ ψ ∈ ({ψ₁, ψ₂} : Set (OpenPartialHomeomorph ℂ ℂ)),
      ContDiffOn ℝ ∞ ψ ψ.source ∧
      ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      (∀ z ∈ ψ.source, Function.Bijective (fderiv ℝ ψ z)) ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u ∘ ψ)
        (Metric.ball (0 : ℂ) (2 * r)) ∧
      Set.InjOn (diskExtension u ∘ ψ) (closedHalfDisk 0 r) ∧
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun q : openHalfDisk 0 r => ψ q) ∧
      Set.MapsTo ψ (openHalfDisk 0 r) (Metric.ball (0 : ℂ) 1) ∧
      (∀ z : openHalfDisk 0 r, Function.Bijective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun q : openHalfDisk 0 r => ψ q) z)) ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u ∘ ψ)
        (closedHalfDisk 0 r) ∧
      (∀ z ∈ closedHalfDisk 0 r, Function.Injective
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ ψ)
          (closedHalfDisk 0 r) z)) := by
    intro ψ hψ
    have hcases : ψ = ψ₁ ∨ ψ = ψ₂ := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hψ
    rcases hcases with hψeq | hψeq
    · subst ψ
      exact sheet_data_from_buffered_chart hu.smoothInterior hr ψ₁
        (fun _ hz => (hbuffer hz).1) htarget₁ hsm₁ hism₁ hbij₁ hinj₁ hrank₁
    · subst ψ
      exact sheet_data_from_buffered_chart hu.smoothInterior hr ψ₂
        (fun _ hz => (hbuffer hz).2) htarget₂ hsm₂ hism₂ hbij₂ hinj₂ hrank₂
  refine ⟨r, ψ₁, ψ₂, hr, hψ₁0, hψ₂0, hbuffer, htarget₁, htarget₂, hdisj,
    hseam, hdata, ?_⟩
  intro Y hY havoid ψ hψ
  obtain ⟨_, _, _, _, _, hψsub, hmaps, hbij, hF, hiF⟩ := hdata ψ hψ
  have hflux :=
    sheet_flux_from_harmonic_reparametrization g (diskExtension u)
      (diskExtension u ∘ ψ) ψ 0 hr hu.smoothInterior hu.conformal hu.harmonic
      hψsub hmaps hbij (fun _ _ => rfl) hF hiF Y hY (havoid ψ hψ)
  dsimp only [Function.comp_apply] at hflux
  rw [zero_sub, zero_add] at hflux
  exact hflux

end DifferentialGeometry.Geometry

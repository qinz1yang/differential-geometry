import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1Standard
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordCoordinates
import DifferentialGeometry.Topology.Manifold.OpenTarget

/-!
# FC39 GROUP G, RIMBOX route B (sheet §3 K5): the unscaled rim parametrization

Lane FC39-G-RIMBOX, dispositions D62-3 (b), (c), (i). From the transport flow `Fl` (on an open `U`,
`P (Fl_t z) = t` from the `P = 0` slice, `B` kept on `{|B| < r'}`) and a two-sided collar `C` of the
end rim in that slice (`P ∘ C = 0`, `B ∘ C = κ (1 − ‖z‖)`, smooth, injective, immersive on
`{|‖z‖ − 1| < δ}`, inside `U`), the map

  `F (θ, X, s) = Fl_s (C ((1 + X/κ) θ̂))`   (`rimParam_GRIM`, `θ̂ = planeOfCircle θ`)

is, on `{|X| < κ δ, s ∈ (a₀, b₀)}`, smooth, injective, an immersion (three directions: `dP` recovers
`ds`; the slice is `dFl_s ∘ dC ∘ d(polar)` with the polar left inverse `rimPolarInv_GRIM`), with
`P ∘ F = s` and `B ∘ F = −X` (`rimParam_props_GRIM`). Both ends of a handle use the SAME flow; the
rim chart of an end is `F` precomposed with the scaled profile (sheet §3 K7).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- The polar map `(θ, X) ↦ (1 + X/κ) • θ̂` of the rim collar. -/
def rimPolar_GRIM (κ : ℝ) (p : Circle × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (1 + p.2 / κ) • planeOfCircle p.1

/-- Its inverse `z ↦ (z/‖z‖, κ (‖z‖ − 1))`. -/
def rimPolarInv_GRIM (κ : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : Circle × ℝ :=
  (unitOf (Complex.orthonormalBasisOneI.repr.symm z), κ * (‖z‖ - 1))

theorem norm_rimPolar_GRIM {κ : ℝ} (hκ : 0 < κ) {p : Circle × ℝ} (hp : -κ < p.2) :
    ‖rimPolar_GRIM κ p‖ = 1 + p.2 / κ := by
  have hpos : 0 < 1 + p.2 / κ := by
    have : -1 < p.2 / κ := by rw [lt_div_iff₀ hκ]; linarith
    linarith
  unfold rimPolar_GRIM
  rw [norm_smul, Real.norm_of_nonneg hpos.le]
  have h1 : ‖planeOfCircle p.1‖ = 1 := by
    unfold planeOfCircle
    rw [LinearIsometryEquiv.norm_map]
    exact Circle.norm_coe p.1
  rw [h1, mul_one]

theorem rimPolarInv_rimPolar_GRIM {κ : ℝ} (hκ : 0 < κ) {p : Circle × ℝ} (hp : -κ < p.2) :
    rimPolarInv_GRIM κ (rimPolar_GRIM κ p) = p := by
  have hpos : 0 < 1 + p.2 / κ := by
    have : -1 < p.2 / κ := by rw [lt_div_iff₀ hκ]; linarith
    linarith
  apply Prod.ext
  · change unitOf (Complex.orthonormalBasisOneI.repr.symm ((1 + p.2 / κ) • planeOfCircle p.1)) = p.1
    simp only [planeOfCircle, map_smul, LinearIsometryEquiv.symm_apply_apply]
    exact unitOf_smul hpos p.1
  · change κ * (‖rimPolar_GRIM κ p‖ - 1) = p.2
    rw [norm_rimPolar_GRIM hκ hp]
    field_simp
    ring

theorem contMDiff_rimPolar_GRIM (κ : ℝ) :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ (rimPolar_GRIM κ) := by
  have ht : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
      (fun p : Circle × ℝ => planeOfCircle p.1) :=
    Complex.orthonormalBasisOneI.repr.contDiff.contMDiff.comp
      (contMDiff_circle_coe.comp contMDiff_fst)
  have hr : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : Circle × ℝ => 1 + p.2 / κ) :=
    (contMDiff_const.add (contMDiff_snd.div_const κ))
  exact hr.smul ht

theorem contMDiffOn_rimPolarInv_GRIM (κ : ℝ) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ (rimPolarInv_GRIM κ)
      {z | z ≠ 0} := by
  have hu : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 1) ∞
      (fun z : EuclideanSpace ℝ (Fin 2) => unitOf (Complex.orthonormalBasisOneI.repr.symm z))
      {z | z ≠ 0} := by
    refine contMDiffOn_unitOf.comp
      (Complex.orthonormalBasisOneI.repr.symm.contDiff.contMDiff.contMDiffOn) fun z hz => ?_
    intro h0
    apply hz
    have := congrArg Complex.orthonormalBasisOneI.repr h0
    rwa [LinearIsometryEquiv.apply_symm_apply, map_zero] at this
  have hn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞
      (fun z : EuclideanSpace ℝ (Fin 2) => κ * (‖z‖ - 1)) {z | z ≠ 0} := fun z hz =>
    ((contMDiffAt_const.mul ((contDiffAt_norm ℝ hz).contMDiffAt.sub contMDiffAt_const))).contMDiffWithinAt
  exact hu.prodMk hn

section Flow

variable {E H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace Y] [ChartedSpace H Y]

open Classical in
/-- The flow extended to `ℝ × Y` (the identity off `U`). -/
def flowExt_GRIM {U : TopologicalSpace.Opens Y} (Fl : ℝ → U ≃ₘ⟮I, I⟯ U) (q : ℝ × Y) : Y :=
  if h : q.2 ∈ U then (Fl q.1 ⟨q.2, h⟩ : Y) else q.2

theorem flowExt_of_mem_GRIM {U : TopologicalSpace.Opens Y} (Fl : ℝ → U ≃ₘ⟮I, I⟯ U) {s : ℝ}
    {y : Y} (hy : y ∈ U) : flowExt_GRIM Fl (s, y) = (Fl s ⟨y, hy⟩ : Y) := by
  simp [flowExt_GRIM, hy]

theorem contMDiffOn_flowExt_GRIM {U : TopologicalSpace.Opens Y} (Fl : ℝ → U ≃ₘ⟮I, I⟯ U)
    (hFl : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × U => Fl q.1 q.2)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (flowExt_GRIM Fl) (univ ×ˢ (U : Set Y)) := by
  intro q hq
  let V : TopologicalSpace.Opens (ℝ × Y) := ⟨univ ×ˢ (U : Set Y), isOpen_univ.prod U.isOpen⟩
  let φ : V → ℝ × U := fun x => (x.1.1, ⟨x.1.2, x.2.2⟩)
  have hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ φ := by
    refine (contMDiff_fst.comp contMDiff_subtype_val).prodMk ?_
    exact (ContMDiff.subtypeVal_comp_iff U _).mp (contMDiff_snd.comp contMDiff_subtype_val)
  have hsub : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun x : V => flowExt_GRIM Fl x) ⟨q, hq⟩ := by
    have h1 : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
        (fun x : V => ((fun q : ℝ × U => Fl q.1 q.2) (φ x) : Y)) ⟨q, hq⟩ :=
      (contMDiff_subtype_val.comp (hFl.comp hφ)) _
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    exact flowExt_of_mem_GRIM Fl x.2.2
  exact (contMDiffAt_subtype_iff.mp hsub).contMDiffWithinAt

/-- **The unscaled rim parametrization** `F (θ, X, s) = Fl_s (C ((1 + X/κ) θ̂))`. -/
def rimParam_GRIM {U : TopologicalSpace.Opens Y} (Fl : ℝ → U ≃ₘ⟮I, I⟯ U)
    (C : EuclideanSpace ℝ (Fin 2) → Y) (κ : ℝ) (p : Circle × (ℝ × ℝ)) : Y :=
  flowExt_GRIM Fl (p.2.2, C (rimPolar_GRIM κ (p.1, p.2.1)))

/-- **The rim parametrization kernel (sheet §3 K5)**: smooth, injective, immersive, `P ∘ F = s`,
`B ∘ F = −X` on `{|X| < κ δ, s ∈ (a₀, b₀)}`. -/
theorem rimParam_props_GRIM {P B : Y → ℝ} (hP : ContMDiff I 𝓘(ℝ, ℝ) ∞ P)
    {U : TopologicalSpace.Opens Y} (Fl : ℝ → U ≃ₘ⟮I, I⟯ U)
    (hFl : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × U => Fl q.1 q.2)) {a₀ b₀ r' : ℝ}
    (hFlP : ∀ z : U, P z = 0 → -r' ≤ B z → ∀ t ∈ Ioo a₀ b₀, P (Fl t z) = t)
    (hFlB : ∀ (z : U) (t : ℝ), |B z| < r' → B (Fl t z) = B z)
    (C : EuclideanSpace ℝ (Fin 2) → Y) {δ κ : ℝ} (hκ : 0 < κ) (hδ1 : δ < 1) (hδr : κ * δ ≤ r')
    (hC : ContMDiffOn (𝓡 2) I ∞ C {z | |‖z‖ - 1| < δ}) (hCinj : InjOn C {z | |‖z‖ - 1| < δ})
    (hCimm : ∀ z, |‖z‖ - 1| < δ → Injective (mfderiv (𝓡 2) I C z))
    (hCP : ∀ z, |‖z‖ - 1| < δ → P (C z) = 0 ∧ B (C z) = κ * (1 - ‖z‖))
    (hCU : ∀ z, |‖z‖ - 1| < δ → C z ∈ U) :
    ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) I ∞ (rimParam_GRIM Fl C κ)
        {p | |p.2.1| < κ * δ ∧ p.2.2 ∈ Ioo a₀ b₀} ∧
      InjOn (rimParam_GRIM Fl C κ) {p | |p.2.1| < κ * δ ∧ p.2.2 ∈ Ioo a₀ b₀} ∧
      (∀ p : Circle × (ℝ × ℝ), |p.2.1| < κ * δ → p.2.2 ∈ Ioo a₀ b₀ →
        Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) I (rimParam_GRIM Fl C κ) p)) ∧
      (∀ p : Circle × (ℝ × ℝ), |p.2.1| < κ * δ → p.2.2 ∈ Ioo a₀ b₀ →
        P (rimParam_GRIM Fl C κ p) = p.2.2 ∧ B (rimParam_GRIM Fl C κ p) = -p.2.1) := by
  -- the polar point lies in the collar annulus
  have hann : ∀ p : Circle × ℝ, |p.2| < κ * δ → |‖rimPolar_GRIM κ p‖ - 1| < δ := by
    intro p hp
    have hX : -κ < p.2 := by
      have := (abs_lt.mp hp).1
      nlinarith
    rw [norm_rimPolar_GRIM hκ hX, add_sub_cancel_left, abs_div, abs_of_pos hκ,
      div_lt_iff₀ hκ]
    linarith
  have hBC : ∀ p : Circle × ℝ, |p.2| < κ * δ → B (C (rimPolar_GRIM κ p)) = -p.2 := by
    intro p hp
    have hX : -κ < p.2 := by
      have := (abs_lt.mp hp).1
      nlinarith
    rw [(hCP _ (hann p hp)).2, norm_rimPolar_GRIM hκ hX]
    field_simp
    ring
  have hval : ∀ p : Circle × (ℝ × ℝ), |p.2.1| < κ * δ → p.2.2 ∈ Ioo a₀ b₀ →
      P (rimParam_GRIM Fl C κ p) = p.2.2 ∧ B (rimParam_GRIM Fl C κ p) = -p.2.1 := by
    intro p hp hs
    have hU := hCU _ (hann (p.1, p.2.1) hp)
    have hB := hBC (p.1, p.2.1) hp
    unfold rimParam_GRIM
    rw [flowExt_of_mem_GRIM Fl hU]
    have habs : |B (C (rimPolar_GRIM κ (p.1, p.2.1)))| < r' := by
      rw [hB, abs_neg]
      exact lt_of_lt_of_le hp hδr
    refine ⟨hFlP ⟨_, hU⟩ (hCP _ (hann (p.1, p.2.1) hp)).1 ?_ p.2.2 hs, ?_⟩
    · have := (abs_lt.mp habs).1
      change -r' ≤ B (C (rimPolar_GRIM κ (p.1, p.2.1)))
      linarith
    · rw [hFlB ⟨_, hU⟩ p.2.2 habs]
      exact hB
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hΩopen : IsOpen {p : Circle × (ℝ × ℝ) | |p.2.1| < κ * δ ∧ p.2.2 ∈ Ioo a₀ b₀} :=
    (isOpen_lt (continuous_abs.comp (continuous_fst.comp continuous_snd)) continuous_const).inter
      (isOpen_Ioo.preimage (continuous_snd.comp continuous_snd))
  have hsmooth : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) I ∞ (rimParam_GRIM Fl C κ)
      {p | |p.2.1| < κ * δ ∧ p.2.2 ∈ Ioo a₀ b₀} := by
    have hK : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : Circle × (ℝ × ℝ) => (p.2.2, C (rimPolar_GRIM κ (p.1, p.2.1))))
        {p | |p.2.1| < κ * δ ∧ p.2.2 ∈ Ioo a₀ b₀} := by
      have h1 : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, ℝ) ∞
          (fun p : Circle × (ℝ × ℝ) => p.2.2) :=
        (contDiff_snd.contMDiff).comp contMDiff_snd
      have h2 : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
          (fun p : Circle × (ℝ × ℝ) => (p.1, p.2.1)) :=
        contMDiff_fst.prodMk ((contDiff_fst.contMDiff).comp contMDiff_snd)
      have h3 : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) I ∞
          (fun p : Circle × (ℝ × ℝ) => C (rimPolar_GRIM κ (p.1, p.2.1)))
          {p | |p.2.1| < κ * δ ∧ p.2.2 ∈ Ioo a₀ b₀} :=
        hC.comp ((contMDiff_rimPolar_GRIM κ).comp h2).contMDiffOn
          (fun p hp => hann (p.1, p.2.1) hp.1)
      exact h1.contMDiffOn.prodMk h3
    exact (contMDiffOn_flowExt_GRIM Fl hFl).comp hK
      (fun p hp => ⟨mem_univ _, hCU _ (hann (p.1, p.2.1) hp.1)⟩)
  refine ⟨hsmooth, ?_, ?_, hval⟩
  · -- injectivity
    intro p hp p' hp' h
    have hs : p.2.2 = p'.2.2 := by
      rw [← (hval p hp.1 hp.2).1, ← (hval p' hp'.1 hp'.2).1, h]
    have hU := hCU _ (hann (p.1, p.2.1) hp.1)
    have hU' := hCU _ (hann (p'.1, p'.2.1) hp'.1)
    unfold rimParam_GRIM at h
    rw [flowExt_of_mem_GRIM Fl hU, flowExt_of_mem_GRIM Fl hU', hs] at h
    have h1 := congrArg Subtype.val ((Fl p'.2.2).injective (Subtype.ext h))
    have h2 := hCinj (hann (p.1, p.2.1) hp.1) (hann (p'.1, p'.2.1) hp'.1) h1
    have hX : -κ < p.2.1 := by
      have := (abs_lt.mp hp.1).1
      nlinarith
    have hX' : -κ < p'.2.1 := by
      have := (abs_lt.mp hp'.1).1
      nlinarith
    have h3 := congrArg (rimPolarInv_GRIM κ) h2
    rw [rimPolarInv_rimPolar_GRIM hκ hX, rimPolarInv_rimPolar_GRIM hκ hX'] at h3
    have e1 : p.1 = p'.1 := (Prod.mk.inj h3).1
    have e2 : p.2.1 = p'.2.1 := (Prod.mk.inj h3).2
    exact Prod.ext e1 (Prod.ext e2 hs)
  · -- injective differential (three directions)
    intro p hp hs
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hpΩ : p ∈ {p : Circle × (ℝ × ℝ) | |p.2.1| < κ * δ ∧ p.2.2 ∈ Ioo a₀ b₀} := ⟨hp, hs⟩
    have hFd : MDifferentiableAt ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) I (rimParam_GRIM Fl C κ) p :=
      (hsmooth.contMDiffAt (hΩopen.mem_nhds hpΩ)).mdifferentiableAt hn
    -- (a) the axial component vanishes
    have hPd : MDifferentiableAt I 𝓘(ℝ, ℝ) P (rimParam_GRIM Fl C κ p) := (hP _).mdifferentiableAt hn
    have hev : P ∘ rimParam_GRIM Fl C κ =ᶠ[𝓝 p] fun q : Circle × (ℝ × ℝ) => q.2.2 := by
      filter_upwards [hΩopen.mem_nhds hpΩ] with q hq
      exact (hval q hq.1 hq.2).1
    have hs2 : v.2.2 = 0 := by
      have h1 : mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, ℝ) (P ∘ rimParam_GRIM Fl C κ) p v = 0 := by
        rw [mfderiv_comp p hPd hFd]
        change mfderiv I 𝓘(ℝ, ℝ) P _ (mfderiv _ I (rimParam_GRIM Fl C κ) p v) = 0
        rw [hv, map_zero]
      rw [hev.mfderiv_eq] at h1
      have hsnd2 : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (Prod.snd : ℝ × ℝ → ℝ) p.2 :=
        ((contDiff_snd.contMDiff) _).mdifferentiableAt hn
      have hsnd1 : MDifferentiableAt ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, ℝ × ℝ)
          (Prod.snd : Circle × (ℝ × ℝ) → ℝ × ℝ) p := mdifferentiableAt_snd
      have hc : (fun q : Circle × (ℝ × ℝ) => q.2.2) = Prod.snd ∘ Prod.snd := rfl
      rw [hc, mfderiv_comp p hsnd2 hsnd1, mfderiv_snd, mfderiv_eq_fderiv, fderiv_snd] at h1
      exact h1
    -- (b) the slice through `p`
    let ι : Circle × ℝ → Circle × (ℝ × ℝ) := fun q => (q.1, (q.2, p.2.2))
    have hιD : HasMFDerivAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ι (p.1, p.2.1)
        ((ContinuousLinearMap.fst ℝ (TangentSpace (𝓡 1) p.1) ℝ).prod
          ((ContinuousLinearMap.inl ℝ ℝ ℝ).comp
            (ContinuousLinearMap.snd ℝ (TangentSpace (𝓡 1) p.1) ℝ))) := by
      have hg : HasMFDerivAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ)
          (fun q : Circle × ℝ => (q.2, p.2.2)) (p.1, p.2.1)
          ((ContinuousLinearMap.inl ℝ ℝ ℝ).comp
            (ContinuousLinearMap.snd ℝ (TangentSpace (𝓡 1) p.1) ℝ)) :=
        ((hasFDerivAt_prodMk_left (𝕜 := ℝ) (p.2.1 : ℝ) p.2.2).hasMFDerivAt).comp (p.1, p.2.1)
          (hasMFDerivAt_snd (I := 𝓡 1) (I' := 𝓘(ℝ, ℝ)) (p.1, p.2.1))
      exact (hasMFDerivAt_fst (p.1, p.2.1)).prodMk hg
    have hιv : mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ι (p.1, p.2.1)
        (v.1, v.2.1) = v := by
      rw [hιD.mfderiv]
      exact Prod.ext rfl (Prod.ext rfl hs2.symm)
    -- (c) the slice map is an immersion
    have hq₀X : -κ < p.2.1 := by
      have := (abs_lt.mp hp).1
      nlinarith
    have hz₀ := hann (p.1, p.2.1) hp
    have hU₀ := hCU _ hz₀
    have hannOpen : IsOpen {z : EuclideanSpace ℝ (Fin 2) | |‖z‖ - 1| < δ} :=
      isOpen_lt (continuous_abs.comp (continuous_norm.sub continuous_const)) continuous_const
    let fs : Y → Y := fun y => flowExt_GRIM Fl (p.2.2, y)
    have hfsOn : ContMDiffOn I I ∞ fs (U : Set Y) :=
      (contMDiffOn_flowExt_GRIM Fl hFl).comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
        (fun y hy => ⟨mem_univ _, hy⟩)
    have hfsd : MDifferentiableAt I I fs (C (rimPolar_GRIM κ (p.1, p.2.1))) :=
      (hfsOn.contMDiffAt (U.isOpen.mem_nhds hU₀)).mdifferentiableAt hn
    have hfsinj : Injective (mfderiv I I fs (C (rimPolar_GRIM κ (p.1, p.2.1)))) := by
      have hres := DifferentialGeometry.mfderiv_restrict_open (I := I) (J := I) fs U
        ⟨C (rimPolar_GRIM κ (p.1, p.2.1)), hU₀⟩
      rw [← hres]
      have heq : (fun y : U => fs y) = (Subtype.val : U → Y) ∘ (Fl p.2.2) :=
        funext fun y => flowExt_of_mem_GRIM Fl y.2
      rw [heq, mfderiv_comp _ ((contMDiff_subtype_val _).mdifferentiableAt hn)
        (((Fl p.2.2).contMDiff _).mdifferentiableAt hn), DifferentialGeometry.mfderiv_subtype_val]
      intro a b hab
      apply (((Fl p.2.2).isLocalDiffeomorph _).mfderivToContinuousLinearEquiv hn).injective
      exact hab
    have hCd : MDifferentiableAt (𝓡 2) I C (rimPolar_GRIM κ (p.1, p.2.1)) :=
      (hC.contMDiffAt (hannOpen.mem_nhds hz₀)).mdifferentiableAt hn
    have hpold : MDifferentiableAt ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        (rimPolar_GRIM κ) (p.1, p.2.1) := (contMDiff_rimPolar_GRIM κ _).mdifferentiableAt hn
    have hpolinj : Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        (rimPolar_GRIM κ) (p.1, p.2.1)) := by
      have hne : rimPolar_GRIM κ (p.1, p.2.1) ≠ 0 := by
        intro h0
        have h1 := norm_rimPolar_GRIM hκ (p := (p.1, p.2.1)) hq₀X
        rw [h0, norm_zero] at h1
        have : -1 < p.2.1 / κ := by rw [lt_div_iff₀ hκ]; linarith
        change (0 : ℝ) = 1 + p.2.1 / κ at h1
        linarith
      have hinvd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ((𝓡 1).prod 𝓘(ℝ, ℝ))
          (rimPolarInv_GRIM κ) (rimPolar_GRIM κ (p.1, p.2.1)) :=
        ((contMDiffOn_rimPolarInv_GRIM κ).contMDiffAt (isOpen_ne.mem_nhds hne)).mdifferentiableAt hn
      have hev : rimPolarInv_GRIM κ ∘ rimPolar_GRIM κ =ᶠ[𝓝 (p.1, p.2.1)] id := by
        have hopen : IsOpen {q : Circle × ℝ | -κ < q.2} := isOpen_lt continuous_const continuous_snd
        filter_upwards [hopen.mem_nhds hq₀X] with q hq
        exact rimPolarInv_rimPolar_GRIM hκ hq
      have hid : mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ))
          (rimPolarInv_GRIM κ ∘ rimPolar_GRIM κ) (p.1, p.2.1) = ContinuousLinearMap.id ℝ _ := by
        rw [hev.mfderiv_eq, mfderiv_id]
        ext v
        rfl
      rw [mfderiv_comp (p.1, p.2.1) hinvd hpold] at hid
      intro a b hab
      have h1 := congrArg (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ((𝓡 1).prod 𝓘(ℝ, ℝ))
        (rimPolarInv_GRIM κ) (rimPolar_GRIM κ (p.1, p.2.1))) hab
      have h2 : ∀ x, mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ((𝓡 1).prod 𝓘(ℝ, ℝ))
          (rimPolarInv_GRIM κ) (rimPolar_GRIM κ (p.1, p.2.1))
          (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (rimPolar_GRIM κ)
            (p.1, p.2.1) x) = x := fun x => congrArg (fun F => F x) hid
      rw [h2, h2] at h1
      exact h1
    have hcompF : rimParam_GRIM Fl C κ ∘ ι = fs ∘ C ∘ rimPolar_GRIM κ := rfl
    have hd : mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) I (rimParam_GRIM Fl C κ ∘ ι) (p.1, p.2.1)
        (v.1, v.2.1) = 0 := by
      rw [mfderiv_comp (p.1, p.2.1) hFd hιD.mdifferentiableAt]
      change mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) I (rimParam_GRIM Fl C κ) p
        (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ι (p.1, p.2.1) (v.1, v.2.1)) = 0
      rw [hιv, hv]
    rw [hcompF, mfderiv_comp (p.1, p.2.1) hfsd (hCd.comp (p.1, p.2.1) hpold),
      mfderiv_comp (p.1, p.2.1) hCd hpold] at hd
    have h0 : (v.1, v.2.1) = (0 : TangentSpace ((𝓡 1).prod 𝓘(ℝ, ℝ)) (p.1, p.2.1)) := by
      apply hpolinj
      apply hCimm _ hz₀
      apply hfsinj
      rw [map_zero, map_zero, map_zero]
      exact hd
    exact Prod.ext (Prod.mk.inj h0).1 (Prod.ext (Prod.mk.inj h0).2 hs2)

end Flow

end GC.GraphManifold.Assembly.FC39P0

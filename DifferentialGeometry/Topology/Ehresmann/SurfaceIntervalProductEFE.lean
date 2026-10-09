import DifferentialGeometry.Topology.Ehresmann.OpenIntervalTransportEFE
import DifferentialGeometry.Topology.Manifold.OneManifold.SmoothCompactOneDomainBCF
import DifferentialGeometry.Topology.Manifold.OneManifold.GraphAtlasCoverBCF
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Standard surface interval products over base arcs (draft 74 §5.2 D, D74-10, package S0)

Lane C14-EDP-FDCe. Review 74 D74-10: the whole `S² × I` / `T² × I` product over an arc of the slim
base needs proper-submersion flow transport; SLIM-STD only gives the standard type of ONE fibre.
The interfaces of draft 74 §5.2 D (names `…74` there, `…_EFE` here; FROZEN in
`build-logs/resume/state-C14-EDP-FDCe.md`):

* `ProperSmoothSurfaceSubmersion_EFE I M ι Bs`: a smooth map `f : M → H` with open source
  `f⁻¹(Bs)`, compact preimages of compact subsets of `Bs`, a graph atlas of `Bs`
  (`GraphAtlas1_BCF`, lane B-BCF134) and open regions covering `Bs`, inside the chart pieces, on
  whose preimages the chart coordinate `κ_i ∘ f` is a submersion.
* `SmoothEmbeddedBaseArc_EFE Bs`: a smooth regular injective arc `[0, 1] → Bs` (the arc fields of
  `SmoothCompactOneDomain_BCF`; constructors `SmoothCompactOneDomain_BCF.arc_EFE`, `loopArc_EFE`).
* `StandardWholeSurfaceFibre_EFE P IF F w`: a smooth embedding of a model surface `F` onto the WHOLE
  fibre `f⁻¹(w)`.
* `WholeSurfaceIntervalProduct_EFE P γ F₀`: the output contract — a smooth full-rank injective map
  `F × [0, 1] → M` with whole range `f⁻¹(γ[0, 1])`, `f ∘ map = γ ∘ pr₂`, equal to `F₀` on the first
  end, onto the whole fibre over `γ 1` on the second end.
* `exists_standard_surface_interval_product_EFE`: the kernel. Route (no global base coordinate):
  a Lebesgue subdivision of `[0, 1]` into windows inside single regions, one global level
  transport per window (`exists_global_interval_transport_EFE`), the composite
  `Ψ_t = D_n(a_n t) ∘ ⋯ ∘ D_1(a_1 t)` with smooth clamps `λ_k`, and `map (x, t) = Ψ_t (F₀ x)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology Manifold Filter
open scoped ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Topology

section Structures

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}
  {EF HF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]

/-- **A proper smooth submersion over a one-dimensional graph-atlas base** (draft 74 §5.2 D,
`ProperSmoothSurfaceSubmersion74`): `f : M → H` smooth, `f⁻¹(Bs)` open, compact preimages of
compact subsets of `Bs`, a graph atlas of `Bs`, and open regions covering `Bs`, inside the chart
pieces, over which the chart coordinate `κ_i ∘ f` is a submersion. -/
structure ProperSmoothSurfaceSubmersion_EFE (I : ModelWithCorners ℝ E HM) (M : Type*)
    [TopologicalSpace M] [ChartedSpace HM M] (ι : Type*) (Bs : Set H) where
  /-- The projection. -/
  toFun : M → H
  smooth : ContMDiff I 𝓘(ℝ, H) ∞ toFun
  isOpen_source : IsOpen (toFun ⁻¹' Bs)
  proper : ∀ K : Set H, IsCompact K → K ⊆ Bs → IsCompact (toFun ⁻¹' K)
  /-- The graph atlas of the base. -/
  atlas : GraphAtlas1_BCF ι Bs
  /-- The submersion regions. -/
  region : ι → Set H
  isOpen_region : ∀ i, IsOpen (region i)
  region_cover : Bs ⊆ ⋃ i, region i
  region_piece : ∀ i, region i ∩ Bs ⊆ atlas.param i '' atlas.dom i
  submersion : ∀ i x, toFun x ∈ region i ∩ Bs →
    Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) (fun y => atlas.coord i (toFun y)) x)

/-- **A smooth regular embedded base arc** (draft 74 §5.2 D, `SmoothEmbeddedBaseArc74`): the arc
fields of `SmoothCompactOneDomain_BCF`. -/
structure SmoothEmbeddedBaseArc_EFE (Bs : Set H) where
  /-- The parametrization on `[0, 1]`. -/
  toFun : ℝ → H
  smooth : ContDiffOn ℝ ∞ toFun (Icc 0 1)
  injOn : InjOn toFun (Icc 0 1)
  deriv_ne : ∀ t ∈ Icc (0 : ℝ) 1, derivWithin toFun (Icc 0 1) t ≠ 0
  mapsTo : MapsTo toFun (Icc 0 1) Bs

/-- **A standard whole fibre** (draft 74 §5.2 D, `StandardWholeSurfaceFibre74`): a smooth
embedding of the model surface `F` onto the WHOLE fibre over `w`. -/
structure StandardWholeSurfaceFibre_EFE (P : ProperSmoothSurfaceSubmersion_EFE I M ι Bs)
    (IF : ModelWithCorners ℝ EF HF) (F : Type*) [TopologicalSpace F] [ChartedSpace HF F]
    (w : H) where
  /-- The embedding. -/
  emb : F → M
  isSmoothEmbedding : IsSmoothEmbedding IF I ∞ emb
  range_eq : range emb = P.toFun ⁻¹' {w}

/-- **The whole interval product** (draft 74 §5.2 D, `WholeSurfaceIntervalProduct74`, output
contract of D74-10): a smooth full-rank injective map `F × [0, 1] → M` with whole range, over the
arc, equal to the given standard fibre on the first end and onto the whole fibre on the second. -/
structure WholeSurfaceIntervalProduct_EFE (P : ProperSmoothSurfaceSubmersion_EFE I M ι Bs)
    (γ : SmoothEmbeddedBaseArc_EFE Bs) (F₀ : StandardWholeSurfaceFibre_EFE P IF F (γ.toFun 0))
    where
  /-- The product map. -/
  map : F × Icc (0 : ℝ) 1 → M
  smooth : ContMDiff (IF.prod (𝓡∂ 1)) I ∞ map
  injective : Function.Injective map
  fullRank : ∀ z, Function.Injective (mfderiv (IF.prod (𝓡∂ 1)) I map z)
  range_eq : range map = P.toFun ⁻¹' (γ.toFun '' Icc 0 1)
  proj_eq : ∀ z, P.toFun (map z) = γ.toFun z.2
  start_eq : ∀ x, map (x, ⟨0, left_mem_Icc.mpr zero_le_one⟩) = F₀.emb x
  end_range : range (fun x => map (x, ⟨1, right_mem_Icc.mpr zero_le_one⟩)) =
    P.toFun ⁻¹' {γ.toFun 1}

end Structures

section Arcs

/-- A `1`-periodic function injective on `[0, 1)` is injective on every `[t₀, t₀ + 1)`. -/
theorem injOn_Ico_of_periodic_EFE {α : Type*} {φ : ℝ → α} (hper : Periodic φ 1)
    (hinj : InjOn φ (Ico 0 1))
    (t₀ : ℝ) : InjOn φ (Ico t₀ (t₀ + 1)) := by
  intro x hx y hy hxy
  have hfr : ∀ z : ℝ, φ (Int.fract z) = φ z := fun z => by
    have h := hper.sub_int_mul_eq (x := z) ⌊z⌋
    rw [mul_one] at h
    exact h
  have h := hinj ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩ ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩
    (by rw [hfr, hfr, hxy])
  obtain ⟨n, hn⟩ : ∃ n : ℤ, x - y = n := by
    refine ⟨⌊x⌋ - ⌊y⌋, ?_⟩
    have hx' := Int.fract_add_floor x
    have hy' := Int.fract_add_floor y
    push_cast
    linarith
  have hlt : |x - y| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  rw [hn] at hlt
  have hn0 : n = 0 := by
    have : |(n : ℝ)| < 1 := hlt
    rw [← Int.cast_abs] at this
    have h1 : |n| < 1 := by exact_mod_cast this
    exact Int.abs_lt_one_iff.mp h1
  rw [hn0, Int.cast_zero] at hn
  linarith

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {Bs : Set H}


/-- The arc `k` of a compact smooth one-dimensional domain as a base arc. -/
def _root_.DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF.arc_EFE
    (D : SmoothCompactOneDomain_BCF Bs) (k : Fin D.m) : SmoothEmbeddedBaseArc_EFE Bs where
  toFun := D.arc k
  smooth := D.arc_smooth k
  injOn := D.arc_injOn k
  deriv_ne := D.arc_deriv k
  mapsTo := fun t ht => D.subset_base (by
    rw [D.carrier_eq]
    exact Or.inl (mem_iUnion.mpr ⟨k, t, ht, rfl⟩))

/-- A proper sub-arc `s ↦ loop j (t₀ + ℓ s)`, `0 < ℓ < 1`, of a loop component as a base arc. -/
def _root_.DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF.loopArc_EFE
    (D : SmoothCompactOneDomain_BCF Bs) (j : Fin D.l) (t₀ ℓ : ℝ) (hℓ : ℓ ∈ Ioo (0 : ℝ) 1) :
    SmoothEmbeddedBaseArc_EFE Bs where
  toFun s := D.loop j (t₀ + ℓ * s)
  smooth :=
    ((D.loop_smooth j).comp (contDiff_const.add (contDiff_const.mul contDiff_id))).contDiffOn
  injOn := by
    intro s hs s' hs' h
    have hI : ∀ u ∈ Icc (0 : ℝ) 1, t₀ + ℓ * u ∈ Ico t₀ (t₀ + 1) := fun u hu =>
      ⟨by nlinarith [hu.1, hℓ.1], by nlinarith [hu.2, hℓ.1, hℓ.2]⟩
    have := injOn_Ico_of_periodic_EFE (D.loop_periodic j) (D.loop_injOn j) t₀ (hI s hs)
      (hI s' hs') h
    exact mul_left_cancel₀ hℓ.1.ne' (by linarith)
  deriv_ne := by
    intro s hs
    have hd : HasDerivAt (fun u => D.loop j (t₀ + ℓ * u))
        (ℓ • deriv (D.loop j) (t₀ + ℓ * s)) s := by
      have h1 : HasDerivAt (fun u : ℝ => t₀ + ℓ * u) ℓ s := by
        simpa using ((hasDerivAt_id s).const_mul ℓ).const_add t₀
      have h2 : HasDerivAt (D.loop j) (deriv (D.loop j) (t₀ + ℓ * s)) (t₀ + ℓ * s) :=
        ((D.loop_smooth j).differentiable (by simp) _).hasDerivAt
      exact h2.scomp s h1
    rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one s hs)]
    exact smul_ne_zero hℓ.1.ne' (D.loop_deriv j _)
  mapsTo := fun s _ => D.subset_base (by
    rw [D.carrier_eq]
    exact Or.inr (mem_iUnion.mpr ⟨j, mem_range_self _⟩))

end Arcs

section Clamp

/-- The smooth clamp at `c` of width `δ`: `= t` for `t ≤ c - δ`, `= c` for `t ≥ c`, with values in
`[c - δ, c]` for `t ≥ c - δ`. -/
def clamp_EFE (c δ t : ℝ) : ℝ :=
  c - δ + δ * ((t - (c - δ)) / δ + (1 - (t - (c - δ)) / δ) *
    Real.smoothTransition ((t - (c - δ)) / δ))

theorem contDiff_clamp_EFE (c δ : ℝ) : ContDiff ℝ ∞ (clamp_EFE c δ) := by
  unfold clamp_EFE
  have hu : ContDiff ℝ ∞ (fun t : ℝ => (t - (c - δ)) / δ) :=
    (contDiff_id.sub contDiff_const).div_const δ
  exact contDiff_const.add (contDiff_const.mul (hu.add ((contDiff_const.sub hu).mul
    (Real.smoothTransition.contDiff.comp hu))))

theorem clamp_of_le_EFE {c δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ c - δ) : clamp_EFE c δ t = t := by
  unfold clamp_EFE
  have hu : (t - (c - δ)) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  rw [Real.smoothTransition.zero_of_nonpos hu, mul_zero, add_zero, mul_div_cancel₀ _ hδ.ne']
  ring

theorem clamp_of_ge_EFE {c δ t : ℝ} (hδ : 0 < δ) (ht : c ≤ t) : clamp_EFE c δ t = c := by
  unfold clamp_EFE
  have hu : 1 ≤ (t - (c - δ)) / δ := by rw [le_div_iff₀ hδ]; linarith
  rw [Real.smoothTransition.one_of_one_le hu]
  ring

theorem clamp_mem_EFE {c δ t : ℝ} (hδ : 0 < δ) (ht : c - δ ≤ t) :
    clamp_EFE c δ t ∈ Icc (c - δ) c := by
  unfold clamp_EFE
  set u := (t - (c - δ)) / δ with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hδ.le
  have hs0 := Real.smoothTransition.nonneg u
  have hs1 := Real.smoothTransition.le_one u
  have hζ : u + (1 - u) * Real.smoothTransition u ∈ Icc (0 : ℝ) 1 := by
    by_cases h1 : u ≤ 1
    · constructor <;> nlinarith
    · rw [Real.smoothTransition.one_of_one_le (le_of_not_ge h1)]
      constructor <;> linarith
  constructor <;> nlinarith [hζ.1, hζ.2]

/-- The clamps of the composite transport: `λ_0 = 0`, `λ_k` the clamp at `k/n` of width `1/n` for
`0 < k < n`, `λ_k = id` for `k ≥ n`. -/
def lam_EFE (n k : ℕ) : ℝ → ℝ :=
  if k = 0 then fun _ => 0 else if k < n then clamp_EFE ((k : ℝ) / n) (1 / n) else id

theorem contDiff_lam_EFE (n k : ℕ) : ContDiff ℝ ∞ (lam_EFE n k) := by
  unfold lam_EFE
  split_ifs
  · exact contDiff_const
  · exact contDiff_clamp_EFE _ _
  · exact contDiff_id

theorem lam_mem_EFE {n k : ℕ} (hn : 0 < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    lam_EFE n k t ∈ Icc (0 : ℝ) 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ : (0 : ℝ) < 1 / n := by positivity
  unfold lam_EFE
  split_ifs with h0 hk
  · exact ⟨le_rfl, zero_le_one⟩
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    have hc : (k : ℝ) / n ≤ 1 := by rw [div_le_one hn']; linarith
    have hcd : 0 ≤ (k : ℝ) / n - 1 / n := by
      rw [← sub_div]; exact div_nonneg (by linarith) hn'.le
    by_cases hle : t ≤ (k : ℝ) / n - 1 / n
    · rw [clamp_of_le_EFE hδ hle]; exact ht
    · have hm := clamp_mem_EFE (c := (k : ℝ) / n) hδ (le_of_not_ge hle)
      exact ⟨hcd.trans hm.1, hm.2.trans hc⟩
  · exact ht

theorem lam_zero_EFE {n k : ℕ} (hn : 0 < n) : lam_EFE n k 0 = 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ : (0 : ℝ) < 1 / n := by positivity
  unfold lam_EFE
  split_ifs with h0 hk
  · rfl
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    refine clamp_of_le_EFE hδ ?_
    rw [← sub_div]; exact div_nonneg (by linarith) hn'.le
  · rfl

theorem lam_self_EFE {n : ℕ} (hn : 0 < n) : lam_EFE n n = id := by
  unfold lam_EFE
  simp [hn.ne']

/-- **The step property of the clamps**: for `k < n` and `t ∈ [0, 1]`, either
`λ_k t = λ_{k+1} t`, or
both lie in the window `[(k-1)/n, (k+1)/n] ∩ [0, 1]`. -/
theorem lam_step_EFE {n k : ℕ} (hkn : k < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    lam_EFE n k t = lam_EFE n (k + 1) t ∨
      (lam_EFE n k t ∈ Icc (((k : ℝ) - 1) / n) (((k : ℝ) + 1) / n) ∩ Icc 0 1 ∧
        lam_EFE n (k + 1) t ∈ Icc (((k : ℝ) - 1) / n) (((k : ℝ) + 1) / n) ∩ Icc 0 1) := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hkn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ : (0 : ℝ) < 1 / n := by positivity
  have hkn' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
  have hm0 := lam_mem_EFE (k := k) hn ht
  have hm1 := lam_mem_EFE (k := k + 1) hn ht
  -- the next clamp, as a function of `t`
  have hnext : ∀ {t : ℝ}, t ∈ Icc (0 : ℝ) 1 → (k : ℝ) / n - 1 / n ≤ t →
      lam_EFE n (k + 1) t ∈ Icc (((k : ℝ) - 1) / n) (((k : ℝ) + 1) / n) := by
    intro t ht hkt
    have hlo : ((k : ℝ) - 1) / n ≤ t := by rw [sub_div]; exact hkt
    unfold lam_EFE
    simp only [Nat.succ_ne_zero k, ↓reduceIte]
    split_ifs with hk1
    · by_cases hle : t ≤ ((k + 1 : ℕ) : ℝ) / n - 1 / n
      · rw [clamp_of_le_EFE hδ hle]
        refine ⟨hlo, ?_⟩
        have : ((k + 1 : ℕ) : ℝ) / n - 1 / n = (k : ℝ) / n := by push_cast; ring
        rw [this] at hle
        exact hle.trans (div_le_div_of_nonneg_right (by linarith) hn'.le)
      · have hm := clamp_mem_EFE (c := ((k + 1 : ℕ) : ℝ) / n) hδ (le_of_not_ge hle)
        have h1 : ((k + 1 : ℕ) : ℝ) / n - 1 / n = (k : ℝ) / n := by push_cast; ring
        have h2 : ((k + 1 : ℕ) : ℝ) / n = ((k : ℝ) + 1) / n := by push_cast; ring
        refine ⟨le_trans ?_ ((le_of_eq h1.symm).trans hm.1), hm.2.trans (le_of_eq h2)⟩
        exact div_le_div_of_nonneg_right (by linarith) hn'.le
    · have hk1' : (n : ℝ) ≤ k + 1 := by exact_mod_cast not_lt.mp hk1
      refine ⟨hlo, ?_⟩
      change t ≤ ((k : ℝ) + 1) / n
      rw [le_div_iff₀ hn']
      nlinarith [ht.2]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · right
    have h00 : lam_EFE n 0 t = 0 := by simp [lam_EFE]
    refine ⟨⟨⟨?_, ?_⟩, hm0⟩, ⟨hnext ht ?_, hm1⟩⟩
    · rw [h00]; push_cast; rw [zero_sub, neg_div]; exact neg_nonpos.mpr hδ.le
    · rw [h00]; push_cast; rw [zero_add]; exact hδ.le
    · push_cast; rw [zero_div, zero_sub]; linarith [ht.1, hδ]
  · have hk : lam_EFE n k = clamp_EFE ((k : ℝ) / n) (1 / n) := by
      unfold lam_EFE; simp only [hk0.ne', hkn, ↓reduceIte]
    by_cases hle : t ≤ (k : ℝ) / n - 1 / n
    · left
      rw [hk, clamp_of_le_EFE hδ hle]
      unfold lam_EFE
      simp only [Nat.succ_ne_zero k, ↓reduceIte]
      split_ifs with hk1
      · refine (clamp_of_le_EFE hδ ?_).symm
        have : ((k + 1 : ℕ) : ℝ) / n - 1 / n = (k : ℝ) / n := by push_cast; ring
        rw [this]
        exact hle.trans (by linarith)
      · rfl
    · right
      have hm := clamp_mem_EFE (c := (k : ℝ) / n) hδ (le_of_not_ge hle)
      refine ⟨⟨⟨?_, ?_⟩, hm0⟩, ⟨hnext ht (le_of_not_ge hle), hm1⟩⟩
      · rw [hk, sub_div]; exact hm.1
      · rw [hk]; exact hm.2.trans (div_le_div_of_nonneg_right (by linarith) hn'.le)

end Clamp

section Kernel

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}

namespace ProperSmoothSurfaceSubmersion_EFE

/-- The open set of chart parameters whose image lies in the submersion region. -/
theorem isOpen_good_EFE (P : ProperSmoothSurfaceSubmersion_EFE I M ι Bs) (i : ι) :
    IsOpen (P.atlas.dom i ∩ P.atlas.param i ⁻¹' P.region i) :=
  (P.atlas.param_smooth i).continuousOn.isOpen_inter_preimage (P.atlas.isOpen_dom i)
    (P.isOpen_region i)

/-- **A window of an arc inside one region** has chart parameters in a closed interval of good
parameters, and the arc is the chart parametrization of its parameters there. -/
theorem arc_window_EFE (P : ProperSmoothSurfaceSubmersion_EFE I M ι Bs)
    (γ : SmoothEmbeddedBaseArc_EFE Bs) (i : ι) {W : Set ℝ} (hWc : IsCompact W)
    (hWp : IsPreconnected W) (hWne : W.Nonempty) (hW01 : W ⊆ Icc 0 1)
    (hreg : ∀ u ∈ W, γ.toFun u ∈ P.region i) :
    ∃ α β : ℝ, α ≤ β ∧ Icc α β ⊆ P.atlas.dom i ∩ P.atlas.param i ⁻¹' P.region i ∧
      ∀ u ∈ W, P.atlas.coord i (γ.toFun u) ∈ Icc α β ∧
        P.atlas.param i (P.atlas.coord i (γ.toFun u)) = γ.toFun u := by
  have hpt : ∀ u ∈ W, P.atlas.coord i (γ.toFun u) ∈ P.atlas.dom i ∧
      P.atlas.param i (P.atlas.coord i (γ.toFun u)) = γ.toFun u := by
    intro u hu
    obtain ⟨b, hb, he⟩ := P.region_piece i ⟨hreg u hu, γ.mapsTo (hW01 hu)⟩
    rw [← he, P.atlas.coord_param i b hb]
    exact ⟨hb, rfl⟩
  set σ : ℝ → ℝ := fun u => P.atlas.coord i (γ.toFun u) with hσ
  have hσc : ContinuousOn σ W :=
    (P.atlas.coord i).continuous.comp_continuousOn (γ.smooth.continuousOn.mono hW01)
  obtain ⟨u₀, hu₀, hmin⟩ := hWc.exists_isMinOn hWne hσc
  obtain ⟨u₁, hu₁, hmax⟩ := hWc.exists_isMaxOn hWne hσc
  have hS : IsPreconnected (σ '' W) := hWp.image σ hσc
  refine ⟨σ u₀, σ u₁, hmin hu₁, ?_, fun u hu => ⟨⟨hmin hu, hmax hu⟩, (hpt u hu).2⟩⟩
  intro y hy
  obtain ⟨u, hu, rfl⟩ := hS.Icc_subset (mem_image_of_mem σ hu₀) (mem_image_of_mem σ hu₁) hy
  refine ⟨(hpt u hu).1, ?_⟩
  change P.atlas.param i (σ u) ∈ P.region i
  rw [(hpt u hu).2]
  exact hreg u hu

/-- **A Lebesgue subdivision** of `[0, 1]` for an arc: there are `n > 0` and regions `c k` with
`γ ([(k - 1)/n, (k + 1)/n] ∩ [0, 1]) ⊆ region (c k)` for every `k`. -/
theorem exists_subdivision_EFE (P : ProperSmoothSurfaceSubmersion_EFE I M ι Bs)
    (γ : SmoothEmbeddedBaseArc_EFE Bs) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : ℕ → ι, ∀ k : ℕ,
      ∀ u ∈ Icc (((k : ℝ) - 1) / n) (((k : ℝ) + 1) / n) ∩ Icc 0 1,
        γ.toFun u ∈ P.region (c k) := by
  have hloc : ∀ i, ∃ O : Set ℝ, IsOpen O ∧ γ.toFun ⁻¹' P.region i ∩ Icc 0 1 = O ∩ Icc 0 1 :=
    fun i => continuousOn_iff'.mp γ.smooth.continuousOn (P.region i) (P.isOpen_region i)
  choose O hO hOeq using hloc
  have hcov : Icc (0 : ℝ) 1 ⊆ ⋃ i, O i := by
    intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp (P.region_cover (γ.mapsTo ht))
    have h : t ∈ O i ∩ Icc 0 1 := (hOeq i) ▸ ⟨hi, ht⟩
    exact mem_iUnion.mpr ⟨i, h.1⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hO hcov
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have hn' : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hnδ : (1 : ℝ) / (n + 1 : ℕ) < δ := by push_cast; exact hn
  have hctr : ∀ k : ℕ, ∃ i, ∀ u ∈ Icc (((k : ℝ) - 1) / (n + 1 : ℕ))
      (((k : ℝ) + 1) / (n + 1 : ℕ)) ∩ Icc 0 1, u ∈ O i := by
    intro k
    set c : ℝ := (projIcc (0 : ℝ) 1 zero_le_one ((k : ℝ) / (n + 1 : ℕ)) : ℝ) with hc
    obtain ⟨i, hi⟩ := hball c (projIcc (0 : ℝ) 1 zero_le_one _).2
    refine ⟨i, fun u hu => hi ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) / (n + 1 : ℕ) := div_nonneg (Nat.cast_nonneg k) hn'.le
    have hlo : ((k : ℝ) - 1) / (n + 1 : ℕ) = (k : ℝ) / (n + 1 : ℕ) - 1 / (n + 1 : ℕ) := by
      rw [sub_div]
    have hhi : ((k : ℝ) + 1) / (n + 1 : ℕ) = (k : ℝ) / (n + 1 : ℕ) + 1 / (n + 1 : ℕ) := by
      rw [add_div]
    rw [hlo] at hu
    rw [hhi] at hu
    by_cases hk1 : (k : ℝ) / (n + 1 : ℕ) ≤ 1
    · have hcv : c = (k : ℝ) / (n + 1 : ℕ) := by
        rw [hc, projIcc_of_mem _ ⟨hk0, hk1⟩]
      rw [hcv]
      constructor <;> linarith [hu.1.1, hu.1.2]
    · have hcv : c = 1 := by
        rw [hc, projIcc_of_right_le _ (le_of_not_ge hk1)]
      rw [hcv]
      constructor <;> linarith [hu.1.1, hu.2.2, hu.2.1, le_of_not_ge hk1]
  choose cI hcI using hctr
  refine ⟨n + 1, Nat.succ_pos n, cI, fun k u hu => ?_⟩
  have h : u ∈ γ.toFun ⁻¹' P.region (cI k) ∩ Icc 0 1 := (hOeq (cI k)).symm ▸ ⟨hcI k u hu, hu.2⟩
  exact h.1

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M]

/-- **Level transport in one chart** (from `exists_global_interval_transport_EFE` on the open set
`f⁻¹(ψ_i(a', b'))`): for a closed interval `[α, β]` of good parameters there is a jointly smooth
family of diffeomorphisms of `M` with `D 0 = id`, `(D s)⁻¹ = D (-s)`, moving the whole fibre over
`ψ_i b` onto the whole fibre over `ψ_i t` by `D (t - b)`, for `b, t ∈ [α, β]`. -/
theorem exists_chart_transport_EFE (P : ProperSmoothSurfaceSubmersion_EFE I M ι Bs) (i : ι)
    {α β : ℝ} (hαβ : α ≤ β) (hI : Icc α β ⊆ P.atlas.dom i ∩ P.atlas.param i ⁻¹' P.region i) :
    ∃ D : ℝ → M ≃ₘ⟮I, I⟯ M,
      ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => D p.1 p.2) ∧
      (∀ y, D 0 y = y) ∧ (∀ s, (D s).symm = D (-s)) ∧
      ∀ b ∈ Icc α β, ∀ x, P.toFun x = P.atlas.param i b → ∀ t ∈ Icc α β,
        P.toFun (D (t - b) x) = P.atlas.param i t := by
  set O := P.atlas.dom i ∩ P.atlas.param i ⁻¹' P.region i with hOdef
  have hO : IsOpen O := P.isOpen_good_EFE i
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := α) (b := β))
    (c := fun _ : Unit => O) (fun _ => hO) (fun x hx => mem_iUnion.mpr ⟨(), hI hx⟩)
  have hwide : Icc (α - δ / 2) (β + δ / 2) ⊆ O := by
    intro y hy
    by_cases h1 : y < α
    · obtain ⟨_, h⟩ := hball α (left_mem_Icc.mpr hαβ)
      exact h (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1])
    · by_cases h2 : β < y
      · obtain ⟨_, h⟩ := hball β (right_mem_Icc.mpr hαβ)
        exact h (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hy.2])
      · exact hI ⟨not_lt.mp h1, not_lt.mp h2⟩
  set a' := α - δ / 2 with ha'
  set b' := β + δ / 2 with hb'
  have hIoo : Ioo a' b' ⊆ O := Ioo_subset_Icc_self.trans hwide
  obtain ⟨V, hV, hVB⟩ := P.atlas.image_relOpen_BCF isOpen_Ioo (hIoo.trans inter_subset_left)
  let Ω : TopologicalSpace.Opens M :=
    ⟨P.toFun ⁻¹' V ∩ P.toFun ⁻¹' Bs, (hV.preimage P.smooth.continuous).inter P.isOpen_source⟩
  have hΩ : ∀ x, x ∈ Ω ↔ ∃ b ∈ Ioo a' b', P.toFun x = P.atlas.param i b := by
    intro x
    change P.toFun x ∈ V ∧ P.toFun x ∈ Bs ↔ _
    constructor
    · intro h
      obtain ⟨b, hb, he⟩ : P.toFun x ∈ P.atlas.param i '' Ioo a' b' := hVB ▸ h
      exact ⟨b, hb, he.symm⟩
    · rintro ⟨b, hb, he⟩
      have h : P.toFun x ∈ V ∩ Bs := hVB ▸ ⟨b, hb, he.symm⟩
      exact h
  let g : M → ℝ := fun x => P.atlas.coord i (P.toFun x)
  have hg : ContMDiff I 𝓘(ℝ) ∞ g := (P.atlas.coord i).contDiff.comp_contMDiff P.smooth
  have hgpar : ∀ b ∈ Ioo a' b', P.atlas.coord i (P.atlas.param i b) = b := fun b hb =>
    P.atlas.coord_param i b (hIoo hb).1
  have hgx : ∀ x b, b ∈ Ioo a' b' → P.toFun x = P.atlas.param i b → g x = b := by
    intro x b hb he
    change P.atlas.coord i (P.toFun x) = b
    rw [he, hgpar b hb]
  have hprop : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo a' b' →
      IsCompact {x | x ∈ Ω ∧ g x ∈ K} := by
    intro K hK hKI
    have heq : {x | x ∈ Ω ∧ g x ∈ K} = P.toFun ⁻¹' (P.atlas.param i '' K) := by
      ext x
      constructor
      · rintro ⟨hx, hgK⟩
        obtain ⟨b, hb, he⟩ := (hΩ x).mp hx
        refine ⟨b, ?_, he.symm⟩
        rw [← hgx x b hb he]
        exact hgK
      · rintro ⟨b, hb, he⟩
        exact ⟨(hΩ x).mpr ⟨b, hKI hb, he.symm⟩, by rw [hgx x b (hKI hb) he.symm]; exact hb⟩
    rw [heq]
    refine P.proper _ (hK.image_of_continuousOn ((P.atlas.param_smooth i).continuousOn.mono
      (hKI.trans (hIoo.trans inter_subset_left)))) ?_
    rintro _ ⟨b, hb, rfl⟩
    exact P.atlas.param_mem_BCF (hIoo (hKI hb)).1
  have hsub : ∀ x ∈ Ω, Surjective (mfderiv I 𝓘(ℝ) g x) := by
    intro x hx
    obtain ⟨b, hb, he⟩ := (hΩ x).mp hx
    refine P.submersion i x ⟨?_, ?_⟩
    · rw [he]; exact (hIoo hb).2
    · rw [he]; exact P.atlas.param_mem_BCF (hIoo hb).1
  obtain ⟨D, hDj, hD0, hDs, -, hDΩ, hDlev⟩ :=
    exists_global_interval_transport_EFE Ω g hg hprop hsub hαβ (by linarith) (by linarith)
  refine ⟨D, hDj, hD0, hDs, ?_⟩
  intro b hb x hx t ht
  have hbI : b ∈ Ioo a' b' := ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hxΩ : x ∈ Ω := (hΩ x).mpr ⟨b, hbI, hx⟩
  have hgb := hgx x b hbI hx
  have hlev := hDlev x hxΩ (hgb ▸ hb) t ht
  rw [hgb] at hlev
  obtain ⟨b'', hb'', he''⟩ := (hΩ _).mp (hDΩ (t - b) x hxΩ)
  rw [he'', ← hgx _ b'' hb'' he'', hlev]

end ProperSmoothSurfaceSubmersion_EFE

end Kernel

section ArcCalculus

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {Bs : Set H}

/-- A function smooth within `[0, 1]` is smooth on the manifold with boundary `[0, 1]`. -/
theorem contMDiff_Icc_of_contDiffOn_EFE {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : ℝ → G} (hg : ContDiffOn ℝ ∞ g (Icc 0 1)) :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ, G) ∞ (fun s : Icc (0 : ℝ) 1 => g s) := by
  apply contMDiffOn_comp_projIcc_iff.mp
  refine (contMDiffOn_iff_contDiffOn.mpr hg).congr ?_
  intro z hz
  simp [projIcc_of_mem zero_le_one hz]

/-- The arc on the manifold with boundary `[0, 1]` is smooth. -/
theorem contMDiff_arc_EFE (γ : SmoothEmbeddedBaseArc_EFE Bs) :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ, H) ∞ (fun s : Icc (0 : ℝ) 1 => γ.toFun s) :=
  contMDiff_Icc_of_contDiffOn_EFE γ.smooth

/-- The differential of the arc on `[0, 1]` sends `1` to the derivative within `[0, 1]`. -/
theorem mfderiv_arc_one_EFE (γ : SmoothEmbeddedBaseArc_EFE Bs) (t : Icc (0 : ℝ) 1) :
    mfderiv (𝓡∂ 1) 𝓘(ℝ, H) (fun s : Icc (0 : ℝ) 1 => γ.toFun s) t 1 =
      derivWithin γ.toFun (Icc 0 1) t := by
  rw [← mfderivWithin_comp_projIcc_one]
  have A : mfderivWithin 𝓘(ℝ) 𝓘(ℝ, H)
      ((fun s : Icc (0 : ℝ) 1 => γ.toFun s) ∘ projIcc 0 1 zero_le_one) (Icc 0 1) t 1 =
      mfderivWithin 𝓘(ℝ) 𝓘(ℝ, H) γ.toFun (Icc 0 1) t 1 := by
    congr 1
    apply mfderivWithin_congr_of_mem _ t.2
    intro z hz
    simp [projIcc_of_mem zero_le_one hz]
  rw [A, mfderivWithin_eq_fderivWithin]
  rfl

/-- **The arc is an immersion of `[0, 1]`**: its differential is injective. -/
theorem mfderiv_arc_injective_EFE (γ : SmoothEmbeddedBaseArc_EFE Bs) (t : Icc (0 : ℝ) 1) :
    Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, H) (fun s : Icc (0 : ℝ) 1 => γ.toFun s) t) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  set L := mfderiv (𝓡∂ 1) 𝓘(ℝ, H) (fun s : Icc (0 : ℝ) 1 => γ.toFun s) t with hL
  have hL1 : L 1 = derivWithin γ.toFun (Icc 0 1) t := mfderiv_arc_one_EFE γ t
  have hne : (1 : TangentSpace (𝓡∂ 1) t) ≠ 0 := by
    intro h
    have h1 := mfderiv_subtypeVal_Icc_one t
    rw [h, map_zero] at h1
    exact absurd h1 (by norm_num : (0 : ℝ) ≠ 1)
  have hrank : Module.finrank ℝ (TangentSpace (𝓡∂ 1) t) = 1 := finrank_euclideanSpace_fin
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : TangentSpace (𝓡∂ 1) t) hne).mp hrank v
  rw [← hc, map_smul, hL1] at hv
  have hc0 : c = 0 := by
    rcases smul_eq_zero.mp hv with h | h
    · exact h
    · exact absurd h (γ.deriv_ne t t.2)
  rw [← hc, hc0, zero_smul]

end ArcCalculus

section Composite

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}

/-- The shift of step `k` at time `t`: `κ_k (γ (λ_{k+1} t)) - κ_k (γ (λ_k t))`. -/
def stepShift_EFE (n : ℕ) (κ : ℕ → H →L[ℝ] ℝ) (γ : ℝ → H) (k : ℕ) (t : ℝ) : ℝ :=
  κ k (γ (lam_EFE n (k + 1) t)) - κ k (γ (lam_EFE n k t))

/-- The composite transport `Ψ_k t = D_{k-1} (a_{k-1} t) ∘ ⋯ ∘ D_0 (a_0 t)`. -/
def compTransport_EFE (n : ℕ) (κ : ℕ → H →L[ℝ] ℝ) (D : ℕ → ℝ → M ≃ₘ⟮I, I⟯ M) (γ : ℝ → H) :
    ℕ → ℝ → M ≃ₘ⟮I, I⟯ M
  | 0, _ => Diffeomorph.refl I M ∞
  | k + 1, t => (compTransport_EFE n κ D γ k t).trans (D k (stepShift_EFE n κ γ k t))

theorem compTransport_zero_apply_EFE (n : ℕ) (κ : ℕ → H →L[ℝ] ℝ) (D : ℕ → ℝ → M ≃ₘ⟮I, I⟯ M)
    (γ : ℝ → H) (t : ℝ) (y : M) : compTransport_EFE n κ D γ 0 t y = y :=
  rfl

theorem compTransport_succ_apply_EFE (n : ℕ) (κ : ℕ → H →L[ℝ] ℝ) (D : ℕ → ℝ → M ≃ₘ⟮I, I⟯ M)
    (γ : ℝ → H) (k : ℕ) (t : ℝ) (y : M) :
    compTransport_EFE n κ D γ (k + 1) t y =
      D k (stepShift_EFE n κ γ k t) (compTransport_EFE n κ D γ k t y) :=
  rfl

/-- The step shifts are smooth within `[0, 1]`. -/
theorem contDiffOn_stepShift_EFE {n : ℕ} (hn : 0 < n) (κ : ℕ → H →L[ℝ] ℝ) {γ : ℝ → H}
    (hγ : ContDiffOn ℝ ∞ γ (Icc 0 1)) (k : ℕ) :
    ContDiffOn ℝ ∞ (stepShift_EFE n κ γ k) (Icc 0 1) := by
  have hl : ∀ j, ContDiffOn ℝ ∞ (fun t => γ (lam_EFE n j t)) (Icc 0 1) := fun j =>
    hγ.comp (contDiff_lam_EFE n j).contDiffOn (fun t ht => lam_mem_EFE hn ht)
  exact ((κ k).contDiff.comp_contDiffOn (hl (k + 1))).sub ((κ k).contDiff.comp_contDiffOn (hl k))

/-- At time `0` all step shifts vanish. -/
theorem stepShift_zero_EFE {n : ℕ} (hn : 0 < n) (κ : ℕ → H →L[ℝ] ℝ) (γ : ℝ → H) (k : ℕ) :
    stepShift_EFE n κ γ k 0 = 0 := by
  unfold stepShift_EFE
  rw [lam_zero_EFE hn, lam_zero_EFE hn, sub_self]

/-- At time `0` the composite transport is the identity. -/
theorem compTransport_at_zero_EFE {n : ℕ} (hn : 0 < n) (κ : ℕ → H →L[ℝ] ℝ)
    {D : ℕ → ℝ → M ≃ₘ⟮I, I⟯ M} (hD0 : ∀ k y, D k 0 y = y) (γ : ℝ → H) (k : ℕ) (y : M) :
    compTransport_EFE n κ D γ k 0 y = y := by
  induction k with
  | zero => rfl
  | succ k ih => rw [compTransport_succ_apply_EFE, stepShift_zero_EFE hn, hD0, ih]

/-- **Joint smoothness of the composite transport** applied to a smooth map `e : F → M`. -/
theorem contMDiff_compTransport_EFE {EF HF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF]
    [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F]
    [ChartedSpace HF F] {n : ℕ} (hn : 0 < n) (κ : ℕ → H →L[ℝ] ℝ) {D : ℕ → ℝ → M ≃ₘ⟮I, I⟯ M}
    (hDj : ∀ k, ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => D k p.1 p.2)) {γ : ℝ → H}
    (hγ : ContDiffOn ℝ ∞ γ (Icc 0 1)) {e : F → M} (he : ContMDiff IF I ∞ e) (k : ℕ) :
    ContMDiff (IF.prod (𝓡∂ 1)) I ∞
      (fun z : F × Icc (0 : ℝ) 1 => compTransport_EFE n κ D γ k z.2 (e z.1)) := by
  induction k with
  | zero => exact he.comp contMDiff_fst
  | succ k ih =>
    have ha : ContMDiff (IF.prod (𝓡∂ 1)) 𝓘(ℝ) ∞
        (fun z : F × Icc (0 : ℝ) 1 => stepShift_EFE n κ γ k z.2) :=
      (contMDiff_Icc_of_contDiffOn_EFE (contDiffOn_stepShift_EFE hn κ hγ k)).comp contMDiff_snd
    exact (hDj k).comp (ha.prodMk ih)

namespace ProperSmoothSurfaceSubmersion_EFE

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M]

/-- **Step transports along an arc**: a subdivision `n > 0`, chart coordinates `κ k` and global
level transports `D k` (jointly smooth, `D k 0 = id`, `(D k s)⁻¹ = D k (-s)`) such that for `k < n`
and `u, v ∈ {λ_k t, λ_{k+1} t}` the diffeomorphism `D k (κ k (γ v) - κ k (γ u))` carries the
fibre over `γ u` into the fibre over `γ v`. -/
theorem exists_step_transports_EFE (P : ProperSmoothSurfaceSubmersion_EFE I M ι Bs)
    (γ : SmoothEmbeddedBaseArc_EFE Bs) :
    ∃ n : ℕ, 0 < n ∧ ∃ (κ : ℕ → H →L[ℝ] ℝ) (D : ℕ → ℝ → M ≃ₘ⟮I, I⟯ M),
      (∀ k, ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => D k p.1 p.2)) ∧
      (∀ k y, D k 0 y = y) ∧ (∀ k s, (D k s).symm = D k (-s)) ∧
      ∀ k < n, ∀ t ∈ Icc (0 : ℝ) 1, ∀ u v : ℝ,
        (u = lam_EFE n k t ∨ u = lam_EFE n (k + 1) t) →
        (v = lam_EFE n k t ∨ v = lam_EFE n (k + 1) t) → ∀ x, P.toFun x = γ.toFun u →
          P.toFun (D k (κ k (γ.toFun v) - κ k (γ.toFun u)) x) = γ.toFun v := by
  obtain ⟨n, hn, c, hc⟩ := P.exists_subdivision_EFE γ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hper : ∀ k : ℕ, ∃ (κ : H →L[ℝ] ℝ) (Dk : ℝ → M ≃ₘ⟮I, I⟯ M),
      ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => Dk p.1 p.2) ∧ (∀ y, Dk 0 y = y) ∧
      (∀ s, (Dk s).symm = Dk (-s)) ∧
      (k < n → ∀ u ∈ Icc (((k : ℝ) - 1) / n) (((k : ℝ) + 1) / n) ∩ Icc 0 1,
        ∀ v ∈ Icc (((k : ℝ) - 1) / n) (((k : ℝ) + 1) / n) ∩ Icc 0 1, ∀ x,
          P.toFun x = γ.toFun u → P.toFun (Dk (κ (γ.toFun v) - κ (γ.toFun u)) x) = γ.toFun v) := by
    intro k
    by_cases hk : k < n
    · set W := Icc (((k : ℝ) - 1) / n) (((k : ℝ) + 1) / n) ∩ Icc 0 1 with hW
      have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
      have hkW : (k : ℝ) / n ∈ W := by
        refine ⟨⟨div_le_div_of_nonneg_right (by linarith) hn'.le,
          div_le_div_of_nonneg_right (by linarith) hn'.le⟩,
          div_nonneg (Nat.cast_nonneg k) hn'.le, ?_⟩
        rw [div_le_one hn']
        linarith
      have hWc : IsCompact W := isCompact_Icc.inter_right isClosed_Icc
      have hWp : IsPreconnected W := by
        rw [hW, Icc_inter_Icc]
        exact isPreconnected_Icc
      obtain ⟨α, β, hαβ, hI, hW'⟩ := P.arc_window_EFE γ (c k) hWc hWp ⟨_, hkW⟩
        inter_subset_right (fun u hu => hc k u hu)
      obtain ⟨Dk, hDj, hD0, hDs, hlev⟩ := P.exists_chart_transport_EFE (c k) hαβ hI
      refine ⟨P.atlas.coord (c k), Dk, hDj, hD0, hDs, fun _ u hu v hv x hx => ?_⟩
      have h1 := hW' u hu
      have h2 := hW' v hv
      rw [hlev _ h1.1 x (by rw [h1.2]; exact hx) _ h2.1, h2.2]
    · refine ⟨0, fun _ => Diffeomorph.refl I M ∞, contMDiff_snd, fun _ => rfl,
        fun _ => Diffeomorph.symm_refl, fun h => absurd h hk⟩
  choose κ D hDj hD0 hDs hlev using hper
  refine ⟨n, hn, κ, D, hDj, hD0, hDs, ?_⟩
  intro k hk t ht u v hu hv x hx
  rcases lam_step_EFE hk ht with heq | ⟨h1, h2⟩
  · have huv : u = v := by
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · rfl
      · exact heq
      · exact heq.symm
      · rfl
    subst huv
    rw [sub_self, hD0]
    exact hx
  · have hmem : ∀ w : ℝ, (w = lam_EFE n k t ∨ w = lam_EFE n (k + 1) t) →
        w ∈ Icc (((k : ℝ) - 1) / n) (((k : ℝ) + 1) / n) ∩ Icc 0 1 := by
      rintro w (rfl | rfl)
      · exact h1
      · exact h2
    exact hlev k hk u (hmem u hu) v (hmem v hv) x hx

end ProperSmoothSurfaceSubmersion_EFE

end Composite

section MainKernel

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}
  {EF HF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]

/-- **Standard surface interval product over a base arc** (draft 74 §5.2 D, D74-10, kernel S0):
for a proper smooth submersion over a graph-atlas base, a smooth regular embedded base arc `γ` and
a smooth embedding `F₀` of a model manifold onto the whole fibre over `γ 0`, the composite level
transport `map (x, t) = Ψ_t (F₀ x)` is a smooth full-rank injective map `F × [0, 1] → M` onto the
whole preimage of `γ [0, 1]`, over `γ`, equal to `F₀` on the first end and onto the whole fibre over
`γ 1` on the second end. (The frozen instance `[IsManifold IF ∞ F]` is not needed and dropped.) -/
theorem exists_standard_surface_interval_product_EFE [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SecondCountableTopology M]
    (P : ProperSmoothSurfaceSubmersion_EFE I M ι Bs) (γ : SmoothEmbeddedBaseArc_EFE Bs)
    (F₀ : StandardWholeSurfaceFibre_EFE P IF F (γ.toFun 0)) :
    Nonempty (WholeSurfaceIntervalProduct_EFE P γ F₀) := by
  obtain ⟨n, hn, κ, D, hDj, hD0, hDs, hstep⟩ := P.exists_step_transports_EFE γ
  have hF0 : ∀ x, P.toFun (F₀.emb x) = γ.toFun 0 := fun x => by
    have h := mem_range_self (f := F₀.emb) x
    rw [F₀.range_eq] at h
    exact h
  -- forward fibre bookkeeping
  have hfwd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ k ≤ n, ∀ x, P.toFun x = γ.toFun 0 →
      P.toFun (compTransport_EFE n κ D γ.toFun k t x) = γ.toFun (lam_EFE n k t) := by
    intro t ht k
    induction k with
    | zero =>
      intro _ x hx
      rw [compTransport_zero_apply_EFE]
      simpa [lam_EFE] using hx
    | succ k ih =>
      intro hk x hx
      rw [compTransport_succ_apply_EFE]
      exact hstep k (by omega) t ht _ _ (Or.inl rfl) (Or.inr rfl) _ (ih (by omega) x hx)
  -- backward fibre bookkeeping
  have hbwd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ k ≤ n, ∀ y, P.toFun y = γ.toFun (lam_EFE n k t) →
      P.toFun ((compTransport_EFE n κ D γ.toFun k t).symm y) = γ.toFun 0 := by
    intro t ht k
    induction k with
    | zero =>
      intro _ y hy
      change P.toFun ((Diffeomorph.refl I M ∞).symm y) = _
      rw [Diffeomorph.symm_refl]
      simpa [lam_EFE] using hy
    | succ k ih =>
      intro hk y hy
      change P.toFun (((compTransport_EFE n κ D γ.toFun k t).trans
        (D k (stepShift_EFE n κ γ.toFun k t))).symm y) = _
      rw [Diffeomorph.symm_trans', Diffeomorph.coe_trans, Function.comp_apply, hDs]
      refine ih (by omega) _ ?_
      have h := hstep k (by omega) t ht _ _ (Or.inr rfl) (Or.inl rfl) y hy
      have hneg : -stepShift_EFE n κ γ.toFun k t =
          κ k (γ.toFun (lam_EFE n k t)) - κ k (γ.toFun (lam_EFE n (k + 1) t)) := by
        unfold stepShift_EFE
        ring
      rw [hneg]
      exact h
  obtain ⟨map, hmap⟩ : ∃ map : F × Icc (0 : ℝ) 1 → M,
      ∀ z, map z = compTransport_EFE n κ D γ.toFun n z.2 (F₀.emb z.1) := ⟨_, fun _ => rfl⟩
  have hproj : ∀ z, P.toFun (map z) = γ.toFun z.2 := fun z => by
    have h := hfwd z.2 z.2.2 n le_rfl (F₀.emb z.1) (hF0 z.1)
    rw [lam_self_EFE hn, id_eq] at h
    rw [hmap]
    exact h
  have hsurj : ∀ t (ht : t ∈ Icc (0 : ℝ) 1) y, P.toFun y = γ.toFun t →
      ∃ x, map (x, ⟨t, ht⟩) = y := by
    intro t ht y hy
    have hy' : P.toFun y = γ.toFun (lam_EFE n n t) := by
      rw [lam_self_EFE hn, id_eq]
      exact hy
    obtain ⟨x, hx⟩ : (compTransport_EFE n κ D γ.toFun n t).symm y ∈ range F₀.emb := by
      rw [F₀.range_eq]
      exact hbwd t ht n le_rfl y hy'
    refine ⟨x, ?_⟩
    rw [hmap]
    change compTransport_EFE n κ D γ.toFun n t (F₀.emb x) = y
    rw [hx, Diffeomorph.apply_symm_apply]
  have hsm : ContMDiff (IF.prod (𝓡∂ 1)) I ∞ map := by
    rw [show map = fun z => compTransport_EFE n κ D γ.toFun n z.2 (F₀.emb z.1) from funext hmap]
    exact contMDiff_compTransport_EFE hn κ hDj γ.smooth F₀.isSmoothEmbedding.contMDiff n
  refine ⟨⟨map, hsm, ?_, ?_, ?_, hproj, ?_, ?_⟩⟩
  · -- injective
    intro z z' h
    have ht : z.2 = z'.2 :=
      Subtype.ext (γ.injOn z.2.2 z'.2.2 (by rw [← hproj z, ← hproj z', h]))
    have h' : compTransport_EFE n κ D γ.toFun n z.2 (F₀.emb z.1) =
        compTransport_EFE n κ D γ.toFun n z.2 (F₀.emb z'.1) := by
      rw [← hmap, h, hmap, ht]
    exact Prod.ext (F₀.isSmoothEmbedding.isEmbedding.injective
      ((compTransport_EFE n κ D γ.toFun n z.2).injective h')) ht
  · -- injective differential
    intro z
    have hn0 : (∞ : WithTop ℕ∞) ≠ 0 := by simp
    have hmd : MDifferentiableAt (IF.prod (𝓡∂ 1)) I map z := (hsm z).mdifferentiableAt hn0
    rw [injective_iff_map_eq_zero]
    intro v hv
    -- (i) the interval component vanishes
    have hPd : MDifferentiableAt I 𝓘(ℝ, H) P.toFun (map z) :=
      (P.smooth (map z)).mdifferentiableAt hn0
    have hcomp : P.toFun ∘ map = (fun s : Icc (0 : ℝ) 1 => γ.toFun s) ∘ Prod.snd := funext hproj
    have h1 : mfderiv (IF.prod (𝓡∂ 1)) 𝓘(ℝ, H) (P.toFun ∘ map) z v = 0 := by
      rw [mfderiv_comp z hPd hmd, ContinuousLinearMap.comp_apply, hv, map_zero]
    rw [hcomp] at h1
    have hγd : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ, H) (fun s : Icc (0 : ℝ) 1 => γ.toFun s) z.2 :=
      (contMDiff_arc_EFE γ z.2).mdifferentiableAt hn0
    have hsndd : MDifferentiableAt (IF.prod (𝓡∂ 1)) (𝓡∂ 1)
        (Prod.snd : F × Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1) z := mdifferentiableAt_snd
    rw [mfderiv_comp z hγd hsndd, mfderiv_snd] at h1
    change mfderiv (𝓡∂ 1) 𝓘(ℝ, H) (fun s : Icc (0 : ℝ) 1 => γ.toFun s) z.2 v.2 = 0 at h1
    have hv2 : v.2 = 0 := mfderiv_arc_injective_EFE γ z.2 (h1.trans (map_zero _).symm)
    -- (ii) the fibre component vanishes
    let j : F → F × Icc (0 : ℝ) 1 := fun x => (x, z.2)
    have hjD : HasMFDerivAt IF (IF.prod (𝓡∂ 1)) j z.1
        ((ContinuousLinearMap.id ℝ (TangentSpace IF z.1)).prod 0) :=
      (hasMFDerivAt_id z.1).prodMk (hasMFDerivAt_const z.2 z.1)
    have hjd : MDifferentiableAt IF (IF.prod (𝓡∂ 1)) j z.1 := hjD.mdifferentiableAt
    have hj : mfderiv IF (IF.prod (𝓡∂ 1)) j z.1 v.1 = v := by
      rw [hjD.mfderiv]
      exact Prod.ext rfl hv2.symm
    set Φ := compTransport_EFE n κ D γ.toFun n z.2 with hΦ
    have hed : MDifferentiableAt IF I F₀.emb z.1 :=
      (F₀.isSmoothEmbedding.contMDiff z.1).mdifferentiableAt hn0
    have hΦd : MDifferentiableAt I I Φ (F₀.emb z.1) := (Φ.contMDiff _).mdifferentiableAt hn0
    have hfac : map ∘ j = Φ ∘ F₀.emb := funext fun x => hmap (x, z.2)
    have h3 : mfderiv IF I (map ∘ j) z.1 v.1 = 0 := by
      rw [mfderiv_comp z.1 hmd hjd]
      change mfderiv (IF.prod (𝓡∂ 1)) I map z (mfderiv IF (IF.prod (𝓡∂ 1)) j z.1 v.1) = 0
      rw [hj, hv]
    rw [hfac, mfderiv_comp z.1 hΦd hed] at h3
    have hinjΦ := ((Φ.isLocalDiffeomorph (F₀.emb z.1)).mfderivToContinuousLinearEquiv
      hn0).injective
    have h4 : mfderiv IF I F₀.emb z.1 v.1 = 0 := by
      apply hinjΦ
      change mfderiv I I Φ (F₀.emb z.1) (mfderiv IF I F₀.emb z.1 v.1) =
        mfderiv I I Φ (F₀.emb z.1) 0
      rw [map_zero]
      exact h3
    have hv1 : v.1 = 0 :=
      F₀.isSmoothEmbedding.isImmersion.mfderiv_injective hn0 z.1 (h4.trans (map_zero _).symm)
    exact Prod.ext hv1 hv2
  · -- whole range
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.2, z.2.2, (hproj z).symm⟩
    · rintro ⟨t, ht, hty⟩
      obtain ⟨x, hx⟩ := hsurj t ht y hty.symm
      exact ⟨_, hx⟩
  · -- the first end
    intro x
    rw [hmap]
    exact compTransport_at_zero_EFE hn κ hD0 γ.toFun n (F₀.emb x)
  · -- the second end
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact hproj _
    · intro hy
      exact hsurj 1 (right_mem_Icc.mpr zero_le_one) y hy

end MainKernel

end DifferentialGeometry.Topology.Ehresmann

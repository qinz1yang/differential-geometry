import DifferentialGeometry.Geometry.Collapse.SublevelCore.Globalization
import DifferentialGeometry.Topology.Morse.RegularLevel.Band
import DifferentialGeometry.Geometry.Connection.LocalFrameRegularity

/-!
# LC46: a common field supplies a smooth product band

Blueprint LC46 (master207A:22259). Let `f` be smooth with compact band `K = f⁻¹[a,b]`, and let
`Y` be a vector field smooth on an open set `W ⊇ K` with `df(Y) > 0` on `K`. The flow of a
compactly supported extension of `Y / df(Y)` gives product coordinates
`Σ × [a,b] ≃ K`, `(x, s) ↦ Φ (s - c) x`, over any level `Σ = f⁻¹(c)`, `c ∈ [a,b]`, with
`f (Φ (s - c) x) = s`; on the band the flow lines are integral curves of `Y / df(Y)`.
No relation between `Y` and the gradient of `f` is required.

* `exists_band_unit_field`: the cut-off field (equal to `-(Y / df Y)` near `K`).
* `exists_field_band_product`: LC46 for a globally smooth `f` (kernel form).
* `exists_field_band_product_of_contMDiffOn`: LC46 for a function smooth only near its band
  (binding form, through `exists_contMDiff_eqOn_band`): the product is that of a globally smooth
  `f` agreeing with `η` near the band, with the same band and the same level sets.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [I.Boundaryless] in
/-- The compactly supported field `-(Y / df(Y))`, cut off away from a compact set `K` on which
`df(Y) > 0`. Its `f`-rate is `-1` near `K` and lies in `[-1, 0]` everywhere. -/
theorem exists_band_unit_field {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K W : Set M}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) (Y : (x : M) → TangentSpace I x)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I M)) W)
    (hpos : ∀ x ∈ K, 0 < mvfderiv (I := I) f x (Y x)) :
    ∃ v : (x : M) → TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, v x⟩ : TangentBundle I M)) ∧
      HasCompactSupport v ∧ tsupport v ⊆ W ∧
      (∃ U : Set M, IsOpen U ∧ K ⊆ U ∧
        ∀ x ∈ U, v x = -((mvfderiv (I := I) f x (Y x))⁻¹ • Y x)) ∧
      (∀ x, -1 ≤ mvfderiv (I := I) f x (v x) ∧ mvfderiv (I := I) f x (v x) ≤ 0) := by
  classical
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let dY : M → ℝ := fun x => mvfderiv (I := I) f x (Y x)
  have hdY : ∀ x ∈ W, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ dY x := fun x hx =>
    mvfderiv_apply_contMDiffAt_of_section (hf x) (hY.contMDiffAt (hW.mem_nhds hx))
  let D : Set M := W ∩ {x | 0 < dY x}
  have hDo : IsOpen D := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact inter_mem (hW.mem_nhds hx.1)
      ((hdY x hx.1).continuousAt.eventually (lt_mem_nhds hx.2))
  have hKD : K ⊆ D := fun x hx => ⟨hKW hx, hpos x hx⟩
  obtain ⟨U, hUo, hKU, hUD, hUc⟩ := exists_open_between_and_isCompact_closure hK hDo hKD
  obtain ⟨θ, hθ1, hθ0, hθI⟩ := exists_contMDiffMap_one_nhds_of_subset_interior I
    (n := (⊤ : ℕ∞)) hK.isClosed (hKU.trans_eq hUo.interior_eq.symm)
  obtain ⟨O₁, hO₁o, hKO₁, hO₁⟩ := mem_nhdsSet_iff_exists.mp hθ1
  let v : (x : M) → TangentSpace I x := fun x => -((θ x / dY x) • Y x)
  have hvzero : ∀ x, x ∉ U → v x = 0 := by
    intro x hx
    change -((θ x / dY x) • Y x) = 0
    rw [hθ0 x hx, zero_div, zero_smul, neg_zero]
  have hsuppU : tsupport v ⊆ closure U := by
    apply closure_mono
    intro x hx
    by_contra hxU
    exact hx (hvzero x hxU)
  have hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, v x⟩ : TangentBundle I M)) := by
    intro x
    by_cases hx : x ∈ D
    · have hc : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => θ y / dY y) x :=
        (θ.contMDiff x).div₀ (hdY x hx.1) (ne_of_gt hx.2)
      have hs := hc.smul_section (hY.contMDiffAt (hW.mem_nhds hx.1))
      exact hs.neg_section
    · have hxU : x ∉ closure U := fun h => hx (hUD h)
      apply ((0 : Cₛ^∞⟮I; E, TangentSpace I⟯).contMDiff x).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxU] with y hy
      have hyU : y ∉ U := fun h => hy (subset_closure h)
      rw [hvzero y hyU]
      rfl
  refine ⟨v, hv, hUc.of_isClosed_subset (isClosed_tsupport v) hsuppU,
    hsuppU.trans (hUD.trans inter_subset_left), ⟨O₁ ∩ U, hO₁o.inter hUo,
    subset_inter hKO₁ hKU, ?_⟩, ?_⟩
  · intro x hx
    change -((θ x / dY x) • Y x) = -((dY x)⁻¹ • Y x)
    rw [show θ x = 1 from hO₁ hx.1, one_div]
  · intro x
    change -1 ≤ mvfderiv (I := I) f x (-((θ x / dY x) • Y x)) ∧
      mvfderiv (I := I) f x (-((θ x / dY x) • Y x)) ≤ 0
    rw [map_neg, map_smul, smul_eq_mul]
    obtain ⟨h0, h1⟩ := hθI x
    by_cases hx : x ∈ U
    · have hpos' : 0 < dY x := (hUD (subset_closure hx)).2
      change -1 ≤ -(θ x / dY x * dY x) ∧ -(θ x / dY x * dY x) ≤ 0
      rw [div_mul_cancel₀ _ (ne_of_gt hpos')]
      constructor <;> linarith
    · rw [hθ0 x hx, zero_div, zero_mul, neg_zero]
      constructor <;> norm_num

/-- LC46, kernel form: product coordinates on the band of a smooth function from any field
`Y` with `df(Y) > 0` on the band. -/
theorem exists_field_band_product {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b c : ℝ}
    (hc : c ∈ Icc a b) (hB : IsCompact (f ⁻¹' Icc a b)) {W : Set M} (hW : IsOpen W)
    (hBW : f ⁻¹' Icc a b ⊆ W) (Y : (x : M) → TangentSpace I x)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I M)) W)
    (hpos : ∀ x ∈ f ⁻¹' Icc a b, 0 < mvfderiv (I := I) f x (Y x)) :
    ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      Φ 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
      (∀ s t x, Φ (s + t) x = Φ t (Φ s x)) ∧
      (∀ x, f x ∈ Icc a b → ∀ s ∈ Icc a b, f (Φ (s - f x) x) = s) ∧
      (∃ S : Set M, IsCompact S ∧ S ⊆ W ∧ ∀ t x, x ∉ S → Φ t x = x ∧ (Φ t).symm x = x) ∧
      (∀ x t, f (Φ t x) ∈ Icc a b →
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t ((1 : ℝ →L[ℝ] ℝ).smulRight
          ((mvfderiv (I := I) f (Φ t x) (Y (Φ t x)))⁻¹ • Y (Φ t x)))) ∧
      ∃ e : ({x : M // f x = c} × Icc a b) ≃ₜ {x : M // f x ∈ Icc a b},
        (∀ p, (e p : M) = Φ (p.2 - c) p.1) ∧
        (∀ y, ((e.symm y).1 : M) = Φ (c - f y) y) ∧
        (∀ y, ((e.symm y).2 : ℝ) = f y) ∧
        (∀ p, f (e p) = p.2) ∧
        ∀ x : {x : M // f x = c}, (e (x, ⟨c, hc⟩) : M) = x := by
  obtain ⟨v, hv, hvc, hvW, ⟨U, hUo, hBU, hvU⟩, hrate⟩ :=
    exists_band_unit_field hf hB hW hBW Y hY hpos
  have hunit : ∀ x ∈ f ⁻¹' Icc a b, mvfderiv I f x (v x) = -1 := by
    intro x hx
    rw [hvU x (hBU hx), map_neg, map_smul, smul_eq_mul, inv_mul_cancel₀ (ne_of_gt (hpos x hx))]
  let F := Diffeomorph.compactSupportFlow v hv hvc
  let Φ : ℝ → Diffeomorph I I M M ∞ := fun t => F (-t)
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => F p.1 p.2) :=
    Diffeomorph.contMDiff_compactSupportFlow v hv hvc
  have hneg : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (-p.1, p.2)) :=
    (contMDiff_fst.neg).prodMk contMDiff_snd
  have hz (x : M) : F 0 x = x :=
    DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero v hv hvc) x
  have hadd (s t : ℝ) (x : M) : F (s + t) x = F t (F s x) :=
    DFunLike.congr_fun (Diffeomorph.compactSupportFlow_add v hv hvc s t) x
  have hΦadd (s t : ℝ) (x : M) : Φ (s + t) x = Φ t (Φ s x) := by
    change F (-(s + t)) x = F (-t) (F (-s) x)
    rw [neg_add, hadd]
  have hΦz (x : M) : Φ 0 x = x := by
    change F (-0) x = x
    rw [neg_zero, hz]
  have hvalue (x : M) (hx : f x ∈ Icc a b) (s : ℝ) (hs : s ∈ Icc a b) :
      f (Φ (s - f x) x) = s := by
    change f (F (-(s - f x)) x) = s
    rw [neg_sub]
    exact Morse.value_compactSupportFlow_eq_of_mem_Icc hf v hv hvc hunit hrate hx hs
  have hforward (p : {x : M // f x = c} × Icc a b) : f (Φ (p.2 - c) p.1) = p.2 := by
    have h := hvalue p.1 (by rw [p.1.2]; exact hc) p.2 p.2.2
    rwa [p.1.2] at h
  have hback (y : {x : M // f x ∈ Icc a b}) : f (Φ (c - f y) y) = c :=
    hvalue y y.2 c hc
  have hΦc : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) := hF.comp hneg
  let e : ({x : M // f x = c} × Icc a b) ≃ₜ {x : M // f x ∈ Icc a b} :=
    { toFun := fun p => ⟨Φ (p.2 - c) p.1, (hforward p).symm ▸ p.2.2⟩
      invFun := fun y => (⟨Φ (c - f y) y, hback y⟩, ⟨f y, y.2⟩)
      left_inv := by
        intro p
        apply Prod.ext
        · apply Subtype.ext
          change Φ (c - f (Φ (p.2 - c) p.1)) (Φ (p.2 - c) p.1) = p.1
          rw [hforward, ← hΦadd, sub_add_sub_cancel, sub_self, hΦz]
        · apply Subtype.ext
          exact hforward p
      right_inv := by
        intro y
        apply Subtype.ext
        change Φ (f y - c) (Φ (c - f y) y) = y
        rw [← hΦadd, sub_add_sub_cancel, sub_self, hΦz]
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact hΦc.continuous.comp
          (((continuous_subtype_val.comp continuous_snd).sub continuous_const).prodMk
            (continuous_subtype_val.comp continuous_fst))
      continuous_invFun := by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          exact hΦc.continuous.comp
            ((continuous_const.sub (hf.continuous.comp continuous_subtype_val)).prodMk
              continuous_subtype_val)
        · exact (hf.continuous.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨Φ, ?_, hΦc, ?_, hΦadd, hvalue, ⟨tsupport v, hvc, hvW, ?_⟩, ?_, e,
    (fun _ => rfl), (fun _ => rfl), (fun _ => rfl), hforward, ?_⟩
  · change F (-0) = Diffeomorph.refl I M ∞
    rw [neg_zero]
    exact Diffeomorph.compactSupportFlow_zero v hv hvc
  · have h := Diffeomorph.contMDiff_compactSupportFlow_symm v hv hvc
    refine (h.comp hneg).congr ?_
    intro p
    rfl
  · intro t x hx
    exact ⟨(Diffeomorph.compactSupportFlow_eqOn_compl_tsupport v hv hvc (-t)).1 hx,
      (Diffeomorph.compactSupportFlow_eqOn_compl_tsupport v hv hvc (-t)).2 hx⟩
  · intro x t ht
    have hγ := (Diffeomorph.isMIntegralCurve_compactSupportFlow v hv hvc x).comp_mul (-1)
    have hfun : ((fun t => F t x) ∘ (· * (-1))) = fun s => Φ s x := by
      funext s
      change F (s * -1) x = F (-s) x
      rw [mul_neg_one]
    have h := hγ t
    rw [hfun] at h
    have h' : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (((-1 : ℝ) • v) (Φ t x))) := h
    have hvec : ((-1 : ℝ) • v) (Φ t x) =
        (mvfderiv (I := I) f (Φ t x) (Y (Φ t x)))⁻¹ • Y (Φ t x) := by
      rw [Pi.smul_apply, hvU _ (hBU ht), neg_one_smul, neg_neg]
    rw [hvec] at h'
    exact h'
  · intro x
    change Φ (c - c) x = x
    rw [sub_self, hΦz]

omit [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] in
private theorem mvfderiv_eq_of_eqOn_open {f η : M → ℝ} {O : Set M} (hO : IsOpen O)
    (hEq : EqOn f η O) {x : M} (hx : x ∈ O) :
    mvfderiv (I := I) f x = mvfderiv (I := I) η x := by
  have h : f =ᶠ[𝓝 x] η := Filter.eventuallyEq_of_mem (hO.mem_nhds hx) hEq
  ext v
  change NormedSpace.fromTangentSpace (f x) (mfderiv I 𝓘(ℝ, ℝ) f x v) =
    NormedSpace.fromTangentSpace (η x) (mfderiv I 𝓘(ℝ, ℝ) η x v)
  rw [h.mfderiv_eq, hEq hx]
  rfl

/-- LC46, binding form: `η` smooth only on an open `W ⊇ K = η⁻¹[a,b]` (as the LC30 radial
function), `Y` smooth on `W` with `dη(Y) > 0` on `K`. Product coordinates
`η⁻¹(c) × [a,b] ≃ K` whose coordinate curves are integral curves of `Y / dη(Y)`. -/
theorem exists_field_band_product_of_contMDiffOn {η : M → ℝ} (hη : Continuous η) {W : Set M}
    (hW : IsOpen W) (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) {a b c : ℝ} (hab : a < b)
    (hc : c ∈ Icc a b) (hK : IsCompact (η ⁻¹' Icc a b)) (hKW : η ⁻¹' Icc a b ⊆ W)
    (Y : (x : M) → TangentSpace I x)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I M)) W)
    (hpos : ∀ x ∈ η ⁻¹' Icc a b, 0 < mvfderiv (I := I) η x (Y x)) :
    ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      Φ 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
      (∀ s t x, Φ (s + t) x = Φ t (Φ s x)) ∧
      (∀ x, η x ∈ Icc a b → ∀ s ∈ Icc a b, η (Φ (s - η x) x) = s) ∧
      (∃ S : Set M, IsCompact S ∧ S ⊆ W ∧ ∀ t x, x ∉ S → Φ t x = x ∧ (Φ t).symm x = x) ∧
      (∀ x t, η (Φ t x) ∈ Icc a b →
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t ((1 : ℝ →L[ℝ] ℝ).smulRight
          ((mvfderiv (I := I) η (Φ t x) (Y (Φ t x)))⁻¹ • Y (Φ t x)))) ∧
      ∃ e : ({x : M // η x = c} × Icc a b) ≃ₜ {x : M // η x ∈ Icc a b},
        (∀ p, (e p : M) = Φ (p.2 - c) p.1) ∧
        (∀ y, ((e.symm y).1 : M) = Φ (c - η y) y) ∧
        (∀ y, ((e.symm y).2 : ℝ) = η y) ∧
        (∀ p, η (e p) = p.2) ∧
        ∀ x : {x : M // η x = c}, (e (x, ⟨c, hc⟩) : M) = x := by
  obtain ⟨f, hf, ⟨O, hOo, hKO, hOW, hEq⟩, hlo, hhi⟩ :=
    exists_contMDiff_eqOn_band hη hW hηW hab hK hKW
  have hband : ∀ {x : M}, f x ∈ Icc a b ↔ η x ∈ Icc a b :=
    band_mem_Icc_iff hEq hKO hlo hhi
  have hfK : f ⁻¹' Icc a b = η ⁻¹' Icc a b := by
    ext x
    exact hband
  have hdf : ∀ x ∈ η ⁻¹' Icc a b, mvfderiv (I := I) f x = mvfderiv (I := I) η x :=
    fun x hx => mvfderiv_eq_of_eqOn_open hOo hEq (hKO hx)
  have hfval : ∀ x ∈ η ⁻¹' Icc a b, f x = η x := fun x hx => hEq (hKO hx)
  obtain ⟨Φ, hΦ0, hΦc, hΦs, hΦadd, hvalue, hsupp, hvel, e, he, hes1, hes2, heh, hebase⟩ :=
    exists_field_band_product hf hc (hfK ▸ hK) hW (hfK ▸ hKW) Y hY
      (fun x hx => by
        have hx' : x ∈ η ⁻¹' Icc a b := hband.mp hx
        rw [hdf x hx']
        exact hpos x hx')
  have hlev : ∀ x : M, η x = c ↔ f x = c := fun x =>
    (band_eq_iff hEq hKO hlo hhi hc).symm
  have hmem : ∀ x : M, η x ∈ Icc a b ↔ f x ∈ Icc a b := fun x => hband.symm
  let L : {x : M // η x = c} ≃ₜ {x : M // f x = c} := (Homeomorph.refl M).subtype hlev
  let L' : {x : M // η x ∈ Icc a b} ≃ₜ {x : M // f x ∈ Icc a b} :=
    (Homeomorph.refl M).subtype hmem
  let e' : ({x : M // η x = c} × Icc a b) ≃ₜ {x : M // η x ∈ Icc a b} :=
    ((L.prodCongr (Homeomorph.refl _)).trans e).trans L'.symm
  have hηΦ : ∀ x, η x ∈ Icc a b → ∀ s ∈ Icc a b, η (Φ (s - η x) x) = s := by
    intro x hx s hs
    have h := hvalue x (hband.mpr hx) s hs
    rw [hfval x hx] at h
    have hin : f (Φ (s - η x) x) ∈ Icc a b := by rw [h]; exact hs
    rw [← hfval _ (hband.mp hin)]
    exact h
  refine ⟨Φ, hΦ0, hΦc, hΦs, hΦadd, hηΦ, hsupp, ?_, e', ?_, ?_, ?_, ?_, ?_⟩
  · intro x t ht
    have h := hvel x t (hband.mpr ht)
    rwa [hdf _ ht] at h
  · intro p
    exact he (L p.1, p.2)
  · intro y
    have h := hes1 (L' y)
    change ((e.symm (L' y)).1 : M) = Φ (c - f y) y at h
    rw [hfval y y.2] at h
    exact h
  · intro y
    exact (hes2 (L' y)).trans (hfval y y.2)
  · intro p
    change η (e (L p.1, p.2) : M) = p.2
    have h := heh (L p.1, p.2)
    have hin : η (e (L p.1, p.2)) ∈ Icc a b := (e (L p.1, p.2)).2 |> hband.mp
    rw [← hfval _ hin]
    exact h
  · intro x
    exact hebase (L x)

end DifferentialGeometry.Geometry.Collapse

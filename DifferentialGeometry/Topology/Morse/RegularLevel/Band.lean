/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.BoundaryVectorField
import DifferentialGeometry.Topology.Diffeomorph.Flow
import DifferentialGeometry.Analysis.ODE.Flow.IntegralCurveTransport
import DifferentialGeometry.Topology.Manifold.RegularLevel.Collar.LevelAtlas

/-! Products of compact regular bands with ambient flows supported in prescribed neighborhoods. -/

open Set Function
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Morse

section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

theorem value_compactSupportFlow_eq_of_mem_Icc {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I I.tangent ∞ (fun x => (v x : TangentBundle I M)))
    (hvc : HasCompactSupport v) {a b : ℝ}
    (hunit : ∀ x ∈ f ⁻¹' Icc a b, mvfderiv I f x (v x) = -1)
    (hrate : ∀ x, -1 ≤ mvfderiv I f x (v x) ∧
      mvfderiv I f x (v x) ≤ 0)
    {x : M} (hx : f x ∈ Icc a b) {c : ℝ} (hc : c ∈ Icc a b) :
    f (Diffeomorph.compactSupportFlow v hv hvc (f x - c) x) = c := by
  let γ : ℝ → M := fun t => Diffeomorph.compactSupportFlow v hv hvc t x
  have hγ : IsMIntegralCurve γ v := Diffeomorph.isMIntegralCurve_compactSupportFlow v hv hvc x
  have hzero : γ 0 = x :=
    DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero v hv hvc) x
  by_cases ht : 0 ≤ f x - c
  · have hstay : ∀ s ∈ Icc (0 : ℝ) (f x - c), γ s ∈ f ⁻¹' Icc a b := by
      intro s hs
      have hb := f_rate_bounds_of_integralCurve f hf v hrate hγ hs.1
      rw [hzero] at hb
      exact ⟨by linarith [hs.2, hc.1], hb.2.trans hx.2⟩
    have he := f_eq_sub_of_integralCurve_on_strip f hf v hunit hγ ht hstay
    rw [hzero] at he
    simpa only [sub_sub_cancel] using he
  · have ht' : 0 ≤ c - f x := by linarith
    have hstay : ∀ s ∈ Icc (0 : ℝ) (c - f x), γ (-s) ∈ f ⁻¹' Icc a b := by
      intro s hs
      have hb := f_rate_bounds_of_integralCurve_back f hf v hrate hγ hs.1
      rw [hzero] at hb
      exact ⟨hx.1.trans hb.1, by linarith [hs.2, hc.2]⟩
    have he := f_add_of_integralCurve_back f hf v hunit hγ ht' hstay
    rw [hzero, neg_sub] at he
    simpa only [add_sub_cancel] using he

theorem exists_regular_band_product {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hB : IsCompact (f ⁻¹' Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Icc a b, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {O : Set M} (hO : IsOpen O) (hBO : f ⁻¹' Icc a b ⊆ O) :
    ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      Φ 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
      (∀ s t x, Φ (s + t) x = Φ t (Φ s x)) ∧
      (∀ x, f x ∈ Icc a b → ∀ c ∈ Icc a b, f (Φ (f x - c) x) = c) ∧
      (∃ K : Set M, IsCompact K ∧ K ⊆ O ∧
        ∀ t x, x ∉ K → Φ t x = x ∧ (Φ t).symm x = x) ∧
      ∃ e : ({x : M // f x = b} × Icc a b) ≃ₜ {x : M // f x ∈ Icc a b},
        (∀ p, (e p : M) = Φ (b - p.2) p.1) ∧
        (∀ y, ((e.symm y).1 : M) = Φ (f y - b) y) ∧
        (∀ y, ((e.symm y).2 : ℝ) = f y) ∧
        (∀ p, f (e p) = p.2) ∧
        ∀ x : {x : M // f x = b}, (e (x, ⟨b, hab, le_rfl⟩) : M) = x := by
  obtain ⟨X, hX, hXc, hXO, hrateX, ⟨U, _, hBU, _, hunitX⟩, _⟩ :=
    Manifold.exists_contMDiff_boundary_tangent_vector_field (n := 0) (D := univ)
      hB hO hBO hf (fun x hx _ => hregular x hx)
      (by intro x hx; simp only [frontier_univ, inter_empty, mem_empty_iff_false] at hx)
  let v : (x : M) → TangentSpace I x := fun x => -X x
  have hv : ContMDiff I I.tangent ∞ (fun x => (v x : TangentBundle I M)) := hX.neg_section
  have hsupport : tsupport v ⊆ tsupport X := by
    apply closure_mono
    intro x hx hzero
    apply hx
    change -(X x : E) = 0
    change (X x : E) = 0 at hzero
    rw [hzero, neg_zero]
  have hvc : HasCompactSupport v := hXc.of_isClosed_subset (isClosed_tsupport v) hsupport
  have hunit : ∀ x ∈ f ⁻¹' Icc a b, mvfderiv I f x (v x) = -1 := by
    intro x hx
    change mvfderiv I f x (-X x) = -1
    rw [map_neg]
    exact congrArg Neg.neg (hunitX x (hBU hx))
  have hrate : ∀ x, -1 ≤ mvfderiv I f x (v x) ∧
      mvfderiv I f x (v x) ≤ 0 := by
    intro x
    change -1 ≤ mvfderiv I f x (-X x) ∧
      mvfderiv I f x (-X x) ≤ 0
    rw [map_neg]
    have hb := hrateX x
    change 0 ≤ mvfderiv I f x (X x) ∧
      mvfderiv I f x (X x) ≤ 1 at hb
    constructor <;> linarith
  let Φ := Diffeomorph.compactSupportFlow v hv hvc
  have hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) :=
    Diffeomorph.contMDiff_compactSupportFlow v hv hvc
  have hz (x : M) : Φ 0 x = x :=
    DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero v hv hvc) x
  have hadd (s t : ℝ) (x : M) : Φ (s + t) x = Φ t (Φ s x) :=
    DFunLike.congr_fun (Diffeomorph.compactSupportFlow_add v hv hvc s t) x
  have hvalue (x : M) (hx : f x ∈ Icc a b) (c : ℝ) (hc : c ∈ Icc a b) :
      f (Φ (f x - c) x) = c := value_compactSupportFlow_eq_of_mem_Icc hf v hv hvc
        hunit hrate hx hc
  have hforward (p : {x : M // f x = b} × Icc a b) : f (Φ (b - p.2) p.1) = p.2 := by
    simpa only [p.1.2] using hvalue p.1 (by rw [p.1.2]; exact ⟨hab, le_rfl⟩) p.2 p.2.2
  have hback (y : {x : M // f x ∈ Icc a b}) : f (Φ (f y - b) y) = b :=
    hvalue y y.2 b ⟨hab, le_rfl⟩
  let e : ({x : M // f x = b} × Icc a b) ≃ₜ {x : M // f x ∈ Icc a b} :=
    { toFun := fun p => ⟨Φ (b - p.2) p.1, (hforward p).symm ▸ p.2.2⟩
      invFun := fun y => (⟨Φ (f y - b) y, hback y⟩, ⟨f y, y.2⟩)
      left_inv := by
        intro p
        apply Prod.ext
        · apply Subtype.ext
          change Φ (f (Φ (b - p.2) p.1) - b) (Φ (b - p.2) p.1) = p.1
          rw [hforward, ← hadd, sub_add_sub_cancel, sub_self, hz]
        · apply Subtype.ext
          exact hforward p
      right_inv := by
        intro y
        apply Subtype.ext
        change Φ (b - f y) (Φ (f y - b) y) = y
        rw [← hadd, sub_add_sub_cancel, sub_self, hz]
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact hΦ.continuous.comp
          ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).prodMk
            (continuous_subtype_val.comp continuous_fst))
      continuous_invFun := by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          exact hΦ.continuous.comp
            (((hf.continuous.comp continuous_subtype_val).sub continuous_const).prodMk
              continuous_subtype_val)
        · exact (hf.continuous.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨Φ, Diffeomorph.compactSupportFlow_zero v hv hvc, hΦ,
    Diffeomorph.contMDiff_compactSupportFlow_symm v hv hvc, hadd, hvalue,
    ⟨tsupport v, hvc, hsupport.trans hXO, ?_⟩, e, (fun _ => rfl), (fun _ => rfl),
    (fun _ => rfl), hforward, ?_⟩
  · intro t x hx
    exact ⟨(Diffeomorph.compactSupportFlow_eqOn_compl_tsupport v hv hvc t).1 hx,
      (Diffeomorph.compactSupportFlow_eqOn_compl_tsupport v hv hvc t).2 hx⟩
  · intro x
    change Φ (b - b) x = x
    rw [sub_self, hz]

end

open DifferentialGeometry.Topology.Morse (MorseModel)
open DifferentialGeometry.Manifold.RegularLevel

variable {m : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (MorseModel (m + 1)) H}
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

theorem exists_regular_band_diffeomorph {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hB : IsCompact (f ⁻¹' Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Icc a b, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {O : Set M} (hO : IsOpen O) (hBO : f ⁻¹' Icc a b ⊆ O) :
    let hrb : ∀ x, f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 :=
      fun x hx => hregular x (by rw [mem_preimage, hx]; exact ⟨hab, le_rfl⟩)
    let _ := levelChartedSpace I hf hrb
    let J : TopologicalSpace.Opens ℝ := ⟨Ioo a b, isOpen_Ioo⟩
    let U : TopologicalSpace.Opens M := ⟨f ⁻¹' Ioo a b, isOpen_Ioo.preimage hf.continuous⟩
    ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      Φ 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
      (∀ s t x, Φ (s + t) x = Φ t (Φ s x)) ∧
      (∀ x, f x ∈ Icc a b → ∀ c ∈ Icc a b, f (Φ (f x - c) x) = c) ∧
      (∃ K : Set M, IsCompact K ∧ K ⊆ O ∧
        ∀ t x, x ∉ K → Φ t x = x ∧ (Φ t).symm x = x) ∧
      ∃ d : Diffeomorph (𝓘(ℝ, MorseModel m).prod 𝓘(ℝ, ℝ)) I
          ({x : M // f x = b} × J) U ∞,
        (∀ p, (d p : M) = Φ (b - p.2) p.1) ∧
        (∀ y, ((d.symm y).1 : M) = Φ (f y - b) y) ∧
        (∀ y, ((d.symm y).2 : ℝ) = f y) ∧
        ∀ p, f (d p) = p.2 := by
  let hrb : ∀ x, f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 :=
    fun x hx => hregular x (by rw [mem_preimage, hx]; exact ⟨hab, le_rfl⟩)
  let _ := levelChartedSpace I hf hrb
  let J : TopologicalSpace.Opens ℝ := ⟨Ioo a b, isOpen_Ioo⟩
  let U : TopologicalSpace.Opens M := ⟨f ⁻¹' Ioo a b, isOpen_Ioo.preimage hf.continuous⟩
  obtain ⟨Φ, hzero, hΦ, hΦinv, hadd, hvalue, hfix, e, hforward, hback, htime, hheight, _⟩ :=
    exists_regular_band_product hf hab hB hregular hO hBO
  let ei : {x : M // f x = b} × J → {x : M // f x = b} × Icc a b :=
    fun p => (p.1, ⟨p.2, Ioo_subset_Icc_self p.2.2⟩)
  let ui : U → {x : M // f x ∈ Icc a b} := fun y => ⟨y, Ioo_subset_Icc_self y.2⟩
  let e' : ({x : M // f x = b} × J) ≃ₜ U :=
    { toFun := fun p => ⟨e (ei p), by
        change f (e (ei p)) ∈ Ioo a b
        rw [hheight]
        exact p.2.2⟩
      invFun := fun y => ((e.symm (ui y)).1, ⟨(e.symm (ui y)).2, by
        change ((e.symm (ui y)).2 : ℝ) ∈ Ioo a b
        rw [htime]
        exact y.2⟩)
      left_inv := by
        intro p
        have heq : ui ⟨e (ei p), by
            change f (e (ei p)) ∈ Ioo a b
            rw [hheight]
            exact p.2.2⟩ = e (ei p) := rfl
        apply Prod.ext
        · change (e.symm (ui _)).1 = p.1
          rw [heq, e.symm_apply_apply]
        · apply Subtype.ext
          change ((e.symm (ui _)).2 : ℝ) = p.2
          rw [heq, e.symm_apply_apply]
      right_inv := by
        intro y
        apply Subtype.ext
        have heq : ei ((e.symm (ui y)).1, ⟨(e.symm (ui y)).2, by
            rw [htime]; exact y.2⟩) = e.symm (ui y) := rfl
        change (e (ei _) : M) = y
        rw [heq, e.apply_symm_apply]
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp (e.continuous.comp
          (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)))
      continuous_invFun := by
        apply Continuous.prodMk
        · exact (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)).fst
        · exact (continuous_subtype_val.comp
            (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)).snd).subtype_mk _ }
  have hef (p : {x : M // f x = b} × J) : (e' p : M) = Φ (b - p.2) p.1 := hforward (ei p)
  have heb (y : U) : ((e'.symm y).1 : M) = Φ (f y - b) y := hback (ui y)
  have het (y : U) : ((e'.symm y).2 : ℝ) = f y := htime (ui y)
  have hinc : ContMDiff 𝓘(ℝ, MorseModel m) I ∞
      (Subtype.val : {x : M // f x = b} → M) := contMDiff_level_inclusion I hf hrb
  have he : ContMDiff (𝓘(ℝ, MorseModel m).prod 𝓘(ℝ, ℝ)) I ∞ e' := by
    apply (ContMDiff.subtypeVal_comp_iff U e').mp
    exact (hΦ.comp
      ((contMDiff_const.sub (contMDiff_subtype_val.comp contMDiff_snd)).prodMk
        (hinc.comp contMDiff_fst))).congr hef
  have hproj : ContMDiff I I ∞ (fun y : U => Φ (f y - b) y) :=
    hΦ.comp (((hf.comp contMDiff_subtype_val).sub contMDiff_const).prodMk contMDiff_subtype_val)
  have hprojlevel : ∀ y : U, f (Φ (f y - b) y) = b := by
    intro y
    rw [← heb]
    exact (e'.symm y).1.2
  have hinv₁ : ContMDiff I 𝓘(ℝ, MorseModel m) ∞ (fun y : U => (e'.symm y).1) := by
    apply (contMDiff_level_factor I hf hrb hproj hprojlevel).congr
    intro y
    apply Subtype.ext
    exact heb y
  have hinv₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : U => (e'.symm y).2) := by
    apply (ContMDiff.subtypeVal_comp_iff J _).mp
    exact (hf.comp contMDiff_subtype_val).congr het
  let d : Diffeomorph (𝓘(ℝ, MorseModel m).prod 𝓘(ℝ, ℝ)) I
      ({x : M // f x = b} × J) U ∞ :=
    { toEquiv := e'.toEquiv
      contMDiff_toFun := he
      contMDiff_invFun := hinv₁.prodMk hinv₂ }
  exact ⟨Φ, hzero, hΦ, hΦinv, hadd, hvalue, hfix, d, hef, heb, het,
    fun p => hheight (ei p)⟩

end DifferentialGeometry.Morse

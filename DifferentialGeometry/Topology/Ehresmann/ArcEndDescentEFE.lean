import DifferentialGeometry.Topology.Ehresmann.ArcEndDefiningFunctionZSP35

/-!
# The end of a base arc: the defining function DESCENDS to the base (EDP05 slim half), group G8a

Lane S-EDP-FDC3. Blueprint `master207B.tex`, EDP05 (B:7040–7090): "For a slim face use a local
coordinate defining its chosen endpoint in `D₃`, composed with `π_{2,3}` on the base." ZSP05's
tube kernels (`exists_end_defining_function_ZSP35`, `exists_arc_end_tube_ZSP35`, lane S-ZSP04 G20)
construct the defining function as `h = σ (a₀ − κ_i ∘ f)` but do not export that form. The
statements below are those kernels with ONE extra conjunct, `∃ a : H → ℝ, ContDiff ℝ ∞ a ∧
∀ x, h x = a (f x)` (the defining function is a smooth function of the base point); the proofs
are the kernels' proofs with the witness `a s = σ (a₀ − κ_i s)` supplied.

* `exists_end_defining_function_descent_EFE` (one chart end of an arc),
* `exists_arc_end_tube_descent_EFE` (an end of an arc of a smooth compact one-dimensional domain,
  with the extra open `G ∋ y`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Topology

section DefiningFunction

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}

/-- **The regular defining function over an arc end, as a smooth function of the base point**
(the ZSP05 kernel `exists_end_defining_function_ZSP35` with the extra conjunct `h = a ∘ f`). -/
theorem exists_end_defining_function_descent_EFE
    (P : ProperSmoothSurfaceSubmersion_EFE I M ι Bs) {γ : ℝ → H}
    (hγc : ContinuousOn γ (Icc 0 1)) (hinj : InjOn γ (Icc 0 1))
    {T : Set H} (hT : γ '' Icc 0 1 ⊆ T) (hTB : T ⊆ Bs)
    (hiso : ∃ N : Set H, IsOpen N ∧ γ 0 ∈ N ∧ T ∩ N ⊆ γ '' Icc 0 1)
    {E' : Set H} (hE' : IsClosed E') (hyE : γ 0 ∉ E') :
    ∃ (U : Set M) (h : M → ℝ) (a : H → ℝ), IsOpen U ∧ P.toFun ⁻¹' {γ 0} ⊆ U ∧
      U ⊆ P.toFun ⁻¹' Bs ∧
      Disjoint U (P.toFun ⁻¹' E') ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ h U ∧
      (∀ x ∈ U, Surjective (mfderiv I 𝓘(ℝ, ℝ) h x)) ∧
      {x | x ∈ U ∧ h x = 0} = P.toFun ⁻¹' {γ 0} ∧
      U ∩ P.toFun ⁻¹' T = {x | x ∈ U ∧ h x ≤ 0} ∧
      ContDiff ℝ ∞ a ∧ ∀ x, h x = a (P.toFun x) := by
  obtain ⟨i, σ, ε, V, hσ, hε, hIcc, hV, hVB, hVR, hVE, hyV, hside⟩ :=
    exists_arc_end_chart_ZSP35 P.atlas P.region P.isOpen_region P.region_cover P.region_piece
      hγc hinj hT hTB hiso hE' hyE
  set κ := P.atlas.coord i with hκ
  set a₀ : ℝ := κ (γ 0) with ha₀
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hfc := P.smooth.continuous
  have hUo : IsOpen (P.toFun ⁻¹' V ∩ P.toFun ⁻¹' Bs) :=
    (hV.preimage hfc).inter P.isOpen_source
  have hUB : ∀ x, x ∈ P.toFun ⁻¹' V ∩ P.toFun ⁻¹' Bs →
      ∃ b ∈ Ioo (a₀ - ε) (a₀ + ε), P.toFun x = P.atlas.param i b := by
    intro x hx
    have : P.toFun x ∈ V ∩ Bs := hx
    rw [hVB] at this
    obtain ⟨b, hb, hxb⟩ := this
    exact ⟨b, hb, hxb.symm⟩
  have hκparam : ∀ b ∈ Ioo (a₀ - ε) (a₀ + ε), κ (P.atlas.param i b) = b := fun b hb =>
    P.atlas.coord_param i b (Ioo_subset_Icc_self.trans hIcc hb)
  have hy0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hyB : γ 0 ∈ Bs := hTB (hT ⟨0, hy0, rfl⟩)
  have hpa : P.atlas.param i a₀ = γ 0 := by
    have : γ 0 ∈ V ∩ Bs := ⟨hyV, hyB⟩
    rw [hVB] at this
    obtain ⟨b, hb, hbγ⟩ := this
    have hb' : κ (γ 0) = b := by rw [← hbγ]; exact hκparam b hb
    have : a₀ = b := hb'
    rw [this, hbγ]
  have hga : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => κ (P.toFun x)) :=
    κ.contDiff.comp_contMDiff P.smooth
  have hφ : ContDiff ℝ ∞ (fun s : ℝ => σ * (a₀ - s)) :=
    contDiff_const.mul (contDiff_const.sub contDiff_id)
  have hacd : ContDiff ℝ ∞ (fun s : H => σ * (a₀ - κ s)) :=
    contDiff_const.mul (contDiff_const.sub κ.contDiff)
  refine ⟨P.toFun ⁻¹' V ∩ P.toFun ⁻¹' Bs, fun x => σ * (a₀ - κ (P.toFun x)),
    fun s : H => σ * (a₀ - κ s), hUo, ?_,
    inter_subset_right, ?_, (hφ.comp_contMDiff hga).contMDiffOn, ?_, ?_, ?_, hacd,
    fun x => rfl⟩
  · intro x hx
    have hx' : P.toFun x = γ 0 := hx
    exact ⟨show P.toFun x ∈ V by rw [hx']; exact hyV, show P.toFun x ∈ Bs by rw [hx']; exact hyB⟩
  · refine disjoint_left.mpr fun x hx hxE => ?_
    have : P.toFun x ∈ V ∩ E' := ⟨hx.1, hxE⟩
    rw [hVE] at this
    exact this
  · intro x hx
    have hxR : P.toFun x ∈ P.region i ∩ Bs := ⟨hVR ⟨hx.1, hx.2⟩, hx.2⟩
    have hsub := P.submersion i x hxR
    have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => κ (P.toFun y)) x :=
      (hga x).mdifferentiableAt (by decide)
    have hdφ : deriv (fun s : ℝ => σ * (a₀ - s)) (κ (P.toFun x)) ≠ 0 := by
      have : deriv (fun s : ℝ => σ * (a₀ - s)) (κ (P.toFun x)) = -σ := by simp
      rw [this]
      exact neg_ne_zero.mpr hσ0
    exact surjective_mfderiv_scalar_comp_ZSP35 (φ := fun s : ℝ => σ * (a₀ - s)) hmd hsub
      (hφ.differentiable (by decide) _) hdφ
  · ext x
    constructor
    · rintro ⟨hx, hx0⟩
      obtain ⟨b, hb, hxb⟩ := hUB x hx
      have hκx : κ (P.toFun x) = b := by rw [hxb]; exact hκparam b hb
      have hba : b = a₀ := by
        have : σ * (a₀ - κ (P.toFun x)) = 0 := hx0
        have h2 := (mul_eq_zero.mp this).resolve_left hσ0
        linarith
      change P.toFun x = γ 0
      rw [hxb, hba, hpa]
    · intro hx
      have hx' : P.toFun x = γ 0 := hx
      refine ⟨⟨show P.toFun x ∈ V by rw [hx']; exact hyV,
        show P.toFun x ∈ Bs by rw [hx']; exact hyB⟩, ?_⟩
      change σ * (a₀ - κ (P.toFun x)) = 0
      rw [hx']
      simp [ha₀]
  · ext x
    constructor
    · rintro ⟨hx, hxT⟩
      refine ⟨hx, ?_⟩
      obtain ⟨b, hb, hxb⟩ := hUB x hx
      have hκx : κ (P.toFun x) = b := by rw [hxb]; exact hκparam b hb
      have h1 : 0 ≤ σ * (b - a₀) := (hside b hb).mp (hxb ▸ hxT)
      change σ * (a₀ - κ (P.toFun x)) ≤ 0
      rw [hκx]
      nlinarith
    · rintro ⟨hx, hxh⟩
      refine ⟨hx, ?_⟩
      obtain ⟨b, hb, hxb⟩ := hUB x hx
      have hκx : κ (P.toFun x) = b := by rw [hxb]; exact hκparam b hb
      have hxh' : σ * (a₀ - b) ≤ 0 := by
        have : σ * (a₀ - κ (P.toFun x)) ≤ 0 := hxh
        rwa [hκx] at this
      change P.toFun x ∈ T
      rw [hxb]
      exact (hside b hb).mpr (by nlinarith)

end DefiningFunction

section ArcEnds

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}

/-- **The tube over an arc end of a smooth compact one-dimensional domain, with the defining
function a smooth function of the base point** (the ZSP05 kernel `exists_arc_end_tube_ZSP35` with
the extra conjunct `h = a ∘ f`). -/
theorem exists_arc_end_tube_descent_EFE
    (P : ProperSmoothSurfaceSubmersion_EFE I M ι Bs) (D : SmoothCompactOneDomain_BCF Bs)
    {y : H} (hy : ∃ k : Fin D.m, y = D.arc k 0 ∨ y = D.arc k 1) {G : Set H} (hG : IsOpen G)
    (hyG : y ∈ G) :
    ∃ (U : Set M) (h : M → ℝ) (a : H → ℝ), IsOpen U ∧ P.toFun ⁻¹' {y} ⊆ U ∧
      U ⊆ P.toFun ⁻¹' (G ∩ Bs) ∧
      Disjoint U (P.toFun ⁻¹' ((⋃ k : Fin D.m, ({D.arc k 0, D.arc k 1} : Set H)) \ {y})) ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ h U ∧ (∀ x ∈ U, Surjective (mfderiv I 𝓘(ℝ, ℝ) h x)) ∧
      {x | x ∈ U ∧ h x = 0} = P.toFun ⁻¹' {y} ∧
      U ∩ P.toFun ⁻¹' D.carrier = {x | x ∈ U ∧ h x ≤ 0} ∧
      ContDiff ℝ ∞ a ∧ ∀ x, h x = a (P.toFun x) := by
  obtain ⟨k, hk⟩ := hy
  have hcarr : ∀ k : Fin D.m, D.arc k '' Icc 0 1 ⊆ D.carrier := fun k z hz => by
    rw [D.carrier_eq]
    exact Or.inl (mem_iUnion.mpr ⟨k, hz⟩)
  have hE : IsClosed (((⋃ k : Fin D.m, ({D.arc k 0, D.arc k 1} : Set H)) \ {y}) ∪ Gᶜ) :=
    (isClosed_otherEnds_ZSP35 D y).union hG.isClosed_compl
  have hyE : y ∉ ((⋃ k : Fin D.m, ({D.arc k 0, D.arc k 1} : Set H)) \ {y}) ∪ Gᶜ :=
    fun h => h.elim (fun h => h.2 rfl) (fun h => h hyG)
  have hmain : ∃ (U : Set M) (h : M → ℝ) (a : H → ℝ), IsOpen U ∧ P.toFun ⁻¹' {y} ⊆ U ∧
      U ⊆ P.toFun ⁻¹' Bs ∧
      Disjoint U (P.toFun ⁻¹' (((⋃ k : Fin D.m, ({D.arc k 0, D.arc k 1} : Set H)) \ {y}) ∪ Gᶜ)) ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ h U ∧ (∀ x ∈ U, Surjective (mfderiv I 𝓘(ℝ, ℝ) h x)) ∧
      {x | x ∈ U ∧ h x = 0} = P.toFun ⁻¹' {y} ∧
      U ∩ P.toFun ⁻¹' D.carrier = {x | x ∈ U ∧ h x ≤ 0} ∧
      ContDiff ℝ ∞ a ∧ ∀ x, h x = a (P.toFun x) := by
    rcases hk with hk | hk
    · subst hk
      have hy0 : D.arc k 0 ∈ D.arc k '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      exact exists_end_defining_function_descent_EFE P (D.arc_smooth k).continuousOn (D.arc_injOn k)
        (hcarr k) D.subset_base (arc_isolated_ZSP35 D k hy0) hE hyE
    · subst hk
      have hy1 : D.arc k 1 ∈ D.arc k '' Icc 0 1 := ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
      have hrev : (fun s : ℝ => D.arc k (1 - s)) '' Icc 0 1 = D.arc k '' Icc 0 1 := by
        ext z
        constructor
        · rintro ⟨s, hs, rfl⟩
          exact ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp⟩
      have hiso : ∃ N : Set H, IsOpen N ∧ (fun s : ℝ => D.arc k (1 - s)) 0 ∈ N ∧
          D.carrier ∩ N ⊆ (fun s : ℝ => D.arc k (1 - s)) '' Icc 0 1 := by
        obtain ⟨N, hN, hyN, hNs⟩ := arc_isolated_ZSP35 D k hy1
        exact ⟨N, hN, by simpa using hyN, by rw [hrev]; exact hNs⟩
      have hcont : ContinuousOn (fun s : ℝ => D.arc k (1 - s)) (Icc 0 1) :=
        (D.arc_smooth k).continuousOn.comp (by fun_prop) (fun s hs =>
          ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      have hinj : InjOn (fun s : ℝ => D.arc k (1 - s)) (Icc 0 1) := by
        intro s hs t ht hst
        have := D.arc_injOn k ⟨by linarith [hs.2], by linarith [hs.1]⟩
          ⟨by linarith [ht.2], by linarith [ht.1]⟩ hst
        linarith
      have := exists_end_defining_function_descent_EFE P hcont hinj
        (T := D.carrier) (by rw [hrev]; exact hcarr k) D.subset_base hiso
        (E' := ((⋃ k : Fin D.m, ({D.arc k 0, D.arc k 1} : Set H)) \ {D.arc k 1}) ∪ Gᶜ) hE
        (by simpa using hyE)
      simpa using this
  obtain ⟨U, h, a, hUo, hfU, hUB, hUE, hh, hsurj, hlev, hside, ha, hha⟩ := hmain
  refine ⟨U, h, a, hUo, hfU, ?_, ?_, hh, hsurj, hlev, hside, ha, hha⟩
  · intro x hx
    have hxB := hUB hx
    have hxG : P.toFun x ∈ G := by
      by_contra hxG
      exact disjoint_left.mp hUE hx (Or.inr hxG)
    exact ⟨hxG, hxB⟩
  · refine disjoint_left.mpr fun x hx hxe => ?_
    exact disjoint_left.mp hUE hx (Or.inl hxe)
end ArcEnds

end DifferentialGeometry.Topology.Ehresmann

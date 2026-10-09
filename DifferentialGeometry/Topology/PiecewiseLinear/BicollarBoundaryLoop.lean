/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.Nullhomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarBands
import DifferentialGeometry.Topology.PiecewiseLinear.JordanDiskPasting
import DifferentialGeometry.Topology.PiecewiseLinear.PLLevelCircles

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_continuousOn_mapsTo_closure_inside_of_forall_isNullHomotopic {Y : Type*}
    [TopologicalSpace Y] {B X : Set Y} (hBX : B ⊆ X)
    (hinj : ∀ γ : freeLoop B, IsNullHomotopic ((⟨Set.inclusion hBX, continuous_inclusion hBX⟩ :
      C(B, X)).comp γ) → IsNullHomotopic γ)
    {J : Set Schoenflies.Plane} (hJ : IsPLSphere 1 J) {G : Schoenflies.Plane → Y}
    (hG : ContinuousOn G (closure (Schoenflies.inside J)))
    (hGX : MapsTo G (closure (Schoenflies.inside J)) X) (hGB : MapsTo G J B) :
    ∃ G' : Schoenflies.Plane → Y, ContinuousOn G' (closure (Schoenflies.inside J)) ∧
      MapsTo G' (closure (Schoenflies.inside J)) B ∧ EqOn G' G J := by
  have hJJ : Schoenflies.IsJordanCurve J := isJordanCurve_of_isPLSphere_one hJ
  have hJD : J ⊆ closure (Schoenflies.inside J) := by
    intro z hz
    rw [← (Schoenflies.jordan_curve_theorem hJJ).frontier_inside] at hz
    exact frontier_subset_closure hz
  obtain ⟨a⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hJ
  have hGJ : ContinuousOn G J := hG.mono hJD
  let bB : C(J, B) := ⟨fun z => ⟨G z, hGB z.2⟩, hGJ.domRestrict.subtype_mk _⟩
  let bX : C(J, X) := ⟨fun z => ⟨G z, hGX (hJD z.2)⟩, hGJ.domRestrict.subtype_mk _⟩
  have hbX : bX.Nullhomotopic :=
    (isPLBall_closure_inside_of_isPLSphere_one hJ).nullhomotopic_of_continuousOn hJD hG hGX bX
      fun _ => rfl
  have heqX : (⟨Set.inclusion hBX, continuous_inclusion hBX⟩ : C(B, X)).comp
      (bB.comp (a : C(loopCircle, J))) = bX.comp (a : C(loopCircle, J)) :=
    ContinuousMap.ext fun _ => Subtype.ext rfl
  have hγX : IsNullHomotopic ((⟨Set.inclusion hBX, continuous_inclusion hBX⟩ : C(B, X)).comp
      (bB.comp (a : C(loopCircle, J)))) := by
    rw [heqX]
    exact hbX.comp_left (a : C(loopCircle, J))
  have hγ : (bB.comp (a : C(loopCircle, J))).Nullhomotopic := hinj _ hγX
  have heqB : (bB.comp (a : C(loopCircle, J))).comp (a.symm : C(J, loopCircle)) = bB :=
    ContinuousMap.ext fun z => Subtype.ext (by
      change G (a (a.symm z)) = G z
      rw [a.apply_symm_apply])
  have hbB : bB.Nullhomotopic := by
    rw [← heqB]
    exact hγ.comp_left (a.symm : C(J, loopCircle))
  obtain ⟨G', hG'c, hG'B, hG'eq⟩ :=
    exists_continuousOn_mapsTo_closure_inside_of_nullhomotopic hJJ bB hbB
  exact ⟨G', hG'c, hG'B, fun z hz => hG'eq ⟨z, hz⟩⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.exists_mem_connectedComponentIn_of_isPreconnected
    {L : Geometry.SimplicialComplex ℝ E} {ρ : E × ℝ → E} {W : Set E}
    (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    {X : Type*} [TopologicalSpace X] {f : X → E} {c : Set X} (hf : ContinuousOn f c)
    (hc : IsPreconnected c) (hfc : MapsTo f c (ρ '' (L.space ×ˢ {t}))) {p : X} (hp : p ∈ c) :
    ∀ q ∈ c, ∃ y ∈ connectedComponentIn L.space
      (Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) (f p)).1, f q = ρ (y, t) := by
  set ψ := Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) with hψdef
  have hψq : ∀ q ∈ c, (ψ (f q)).1 ∈ L.space ∧ f q = ρ ((ψ (f q)).1, t) ∧ f q ∈ W := by
    intro q hq
    obtain ⟨z, hz, hzq⟩ := hfc hq
    have hzt : z.2 = t := hz.2
    have hzI : z ∈ L.space ×ˢ Icc (-1 : ℝ) 1 := ⟨hz.1, hzt ▸ ht⟩
    have h : ψ (f q) = z := by
      rw [← hzq, hψdef]
      exact hρ.bijOn.invOn_invFunOn.1 hzI
    rw [h, ← hzq, ← hzt]
    exact ⟨hz.1, rfl, hρ.bijOn.mapsTo hzI⟩
  have hπ : ContinuousOn (fun q => (ψ (f q)).1) c :=
    continuous_fst.comp_continuousOn (hρ.isPiecewiseAffineOn_invFunOn.continuousOn.comp hf
      fun q hq => (hψq q hq).2.2)
  have himg : (fun q => (ψ (f q)).1) '' c ⊆ connectedComponentIn L.space (ψ (f p)).1 :=
    (hc.image _ hπ).subset_connectedComponentIn ⟨p, hp, rfl⟩ (by
      rintro _ ⟨q, hq, rfl⟩
      exact (hψq q hq).1)
  intro q hq
  exact ⟨(ψ (f q)).1, himg ⟨q, hq, rfl⟩, (hψq q hq).2.1⟩

theorem IsPLHomeomorphOn.exists_finite_isPLSphere_levels_of_bicollar
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    {ρ : E × ℝ → E} {W : Set E} (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W)
    (hρzero : ∀ y ∈ L.space, ρ (y, 0) = y) (hWK : W ⊆ K.space) {P : Set Schoenflies.Plane}
    (hP : IsPLBall 2 P) {f : Schoenflies.Plane → E} (hf : IsPiecewiseAffineOn f P)
    (hfK : MapsTo f P K.space) (hfL : MapsTo f (frontier P) L.space) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ t ∈ ({-s, s} : Set ℝ),
      ∃ C : Set (Set Schoenflies.Plane), C.Finite ∧ (∀ c ∈ C, IsPLSphere 1 c) ∧
        C.PairwiseDisjoint id ∧ (∀ c ∈ C, c ⊆ interior P) ∧
        P ∩ f ⁻¹' (ρ '' (L.space ×ˢ {t})) = ⋃₀ C := by
  set ψ := Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) with hψdef
  have hWpoly : IsPolyhedron W := by
    rw [← hρ.image_eq]
    exact ((isPolyhedron_space L).prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      hρ.isPiecewiseAffineOn hρ.bijOn.injOn
  have hQ : IsPolyhedron (P ∩ f ⁻¹' W) :=
    hf.isPolyhedron_inter_preimage_of_isPolyhedron hP.isPolyhedron hWpoly
  have hφ : IsPiecewiseAffineOn (fun q => (ψ (f q)).2) (P ∩ f ⁻¹' W) :=
    (hρ.isPiecewiseAffineOn_invFunOn.comp hf).affine_comp (LinearMap.snd ℝ E ℝ).toAffineMap
  obtain ⟨S₀, hS₀, hlev⟩ := hφ.exists_finite_levels_isPLSphere_decomposition hQ
  obtain ⟨G₁, hG₁, hG₁K⟩ := hρ.exists_isOpen_inter_eq_image_prod_Ioo hK hL hWK le_rfl
  have hlevel : ∀ t ∈ Icc (-1 : ℝ) 1,
      P ∩ f ⁻¹' (ρ '' (L.space ×ˢ {t})) = P ∩ f ⁻¹' W ∩ (fun q => (ψ (f q)).2) ⁻¹' {t} := by
    intro t ht
    ext q
    constructor
    · rintro ⟨hqP, z, hz, hzq⟩
      have hzt : z.2 = t := hz.2
      have hzI : z ∈ L.space ×ˢ Icc (-1 : ℝ) 1 := ⟨hz.1, hzt ▸ ht⟩
      have h : ψ (f q) = z := by
        rw [← hzq, hψdef]
        exact hρ.bijOn.invOn_invFunOn.1 hzI
      refine ⟨⟨hqP, ?_⟩, ?_⟩
      · change f q ∈ W
        rw [← hzq]
        exact hρ.bijOn.mapsTo hzI
      · change (ψ (f q)).2 = t
        rw [h, hzt]
    · rintro ⟨⟨hqP, hqW⟩, hqt⟩
      exact ⟨hqP, ψ (f q), ⟨(hρ.bijOn.surjOn.mapsTo_invFunOn hqW).1, hqt⟩,
        hρ.bijOn.invOn_invFunOn.2 hqW⟩
  have hnotfr : ∀ t ∈ Icc (-1 : ℝ) 1, t ≠ 0 →
      ∀ q ∈ P ∩ f ⁻¹' (ρ '' (L.space ×ˢ {t})), q ∈ interior P := by
    rintro t ht ht0 q ⟨hqP, z, hz, hzq⟩
    have hzt : z.2 = t := hz.2
    by_contra hqi
    have hqfr : q ∈ frontier P := ⟨subset_closure hqP, hqi⟩
    have hfq := hfL hqfr
    have h := hρ.bijOn.injOn ⟨hz.1, hzt ▸ ht⟩ (⟨hfq, by norm_num, by norm_num⟩ :
      (f q, (0 : ℝ)) ∈ L.space ×ˢ Icc (-1 : ℝ) 1) (hzq.trans (hρzero _ hfq).symm)
    exact ht0 (hzt.symm.trans (congrArg Prod.snd h))
  have hintQ : ∀ t ∈ Ioo (-1 : ℝ) 1, t ≠ 0 →
      P ∩ f ⁻¹' W ∩ (fun q => (ψ (f q)).2) ⁻¹' {t} ⊆ interior (P ∩ f ⁻¹' W) := by
    intro t ht ht0 q hq
    have htI : t ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self ht
    rw [← hlevel t htI] at hq
    have hqi := hnotfr t htI ht0 q hq
    obtain ⟨-, z, hz, hzq⟩ := hq
    have hzt : z.2 = t := hz.2
    have hO : IsOpen (interior P ∩ f ⁻¹' G₁) :=
      (hf.continuousOn.mono interior_subset).isOpen_inter_preimage isOpen_interior hG₁
    refine interior_maximal ?_ hO ⟨hqi, ?_⟩
    · rintro q' ⟨hq'P, hq'G⟩
      refine ⟨interior_subset hq'P, ?_⟩
      have hmem : f q' ∈ G₁ ∩ K.space := ⟨hq'G, hfK (interior_subset hq'P)⟩
      rw [hG₁K] at hmem
      obtain ⟨w, hw, hwq⟩ := hmem
      change f q' ∈ W
      rw [← hwq]
      exact hρ.bijOn.mapsTo ⟨hw.1, hw.2.1.le, hw.2.2.le⟩
    · have hmem : f q ∈ ρ '' (L.space ×ˢ Ioo (-1 : ℝ) 1) := ⟨z, ⟨hz.1, hzt ▸ ht⟩, hzq⟩
      rw [← hG₁K] at hmem
      exact hmem.1
  obtain ⟨s, hs, hsS⟩ := (Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finite
    (hS₀.union (hS₀.image Neg.neg))
  refine ⟨s, hs.1, hs.2, fun t ht => ?_⟩
  have hts : t ∈ Ioo (-1 : ℝ) 1 ∧ t ≠ 0 ∧ t ∉ S₀ := by
    rcases ht with h | h
    · rw [h]
      refine ⟨⟨by linarith [hs.2], by linarith [hs.1]⟩, fun h0 => by linarith [hs.1], fun h' => ?_⟩
      exact hsS (Or.inr ⟨-s, h', neg_neg s⟩)
    · rw [show t = s from h]
      exact ⟨⟨by linarith [hs.1], hs.2⟩, hs.1.ne', fun h' => hsS (Or.inl h')⟩
  obtain ⟨htI, ht0, htS⟩ := hts
  obtain ⟨C, hCfin, hC, hCdisj, hCeq⟩ := hlev t htS (hintQ t htI ht0)
  have hlt := hlevel t (Ioo_subset_Icc_self htI)
  refine ⟨C, hCfin, hC, hCdisj, fun c hc q hq => ?_, hlt.trans hCeq⟩
  have hq' : q ∈ P ∩ f ⁻¹' (ρ '' (L.space ×ˢ {t})) := by
    rw [hlt, hCeq]
    exact ⟨c, hc, hq⟩
  exact hnotfr t (Ioo_subset_Icc_self htI) ht0 q hq'

open Classical in
theorem IsPLHomeomorphOn.exists_continuousOn_push_to_ends_mapsTo
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    {ρ : E × ℝ → E} {W : Set E} (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W)
    (hρzero : ∀ y ∈ L.space, ρ (y, 0) = y)
    (hW : W ⊆ K.space \ (boundaryComplex 3 K).space) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∃ Φ : E → E, ContinuousOn Φ K.space ∧ MapsTo Φ W W ∧
      MapsTo Φ (K.space \ ρ '' (L.space ×ˢ Icc (-s) s)) (closure (K.space \ W)) ∧
      (∀ y ∈ L.space, Φ y = y) ∧
      ∀ y ∈ L.space, ∀ e ∈ ({-1, 1} : Set ℝ), Φ (ρ (y, e * s)) = ρ (y, e) := by
  obtain ⟨Φ, hΦc, -, hΦout, hΦρ⟩ := hρ.exists_continuousOn_push_to_ends hK hL hW hs0 hs1
  obtain ⟨-, -, -, -, -, htrace⟩ := hρ.inter_closure_sdiff_eq_image_prod_pair hK hL hW
  refine ⟨Φ, hΦc, ?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [← hρ.image_eq] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    rw [hΦρ z hz]
    exact hρ.bijOn.mapsTo ⟨hz.1, le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · rintro w ⟨hwK, hws⟩
    by_cases hwW : w ∈ W
    · rw [← hρ.image_eq] at hwW
      obtain ⟨z, hz, rfl⟩ := hwW
      rw [hΦρ z hz]
      have hzs : z.2 < -s ∨ s < z.2 := by
        by_contra h
        push Not at h
        exact hws ⟨z, ⟨hz.1, h.1, h.2⟩, rfl⟩
      have hend : max (-1) (min 1 (z.2 / s)) ∈ ({-1, 1} : Set ℝ) := by
        rcases hzs with h | h
        · refine Or.inl ?_
          have h' : z.2 / s < -1 := by
            rw [div_lt_iff₀ hs0]
            linarith
          rw [min_eq_right (show z.2 / s ≤ 1 by linarith),
            max_eq_left (show z.2 / s ≤ -1 by linarith)]
        · refine Or.inr ?_
          have h' : 1 < z.2 / s := by
            rw [lt_div_iff₀ hs0]
            linarith
          change max (-1) (min 1 (z.2 / s)) = 1
          rw [min_eq_left h'.le, max_eq_right (show (-1 : ℝ) ≤ 1 by norm_num)]
      have hmem : ρ (z.1, max (-1) (min 1 (z.2 / s))) ∈ ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ)) :=
        ⟨(z.1, max (-1) (min 1 (z.2 / s))), ⟨hz.1, hend⟩, rfl⟩
      rw [← htrace] at hmem
      exact hmem.2
    · rw [hΦout w hwK hwW]
      exact subset_closure ⟨hwK, hwW⟩
  · intro y hy
    have h := hΦρ (y, 0) ⟨hy, by norm_num, by norm_num⟩
    rw [hρzero y hy] at h
    rw [h]
    change ρ (y, max (-1) (min 1 (0 / s))) = y
    rw [zero_div, min_eq_right (show (0 : ℝ) ≤ 1 by norm_num),
      max_eq_right (show (-1 : ℝ) ≤ 0 by norm_num)]
    exact hρzero y hy
  · intro y hy e he
    have heI : e * s ∈ Icc (-1 : ℝ) 1 := by
      rcases he with h | h <;> rw [h] <;> exact ⟨by linarith, by linarith⟩
    rw [hΦρ (y, e * s) ⟨hy, heI⟩]
    change ρ (y, max (-1) (min 1 (e * s / s))) = ρ (y, e)
    rw [mul_div_assoc, div_self hs0.ne', mul_one]
    rcases he with h | h <;> rw [h]
    · rw [min_eq_right (show (-1 : ℝ) ≤ 1 by norm_num), max_self]
    · rw [min_self, max_eq_right (show (-1 : ℝ) ≤ 1 by norm_num)]

theorem IsPLHomeomorphOn.exists_isOpen_pair_of_bicollar_levels
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    {ρ : E × ℝ → E} {W : Set E} (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W)
    (hρzero : ∀ y ∈ L.space, ρ (y, 0) = y) (hWK : W ⊆ K.space) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1) {P : Set Schoenflies.Plane} (hPc : IsClosed P) {f : Schoenflies.Plane → E}
    (hf : ContinuousOn f P) (hfK : MapsTo f P K.space) (hfL : MapsTo f (frontier P) L.space) :
    ∃ U V : Set Schoenflies.Plane, IsOpen U ∧ IsOpen V ∧
      MapsTo f (U ∩ P) (ρ '' (L.space ×ˢ Ioo (-s) s)) ∧
      MapsTo f (V ∩ P) (K.space \ ρ '' (L.space ×ˢ Icc (-s) s)) ∧
      Disjoint (U ∩ P) (V ∩ P) ∧
      P \ f ⁻¹' (ρ '' (L.space ×ˢ {-s, s})) ⊆ U ∪ V ∧ frontier P ⊆ U := by
  obtain ⟨G, hG, hGK⟩ := hρ.exists_isOpen_inter_eq_image_prod_Ioo hK hL hWK hs1
  have hIcc : IsCompact (L.space ×ˢ Icc (-s) s) :=
    (isPolyhedron_space L).isCompact.prod isCompact_Icc
  have hcl : IsClosed (ρ '' (L.space ×ˢ Icc (-s) s)) :=
    (hIcc.image_of_continuousOn (hρ.isPiecewiseAffineOn.continuousOn.mono
      (prod_mono subset_rfl (Icc_subset_Icc (show (-1 : ℝ) ≤ -s by linarith) hs1)))).isClosed
  obtain ⟨U, hU, hUeq⟩ := continuousOn_iff'.mp hf G hG
  obtain ⟨V, hV, hVeq⟩ := continuousOn_iff'.mp hf _ hcl.isOpen_compl
  have hUmaps : MapsTo f (U ∩ P) (ρ '' (L.space ×ˢ Ioo (-s) s)) := by
    intro q hq
    rw [← hUeq] at hq
    rw [← hGK]
    exact ⟨hq.1, hfK hq.2⟩
  have hVmaps : MapsTo f (V ∩ P) (K.space \ ρ '' (L.space ×ˢ Icc (-s) s)) := by
    intro q hq
    rw [← hVeq] at hq
    exact ⟨hfK hq.2, hq.1⟩
  have hGmem : ∀ q ∈ P, f q ∈ ρ '' (L.space ×ˢ Ioo (-s) s) → q ∈ U := by
    intro q hqP hq
    rw [← hGK] at hq
    have hqG : q ∈ f ⁻¹' G ∩ P := ⟨hq.1, hqP⟩
    rw [hUeq] at hqG
    exact hqG.1
  refine ⟨U, V, hU, hV, hUmaps, hVmaps, ?_, ?_, ?_⟩
  · refine disjoint_left.mpr fun q hqU hqV => (hVmaps hqV).2 ?_
    obtain ⟨z, hz, hzq⟩ := hUmaps hqU
    exact ⟨z, ⟨hz.1, hz.2.1.le, hz.2.2.le⟩, hzq⟩
  · rintro q ⟨hqP, hqs⟩
    by_cases hq : f q ∈ ρ '' (L.space ×ˢ Icc (-s) s)
    · refine Or.inl (hGmem q hqP ?_)
      obtain ⟨z, hz, hzq⟩ := hq
      have hlo : -s < z.2 := by
        refine lt_of_le_of_ne hz.2.1 fun h => hqs ⟨(z.1, -s), ⟨hz.1, Or.inl rfl⟩, ?_⟩
        rw [h]
        exact hzq
      have hhi : z.2 < s := by
        refine lt_of_le_of_ne hz.2.2 fun h => hqs ⟨(z.1, s), ⟨hz.1, Or.inr rfl⟩, ?_⟩
        rw [← h]
        exact hzq
      exact ⟨z, ⟨hz.1, hlo, hhi⟩, hzq⟩
    · refine Or.inr ?_
      have hqV : q ∈ f ⁻¹' (ρ '' (L.space ×ˢ Icc (-s) s))ᶜ ∩ P := ⟨hq, hqP⟩
      rw [hVeq] at hqV
      exact hqV.1
  · intro q hq
    have hfq := hfL hq
    exact hGmem q (hPc.frontier_subset hq)
      ⟨(f q, 0), ⟨hfq, show -s < 0 by linarith, hs0⟩, hρzero _ hfq⟩

open Classical in
theorem IsPLHomeomorphOn.exists_continuousOn_mapsTo_space_of_bicollar_disk
    {K L R : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hR : IsCombinatorialManifoldWithBoundary 3 R) {ρ : E × ℝ → E} {W : Set E}
    (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W)
    (hρzero : ∀ y ∈ L.space, ρ (y, 0) = y)
    (hW : W ⊆ K.space \ (boundaryComplex 3 K).space) (hRspace : R.space = closure (K.space \ W))
    (hinj : ∀ c : ConnectedComponents (boundaryComplex 3 R).space,
      (connectedComponentComplex (boundaryComplex 3 R) c).space ⊆ W →
      ∀ hsub : (connectedComponentComplex (boundaryComplex 3 R) c).space ⊆ R.space,
      ∀ γ : freeLoop (connectedComponentComplex (boundaryComplex 3 R) c).space,
        IsNullHomotopic ((⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
          C((connectedComponentComplex (boundaryComplex 3 R) c).space, R.space)).comp γ) →
        IsNullHomotopic γ)
    {P : Set Schoenflies.Plane} (hP : IsPLBall 2 P) {f : Schoenflies.Plane → E}
    (hf : IsPiecewiseAffineOn f P) (hfK : MapsTo f P K.space)
    (hfL : MapsTo f (frontier P) L.space) :
    ∃ H : Schoenflies.Plane → E, ContinuousOn H P ∧ MapsTo H P L.space ∧
      EqOn H f (frontier P) := by
  set ψ := Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) with hψdef
  have hWK : W ⊆ K.space := hW.trans sdiff_subset
  have hfc : ContinuousOn f P := hf.continuousOn
  obtain ⟨s, hs0, hs1, hlev⟩ :=
    hρ.exists_finite_isPLSphere_levels_of_bicollar hK hL hρzero hWK hP hf hfK hfL
  obtain ⟨Cp, hCpfin, hCp, hCpdisj, hCpP, hCpeq⟩ := hlev s (by simp)
  obtain ⟨Cm, hCmfin, hCm, hCmdisj, hCmP, hCmeq⟩ := hlev (-s) (by simp)
  obtain ⟨Φ, hΦc, hΦW, hΦR, hΦL, hΦe⟩ :=
    hρ.exists_continuousOn_push_to_ends_mapsTo hK hL hρzero hW hs0 hs1.le
  obtain ⟨U, V, hU, hV, hUf, hVf, hUV, hcov, hfrU⟩ :=
    hρ.exists_isOpen_pair_of_bicollar_levels hK hL hρzero hWK hs0 hs1.le
      hP.isPolyhedron.isClosed hfc hfK hfL
  obtain ⟨-, -, -, -, -, htrace⟩ := hρ.inter_closure_sdiff_eq_image_prod_pair hK hL hW
  let ec : Set Schoenflies.Plane → ℝ := fun c => if c ∈ Cp then 1 else -1
  have hec : ∀ c, ec c ∈ ({-1, 1} : Set ℝ) := by
    intro c
    by_cases hcp : c ∈ Cp
    · exact Or.inr (ite_eq_left hcp)
    · exact Or.inl (ite_eq_right hcp)
  have hecI : ∀ c, ec c ∈ Icc (-1 : ℝ) 1 := by
    intro c
    rcases hec c with h | h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩
  have hlevc : ∀ c ∈ Cp ∪ Cm, c ⊆ P ∩ f ⁻¹' (ρ '' (L.space ×ˢ {ec c * s})) := by
    intro c hc
    by_cases hcp : c ∈ Cp
    · have h1 : ec c = 1 := ite_eq_left hcp
      rw [h1, one_mul, hCpeq]
      exact subset_sUnion_of_mem hcp
    · have h1 : ec c = -1 := ite_eq_right hcp
      rw [h1, neg_one_mul, hCmeq]
      exact subset_sUnion_of_mem (Or.resolve_left hc hcp)
  have hCsph : ∀ c ∈ Cp ∪ Cm, IsPLSphere 1 c := fun c hc => Or.elim hc (hCp c) (hCm c)
  have hne : ∀ c ∈ Cp ∪ Cm, c.Nonempty := fun c hc => (hCsph c hc).isConnected.nonempty
  choose! pt hpt using hne
  let yc : Set Schoenflies.Plane → E := fun c => (ψ (f (pt c))).1
  let B : Set Schoenflies.Plane → Set E := fun c =>
    (fun y => ρ (y, ec c)) '' connectedComponentIn L.space (yc c)
  have hcirc : ∀ c ∈ Cp ∪ Cm, ∀ q ∈ c, ∃ y ∈ connectedComponentIn L.space (yc c),
      f q = ρ (y, ec c * s) := by
    intro c hc
    have hts : ec c * s ∈ Icc (-1 : ℝ) 1 := by
      rcases hec c with h | h <;> rw [h] <;> exact ⟨by linarith, by linarith⟩
    exact hρ.exists_mem_connectedComponentIn_of_isPreconnected hts
      (hfc.mono fun q hq => (hlevc c hc hq).1) (hCsph c hc).isConnected.isPreconnected
      (fun q hq => (hlevc c hc hq).2) (hpt c hc)
  have hyc : ∀ c ∈ Cp ∪ Cm, yc c ∈ L.space := by
    intro c hc
    obtain ⟨y₀, hy₀, -⟩ := hcirc c hc (pt c) (hpt c hc)
    exact connectedComponentIn_nonempty_iff.mp ⟨y₀, hy₀⟩
  have hBW : ∀ c, B c ⊆ W := by
    rintro c _ ⟨y, hy, rfl⟩
    exact hρ.bijOn.mapsTo ⟨connectedComponentIn_subset _ _ hy, hecI c⟩
  have hBR : ∀ c, B c ⊆ R.space := by
    rintro c _ ⟨y, hy, rfl⟩
    have hmem : ρ (y, ec c) ∈ ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ)) :=
      ⟨(y, ec c), ⟨connectedComponentIn_subset _ _ hy, hec c⟩, rfl⟩
    rw [← htrace] at hmem
    rw [hRspace]
    exact hmem.2
  have hFB : ∀ c ∈ Cp ∪ Cm, MapsTo (fun q => Φ (f q)) c (B c) := by
    intro c hc q hq
    obtain ⟨y, hy, hfq⟩ := hcirc c hc q hq
    change Φ (f q) ∈ B c
    rw [hfq, hΦe y (connectedComponentIn_subset _ _ hy) (ec c) (hec c)]
    exact ⟨y, hy, rfl⟩
  have hfillW : ∀ c ∈ Cp ∪ Cm, ∀ G : Schoenflies.Plane → E,
      ContinuousOn G (closure (Schoenflies.inside c)) →
      MapsTo G (closure (Schoenflies.inside c)) W → MapsTo G c (B c) →
      ∃ G' : Schoenflies.Plane → E, ContinuousOn G' (closure (Schoenflies.inside c)) ∧
        MapsTo G' (closure (Schoenflies.inside c)) (B c) ∧ EqOn G' G c := by
    intro c hc G hG hGW hGB
    obtain ⟨r, hrc, hrB, hrfix⟩ :=
      hρ.exists_continuousOn_retraction_image_connectedComponentIn (hyc c hc) (hecI c)
    refine ⟨fun q => r (G q), hrc.comp hG hGW, fun q hq => hrB (hGW hq), fun q hq => ?_⟩
    obtain ⟨y, hy, hyq⟩ := hGB hq
    change r (G q) = G q
    rw [← hyq]
    exact hrfix y hy
  have hfillR : ∀ c ∈ Cp ∪ Cm, ∀ G : Schoenflies.Plane → E,
      ContinuousOn G (closure (Schoenflies.inside c)) →
      MapsTo G (closure (Schoenflies.inside c)) R.space → MapsTo G c (B c) →
      ∃ G' : Schoenflies.Plane → E, ContinuousOn G' (closure (Schoenflies.inside c)) ∧
        MapsTo G' (closure (Schoenflies.inside c)) (B c) ∧ EqOn G' G c := by
    intro c hc G hG hGR hGB
    obtain ⟨c', hc'⟩ := exists_connectedComponentComplex_boundaryComplex_eq_image_of_bicollar
      hK hL hR hρ hW hRspace (hyc c hc) (hec c)
    have hBc : B c = (connectedComponentComplex (boundaryComplex 3 R) c').space := hc'.symm
    have hsub : (connectedComponentComplex (boundaryComplex 3 R) c').space ⊆ R.space :=
      hBc ▸ hBR c
    rw [hBc] at hGB ⊢
    exact exists_continuousOn_mapsTo_closure_inside_of_forall_isNullHomotopic hsub
      (hinj c' (hBc ▸ hBW c) hsub) (hCsph c hc) hG hGR hGB
  have hdisj : (Cp ∪ Cm).PairwiseDisjoint id := by
    refine pairwiseDisjoint_union.mpr ⟨hCpdisj, hCmdisj, fun c hc c' hc' _ => ?_⟩
    refine disjoint_left.mpr fun q hq hq' => ?_
    have h1 : q ∈ ⋃₀ Cp := ⟨c, hc, hq⟩
    have h2 : q ∈ ⋃₀ Cm := ⟨c', hc', hq'⟩
    rw [← hCpeq] at h1
    rw [← hCmeq] at h2
    obtain ⟨-, z, hz, hzq⟩ := h1
    obtain ⟨-, z', hz', hzq'⟩ := h2
    have e1 : z.2 = s := hz.2
    have e2 : z'.2 = -s := hz'.2
    have hzI : z ∈ L.space ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨hz.1, by rw [e1]; exact ⟨by linarith, by linarith⟩⟩
    have hz'I : z' ∈ L.space ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨hz'.1, by rw [e2]; exact ⟨by linarith, by linarith⟩⟩
    have h := congrArg Prod.snd (hρ.bijOn.injOn hzI hz'I (hzq.trans hzq'.symm))
    rw [e1, e2] at h
    linarith
  have hcover : P \ ⋃₀ (Cp ∪ Cm) ⊆ U ∪ V := by
    rintro q ⟨hqP, hqC⟩
    refine hcov ⟨hqP, ?_⟩
    rintro ⟨z, ⟨hz1, hz2⟩, hzq⟩
    apply hqC
    rcases hz2 with h | h
    · have hq : q ∈ P ∩ f ⁻¹' (ρ '' (L.space ×ˢ {-s})) := ⟨hqP, z, ⟨hz1, h⟩, hzq⟩
      rw [hCmeq] at hq
      obtain ⟨c, hc, hqc⟩ := hq
      exact ⟨c, Or.inr hc, hqc⟩
    · have hq : q ∈ P ∩ f ⁻¹' (ρ '' (L.space ×ˢ {s})) := ⟨hqP, z, ⟨hz1, h⟩, hzq⟩
      rw [hCpeq] at hq
      obtain ⟨c, hc, hqc⟩ := hq
      exact ⟨c, Or.inl hc, hqc⟩
  have hFU : MapsTo (fun q => Φ (f q)) (U ∩ P) W := by
    intro q hq
    obtain ⟨z, hz, hzq⟩ := hUf hq
    apply hΦW
    rw [← hzq]
    exact hρ.bijOn.mapsTo ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hFV : MapsTo (fun q => Φ (f q)) (V ∩ P) R.space := by
    intro q hq
    rw [hRspace]
    exact hΦR (hVf hq)
  obtain ⟨G₀, hG₀c, hG₀W, hG₀f⟩ := exists_continuousOn_mapsTo_of_jordan_disk_pasting hP
    (XW := W) (XR := R.space) (C := Cp ∪ Cm) B (fun c _ => subset_inter (hBW c) (hBR c))
    hfillW hfillR (hCpfin.union hCmfin) hCsph hdisj
    (fun c hc => Or.elim hc (hCpP c) (hCmP c)) (F := fun q => Φ (f q)) (hΦc.comp hfc hfK)
    hFB hU hV hUV hcover hFU hFV hfrU
  have hψc : ContinuousOn ψ W := hρ.isPiecewiseAffineOn_invFunOn.continuousOn
  refine ⟨fun q => (ψ (G₀ q)).1, continuous_fst.comp_continuousOn (hψc.comp hG₀c hG₀W),
    fun q hq => (hρ.bijOn.surjOn.mapsTo_invFunOn (hG₀W hq)).1, fun q hq => ?_⟩
  have hfq := hfL hq
  have h : ψ (ρ (f q, 0)) = (f q, 0) :=
    hρ.bijOn.invOn_invFunOn.1 ⟨hfq, by norm_num, by norm_num⟩
  rw [hρzero (f q) hfq] at h
  change (ψ (G₀ q)).1 = f q
  rw [hG₀f hq]
  change (ψ (Φ (f q))).1 = f q
  rw [hΦL (f q) hfq, h]

open Classical in
theorem exists_nontrivial_boundary_loop_of_bicollar_complement
    (K L R : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite L.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space \ (boundaryComplex 3 K).space)
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (W : Set E) (ρ : E × ℝ → E)
    (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W)
    (hρzero : ∀ y ∈ L.space, ρ (y, 0) = y)
    (hW : W ⊆ K.space \ (boundaryComplex 3 K).space)
    (hWnhds : W ∈ 𝓝ˢ[K.space] L.space)
    (hRspace : R.space = closure (K.space \ W))
    (x : L.space) (g : FundamentalGroup L.space x) (hg : g ≠ 1)
    (hgin : FundamentalGroup.map
      (⟨Set.inclusion (hLK.trans sdiff_subset), continuous_inclusion _⟩ :
        C(L.space, K.space)) x g = 1) :
    ∃ c : ConnectedComponents (boundaryComplex 3 R).space,
      (connectedComponentComplex (boundaryComplex 3 R) c).space ⊆ W ∧
      ∃ hsub : (connectedComponentComplex (boundaryComplex 3 R) c).space ⊆ R.space,
      ∃ γ : freeLoop (connectedComponentComplex (boundaryComplex 3 R) c).space,
        IsNullHomotopic ((⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
          C((connectedComponentComplex (boundaryComplex 3 R) c).space, R.space)).comp γ) ∧
        ¬ IsNullHomotopic γ := by
  by_contra hno
  let _ := hWnhds
  have hinj : ∀ c : ConnectedComponents (boundaryComplex 3 R).space,
      (connectedComponentComplex (boundaryComplex 3 R) c).space ⊆ W →
      ∀ hsub : (connectedComponentComplex (boundaryComplex 3 R) c).space ⊆ R.space,
      ∀ γ : freeLoop (connectedComponentComplex (boundaryComplex 3 R) c).space,
        IsNullHomotopic ((⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
          C((connectedComponentComplex (boundaryComplex 3 R) c).space, R.space)).comp γ) →
        IsNullHomotopic γ := by
    intro c hcW hsub γ hγ
    by_contra hγ'
    exact hno ⟨c, hcW, hsub, γ, hγ, hγ'⟩
  have hLK' : L.space ⊆ K.space := hLK.trans sdiff_subset
  obtain ⟨γ₀, hγ₀, hγ₀K⟩ :=
    exists_non_nullhomotopic_freeLoop_of_nontrivial_fundamentalGroup_kernel _ x g hg hgin
  obtain ⟨K', hK'K, hK'fin, hK'L⟩ :=
    exists_isSubdivision_restrict_space K (isPolyhedron_space L) hLK'
  let _ : Finite K'.faces := hK'fin.to_subtype
  have hK'space : K'.space = K.space := hK'K.1
  have hγ₀mem : ∀ θ, (γ₀ θ : E) ∈ connectedComponentIn L.space (γ₀ 0 : E) := by
    intro θ
    have hpre : IsPreconnected (range fun θ => (γ₀ θ : E)) :=
      isPreconnected_range (continuous_subtype_val.comp γ₀.continuous)
    refine hpre.subset_connectedComponentIn ⟨0, rfl⟩ ?_ ⟨θ, rfl⟩
    rintro _ ⟨θ', rfl⟩
    exact (γ₀ θ').2
  set V := connectedComponentIn L.space (γ₀ 0 : E) with hVdef
  have hVL : V ⊆ L.space := connectedComponentIn_subset _ _
  have hVB : V ⊆ (restrict K' L.space).space := by
    rw [hK'L]
    exact hVL
  have hVK : V ⊆ K'.space := by
    rw [hK'space]
    exact hVL.trans hLK'
  have hVcomp : ∀ y ∈ V, connectedComponentIn (restrict K' L.space).space y = V := by
    intro y hy
    rw [hK'L]
    exact (connectedComponentIn_eq hy).symm
  let γV : freeLoop V := ⟨fun θ => ⟨γ₀ θ, hγ₀mem θ⟩,
    (continuous_subtype_val.comp γ₀.continuous).subtype_mk _⟩
  have hnull : ((⟨Set.inclusion hVK, continuous_inclusion hVK⟩ : C(V, K'.space)).comp
      γV).Nullhomotopic := by
    have h := hγ₀K.comp_right
      ((Homeomorph.setCongr hK'space.symm : K.space ≃ₜ K'.space) : C(K.space, K'.space))
    have heq : ((Homeomorph.setCongr hK'space.symm : K.space ≃ₜ K'.space) :
        C(K.space, K'.space)).comp
        ((⟨Set.inclusion hLK', continuous_inclusion hLK'⟩ : C(L.space, K.space)).comp γ₀) =
        (⟨Set.inclusion hVK, continuous_inclusion hVK⟩ : C(V, K'.space)).comp γV :=
      ContinuousMap.ext fun _ => Subtype.ext rfl
    rw [← heq]
    exact h
  obtain ⟨P, f, a, δ, hP, hf, hfK', hfV, hδ, hδγ⟩ :=
    exists_isPiecewiseAffineOn_fill_of_nullhomotopic K' (restrict K' L.space)
      (restrict_faces_subset K' L.space) hVB hVK hVcomp γV hnull
  have hfK : MapsTo f P K.space := hK'space ▸ hfK'
  have hfL : MapsTo f (frontier P) L.space := hfV.mono_right hVL
  obtain ⟨H, hHc, hHL, hHf⟩ := hρ.exists_continuousOn_mapsTo_space_of_bicollar_disk hK hL hR
    hρzero hW hRspace hinj hP hf hfK hfL
  have hfrP : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  let bL : C(frontier P, L.space) :=
    ⟨fun z => ⟨f z, hfL z.2⟩, (hf.continuousOn.mono hfrP).domRestrict.subtype_mk _⟩
  have hbL : bL.Nullhomotopic :=
    hP.nullhomotopic_of_continuousOn hfrP hHc hHL bL fun z => (hHf z.2).symm
  let iV : C(V, L.space) := ⟨Set.inclusion hVL, continuous_inclusion hVL⟩
  have h1 : (iV.comp δ).Nullhomotopic := by
    have heq : iV.comp δ = bL.comp (a : C(loopCircle, frontier P)) :=
      ContinuousMap.ext fun θ => Subtype.ext (hδ θ)
    rw [heq]
    exact hbL.comp_left _
  have h2 : (iV.comp δ).Homotopic γ₀ := by
    have heq : iV.comp γV = γ₀ := ContinuousMap.ext fun _ => Subtype.ext rfl
    rw [← heq]
    exact (ContinuousMap.Homotopic.refl iV).comp hδγ
  obtain ⟨y, hy⟩ := h1
  exact hγ₀ ⟨y, h2.symm.trans hy⟩

end DifferentialGeometry.Topology.PiecewiseLinear

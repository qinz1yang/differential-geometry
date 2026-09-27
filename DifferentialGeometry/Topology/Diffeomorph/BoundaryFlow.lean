import DifferentialGeometry.Topology.Diffeomorph.Flow
import DifferentialGeometry.Analysis.ODE.InvariantHyperplane
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

import Mathlib.Tactic.Ring

open Set Filter
open scoped ContDiff Manifold Topology

namespace Diffeomorph

private theorem contDiffOn_native_chart_pushforward
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    (X : (x : M) → TangentSpace I x)
    (hX : ContMDiff I I.tangent ∞ (fun x => (X x : TangentBundle I M))) :
    ContDiffOn ℝ ∞
      (fun y => mfderiv I 𝓘(ℝ, E) c (c.symm y) (X (c.symm y))) c.target := by
  have hT := c.contMDiffOn.contMDiffOn_tangentMapWithin
    (m := ∞) (by simp) c.open_source.uniqueMDiffOn
  have hsection : ContMDiffOn I (𝓘(ℝ, E).tangent) ∞
      (fun x => tangentMapWithin I 𝓘(ℝ, E) c c.source
        (X x : TangentBundle I M)) c.source :=
    hT.comp hX.contMDiffOn (fun _ hx => hx)
  have hraw : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun x => mfderivWithin I 𝓘(ℝ, E) c c.source x (X x)) c.source := by
    intro x hx
    exact (contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E)).contMDiffAt.comp_contMDiffWithinAt x
      (hsection x hx)
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun y => mfderivWithin I 𝓘(ℝ, E) c c.source (c.symm y) (X (c.symm y))) c.target :=
    hraw.comp c.symm.contMDiffOn (fun _ hy => c.toPartialEquiv.map_target hy)
  apply hcomp.contDiffOn.congr
  intro y hy
  have he : mfderivWithin I 𝓘(ℝ, E) c c.source (c.symm y) =
      mfderiv I 𝓘(ℝ, E) c (c.symm y) :=
    mfderivWithin_of_mem_nhds (c.open_source.mem_nhds (c.toPartialEquiv.map_target hy))
  exact congrArg (fun A : TangentSpace I (c.symm y) →L[ℝ] E => A (X (c.symm y))) he.symm

private theorem exists_compact_tangent_extension_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set (ℝ × E)} (hU : IsOpen U) {p : ℝ × E} (hp : p ∈ U)
    {V : ℝ × E → ℝ × E} (hV : ContDiffOn ℝ ∞ V U)
    (htangent : ∀ y ∈ U, y.1 = 0 → (V y).1 = 0) :
    ∃ W : ℝ × E → ℝ × E, ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
      (∀ y, y.1 = 0 → (W y).1 = 0) ∧ W =ᶠ[𝓝 p] V := by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
  let b : ContDiffBump p := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let W : ℝ × E → ℝ × E := fun y => b y • V y
  have hbU : tsupport b ⊆ U := by simpa only [b.tsupport_eq] using hrU
  have hWs : tsupport W ⊆ tsupport b := tsupport_smul_subset_left b V
  have hW : ContDiff ℝ ∞ W := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact b.contDiffAt.smul ((hV y hy).contDiffAt (hU.mem_nhds hy))
    · have hyb : y ∉ tsupport b := fun hyb => hy (hbU hyb)
      have hz : W =ᶠ[𝓝 y] fun _ => (0 : ℝ × E) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hyb] with z hz
        simp only [W, hz, Pi.zero_apply, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  refine ⟨W, hW, b.hasCompactSupport.of_isClosed_subset isClosed_closure hWs, ?_, ?_⟩
  · intro y hy
    by_cases hyU : y ∈ U
    · change b y * (V y).1 = 0
      rw [htangent y hyU hy, mul_zero]
    · have hyb : y ∉ tsupport b := fun hyb => hyU (hbU hyb)
      simp only [W, image_eq_zero_of_notMem_tsupport hyb, zero_smul, Prod.fst_zero]
  · filter_upwards [b.eventuallyEq_one] with y hy
    simp only [W, hy, one_smul, Pi.one_apply]

private theorem frontier_product_halfspace {E : Type*} [TopologicalSpace E] :
    frontier {z : ℝ × E | 0 ≤ z.1} = {z | z.1 = 0} := by
  change frontier (Prod.fst ⁻¹' Ici (0 : ℝ)) = Prod.fst ⁻¹' {(0 : ℝ)}
  rw [← isOpenMap_fst.preimage_frontier_eq_frontier_preimage continuous_fst (Ici (0 : ℝ)),
    frontier_Ici]

private theorem compactSupportFlow_eventually_mem_frontier_of_chart_tangent
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (X : (x : M) → TangentSpace I x)
    (hX : ContMDiff I I.tangent ∞ (fun x => (X x : TangentBundle I M)))
    (hsupp : IsCompact (tsupport X)) (D : Set M)
    (c : PartialDiffeomorph I 𝓘(ℝ, ℝ × E) M (ℝ × E) ∞)
    (hD : c.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z.1})
    (htangent : ∀ x ∈ frontier D ∩ c.source,
      (mfderiv I 𝓘(ℝ, ℝ × E) c x (X x)).1 = 0)
    {p : M} (hp : p ∈ frontier D ∩ c.source) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      Diffeomorph.compactSupportFlow X hX hsupp t p ∈ frontier D ∩ c.source := by
  let e : F ≃L[ℝ] (ℝ × E) :=
    (c.isLocalDiffeomorphAt I 𝓘(ℝ, ℝ × E) ∞ hp.2).mfderivToContinuousLinearEquiv (by simp)
  let : FiniteDimensional ℝ (ℝ × E) :=
    FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  let : FiniteDimensional ℝ E :=
    FiniteDimensional.of_surjective (LinearMap.snd ℝ ℝ E) Prod.snd_surjective
  let V : ℝ × E → ℝ × E := fun y => mfderiv I 𝓘(ℝ, ℝ × E) c (c.symm y) (X (c.symm y))
  have hV : ContDiffOn ℝ ∞ V c.target := contDiffOn_native_chart_pushforward c X hX
  have hVp : (c p).1 = 0 := by
    have h := (hD.frontier hp.2).mpr hp.1
    simpa only [frontier_product_halfspace, mem_ofPred_eq] using! h
  have hVt : ∀ y ∈ c.target, y.1 = 0 → (V y).1 = 0 := by
    intro y hy hy0
    have hsrc := c.toPartialEquiv.map_target hy
    have hfr : c.symm y ∈ frontier D := by
      apply (hD.frontier hsrc).mp
      change c (c.symm y) ∈ frontier {z : ℝ × E | 0 ≤ z.1}
      have he : c (c.symm y) = y := c.toPartialEquiv.right_inv hy
      rw [he, frontier_product_halfspace]
      exact hy0
    exact htangent _ ⟨hfr, hsrc⟩
  obtain ⟨W, hW, hWc, hWt, hWV⟩ := exists_compact_tangent_extension_of_contDiffOn
    c.open_target (c.toPartialEquiv.map_source hp.2) hV hVt
  have hWm : ContMDiff 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ × E).tangent) ∞
      (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, ℝ × E) (ℝ × E))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hW
  let γ : ℝ → M := fun t => Diffeomorph.compactSupportFlow X hX hsupp t p
  let η : ℝ → ℝ × E := fun t => Diffeomorph.compactSupportFlow W hWm hWc t (c p)
  have hγ : IsMIntegralCurve γ X := Diffeomorph.isMIntegralCurve_compactSupportFlow X hX hsupp p
  have hη : IsMIntegralCurve η W := Diffeomorph.isMIntegralCurve_compactSupportFlow W hWm hWc (c p)
  have hγ0 : γ 0 = p := by simp [γ]
  have hη0 : η 0 = c p :=
    DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero W hWm hWc) (c p)
  have hηi : IsIntegralCurve η (fun _ y => W y) := by
    intro t
    have h : HasFDerivAt η ((1 : ℝ →L[ℝ] ℝ).smulRight (W (η t))) t :=
      (hη t).hasFDerivAt
    simpa using h.hasDerivAt
  have hηplane (t : ℝ) : (η t).1 = 0 := by
    have h := hηi.fst_eq_zero_iff_of_tangent
      ((hW.comp contDiff_snd).of_le (by simp)) (fun _ y => hWt (0, y) rfl) 0 t
    exact h.mp (by simpa only [hη0] using hVp)
  have hsrc : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ c.source :=
    hγ.continuous.continuousAt.tendsto.eventually (hγ0.symm ▸ c.open_source.mem_nhds hp.2)
  have hcγ : ContinuousAt (c ∘ γ) 0 := by
    exact (c.contMDiffOn.contMDiffAt
      (c.open_source.mem_nhds (hγ0.symm ▸ hp.2))).continuousAt.comp hγ.continuous.continuousAt
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), W (c (γ t)) = V (c (γ t)) := by
    have ht : Tendsto (c ∘ γ) (𝓝 0) (𝓝 (c p)) := by
      simpa only [Function.comp_apply, hγ0] using! hcγ.tendsto
    exact ht.eventually hWV
  have hcoord : IsMIntegralCurveAt (I := 𝓘(ℝ, ℝ × E)) (c ∘ γ) W 0 := by
    filter_upwards [hsrc, hevent] with t ht he
    have hc := (c.mdifferentiableAt (by simp) ht).hasMFDerivAt
    have hcomp := hc.comp t (hγ t)
    apply hcomp.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro a
    let u : ℝ := NormedSpace.fromTangentSpace t a
    change mfderiv I 𝓘(ℝ, ℝ × E) c (γ t) (u • X (γ t)) = u • W (c (γ t))
    rw [map_smul, he]
    dsimp only [V]
    have hinv : c.symm (c (γ t)) = γ t := c.toPartialEquiv.left_inv ht
    exact congrArg (fun y : M => u • (mfderiv I 𝓘(ℝ, ℝ × E) c y (X y) : ℝ × E)) hinv.symm
  have heq : c ∘ γ =ᶠ[𝓝 (0 : ℝ)] η :=
    isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
      ((hWm.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).contMDiffAt)
      hcoord (hη.isMIntegralCurveAt 0) (by simp only [Function.comp_apply, hγ0, hη0])
  filter_upwards [hsrc, heq] with t ht he
  refine ⟨(hD.frontier ht).mp ?_, ht⟩
  rw [frontier_product_halfspace]
  change (c (γ t)).1 = 0
  rw [show c (γ t) = η t from he]
  exact hηplane t

private theorem continuous_curve_mem_of_avoids_frontier
    {M : Type*} [TopologicalSpace M] (γ : ℝ → M) (hγ : Continuous γ)
    (D : Set M) (havoid : ∀ t, γ t ∉ frontier D) (hzero : γ 0 ∈ D) :
    ∀ t, γ t ∈ D := by
  let S : Set ℝ := {t | γ t ∈ D}
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    change γ t ∈ D at ht
    have hi : γ t ∈ interior D := (mem_interior_iff_notMem_frontier ht).mpr (havoid t)
    exact hγ.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hi)
  have hSc : IsOpen Sᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    change γ t ∈ Dᶜ at ht
    have hn : γ t ∉ frontier Dᶜ := by simpa only [frontier_compl] using havoid t
    have hi : γ t ∈ interior Dᶜ := (mem_interior_iff_notMem_frontier ht).mpr hn
    exact hγ.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hi)
  have hclosed : IsClosed S := by simpa only [compl_compl] using hSc.isClosed_compl
  have hall : S = univ := (show IsClopen S from ⟨hclosed, hS⟩).eq_univ ⟨0, hzero⟩
  intro t
  have ht : t ∈ S := by rw [hall]; exact mem_univ _
  exact ht

theorem compactSupportFlow_mem_iff_of_boundary_tangent
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (X : (x : M) → TangentSpace I x)
    (hX : ContMDiff I I.tangent ∞ (fun x => (X x : TangentBundle I M)))
    (hsupp : IsCompact (tsupport X)) (D : Set M)
    (hcharts : ∀ p ∈ frontier D, X p ≠ 0 →
      ∃ c : PartialDiffeomorph I 𝓘(ℝ, ℝ × E) M (ℝ × E) ∞,
        p ∈ c.source ∧ c.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z.1} ∧
        ∀ x ∈ frontier D ∩ c.source,
          (mfderiv I 𝓘(ℝ, ℝ × E) c x (X x)).1 = 0) :
    let Φ := Diffeomorph.compactSupportFlow X hX hsupp
    ∀ (t : ℝ) (x : M),
      (Φ t x ∈ frontier D ↔ x ∈ frontier D) ∧
      (Φ t x ∈ D ↔ x ∈ D) ∧
      ((Φ t).symm x ∈ frontier D ↔ x ∈ frontier D) ∧
      ((Φ t).symm x ∈ D ↔ x ∈ D) := by
  dsimp only
  let Φ := Diffeomorph.compactSupportFlow X hX hsupp
  have hzero (x : M) : Φ 0 x = x := by simp [Φ]
  have hadd (s t : ℝ) (x : M) : Φ (s + t) x = Φ t (Φ s x) := by
    exact DFunLike.congr_fun (Diffeomorph.compactSupportFlow_add X hX hsupp s t) x
  have hcancel (t : ℝ) (x : M) : Φ (-t) (Φ t x) = x := by
    rw [← hadd, add_neg_cancel, hzero]
  have hcontinuous (x : M) : Continuous (fun t => Φ t x) :=
    (Diffeomorph.isMIntegralCurve_compactSupportFlow X hX hsupp x).continuous
  have hstationary (x : M) (hx : X x = 0) (t : ℝ) : Φ t x = x :=
    Diffeomorph.compactSupportFlow_apply_eq_self_of_eq_zero X hX hsupp hx t
  have hlocal (x : M) (hx : x ∈ frontier D) :
      ∀ᶠ t in 𝓝 (0 : ℝ), Φ t x ∈ frontier D := by
    by_cases hxX : X x = 0
    · exact Eventually.of_forall (fun t => by rw [hstationary x hxX t]; exact hx)
    · obtain ⟨c, hxc, hcD, hct⟩ := hcharts x hx hxX
      exact (compactSupportFlow_eventually_mem_frontier_of_chart_tangent
        X hX hsupp D c hcD hct ⟨hx, hxc⟩).mono (fun _ ht => ht.1)
  have hfrontier (x : M) (hx : x ∈ frontier D) (t : ℝ) : Φ t x ∈ frontier D := by
    let S : Set ℝ := {s | Φ s x ∈ frontier D}
    have hSc : IsClosed S := isClosed_frontier.preimage (hcontinuous x)
    have hSo : IsOpen S := by
      apply isOpen_iff_mem_nhds.mpr
      intro s hs
      have hshift : Tendsto (fun u : ℝ => u - s) (𝓝 s) (𝓝 0) := by
        have h : Continuous (fun u : ℝ => u - s) := continuous_id.sub continuous_const
        simpa only [sub_self] using (h.continuousAt (x := s)).tendsto
      filter_upwards [hshift.eventually (hlocal (Φ s x) hs)] with u hu
      have he : Φ (u - s) (Φ s x) = Φ u x := by
        calc
          Φ (u - s) (Φ s x) = Φ (s + (u - s)) x := (hadd s (u - s) x).symm
          _ = Φ u x := congrArg (fun v : ℝ => Φ v x) (by ring)
      change Φ u x ∈ frontier D
      rw [← he]
      exact hu
    have hall : S = univ := (show IsClopen S from ⟨hSc, hSo⟩).eq_univ
      ⟨0, by change Φ 0 x ∈ frontier D; rw [hzero]; exact hx⟩
    have ht : t ∈ S := by rw [hall]; exact mem_univ _
    exact ht
  have hfrontier_iff (t : ℝ) (x : M) : Φ t x ∈ frontier D ↔ x ∈ frontier D := by
    constructor
    · intro hx
      have h := hfrontier (Φ t x) hx (-t)
      simpa only [hcancel] using h
    · exact fun hx => hfrontier x hx t
  have hset (x : M) (hx : x ∈ D) (t : ℝ) : Φ t x ∈ D := by
    by_cases hxX : X x = 0
    · rw [hstationary x hxX t]
      exact hx
    by_cases hxb : x ∈ frontier D
    · have hyb : Φ t x ∈ frontier D := hfrontier x hxb t
      have hyX : X (Φ t x) ≠ 0 := by
        intro hyX
        have hfix := hstationary (Φ t x) hyX (-t)
        have he : Φ t x = x := hfix.symm.trans (hcancel t x)
        have hy0 : (X (Φ t x) : F) = 0 := hyX
        have hx0 : (X x : F) = 0 :=
          (congrArg (fun y : M => (X y : F)) he).symm.trans hy0
        exact hxX hx0
      obtain ⟨c, hyc, hcD, _⟩ := hcharts (Φ t x) hyb hyX
      have hy0 : (c (Φ t x)).1 = 0 := by
        have h := (hcD.frontier hyc).mpr hyb
        simpa only [frontier_product_halfspace, mem_ofPred_eq] using! h
      apply (hcD hyc).mp
      change 0 ≤ (c (Φ t x)).1
      rw [hy0]
    · exact continuous_curve_mem_of_avoids_frontier (fun s => Φ s x) (hcontinuous x) D
        (fun s hs => hxb ((hfrontier_iff s x).mp hs)) (by rw [hzero]; exact hx) t
  have hset_iff (t : ℝ) (x : M) : Φ t x ∈ D ↔ x ∈ D := by
    constructor
    · intro hx
      have h := hset (Φ t x) hx (-t)
      simpa only [hcancel] using h
    · exact fun hx => hset x hx t
  intro t x
  have he : (Φ t).symm = Φ (-t) := Diffeomorph.compactSupportFlow_symm X hX hsupp t
  exact ⟨hfrontier_iff t x, hset_iff t x,
    by rw [he]; exact hfrontier_iff (-t) x,
    by rw [he]; exact hset_iff (-t) x⟩

end Diffeomorph

import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing
import DifferentialGeometry.Topology.Manifold.RelativeCollarIsotopy
import DifferentialGeometry.Topology.Manifold.RelativeCollarUniqueness
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.SupportedExtension
import DifferentialGeometry.Topology.Manifold.ProductBoundaryExtension
import DifferentialGeometry.Topology.Manifold.SmoothExtension
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

/-!
# Straightening two half collars of a boundary torus

Packet CS of the P1 survey. Two half collars `c₀ c₁` of the same boundary torus of a compact
carrier that agree on the torus are related by a diffeomorphism supported in any prescribed open
neighbourhood of the torus: `Φ ∘ c₀ = c₁` on a thinner half collar.

The transition `g = c₀⁻¹ ∘ c₁` and its inverse are extended across the boundary to maps of the
boundaryless model `T² × ℝ`. In each chart of `T²` the straight-line isotopy from the identity to
the chart expression is extended to an ambient isotopy, relative to the zero section and to the
region already straightened; finitely many charts cover `T²`. The straightening of `T² × ℝ` fixes
`T² × 0` and has compact support, so it preserves `T² × [0, ∞)`; its restriction is conjugated
back to the carrier by `c₀`. The boundary hypothesis `hb` of the frozen statement is not needed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

section Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem fderiv_apply_zeroSection {F : E × ℝ → E × ℝ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hfixed : ∀ y ∈ U, F (y, 0) = (y, 0))
    (hF : DifferentiableAt ℝ F (x, 0)) (v : E) :
    fderiv ℝ F (x, 0) (v, 0) = (v, 0) := by
  have hd := hF.hasFDerivAt.comp (f := fun y : E => (y, (0 : ℝ))) x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x))
  have hid := ((hasFDerivAt_id x).prodMk
    (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x)).congr_of_eventuallyEq
      (f₁ := F ∘ fun y : E => (y, (0 : ℝ)))
      (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) (fun y hy => hfixed y hy))
  exact congrArg (fun L : E →L[ℝ] E × ℝ => L v) (hd.unique hid)

private theorem pos_normal_of_leftInverse {F F' : E × ℝ → E × ℝ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hfixed : ∀ y ∈ U, F (y, 0) = (y, 0))
    (hF : DifferentiableAt ℝ F (x, 0)) (hF' : DifferentiableAt ℝ F' (x, 0))
    (hinv : ∀ᶠ z in 𝓝[{z : E × ℝ | 0 ≤ z.2}] (x, 0), F' (F z) = z)
    (hnn : ∀ᶠ z in 𝓝[{z : E × ℝ | 0 ≤ z.2}] (x, 0), 0 ≤ (F z).2) :
    0 < (fderiv ℝ F (x, 0) (0, 1)).2 := by
  set B := fderiv ℝ F (x, 0)
  set s : Set (E × ℝ) := {z | 0 ≤ z.2}
  have htan := fderiv_apply_zeroSection hU hx hfixed hF
  have hFx : F (x, 0) = (x, 0) := hfixed x hx
  have hxs : ((x, 0) : E × ℝ) ∈ s := show (0 : ℝ) ≤ 0 from le_rfl
  have hs : UniqueDiffWithinAt ℝ s (x, 0) := by
    have hseq : s = univ ×ˢ Ici (0 : ℝ) := by
      ext z
      simp [s]
    rw [hseq]
    exact (uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)) (x, 0)
      ⟨mem_univ _, show (0 : ℝ) ∈ Ici (0 : ℝ) from mem_Ici.mpr le_rfl⟩
  have h1 : HasFDerivAt F' (fderiv ℝ F' (x, 0)) (F (x, 0)) := by
    rw [hFx]
    exact hF'.hasFDerivAt
  have hcomp : HasFDerivWithinAt (F' ∘ F) ((fderiv ℝ F' (x, 0)).comp B) s (x, 0) :=
    (h1.comp (x, 0) hF.hasFDerivAt).hasFDerivWithinAt
  have hid : HasFDerivWithinAt (F' ∘ F) (ContinuousLinearMap.id ℝ (E × ℝ)) s (x, 0) :=
    (hasFDerivWithinAt_id (x, 0) s).congr_of_eventuallyEq hinv
      (hinv.self_of_nhdsWithin hxs)
  have heq : (fderiv ℝ F' (x, 0)).comp B = ContinuousLinearMap.id ℝ (E × ℝ) :=
    hs.eq hcomp hid
  have hinjB : Injective B := fun a b hab => by
    have ha := congrArg (fun L : (E × ℝ) →L[ℝ] (E × ℝ) => L a) heq
    have hb := congrArg (fun L : (E × ℝ) →L[ℝ] (E × ℝ) => L b) heq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at ha hb
    rw [← ha, ← hb, hab]
  have hmin : IsLocalMinOn (fun z => (F z).2) s (x, 0) := by
    change ∀ᶠ z in 𝓝[s] (x, 0), (F (x, 0)).2 ≤ (F z).2
    rw [hFx]
    exact hnn
  have hderiv : HasFDerivWithinAt (fun z => (F z).2)
      ((ContinuousLinearMap.snd ℝ E ℝ).comp B) s (x, 0) :=
    (hasFDerivAt_snd.comp (x, 0) hF.hasFDerivAt).hasFDerivWithinAt
  have hconv : Convex ℝ s := (convex_Ici (0 : ℝ)).linear_preimage (LinearMap.snd ℝ E ℝ)
  have hcone : ((0 : E), (1 : ℝ)) ∈ posTangentConeAt s (x, 0) := by
    apply mem_posTangentConeAt_of_segment_subset
    apply hconv.segment_subset hxs
    change (0 : ℝ) ≤ ((x, (0 : ℝ)) + ((0 : E), (1 : ℝ))).2
    simp
  have hnonneg : 0 ≤ (B (0, 1)).2 := hmin.hasFDerivWithinAt_nonneg hderiv hcone
  rcases hnonneg.lt_or_eq with h | h
  · exact h
  · exfalso
    have h2 : B (0, 1) = B ((B (0, 1)).1, 0) := by
      rw [htan]
      exact Prod.ext rfl h.symm
    have h3 := congrArg Prod.snd (hinjB h2)
    simp at h3

end Analysis

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Z H M : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ Z H}

private theorem exists_chart_straightening
    (e : OpenPartialHomeomorph M (E × ℝ))
    (he : ContMDiffOn I 𝓘(ℝ, E × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E × ℝ) I ∞ e.symm e.target)
    {F : E × ℝ → E × ℝ} {W : Set (E × ℝ)} (hW : IsOpen W) (hWt : W ⊆ e.target)
    (hF : ContDiffOn ℝ ∞ F W) {U : Set E} (hU : IsOpen U)
    (hUW : U ×ˢ ({0} : Set ℝ) ⊆ W) (hfixed : ∀ x ∈ U, F (x, 0) = (x, 0))
    {Y : Set M} (hY : ∀ z ∈ W, e.symm z ∈ Y → F z = z)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (hpos : ∀ x ∈ K, 0 < (fderiv ℝ F (x, 0) (0, 1)).2)
    {O : Set M} (hO : IsOpen O) (hKO : e.symm '' (K ×ˢ ({0} : Set ℝ)) ⊆ O) :
    ∃ V : Set (E × ℝ), IsOpen V ∧ K ×ˢ ({0} : Set ℝ) ⊆ V ∧ V ⊆ W ∧
      ∃ Φ : Diffeomorph I I M M ∞, (∀ z ∈ V, Φ (e.symm z) = e.symm (F z)) ∧
        (∀ x ∈ e.source, (e x).2 = 0 → Φ x = x) ∧ (∀ x ∈ Y, Φ x = x) ∧
        ∃ C : Set M, IsCompact C ∧ C ⊆ O ∩ e.source ∧ ∀ x ∉ C, Φ x = x := by
  let Q := e.target ∩ e.symm ⁻¹' O
  have hQ : IsOpen Q := hei.continuousOn.isOpen_inter_preimage e.open_target hO
  have hKQ : K ×ˢ ({0} : Set ℝ) ⊆ Q := fun z hz =>
    ⟨hWt (hUW ⟨hKU hz.1, hz.2⟩), hKO ⟨z, hz, rfl⟩⟩
  let W' := W ∩ (U ×ˢ (univ : Set ℝ))
  have hW' : IsOpen W' := hW.inter (hU.prod isOpen_univ)
  let S := (univ ×ˢ ({0} : Set ℝ)) ∪ {z : E × ℝ | e.symm z ∈ Y}
  have hSfix : EqOn F id (S ∩ W') := by
    rintro z ⟨hzS | hzS, hzW, hzU, -⟩
    · have hz : z = (z.1, 0) := Prod.ext rfl hzS.2
      rw [hz]
      exact hfixed z.1 hzU
    · exact hY z hzW hzS
  have hKS : K ×ˢ ({0} : Set ℝ) ⊆ S ∩ W' := fun z hz =>
    ⟨Or.inl ⟨mem_univ _, hz.2⟩, hUW ⟨hKU hz.1, hz.2⟩, hKU hz.1, mem_univ _⟩
  have hinj : ∀ z ∈ K ×ˢ ({0} : Set ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
      Injective ((1 - t) • ContinuousLinearMap.id ℝ (E × ℝ) + t • fderiv ℝ F z) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩ t ht
    have hy0 : y = 0 := hy
    subst hy0
    have hd : DifferentiableAt ℝ F (x, 0) :=
      (hF.contDiffAt (hW.mem_nhds (hUW ⟨hKU hx, rfl⟩))).differentiableAt (by simp)
    have htan := fderiv_apply_zeroSection hU (hKU hx) hfixed hd
    exact LinearMap.injective_convex_combination_of_eqOn_ker_id
      (fderiv ℝ F (x, 0)).toLinearMap (LinearMap.snd ℝ E ℝ) (n := (0, 1)) rfl
      (fun v hv => by
        change fderiv ℝ F (x, 0) v = v
        change v.2 = 0 at hv
        rw [show v = (v.1, 0) from Prod.ext rfl hv]
        exact htan v.1)
      (hpos x hx) ht
  obtain ⟨V, hV, hKV, hVW, D, hD, hDi, -, htrack, hDS, L, hL, hLQ, hDL⟩ :=
    Diffeomorph.exists_contDiff_compact_isotopy_eqOn_of_injective_convex_combination
      hW' (hF.mono inter_subset_left) hSfix (hK.prod isCompact_singleton) hKS hinj hQ hKQ
  obtain ⟨J, -, -, hJe, hJL, hJLs, hJfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_extension_of_partial_chart_family
      e he hei D hD hDi hL (fun z hz => (hLQ hz).1)
      (fun t z hz => ⟨(hDL t).1 hz, (hDL t).2 hz⟩)
  have hJ (x : M) (hx : x ∈ e.source) : J 1 x = e.symm (D 1 (e x)) := by
    rw [(hJe 1 x).1]
    exact ite_eq_left hx
  refine ⟨V, hV, hKV, fun z hz => (hVW hz).1, J 1, ?_, ?_, ?_,
    e.symm '' L, hJL, ?_, fun x hx => (hJfix 1 x hx).1⟩
  · intro z hz
    have hzt : z ∈ e.target := hWt (hVW hz).1
    rw [hJ _ (e.map_target hzt), e.right_inv hzt, htrack 1 ⟨zero_le_one, le_rfl⟩ z hz]
    simp
  · intro x hx hx0
    rw [hJ x hx, (hDS 1).1 (Or.inl ⟨mem_univ _, hx0⟩)]
    exact e.left_inv hx
  · intro x hxY
    by_cases hx : x ∈ e.source
    · have hmem : e x ∈ S := Or.inr (show e.symm (e x) ∈ Y by rw [e.left_inv hx]; exact hxY)
      rw [hJ x hx, (hDS 1).1 hmem]
      exact e.left_inv hx
    · rw [(hJe 1 x).1]
      exact ite_eq_right hx
  · rintro x ⟨z, hz, rfl⟩
    exact ⟨(hLQ hz).2, hJLs ⟨z, hz, rfl⟩⟩

end Chart

section Signed

private theorem snd_pos_of_fixes_zero {Φ : Torus × ℝ → Torus × ℝ} (hc : Continuous Φ)
    (hinj : Injective Φ) (hfix : ∀ q, Φ (q, 0) = (q, 0)) {L : Set (Torus × ℝ)}
    (hL : IsCompact L) (hid : ∀ x ∉ L, Φ x = x) {y : Torus × ℝ} (hy : 0 < y.2) :
    0 < (Φ y).2 := by
  obtain ⟨R, hR⟩ := (hL.image continuous_snd).bddAbove
  set T := max R y.2 + 1 with hTdef
  have hT : (y.1, T) ∉ L := fun h => by
    have h1 : T ≤ R := hR ⟨_, h, rfl⟩
    linarith [le_max_left R y.2]
  have hTpos : 0 < T := by linarith [le_max_right R y.2]
  have hne : ∀ t ∈ Ioi (0 : ℝ), (Φ (y.1, t)).2 ≠ 0 := by
    intro t ht h0
    have h1 : Φ (y.1, t) = Φ ((Φ (y.1, t)).1, 0) := by
      rw [hfix]
      exact Prod.ext rfl h0
    have h2 := congrArg Prod.snd (hinj h1)
    exact (ne_of_gt (show (0 : ℝ) < t from ht)) h2
  have hcont : ContinuousOn (fun t : ℝ => (Φ (y.1, t)).2) (Ioi 0) :=
    (continuous_snd.comp (hc.comp (continuous_const.prodMk continuous_id))).continuousOn
  by_contra hneg'
  have hneg : (Φ y).2 ≤ 0 := not_lt.mp hneg'
  have hmem : (0 : ℝ) ∈ Icc ((fun t : ℝ => (Φ (y.1, t)).2) y.2)
      ((fun t : ℝ => (Φ (y.1, t)).2) T) := by
    refine ⟨hneg, ?_⟩
    change (0 : ℝ) ≤ (Φ (y.1, T)).2
    rw [hid _ hT]
    exact hTpos.le
  obtain ⟨t, ht, ht0⟩ := isPreconnected_Ioi.intermediate_value
    (show y.2 ∈ Ioi (0 : ℝ) from hy) (show T ∈ Ioi (0 : ℝ) from hTpos) hcont hmem
  exact hne t ht ht0

private theorem snd_nonneg_of_fixes_zero {Φ : Torus × ℝ → Torus × ℝ} (hc : Continuous Φ)
    (hinj : Injective Φ) (hfix : ∀ q, Φ (q, 0) = (q, 0)) {L : Set (Torus × ℝ)}
    (hL : IsCompact L) (hid : ∀ x ∉ L, Φ x = x) {y : Torus × ℝ} (hy : 0 ≤ y.2) :
    0 ≤ (Φ y).2 := by
  rcases hy.lt_or_eq with h | h
  · exact (snd_pos_of_fixes_zero hc hinj hfix hL hid h).le
  · have hy' : y = (y.1, 0) := Prod.ext rfl h.symm
    rw [hy', hfix]

private theorem signedChart_eq (p : Torus) :
    extChartAt signedCollarModel ((p, 0) : Torus × ℝ) =
      (extChartAt torusModel p).prod (PartialEquiv.refl ℝ) := by
  rw [extChartAt_prod, extChartAt_model_space_eq_id]

private def Good (G : Torus × ℝ → Torus × ℝ) (N O : Set (Torus × ℝ)) (A : Set Torus) : Prop :=
  ∃ Ψ : Diffeomorph signedCollarModel signedCollarModel (Torus × ℝ) (Torus × ℝ) ∞,
    ∃ Y : Set (Torus × ℝ), IsOpen Y ∧ A ×ˢ ({0} : Set ℝ) ⊆ Y ∧ Y ⊆ N ∧ EqOn Ψ G Y ∧
      (∀ q, Ψ (q, 0) = (q, 0)) ∧
      ∃ L : Set (Torus × ℝ), IsCompact L ∧ L ⊆ O ∧ ∀ x ∉ L, Ψ x = x

private theorem good_union {G G' : Torus × ℝ → Torus × ℝ} {N N' O : Set (Torus × ℝ)}
    (hN : IsOpen N) (hN0 : ∀ q, (q, (0 : ℝ)) ∈ N)
    (hG : ContMDiffOn signedCollarModel signedCollarModel ∞ G N)
    (hN' : IsOpen N') (hN'0 : ∀ q, (q, (0 : ℝ)) ∈ N')
    (hG' : ContMDiffOn signedCollarModel signedCollarModel ∞ G' N')
    (hG0 : ∀ q, G (q, 0) = (q, 0)) (hG'0 : ∀ q, G' (q, 0) = (q, 0))
    (hnn : ∀ y ∈ N, 0 ≤ y.2 → 0 ≤ (G y).2)
    (hinv : ∀ y ∈ N, 0 ≤ y.2 → G y ∈ N' → G' (G y) = y)
    (hO : IsOpen O) (hO0 : ∀ q, (q, (0 : ℝ)) ∈ O)
    {A : Set Torus} (hA : Good G N O A) (p : Torus) {K : Set Torus} (hK : IsCompact K)
    (hKs : K ⊆ (extChartAt torusModel p).source) :
    Good G N O (A ∪ K) := by
  obtain ⟨Ψ, Y, hY, hAY, hYN, hΨG, hΨ0, L, hL, hLO, hLfix⟩ := hA
  have hΨs0 (q : Torus) : Ψ.symm (q, 0) = (q, 0) := by
    conv_lhs => rw [← hΨ0 q]
    exact Ψ.symm_apply_apply _
  have hΨsL (x : Torus × ℝ) (hx : x ∉ L) : Ψ.symm x = x := by
    conv_lhs => rw [← hLfix x hx]
    exact Ψ.symm_apply_apply _
  have hΨsnn (y : Torus × ℝ) (hy : 0 ≤ y.2) : 0 ≤ (Ψ.symm y).2 :=
    snd_nonneg_of_fixes_zero Ψ.symm.continuous Ψ.symm.injective hΨs0 hL hΨsL hy
  let ec := extChartAt torusModel p
  let e := DifferentialGeometry.Topology.PartialDiffeomorph.extendedChart
    (I := signedCollarModel) ((p, 0) : Torus × ℝ)
  let eo := e.toOpenPartialHomeomorph
  have hchart : eo.toPartialEquiv = ec.prod (PartialEquiv.refl ℝ) := signedChart_eq p
  have he_apply (y : Torus × ℝ) : eo y = (ec y.1, y.2) := by
    change eo.toPartialEquiv y = _
    rw [hchart]
    rfl
  have he_symm (z : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ) :
      eo.symm z = (ec.symm z.1, z.2) := by
    change eo.toPartialEquiv.symm z = _
    rw [hchart]
    rfl
  have he_source : eo.source = ec.source ×ˢ univ := by
    rw [hchart]
    rfl
  have he_target : eo.target = ec.target ×ˢ univ := by
    rw [hchart]
    rfl
  have hKec : K ⊆ ec.source := hKs
  have hsy (q : Torus) (hq : q ∈ ec.source) : eo.symm (ec q, 0) = (q, 0) := by
    rw [he_symm]
    exact Prod.ext (ec.left_inv hq) rfl
  have hty (q : Torus) (hq : q ∈ ec.source) : (ec q, (0 : ℝ)) ∈ eo.target := by
    rw [he_target]
    exact ⟨ec.map_source hq, mem_univ _⟩
  let F : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ →
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ :=
    fun z => eo (Ψ.symm (G (eo.symm z)))
  let W₁ := eo.target ∩ eo.symm ⁻¹' N
  have hW₁ : IsOpen W₁ := eo.continuousOn_symm.isOpen_inter_preimage eo.open_target hN
  have hGW₁ : ContMDiffOn 𝓘(ℝ, _) signedCollarModel ∞ (fun z => G (eo.symm z)) W₁ :=
    hG.comp (e.contMDiffOn_invFun.mono inter_subset_left) (fun z hz => hz.2)
  have hΨGW₁ : ContMDiffOn 𝓘(ℝ, _) signedCollarModel ∞
      (fun z => Ψ.symm (G (eo.symm z))) W₁ :=
    Ψ.symm.contMDiff.comp_contMDiffOn hGW₁
  let W := W₁ ∩ (fun z => Ψ.symm (G (eo.symm z))) ⁻¹' eo.source
  have hW : IsOpen W := hΨGW₁.continuousOn.isOpen_inter_preimage hW₁ eo.open_source
  have hFm : ContMDiffOn 𝓘(ℝ, _) 𝓘(ℝ, _) ∞ F W :=
    e.contMDiffOn_toFun.comp (hΨGW₁.mono inter_subset_left) (fun z hz => hz.2)
  have hF : ContDiffOn ℝ ∞ F W := contMDiffOn_iff_contDiffOn.mp hFm
  let U := {x : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) | (x, (0 : ℝ)) ∈ W}
  have hU : IsOpen U := hW.preimage (continuous_id.prodMk continuous_const)
  have hUW : U ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hy0 : y = 0 := hy
    subst hy0
    exact hx
  have hfixed : ∀ x ∈ U, F (x, 0) = (x, 0) := by
    intro x hx
    have hs : eo.symm (x, 0) = (ec.symm x, 0) := he_symm _
    calc F (x, 0) = eo (Ψ.symm (G (eo.symm (x, 0)))) := rfl
      _ = eo (eo.symm (x, 0)) := by rw [hs, hG0, hΨs0]
      _ = (x, 0) := eo.right_inv hx.1.1
  have hYfix : ∀ z ∈ W, eo.symm z ∈ Y → F z = z := by
    intro z hz hzY
    change eo (Ψ.symm (G (eo.symm z))) = z
    rw [← hΨG hzY, Ψ.symm_apply_apply, eo.right_inv hz.1.1]
  let KE := ec '' K
  have hKE : IsCompact KE := hK.image_of_continuousOn ((continuousOn_extChartAt p).mono hKec)
  have hKU : KE ⊆ U := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨⟨hty q (hKec hq), ?_⟩, ?_⟩
    · change eo.symm (ec q, 0) ∈ N
      rw [hsy q (hKec hq)]
      exact hN0 q
    · change Ψ.symm (G (eo.symm (ec q, 0))) ∈ eo.source
      rw [hsy q (hKec hq), hG0, hΨs0, he_source]
      exact ⟨hKec hq, mem_univ _⟩
  have hpos : ∀ x ∈ KE, 0 < (fderiv ℝ F (x, 0) (0, 1)).2 := by
    rintro _ ⟨q, hq, rfl⟩
    have hxU : ec q ∈ U := hKU ⟨q, hq, rfl⟩
    let F' : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ →
        (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ :=
      fun z => eo (G' (Ψ (eo.symm z)))
    let W₂ := eo.target ∩ eo.symm ⁻¹' (Ψ ⁻¹' N')
    have hW₂ : IsOpen W₂ := eo.continuousOn_symm.isOpen_inter_preimage eo.open_target
      (hN'.preimage Ψ.continuous)
    have hGW₂ : ContMDiffOn 𝓘(ℝ, _) signedCollarModel ∞ (fun z => G' (Ψ (eo.symm z))) W₂ :=
      hG'.comp (Ψ.contMDiff.comp_contMDiffOn (e.contMDiffOn_invFun.mono inter_subset_left))
        (fun z hz => hz.2)
    let W₃ := W₂ ∩ (fun z => G' (Ψ (eo.symm z))) ⁻¹' eo.source
    have hW₃ : IsOpen W₃ := hGW₂.continuousOn.isOpen_inter_preimage hW₂ eo.open_source
    have hF'm : ContMDiffOn 𝓘(ℝ, _) 𝓘(ℝ, _) ∞ F' W₃ :=
      e.contMDiffOn_toFun.comp (hGW₂.mono inter_subset_left) (fun z hz => hz.2)
    have hxW₃ : (ec q, (0 : ℝ)) ∈ W₃ := by
      refine ⟨⟨hty q (hKec hq), ?_⟩, ?_⟩
      · change Ψ (eo.symm (ec q, 0)) ∈ N'
        rw [hsy q (hKec hq), hΨ0]
        exact hN'0 q
      · change G' (Ψ (eo.symm (ec q, 0))) ∈ eo.source
        rw [hsy q (hKec hq), hΨ0, hG'0, he_source]
        exact ⟨hKec hq, mem_univ _⟩
    have hdF : DifferentiableAt ℝ F (ec q, 0) :=
      (hF.contDiffAt (hW.mem_nhds hxU)).differentiableAt (by simp)
    have hdF' : DifferentiableAt ℝ F' (ec q, 0) :=
      ((contMDiffOn_iff_contDiffOn.mp hF'm).contDiffAt (hW₃.mem_nhds hxW₃)).differentiableAt
        (by simp)
    let W₄ := W ∩ (fun z => G (eo.symm z)) ⁻¹' N'
    have hW₄ : IsOpen W₄ :=
      (hGW₁.continuousOn.mono inter_subset_left).isOpen_inter_preimage hW hN'
    have hxW₄ : (ec q, (0 : ℝ)) ∈ W₄ := by
      refine ⟨hxU, ?_⟩
      change G (eo.symm (ec q, 0)) ∈ N'
      rw [hsy q (hKec hq), hG0]
      exact hN'0 q
    apply pos_normal_of_leftInverse hU hxU hfixed hdF hdF'
    · filter_upwards [inter_mem_nhdsWithin _ (hW₄.mem_nhds hxW₄)] with z hz
      obtain ⟨hz0, ⟨⟨hzt, hzN⟩, hzs⟩, hzN'⟩ := hz
      have hy0 : 0 ≤ (eo.symm z).2 := by
        rw [he_symm]
        exact hz0
      change eo (G' (Ψ (eo.symm (eo (Ψ.symm (G (eo.symm z))))))) = z
      rw [eo.left_inv hzs, Ψ.apply_symm_apply, hinv _ hzN hy0 hzN', eo.right_inv hzt]
    · filter_upwards [inter_mem_nhdsWithin _ (hW.mem_nhds hxU)] with z hz
      obtain ⟨hz0, ⟨hzt, hzN⟩, hzs⟩ := hz
      have hy0 : 0 ≤ (eo.symm z).2 := by
        rw [he_symm]
        exact hz0
      change 0 ≤ (eo (Ψ.symm (G (eo.symm z)))).2
      rw [he_apply]
      exact hΨsnn _ (hnn _ hzN hy0)
  have hKO : eo.symm '' (KE ×ˢ ({0} : Set ℝ)) ⊆ O := by
    rintro _ ⟨⟨_, s⟩, ⟨⟨q, hq, rfl⟩, hs⟩, rfl⟩
    have hs0 : s = 0 := hs
    subst hs0
    rw [hsy q (hKec hq)]
    exact hO0 q
  obtain ⟨V, hV, hKV, hVW, Φ, hΦtrack, hΦ0, hΦY, C, hC, hCO, hCfix⟩ :=
    exists_chart_straightening eo e.contMDiffOn_toFun e.contMDiffOn_invFun hW
      (fun z hz => hz.1.1) hF hU hUW hfixed hYfix hKE hKU hpos hO hKO
  refine ⟨Φ.trans Ψ, Y ∪ eo.symm '' V, ?_, ?_, ?_, ?_, ?_, L ∪ C, hL.union hC,
    union_subset hLO (fun x hx => (hCO hx).1), ?_⟩
  · refine hY.union (eo.symm.isOpen_image_of_subset_source hV ?_)
    rw [OpenPartialHomeomorph.symm_source]
    exact fun z hz => (hVW hz).1.1
  · rintro ⟨q, s⟩ ⟨hq | hq, hs⟩
    · exact Or.inl (hAY ⟨hq, hs⟩)
    · have hs0 : s = 0 := hs
      subst hs0
      exact Or.inr ⟨(ec q, 0), hKV ⟨⟨q, hq, rfl⟩, rfl⟩, hsy q (hKec hq)⟩
  · rintro x (hx | ⟨z, hz, rfl⟩)
    · exact hYN hx
    · exact (hVW hz).1.2
  · rintro x (hx | ⟨z, hz, rfl⟩)
    · change Ψ (Φ x) = G x
      rw [hΦY x hx]
      exact hΨG hx
    · change Ψ (Φ (eo.symm z)) = G (eo.symm z)
      rw [hΦtrack z hz]
      change Ψ (eo.symm (eo (Ψ.symm (G (eo.symm z))))) = G (eo.symm z)
      rw [eo.left_inv (hVW hz).2, Ψ.apply_symm_apply]
  · intro q
    change Ψ (Φ (q, 0)) = (q, 0)
    by_cases hq : ((q, 0) : Torus × ℝ) ∈ eo.source
    · rw [hΦ0 _ hq (by rw [he_apply]), hΨ0]
    · rw [hCfix _ (fun h => hq (hCO h).2), hΨ0]
  · intro x hx
    change Ψ (Φ x) = x
    rw [hCfix x (fun h => hx (Or.inr h)), hLfix x (fun h => hx (Or.inl h))]

private theorem exists_signed_straightening {G G' : Torus × ℝ → Torus × ℝ}
    {N N' O : Set (Torus × ℝ)}
    (hN : IsOpen N) (hN0 : ∀ q, (q, (0 : ℝ)) ∈ N)
    (hG : ContMDiffOn signedCollarModel signedCollarModel ∞ G N)
    (hN' : IsOpen N') (hN'0 : ∀ q, (q, (0 : ℝ)) ∈ N')
    (hG' : ContMDiffOn signedCollarModel signedCollarModel ∞ G' N')
    (hG0 : ∀ q, G (q, 0) = (q, 0)) (hG'0 : ∀ q, G' (q, 0) = (q, 0))
    (hnn : ∀ y ∈ N, 0 ≤ y.2 → 0 ≤ (G y).2)
    (hinv : ∀ y ∈ N, 0 ≤ y.2 → G y ∈ N' → G' (G y) = y)
    (hO : IsOpen O) (hO0 : ∀ q, (q, (0 : ℝ)) ∈ O) :
    ∃ Ψ : Diffeomorph signedCollarModel signedCollarModel (Torus × ℝ) (Torus × ℝ) ∞,
      ∃ Y : Set (Torus × ℝ), IsOpen Y ∧ (∀ q, (q, (0 : ℝ)) ∈ Y) ∧ EqOn Ψ G Y ∧
        (∀ q, Ψ (q, 0) = (q, 0)) ∧
        ∃ L : Set (Torus × ℝ), IsCompact L ∧ L ⊆ O ∧ ∀ x ∉ L, Ψ x = x := by
  have hloc (p : Torus) : ∃ K : Set Torus, IsCompact K ∧ p ∈ interior K ∧
      K ⊆ (extChartAt torusModel p).source :=
    exists_compact_subset (isOpen_extChartAt_source p) (mem_extChartAt_source p)
  choose K hKc hKi hKs using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun p => interior (K p))
    (fun _ => isOpen_interior) (fun p _ => mem_iUnion.mpr ⟨p, hKi p⟩)
  have hgood : ∀ s : Finset Torus, Good G N O (⋃ p ∈ s, K p) := by
    classical
    intro s
    induction s using Finset.induction with
    | empty =>
      refine ⟨Diffeomorph.refl _ _ ∞, ∅, isOpen_empty, by simp, empty_subset _,
        fun _ h => h.elim, fun _ => rfl, ∅, isCompact_empty, empty_subset _,
        fun _ _ => rfl⟩
    | @insert p s _ ih =>
      have h := good_union hN hN0 hG hN' hN'0 hG' hG0 hG'0 hnn hinv hO hO0 ih p (hKc p)
        (hKs p)
      rwa [Finset.set_biUnion_insert, union_comm]
  obtain ⟨Ψ, Y, hY, hAY, -, hΨG, hΨ0, L, hL, hLO, hLfix⟩ := hgood t
  refine ⟨Ψ, Y, hY, fun q => hAY ⟨?_, rfl⟩, hΨG, hΨ0, L, hL, hLO, hLfix⟩
  obtain ⟨p, hp, hq⟩ := mem_iUnion₂.mp (ht (mem_univ q))
  exact mem_iUnion₂.mpr ⟨p, hp, interior_subset hq⟩

end Signed

section Half

private def toSigned (x : Torus × EuclideanHalfSpace 1) : Torus × ℝ := (x.1, x.2.1 0)

private def toHalf (y : Torus × ℝ) : Torus × EuclideanHalfSpace 1 :=
  (y.1, halfSpaceOneLift y.2)

private theorem halfSpaceOneLift_coordinate (s : EuclideanHalfSpace 1) :
    halfSpaceOneLift (s.1 0) = s := by
  apply Subtype.ext
  apply (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).injective
  change max (s.1 0) 0 = s.1 0
  exact max_eq_left s.2

private theorem halfZero_coord : halfZero.1 0 = 0 := rfl

private theorem halfZero_eq_lift : halfZero = halfSpaceOneLift 0 := by
  conv_lhs => rw [← halfSpaceOneLift_coordinate halfZero, halfZero_coord]

private theorem halfZero_eq_zero : halfZero = 0 := by
  rw [halfZero_eq_lift, ← halfSpaceOneLift_coordinate (0 : EuclideanHalfSpace 1)]
  congr 1

private theorem toHalf_toSigned (x : Torus × EuclideanHalfSpace 1) : toHalf (toSigned x) = x :=
  Prod.ext rfl (halfSpaceOneLift_coordinate x.2)

private theorem toSigned_toHalf {y : Torus × ℝ} (hy : 0 ≤ y.2) : toSigned (toHalf y) = y :=
  Prod.ext rfl (max_eq_left hy)

private theorem toSigned_injective : Injective toSigned := fun a b hab => by
  rw [← toHalf_toSigned a, hab, toHalf_toSigned]

private theorem toSigned_nonneg (x : Torus × EuclideanHalfSpace 1) : 0 ≤ (toSigned x).2 :=
  x.2.2

private theorem toHalf_zero (q : Torus) : toHalf (q, 0) = (q, halfZero) :=
  Prod.ext rfl halfZero_eq_lift.symm

private theorem toSigned_zero (q : Torus) : toSigned (q, halfZero) = (q, 0) :=
  Prod.ext rfl halfZero_coord

private theorem contMDiff_toSigned : ContMDiff halfCollarModel signedCollarModel ∞ toSigned :=
  contMDiff_fst.prodMk (contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd)

private theorem contMDiffOn_toHalf :
    ContMDiffOn signedCollarModel halfCollarModel ∞ toHalf {y | 0 ≤ y.2} :=
  contMDiffOn_fst.prodMk (contMDiffOn_halfSpaceOneLift.comp contMDiffOn_snd (fun _ hy => hy))

private theorem continuous_halfSpaceOneLift : Continuous halfSpaceOneLift :=
  (𝓡∂ 1).continuous_symm.comp (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.continuous

private theorem exists_half_diffeomorph
    (Ψ : Diffeomorph signedCollarModel signedCollarModel (Torus × ℝ) (Torus × ℝ) ∞)
    (h₁ : ∀ y : Torus × ℝ, 0 ≤ y.2 → 0 ≤ (Ψ y).2)
    (h₂ : ∀ y : Torus × ℝ, 0 ≤ y.2 → 0 ≤ (Ψ.symm y).2) :
    ∃ h : Diffeomorph halfCollarModel halfCollarModel (Torus × EuclideanHalfSpace 1)
      (Torus × EuclideanHalfSpace 1) ∞, ∀ x, toSigned (h x) = Ψ (toSigned x) := by
  let eqv : (Torus × EuclideanHalfSpace 1) ≃ (Torus × EuclideanHalfSpace 1) :=
    { toFun := fun x => toHalf (Ψ (toSigned x))
      invFun := fun x => toHalf (Ψ.symm (toSigned x))
      left_inv := fun x => (congrArg toHalf ((congrArg Ψ.symm
        (toSigned_toHalf (h₁ _ (toSigned_nonneg x)))).trans (Ψ.symm_apply_apply _))).trans
          (toHalf_toSigned x)
      right_inv := fun x => (congrArg toHalf ((congrArg Ψ
        (toSigned_toHalf (h₂ _ (toSigned_nonneg x)))).trans (Ψ.apply_symm_apply _))).trans
          (toHalf_toSigned x) }
  refine ⟨{ toEquiv := eqv
            contMDiff_toFun := contMDiffOn_toHalf.comp_contMDiff
              (Ψ.contMDiff.comp contMDiff_toSigned) (fun x => h₁ _ (toSigned_nonneg x))
            contMDiff_invFun := contMDiffOn_toHalf.comp_contMDiff
              (Ψ.symm.contMDiff.comp contMDiff_toSigned) (fun x => h₂ _ (toSigned_nonneg x)) },
    fun x => toSigned_toHalf (h₁ _ (toSigned_nonneg x))⟩

private theorem exists_signed_extension (f : Torus × EuclideanHalfSpace 1 → Torus × ℝ)
    {Wf : Set (Torus × EuclideanHalfSpace 1)} (hWf : IsOpen Wf) (h0 : ∀ q, (q, halfZero) ∈ Wf)
    (hf : ContMDiffOn halfCollarModel signedCollarModel ∞ f Wf) :
    ∃ G : Torus × ℝ → Torus × ℝ, ∃ N : Set (Torus × ℝ), IsOpen N ∧
      (∀ q, (q, (0 : ℝ)) ∈ N) ∧ ContMDiffOn signedCollarModel signedCollarModel ∞ G N ∧
      ∀ y ∈ N, 0 ≤ y.2 → toHalf y ∈ Wf ∧ G y = f (toHalf y) := by
  obtain ⟨w, hw, hwW⟩ :=
    DifferentialGeometry.Topology.Collar.exists_pos_forall_mem_of_compact_zeroSection hWf
      (fun q => by rw [← halfZero_eq_zero]; exact h0 q)
  set r := w / 2 with hr
  have hr0 : 0 < r := half_pos hw
  have hrw : r < w := half_lt_self hw
  have hlift (t : ℝ) (ht : t < w) (q : Torus) : (q, halfSpaceOneLift t) ∈ Wf :=
    hwW q _ (show max t 0 < w from max_lt ht hw)
  let c : Torus × ℝ → Torus × EuclideanHalfSpace 1 :=
    fun y => (y.1, halfSpaceOneLift (min y.2 r))
  have hcW (y : Torus × ℝ) : c y ∈ Wf := hlift _ ((min_le_right _ _).trans_lt hrw) y.1
  have hc : Continuous c :=
    continuous_fst.prodMk (continuous_halfSpaceOneLift.comp (continuous_snd.min continuous_const))
  let f₀ : Torus × ℝ → Torus × ℝ := fun y => f (c y)
  have hf₀ : Continuous f₀ := hf.continuousOn.comp_continuous hc hcW
  have hf₀eq (y : Torus × ℝ) (hy : y.2 ≤ r) : f₀ y = f (toHalf y) := by
    change f (y.1, halfSpaceOneLift (min y.2 r)) = f (y.1, halfSpaceOneLift y.2)
    rw [min_eq_left hy]
  let Hs : Set (Torus × ℝ) := {y | 0 ≤ y.2} ∩ {y | y.2 < w}
  have hsm : ContMDiffOn signedCollarModel signedCollarModel ∞ (fun y => f (toHalf y)) Hs :=
    hf.comp (contMDiffOn_toHalf.mono inter_subset_left) (fun y hy => hlift _ hy.2 y.1)
  let K : Set (Torus × ℝ) := univ ×ˢ Icc (0 : ℝ) r
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  have hloc : ∀ x ∈ K, ∃ U : Torus × ℝ → Torus × ℝ, ∃ V : Set (Torus × ℝ), IsOpen V ∧
      x ∈ V ∧ ContMDiffOn signedCollarModel signedCollarModel ∞ U V ∧ EqOn U f₀ (K ∩ V) := by
    intro x hx
    rcases hx.2.1.lt_or_eq with hpos | hzero
    · refine ⟨fun y => f (toHalf y), {y | 0 < y.2 ∧ y.2 < w}, ?_, ⟨hpos, hx.2.2.trans_lt hrw⟩,
        hsm.mono (fun y hy => ⟨hy.1.le, hy.2⟩), ?_⟩
      · exact (isOpen_lt continuous_const continuous_snd).inter
          (isOpen_lt continuous_snd continuous_const)
      · intro y hy
        exact (hf₀eq y hy.1.2.2).symm
    · have hU : IsOpen (univ ×ˢ Iio r : Set (Torus × ℝ)) := isOpen_univ.prod isOpen_Iio
      have hfU : ContMDiffOn (torusModel.prod 𝓘(ℝ)) signedCollarModel ∞ f₀
          ((univ ×ˢ Iio r) ∩ (univ ×ˢ Ici (0 : ℝ))) :=
        (hsm.mono (fun y hy => ⟨hy.2.2, hy.1.2.trans hrw⟩)).congr
          (fun y hy => hf₀eq y (le_of_lt hy.1.2))
      obtain ⟨V, hV, hxV, -, g, hg, hgeq⟩ :=
        exists_contMDiffOn_extension_across_product_boundary hU (p := x.1)
          ⟨mem_univ _, hr0⟩ hfU
      have hx' : x = (x.1, 0) := Prod.ext rfl hzero.symm
      refine ⟨g, V, hV, by rw [hx']; exact hxV, hg, fun y hy => hgeq ⟨hy.2, mem_univ _, hy.1.2.1⟩⟩
  obtain ⟨G, -, hGK, N₀, hN₀, hKN₀, hG⟩ :=
    exists_contMDiffOn_eqOn_of_locally_extendable (J := signedCollarModel)
      (I := signedCollarModel) (n := ⊤) hf₀ hK hloc
  refine ⟨G, N₀ ∩ {y | y.2 < r}, hN₀.inter (isOpen_lt continuous_snd continuous_const),
    fun q => ⟨hKN₀ ⟨mem_univ _, le_rfl, hr0.le⟩, hr0⟩, hG.mono inter_subset_left, ?_⟩
  intro y hy hy0
  refine ⟨hlift _ (hy.2.trans hrw) y.1, ?_⟩
  rw [hGK ⟨mem_univ _, hy0, hy.2.le⟩, hf₀eq y hy.2.le]

end Half

theorem exists_torusCollar_straightening {C : CompactCarrier.{u}}
    (c₀ c₁ : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hsrc : ∀ p, (p, halfZero) ∈ c₀.source ∩ c₁.source)
    (h₀ : ∀ p, c₀ (p, halfZero) = c₁ (p, halfZero))
    (hb : ∀ p, C.model.IsBoundaryPoint (c₀ (p, halfZero)))
    {O : Set C.Carrier} (hO : IsOpen O) (hK : range (fun p => c₀ (p, halfZero)) ⊆ O) :
    ∃ δ > 0, ∃ Φ : C.Carrier ≃ₘ⟮C.model, C.model⟯ C.Carrier,
      (∀ p t, t.1 0 < δ → Φ (c₀ (p, t)) = c₁ (p, t)) ∧ EqOn Φ id Oᶜ := by
  refine (fun _ => ?_) hb
  let g := c₁.trans c₀.symm
  have hg_src (q : Torus) : (q, halfZero) ∈ g.source := by
    rw [PartialDiffeomorph.trans_source]
    refine ⟨(hsrc q).2, ?_⟩
    change c₁ (q, halfZero) ∈ c₀.target
    rw [← h₀ q]
    exact c₀.toPartialEquiv.map_source (hsrc q).1
  have hg0 (q : Torus) : g (q, halfZero) = (q, halfZero) := by
    change c₀.symm (c₁ (q, halfZero)) = (q, halfZero)
    rw [← h₀ q]
    exact c₀.symm_apply_apply (hsrc q).1
  have hgs_src (q : Torus) : (q, halfZero) ∈ g.symm.source := by
    rw [PartialDiffeomorph.symm_source, ← hg0 q]
    exact g.toPartialEquiv.map_source (hg_src q)
  have hgs0 (q : Torus) : g.symm (q, halfZero) = (q, halfZero) := by
    conv_lhs => rw [← hg0 q]
    exact g.symm_apply_apply (hg_src q)
  obtain ⟨G, N, hN, hN0, hG, hGeq⟩ := exists_signed_extension (fun x => toSigned (g x))
    g.open_source hg_src (contMDiff_toSigned.comp_contMDiffOn g.contMDiffOn)
  obtain ⟨G', N', hN', hN'0, hG', hG'eq⟩ := exists_signed_extension
    (fun x => toSigned (g.symm x)) g.symm.open_source hgs_src
    (contMDiff_toSigned.comp_contMDiffOn g.symm.contMDiffOn)
  have hG0 (q : Torus) : G (q, 0) = (q, 0) := by
    have h1 := (hGeq _ (hN0 q) le_rfl).2
    simp only [toHalf_zero, hg0, toSigned_zero] at h1
    exact h1
  have hG'0 (q : Torus) : G' (q, 0) = (q, 0) := by
    have h1 := (hG'eq _ (hN'0 q) le_rfl).2
    simp only [toHalf_zero, hgs0, toSigned_zero] at h1
    exact h1
  have hnn : ∀ y ∈ N, 0 ≤ y.2 → 0 ≤ (G y).2 := by
    intro y hy hy0
    rw [(hGeq y hy hy0).2]
    exact toSigned_nonneg _
  have hinv : ∀ y ∈ N, 0 ≤ y.2 → G y ∈ N' → G' (G y) = y := by
    intro y hy hy0 hy'
    have h1 := hGeq y hy hy0
    have h2 := (hG'eq _ hy' (hnn y hy hy0)).2
    rw [h2, h1.2, toHalf_toSigned, g.symm_apply_apply h1.1, toSigned_toHalf hy0]
  let OX := c₀.source ∩ c₀ ⁻¹' O
  have hOX : IsOpen OX := c₀.contMDiffOn.continuousOn.isOpen_inter_preimage c₀.open_source hO
  obtain ⟨ε, hε, hεO⟩ :=
    DifferentialGeometry.Topology.Collar.exists_pos_forall_mem_of_compact_zeroSection hOX
      (fun q => by rw [← halfZero_eq_zero]; exact ⟨(hsrc q).1, hK ⟨q, rfl⟩⟩)
  obtain ⟨Ψ, Y, hY, hY0, hΨG, hΨ0, L, hL, hLO, hLfix⟩ :=
    exists_signed_straightening hN hN0 hG hN' hN'0 hG' hG0 hG'0 hnn hinv
      (isOpen_lt continuous_snd continuous_const : IsOpen {y : Torus × ℝ | y.2 < ε / 2})
      (fun q => show ((q, (0 : ℝ)) : Torus × ℝ).2 < ε / 2 from half_pos hε)
  have hΨs0 (q : Torus) : Ψ.symm (q, 0) = (q, 0) := by
    conv_lhs => rw [← hΨ0 q]
    exact Ψ.symm_apply_apply _
  have hΨsL (x : Torus × ℝ) (hx : x ∉ L) : Ψ.symm x = x := by
    conv_lhs => rw [← hLfix x hx]
    exact Ψ.symm_apply_apply _
  obtain ⟨h, hh⟩ := exists_half_diffeomorph Ψ
    (fun y hy => snd_nonneg_of_fixes_zero Ψ.continuous Ψ.injective hΨ0 hL hLfix hy)
    (fun y hy => snd_nonneg_of_fixes_zero Ψ.symm.continuous Ψ.symm.injective hΨs0 hL hΨsL hy)
  let KX : Set (Torus × EuclideanHalfSpace 1) := univ ×ˢ (halfSpaceOneLift '' Icc 0 (ε / 2))
  have hKX : IsCompact KX := isCompact_univ.prod (isCompact_Icc.image continuous_halfSpaceOneLift)
  have hKXmem (x : Torus × EuclideanHalfSpace 1) (hx : x.2.1 0 ≤ ε / 2) : x ∈ KX :=
    ⟨mem_univ _, x.2.1 0, ⟨x.2.2, hx⟩, halfSpaceOneLift_coordinate x.2⟩
  have hKXle (x : Torus × EuclideanHalfSpace 1) (hx : x ∈ KX) : x.2.1 0 ≤ ε / 2 := by
    obtain ⟨-, t, ht, hxt⟩ := hx
    rw [← hxt]
    exact max_le ht.2 (half_pos hε).le
  have hKXs : KX ⊆ c₀.source := fun x hx =>
    (hεO x.1 x.2 ((hKXle x hx).trans_lt (half_lt_self hε))).1
  have hhfix (z : Torus × EuclideanHalfSpace 1) (hz : z ∉ KX) : h z = z := by
    have hz' : ε / 2 < z.2.1 0 := not_le.mp (fun hle => hz (hKXmem z hle))
    have hzL : toSigned z ∉ L := fun hmem => absurd (hLO hmem) (not_lt.mpr hz'.le)
    exact toSigned_injective (by rw [hh, hLfix _ hzL])
  obtain ⟨Fam, -, -, hFe, -, -, hFfix⟩ := PartialDiffeomorph.exists_diffeomorph_family_extension
    (P := ℝ) (IP := 𝓘(ℝ, ℝ)) c₀ (fun _ => h) (h.contMDiff.comp contMDiff_snd)
    (h.symm.contMDiff.comp contMDiff_snd) hKX hKXs (fun _ z hz => hhfix z hz)
  let WX := c₀.source ∩ toSigned ⁻¹' (Y ∩ N)
  have hWX : IsOpen WX :=
    c₀.open_source.inter ((hY.inter hN).preimage contMDiff_toSigned.continuous)
  obtain ⟨δ, hδ, hδW⟩ :=
    DifferentialGeometry.Topology.Collar.exists_pos_forall_mem_of_compact_zeroSection hWX
      (fun q => by
        rw [← halfZero_eq_zero]
        refine ⟨(hsrc q).1, ?_⟩
        change toSigned (q, halfZero) ∈ Y ∩ N
        rw [toSigned_zero]
        exact ⟨hY0 q, hN0 q⟩)
  refine ⟨δ, hδ, Fam 0, ?_, ?_⟩
  · intro p t ht
    obtain ⟨hx0, hxY, hxN⟩ := hδW p t ht
    have h1 := hGeq _ hxN (toSigned_nonneg (p, t))
    simp only [toHalf_toSigned] at h1
    have hhx : h (p, t) = g (p, t) := toSigned_injective (by rw [hh, hΨG hxY, h1.2])
    have hgx := h1.1
    rw [PartialDiffeomorph.trans_source] at hgx
    have hext := (hFe 0 (c₀ (p, t))).1
    calc Fam 0 (c₀ (p, t)) = c₀ (h (c₀.symm (c₀ (p, t)))) :=
          hext.trans (ite_eq_left (c₀.toPartialEquiv.map_source hx0))
      _ = c₁ (p, t) := by
          rw [c₀.symm_apply_apply hx0, hhx]
          exact c₀.apply_symm_apply hgx.2
  · intro x hx
    refine (hFfix 0 x (fun hmem => hx ?_)).1
    obtain ⟨z, hz, rfl⟩ := hmem
    exact (hεO z.1 z.2 ((hKXle z hz).trans_lt (half_lt_self hε))).2

end GC.Seifert

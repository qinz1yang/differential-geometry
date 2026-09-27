import DifferentialGeometry.Topology.Embedding.RelativeAmbientIsotopy
import DifferentialGeometry.Topology.Diffeomorph.SaddleFiberFlow
import DifferentialGeometry.Topology.Diffeomorph.QuadraticFiberFlow
import Mathlib.Topology.MetricSpace.Thickening

open Set Metric Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Analysis.ODE

namespace Manifold

private theorem isOpen_saddle_curve_domain (a : ℝ) :
    IsOpen {p : ℝ × (ℝ × ℝ) | 1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
      0 < 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * (p.1 - a) / p.2.2 ^ 2} := by
  let D : Set (ℝ × (ℝ × ℝ)) := {p | 1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0}
  let q : ℝ × (ℝ × ℝ) → ℝ :=
    fun p => 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * (p.1 - a) / p.2.2 ^ 2
  have hD : IsOpen D :=
    (isOpen_ne_fun (continuous_const.sub (continuous_snd.fst.pow 2)) continuous_const).inter
      (isOpen_ne_fun continuous_snd.snd continuous_const)
  have hq : ContinuousOn q D := by
    apply continuousOn_const.add
    apply ContinuousOn.div
    · exact ((continuousOn_const.mul ((continuousOn_const.sub
        (continuousOn_snd.fst.pow 2)).inv₀ (fun _ hp => hp.1))).mul
        (continuousOn_fst.sub continuousOn_const))
    · exact continuousOn_snd.snd.pow 2
    · exact fun _ hp => pow_ne_zero 2 hp.2
  have h : IsOpen (D ∩ q ⁻¹' Ioi 0) := hq.isOpen_inter_preimage hD isOpen_Ioi
  convert h using 1
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioi, D, q, and_assoc]

private theorem continuousOn_saddle_curve_shift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] E) (a : ℝ) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => (p.1, B (saddleBandCurve p.2 (p.1 - a))))
      {p | 1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
        0 < 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * (p.1 - a) / p.2.2 ^ 2} := by
  have hshift : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (p.1 - a, p.2)) :=
    (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
  have hcurve := B.contDiffOn_comp_saddleBandCurve.comp hshift.contDiffOn (fun _ hp => hp)
  exact continuousOn_fst.prodMk hcurve.continuousOn

private theorem exists_saddle_curve_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : (ℝ × ℝ) ≃ₘ[ℝ] E) {a : ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hreg : ∀ z ∈ K, (1 - z.1 ^ 2) * z.2 ≠ 0)
    {V : Set (ℝ × E)} (hV : IsOpen V) (hKV : ∀ z ∈ K, (a, B z) ∈ V) :
    ∃ W : Set (ℝ × ℝ), IsOpen W ∧ K ⊆ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ t ∈ Icc (a - δ) (a + δ), ∀ z ∈ W,
        (1 - z.1 ^ 2 ≠ 0 ∧ z.2 ≠ 0 ∧
          0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (t - a) / z.2 ^ 2) ∧
          (t, B (saddleBandCurve z (t - a))) ∈ V := by
  let D' : Set (ℝ × (ℝ × ℝ)) :=
    {p | 1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
      0 < 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * (p.1 - a) / p.2.2 ^ 2}
  have hD' : IsOpen D' := isOpen_saddle_curve_domain a
  let T : ℝ × (ℝ × ℝ) → ℝ × E := fun p => (p.1, B (saddleBandCurve p.2 (p.1 - a)))
  have hT : ContinuousOn T D' := continuousOn_saddle_curve_shift B a
  have hN : IsOpen (D' ∩ T ⁻¹' V) := hT.isOpen_inter_preimage hD' hV
  have hbase : {a} ×ˢ K ⊆ D' ∩ T ⁻¹' V := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have ht' : t = a := ht
    subst t
    refine ⟨⟨(mul_ne_zero_iff.mp (hreg z hz)).1,
      (mul_ne_zero_iff.mp (hreg z hz)).2, ?_⟩, ?_⟩
    · simp only [sub_self, mul_zero, zero_div, add_zero]; norm_num
    · simpa only [mem_preimage, T, sub_self, saddleBandCurve_zero] using hKV z hz
  obtain ⟨O, W, hO, hW, haO, hKW, hOW⟩ :=
    generalized_tube_lemma isCompact_singleton hK hN hbase
  obtain ⟨η, hη, hηO⟩ := Metric.isOpen_iff.mp hO a (haO (mem_singleton a))
  refine ⟨W, hW, hKW, η / 2, half_pos hη, ?_⟩
  intro t ht z hz
  have htO : t ∈ O := hηO (by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2])
  exact hOW (a := (t, z)) ⟨htO, hz⟩

theorem exists_contDiff_compact_ambient_isotopy_eqOn_saddle_quadratic_models
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {e : ℝ × M → V} {a b c δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (hpos : ∀ t ∈ Icc (b - δ) (b + δ), 0 < (t - c) / (b - c))
    (he : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e (Icc a b ×ˢ univ))
    (hemb : ∀ t ∈ Icc a b, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    (B : (ℝ × ℝ) ≃ₘ[ℝ] V) (A : (V × ℝ) ≃ₘ[ℝ] (V × ℝ))
    (hA : ∀ z, (A z).2 = z.2)
    {U₀ U₁ : Set (ℝ × V)} (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (hdisj : Disjoint U₀ U₁)
    (hD : ∀ z ∈ U₀, (1 - (B.symm z.2).1 ^ 2) * (B.symm z.2).2 ≠ 0)
    (hUc : ∀ z ∈ U₁, z.1 ≠ c)
    (hv₀ : ∀ t ∈ Icc a b, ∀ x, (t, e (t, x)) ∈ U₀ →
      HasDerivWithinAt (fun s => e (s, x)) (B.saddleFiberVectorField (e (t, x))) (Icc a b) t)
    (hv₁ : ∀ t ∈ Icc a b, ∀ x, (t, e (t, x)) ∈ U₁ →
      HasDerivWithinAt (fun s => e (s, x))
        (A.quadraticFiberVectorField c (t, e (t, x))) (Icc a b) t)
    {K₀ : Set (ℝ × ℝ)} (hK₀ : IsCompact K₀)
    (hK₀U : ∀ z ∈ K₀, (a, B z) ∈ U₀)
    {K₁ : Set V} (hK₁ : IsCompact K₁)
    (hK₁U : ∀ t ∈ Icc (b - δ) (b + δ), ∀ z ∈ K₁,
      (t, (A (quadraticLevelScaling b c z t, t)).1) ∈ U₁) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun z : ℝ × V => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × V => (Φ z.1).symm z.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x)) ∧
      (∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧
        ∀ t ∈ Icc (a - δ₀) (a + δ₀), ∀ z ∈ cthickening ε K₀,
          Φ t (B z) = B (saddleBandCurve z (t - a))) ∧
      (∀ t ∈ Icc (b - δ) (b + δ), ∀ z ∈ K₁,
        Φ t ((Φ b).symm (A (z, b)).1) =
          (A (quadraticLevelScaling b c z t, t)).1) ∧
      ∃ S : Set V, IsCompact S ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  let L : V ≃L[ℝ] (ℝ × ℝ) :=
    (B.symm.isLocalDiffeomorph 0).mfderivToContinuousLinearEquiv (by simp)
  let : FiniteDimensional ℝ V := FiniteDimensional.of_injective L.toLinearMap L.injective
  have hKreg (z : ℝ × ℝ) (hz : z ∈ K₀) : (1 - z.1 ^ 2) * z.2 ≠ 0 := by
    simpa only [B.symm_apply_apply] using hD (a, B z) (hK₀U z hz)
  obtain ⟨N, hN, hKN, δ₀, hδ₀, hmodelN⟩ :=
    exists_saddle_curve_neighborhood B hK₀ hKreg hU₀ hK₀U
  obtain ⟨ε, hε, hεN⟩ := hK₀.exists_cthickening_subset_open hN hKN
  have hmodel₀ (t : ℝ) (ht : t ∈ Icc (a - δ₀) (a + δ₀))
      (z : ℝ × ℝ) (hz : z ∈ cthickening ε K₀) := hmodelN t ht z (hεN hz)
  let K := cthickening ε K₀
  let T₀ : ℝ × (ℝ × ℝ) → ℝ × V :=
    fun z => (z.1, B (saddleBandCurve z.2 (z.1 - a)))
  let T₁ : ℝ × V → ℝ × V :=
    fun z => (z.1, (A (quadraticLevelScaling b c z.2 z.1, z.1)).1)
  have hT₀ : ContDiffOn ℝ ∞ T₀ (Icc (a - δ₀) (a + δ₀) ×ˢ K) :=
    contDiffOn_fst.prodMk ((B.contDiffOn_comp_saddleBandCurve).comp
      ((contDiffOn_fst.sub contDiffOn_const).prodMk contDiffOn_snd)
      (fun z hz => (hmodel₀ z.1 hz.1 z.2 hz.2).1))
  have hT₁ : Continuous T₁ := continuous_fst.prodMk
    (A.continuous_fst_comp_quadraticLevelScaling b c)
  let C : Bool → Set (ℝ × V) := fun i =>
    if i then T₁ '' (Icc (b - δ) (b + δ) ×ˢ K₁)
    else T₀ '' (Icc (a - δ₀) (a + δ₀) ×ˢ K)
  let O : Bool → Set (ℝ × V) := fun i => if i then U₁ else U₀
  let W : Bool → ℝ × V → V :=
    fun i => if i then A.quadraticFiberVectorField c else fun z => B.saddleFiberVectorField z.2
  let P : Bool → Type _ := fun i => if i then K₁ else ULift K
  let γ : (i : Bool) → P i → ℝ → V := fun i =>
    match i with
    | false => fun z t => B (saddleBandCurve z.down.val (t - a))
    | true => fun z t => (A (quadraticLevelScaling b c z.val t, t)).1
  let l : (i : Bool) → P i → ℝ := fun i _ => if i then b - δ else a - δ₀
  let u : (i : Bool) → P i → ℝ := fun i _ => if i then b + δ else a + δ₀
  have hV (i : Bool) : IsOpen (O i) := by cases i <;> assumption
  have hcompC : IsCompact (⋃ i, C i) := isCompact_iUnion fun i => by
    cases i
    · exact (isCompact_Icc.prod hK₀.cthickening).image_of_continuousOn hT₀.continuousOn
    · exact (isCompact_Icc.prod hK₁).image hT₁
  have hCV (i : Bool) : C i ⊆ O i ∩ (univ ×ˢ univ) := by
    cases i
    · rintro _ ⟨⟨t, z⟩, ⟨ht, hz⟩, rfl⟩
      exact ⟨(hmodel₀ t ht z hz).2, mem_univ _, mem_univ _⟩
    · rintro _ ⟨⟨t, z⟩, ⟨ht, hz⟩, rfl⟩
      exact ⟨hK₁U t ht z hz, mem_univ _, mem_univ _⟩
  have hW (i : Bool) : ContDiffOn ℝ ∞ (W i) (O i) := by
    cases i
    · exact B.contDiffOn_saddleFiberVectorField.comp contDiffOn_snd (fun _ hz => hD _ hz)
    · exact (A.contDiffOn_quadraticFiberVectorField c).mono hUc
  have hWe (i : Bool) (t : ℝ) (ht : t ∈ Icc a b) (x : M)
      (hx : (t, e (t, x)) ∈ O i) :
      HasDerivWithinAt (fun s => e (s, x)) (W i (t, e (t, x))) (Icc a b) t := by
    cases i
    · exact hv₀ t ht x hx
    · exact hv₁ t ht x hx
  have hagree (i j : Bool) : EqOn (W i) (W j) (O i ∩ O j) := by
    cases i <;> cases j
    · exact fun _ _ => rfl
    · exact fun _ hz => (Set.disjoint_left.mp hdisj hz.1 hz.2).elim
    · exact fun _ hz => (Set.disjoint_left.mp hdisj hz.2 hz.1).elim
    · exact fun _ _ => rfl
  have hγ (i : Bool) (z : P i) : ContinuousOn (γ i z) (Icc (l i z) (u i z)) := by
    cases i
    · exact (hT₀.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht => ⟨ht, z.down.property⟩)).snd
    · exact ((A.continuous_fst_comp_quadraticLevelScaling b c).comp
        (continuous_id.prodMk continuous_const)).continuousOn
  have hγ' (i : Bool) (z : P i) (t : ℝ) (ht : t ∈ Ico (l i z) (u i z)) :
      HasDerivWithinAt (γ i z) (W i (t, γ i z t)) (Ici t) t := by
    cases i
    · have hm := (hmodel₀ t ⟨ht.1, ht.2.le⟩ z.down.val z.down.property).1
      have hd := (B.hasDerivAt_comp_saddleBandCurve hm.2.1 hm.2.2).scomp t
        ((hasDerivAt_id t).sub_const a)
      simpa only [γ, W, Bool.false_eq_true, ↓reduceIte, Function.comp_def, id_eq, one_smul]
        using hd.hasDerivWithinAt (s := Ici t)
    · exact (A.hasDerivAt_fst_comp_quadraticLevelScaling hA b c z.val
        (hpos t ⟨ht.1, ht.2.le⟩)).hasDerivWithinAt
  have hγC (i : Bool) (z : P i) (t : ℝ) (ht : t ∈ Icc (l i z) (u i z)) :
      (t, γ i z t) ∈ C i := by
    cases i
    · exact ⟨(t, z.down.val), ⟨ht, z.down.property⟩, rfl⟩
    · exact ⟨(t, z.val), ⟨ht, z.property⟩, rfl⟩
  obtain ⟨Φ, hΦ, hΦinv, hΦa, hΦJe, hΦγ, S, hS, _, hfix⟩ :=
    exists_contDiff_compact_ambient_isotopy_Icc_eqOn_integralCurve_family hab
      he hemb isOpen_univ (subset_univ _) hV hcompC hCV W hW hWe hagree
      hγ hγ' hγC
  have hΦJ (t : ℝ) (ht : t ∈ Icc a b) (x : M) : Φ t (e (a, x)) = e (t, x) :=
    (hΦJe t ht x).1
  have hsupport : ∃ S : Set (V), IsCompact S ∧ ∀ t : ℝ,
      EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := ⟨S, hS, hfix⟩
  have hΦsaddle (t : ℝ) (ht : t ∈ Icc (a - δ₀) (a + δ₀))
      (z : ℝ × ℝ) (hz : z ∈ cthickening ε K₀) :
      Φ t (B z) = B (saddleBandCurve z (t - a)) := by
    have haδ : a ∈ Icc (a - δ₀) (a + δ₀) := ⟨by linarith, by linarith⟩
    have hbase := hΦγ false ⟨⟨z, hz⟩⟩ a haδ
    have htrack := hΦγ false ⟨⟨z, hz⟩⟩ t ht
    have hbase' : (Φ (a - δ₀)).symm (γ false ⟨⟨z, hz⟩⟩ (a - δ₀)) = B z := by
      simpa only [γ, hΦa, Diffeomorph.coe_refl, id_eq, l, Bool.false_eq_true, ↓reduceIte,
        sub_self, saddleBandCurve_zero] using hbase
    simpa only [l, Bool.false_eq_true, ↓reduceIte, hbase'] using htrack
  have hΦcap (t : ℝ) (ht : t ∈ Icc (b - δ) (b + δ))
      (z : V) (hz : z ∈ K₁) :
      Φ t ((Φ b).symm (A (z, b)).1) =
        (A (quadraticLevelScaling b c z t, t)).1 := by
    have hbδ : b ∈ Icc (b - δ) (b + δ) := ⟨by linarith, by linarith⟩
    have hbase := hΦγ true ⟨z, hz⟩ b hbδ
    have htrack := hΦγ true ⟨z, hz⟩ t ht
    have hbase' : (Φ (b - δ)).symm (γ true ⟨z, hz⟩ (b - δ)) =
        (Φ b).symm (A (z, b)).1 := by
      have hbne : b ≠ c := by
        intro hbc
        have hp := hpos b ⟨by linarith, by linarith⟩
        simp only [hbc, sub_self, div_zero] at hp
        exact (lt_irrefl 0 hp)
      have hbmodel : γ true ⟨z, hz⟩ b = (A (z, b)).1 := by
        simp only [γ, quadraticLevelScaling_self hbne]
      rw [← hbmodel, ← hbase, (Φ b).symm_apply_apply]
      rfl
    simpa only [l, ↓reduceIte, hbase'] using htrack
  exact ⟨Φ, hΦ, hΦinv, hΦa, hΦJ, ⟨ε, δ₀, hε, hδ₀, hΦsaddle⟩, hΦcap, hsupport⟩

end Manifold

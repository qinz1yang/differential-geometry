import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClass
import DifferentialGeometry.Topology.Manifold.RelativeCollarIsotopy
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.IsotopyExtension

/-!
# Torus mapping classes: circle normal forms

Chapter 6, packet K08, lane MC1 of the `TorusMappingClassLinear` programme
(`docs/geometrization/handoffs/20261004-survey-torus-mapping-class.md`, corrected by review 12,
§4.6). Everything is stated for `TDiff` with `torusMatrix φ = 1`.

(1) Set-wise to point-wise (`exists_isotopic_fixed_alpha`). If `φ (z, 1) ∈ α` for all `z`, the
lift shows that `z ↦ (φ (z, 1)).1` is onto, so `Θ (u, v) = ((φ⁻¹ (u, 1)).1, v)` is a torus
diffeomorphism; it preserves the first coordinate fibres and has matrix `1`, hence is isotopic to
the identity by the easy layer of MC0, and `φ.trans Θ` fixes `α` pointwise. A vertical band
`|x| < δ` on which `φ` is the identity is kept.

(2) One chart step (`exists_isotopic_chart_correction`). Given a lift `Φ` of `φ`, a set `S` on
which `Φ = id`, a compact `K ⊆ S` on which `(1 - t) id + t DΦ` is injective for `t ∈ [0, 1]`, and
an open box `Q ⊇ K` on which `torusCover` is injective, the tree lemma
`Diffeomorph.exists_contDiff_compact_isotopy_eqOn_of_injective_convex_combination` gives a
compactly supported isotopy `D` of `ℝ²`, supported in `Q`, equal to the straight line from `id`
to `Φ` near `K` and fixing `S` pointwise for all times; it is transported to the torus through the
partial diffeomorphism `torusCover|Q` (`PartialDiffeomorph.exists_isotopy_extension_of_isCompact`).
The result `ψ = φ ∘ Θ₁⁻¹` is the identity near `torusCover K`, and fixes every `φ`-fixed point all
of whose `Q`-preimages lie in `S`: this is how a later correction keeps the identity
neighbourhood produced by an earlier one (it is put into `S`, with the buffer `|y| < 1/4`
guaranteeing that its preimages in `Q` are the translates already in `S`).

(3) Normal derivative (`exists_lift_of_fixed_alpha`). If `φ` fixes `α` pointwise, the lift with
`Φ 0 = 0` fixes `ℝ × 0` pointwise, commutes with `ℤ²`, and `∂_y Φ₂ > 0` on `ℝ × 0`: the sign is
constant, and a negative sign would give, by the intermediate value theorem between `0⁺` and
`Φ (0, 1) = (0, 1)`, a second preimage of a point of `ℝ × 0`. Hence the convex combinations of
`id` and `DΦ` are injective along `ℝ × 0`.

(4) Identity near `α` (`exists_isotopic_eqOn_nhds_alpha_of_fixed`): two chart steps, centred at
`0` (box `(-1/2, 1/2)²`, `K = [-3/10, 3/10] × 0`) and at `1/2` (box `(0, 1) × (-1/2, 1/2)`,
`K = [1/5, 4/5] × 0`), the second keeping a box `B₁ = (-3/10 - ε, 3/10 + ε) × (-ε, ε)`,
`ε ≤ 1/4`, produced by the first; a vertical band is kept throughout. With (1) this gives the
frozen `exists_isotopic_eqOn_nhds_alpha`.

(5) Relative version for `β` (`exists_isotopic_eqOn_nhds_axes_of_beta`): if `φ` is the identity on
an open `U ⊇ α` and maps `β` into `β`, then `φ` is isotopic to a `ψ` that is the identity on an
open `V ⊇ α ∪ β`. A band `|y| < ε` inside `U` is found by compactness; conjugating by the swap
`swapTDiff` turns it into a vertical band and `β` into `α`, and (1) and (4) keep that band fixed
pointwise while making the map the identity near `α`.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

open AnnulusStraightening

namespace IsotopicDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem trans_right (φ : M ≃ₘ⟮I, I⟯ M) {θ θ' : M ≃ₘ⟮I, I⟯ M}
    (h : IsotopicDiffeomorph θ θ') : IsotopicDiffeomorph (φ.trans θ) (φ.trans θ') := by
  obtain ⟨F, hF, hF', h0, h1⟩ := h
  refine ⟨fun t => φ.trans (F t), hF.comp (contMDiff_fst.prodMk (φ.contMDiff.comp contMDiff_snd)),
    φ.symm.contMDiff.comp hF', ?_, ?_⟩ <;> ext x <;> simp [h0, h1]

theorem trans_left {φ φ' : M ≃ₘ⟮I, I⟯ M} (θ : M ≃ₘ⟮I, I⟯ M)
    (h : IsotopicDiffeomorph φ φ') : IsotopicDiffeomorph (φ.trans θ) (φ'.trans θ) := by
  obtain ⟨F, hF, hF', h0, h1⟩ := h
  refine ⟨fun t => (F t).trans θ, θ.contMDiff.comp hF,
    hF'.comp (contMDiff_fst.prodMk (θ.symm.contMDiff.comp contMDiff_snd)), ?_, ?_⟩ <;>
    ext x <;> simp [h0, h1]

theorem inv {φ ψ : M ≃ₘ⟮I, I⟯ M} (h : IsotopicDiffeomorph φ ψ) :
    IsotopicDiffeomorph φ.symm ψ.symm := by
  obtain ⟨F, hF, hF', h0, h1⟩ := h
  exact ⟨fun t => (F t).symm, hF', hF, congrArg Diffeomorph.symm h0,
    congrArg Diffeomorph.symm h1⟩

end IsotopicDiffeomorph

theorem injOn_torusCover_box (a b : ℝ) :
    InjOn torusCover (Ioo a (a + 1) ×ˢ Ioo b (b + 1)) := by
  intro p hp q hq hpq
  obtain ⟨m, n, hmn⟩ := torusCover_eq_torusCover_iff.mp hpq
  have hm : m = 0 := by
    have h1 : p.1 = q.1 + m := congrArg Prod.fst hmn
    have h2 : (m : ℝ) < 1 := by linarith [hp.1.1, hp.1.2, hq.1.1, hq.1.2]
    have h3 : (-1 : ℝ) < m := by linarith [hp.1.1, hp.1.2, hq.1.1, hq.1.2]
    have h4 : m < 1 := by exact_mod_cast h2
    have h5 : -1 < m := by exact_mod_cast h3
    omega
  have hn : n = 0 := by
    have h1 : p.2 = q.2 + n := congrArg Prod.snd hmn
    have h2 : (n : ℝ) < 1 := by linarith [hp.2.1, hp.2.2, hq.2.1, hq.2.2]
    have h3 : (-1 : ℝ) < n := by linarith [hp.2.1, hp.2.2, hq.2.1, hq.2.2]
    have h4 : n < 1 := by exact_mod_cast h2
    have h5 : -1 < n := by exact_mod_cast h3
    omega
  rw [hmn, hm, hn, Int.cast_zero, add_zero, add_zero]

theorem exists_isotopic_chart_correction (φ : TDiff) {Φ : ℝ × ℝ → ℝ × ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hlift : ∀ p, φ (torusCover p) = torusCover (Φ p))
    {S : Set (ℝ × ℝ)} (hS : ∀ p ∈ S, Φ p = p)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKS : K ⊆ S)
    (hinj : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
      Function.Injective ((1 - t) • ContinuousLinearMap.id ℝ (ℝ × ℝ) + t • fderiv ℝ Φ x))
    {Q : Set (ℝ × ℝ)} (hQ : IsOpen Q) (hQinj : InjOn torusCover Q) (hKQ : K ⊆ Q) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧
      (∃ V : Set (ℝ × ℝ), IsOpen V ∧ K ⊆ V ∧ ∀ p ∈ V, ψ (torusCover p) = torusCover p) ∧
      ∀ z, φ z = z → (∀ p ∈ Q, torusCover p = z → p ∈ S) → ψ z = z := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨φ, IsotopicDiffeomorph.refl φ, ⟨∅, isOpen_empty, by rw [hKe], fun p hp => hp.elim⟩,
      fun z hz _ => hz⟩
  obtain ⟨V, hV, hKV, -, D, hD, hDi, hD0, htrack, hDS, L, hL, hLQ, hDL⟩ :=
    Diffeomorph.exists_contDiff_compact_isotopy_eqOn_of_injective_convex_combination
      (F := Φ) (W := univ) isOpen_univ hΦ.contDiffOn (S := S)
      (fun p hp => hS p hp.1) hK (fun p hp => ⟨hKS hp, mem_univ p⟩) hinj hQ hKQ
  obtain ⟨P, hPs, -, hPf⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (isLocalDiffeomorph_torusCover.isLocalDiffeomorphOn Q) hQ (hKne.mono hKQ) hQinj
  have hPapp (p : ℝ × ℝ) : P.symm.symm p = torusCover p := congrFun hPf p
  have hDm : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun z : ℝ × (ℝ × ℝ) => D z.1 z.2) :=
    hD.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  have hDim : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun z : ℝ × (ℝ × ℝ) => (D z.1).symm z.2) :=
    hDi.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  obtain ⟨Θ, hΘ, hΘi, -, hΘf, -, hΘ0, -, -, hΘs⟩ :=
    PartialDiffeomorph.exists_isotopy_extension_of_isCompact P.symm D hDm hDim hL
      (by rw [show P.symm.target = Q from hPs]; exact hLQ)
      (fun t x hx => (hDL t).1 hx)
  have hΘ0' : Θ 0 = torusRefl := hΘ0 0 hD0
  refine ⟨φ.trans (Θ 1).symm, ?_, ⟨V ∩ Q, hV.inter hQ, fun p hp => ⟨hKV hp, hKQ hp⟩, ?_⟩, ?_⟩
  · have h := IsotopicDiffeomorph.trans_right φ (IsotopicDiffeomorph.inv
      (⟨Θ, hΘ, hΘi, hΘ0', rfl⟩ : IsotopicDiffeomorph torusRefl (Θ 1)))
    have he : φ.trans torusRefl.symm = φ := Diffeomorph.ext fun x => rfl
    rwa [he] at h
  · rintro p ⟨hpV, hpQ⟩
    have h1 : Θ 1 (torusCover p) = torusCover (Φ p) := by
      have h := hΘf 1 p (by rw [show P.symm.target = Q from hPs]; exact hpQ)
      rw [hPapp, hPapp, htrack 1 ⟨zero_le_one, le_rfl⟩ p hpV] at h
      simpa using h
    change (Θ 1).symm (φ (torusCover p)) = torusCover p
    rw [hlift, ← h1, Diffeomorph.symm_apply_apply]
  · intro z hz hzS
    have hΘz : Θ 1 z = z := by
      by_cases hzL : z ∈ P.symm.symm '' L
      · obtain ⟨p, hpL, rfl⟩ := hzL
        have hpQ : p ∈ Q := hLQ hpL
        have hpS : p ∈ S := hzS p hpQ (hPapp p).symm
        have h := hΘf 1 p (by rw [show P.symm.target = Q from hPs]; exact hpQ)
        rw [h, (hDS 1).1 hpS]
        rfl
      · exact (hΘs 1 z hzL).1
    change (Θ 1).symm (φ z) = z
    rw [hz]
    conv_lhs => rw [← hΘz]
    exact Diffeomorph.symm_apply_apply _ _

theorem injective_fderiv_of_diffeomorph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : E ≃ₘ[ℝ] E) (q : E) : Function.Injective (fderiv ℝ Φ q) := by
  have hΦd : DifferentiableAt ℝ Φ q :=
    ((contMDiff_iff_contDiff.mp Φ.contMDiff).differentiable (by simp)) q
  have hΨd : DifferentiableAt ℝ Φ.symm (Φ q) :=
    ((contMDiff_iff_contDiff.mp Φ.symm.contMDiff).differentiable (by simp)) _
  have hcomp : HasFDerivAt (Φ.symm ∘ Φ) ((fderiv ℝ Φ.symm (Φ q)).comp (fderiv ℝ Φ q)) q :=
    hΨd.hasFDerivAt.comp q hΦd.hasFDerivAt
  have hid : (Φ.symm ∘ Φ : E → E) = id := funext fun p => Φ.symm_apply_apply p
  rw [hid] at hcomp
  have hu := hcomp.unique (hasFDerivAt_id q)
  intro v w hvw
  have h1 := congrArg (fun L : E →L[ℝ] E => L v) hu
  have h2 := congrArg (fun L : E →L[ℝ] E => L w) hu
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 h2
  rw [← h1, ← h2, hvw]

theorem injective_convex_of_triangular {L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (h10 : L (1, 0) = (1, 0)) (hpos : 0 < (L (0, 1)).2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Function.Injective ((1 - t) • ContinuousLinearMap.id ℝ (ℝ × ℝ) + t • L) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hv' : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) :=
    Prod.ext (by simp) (by simp)
  have hLv : L v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • L (0, 1) := by
    rw [hv', map_add, map_smul, map_smul, h10]
    simp
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, hLv] at hv
  have h2 := congrArg Prod.snd hv
  have h1 := congrArg Prod.fst hv
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_zero, mul_zero, zero_add] at h2
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_zero, mul_one] at h1
  have hc : 0 < (1 - t) + t * (L (0, 1)).2 := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]
      norm_num
    · nlinarith [mul_pos h hpos, ht.2]
  have hv2 : v.2 = 0 := by
    have : v.2 * ((1 - t) + t * (L (0, 1)).2) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  have hv1 : v.1 = 0 := by
    rw [hv2] at h1
    simp only [zero_mul, add_zero] at h1
    linear_combination h1
  exact Prod.ext hv1 hv2

theorem exists_lift_of_fixed_alpha (φ : TDiff) (h : torusMatrix φ = 1)
    (hfix : ∀ z, φ (alphaCircle z) = alphaCircle z) :
    ∃ Φ : (ℝ × ℝ) ≃ₘ⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ (ℝ × ℝ),
      (∀ p, φ (torusCover p) = torusCover (Φ p)) ∧
      (∀ (p : ℝ × ℝ) (m n : ℤ), Φ (p.1 + m, p.2 + n) = ((Φ p).1 + m, (Φ p).2 + n)) ∧
      (∀ x : ℝ, Φ (x, 0) = (x, 0)) ∧
      ∀ x : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, Function.Injective
        ((1 - t) • ContinuousLinearMap.id ℝ (ℝ × ℝ) + t • fderiv ℝ Φ (x, 0)) := by
  have hα (x : ℝ) : torusCover (x, 0) = alphaCircle (cexp x) := by
    rw [torusCover_eq]
    exact Prod.ext rfl cexp_zero
  obtain ⟨Φ, hΦ0, hlift, -, hdeck⟩ := exists_torusLiftDiffeomorph φ (p₀ := 0) (q₀ := 0)
    (by rw [show (0 : ℝ × ℝ) = (0, 0) from rfl, hα, hfix])
  have hdeck' (p : ℝ × ℝ) (m n : ℤ) : Φ (p.1 + m, p.2 + n) = ((Φ p).1 + m, (Φ p).2 + n) := by
    obtain ⟨h1, h2⟩ := hdeck p m n
    rw [h] at h1 h2
    exact Prod.ext (by rw [h1]; simp) (by rw [h2]; simp)
  have hΦc : ContDiff ℝ ∞ Φ := contMDiff_iff_contDiff.mp Φ.contMDiff
  have hΦd : Differentiable ℝ Φ := hΦc.differentiable (by simp)
  have hzero (x : ℝ) : Φ (x, 0) = (x, 0) := by
    have he := eq_of_torusCover_eq (A := ℝ) (F := fun x => (x, (0 : ℝ)))
      (F' := fun x => Φ (x, 0)) (continuous_id.prodMk continuous_const)
      (Φ.continuous.comp (continuous_id.prodMk continuous_const))
      (fun x => by rw [← hlift, hα, hfix]) (a₀ := 0) hΦ0
    exact congrFun he x
  have h10 (x : ℝ) : fderiv ℝ Φ (x, 0) (1, 0) = (1, 0) := by
    have h1 : HasDerivAt (fun x' => Φ (x', 0)) (fderiv ℝ Φ (x, 0) (1, 0)) x :=
      (hΦd (x, 0)).hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id x).prodMk
        (hasDerivAt_const x (0 : ℝ)))
    have h2 : (fun x' => Φ (x', 0)) = fun x' => (x', (0 : ℝ)) := funext hzero
    rw [h2] at h1
    exact h1.unique ((hasDerivAt_id x).prodMk (hasDerivAt_const x (0 : ℝ)))
  have hne (x : ℝ) : (fderiv ℝ Φ (x, 0) (0, 1)).2 ≠ 0 := by
    intro h0
    have h3 : fderiv ℝ Φ (x, 0) (0, 1) =
        fderiv ℝ Φ (x, 0) ((fderiv ℝ Φ (x, 0) (0, 1)).1 • ((1 : ℝ), (0 : ℝ))) := by
      rw [map_smul, h10]
      exact Prod.ext (by simp) (by simp [h0])
    have h4 := congrArg Prod.snd (injective_fderiv_of_diffeomorph Φ (x, 0) h3)
    simp at h4
  have hdc : Continuous fun x : ℝ => (fderiv ℝ Φ (x, 0) (0, 1)).2 :=
    (((hΦc.continuous_fderiv (by simp)).comp (continuous_id.prodMk continuous_const)).clm_apply
      continuous_const).snd
  have hpos : ∀ x : ℝ, 0 < (fderiv ℝ Φ (x, 0) (0, 1)).2 := by
    rcases pos_or_neg_of_forall_ne_zero hdc hne with hp | hn
    · exact hp
    exfalso
    let f : ℝ → ℝ := fun y => (Φ (0, y)).2
    have hf : ContDiff ℝ ∞ f := hΦc.snd.comp (contDiff_const.prodMk contDiff_id)
    have hfd : HasDerivAt f (fderiv ℝ Φ (0, 0) (0, 1)).2 0 := by
      have h1 := hasFDerivAt_snd.comp_hasDerivAt (0 : ℝ) ((hΦd (0, 0)).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ))))
      exact h1
    have hf0 : f 0 = 0 := by simp only [f, hzero]
    have hf1 : f 1 = 1 := by
      have h5 := hdeck' (0, 0) 0 1
      simp only [Int.cast_zero, Int.cast_one, add_zero, zero_add, hzero] at h5
      simp only [f, h5]
    have hev : ∀ᶠ y in 𝓝 (0 : ℝ), deriv f y < 0 :=
      (hf.continuous_deriv (by simp)).continuousAt.eventually_lt continuousAt_const
        (by rw [hfd.deriv]; exact hn 0)
    obtain ⟨ε, hε, hεf⟩ := Metric.eventually_nhds_iff.mp hev
    set y₁ := min (ε / 2) (1 / 2) with hy₁
    have hy₁0 : 0 < y₁ := lt_min (by linarith) (by norm_num)
    have hy₁ε : y₁ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hy₁1 : y₁ ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
    have hanti : StrictAntiOn f (Icc 0 y₁) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc 0 y₁) hf.continuous.continuousOn ?_
      intro y hy
      rw [interior_Icc] at hy
      refine hεf ?_
      rw [Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [hy.1, hy.2]
    have hfy₁ : f y₁ < 0 := by
      have := hanti ⟨le_rfl, hy₁0.le⟩ ⟨hy₁0.le, le_rfl⟩ hy₁0
      rwa [hf0] at this
    obtain ⟨y₀, hy₀, hfy₀⟩ := intermediate_value_Icc hy₁1 hf.continuous.continuousOn
      ⟨hfy₁.le, by rw [hf1]; norm_num⟩
    have h6 : Φ (0, y₀) = Φ ((Φ (0, y₀)).1, 0) := by
      rw [hzero]
      exact Prod.ext rfl hfy₀
    have h7 := congrArg Prod.snd (Φ.injective h6)
    simp only at h7
    linarith [hy₀.1]
  exact ⟨Φ, hlift, hdeck', hzero, fun x t ht =>
    injective_convex_of_triangular (h10 x) (hpos x) ht⟩

theorem int_eq_zero_of_abs_lt_one {n : ℤ} (h : |(n : ℝ)| < 1) : n = 0 := by
  rw [abs_lt] at h
  have h1 : -1 < n := by exact_mod_cast h.1
  have h2 : n < 1 := by exact_mod_cast h.2
  omega

theorem exists_box_subset_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {a b : ℝ} (hab : a ≤ b)
    (hK : Icc a b ×ˢ ({0} : Set ℝ) ⊆ V) :
    ∃ ε > 0, Ioo (a - ε) (b + ε) ×ˢ Ioo (-ε) ε ⊆ V := by
  obtain ⟨r, hr, hrV⟩ :=
    (isCompact_Icc.prod isCompact_singleton).exists_thickening_subset_open hV hK
  refine ⟨r / 2, by linarith, fun p hp => hrV ?_⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨(max a (min p.1 b), 0), ⟨⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩, rfl⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, sub_zero]
  constructor
  · rcases le_total p.1 b with h1 | h1
    · rw [min_eq_left h1]
      rcases le_total a p.1 with h2 | h2
      · rw [max_eq_right h2, sub_self, abs_zero]
        exact hr
      · rw [max_eq_left h2, abs_lt]
        constructor <;> linarith [hp.1.1]
    · rw [min_eq_right h1, max_eq_right hab, abs_lt]
      constructor <;> linarith [hp.1.2]
  · rw [abs_lt]
    constructor <;> linarith [hp.2.1, hp.2.2]

theorem lift_eq_self_of_convex {ψ : TDiff} {Φ : ℝ × ℝ → ℝ × ℝ} (hΦ : Continuous Φ)
    (hlift : ∀ p, ψ (torusCover p) = torusCover (Φ p)) {C : Set (ℝ × ℝ)} (hC : Convex ℝ C)
    (hψC : ∀ p ∈ C, ψ (torusCover p) = torusCover p) {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ C)
    (hΦp₀ : Φ p₀ = p₀) : ∀ p ∈ C, Φ p = p := by
  have : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC.isPreconnected
  have he := eq_of_torusCover_eq (A := C) (F := fun p => (p : ℝ × ℝ)) (F' := fun p => Φ p)
    continuous_subtype_val (hΦ.comp continuous_subtype_val)
    (fun p => by rw [← hlift, hψC p p.2]) (a₀ := ⟨p₀, hp₀⟩) hΦp₀
  intro p hp
  exact congrFun he ⟨p, hp⟩

theorem lift_eq_self_of_translate {Φ : ℝ × ℝ → ℝ × ℝ}
    (hdeck : ∀ (p : ℝ × ℝ) (m n : ℤ), Φ (p.1 + m, p.2 + n) = ((Φ p).1 + m, (Φ p).2 + n))
    {p : ℝ × ℝ} (m n : ℤ) (h : Φ (p.1 - m, p.2 - n) = (p.1 - m, p.2 - n)) : Φ p = p := by
  have h' := hdeck (p.1 - m, p.2 - n) m n
  simp only [sub_add_cancel, h] at h'
  exact h'

theorem lift_eq_self_of_band {ψ : TDiff} {Φ : ℝ × ℝ → ℝ × ℝ} (hΦ : Continuous Φ)
    (hlift : ∀ p, ψ (torusCover p) = torusCover (Φ p))
    (hdeck : ∀ (p : ℝ × ℝ) (m n : ℤ), Φ (p.1 + m, p.2 + n) = ((Φ p).1 + m, (Φ p).2 + n))
    (hΦ0 : Φ (0, 0) = (0, 0)) {δ : ℝ}
    (hband : ∀ p : ℝ × ℝ, |p.1| < δ → ψ (torusCover p) = torusCover p)
    {p : ℝ × ℝ} {k : ℤ} (hp : |p.1 - k| < δ) : Φ p = p := by
  have hδ : 0 < δ := lt_of_le_of_lt (abs_nonneg _) hp
  have hC : Convex ℝ (Ioo (-δ) δ ×ˢ (univ : Set ℝ)) := (convex_Ioo _ _).prod convex_univ
  have hmem (q : ℝ × ℝ) : q ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ) ↔ |q.1| < δ := by
    simp [abs_lt]
  have h := lift_eq_self_of_convex hΦ hlift hC (fun q hq => hband q ((hmem q).mp hq))
    ((hmem (0, 0)).mpr (by simpa using hδ)) hΦ0
  refine lift_eq_self_of_translate hdeck k 0 (h _ ((hmem _).mpr ?_))
  simpa using hp

theorem torusCover_fract (x y : ℝ) : torusCover (Int.fract x, y) = torusCover (x, y) := by
  rw [← torusCover_add_int (Int.fract x, y) ⌊x⌋ 0]
  simp [Int.fract_add_floor]

theorem exists_isotopic_eqOn_nhds_alpha_of_fixed (φ : TDiff) (h : torusMatrix φ = 1)
    (hfix : ∀ z, φ (alphaCircle z) = alphaCircle z) {δ : ℝ}
    (hband : ∀ p : ℝ × ℝ, |p.1| < δ → φ (torusCover p) = torusCover p) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧
      (∀ p : ℝ × ℝ, |p.1| < δ → ψ (torusCover p) = torusCover p) ∧
      ∃ U : Set Torus, IsOpen U ∧ range alphaCircle ⊆ U ∧ ∀ p ∈ U, ψ p = p := by
  have hα (x : ℝ) : torusCover (x, 0) = alphaCircle (cexp x) := by
    rw [torusCover_eq]
    exact Prod.ext rfl cexp_zero
  have hpre {p q : ℝ × ℝ} (hpq : torusCover q = torusCover p) :
      ∃ m n : ℤ, q = (p.1 + m, p.2 + n) := torusCover_eq_torusCover_iff.mp hpq
  obtain ⟨Φ, hlift, hdeck, hzero, hinj⟩ := exists_lift_of_fixed_alpha φ h hfix
  have hΦc : ContDiff ℝ ∞ Φ := contMDiff_iff_contDiff.mp Φ.contMDiff
  let S₁ : Set (ℝ × ℝ) := {p | p.2 = 0} ∪ {p | ∃ k : ℤ, |p.1 - k| < δ}
  have hS₁ : ∀ p ∈ S₁, Φ p = p := by
    rintro p (hp | ⟨k, hk⟩)
    · have h0 := hzero p.1
      rw [show ((p.1, 0) : ℝ × ℝ) = p from Prod.ext rfl hp.symm] at h0
      exact h0
    · exact lift_eq_self_of_band Φ.continuous hlift hdeck (hzero 0) hband hk
  have hK₁ : IsCompact (Icc (-(3 / 10) : ℝ) (3 / 10) ×ˢ ({0} : Set ℝ)) :=
    isCompact_Icc.prod isCompact_singleton
  have hK₁S : Icc (-(3 / 10) : ℝ) (3 / 10) ×ˢ ({0} : Set ℝ) ⊆ S₁ :=
    fun p hp => Or.inl hp.2
  have hinj₁ : ∀ x ∈ Icc (-(3 / 10) : ℝ) (3 / 10) ×ˢ ({0} : Set ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
      Function.Injective ((1 - t) • ContinuousLinearMap.id ℝ (ℝ × ℝ) + t • fderiv ℝ Φ x) := by
    intro x hx t ht
    have hx' : x = (x.1, 0) := Prod.ext rfl hx.2
    rw [hx']
    exact hinj x.1 t ht
  have hQ₁ : IsOpen (Ioo (-(1 / 2) : ℝ) (-(1 / 2) + 1) ×ˢ Ioo (-(1 / 2) : ℝ) (-(1 / 2) + 1)) :=
    isOpen_Ioo.prod isOpen_Ioo
  have hK₁Q : Icc (-(3 / 10) : ℝ) (3 / 10) ×ˢ ({0} : Set ℝ) ⊆
      Ioo (-(1 / 2) : ℝ) (-(1 / 2) + 1) ×ˢ Ioo (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
    rintro p ⟨⟨h1, h2⟩, h3⟩
    rw [mem_singleton_iff] at h3
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨ψ₁, hψ₁, ⟨V₁, hV₁, hKV₁, hψ₁V⟩, hψ₁fix⟩ := exists_isotopic_chart_correction φ hΦc
    hlift hS₁ hK₁ hK₁S hinj₁ hQ₁ (injOn_torusCover_box _ _) hK₁Q
  have hψ₁α : ∀ z, ψ₁ (alphaCircle z) = alphaCircle z := by
    intro z
    refine hψ₁fix _ (hfix z) fun q hq hqz => Or.inl ?_
    rw [← cexp_rep z, ← hα] at hqz
    obtain ⟨m, n, rfl⟩ := hpre hqz
    have hn : n = 0 := int_eq_zero_of_abs_lt_one (by
      rw [abs_lt]
      constructor <;> linarith [hq.2.1, hq.2.2])
    simp [hn]
  have hψ₁band : ∀ p : ℝ × ℝ, |p.1| < δ → ψ₁ (torusCover p) = torusCover p := by
    intro p hp
    refine hψ₁fix _ (hband p hp) fun q _ hqz => Or.inr ?_
    obtain ⟨m, n, rfl⟩ := hpre hqz
    exact ⟨m, by simpa using hp⟩
  obtain ⟨ε, hε, hεV⟩ := exists_box_subset_of_isOpen hV₁ (by norm_num) hKV₁
  set ε₁ := min ε (1 / 4) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε (by norm_num)
  have hε₁q : ε₁ ≤ 1 / 4 := min_le_right _ _
  let B₁ : Set (ℝ × ℝ) := Ioo (-(3 / 10) - ε₁) (3 / 10 + ε₁) ×ˢ Ioo (-ε₁) ε₁
  have hB₁V : B₁ ⊆ V₁ := by
    refine fun p hp => hεV ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2, min_le_left ε (1 / 4)]
  have hB₁0 : ((0 : ℝ), (0 : ℝ)) ∈ B₁ :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have h₁ : torusMatrix ψ₁ = 1 := (torusMatrix_eq_of_isotopic hψ₁).symm.trans h
  obtain ⟨Φ₁, hlift₁, hdeck₁, hzero₁, hinj₁'⟩ := exists_lift_of_fixed_alpha ψ₁ h₁ hψ₁α
  have hΦ₁c : ContDiff ℝ ∞ Φ₁ := contMDiff_iff_contDiff.mp Φ₁.contMDiff
  have hΦ₁B : ∀ p ∈ B₁, Φ₁ p = p :=
    lift_eq_self_of_convex Φ₁.continuous hlift₁ ((convex_Ioo _ _).prod (convex_Ioo _ _))
      (fun p hp => hψ₁V p (hB₁V hp)) hB₁0 (hzero₁ 0)
  let S₂ : Set (ℝ × ℝ) := S₁ ∪ {p | ∃ k : ℤ, (p.1 - k, p.2) ∈ B₁}
  have hS₂ : ∀ p ∈ S₂, Φ₁ p = p := by
    rintro p ((hp | ⟨k, hk⟩) | ⟨k, hk⟩)
    · have h0 := hzero₁ p.1
      rw [show ((p.1, 0) : ℝ × ℝ) = p from Prod.ext rfl hp.symm] at h0
      exact h0
    · exact lift_eq_self_of_band Φ₁.continuous hlift₁ hdeck₁ (hzero₁ 0) hψ₁band hk
    · refine lift_eq_self_of_translate hdeck₁ k 0 ?_
      simpa using hΦ₁B _ hk
  have hK₂ : IsCompact (Icc (1 / 5 : ℝ) (4 / 5) ×ˢ ({0} : Set ℝ)) :=
    isCompact_Icc.prod isCompact_singleton
  have hK₂S : Icc (1 / 5 : ℝ) (4 / 5) ×ˢ ({0} : Set ℝ) ⊆ S₂ :=
    fun p hp => Or.inl (Or.inl hp.2)
  have hinj₂ : ∀ x ∈ Icc (1 / 5 : ℝ) (4 / 5) ×ˢ ({0} : Set ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
      Function.Injective ((1 - t) • ContinuousLinearMap.id ℝ (ℝ × ℝ) + t • fderiv ℝ Φ₁ x) := by
    intro x hx t ht
    have hx' : x = (x.1, 0) := Prod.ext rfl hx.2
    rw [hx']
    exact hinj₁' x.1 t ht
  have hQ₂ : IsOpen (Ioo (0 : ℝ) (0 + 1) ×ˢ Ioo (-(1 / 2) : ℝ) (-(1 / 2) + 1)) :=
    isOpen_Ioo.prod isOpen_Ioo
  have hK₂Q : Icc (1 / 5 : ℝ) (4 / 5) ×ˢ ({0} : Set ℝ) ⊆
      Ioo (0 : ℝ) (0 + 1) ×ˢ Ioo (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
    rintro p ⟨⟨h1, h2⟩, h3⟩
    rw [mem_singleton_iff] at h3
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨ψ₂, hψ₂, ⟨V₂, hV₂, hKV₂, hψ₂V⟩, hψ₂fix⟩ := exists_isotopic_chart_correction ψ₁ hΦ₁c
    hlift₁ hS₂ hK₂ hK₂S hinj₂ hQ₂ (injOn_torusCover_box _ _) hK₂Q
  have hψ₂band : ∀ p : ℝ × ℝ, |p.1| < δ → ψ₂ (torusCover p) = torusCover p := by
    intro p hp
    refine hψ₂fix _ (hψ₁band p hp) fun q _ hqz => Or.inl (Or.inr ?_)
    obtain ⟨m, n, rfl⟩ := hpre hqz
    exact ⟨m, by simpa using hp⟩
  have hψ₂B : ∀ p ∈ B₁, ψ₂ (torusCover p) = torusCover p := by
    intro p hp
    refine hψ₂fix _ (hψ₁V p (hB₁V hp)) fun q hq hqz => Or.inr ?_
    obtain ⟨m, n, rfl⟩ := hpre hqz
    have hn : n = 0 := int_eq_zero_of_abs_lt_one (by
      rw [abs_lt]
      constructor <;> linarith [hq.2.1, hq.2.2, hp.2.1, hp.2.2])
    exact ⟨m, by simpa [hn] using hp⟩
  refine ⟨ψ₂, hψ₁.trans hψ₂, hψ₂band, torusCover '' B₁ ∪ torusCover '' V₂,
    (isOpenQuotientMap_torusCover.isOpenMap _ (isOpen_Ioo.prod isOpen_Ioo)).union
      (isOpenQuotientMap_torusCover.isOpenMap _ hV₂), ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = Int.fract (rep z) := ⟨_, rfl⟩
    have hx : alphaCircle z = torusCover (x, 0) := by
      rw [hxdef, torusCover_fract, hα, cexp_rep]
    have hx0 : 0 ≤ x := hxdef ▸ Int.fract_nonneg _
    have hx1 : x < 1 := hxdef ▸ Int.fract_lt_one _
    rw [hx]
    by_cases h1 : x < 1 / 5
    · exact Or.inl ⟨(x, 0), ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, rfl⟩
    by_cases h2 : x ≤ 4 / 5
    · exact Or.inr ⟨(x, 0), hKV₂ ⟨⟨by linarith, h2⟩, rfl⟩, rfl⟩
    · refine Or.inl ⟨(x - 1, 0), ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, ?_⟩
      have h3 := torusCover_add_int (x - 1, 0) 1 0
      simp only [Int.cast_one, Int.cast_zero, sub_add_cancel, add_zero] at h3
      exact h3.symm
  · rintro _ (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact hψ₂B p hp
    · exact hψ₂V p hp

theorem surjective_of_add_int {f : ℝ → ℝ} (hf : Continuous f)
    (hper : ∀ x (n : ℤ), f (x + n) = f x + n) : Function.Surjective f := by
  intro y
  obtain ⟨n, hn⟩ := exists_int_gt (|y - f 0|)
  have ha : f (0 + (-n : ℤ)) ≤ y := by
    rw [hper]
    push_cast
    linarith [neg_abs_le (y - f 0)]
  have hb : y ≤ f (0 + (n : ℤ)) := by
    rw [hper]
    linarith [le_abs_self (y - f 0)]
  have hle : (0 : ℝ) + (-n : ℤ) ≤ 0 + (n : ℤ) := by
    push_cast
    linarith [abs_nonneg (y - f 0)]
  obtain ⟨c, -, hc⟩ := intermediate_value_Icc hle hf.continuousOn ⟨ha, hb⟩
  exact ⟨c, hc⟩

theorem linearTorusDiffeomorph_one : linearTorusDiffeomorph 1 = torusRefl :=
  Diffeomorph.ext fun x => linearTorusMap_one x

theorem isotopicDiffeomorph_refl_of_fst_eq (θ : TDiff) (h : torusMatrix θ = 1)
    (hθ : ∀ u v v' : Circle, (θ (u, v)).1 = (θ (u, v')).1) :
    IsotopicDiffeomorph θ torusRefl := by
  have hu : torusUnit θ = 1 := Units.ext h
  have h' := isotopicDiffeomorph_linear_of_fst_eq θ hθ
  rwa [hu, linearTorusDiffeomorph_one] at h'

theorem exists_isotopic_fixed_alpha (φ : TDiff) (h : torusMatrix φ = 1)
    (hα : ∀ z, heightOnCircle φ z = 1) {δ : ℝ}
    (hband : ∀ p : ℝ × ℝ, |p.1| < δ → φ (torusCover p) = torusCover p) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ torusMatrix ψ = 1 ∧
      (∀ z, ψ (alphaCircle z) = alphaCircle z) ∧
      ∀ p : ℝ × ℝ, |p.1| < δ → ψ (torusCover p) = torusCover p := by
  have hφα (z : Circle) : φ (z, 1) = ((φ (z, 1)).1, 1) := Prod.ext rfl (hα z)
  obtain ⟨Φ, hΦ, hlift, hdeck⟩ := exists_torusLift φ
  have hã (x : ℝ) : cexp (Φ (x, 0)).1 = (φ (cexp x, 1)).1 := by
    have h1 := congrArg Prod.fst (hlift (x, 0))
    rw [torusCover_eq, torusCover_eq] at h1
    dsimp only at h1
    rw [← h1, cexp_zero]
  have hper (x : ℝ) (n : ℤ) : (Φ (x + n, 0)).1 = (Φ (x, 0)).1 + n := by
    have h1 := (hdeck (x, 0) n 0).1
    rw [h] at h1
    simpa using h1
  have hsurj : ∀ u : Circle, ∃ z : Circle, (φ (z, 1)).1 = u := by
    intro u
    obtain ⟨x, hx⟩ := surjective_of_add_int (f := fun x => (Φ (x, 0)).1)
      (hΦ.continuous.fst.comp (continuous_id.prodMk continuous_const)) hper (rep u)
    refine ⟨cexp x, ?_⟩
    rw [← hã]
    simp only at hx
    rw [hx, cexp_rep]
  have hsymm (u : Circle) : φ.symm (u, 1) = ((φ.symm (u, 1)).1, 1) := by
    obtain ⟨z, rfl⟩ := hsurj u
    rw [← hφα, Diffeomorph.symm_apply_apply]
  let Θ : TDiff :=
    { toFun := fun q => ((φ.symm (q.1, 1)).1, q.2)
      invFun := fun q => ((φ (q.1, 1)).1, q.2)
      left_inv := fun q => by
        change ((φ ((φ.symm (q.1, 1)).1, 1)).1, q.2) = q
        rw [← hsymm, Diffeomorph.apply_symm_apply]
      right_inv := fun q => by
        change ((φ.symm ((φ (q.1, 1)).1, 1)).1, q.2) = q
        rw [← hφα, Diffeomorph.symm_apply_apply]
      contMDiff_toFun :=
        (contMDiff_fst.comp (φ.symm.contMDiff.comp (contMDiff_fst.prodMk contMDiff_const))).prodMk
          contMDiff_snd
      contMDiff_invFun :=
        (contMDiff_fst.comp (φ.contMDiff.comp (contMDiff_fst.prodMk contMDiff_const))).prodMk
          contMDiff_snd }
  have hΘs : torusMatrix Θ.symm = 1 := by
    refine torusMatrix_eq_of_torusLift (Φ := fun p => ((Φ (p.1, 0)).1, p.2))
      ((hΦ.continuous.fst.comp (continuous_fst.prodMk continuous_const)).prodMk continuous_snd)
      (fun p => ?_) 1 (fun p m n => ?_)
    · change ((φ ((torusCover p).1, 1)).1, (torusCover p).2) = _
      rw [torusCover_eq, torusCover_eq]
      exact Prod.ext (hã p.1).symm rfl
    · simp only [hper]
      simp
  have hΘ : torusMatrix Θ = 1 := by
    have h1 := torusMatrix_trans Θ Θ.symm
    rw [Diffeomorph.self_trans_symm, torusMatrix_refl, hΘs, one_mul] at h1
    exact h1.symm
  have hΘi : IsotopicDiffeomorph Θ torusRefl :=
    isotopicDiffeomorph_refl_of_fst_eq Θ hΘ fun _ _ _ => rfl
  refine ⟨φ.trans Θ, ?_, ?_, fun z => ?_, fun p hp => ?_⟩
  · have h1 := IsotopicDiffeomorph.trans_right φ hΘi.symm
    have he : φ.trans torusRefl = φ := Diffeomorph.ext fun x => rfl
    rwa [he] at h1
  · rw [torusMatrix_trans, hΘ, h, one_mul]
  · change ((φ.symm ((φ (z, 1)).1, 1)).1, (φ (z, 1)).2) = (z, 1)
    rw [← hφα, Diffeomorph.symm_apply_apply]
    exact Prod.ext rfl (hα z)
  · change ((φ.symm ((φ (torusCover p)).1, 1)).1, (φ (torusCover p)).2) = torusCover p
    have h0 : ((torusCover p).1, (1 : Circle)) = torusCover (p.1, 0) := by
      rw [torusCover_eq, torusCover_eq, cexp_zero]
    have h1 : φ.symm (torusCover (p.1, 0)) = torusCover (p.1, 0) := by
      conv_lhs => rw [← hband (p.1, 0) hp]
      exact Diffeomorph.symm_apply_apply _ _
    rw [hband p hp, h0, h1]
    rw [torusCover_eq, torusCover_eq]

theorem exists_isotopic_eqOn_nhds_alpha (φ : TDiff) (h : torusMatrix φ = 1)
    (hα : ∀ z, heightOnCircle φ z = 1) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧
      ∃ U : Set Torus, IsOpen U ∧ range alphaCircle ⊆ U ∧ ∀ p ∈ U, ψ p = p := by
  have hnone : ∀ p : ℝ × ℝ, |p.1| < 0 → φ (torusCover p) = torusCover p :=
    fun p hp => absurd hp (not_lt.mpr (abs_nonneg _))
  obtain ⟨ψ₁, hψ₁, h₁, hfix₁, hband₁⟩ := exists_isotopic_fixed_alpha φ h hα hnone
  obtain ⟨ψ, hψ, -, hU⟩ := exists_isotopic_eqOn_nhds_alpha_of_fixed ψ₁ h₁ hfix₁ hband₁
  exact ⟨ψ, hψ₁.trans hψ, hU⟩

def swapTDiff : TDiff where
  toFun q := (q.2, q.1)
  invFun q := (q.2, q.1)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_snd.prodMk contMDiff_fst
  contMDiff_invFun := contMDiff_snd.prodMk contMDiff_fst

theorem swapTDiff_torusCover (p : ℝ × ℝ) : swapTDiff (torusCover p) = torusCover (p.2, p.1) :=
  rfl

theorem swapTDiff_trans_self : swapTDiff.trans swapTDiff = torusRefl :=
  Diffeomorph.ext fun _ => rfl

theorem torusMatrix_swapTDiff_conj {φ : TDiff} (h : torusMatrix φ = 1) :
    torusMatrix (swapTDiff.trans (φ.trans swapTDiff)) = 1 := by
  rw [torusMatrix_trans, torusMatrix_trans, h, mul_one, ← torusMatrix_trans,
    swapTDiff_trans_self, torusMatrix_refl]

theorem exists_isotopic_eqOn_nhds_axes_of_beta (φ : TDiff) (h : torusMatrix φ = 1)
    {U : Set Torus} (hU : IsOpen U) (hαU : range alphaCircle ⊆ U) (hφU : ∀ p ∈ U, φ p = p)
    (hβ : ∀ w, (φ (betaCircle w)).1 = 1) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ ∃ V : Set Torus, IsOpen V ∧
      range alphaCircle ∪ range betaCircle ⊆ V ∧ ∀ p ∈ V, ψ p = p := by
  have hα (x : ℝ) : torusCover (x, 0) = alphaCircle (cexp x) := by
    rw [torusCover_eq]
    exact Prod.ext rfl cexp_zero
  obtain ⟨ε, hε, hεU⟩ := exists_box_subset_of_isOpen (hU.preimage continuous_torusCover)
    zero_le_one (fun p hp => by
      have hp' : p = (p.1, 0) := Prod.ext rfl hp.2
      change torusCover p ∈ U
      rw [hp', hα]
      exact hαU ⟨_, rfl⟩)
  have hφband (p : ℝ × ℝ) (hp : |p.2| < ε) : φ (torusCover p) = torusCover p := by
    rw [abs_lt] at hp
    refine hφU _ ?_
    rw [← torusCover_fract]
    exact hεU ⟨⟨by linarith [Int.fract_nonneg p.1], by linarith [Int.fract_lt_one p.1]⟩,
      ⟨hp.1, hp.2⟩⟩
  let χ : TDiff := swapTDiff.trans (φ.trans swapTDiff)
  have hχ (p : ℝ × ℝ) : χ (torusCover p) = swapTDiff (φ (torusCover (p.2, p.1))) := rfl
  have hχband : ∀ p : ℝ × ℝ, |p.1| < ε → χ (torusCover p) = torusCover p := by
    intro p hp
    rw [hχ, hφband (p.2, p.1) hp]
    rfl
  have hχα : ∀ z, heightOnCircle χ z = 1 := fun z => hβ z
  obtain ⟨χ₁, hχ₁, h₁, hfix₁, hband₁⟩ :=
    exists_isotopic_fixed_alpha χ (torusMatrix_swapTDiff_conj h) hχα hχband
  obtain ⟨χ₂, hχ₂, hband₂, U', hU', hαU', hχ₂U'⟩ :=
    exists_isotopic_eqOn_nhds_alpha_of_fixed χ₁ h₁ hfix₁ hband₁
  have hconj := IsotopicDiffeomorph.trans_right swapTDiff
    (IsotopicDiffeomorph.trans_left swapTDiff (hχ₁.trans hχ₂))
  have he : swapTDiff.trans (χ.trans swapTDiff) = φ := Diffeomorph.ext fun _ => rfl
  rw [he] at hconj
  refine ⟨swapTDiff.trans (χ₂.trans swapTDiff), hconj,
    swapTDiff ⁻¹' U' ∪ torusCover '' (univ ×ˢ Ioo (-ε) ε),
    (hU'.preimage swapTDiff.continuous).union
      (isOpenQuotientMap_torusCover.isOpenMap _ (isOpen_univ.prod isOpen_Ioo)), ?_, ?_⟩
  · rintro _ (⟨u, rfl⟩ | ⟨w, rfl⟩)
    · refine Or.inr ⟨(rep u, 0), ⟨mem_univ _, ⟨by linarith, hε⟩⟩, ?_⟩
      rw [hα, cexp_rep]
    · exact Or.inl (hαU' ⟨w, rfl⟩)
  · rintro x (hx | ⟨p, hp, rfl⟩)
    · change swapTDiff (χ₂ (swapTDiff x)) = x
      rw [hχ₂U' _ hx]
      rfl
    · change swapTDiff (χ₂ (swapTDiff (torusCover p))) = torusCover p
      rw [swapTDiff_torusCover, hband₂ (p.2, p.1) (by rw [abs_lt]; exact hp.2)]
      rfl

end GC.Seifert

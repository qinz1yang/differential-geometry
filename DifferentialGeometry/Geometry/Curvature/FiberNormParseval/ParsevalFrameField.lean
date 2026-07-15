import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentitySmoothFrame
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Global smooth Parseval frame fields

For a closed (compact, boundaryless is not needed here — compactness suffices) smooth Riemannian
manifold `(M, g)` modelled on a real inner-product space `E`, this file constructs a **global smooth
Parseval frame family**: finitely many smooth global tangent vector fields `W a : Π b, T_b M`
(`a : Fin N`) whose fibre values reproduce every tangent vector through the metric,

```
∀ x u,  ∑ a, ⟨W a x, u⟩_g • W a x = u.
```

No global orthonormal frame exists on a general closed manifold (hairy ball), but a Parseval frame
family always does: glue the local Gram–Schmidt orthonormal frames `smoothOrthoFrame g α`
(`RicciIdentitySmoothFrame`) over a finite subcover of their orthonormality neighbourhoods with a
smooth partition of unity `(f k)`, weight by `f k / √(∑ⱼ (f j)²)`, and renormalise — the square
weights then sum to `1` pointwise, so the local Parseval identities glue exactly.

The point of the family is that **every `g`-trace over a pointwise orthonormal frame is computed by
the fixed global family**: for a bilinear form `B` on the tangent fibre,

```
∑ a, B (W a x) (W a x) = ∑ i, B (e i) (e i)        (any `g_x`-orthonormal basis `e`),
```

(`parseval_family_sum_bilin_eq`). Consequently moving-frame trace expressions — the rough Laplacian
frame trace, curvature traces, Ricci contractions — can be rewritten as finite sums of expressions
in the *fixed smooth global fields* `W a`, on which the per-direction covariant
integration-by-parts engines (`integral_tensorInner_covDeriv_combined_eq_zero`,
`integral_frameSummed_covDeriv_combined_eq_zero`) apply directly. This removes the
moving-centre obstruction (the frame `smoothOrthoFrame g x` read at its own centre `x` is not a
fixed field, so it cannot be integrated by parts) from the integrated Bochner–Weitzenböck
telescoping.

## Main results

* `orthonormal_tangent_expansion` — the pointwise `g_x`-orthonormal expansion
  `∑ i, ⟨e i, u⟩_g • e i = u` for a `g_x`-orthonormal family of `finrank` tangent vectors.
* `exists_smooth_parseval_frame_family` — the headline existence of the global smooth Parseval
  frame family on a compact manifold.
* `parseval_family_inner_mul_sum` — the scalar dual-Parseval identity
  `∑ a, ⟨W a, u⟩_g ⟨W a, v⟩_g = ⟨u, v⟩_g`.
* `parseval_family_sum_bilin_eq` — the bilinear trace conversion: the Parseval family computes the
  same diagonal sum as every `g_x`-orthonormal basis, for every `ℝ`-bilinear map into a module.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
/-- **The pointwise `g_x`-orthonormal expansion.** A `g_x`-orthonormal family
`e : Fin (finrank ℝ E) → T_x M` of full cardinality is a basis, and every tangent vector expands as
`u = ∑ i, ⟨e i, u⟩_g • e i`. The inner-product-space structure induced by `g_x` on the tangent fibre
is installed locally (as in `tangent_orthonormalBasisS_witness`), the family upgrades to an
orthonormal basis (`basisOfOrthonormalOfCardEqFinrank`, `Module.Basis.toOrthonormalBasis`), and the
expansion is `OrthonormalBasis.sum_repr'`. -/
theorem orthonormal_tangent_expansion
    (g : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i j, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (u : TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E), g.inner x (e i) u • e i) = u := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  haveI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, NeZero.pos _⟩⟩
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  have hON : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner_eq (e i) (e j)]
    exact horth i j
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfOrthonormalOfCardEqFinrank hON hcard
  have hb_coe : ⇑b = e := coe_basisOfOrthonormalOfCardEqFinrank hON hcard
  have hb_on : Orthonormal ℝ ⇑b := by rw [hb_coe]; exact hON
  let ob : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    b.toOrthonormalBasis hb_on
  have hob : ∀ i, ob i = e i := by
    intro i
    have h1 : ob i = b i := by
      have := Module.Basis.coe_toOrthonormalBasis b hb_on
      exact congrFun this i
    rw [h1, show b i = e i from congrFun hb_coe i]
  have hrepr := ob.sum_repr' u
  calc
    (∑ i : Fin (Module.finrank ℝ E), g.inner x (e i) u • e i)
        = ∑ i : Fin (Module.finrank ℝ E), (inner ℝ (ob i) u : ℝ) • ob i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hob i, hinner_eq (e i) u]
    _ = u := hrepr

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [BoundarylessManifold I M] in
/-- **The scalar dual-Parseval identity.** A family reproducing every tangent vector through the
metric also reproduces the metric itself:
`∑ a, ⟨W a, u⟩_g · ⟨W a, v⟩_g = ⟨u, v⟩_g`. Apply the continuous-linear `g`-pairing against `v` to
the reproducing identity at `u`. -/
theorem parseval_family_inner_mul_sum
    (g : SmoothRiemannianMetric I M) (x : M)
    {N : ℕ} (W : Fin N → TangentSpace I x)
    (hW : ∀ u : TangentSpace I x, (∑ a : Fin N, g.inner x (W a) u • W a) = u)
    (u v : TangentSpace I x) :
    (∑ a : Fin N, g.inner x (W a) u * g.inner x (W a) v) = g.inner x u v := by
  classical
  have h := congrArg (fun w : TangentSpace I x => g.inner x w v) (hW u)
  simp only at h
  rw [show g.inner x (∑ a : Fin N, g.inner x (W a) u • W a) v =
      ∑ a : Fin N, g.inner x (W a) u * g.inner x (W a) v from ?_] at h
  · exact h
  · rw [map_sum (g.inner x) (fun a : Fin N => g.inner x (W a) u • W a) Finset.univ,
      ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_smul (g.inner x) (g.inner x (W a) u) (W a), ContinuousLinearMap.smul_apply,
      smul_eq_mul]

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
/-- **The bilinear trace conversion.** A `g_x`-Parseval family computes the same diagonal sum as
every `g_x`-orthonormal basis: for every `ℝ`-bilinear map `B` into an `ℝ`-module,
`∑ a, B (W a) (W a) = ∑ i, B (e i) (e i)`. Expanding each `W a` over the orthonormal basis and
using the dual-Parseval identity `∑ a, ⟨e i, W a⟩_g ⟨e j, W a⟩_g = δᵢⱼ` collapses the double frame
sum to the diagonal. This is the conversion through which fixed-family expressions compute
pointwise metric traces (the rough-Laplacian frame trace, curvature traces, Ricci contractions). -/
theorem parseval_family_sum_bilin_eq
    (g : SmoothRiemannianMetric I M) (x : M)
    {N : ℕ} (W : Fin N → TangentSpace I x)
    (hW : ∀ u : TangentSpace I x, (∑ a : Fin N, g.inner x (W a) u • W a) = u)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i j, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    {Z : Type*} [AddCommMonoid Z] [Module ℝ Z]
    (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] Z) :
    (∑ a : Fin N, B (W a) (W a)) =
      ∑ i : Fin (Module.finrank ℝ E), B (e i) (e i) := by
  classical
  have hexp : ∀ u : TangentSpace I x,
      (∑ i : Fin (Module.finrank ℝ E), g.inner x (e i) u • e i) = u :=
    orthonormal_tangent_expansion (I := I) (M := M) g x e horth
  have hdual : ∀ i j : Fin (Module.finrank ℝ E),
      (∑ a : Fin N, g.inner x (e i) (W a) * g.inner x (e j) (W a)) =
        if i = j then (1 : ℝ) else 0 := by
    intro i j
    have h1 : (∑ a : Fin N, g.inner x (W a) (e j) • W a) = e j := hW (e j)
    have h2 : g.inner x (e i) (e j) =
        ∑ a : Fin N, g.inner x (W a) (e j) * g.inner x (e i) (W a) := by
      conv_lhs => rw [← h1]
      rw [map_sum (g.inner x (e i)) (fun a : Fin N => g.inner x (W a) (e j) • W a)
        Finset.univ]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_smul (g.inner x (e i)) (g.inner x (W a) (e j)) (W a), smul_eq_mul]
    rw [← horth i j, h2]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [g.symm x (W a) (e j)]
    ring
  calc
    (∑ a : Fin N, B (W a) (W a))
        = ∑ a : Fin N, ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (g.inner x (e i) (W a) * g.inner x (e j) (W a)) • B (e i) (e j) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          conv_lhs => rw [← hexp (W a)]
          rw [map_sum B (fun i : Fin (Module.finrank ℝ E) => g.inner x (e i) (W a) • e i)
            Finset.univ, LinearMap.coe_sum, Finset.sum_apply]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [map_smul B (g.inner x (e i) (W a)) (e i), LinearMap.smul_apply]
          rw [map_sum (B (e i)) (fun j : Fin (Module.finrank ℝ E) =>
            g.inner x (e j) (W a) • e j) Finset.univ, Finset.smul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [map_smul (B (e i)) (g.inner x (e j) (W a)) (e j), smul_smul]
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (∑ a : Fin N, g.inner x (e i) (W a) * g.inner x (e j) (W a)) • B (e i) (e j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_smul]
    _ = ∑ i : Fin (Module.finrank ℝ E), B (e i) (e i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_congr rfl (fun j _ => by
            rw [hdual i j, ite_smul, one_smul, zero_smul])]
          rw [Finset.sum_ite_eq (Finset.univ : Finset (Fin (Module.finrank ℝ E))) i
            (fun j => B (e i) (e j))]
          simp

variable [CompactSpace M]

/-- **Existence of a global smooth Parseval frame family on a compact manifold.** There are
finitely many smooth global tangent vector fields `W a` whose fibre values reproduce every tangent
vector through the metric: `∀ x u, ∑ a, ⟨W a x, u⟩_g • W a x = u`.

**Construction.** Each centre `α` carries the smooth Gram–Schmidt frame `smoothOrthoFrame g α`,
`g_b`-orthonormal for every `b` in the neighbourhood `smoothOrthoFrameNbhd α`
(`smoothOrthoFrame_orthonormal`). The interiors of these neighbourhoods cover the compact manifold;
take a finite subcover with centres `k ∈ t` and a smooth partition of unity `(f k)` subordinate to
it (`SmoothPartitionOfUnity.exists_isSubordinate`). With `ρ := ∑ₖ (f k)²` (smooth and everywhere
positive since some `f k x > 0`), the weighted fields `W (k,i) := ((√ρ)⁻¹ f k) • smoothOrthoFrame g
k i` are smooth global tangent fields. At a point `x`, the `k`-summands with `f k x = 0` vanish;
for the others `x` lies in the orthonormality neighbourhood of `k`, so the inner `i`-sum reproduces
`u` by the orthonormal expansion (`orthonormal_tangent_expansion`), leaving
`∑ₖ (f k x)²/ρ x • u = u`. -/
theorem exists_smooth_parseval_frame_family (g : SmoothRiemannianMetric I M) :
    ∃ (N : ℕ) (W : Fin N → Π b : M, TangentSpace I b),
      (∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (W a))) ∧
      ∀ (x : M) (u : TangentSpace I x),
        (∑ a : Fin N, g.inner x (W a x) u • W a x) = u := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set U : M → Set M := fun α => interior (smoothOrthoFrameNbhd (I := I) (M := M) α) with hU_def
  have hU_open : ∀ α : M, IsOpen (U α) := fun _ => isOpen_interior
  have hU_mem : ∀ α : M, α ∈ U α := fun α =>
    mem_interior_iff_mem_nhds.mpr (smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) α)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU_open
    (fun x _ => mem_iUnion.mpr ⟨x, hU_mem x⟩)
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := I) isClosed_univ
    (fun k : ↥t => U (k : M)) (fun _ => isOpen_interior)
    (by
      intro x _
      rcases mem_iUnion₂.mp (ht (mem_univ x)) with ⟨α, hαt, hαx⟩
      exact mem_iUnion.mpr ⟨⟨α, hαt⟩, hαx⟩)
  set ρ : M → ℝ := fun x => ∑ k : ↥t, (f k x) ^ 2 with hρ_def
  have hρ_pos : ∀ x : M, 0 < ρ x := by
    intro x
    obtain ⟨k, hk⟩ := f.exists_pos_of_mem (mem_univ x)
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨k, Finset.mem_univ k, pow_pos hk 2⟩
  have hρ_smooth : ContMDiff I 𝓘(ℝ) ∞ ρ := by
    have hgen : ∀ s : Finset ↥t,
        ContMDiff I 𝓘(ℝ) ∞ (fun x : M => ∑ k ∈ s, (f k x) ^ 2) := by
      intro s
      induction s using Finset.induction with
      | empty => simpa using contMDiff_const (c := (0 : ℝ))
      | insert k s hk ih =>
          have hsq : ContMDiff I 𝓘(ℝ) ∞ (fun x : M => (f k x) ^ 2) := by
            have h := (f k).contMDiff
            simpa [pow_two] using h.mul h
          simpa [Finset.sum_insert hk] using hsq.add ih
    exact hgen Finset.univ
  set c : ↥t → M → ℝ := fun k x => (Real.sqrt (ρ x))⁻¹ * f k x with hc_def
  have hc_smooth : ∀ k : ↥t, ContMDiff I 𝓘(ℝ) ∞ (c k) := by
    intro k x
    have hsq : ContMDiffAt I 𝓘(ℝ) ∞ (fun y : M => Real.sqrt (ρ y)) x := by
      have h1 : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ Real.sqrt (ρ x) :=
        (Real.contDiffAt_sqrt (ne_of_gt (hρ_pos x))).contMDiffAt
      exact h1.comp x (hρ_smooth x)
    have hinv : ContMDiffAt I 𝓘(ℝ) ∞ (fun y : M => (Real.sqrt (ρ y))⁻¹) x :=
      hsq.inv₀ (ne_of_gt (Real.sqrt_pos.mpr (hρ_pos x)))
    exact hinv.mul ((f k).contMDiff x)
  set W0 : ↥t × Fin n → Π b : M, TangentSpace I b :=
    fun p => fun b => c p.1 b • smoothOrthoFrame (I := I) g (p.1 : M) p.2 b with hW0_def
  have hW0_smooth : ∀ p : ↥t × Fin n,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (W0 p)) := by
    intro p
    have h := ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (n := ∞)
      (V := TangentSpace I) (ψ := c p.1) (s := smoothOrthoFrame (I := I) g (p.1 : M) p.2)
      ((hc_smooth p.1).contMDiffOn (s := univ)) isOpen_univ (subset_univ _)
      ((smoothOrthoFrame_smooth (I := I) g (p.1 : M) p.2).contMDiffOn (s := univ))
    exact h
  have hrepr : ∀ (x : M) (u : TangentSpace I x),
      (∑ p : ↥t × Fin n, g.inner x (W0 p x) u • W0 p x) = u := by
    intro x u
    rw [Fintype.sum_prod_type]
    have hperk : ∀ k : ↥t,
        (∑ i : Fin n, g.inner x (W0 (k, i) x) u • W0 (k, i) x) =
          ((f k x) ^ 2 * (ρ x)⁻¹) • u := by
      intro k
      by_cases hfk : f k x = 0
      · have hc0 : c k x = 0 := by rw [hc_def]; simp [hfk]
        rw [hfk]
        simp only [hW0_def, hc0, zero_smul, map_zero, ContinuousLinearMap.zero_apply,
          smul_zero, Finset.sum_const_zero]
        rw [show (0 : ℝ) ^ 2 * (ρ x)⁻¹ = 0 by ring, zero_smul]
      · have hx_mem : x ∈ smoothOrthoFrameNbhd (I := I) (M := M) (k : M) := by
          have h1 : x ∈ tsupport (f k) := subset_closure (Function.mem_support.mpr hfk)
          exact interior_subset (hf k h1)
        have horth : ∀ i j : Fin n,
            g.inner x (smoothOrthoFrame (I := I) g (k : M) i x)
              (smoothOrthoFrame (I := I) g (k : M) j x) = if i = j then (1 : ℝ) else 0 :=
          fun i j => smoothOrthoFrame_orthonormal (I := I) g (k : M) hx_mem i j
        have hstep : ∀ i : Fin n,
            g.inner x (W0 (k, i) x) u • W0 (k, i) x =
              (c k x) ^ 2 • (g.inner x (smoothOrthoFrame (I := I) g (k : M) i x) u •
                smoothOrthoFrame (I := I) g (k : M) i x) := by
          intro i
          rw [hW0_def]
          simp only
          rw [map_smul (g.inner x) (c k x) (smoothOrthoFrame (I := I) g (k : M) i x),
            ContinuousLinearMap.smul_apply, smul_eq_mul, smul_smul, smul_smul]
          congr 1
          ring
        rw [Finset.sum_congr rfl (fun i _ => hstep i), ← Finset.smul_sum,
          orthonormal_tangent_expansion (I := I) (M := M) g x
            (fun i => smoothOrthoFrame (I := I) g (k : M) i x) horth u]
        congr 1
        rw [hc_def]
        simp only
        rw [mul_pow]
        have hsq : ((Real.sqrt (ρ x))⁻¹) ^ 2 = (ρ x)⁻¹ := by
          rw [← Real.sqrt_inv, Real.sq_sqrt (inv_nonneg.mpr (le_of_lt (hρ_pos x)))]
        rw [hsq]
        ring
    rw [Finset.sum_congr rfl (fun k _ => hperk k), ← Finset.sum_smul, ← Finset.sum_mul]
    rw [show (∑ k : ↥t, (f k x) ^ 2) = ρ x from rfl]
    rw [mul_inv_cancel₀ (ne_of_gt (hρ_pos x)), one_smul]
  refine ⟨Fintype.card (↥t × Fin n), fun a => W0 ((Fintype.equivFin (↥t × Fin n)).symm a),
    fun a => hW0_smooth _, ?_⟩
  intro x u
  conv_rhs => rw [← hrepr x u]
  exact Equiv.sum_comp (Fintype.equivFin (↥t × Fin n)).symm
    (fun p => g.inner x (W0 p x) u • W0 p x)

end Connection
end Integral
end DifferentialGeometry

end

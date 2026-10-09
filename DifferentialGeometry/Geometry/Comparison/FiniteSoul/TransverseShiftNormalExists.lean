import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftNormalLocal

/-!
# Existence of a continuous unit normal along a geodesic of a surface (S-SHIFT2, J7)

The finite replacement for the smooth `exists_isParallelPerpUnitField`: in dimension two, for a unit
geodesic `γ t = π φ_t(p)` of a `C^(r+1)` metric and a unit vector `w ⊥ γ'(0)`, there is a unit vector
field `ξ` along `γ` on any interval `[a, b] ∋ 0`, continuous as a curve in the tangent bundle,
orthogonal to `γ'`, with `ξ 0 = w` (`exists_unitNormal_dim_two`).

Route: local unit normals (`exists_local_unitNormal_dim_two`), the sign is fixed by the two-dimensional
lemma `eq_smul_of_orthonormal_dim_two`, and a `sSup` continuation along `[a, b]`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] in
private theorem signed_unit_facts (B : E →L[ℝ] E →L[ℝ] ℝ) {c : ℝ} (hc : c * c = 1) {v u : E}
    (hvv : B v v = 1) (hvu : B v u = 0) : B (c • v) (c • v) = 1 ∧ B (c • v) u = 0 := by
  constructor
  · simp only [map_smul, smul_apply, smul_eq_mul, hvv]
    linarith
  · simp only [map_smul, smul_apply, smul_eq_mul, hvu, mul_zero]

private theorem coeff_sq_of_orthonormal_dim_two (hdim : Module.finrank ℝ E = 2)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ a b, B a b = B b a) {U N X : E}
    (hU : B U U = 1) (hN : B N N = 1) (hNU : B N U = 0) (hXU : B X U = 0) (hXX : B X X = 1) :
    X = B X N • N ∧ B X N * B X N = 1 := by
  have hrep := eq_smul_of_orthonormal_dim_two hdim hsymm hU hN hNU hXU
  refine ⟨hrep, ?_⟩
  have h := hXX
  rw [hrep] at h
  simp only [map_smul, smul_apply, smul_eq_mul, hN, mul_one] at h
  linarith

variable {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- **Sign matching.** A local unit normal can be replaced by `±` itself so as to take a prescribed unit
normal value at one time. -/
theorem exists_signed_unitNormal (hr : 1 ≤ r) (hdim : Module.finrank ℝ E = 2)
    (p : TangentBundle I M) (hdom : ∀ t, (p, t) ∈ g.geodesicFlowDomain)
    (hp : g.inner p.proj p.snd p.snd = 1) {S : Set ℝ} {N : ℝ → E}
    (hNc : ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj, N t⟩ : TangentBundle I M)) S)
    (hN : ∀ t ∈ S, g.inner (g.geodesicFlow p t).proj (N t) (N t) = 1 ∧
      g.inner (g.geodesicFlow p t).proj (N t) (g.geodesicFlow p t).snd = 0)
    {T : ℝ} (hT : T ∈ S) {w : E} (hw : g.inner (g.geodesicFlow p T).proj w w = 1)
    (hwp : g.inner (g.geodesicFlow p T).proj w (g.geodesicFlow p T).snd = 0) :
    ∃ Ñ : ℝ → E,
      ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj, Ñ t⟩ : TangentBundle I M)) S ∧
      (∀ t ∈ S, g.inner (g.geodesicFlow p t).proj (Ñ t) (Ñ t) = 1 ∧
        g.inner (g.geodesicFlow p t).proj (Ñ t) (g.geodesicFlow p t).snd = 0) ∧ Ñ T = w := by
  have hspeed : g.inner (g.geodesicFlow p T).proj (g.geodesicFlow p T).snd
      (g.geodesicFlow p T).snd = 1 := by
    rw [g.inner_geodesicFlow_eq hr p T (hdom T), hp]
  obtain ⟨hrep, hc2⟩ := coeff_sq_of_orthonormal_dim_two (E := E) hdim
    (g.inner (g.geodesicFlow p T).proj) (fun a b => g.symm _ a b) hspeed (hN T hT).1
    (hN T hT).2 hwp hw
  generalize g.inner (g.geodesicFlow p T).proj w (N T) = c at hrep hc2
  refine ⟨fun t => c • N t, ?_, ?_, hrep.symm⟩
  · rcases mul_self_eq_one_iff.mp hc2 with h1 | h1
    · simp only [h1, one_smul]
      exact hNc
    · simp only [h1, neg_one_smul]
      exact continuousOn_neg_field hNc
  · intro t ht
    exact signed_unit_facts (E := E) (g.inner (g.geodesicFlow p t).proj) hc2 (hN t ht).1
      (hN t ht).2

omit [I.Boundaryless] [T2Space M] in
/-- **Extension step.** A unit normal on `[a, T']` and a matching local unit normal on an open interval
`S ∋ T'` glue to a unit normal on `[a, T'']` for `[T', T''] ⊆ S`. -/
theorem unitNormal_extend (p : TangentBundle I M) {ξ Ñ : ℝ → E} {a T' T'' : ℝ} {S : Set ℝ}
    (haT : a ≤ T') (hTT : T' ≤ T'') (hsub : Icc T' T'' ⊆ S)
    (hξc : ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M))
      (Icc a T'))
    (hξ : ∀ t ∈ Icc a T', g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
      g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0)
    (hÑc : ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj, Ñ t⟩ : TangentBundle I M)) S)
    (hÑ : ∀ t ∈ S, g.inner (g.geodesicFlow p t).proj (Ñ t) (Ñ t) = 1 ∧
      g.inner (g.geodesicFlow p t).proj (Ñ t) (g.geodesicFlow p t).snd = 0)
    (hmatch : ξ T' = Ñ T') :
    ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj,
        (if t ≤ T' then ξ t else Ñ t)⟩ : TangentBundle I M)) (Icc a T'') ∧
      (∀ t ∈ Icc a T'', g.inner (g.geodesicFlow p t).proj (if t ≤ T' then ξ t else Ñ t)
          (if t ≤ T' then ξ t else Ñ t) = 1 ∧
        g.inner (g.geodesicFlow p t).proj (if t ≤ T' then ξ t else Ñ t)
          (g.geodesicFlow p t).snd = 0) ∧
      (if a ≤ T' then ξ a else Ñ a) = ξ a := by
  refine ⟨?_, ?_, by simp [haT]⟩
  · have h1 : ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj,
        (if t ≤ T' then ξ t else Ñ t)⟩ : TangentBundle I M)) (Icc a T') :=
      hξc.congr fun t ht => by simp [ht.2]
    have h2 : ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj,
        (if t ≤ T' then ξ t else Ñ t)⟩ : TangentBundle I M)) (Icc T' T'') := by
      refine (hÑc.mono hsub).congr fun t ht => ?_
      by_cases htT : t ≤ T'
      · have : t = T' := le_antisymm htT ht.1
        subst this
        simp [hmatch]
      · simp [htT]
    refine (h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc).mono fun t ht => ?_
    by_cases htT : t ≤ T'
    · exact Or.inl ⟨ht.1, htT⟩
    · exact Or.inr ⟨le_of_lt (not_le.mp htT), ht.2⟩
  · intro t ht
    by_cases htT : t ≤ T'
    · simp only [htT, ↓reduceIte]
      exact hξ t ⟨ht.1, htT⟩
    · simp only [htT, ↓reduceIte]
      exact hÑ t (hsub ⟨le_of_lt (not_le.mp htT), ht.2⟩)

/-- **Forward continuation.** A unit normal at time `a` extends to a continuous unit normal on
`[a, b]`. -/
theorem exists_unitNormal_Icc (hr : 1 ≤ r) (hdim : Module.finrank ℝ E = 2)
    (p : TangentBundle I M) (hdom : ∀ t, (p, t) ∈ g.geodesicFlowDomain)
    (hp : g.inner p.proj p.snd p.snd = 1) {a b : ℝ} (hab : a ≤ b) {w₀ : E}
    (hw₀ : g.inner (g.geodesicFlow p a).proj w₀ w₀ = 1)
    (hw₀p : g.inner (g.geodesicFlow p a).proj w₀ (g.geodesicFlow p a).snd = 0) :
    ∃ ξ : ℝ → E,
      ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) (Icc a b) ∧
      (∀ t ∈ Icc a b, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
        g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) ∧ ξ a = w₀ := by
  set A : Set ℝ := {T | T ∈ Icc a b ∧ ∃ ξ : ℝ → E,
    ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) (Icc a T) ∧
    (∀ t ∈ Icc a T, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
      g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) ∧ ξ a = w₀}
    with hA
  have haA : a ∈ A := by
    refine ⟨⟨le_rfl, hab⟩, fun _ => w₀, ?_, ?_, rfl⟩
    · rw [Icc_self]; exact continuousOn_singleton _ _
    · intro t ht
      rw [Icc_self, mem_singleton_iff] at ht
      subst ht
      exact ⟨hw₀, hw₀p⟩
  have hAbdd : BddAbove A := ⟨b, fun T hT => hT.1.2⟩
  set s := sSup A with hs
  have has : a ≤ s := le_csSup hAbdd haA
  have hsb : s ≤ b := csSup_le ⟨a, haA⟩ fun T hT => hT.1.2
  obtain ⟨δ, hδ, N, hNc, hN⟩ := exists_local_unitNormal_dim_two g hr hdim p hdom hp s
  obtain ⟨T', hT'A, hT'⟩ := exists_lt_of_lt_csSup ⟨a, haA⟩ (show s - δ < s by linarith)
  have hT's : T' ≤ s := le_csSup hAbdd hT'A
  obtain ⟨⟨haT', -⟩, ξ', hξ'c, hξ', hξ'a⟩ := hT'A
  have hT'S : T' ∈ Ioo (s - δ) (s + δ) := ⟨hT', by linarith⟩
  obtain ⟨Ñ, hÑc, hÑ, hÑT⟩ := exists_signed_unitNormal g hr hdim p hdom hp hNc hN hT'S
    (hξ' T' ⟨haT', le_rfl⟩).1 (hξ' T' ⟨haT', le_rfl⟩).2
  set T'' := min b (s + δ / 2) with hT''
  have hT'T'' : T' ≤ T'' := le_min (hT's.trans hsb) (by linarith)
  have hsub : Icc T' T'' ⊆ Ioo (s - δ) (s + δ) := fun t ht =>
    ⟨lt_of_lt_of_le hT' ht.1, lt_of_le_of_lt (ht.2.trans (min_le_right _ _)) (by linarith)⟩
  obtain ⟨hc, hu, h0⟩ := unitNormal_extend g p haT' hT'T'' hsub hξ'c hξ' hÑc hÑ hÑT.symm
  have hT''A : T'' ∈ A := ⟨⟨haT'.trans hT'T'', min_le_left _ _⟩, _, hc, hu, h0.trans hξ'a⟩
  have hT''b : T'' = b := by
    by_contra hne
    have h1 : T'' = s + δ / 2 := by
      rcases min_choice b (s + δ / 2) with h | h
      · exact absurd h hne
      · exact h
    have h2 : T'' ≤ s := le_csSup hAbdd hT''A
    linarith
  rw [hT''b] at hT''A
  exact hT''A.2

/-- **J7: a continuous unit normal with prescribed value at time `0`** (dimension two), on any interval
`[a, b] ∋ 0`. The finite replacement for the smooth `exists_isParallelPerpUnitField`. -/
theorem exists_unitNormal_dim_two (hr : 1 ≤ r) (hdim : Module.finrank ℝ E = 2)
    (p : TangentBundle I M) (hdom : ∀ t, (p, t) ∈ g.geodesicFlowDomain)
    (hp : g.inner p.proj p.snd p.snd = 1) {w : E} (hw : g.inner p.proj w w = 1)
    (hwp : g.inner p.proj w p.snd = 0) {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    ∃ ξ : ℝ → E,
      ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) (Icc a b) ∧
      (∀ t ∈ Icc a b, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
        g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) ∧ ξ 0 = w := by
  obtain ⟨δ, hδ, N, hNc, hN⟩ := exists_local_unitNormal_dim_two g hr hdim p hdom hp a
  have haS : a ∈ Ioo (a - δ) (a + δ) := ⟨by linarith, by linarith⟩
  obtain ⟨ξ', hξ'c, hξ', -⟩ := exists_unitNormal_Icc g hr hdim p hdom hp (ha.trans hb)
    (hN a haS).1 (hN a haS).2
  have h0 : (0 : ℝ) ∈ Icc a b := ⟨ha, hb⟩
  have hw' : g.inner (g.geodesicFlow p 0).proj w w = 1 := by rw [g.geodesicFlow_zero hr]; exact hw
  have hwp' : g.inner (g.geodesicFlow p 0).proj w (g.geodesicFlow p 0).snd = 0 := by
    rw [g.geodesicFlow_zero hr]; exact hwp
  obtain ⟨ξ, hξc, hξ, hξ0⟩ := exists_signed_unitNormal g hr hdim p hdom hp
    (S := Icc a b) hξ'c hξ' h0 hw' hwp'
  exact ⟨ξ, hξc, hξ, hξ0⟩

end DifferentialGeometry.Geometry.FiniteSoul

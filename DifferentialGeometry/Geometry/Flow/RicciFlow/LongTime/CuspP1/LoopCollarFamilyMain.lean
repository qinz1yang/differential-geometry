import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopCollarFamily

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1

open GC.Endpoint GC.GraphManifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Geometry.Hyperbolic

universe u v

section FamilyMain

variable {M : Type u} [TopologicalSpace M] {I : Type v}
  {H : I → FiniteVolumeHyperbolicModel.{u}}
  (T : ∀ i, HyperbolicTruncation (H i)) (D : ∀ i, Set (H i).Carrier)
  (f : ∀ i, (H i).Carrier → M) (c : ℝ)

/-- The rescaled, reindexed bicollar map on `(ι × Torus) × ℝ`. -/
def sigmaFun_LTP1 : (TorusIdx_LTP1 T × Torus) × ℝ → M := fun p =>
  f p.1.1.1 (bicollar_LTP1 (T p.1.1.1) p.1.1.2 (p.1.2, c * p.2))

/-- Source `-1 < s < 1`. -/
def sigmaSource_LTP1 : Set ((TorusIdx_LTP1 T × Torus) × ℝ) := {p | -1 < p.2 ∧ p.2 < 1}

theorem isOpen_sigmaSource_LTP1 : IsOpen (sigmaSource_LTP1 T) :=
  (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)

variable {T D f c}

theorem scaled_mem_source_LTP1 (hc0 : 0 < c) (hc1 : c ≤ 1) {s : ℝ} (hs : -1 < s ∧ s < 1)
    {i : I} {q : Fin (T i).count} {z : Torus} :
    (z, c * s) ∈ (bicollar_LTP1 (T i) q).source := by
  refine ⟨?_, ?_⟩
  · change -1 < c * s; nlinarith [hs.1, hs.2]
  · change c * s < 1; nlinarith [hs.1, hs.2]

theorem abs_scaled_lt_LTP1 (hc0 : 0 < c) {s : ℝ} (hs : -1 < s ∧ s < 1) : |c * s| < c := by
  rw [abs_mul, abs_of_pos hc0]
  have : |s| < 1 := abs_lt.mpr hs
  nlinarith

variable (hDo : ∀ i, IsOpen (D i)) (hcont : ∀ i, ContinuousOn (f i) (D i))
  (hinj : ∀ i, InjOn (f i) (D i))
  (hdisj : ∀ i i', i ≠ i' → Disjoint (f i '' D i) (f i' '' D i'))
  (hc0 : 0 < c) (hc1 : c ≤ 1)
  (hcD : ∀ (j : TorusIdx_LTP1 T) (z : Torus) (s : ℝ), |s| < c →
      bicollar_LTP1 (T j.1) j.2 (z, s) ∈ D j.1)

include hcont hc0 hc1 hcD in
theorem continuousOn_sigmaFun_LTP1 : ContinuousOn (sigmaFun_LTP1 T f c) (sigmaSource_LTP1 T) := by
  intro p0 hp0
  obtain ⟨⟨j0, z0⟩, s0⟩ := p0
  let G : (TorusIdx_LTP1 T × Torus) × ℝ → M := fun p =>
    f j0.1 (bicollar_LTP1 (T j0.1) j0.2 (p.1.2, c * p.2))
  have hG : ContinuousWithinAt G (sigmaSource_LTP1 T) ((j0, z0), s0) := by
    have h1 : ContinuousOn (fun p : (TorusIdx_LTP1 T × Torus) × ℝ => (p.1.2, c * p.2))
        (sigmaSource_LTP1 T) := by
      apply Continuous.continuousOn
      exact (continuous_snd.comp continuous_fst).prodMk (continuous_const.mul continuous_snd)
    have h2 : ContinuousOn (fun p : (TorusIdx_LTP1 T × Torus) × ℝ =>
        bicollar_LTP1 (T j0.1) j0.2 (p.1.2, c * p.2)) (sigmaSource_LTP1 T) :=
      (bicollar_LTP1 (T j0.1) j0.2).continuousOn.comp h1
        (fun p hp => scaled_mem_source_LTP1 hc0 hc1 hp)
    exact (hcont j0.1).comp h2 (fun p hp => hcD j0 _ _ (abs_scaled_lt_LTP1 hc0 hp)) _ hp0
  have hev : {p : (TorusIdx_LTP1 T × Torus) × ℝ | p.1.1 = j0} ∈ 𝓝 ((j0, z0), s0) := by
    have : IsOpen {p : (TorusIdx_LTP1 T × Torus) × ℝ | p.1.1 = j0} :=
      (isOpen_discrete {j0}).preimage (continuous_fst.comp continuous_fst)
    exact this.mem_nhds (show ((j0, z0), s0).1.1 = j0 from rfl)
  refine hG.congr_of_eventuallyEq ?_ rfl
  filter_upwards [nhdsWithin_le_nhds hev] with p hp
  obtain ⟨⟨j, z⟩, s⟩ := p
  change j = j0 at hp
  subst hp
  rfl

include hinj hdisj hc0 hc1 hcD in
theorem injOn_sigmaFun_LTP1 : InjOn (sigmaFun_LTP1 T f c) (sigmaSource_LTP1 T) := by
  rintro ⟨⟨⟨i, q⟩, z⟩, s⟩ hp ⟨⟨⟨i', q'⟩, z'⟩, s'⟩ hp' h
  have ha := hcD ⟨i, q⟩ z (c * s) (abs_scaled_lt_LTP1 hc0 hp)
  have ha' := hcD ⟨i', q'⟩ z' (c * s') (abs_scaled_lt_LTP1 hc0 hp')
  change f i (bicollar_LTP1 (T i) q (z, c * s)) = f i' (bicollar_LTP1 (T i') q' (z', c * s')) at h
  by_cases hii : i = i'
  · subst hii
    have h1 := hinj i ha ha' h
    by_cases hqq : q = q'
    · subst hqq
      have h2 := (bicollar_LTP1 (T i) q).injOn (scaled_mem_source_LTP1 (z := z) hc0 hc1 hp)
        (scaled_mem_source_LTP1 (z := z') hc0 hc1 hp') h1
      have h3 := Prod.mk.inj h2
      have : s = s' := by
        have := h3.2
        nlinarith [mul_left_cancel₀ hc0.ne' this]
      subst this; rw [h3.1]
    · exfalso
      have a1 := (bicollar_LTP1 (T i) q).map_source (scaled_mem_source_LTP1 (z := z) hc0 hc1 hp)
      have a2 := (bicollar_LTP1 (T i) q').map_source (scaled_mem_source_LTP1 (z := z') hc0 hc1 hp')
      exact Set.disjoint_left.mp (bicollar_disjoint_LTP1 (T i) hqq) a1 (h1 ▸ a2)
  · exfalso
    exact Set.disjoint_left.mp (hdisj i i' hii) ⟨_, ha, rfl⟩ ⟨_, ha', h.symm⟩

end FamilyMain

end GC.LongTime.CuspP1

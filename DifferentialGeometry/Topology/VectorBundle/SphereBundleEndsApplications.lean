import DifferentialGeometry.Topology.VectorBundle.SphereBundleEnds

/-!
# Consumers of the LFR52 end count: one end for rank `≥ 2`, two ends for the trivial line

Frozen blueprint master207A, LFR52 (lines 29386–29388, 29425–29436): the first two rows of
(LFR51.1) (`ℝ³`, `S¹ × ℝ²`) have one end, the trivial surface-line rows (`S² × ℝ`, `T² × ℝ`) have
two. LFR54 (lines 29547–29548): "LFR52 and LC77 exclude its two trivial surface-line bundles".

* `unbounded_components_eq_of_one_lt_finrank`: rank `≥ 2` over a compact connected base gives LC77's
  one-end form on any homeomorphic proper metric space.
* `not_isPreconnected_sphereBundle_trivial_real`: the unit sphere bundle of `B × ℝ` is disconnected.
* `false_of_homeomorph_trivial_line`: a proper metric space homeomorphic to `B × ℝ` (compact
  nonempty `B`) violates LC77's at-most-one-end conclusion — the LFR54 exclusion.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set

namespace DifferentialGeometry.Topology.VectorBundle

/-- **LFR52, rows `ℝ³` and `S¹ × ℝ²`.** A Riemannian bundle of rank `≥ 2` over a compact connected
base has one end in LC77's sense, after any homeomorphism onto a proper metric space. -/
theorem unbounded_components_eq_of_one_lt_finrank {B : Type*} [TopologicalSpace B]
    [CompactSpace B] [ConnectedSpace B]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    {N : Type*} [MetricSpace N] (hF : 1 < Module.finrank ℝ F) (e : TotalSpace F V ≃ₜ N)
    (K : Set N) (hK : IsCompact K) (a b : N)
    (ha : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a))
    (hb : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b)) :
    connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b :=
  unbounded_components_eq_of_isPreconnected_sphereBundle e
    (isConnected_sphereBundle_of_one_lt_finrank hF).isPreconnected K hK a b ha hb

/-- **LFR52, rows `S² × ℝ` and `T² × ℝ`.** The unit sphere bundle of the trivial line bundle over a
nonempty base is not preconnected (its two sheets `±1` are separated). -/
theorem not_isPreconnected_sphereBundle_trivial_real {B : Type*} [TopologicalSpace B]
    [Nonempty B] : ¬ IsPreconnected {z : TotalSpace ℝ (Bundle.Trivial B ℝ) | ‖z.2‖ = 1} := by
  intro hS
  obtain ⟨b⟩ := (inferInstance : Nonempty B)
  have hc : Continuous (fun z : TotalSpace ℝ (Bundle.Trivial B ℝ) => (z.2 : ℝ)) :=
    continuous_snd.comp (Bundle.Trivial.homeomorphProd B ℝ).continuous
  obtain ⟨z, hzS, hzu, hzv⟩ := hS {z | (0 : ℝ) < z.2} {z | (z.2 : ℝ) < 0}
    (isOpen_lt continuous_const hc) (isOpen_lt hc continuous_const)
    (fun z hz => by
      have hz' : |(z.2 : ℝ)| = 1 := by simpa [Real.norm_eq_abs] using hz
      rcases lt_or_gt_of_ne (show (z.2 : ℝ) ≠ 0 by intro h0; rw [h0] at hz'; simp at hz') with
        h | h
      · exact Or.inr h
      · exact Or.inl h)
    ⟨⟨b, (1 : ℝ)⟩, by simp, by norm_num⟩ ⟨⟨b, (-1 : ℝ)⟩, by simp, by norm_num⟩
  exact lt_asymm (show (0 : ℝ) < z.2 from hzu) (show (z.2 : ℝ) < 0 from hzv)

/-- **LFR54 exclusion of the trivial surface-line bundles (LFR52 + LC77).** A proper metric space
homeomorphic to the total space of the trivial line bundle over a compact nonempty base cannot
satisfy LC77's conclusion that, for every compact `K`, all unbounded components of `Kᶜ`
coincide. -/
theorem false_of_homeomorph_trivial_line {B : Type*} [TopologicalSpace B] [CompactSpace B]
    [Nonempty B] {N : Type*} [MetricSpace N] [ProperSpace N]
    (Φ : TotalSpace ℝ (Bundle.Trivial B ℝ) ≃ₜ N)
    (hN : ∀ K : Set N, IsCompact K → ∀ a b : N,
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
      connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b) : False :=
  not_isPreconnected_sphereBundle_trivial_real ((isPreconnected_sphereBundle_iff Φ).mpr hN)

end DifferentialGeometry.Topology.VectorBundle

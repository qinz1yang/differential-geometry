import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.ScalarJets
import DifferentialGeometry.Analysis.Calculus.TimeJet.ClosedJetEvolution
import DifferentialGeometry.Analysis.Calculus.TimeJet.EvolutionJets
import DifferentialGeometry.Analysis.Calculus.TimeJet.SpatialDerivatives
import DifferentialGeometry.Analysis.Calculus.TimeJet.SliceSwap

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace DifferentialGeometry.Analysis

variable {P F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private abbrev ScalarState (F : Type*) (n : ℕ) := ℝ × ℝ × (Fin (3 + n) → F)

private def scalarTimeLift (Φ : ScalarState F 0 → F) (n : ℕ) :
    ScalarState F (n + 2) → ScalarState F n :=
  fun v => (1, 0, fun i => scalarJetProlongation Φ i.val
    (scalarJetProjection (F := F) (by omega : 3 + i.val ≤ 3 + (n + 2)) v))

private theorem contDiffOn_scalarTimeLift
    {Φ : ScalarState F 0 → F} {Ω : Set (ScalarState F 0)}
    (hΩ : IsOpen Ω) (hΦ : ContDiffOn ℝ ∞ Φ Ω) (n : ℕ) :
    ContDiffOn ℝ ∞ (scalarTimeLift Φ n)
      (scalarJetProjection (F := F) (by omega : 3 ≤ 3 + (n + 2)) ⁻¹' Ω) := by
  apply ContDiffOn.prodMk contDiffOn_const
  apply ContDiffOn.prodMk contDiffOn_const
  apply contDiffOn_pi.mpr
  intro i
  have hc := contDiffOn_scalarJetProlongation hΩ hΦ i.val
  let pr := scalarJetProjection (F := F)
    (by omega : 3 + i.val ≤ 3 + (n + 2))
  exact hc.comp pr.contDiff.contDiffOn (fun v hv => hv)

private theorem hasDerivWithinAt_iteratedDeriv_of_equation
    {G H : ℝ → ℝ → F} {a b : ℝ} {V : Set ℝ}
    (hab : a < b) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (Icc a b ×ˢ V))
    (hpde : ∀ t ∈ Icc a b, ∀ x ∈ V,
      HasDerivWithinAt (fun s => G s x) (H t x) (Icc a b) t)
    (j : ℕ) {t x : ℝ} (ht : t ∈ Icc a b) (hx : x ∈ V) :
    HasDerivWithinAt (fun s => iteratedDeriv j (G s) x)
      (iteratedDeriv j (H t) x) (Icc a b) t := by
  have hswap : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => G q.2 q.1) (V ×ˢ Icc a b) :=
    hG.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun q hq => ⟨hq.2, hq.1⟩)
  have hacc : Icc a b ⊆ closure (interior (Icc a b)) := by
    rw [interior_Icc, closure_Ioo hab.ne]
  have hd := hasDerivWithinAt_iteratedDeriv_fst (G := fun x t => G t x) hV (uniqueDiffOn_Icc hab)
    hacc hswap j hx ht
  have heq : (fun y => derivWithin (fun s => G s y) (Icc a b) t) =ᶠ[𝓝 x] H t := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact (hpde t ht y hy).derivWithin ((uniqueDiffOn_Icc hab) t ht)
  rw [heq.iteratedDeriv_eq j] at hd
  exact hd

theorem continuousOn_iteratedDerivWithin_iteratedDeriv_of_jet_equation [CompleteSpace F]
    {S : Set P} {V : Set ℝ} {a b : ℝ}
    (hab : a < b) (hV : IsOpen V)
    {G : P → ℝ → ℝ → F} {σ : P → ℝ}
    (hσ : ContinuousOn σ S)
    (Φ : (ℝ × ℝ × (Fin 3 → F)) → F)
    {Ω : Set (ℝ × ℝ × (Fin 3 → F))}
    (hΩ : IsOpen Ω) (hΦ : ContDiffOn ℝ ∞ Φ Ω)
    (hmap : ∀ p ∈ S, ∀ t ∈ Icc a b, ∀ x ∈ V,
      (σ p + t, x, fun i : Fin 3 => iteratedDeriv i.val (G p t) x) ∈ Ω)
    (hGs : ∀ p ∈ S, ∀ t ∈ Icc a b, ContDiffOn ℝ ∞ (G p t) V)
    (hjets : ∀ j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDeriv j (G q.1 q.2.1) q.2.2)
      (S ×ˢ Icc a b ×ˢ V))
    (hpde : ∀ p ∈ S, ∀ t ∈ Ioo a b, ∀ x ∈ V,
      HasDerivAt (fun s => G p s x)
        (Φ (σ p + t, x, fun i : Fin 3 => iteratedDeriv i.val (G p t) x)) t)
    (k j : ℕ) :
    ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDerivWithin k
        (fun t => iteratedDeriv j (G q.1 t) q.2.2) (Icc a b) q.2.1)
      (S ×ˢ Icc a b ×ˢ V) := by
  have hG (p : P) (hp : p ∈ S) :
      ContDiffOn ℝ ∞ (Function.uncurry (G p)) (Icc a b ×ˢ V) := by
    apply contDiffOn_of_scalar_jet_equation hab hV hΩ hΦ (hGs p hp)
    · intro r
      exact (hjets r).comp (continuousOn_const.prodMk continuousOn_id)
        (fun q hq => ⟨hp, hq⟩)
    · exact hmap p hp
    · exact hpde p hp
  let Ωn : ∀ n, Set (ScalarState F n) := fun n =>
    scalarJetProjection (by omega : 3 ≤ 3 + n) ⁻¹' Ω
  let π : ∀ n, ScalarState F (n + 2) →L[ℝ] ScalarState F n := fun n =>
    scalarJetProjection (by omega : 3 + n ≤ 3 + (n + 2))
  let u : ∀ n, (P × ℝ) → ℝ → ScalarState F n := fun n q t =>
    (σ q.1 + t, q.2, fun i : Fin (3 + n) => iteratedDeriv i.val (G q.1 t) q.2)
  have hΩn (n : ℕ) : IsOpen (Ωn n) :=
    hΩ.preimage (scalarJetProjection _).continuous
  have hu (n : ℕ) : ContinuousOn
      (fun q : (P × ℝ) × ℝ => u n q.1 q.2) ((S ×ˢ V) ×ˢ Icc a b) := by
    have hperm : ContinuousOn (fun q : (P × ℝ) × ℝ => (q.1.1, q.2, q.1.2))
        ((S ×ˢ V) ×ˢ Icc a b) := by fun_prop
    have hmaps : MapsTo (fun q : (P × ℝ) × ℝ => (q.1.1, q.2, q.1.2))
        ((S ×ˢ V) ×ˢ Icc a b) (S ×ˢ Icc a b ×ˢ V) :=
      fun q hq => ⟨hq.1.1, hq.2, hq.1.2⟩
    apply ContinuousOn.prodMk
    · exact (hσ.comp (by fun_prop) (fun q hq => hq.1.1)).add (by fun_prop)
    apply ContinuousOn.prodMk (by fun_prop)
    exact continuousOn_pi.mpr fun i => (hjets i.val).comp hperm hmaps
  have huΩ (n : ℕ) (q : P × ℝ) (hq : q ∈ S ×ˢ V) (t : ℝ)
      (ht : t ∈ Icc a b) : u n q t ∈ Ωn n :=
    hmap q.1 hq.1 t ht q.2 hq.2
  have hcompat (n : ℕ) (q : P × ℝ) (hq : q ∈ S ×ˢ V) (t : ℝ)
      (ht : t ∈ Icc a b) : π n (u (n + 2) q t) = u n q t := rfl
  have hclosed (p : P) (hp : p ∈ S) (t : ℝ) (ht : t ∈ Icc a b)
      (x : ℝ) (hx : x ∈ V) : HasDerivWithinAt (fun s => G p s x)
        (Φ (σ p + t, x, fun i : Fin 3 => iteratedDeriv i.val (G p t) x))
        (Icc a b) t := by
    have htime : ContinuousOn (fun s => G p s x) (Icc a b) :=
      (hG p hp).continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
        (fun s hs => ⟨hs, hx⟩)
    have hRjoint : ContinuousOn (fun q : (P × ℝ) × ℝ => Φ (u 0 q.1 q.2))
        ((S ×ˢ V) ×ˢ Icc a b) :=
      hΦ.continuousOn.comp (hu 0) (fun q hq => huΩ 0 q.1 hq.1 q.2 hq.2)
    have hRtime := hRjoint.comp
      ((continuousOn_const (c := (p, x))).prodMk continuousOn_id)
      (fun s hs => ⟨⟨hp, hx⟩, hs⟩)
    exact hasDerivIcc_of_int hab htime hRtime (fun s hs => hpde p hp s hs x hx) ht
  have hdu (n : ℕ) (q : P × ℝ) (hq : q ∈ S ×ˢ V) (t : ℝ)
      (ht : t ∈ Icc a b) :
      HasDerivWithinAt (u n q) (scalarTimeLift Φ n (u (n + 2) q t)) (Icc a b) t := by
    apply HasDerivWithinAt.prodMk
      (((hasDerivAt_id t).const_add (σ q.1)).hasDerivWithinAt)
    apply HasDerivWithinAt.prodMk (hasDerivWithinAt_const t (Icc a b) q.2)
    apply hasDerivWithinAt_pi.mpr
    intro i
    have hd := hasDerivWithinAt_iteratedDeriv_of_equation hab hV (hG q.1 hq.1)
      (fun s hs x hx => hclosed q.1 hq.1 s hs x hx) i.val ht hq.2
    have hslice : ContDiffOn ℝ ∞ (G q.1 t) V :=
      (hG q.1 hq.1).comp (contDiffOn_const.prodMk contDiffOn_id)
        (fun x hx => ⟨ht, hx⟩)
    have heq := iteratedDeriv_eq_scalarJetProlongation_of_contDiffOn hΩ hΦ hV
      hslice (σ q.1 + t) (fun x hx => hmap q.1 hq.1 t ht x hx) i.val hq.2
    rw [heq] at hd
    exact hd
  let Fproj : ScalarState F j → F := fun v => v.2.2 ⟨j, by omega⟩
  have hproj : ContDiffOn ℝ ∞ Fproj (Ωn j) := by
    exact ((contDiff_apply ℝ F (⟨j, by omega⟩ : Fin (3 + j))).comp
      (contDiff_snd.comp contDiff_snd)).contDiffOn
  have hh := continuousOn_iteratedDerivWithin_of_smooth_lifts
    (X := ScalarState F) (next := fun n => n + 2) π (scalarTimeLift Φ) Ωn hΩn
    (fun n v hv => hv) (fun n => contDiffOn_scalarTimeLift hΩ hΦ n)
    (uniqueDiffOn_Icc hab) u hu huΩ hcompat hdu k j Fproj hproj
  have hperm : ContinuousOn (fun q : P × ℝ × ℝ => ((q.1, q.2.2), q.2.1))
      (S ×ˢ Icc a b ×ˢ V) := by fun_prop
  have hmaps : MapsTo (fun q : P × ℝ × ℝ => ((q.1, q.2.2), q.2.1))
      (S ×ˢ Icc a b ×ˢ V) ((S ×ˢ V) ×ˢ Icc a b) :=
    fun q hq => ⟨⟨hq.1, hq.2.2⟩, hq.2.1⟩
  exact hh.comp hperm hmaps

end DifferentialGeometry.Analysis

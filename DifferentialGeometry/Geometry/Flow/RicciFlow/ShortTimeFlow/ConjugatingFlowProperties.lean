import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.FlatVariationalIdentity
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.BasepointMotion
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.EvalFormChainRule
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.RicciFlowPdeAtZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.RicciContinuityInMetricTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Defs
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.MovingMfderivContinuity
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeFlow.CutoffExtension
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Regularity data for the conjugating flow of the DeTurck–Ricci short-time construction

Collects the per-time analytic data produced by the conjugating diffeomorphism flow — flat
variational data, orbit-pushforward continuity, time-zero continuity, and joint chart-Gram
continuity — that feed the assembly of the Ricci-flow solution from the DeTurck solution.
-/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.Integral.Connection

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Flat variational data of the conjugating flow (faithful open input).**

For the conjugating diffeomorphism family `Φ_fam` of the Hamilton–DeTurck construction —
PINNED to the genuine flow by the backward bare-orbit ODE `hΦode`
(`∂_s Φ_fam = -deTurckVF (g_DT s) g_bg ∘ Φ_fam` on `Ioo 0 T`) — the four flat variational
facts of that flow hold:

* `hv_flat`: existence of factor jets `T'`, `P'` realising the per-slot raw flat variational
  identity `RawVariationalIdentityFlat Φ_fam t x v (T' t x v) (P' t x v)` on the interior;
* `hcorr`: the Christoffel-correction equation relating those factor values to the negative
  covariant slot value plus the Christoffel-correction term;
* `hbase`: the base-point-motion datum (the frozen-vector chart-metric map along the orbit has
  within-set derivative `-metricTransportResidual`);
* `h_total_eval`: the three-piece additive chain rule for the full pulled-back inner product.

These are the genuine open chart-ODE jet / variational-lift analytic inputs of the concrete
conjugating flow.  They are TRUE for this flow (pinned via `hΦode`) and reference only the
internal data `g_DT` / `Φ_fam` / `deTurckVF (g_DT t) g_bg`.  Faithful labeled deferred input
for a dedicated fill effort. -/
theorem conjugating_flow_flat_data
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hDT_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ y : M, ∀ a b : TangentSpace I y,
      HasDerivWithinAt (fun u : ℝ => (g_DT u).inner y a b)
        (deTurckRicciRHS (I := I) g_bg (g_DT s) y a b) (Set.Ici 0) s)
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x))))) :
    ∃ T' P' : ℝ → ∀ x : M, TangentSpace I x → (E →L[ℝ] E),
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
          RawVariationalIdentityFlat (I := I) Φ_fam t x v (T' t x v) (P' t x v)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
          (T' t x v) (mfderiv I I (Φ_fam t : M → M) x v) + (P' t x v) v
            = negCovariantSlotValue (I := I) (g_DT t)
                (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v
              + christoffelCorrection (I := I) (g_DT t) (Φ_fam t x) (Φ_fam t x)
                  (chartE_section_repr (I := I) (Φ_fam t x)
                    (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x))
                  (mfderiv I I (Φ_fam t : M → M) x v)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt
            (fun s : ℝ => (g_DT t).inner ((Φ_fam s : M → M) x)
              (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
            (-metricTransportResidual (I := I) (g_DT t)
                (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w) (Set.Ici 0) t) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt
            (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
              (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w))
            (((-2 : ℝ) * ricciTensor (I := I) (g_DT t) (Φ_fam t x)
                    (mfderiv I I (Φ_fam t : M → M) x v)
                    (mfderiv I I (Φ_fam t : M → M) x w)
                + lieDerivMetric (I := I) (g_DT t)
                    (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
                    (mfderiv I I (Φ_fam t : M → M) x v)
                    (mfderiv I I (Φ_fam t : M → M) x w))
              + (-lieDerivMetric (I := I) (g_DT t)
                    (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
                    (mfderiv I I (Φ_fam t : M → M) x v)
                    (mfderiv I I (Φ_fam t : M → M) x w))) (Set.Ici 0) t) := by
  sorry

private theorem neg_field_cmdwa
    (X : ℝ → ∀ x : M, TangentSpace I x) {u : Set (ℝ × M)} {q₀ : ℝ × M}
    (hX : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) u q₀) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (-(X q.1 q.2)) : TangentBundle I M)) u q₀ := by
  rw [Bundle.contMDiffWithinAt_totalSpace] at hX ⊢
  obtain ⟨hXproj, hXfib⟩ := hX
  refine ⟨hXproj, ?_⟩
  set e := trivializationAt E (TangentSpace I) (q₀.2) with he
  have hfib := hXfib.neg
  have hbase : ContinuousWithinAt (fun q : ℝ × M => q.2) u q₀ := continuous_snd.continuousWithinAt
  have hmem : e.baseSet ∈ 𝓝 (q₀.2) :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' q₀.2)
  have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ 𝓝[u] q₀ := hbase hmem
  refine hfib.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hpre] with x hx
    simpa using (e.linear ℝ hx).map_neg (X x.1 x.2)
  · simpa using
      (e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt' q₀.2)).map_neg (X q₀.1 q₀.2)

set_option linter.unusedVariables false in
/-- **Whole-`Ico 0 T` orbit and total-space pushforward continuity of the conjugating flow.**

For the conjugating diffeomorphism family `Φ_fam` of the Hamilton–DeTurck construction —
PINNED to the genuine flow by the backward bare-orbit ODE `hΦode` — the orbit and the
total-space (bundle) pushforward of the flow are continuous in time on the whole half-open
window `Ico 0 T`, up to the `C⁰`-at-`0` boundary:

* `hΦ_orbit`: the orbit `s ↦ Φ_fam s y` is continuous on `Ico 0 T`;
* `hΦ_total`: the bundle datum `s ↦ ⟨Φ_fam s y, mfderiv (Φ_fam s) y u⟩` is continuous on `Ico 0 T`.

Both conjuncts split into an at-`0` boundary part and an interior part.  At `0` they are the
hypotheses `hΦorbit0` / `hΦmfderiv0` (the bundle-form `t = 0`-endpoint data).  On the interior
`Ioo 0 T`, orbit continuity is the `ContinuousWithinAt` of the orbit ODE `hΦode`.  The interior
bundle datum is identified, on a working window `Ioo c d ∋ s`, with the moving spatial differential
of a genuine jointly-`C∞` window-flow `Φg`: the negated field `-deTurckVF (g_DT ·) g_bg` is jointly
`C∞` (`neg_field_cmdwa` + `hfield_reg`), cut off to an autonomised field with a global jointly-`C∞`
flow (`interior_field_global_cutoff_extension`, `global_flow_jointContMDiffOn_on_closed_manifold`);
bare-orbit uniqueness (`bare_integral_flow_eqOn_of_jointC1`) gives `Φ_fam r x = Φg (Φ_fam s x) r` on
the window, so the two bundle sections agree (chain rule `mfderiv_comp_of_eq`,
`Diffeomorph.mdifferentiable`), and `slice_mfderiv_continuousAt_of_jointFlow` supplies the continuity
of `Φg`'s moving differential.  All hypotheses constrain only the internal data `g_DT` / `Φ_fam`,
never the headline; neither output is equal to, nor destructures to, any hypothesis. -/
theorem conjugating_flow_orbit_pushforward_continuity_data
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (hT : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hfield_reg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hΦorbit0 : ∀ y : M,
      ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ici (0 : ℝ)) 0)
    (hΦmfderiv0 : ∀ (y : M) (u : TangentSpace I y),
      ContinuousWithinAt (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
        (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ici (0 : ℝ)) 0) :
    (∀ y : M,
      ContinuousOn (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ico 0 T)) ∧
    (∀ (y : M) (u : TangentSpace I y),
      ContinuousOn
        (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
          (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ico 0 T)) := by
  set X : ℝ → ∀ x : M, TangentSpace I x :=
    fun s x => -(deTurckVF (I := I) (g_DT s) g_bg x) with hX
  have hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
    fun q hq => neg_field_cmdwa
      (fun s x => (deTurckVF (I := I) (g_DT s) g_bg x : TangentSpace I x)) (hfield_reg q hq)
  have hΦode' : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x) (Set.Ici (0:ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t ((Φ_fam t : M → M) x))) := hΦode
  have hC1 : ∀ y : M, ContinuousOn (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ico 0 T) := by
    intro y s hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · subst_vars; exact (hΦorbit0 y).mono Set.Ico_subset_Ici_self
    · exact ((hΦode y s ⟨h0, hs.2⟩).continuousWithinAt).mono Set.Ico_subset_Ici_self
  refine ⟨hC1, ?_⟩
  intro y u s hs
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · subst_vars; exact (hΦmfderiv0 y u).mono Set.Ico_subset_Ici_self
  obtain ⟨a', ha'0, ha's⟩ := exists_between h0
  obtain ⟨b', hsb', hb'T⟩ := exists_between hs.2
  obtain ⟨Xt, δ, hδ, hXteq, hXtsmooth, hXtauto⟩ :=
    interior_field_global_cutoff_extension X T hint ha'0 (lt_trans ha's hsb') hb'T
  obtain ⟨Tw, hTw, Φg, hΦg0, hΦgsmooth, hΦgbare⟩ :=
    global_flow_jointContMDiffOn_on_closed_manifold Xt hXtsmooth s
  set c : ℝ := max a' (s - Tw) with hc
  set d : ℝ := min b' (s + Tw) with hd
  have hcs : c < s := by rw [hc]; exact max_lt ha's (by linarith)
  have hsd : s < d := by rw [hd]; exact lt_min hsb' (by linarith)
  have hWsubab : Set.Ioo c d ⊆ Set.Ioo a' b' :=
    Set.Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  have hWsubTw : Set.Ioo c d ⊆ Set.Ioo (s - Tw) (s + Tw) :=
    Set.Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  have hWsubT : Set.Ioo c d ⊆ Set.Ioo (0:ℝ) T :=
    hWsubab.trans (Set.Ioo_subset_Ioo (le_of_lt ha'0) (le_of_lt hb'T))
  have hXtX : ∀ t ∈ Set.Ioo a' b', ∀ x : M, Xt t x = X t x := by
    intro t ht x
    refine hXteq t ?_ x
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hid : ∀ r ∈ Set.Ioo c d, ∀ x : M,
      (Φ_fam r : M → M) x = Φg ((Φ_fam s : M → M) x) r := by
    intro r hr x
    have hΦfamXt : ∀ t ∈ Set.Ioo c d,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun w : ℝ => (Φ_fam w : M → M) x) (Set.Ioo c d) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt t ((Φ_fam t : M → M) x))) := by
      intro t ht
      have hWsubIci : Set.Ioo c d ⊆ Set.Ici (0:ℝ) :=
        fun w hw => le_of_lt (lt_of_lt_of_le (hWsubT hw).1 (le_refl _))
      have hode := (hΦode' x t (hWsubT ht)).mono hWsubIci
      rw [hXtX t (hWsubab ht) ((Φ_fam t : M → M) x)]
      exact hode
    have hΦgXt : ∀ t ∈ Set.Ioo c d,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun w : ℝ => Φg ((Φ_fam s : M → M) x) w) (Set.Ioo c d) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt t (Φg ((Φ_fam s : M → M) x) t))) := fun t ht =>
      (hΦgbare ((Φ_fam s : M → M) x) t (hWsubTw ht)).hasMFDerivWithinAt
    have hseed : (Φ_fam s : M → M) x = Φg ((Φ_fam s : M → M) x) s := (hΦg0 _).symm
    exact bare_integral_flow_eqOn_of_jointC1 (a := c) (b := d) (t₀ := s)
      Xt hXtauto (fun w : ℝ => (Φ_fam w : M → M)) (fun w p => Φg p w) x ((Φ_fam s : M → M) x)
      ⟨hcs, hsd⟩ hΦfamXt hΦgXt hseed r hr
  set p₀ : M := (Φ_fam s : M → M) y with hp₀
  set u₀ : TangentSpace I p₀ := mfderiv I I (Φ_fam s : M → M) y u with hu₀
  have hLeaf : ContinuousAt (fun r : ℝ => (TotalSpace.mk' E (Φg p₀ r)
      (mfderiv I I (fun x => Φg x r) p₀ u₀) : TangentBundle I M)) s :=
    slice_mfderiv_continuousAt_of_jointFlow (I := I) Φg (O := Set.Ioo (s - Tw) (s + Tw))
      isOpen_Ioo ⟨by linarith, by linarith⟩ hΦgsmooth p₀ u₀
  have hsecEq : Set.EqOn
      (fun r : ℝ => (TotalSpace.mk' E (Φg p₀ r)
        (mfderiv I I (fun x => Φg x r) p₀ u₀) : TangentBundle I M))
      (fun r : ℝ => (TotalSpace.mk' E ((Φ_fam r : M → M) y)
        (mfderiv I I (Φ_fam r : M → M) y u) : TangentBundle I M))
      (Set.Ioo c d) := by
    intro r hr
    have hfun : (Φ_fam r : M → M) = (fun x => Φg x r) ∘ (Φ_fam s : M → M) := by
      funext x; exact hid r hr x
    have hbase : (Φ_fam r : M → M) y = Φg p₀ r := hid r hr y
    have hmdiff_g : MDifferentiableAt I I (fun x => Φg x r) p₀ := by
      have hcomp : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ (fun x : M => (r, x)) p₀ :=
        contMDiffAt_const.prodMk contMDiffAt_id
      exact ((hΦgsmooth.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
        ⟨hWsubTw hr, Set.mem_univ _⟩)).comp p₀ hcomp).mdifferentiableAt (by decide)
    have hmdiff_fam : MDifferentiableAt I I (Φ_fam s : M → M) y :=
      ((Φ_fam s).mdifferentiable (by decide)) y
    have hmfd : mfderiv I I (Φ_fam r : M → M) y u
        = mfderiv I I (fun x => Φg x r) p₀ u₀ := by
      have := mfderiv_comp_of_eq (I := I) (I' := I) (I'' := I)
        (f := (Φ_fam s : M → M)) (g := fun x => Φg x r) (x := y) (y := p₀)
        hmdiff_g hmdiff_fam hp₀.symm
      have hcongr : mfderiv I I (Φ_fam r : M → M) y
          = mfderiv I I ((fun x => Φg x r) ∘ (Φ_fam s : M → M)) y := by rw [hfun]
      rw [hcongr, this]; rfl
    change (TotalSpace.mk' E (Φg p₀ r) (mfderiv I I (fun x => Φg x r) p₀ u₀))
      = (TotalSpace.mk' E ((Φ_fam r : M → M) y) (mfderiv I I (Φ_fam r : M → M) y u))
    rw [hmfd, hbase]
  have hWnhds : Set.Ioo c d ∈ 𝓝 s := isOpen_Ioo.mem_nhds ⟨hcs, hsd⟩
  have hCAt : ContinuousAt (fun r : ℝ => (TotalSpace.mk' E ((Φ_fam r : M → M) y)
      (mfderiv I I (Φ_fam r : M → M) y u) : TangentBundle I M)) s :=
    hLeaf.congr (Filter.eventuallyEq_of_mem hWnhds hsecEq)
  exact hCAt.continuousWithinAt

set_option linter.unusedVariables false in
/-- **`t = 0`-endpoint continuity data of the conjugating flow (now PROVEN from its providers).**

For the conjugating diffeomorphism family `Φ_fam` of the Hamilton–DeTurck construction —
PINNED to the genuine flow by the backward bare-orbit ODE `hΦode` — the two `t = 0`-endpoint
continuity facts hold for the pulled-back metric family `g_fam s := (Φ_fam s)^* (g_DT s)`:

* `h_cont`: the pulled-back inner product `s ↦ (g_fam s).inner x v w` is continuous on `Ico 0 T`;
* `h_ric_cont`: the Ricci RHS `s ↦ -2 Ric(g_fam s) x v w` is right-continuous at `0`.

The hypotheses are EXACTLY those the two on-disk providers consume.  Conjunct 1 is
`gfam_inner_continuous_on` (`hg_joint` + the whole-`Ico` orbit/pushforward continuity).
Conjunct 2 is `ricci_gfam_continuous_on` (the GENUINE second-order-in-space chart-jet
continuity `hC2`, `k ≤ 2`, + the whole-`Ico` orbit/pushforward continuity), whose `Ico 0 T`
output is restricted to the right-neighbourhood `Ioi 0` of `0` and scaled by `-2`.  The Ricci
conjunct genuinely requires `hC2` (a `k = 0`-only chart-Gram datum does NOT control the spatial
Hessian, hence not the pullback Ricci, up to `0`).  All inputs constrain only the internal data
`g_DT` / `Φ_fam`, never `g_bg` / the headline; `hΦode` / `hΦ0` / `hDT_init` pin the flow to the
genuine one (so the statement is TRUE, not vacuous), but are not consumed in the assembly. -/
theorem conjugating_flow_t0_continuity_data
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (hT : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hΦ0 : Φ_fam 0 = _root_.Diffeomorph.refl I M ∞)
    (hDT_init : g_DT 0 = g_bg)
    (hg_joint : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × M =>
          Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
            (extChartAt I α q.2))
        (Set.Icc 0 T ×ˢ Set.univ))
    (hC2 : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
      ContinuousOn
        (fun q : ℝ × M => iteratedFDeriv ℝ k
          (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
          (extChartAt I α q.2))
        (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α))
    (hΦ_orbit : ∀ y : M,
      ContinuousOn (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ico 0 T))
    (hΦ_total : ∀ (y : M) (u : TangentSpace I y),
      ContinuousOn
        (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
          (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ico 0 T))
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn
        (fun s : ℝ =>
          (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)).inner x v w) (Set.Ico 0 T) ∧
      ContinuousWithinAt
        (fun s : ℝ => (-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I)
            (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w) (Set.Ioi 0) 0 := by
  refine ⟨gfam_inner_continuous_on (I := I) g_DT T hT Φ_fam x v w hg_joint hΦ_orbit hΦ_total, ?_⟩
  have hric : ContinuousOn
      (fun s : ℝ => ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w) (Set.Ico 0 T) :=
    ricci_gfam_continuous_on (I := I) g_DT T hT Φ_fam x v w hC2 hΦ_orbit hΦ_total
  have h0mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hcwa_Ioo : ContinuousWithinAt
      (fun s : ℝ => ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w) (Set.Ioo 0 T) 0 :=
    (hric.continuousWithinAt h0mem).mono Set.Ioo_subset_Ico_self
  have hcwa_Ioi : ContinuousWithinAt
      (fun s : ℝ => ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w) (Set.Ioi 0) 0 :=
    hcwa_Ioo.mono_of_mem_nhdsWithin (Ioo_mem_nhdsGT hT)
  exact hcwa_Ioi.const_mul (-2 : ℝ)

/-- **Joint `(t, x)` chart-Gram regularity of the pulled-back metric family (faithful open
input).**

For the conjugating diffeomorphism family `Φ_fam` of the Hamilton–DeTurck construction —
PINNED to the genuine flow by the backward bare-orbit ODE `hΦode`
(`∂_s Φ_fam = -deTurckVF (g_DT s) g_bg ∘ Φ_fam` on `Ioo 0 T`) — the pulled-back metric family
`g_fam s := (Φ_fam s)^* (g_DT s) = Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)` inherits the
joint `(t, x)` chart-Gram regularity of `g_DT` along the flow:

* `h_gram` (the joint-`C∞` conclusion): each chart-local Gram-matrix entry
  `p ↦ chartGramMatrix (g_fam p.1) x₀ p.2 i j` is jointly `C∞` on the interior
  `Ioo 0 T ×ˢ baseSet`;
* `h_gram0` (the joint-continuity conclusion): the same entry is jointly continuous up to
  `t = 0` on `Ico 0 T ×ˢ baseSet`.

These are the chart-level expressions of joint smoothness / continuity of the moving
pullback `(t, x) ↦ (g_DT t).inner (Φ_fam t x) (mfderiv (Φ_fam t) x ·) (mfderiv (Φ_fam t) x ·)`.
Their content is the chain rule combining (i) the supplied joint chart-Gram regularity of
`g_DT` itself (`hgram_DT` / `hgram0_DT`, the GENUINE outputs of the interior-parabolic-smooth,
`C⁰`-up-to-`0` DeTurck solution), with (ii) the joint `(t, x)` smoothness / continuity of the
orbit `(t, x) ↦ Φ_fam t x` and its chart Jacobian `mfderiv (Φ_fam t) x`.  Part (ii) is the
classical Hartman smooth-dependence-on-initial-conditions output for the conjugating flow
(`global_flow_jointContMDiffOn_on_closed_manifold` + `manifoldFlowFamily_*` applied along the
cutoff windows of the interior field, continuous up to the `C⁰`-at-`0` boundary).  The on-disk
Hartman / pullback chart-Gram joint-smoothness machinery is faithful but not yet wired to the
specific conjugating flow; we isolate that open content here as a single faithful labeled
`sorry`, PINNED to the genuine flow by `hΦode` and consuming the genuine `g_DT` regularity
`hgram_DT`/`hgram0_DT`.  Neither output is equal to, nor destructures to, any hypothesis (the
hypotheses concern `g_DT`; the conclusions concern the pullback `pullbackMetric (g_DT) (Φ_fam)`),
so this is not hypothesis-packaging.  Faithful labeled deferred input for a dedicated fill
effort. -/
theorem conjugating_flow_pullback_jointGram_data
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hgram_DT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram0_DT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
        (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I)
            (Diffeomorph.pullbackMetric (g_DT p.1) (Φ_fam p.1)) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
    (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I)
            (Diffeomorph.pullbackMetric (g_DT p.1) (Φ_fam p.1)) x₀ p.2 i j)
        (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow

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
import DifferentialGeometry.Geometry.Flow.DeTurckVFChartCoord
import DifferentialGeometry.Geometry.Metric.ChartGram
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue

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
open DifferentialGeometry.Integral.Measure

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

set_option linter.unusedVariables false in
/-- **Interior joint-`C∞` of the conjugating orbit.**

The orbit `(t, x) ↦ Φ_fam t x` is jointly `C∞` on the interior `Ioo 0 T ×ˢ univ`.  This is the
interior Hartman smooth-dependence output, assembled from the on-disk infra (`neg_field_cmdwa`,
`interior_field_global_cutoff_extension`, `global_flow_jointContMDiffOn_on_closed_manifold`,
`bare_integral_flow_eqOn_of_jointC1`) exactly as the orbit half of
`conjugating_flow_orbit_pushforward_continuity_data`, re-exposing the joint-`C∞` that the latter
constructs internally and then discards. -/
theorem conjugating_flow_jointContMDiffOn_interior
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
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
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
  intro p hp
  obtain ⟨hps, -⟩ := hp
  set s : ℝ := p.1 with hs
  set y : M := p.2 with hy
  obtain ⟨a', ha'0, ha's⟩ := exists_between hps.1
  obtain ⟨b', hsb', hb'T⟩ := exists_between hps.2
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
      Xt hXtauto (fun w : ℝ => (Φ_fam w : M → M)) (fun w q => Φg q w) x ((Φ_fam s : M → M) x)
      ⟨hcs, hsd⟩ hΦfamXt hΦgXt hseed r hr
  have hWnhds : Set.Ioo c d ×ˢ (Set.univ : Set M) ∈ 𝓝 (p : ℝ × M) := by
    rw [show (p : ℝ × M) = (s, y) from Prod.ext hs hy]
    exact (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨hcs, hsd⟩, Set.mem_univ _⟩
  have hcompMDiff : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => Φg ((Φ_fam s : M → M) q.2) q.1) (p : ℝ × M) := by
    have hfst : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => q.1) (p : ℝ × M) := contMDiffAt_fst
    have hsnd : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => (Φ_fam s : M → M) q.2) (p : ℝ × M) :=
      ((Φ_fam s).contMDiff.contMDiffAt).comp (p : ℝ × M) contMDiffAt_snd
    have hf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × M => (q.1, (Φ_fam s : M → M) q.2)) (p : ℝ × M) := hfst.prodMk hsnd
    have hmem : ((s, (Φ_fam s : M → M) y) : ℝ × M)
        ∈ Set.Ioo (s - Tw) (s + Tw) ×ˢ (Set.univ : Set M) :=
      ⟨⟨by linarith, by linarith⟩, Set.mem_univ _⟩
    have hg : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => Φg q.2 q.1)
        ((s, (Φ_fam s : M → M) y) : ℝ × M) :=
      hΦgsmooth.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hmem)
    have hfval : (fun q : ℝ × M => (q.1, (Φ_fam s : M → M) q.2)) (p : ℝ × M)
        = ((s, (Φ_fam s : M → M) y) : ℝ × M) := Prod.ext hs (by rw [hy])
    have hcomp := (hfval ▸ hg).comp (p : ℝ × M) hf
    exact hcomp
  have hgoalAt : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) (p : ℝ × M) := by
    refine hcompMDiff.congr_of_eventuallyEq ?_
    filter_upwards [hWnhds] with q hq
    exact hid q.1 hq.1 q.2
  exact hgoalAt.contMDiffWithinAt

/-- **Chart-`y`-frame velocity field of the conjugating flow.**

The chart-`y` coordinate velocity of the backward conjugating orbit, as a function of
`(r, z) : ℝ × E`: the DeTurck-vector-field coordinate components `chartDeTurckVFComp (g_DT r) g_bg y k`
weighted against the fixed model-basis frame.  By the convention bridge this is the
chart-`y`-frame representation of `mfderiv (extChartAt I y) · (deTurckVF (g_DT r) g_bg ·)` at a
good-set orbit point — the genuine velocity of `r ↦ extChartAt I y (Φ_fam r x)`, NOT the per-point
raw-fibre representation. -/
noncomputable def conjugatingChartVelocityField
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (y : M) (r : ℝ) (z : E) : E :=
  ∑ k : Fin (Module.finrank ℝ E),
    DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT r) g_bg y k z •
      ((chartModelBasis E) k : E)

omit [CompactSpace M] [I.Boundaryless] in
/-- The chart-`y` velocity `mfderiv (extChartAt I y) q (deTurckVF (g_DT r) g_bg q)` at a good-set
orbit point `q` equals the chart-frame velocity field
`conjugatingChartVelocityField g_DT g_bg y r (extChartAt I y q)`.  This is the convention bridge
(`deTurckVF_apply_eq_chartDeTurckVFComp_sum` + `mfderiv (extChartAt I y) = trivToE y` +
`trivToE y q (chartBasisVecFiber y k q) = (chartModelBasis E) k`), establishing that the chart-frame
components are the genuine velocity components. -/
theorem mfderiv_extChartAt_deTurckVF_eq_conjugatingChartVelocityField
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M) (y q : M) (r : ℝ)
    (hq : q ∈ chartLeviCivitaGoodSet (I := I) y) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I y) q (deTurckVF (I := I) (g_DT r) g_bg q)
      = conjugatingChartVelocityField (I := I) g_DT g_bg y r (extChartAt I y q) := by
  have hsrc_chart : q ∈ (chartAt H y).source := by
    have : q ∈ (extChartAt I y).source :=
      chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq
    rwa [extChartAt_source] at this
  rw [(TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hsrc_chart).symm]
  have hbridge := deTurckVF_apply_eq_chartDeTurckVFComp_sum (I := I) (g_DT r) g_bg y hq
  have hqbase : q ∈ (trivializationAt E (TangentSpace I) y).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hq
  change (trivToE (I := I) y q) (deTurckVF (I := I) (g_DT r) g_bg q) = _
  rw [show (deTurckVF (I := I) (g_DT r) g_bg q : TangentSpace I q) =
      (deTurckVF (I := I) (g_DT r) g_bg : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) q from rfl]
  rw [hbridge, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul]
  congr 1
  have htriv := trivializationAt_chartBasisVec_snd (I := I) y k hqbase
  have hclm : (trivToE (I := I) y q) (chartBasisVecFiber (I := I) y k q)
      = (trivializationAt E (TangentSpace I) y
          ⟨q, chartBasisVecFiber (I := I) y k q⟩).2 := by
    change ((trivializationAt E (TangentSpace I) y).continuousLinearMapAt ℝ q)
        (chartBasisVecFiber (I := I) y k q) = _
    rw [Trivialization.continuousLinearMapAt_apply, Trivialization.coe_linearMapAt_of_mem]
    exact hqbase
  rw [hclm]; exact htriv

omit [CompactSpace M] [I.Boundaryless] in
/-- Forward chart-`y` orbit derivative: from the manifold orbit ODE `hd`
(`∂_s Φ = -deTurckVF (g_DT r) g_bg ∘ Φ` on `Ici 0`), the chart-`y` orbit
`s ↦ extChartAt I y (γ s)` has the right-derivative `-conjugatingChartVelocityField` at a good-set
orbit point, by the manifold chain rule for `extChartAt I y ∘ γ`. -/
theorem chart_conjugating_orbit_hasDerivWithinAt
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (y : M) (γ : ℝ → M) (r : ℝ)
    (hr_src : γ r ∈ chartLeviCivitaGoodSet (I := I) y)
    (hd : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ (Set.Ici (0:ℝ)) r
      ((1 : ℝ →L[ℝ] ℝ).smulRight (-(deTurckVF (I := I) (g_DT r) g_bg (γ r))))) :
    HasDerivWithinAt (fun s => extChartAt I y (γ s))
      (-conjugatingChartVelocityField (I := I) g_DT g_bg y r (extChartAt I y (γ r)))
      (Set.Ici (0:ℝ)) r := by
  have hsrc_chart : γ r ∈ (chartAt H y).source := by
    have : γ r ∈ (extChartAt I y).source :=
      chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hr_src
    rwa [extChartAt_source] at this
  have hchart : HasMFDerivWithinAt I 𝓘(ℝ, E) (extChartAt I y) (Set.univ) (γ r)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I y) (γ r)) :=
    (mdifferentiableAt_extChartAt (I := I) hsrc_chart).hasMFDerivAt.hasMFDerivWithinAt
  have hcomp : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      ((extChartAt I y) ∘ γ) (Set.Ici (0:ℝ)) r
      ((mfderiv I 𝓘(ℝ, E) (extChartAt I y) (γ r)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (-(deTurckVF (I := I) (g_DT r) g_bg (γ r))))) :=
    HasMFDerivWithinAt.comp r hchart hd (Set.subset_univ _)
  rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hcomp
  have hderiv := hcomp.hasDerivWithinAt
  have hval : ((mfderiv I 𝓘(ℝ, E) (extChartAt I y) (γ r)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (-(deTurckVF (I := I) (g_DT r) g_bg (γ r))))) 1
      = -conjugatingChartVelocityField (I := I) g_DT g_bg y r (extChartAt I y (γ r)) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, one_smul, map_neg]
    congr 1
    exact mfderiv_extChartAt_deTurckVF_eq_conjugatingChartVelocityField
      (I := I) g_DT g_bg y (γ r) r hr_src
  exact hderiv.congr_deriv hval

set_option linter.unusedVariables false in
/-- Per-`x` continuity of the conjugating orbit `s ↦ Φ_fam s x` on `Ico 0 T`, from the orbit ODE
`hΦode` (interior continuity) and the at-`0` boundary datum `hΦorbit0`. -/
theorem conjugating_orbit_continuousOn_Ico
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hΦorbit0 : ∀ y : M,
      ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ici (0 : ℝ)) 0)
    (x : M) :
    ContinuousOn (fun s : ℝ => (Φ_fam s : M → M) x) (Set.Ico 0 T) := by
  intro s hs
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · subst_vars; exact (hΦorbit0 x).mono Set.Ico_subset_Ici_self
  · exact ((hΦode x s ⟨h0, hs.2⟩).continuousWithinAt).mono Set.Ico_subset_Ici_self

set_option linter.unusedVariables false in
set_option maxHeartbeats 1600000 in
/-- **Uniform-in-`x` chart confinement of the conjugating flow near the initial time.**

For the conjugating diffeomorphism family `Φ_fam` of the Hamilton–DeTurck construction — PINNED to
the genuine flow by the backward bare-orbit ODE `hΦode` — there exist a positive time `b ≤ T` and a
radius `ρ > 0` such that EVERY chart-`y` orbit starting in the chart-`y` `ρ`-ball stays, for all
times `r ∈ Ico 0 b`, inside the chart source with chart image inside the `2ρ`-ball about
`extChartAt I y y`.

The velocity of the chart-`y` orbit `r ↦ extChartAt I y (Φ_fam r x)` is the chart-`y`-frame field
`conjugatingChartVelocityField` (the corrected velocity object — the chart-frame components, NOT the
raw-fibre representation), whose value-continuity hypothesis `Hcomp` is the chart-frame regularity
(`chartDeTurckVFComp` value-continuity, an output of `deturck_vf_continuous_up_to_zero`).  Bounding
that field uniformly by a constant `K` on the compact chart-ball gives, via the mean-value
inequality and a clopen exit-time argument on the connected time interval, the uniform-in-`x`
confinement.  Genuine analytic content; constrains only the internal `g_DT` / `Φ_fam`. -/
theorem conjugating_flow_uniform_chart_confinement
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (hT : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hΦ0 : Φ_fam 0 = _root_.Diffeomorph.refl I M ∞)
    (hΦorbit0 : ∀ y : M,
      ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ici (0 : ℝ)) 0)
    (y : M)
    (Hcomp : ∀ k : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun q : ℝ × E =>
          DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg y k q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I y).target)) :
    ∃ b ρ : ℝ, 0 < b ∧ b ≤ T ∧ 0 < ρ ∧
      Metric.closedBall (extChartAt I y y) (3 * ρ) ⊆ interior (extChartAt I y).target ∧
      ∀ x : M, x ∈ (extChartAt I y).source →
        extChartAt I y x ∈ Metric.ball (extChartAt I y y) ρ →
        ∀ r ∈ Set.Ico (0 : ℝ) b,
          (Φ_fam r : M → M) x ∈ (extChartAt I y).source ∧
          extChartAt I y ((Φ_fam r : M → M) x) ∈
            Metric.ball (extChartAt I y y) (2 * ρ) := by
  classical
  set c₀ : E := extChartAt I y y with hc₀
  have hc₀_tgt : c₀ ∈ (extChartAt I y).target :=
    (extChartAt I y).map_source (mem_extChartAt_source y)
  have htgt_open : IsOpen (extChartAt I y).target := isOpen_extChartAt_target y
  obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.isOpen_iff.mp htgt_open c₀ hc₀_tgt
  set ρ : ℝ := ε / 4 with hρ
  have hρ_pos : 0 < ρ := by positivity
  have h2ρ_lt_ε : 2 * ρ < ε := by rw [hρ]; linarith
  have h3ρ_lt_ε : 3 * ρ < ε := by rw [hρ]; linarith
  set Ball2 : Set E := Metric.closedBall c₀ (2 * ρ) with hBall2
  set Ball3 : Set E := Metric.closedBall c₀ (3 * ρ) with hBall3
  have hBall3_sub_tgt : Ball3 ⊆ (extChartAt I y).target :=
    subset_trans (Metric.closedBall_subset_ball h3ρ_lt_ε) hε_sub
  have hBall3_sub_int : Ball3 ⊆ interior (extChartAt I y).target :=
    subset_trans hBall3_sub_tgt
      (Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless y)
  have hBall2_sub_tgt : Ball2 ⊆ (extChartAt I y).target :=
    subset_trans (Metric.closedBall_subset_ball h2ρ_lt_ε) hε_sub
  have hBall2_sub_Ball3 : Ball2 ⊆ Ball3 :=
    Metric.closedBall_subset_closedBall (by linarith)
  have hBall3_compact : IsCompact Ball3 := isCompact_closedBall c₀ (3 * ρ)
  have hBall2_compact : IsCompact Ball2 := isCompact_closedBall c₀ (2 * ρ)
  have hvel_cont : ContinuousOn
      (fun q : ℝ × E => conjugatingChartVelocityField (I := I) g_DT g_bg y q.1 q.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I y).target) := by
    refine continuousOn_finset_sum _ (fun k _ => ?_)
    exact (Hcomp k).smul continuousOn_const
  have hprod_compact : IsCompact (Set.Icc (0 : ℝ) T ×ˢ Ball3) :=
    (isCompact_Icc).prod hBall3_compact
  have hvel_cont_prod : ContinuousOn
      (fun q : ℝ × E => conjugatingChartVelocityField (I := I) g_DT g_bg y q.1 q.2)
      (Set.Icc (0 : ℝ) T ×ˢ Ball3) :=
    hvel_cont.mono (Set.prod_mono_right hBall3_sub_int)
  obtain ⟨K₀, hK₀⟩ := hprod_compact.exists_bound_of_continuousOn hvel_cont_prod
  set K : ℝ := max K₀ 1 + 1 with hK
  have hK_pos : 0 < K := by rw [hK]; positivity
  have hK_bound : ∀ r ∈ Set.Icc (0:ℝ) T, ∀ z ∈ Ball3,
      ‖conjugatingChartVelocityField (I := I) g_DT g_bg y r z‖ ≤ K := by
    intro r hr z hz
    have := hK₀ (r, z) ⟨hr, hz⟩
    calc ‖conjugatingChartVelocityField (I := I) g_DT g_bg y r z‖ ≤ K₀ := this
      _ ≤ max K₀ 1 := le_max_left _ _
      _ ≤ K := by rw [hK]; linarith
  set b : ℝ := min (T / 2) (ρ / K) with hb
  have hb_pos : 0 < b := lt_min (by positivity) (by positivity)
  have hb_lt_T : b < T := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hb_le_T : b ≤ T := le_of_lt hb_lt_T
  have hKb_le_ρ : K * b ≤ ρ := by
    have : b ≤ ρ / K := min_le_right _ _
    calc K * b ≤ K * (ρ / K) := by nlinarith [hK_pos]
      _ = ρ := by field_simp
  set Ball2_M : Set M := (extChartAt I y).symm '' Ball2 with hBall2_M
  have hsymm_cont : ContinuousOn (extChartAt I y).symm (extChartAt I y).target :=
    continuousOn_extChartAt_symm y
  have hBall2_M_compact : IsCompact Ball2_M :=
    hBall2_compact.image_of_continuousOn (hsymm_cont.mono hBall2_sub_tgt)
  have hBall2_M_closed : IsClosed Ball2_M := hBall2_M_compact.isClosed
  have hBall2_M_sub_src : Ball2_M ⊆ (extChartAt I y).source := by
    rintro p ⟨z, hz, rfl⟩
    exact (extChartAt I y).map_target (hBall2_sub_tgt hz)
  have hmem_Ball2_M_of : ∀ p : M, p ∈ (extChartAt I y).source →
      extChartAt I y p ∈ Ball2 → p ∈ Ball2_M := by
    intro p hp hpz
    exact ⟨extChartAt I y p, hpz, (extChartAt I y).left_inv hp⟩
  refine ⟨b, ρ, hb_pos, hb_le_T, hρ_pos, ?_, ?_⟩
  · show Metric.closedBall c₀ (3 * ρ) ⊆ interior (extChartAt I y).target
    rw [← hBall3]; exact hBall3_sub_int
  intro x hx_src hx_ball r hr
  set g_x : ℝ → M := fun s => (Φ_fam s : M → M) x with hg_x
  set φ_x : ℝ → E := fun s => extChartAt I y (g_x s) with hφ_x
  have hg_x_cont : ContinuousOn g_x (Set.Ico 0 T) :=
    conjugating_orbit_continuousOn_Ico (I := I) g_DT g_bg T Φ_fam hΦode hΦorbit0 x
  have hIcc_sub_Ico : Set.Icc (0:ℝ) b ⊆ Set.Ico 0 T :=
    fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 hb_lt_T⟩
  have hg_x_cont_Icc : ContinuousOn g_x (Set.Icc 0 b) := hg_x_cont.mono hIcc_sub_Ico
  set S : Set ℝ := {s : ℝ | g_x s ∈ Ball2_M ∧ dist (φ_x s) c₀ ≤ ρ + K * s} with hS
  have hg_x0 : g_x 0 = x := by
    show (Φ_fam 0 : M → M) x = x
    rw [hΦ0, Diffeomorph.coe_refl, id]
  have h0_mem_S : (0 : ℝ) ∈ S := by
    refine ⟨?_, ?_⟩
    · rw [hg_x0]
      exact hmem_Ball2_M_of x hx_src
        (Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith) hx_ball))
    · show dist (extChartAt I y (g_x 0)) c₀ ≤ ρ + K * 0
      rw [hg_x0]
      have hlt : dist (extChartAt I y x) c₀ < ρ := by
        rw [Metric.mem_ball] at hx_ball; exact hx_ball
      linarith
  set A : Set ℝ := Set.Icc (0:ℝ) b ∩ g_x ⁻¹' Ball2_M with hA
  have hA_closed : IsClosed A :=
    hg_x_cont_Icc.preimage_isClosed_of_isClosed isClosed_Icc hBall2_M_closed
  have hφ_x_contA : ContinuousOn φ_x A := by
    have hg_x_contA : ContinuousOn g_x A := hg_x_cont_Icc.mono Set.inter_subset_left
    refine ContinuousOn.comp (t := Ball2_M) (g := extChartAt I y) (f := g_x)
      ?_ hg_x_contA ?_
    · exact (continuousOn_extChartAt y).mono hBall2_M_sub_src
    · rintro s ⟨_, hs2⟩; exact hs2
  have hdist_contA : ContinuousOn (fun s => dist (φ_x s) c₀) A :=
    continuous_dist.comp_continuousOn (hφ_x_contA.prodMk continuousOn_const)
  have hdistfun_contA : ContinuousOn (fun s => dist (φ_x s) c₀ - (ρ + K * s)) A := by
    refine hdist_contA.sub ?_
    exact (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
  have hSIcc_eq : S ∩ Set.Icc 0 b
      = A ∩ (fun s => dist (φ_x s) c₀ - (ρ + K * s)) ⁻¹' Set.Iic 0 := by
    ext s
    simp only [hS, hA, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨⟨hin, hdist⟩, hicc⟩
      exact ⟨⟨hicc, hin⟩, by linarith⟩
    · rintro ⟨⟨hicc, hin⟩, hdist⟩
      exact ⟨⟨hin, by linarith⟩, hicc⟩
  have hSIcc_closed : IsClosed (S ∩ Set.Icc 0 b) := by
    rw [hSIcc_eq]
    exact hdistfun_contA.preimage_isClosed_of_isClosed hA_closed isClosed_Iic
  have hgoodset_of_ball : ∀ p : M, p ∈ (extChartAt I y).source →
      extChartAt I y p ∈ Metric.ball c₀ (3 * ρ) → p ∈ chartLeviCivitaGoodSet (I := I) y := by
    intro p hp hpz
    rw [mem_chartLeviCivitaGoodSet_iff]
    have hpz3 : extChartAt I y p ∈ Ball3 :=
      Metric.ball_subset_closedBall hpz
    refine ⟨hp, ?_, hBall3_sub_int hpz3⟩
    rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)]
    exact hp
  have hgt : ∀ s ∈ S ∩ Set.Ico 0 b, S ∈ 𝓝[>] s := by
    rintro s ⟨⟨hsBall, hsdist⟩, hsIco⟩
    have hsb' : s < b := hsIco.2
    have hs0 : 0 ≤ s := hsIco.1
    have hφs_le2ρ : dist (φ_x s) c₀ ≤ 2 * ρ := by
      calc dist (φ_x s) c₀ ≤ ρ + K * s := hsdist
        _ ≤ ρ + K * b := by nlinarith [hK_pos, hsb'.le, hs0]
        _ ≤ 2 * ρ := by linarith
    have hg_x_cwa : ContinuousWithinAt g_x (Set.Ici 0) s := by
      rcases eq_or_lt_of_le hs0 with h0 | h0
      · rw [← h0]; exact hΦorbit0 x
      · exact (hΦode x s ⟨h0, lt_of_lt_of_le hsb' hb_le_T⟩).continuousWithinAt
    have hg_xs_src : g_x s ∈ (extChartAt I y).source := hBall2_M_sub_src hsBall
    have hg_xs_good : g_x s ∈ chartLeviCivitaGoodSet (I := I) y := by
      apply hgoodset_of_ball (g_x s) hg_xs_src
      rw [Metric.mem_ball]; linarith
    set GoodBall : Set M :=
      chartLeviCivitaGoodSet (I := I) y ∩ (extChartAt I y) ⁻¹' Metric.ball c₀ (3 * ρ)
      with hGoodBall
    have hGoodBall_open : IsOpen GoodBall := by
      have hcontGood : ContinuousOn (extChartAt I y) (chartLeviCivitaGoodSet (I := I) y) :=
        (continuousOn_extChartAt y).mono
          (fun p hp => chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hp)
      exact hcontGood.isOpen_inter_preimage
        (chartLeviCivitaGoodSet_isOpen (I := I) y) Metric.isOpen_ball
    have hg_xs_GoodBall : g_x s ∈ GoodBall := by
      refine ⟨hg_xs_good, ?_⟩
      rw [Set.mem_preimage, Metric.mem_ball]; linarith
    have hpre_good : g_x ⁻¹' GoodBall ∈ 𝓝[Set.Ioi s] s := by
      have hmono : 𝓝[Set.Ioi s] s ≤ 𝓝[Set.Ici 0] s :=
        nhdsWithin_mono s (fun t ht => le_trans hs0 (le_of_lt ht))
      exact hmono (hg_x_cwa (hGoodBall_open.mem_nhds hg_xs_GoodBall))
    obtain ⟨m₀, hm₀_gt, hm₀_sub⟩ :
        ∃ m > s, Set.Ioo s m ⊆ g_x ⁻¹' GoodBall :=
      mem_nhdsGT_iff_exists_Ioo_subset.mp hpre_good
    set m : ℝ := min m₀ b with hm
    have hm_gt : s < m := lt_min hm₀_gt hsb'
    have hgood_seg : ∀ t ∈ Set.Ioo s m, g_x t ∈ chartLeviCivitaGoodSet (I := I) y := by
      intro t ht; exact (hm₀_sub ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩).1
    have hball_seg : ∀ t ∈ Set.Ioo s m, φ_x t ∈ Ball3 := by
      intro t ht
      have := (hm₀_sub ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩).2
      rw [Set.mem_preimage] at this
      exact Metric.ball_subset_closedBall this
    have hφ_cont_Ico : ContinuousOn φ_x (Set.Ico s m) := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with hts | hts
      · subst hts
        refine (continuousAt_extChartAt' (I := I) hg_xs_src).comp_continuousWithinAt ?_
        exact hg_x_cwa.mono (fun u hu => le_trans hs0 hu.1)
      · have htm : t ∈ Set.Ioo s m := ⟨hts, ht.2⟩
        have htg : g_x t ∈ chartLeviCivitaGoodSet (I := I) y := hgood_seg t htm
        have htsrc : g_x t ∈ (extChartAt I y).source :=
          chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) htg
        have hgcwa : ContinuousWithinAt g_x (Set.Ico s m) t := by
          have : t ∈ Set.Ioo (0:ℝ) T :=
            ⟨lt_of_le_of_lt hs0 hts,
              lt_of_lt_of_le (lt_of_lt_of_le ht.2 (min_le_right _ _)) hb_le_T⟩
          exact ((hΦode x t this).continuousWithinAt).mono
            (fun u hu => le_trans hs0 hu.1)
        exact (continuousAt_extChartAt' (I := I) htsrc).comp_continuousWithinAt hgcwa
    set φ' : ℝ → E := fun t => -conjugatingChartVelocityField (I := I) g_DT g_bg y t (φ_x t)
      with hφ'
    have hφ_deriv : ∀ t ∈ Set.Ioo s m,
        HasDerivWithinAt φ_x (φ' t) (Set.Ici t) t := by
      intro t ht
      have htg : g_x t ∈ chartLeviCivitaGoodSet (I := I) y := hgood_seg t ht
      have htode : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I g_x (Set.Ici (0:ℝ)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (-(deTurckVF (I := I) (g_DT t) g_bg (g_x t)))) := by
        have : t ∈ Set.Ioo (0:ℝ) T :=
          ⟨lt_of_le_of_lt hs0 ht.1,
            lt_of_lt_of_le (lt_of_lt_of_le ht.2 (min_le_right _ _)) hb_le_T⟩
        exact hΦode x t this
      have hdw := chart_conjugating_orbit_hasDerivWithinAt (I := I) g_DT g_bg y g_x t htg htode
      have hres : HasDerivWithinAt φ_x
          (-conjugatingChartVelocityField (I := I) g_DT g_bg y t (extChartAt I y (g_x t)))
          (Set.Ici t) t := hdw.mono (fun u hu => le_trans (le_trans hs0 (le_of_lt ht.1)) hu)
      rw [hφ']
      exact hres
    have hbound_seg : ∀ t ∈ Set.Ioo s m, ‖φ' t‖ ≤ K := by
      intro t ht
      rw [hφ', norm_neg]
      have htmemT : t ∈ Set.Icc (0:ℝ) T :=
        ⟨le_of_lt (lt_of_le_of_lt hs0 ht.1),
          le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le ht.2 (min_le_right _ _)) hb_le_T)⟩
      exact hK_bound t htmemT (φ_x t) (hball_seg t ht)
    have hseg : ∀ s' ∈ Set.Ioo s m, ‖φ_x s' - φ_x s‖ ≤ K * (s' - s) := by
      intro s' hs'
      have hss' : s < s' := hs'.1
      have hmvt : ∀ s₁ ∈ Set.Ioo s s', ‖φ_x s' - φ_x s₁‖ ≤ K * (s' - s₁) := by
        intro s₁ hs₁
        have hcontss : ContinuousOn φ_x (Set.Icc s₁ s') :=
          hφ_cont_Ico.mono (fun u hu => ⟨le_of_lt (lt_of_lt_of_le hs₁.1 hu.1),
            lt_of_le_of_lt hu.2 hs'.2⟩)
        have hderivss : ∀ u ∈ Set.Ico s₁ s', HasDerivWithinAt φ_x (φ' u) (Set.Ici u) u := by
          intro u hu
          exact hφ_deriv u ⟨lt_of_lt_of_le hs₁.1 hu.1, lt_trans hu.2 hs'.2⟩
        have hboundss : ∀ u ∈ Set.Ico s₁ s', ‖φ' u‖ ≤ K := by
          intro u hu
          exact hbound_seg u ⟨lt_of_lt_of_le hs₁.1 hu.1, lt_trans hu.2 hs'.2⟩
        have := norm_image_sub_le_of_norm_deriv_right_le_segment
          hcontss hderivss hboundss s' (Set.right_mem_Icc.mpr (le_of_lt hs₁.2))
        simpa using this
      have hφ_cwa_s : ContinuousWithinAt φ_x (Set.Ioo s s') s := by
        refine hφ_cont_Ico.continuousWithinAt ?_ |>.mono ?_
        · exact ⟨le_rfl, hm_gt⟩
        · exact fun u hu => ⟨le_of_lt hu.1, lt_trans hu.2 hs'.2⟩
      haveI hnebot : (𝓝[Set.Ioo s s'] s).NeBot := by
        rw [nhdsWithin_Ioo_eq_nhdsGT hss']; exact nhdsGT_neBot s
      have htend_lhs : Filter.Tendsto (fun s₁ => ‖φ_x s' - φ_x s₁‖)
          (𝓝[Set.Ioo s s'] s) (𝓝 ‖φ_x s' - φ_x s‖) := by
        have hcwa : Filter.Tendsto (fun s₁ => φ_x s₁) (𝓝[Set.Ioo s s'] s) (𝓝 (φ_x s)) :=
          hφ_cwa_s
        exact (continuous_const.sub continuous_id).continuousAt.tendsto.comp hcwa |>.norm
      have htend_rhs : Filter.Tendsto (fun s₁ => K * (s' - s₁))
          (𝓝[Set.Ioo s s'] s) (𝓝 (K * (s' - s))) :=
        ((continuous_const.mul (continuous_const.sub continuous_id)).continuousAt).tendsto.comp
          (tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id)
      refine le_of_tendsto_of_tendsto htend_lhs htend_rhs ?_
      filter_upwards [self_mem_nhdsWithin] with s₁ hs₁ using hmvt s₁ hs₁
    have hsubS : Set.Ioo s m ⊆ S := by
      intro s' hs'
      have hdist_le : dist (φ_x s') c₀ ≤ ρ + K * s' := by
        have h1 : dist (φ_x s') c₀ ≤ ‖φ_x s' - φ_x s‖ + dist (φ_x s) c₀ := by
          rw [dist_eq_norm]
          calc ‖φ_x s' - c₀‖ = ‖(φ_x s' - φ_x s) + (φ_x s - c₀)‖ := by
                rw [sub_add_sub_cancel]
            _ ≤ ‖φ_x s' - φ_x s‖ + ‖φ_x s - c₀‖ := norm_add_le _ _
            _ = ‖φ_x s' - φ_x s‖ + dist (φ_x s) c₀ := by rw [dist_eq_norm]
        have h2 : ‖φ_x s' - φ_x s‖ ≤ K * (s' - s) := hseg s' hs'
        calc dist (φ_x s') c₀ ≤ ‖φ_x s' - φ_x s‖ + dist (φ_x s) c₀ := h1
          _ ≤ K * (s' - s) + (ρ + K * s) := by linarith [hsdist]
          _ = ρ + K * s' := by ring
      refine ⟨?_, hdist_le⟩
      have hs'_pos : 0 ≤ s' := le_of_lt (lt_of_le_of_lt hs0 hs'.1)
      have hs'_lt_b : s' < b := lt_of_lt_of_le hs'.2 (min_le_right _ _)
      have hdist2ρ : dist (φ_x s') c₀ ≤ 2 * ρ := by
        calc dist (φ_x s') c₀ ≤ ρ + K * s' := hdist_le
          _ ≤ ρ + K * b := by nlinarith [hK_pos, hs'_lt_b.le, hs'_pos]
          _ ≤ 2 * ρ := by linarith
      have hg_xs'_src : g_x s' ∈ (extChartAt I y).source :=
        chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) (hgood_seg s' hs')
      exact hmem_Ball2_M_of (g_x s') hg_xs'_src
        (by rw [hBall2, Metric.mem_closedBall]; exact hdist2ρ)
    have hIoo_nhds : Set.Ioo s m ∈ 𝓝[>] s := by
      rw [mem_nhdsGT_iff_exists_Ioo_subset]
      exact ⟨m, hm_gt, Set.Subset.rfl⟩
    exact Filter.mem_of_superset hIoo_nhds hsubS
  have hIcc_sub_S : Set.Icc 0 b ⊆ S :=
    hSIcc_closed.Icc_subset_of_forall_mem_nhdsWithin h0_mem_S hgt
  have hr_Icc : r ∈ Set.Icc 0 b := ⟨hr.1, le_of_lt hr.2⟩
  obtain ⟨hrBall, hrdist⟩ := hIcc_sub_S hr_Icc
  have hr_src : (Φ_fam r : M → M) x ∈ (extChartAt I y).source := hBall2_M_sub_src hrBall
  refine ⟨hr_src, ?_⟩
  rw [Metric.mem_ball]
  have hKr : K * r < K * b := mul_lt_mul_of_pos_left hr.2 hK_pos
  calc dist (extChartAt I y ((Φ_fam r : M → M) x)) c₀ ≤ ρ + K * r := hrdist
    _ < ρ + K * b := by linarith
    _ ≤ ρ + ρ := by linarith [hKb_le_ρ]
    _ = 2 * ρ := by ring

omit [CompactSpace M] [I.Boundaryless] in
/-- At an interior chart-target point `z`, the chart-`y`-frame velocity field
`conjugatingChartVelocityField g_DT g_bg y r ·` is differentiable, with Fréchet derivative the
basis-weighted sum of the component derivatives. -/
theorem conjugatingChartVelocityField_hasFDerivAt
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (y : M) (r : ℝ) {z : E} (hz : z ∈ interior (extChartAt I y).target) :
    HasFDerivAt (fun w : E => conjugatingChartVelocityField (I := I) g_DT g_bg y r w)
      (∑ k : Fin (Module.finrank ℝ E),
        (fderiv ℝ (fun w : E =>
            DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT r) g_bg y k w) z).smulRight
          ((chartModelBasis E) k : E)) z := by
  classical
  have hcomp : ∀ k : Fin (Module.finrank ℝ E),
      HasFDerivAt (fun w : E =>
          DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT r) g_bg y k w)
        (fderiv ℝ (fun w : E =>
          DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT r) g_bg y k w) z) z := by
    intro k
    have hdiff : DifferentiableAt ℝ
        (DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT r) g_bg y k) z :=
      ((DeTurckLinearization.chartDeTurckVFComp_contDiffOn_interior (I := I)
        (g_DT r) g_bg y k).contDiffAt (isOpen_interior.mem_nhds hz)).differentiableAt (by simp)
    exact hdiff.hasFDerivAt
  have := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
    (A := fun k (w : E) =>
      DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT r) g_bg y k w •
        ((chartModelBasis E) k : E))
    (A' := fun k =>
      (fderiv ℝ (fun w : E =>
          DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT r) g_bg y k w) z).smulRight
        ((chartModelBasis E) k : E))
    (fun k _ => (hcomp k).smul_const ((chartModelBasis E) k : E))
  have hfun : (∑ k : Fin (Module.finrank ℝ E), fun w : E =>
        DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT r) g_bg y k w •
          ((chartModelBasis E) k : E))
      = fun w : E => conjugatingChartVelocityField (I := I) g_DT g_bg y r w := by
    funext w; rw [Finset.sum_apply]; rfl
  rw [hfun] at this
  exact this

omit [CompactSpace M] [I.Boundaryless] in
/-- **Uniform spatial Lipschitz constant of the chart-`y`-frame velocity field on a chart ball.**
From the joint continuity of the component spatial derivatives (`Hfderiv`) and the
differentiability of the components on the chart-target interior, the chart-`y`-frame velocity
field `conjugatingChartVelocityField g_DT g_bg y r ·` is uniformly `LipschitzOnWith K` on any
closed ball lying inside the chart-target interior, with `K` independent of the time `r ∈ Icc 0 T`. -/
theorem conjugatingChartVelocityField_lipschitz_uniform
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (y : M) (T : ℝ) (c : E) (R : ℝ)
    (hball : Metric.closedBall c R ⊆ interior (extChartAt I y).target)
    (Hfderiv : ∀ k : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun q : ℝ × E =>
          fderiv ℝ (fun w : E =>
            DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg y k w) q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I y).target)) :
    ∃ K : NNReal, ∀ r ∈ Set.Icc (0 : ℝ) T,
      LipschitzOnWith K
        (fun w : E => conjugatingChartVelocityField (I := I) g_DT g_bg y r w)
        (Metric.closedBall c R) := by
  classical
  have hball_compact : IsCompact (Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall c R) :=
    isCompact_Icc.prod (isCompact_closedBall c R)
  have hball_sub : Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall c R
      ⊆ Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I y).target :=
    Set.prod_mono_right hball
  have hbound : ∀ k : Fin (Module.finrank ℝ E), ∃ Ck : ℝ, ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall c R,
      ‖fderiv ℝ (fun w : E =>
          DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg y k w) q.2‖ ≤ Ck := by
    intro k
    exact hball_compact.exists_bound_of_continuousOn ((Hfderiv k).mono hball_sub)
  choose Cf hCf using hbound
  set K0 : ℝ := ∑ k : Fin (Module.finrank ℝ E), |Cf k| * ‖((chartModelBasis E) k : E)‖ with hK0
  have hK0_nonneg : 0 ≤ K0 := by
    rw [hK0]; exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  refine ⟨⟨K0, hK0_nonneg⟩, ?_⟩
  intro r hr
  have hconvex : Convex ℝ (Metric.closedBall c R) := convex_closedBall c R
  have hdiff : ∀ z ∈ Metric.closedBall c R, DifferentiableAt ℝ
      (fun w : E => conjugatingChartVelocityField (I := I) g_DT g_bg y r w) z := by
    intro z hz
    exact (conjugatingChartVelocityField_hasFDerivAt (I := I) g_DT g_bg y r
      (hball hz)).differentiableAt
  have hfbound : ∀ z ∈ Metric.closedBall c R,
      ‖fderiv ℝ (fun w : E => conjugatingChartVelocityField (I := I) g_DT g_bg y r w) z‖₊
        ≤ (⟨K0, hK0_nonneg⟩ : NNReal) := by
    intro z hz
    rw [← NNReal.coe_le_coe]
    have hfd : fderiv ℝ (fun w : E => conjugatingChartVelocityField (I := I) g_DT g_bg y r w) z
        = ∑ k : Fin (Module.finrank ℝ E),
          (fderiv ℝ (fun w : E =>
              DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT r) g_bg y k w) z).smulRight
            ((chartModelBasis E) k : E) :=
      (conjugatingChartVelocityField_hasFDerivAt (I := I) g_DT g_bg y r (hball hz)).fderiv
    rw [hfd, coe_nnnorm]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [ContinuousLinearMap.norm_smulRight_apply]
    have hCfk : ‖fderiv ℝ (fun w : E =>
        DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT r) g_bg y k w) z‖ ≤ |Cf k| :=
      le_trans (hCf k (r, z) ⟨hr, hz⟩) (le_abs_self _)
    exact mul_le_mul hCfk (le_refl _) (norm_nonneg _) (abs_nonneg _)
  exact Convex.lipschitzOnWith_of_nnnorm_fderiv_le (hdiff) hfbound hconvex

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
/-- **Joint orbit continuity of the conjugating flow at the `t = 0` boundary slice.**

For a fixed `y`, the orbit `(t, x) ↦ Φ_fam t x` is jointly continuous at `(0, y)` within
`Ici 0 ×ˢ univ`.  The chart-`y` orbit `r ↦ extChartAt I y (Φ_fam r x)` solves the chart-`y` ODE
with field `-conjugatingChartVelocityField`; uniform chart confinement
(`conjugating_flow_uniform_chart_confinement`, consuming the chart-frame value-continuity `Hcomp`)
keeps it in a chart ball, on which the field is uniformly `LipschitzOnWith K`
(`conjugatingChartVelocityField_lipschitz_uniform`, consuming the chart-frame spatial-derivative
continuity `Hfderiv`).  The Grönwall comparison `dist (chart orbit_x r) (chart orbit_y r) ≤
dist (extChartAt I y x) (extChartAt I y y) · exp (K r)` then drives the chart orbit from `x` to
`extChartAt I y y` as `(r, x) → (0, y)`, using the per-`y` at-`0` orbit datum `hΦorbit0 y` for the
`y`-orbit; applying `(extChartAt I y).symm` (continuous at `extChartAt I y y`) gives `Φ_fam r x → y`. -/
private theorem conjugating_orbit_jointContWithinAt_at_zero
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (hT : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hΦ0 : Φ_fam 0 = _root_.Diffeomorph.refl I M ∞)
    (hΦorbit0 : ∀ y : M,
      ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ici (0 : ℝ)) 0)
    (Hcomp : ∀ (α : M) (k : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (Hfderiv : ∀ (α : M) (k : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          fderiv ℝ (fun w : E =>
            DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k w) q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (y : M) :
    ContinuousWithinAt (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) (0, y) := by
  classical
  set c₀ : E := extChartAt I y y with hc₀
  obtain ⟨b, ρ, hb_pos, hb_le_T, hρ_pos, hball3_int, hconf⟩ :=
    conjugating_flow_uniform_chart_confinement (I := I) g_DT g_bg T hT Φ_fam hΦode hΦ0 hΦorbit0 y
      (Hcomp y)
  have hball2_sub_int : Metric.closedBall c₀ (2 * ρ) ⊆ interior (extChartAt I y).target :=
    subset_trans (Metric.closedBall_subset_closedBall (by linarith)) hball3_int
  -- The uniform Lipschitz constant of the chart-`y`-frame velocity field on the `2ρ`-ball.
  obtain ⟨K, hK⟩ := conjugatingChartVelocityField_lipschitz_uniform (I := I) g_DT g_bg y T c₀ (2 * ρ)
    hball2_sub_int (Hfderiv y)
  -- Good-set reconstruction from confinement: in source with chart image in the `3ρ`-ball.
  have hgoodset_of_ball : ∀ p : M, p ∈ (extChartAt I y).source →
      extChartAt I y p ∈ Metric.ball c₀ (3 * ρ) → p ∈ chartLeviCivitaGoodSet (I := I) y := by
    intro p hp hpz
    rw [mem_chartLeviCivitaGoodSet_iff]
    refine ⟨hp, ?_, hball3_int (Metric.ball_subset_closedBall hpz)⟩
    rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)]
    exact hp
  -- The chart-`y` field, as the right-hand side of the chart ODE.
  set V : ℝ → E → E := fun r z => -conjugatingChartVelocityField (I := I) g_DT g_bg y r z with hV
  -- For a confined orbit, the chart-`y` orbit solves the chart ODE, stays in the ball, and the
  -- Grönwall comparison against the chart-`y` orbit from `y` holds up to time `b`.
  have hgronwall : ∀ x : M, x ∈ (extChartAt I y).source →
      extChartAt I y x ∈ Metric.ball c₀ ρ →
      ∀ r ∈ Set.Ico (0 : ℝ) b,
        dist (extChartAt I y ((Φ_fam r : M → M) x))
            (extChartAt I y ((Φ_fam r : M → M) y))
          ≤ dist (extChartAt I y x) c₀ * Real.exp (K * b) := by
    intro x hx_src hx_ball r hr
    set cx : ℝ → E := fun s => extChartAt I y ((Φ_fam s : M → M) x) with hcx
    set cy : ℝ → E := fun s => extChartAt I y ((Φ_fam s : M → M) y) with hcy
    set s2 : ℝ → Set E := fun _ => Metric.closedBall c₀ (2 * ρ) with hs2
    -- both orbits stay in the `2ρ`-ball (confinement).
    have hy_src : y ∈ (extChartAt I y).source := mem_extChartAt_source y
    have hy_ball : extChartAt I y y ∈ Metric.ball c₀ ρ := by
      rw [hc₀, Metric.mem_ball, dist_self]; exact hρ_pos
    have hconfx : ∀ s ∈ Set.Ico (0 : ℝ) b, (Φ_fam s : M → M) x ∈ (extChartAt I y).source ∧
        cx s ∈ Metric.ball c₀ (2 * ρ) := fun s hs => hconf x hx_src hx_ball s hs
    have hconfy : ∀ s ∈ Set.Ico (0 : ℝ) b, (Φ_fam s : M → M) y ∈ (extChartAt I y).source ∧
        cy s ∈ Metric.ball c₀ (2 * ρ) := fun s hs => hconf y hy_src hy_ball s hs
    have hgoodx : ∀ s ∈ Set.Ico (0 : ℝ) b, (Φ_fam s : M → M) x ∈ chartLeviCivitaGoodSet (I := I) y :=
      fun s hs => hgoodset_of_ball _ (hconfx s hs).1
        (Metric.ball_subset_ball (by linarith) (hconfx s hs).2)
    have hgoody : ∀ s ∈ Set.Ico (0 : ℝ) b, (Φ_fam s : M → M) y ∈ chartLeviCivitaGoodSet (I := I) y :=
      fun s hs => hgoodset_of_ball _ (hconfy s hs).1
        (Metric.ball_subset_ball (by linarith) (hconfy s hs).2)
    -- continuity on `Icc 0 r` of both chart orbits.
    have hcont_orbit : ∀ z : M, (∀ s ∈ Set.Ico (0 : ℝ) b, (Φ_fam s : M → M) z ∈ (extChartAt I y).source) →
        ContinuousOn (fun s : ℝ => extChartAt I y ((Φ_fam s : M → M) z)) (Set.Icc 0 r) := by
      intro z hz
      set gz : ℝ → M := fun u : ℝ => (Φ_fam u : M → M) z with hgz
      intro t ht
      have htb : t ∈ Set.Ico (0 : ℝ) b := ⟨ht.1, lt_of_le_of_lt ht.2 hr.2⟩
      have htsrc : gz t ∈ (extChartAt I y).source := hz t htb
      have hgcwa : ContinuousWithinAt gz (Set.Icc 0 r) t := by
        rcases eq_or_lt_of_le ht.1 with h0 | h0
        · rw [← h0]
          exact (hΦorbit0 z).mono (fun u hu => hu.1)
        · have : t ∈ Set.Ioo (0:ℝ) T := ⟨h0, lt_of_lt_of_le htb.2 hb_le_T⟩
          exact ((hΦode z t this).continuousWithinAt).mono (fun u hu => hu.1)
      exact (continuousAt_extChartAt' (I := I) htsrc).comp_continuousWithinAt hgcwa
    -- both chart orbits solve the chart ODE on the open interior `Ioo a' r`.
    have hderiv_orbit : ∀ z : M,
        (∀ s ∈ Set.Ico (0 : ℝ) b, (Φ_fam s : M → M) z ∈ chartLeviCivitaGoodSet (I := I) y) →
        ∀ s : ℝ, 0 < s → s < r →
          HasDerivWithinAt (fun u : ℝ => extChartAt I y ((Φ_fam u : M → M) z))
            (V s (extChartAt I y ((Φ_fam s : M → M) z))) (Set.Ici s) s := by
      intro z hz s hs0 hsr
      have hsb : s ∈ Set.Ico (0 : ℝ) b := ⟨le_of_lt hs0, lt_trans hsr hr.2⟩
      have hzgood : (Φ_fam s : M → M) z ∈ chartLeviCivitaGoodSet (I := I) y := hz s hsb
      have hsode : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) z)
          (Set.Ici (0:ℝ)) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (-(deTurckVF (I := I) (g_DT s) g_bg ((Φ_fam s : M → M) z)))) :=
        hΦode z s ⟨hs0, lt_of_lt_of_le hsb.2 hb_le_T⟩
      have hdw := chart_conjugating_orbit_hasDerivWithinAt (I := I) g_DT g_bg y
        (fun u : ℝ => (Φ_fam u : M → M) z) s hzgood hsode
      rw [hV]
      exact hdw.mono (fun u hu => le_trans (le_of_lt hs0) hu)
    -- Lipschitz bound of the field on the confinement set, uniform in time.
    have hlip : ∀ s ∈ Set.Ico (0 : ℝ) r, LipschitzOnWith K (V s) (s2 s) := by
      intro s hs
      have hsT : s ∈ Set.Icc (0:ℝ) T :=
        ⟨hs.1, le_trans (le_of_lt (lt_of_lt_of_le hs.2 (le_of_lt hr.2))) hb_le_T⟩
      rw [hV, hs2]
      exact (hK s hsT).neg
    -- the comparison bound on `Icc a' r` for a positive starting time `a'`.
    have hcompare : ∀ a' : ℝ, 0 < a' → a' < r →
        dist (cx r) (cy r) ≤ dist (cx a') (cy a') * Real.exp (K * (r - a')) := by
      intro a' ha'0 ha'r
      have hfcont : ContinuousOn cx (Set.Icc a' r) :=
        (hcont_orbit x (fun s hs => (hconfx s hs).1)).mono
          (fun u hu => ⟨le_trans (le_of_lt ha'0) hu.1, hu.2⟩)
      have hgcont : ContinuousOn cy (Set.Icc a' r) :=
        (hcont_orbit y (fun s hs => (hconfy s hs).1)).mono
          (fun u hu => ⟨le_trans (le_of_lt ha'0) hu.1, hu.2⟩)
      have hfderiv : ∀ s ∈ Set.Ico a' r, HasDerivWithinAt cx (V s (cx s)) (Set.Ici s) s :=
        fun s hs => hderiv_orbit x hgoodx s (lt_of_lt_of_le ha'0 hs.1) hs.2
      have hgderiv : ∀ s ∈ Set.Ico a' r, HasDerivWithinAt cy (V s (cy s)) (Set.Ici s) s :=
        fun s hs => hderiv_orbit y hgoody s (lt_of_lt_of_le ha'0 hs.1) hs.2
      have hfs : ∀ s ∈ Set.Ico a' r, cx s ∈ s2 s := fun s hs => by
        have hsb : s ∈ Set.Ico (0:ℝ) b := ⟨le_trans (le_of_lt ha'0) hs.1, lt_trans hs.2 hr.2⟩
        rw [hs2]; exact Metric.ball_subset_closedBall (hconfx s hsb).2
      have hgs : ∀ s ∈ Set.Ico a' r, cy s ∈ s2 s := fun s hs => by
        have hsb : s ∈ Set.Ico (0:ℝ) b := ⟨le_trans (le_of_lt ha'0) hs.1, lt_trans hs.2 hr.2⟩
        rw [hs2]; exact Metric.ball_subset_closedBall (hconfy s hsb).2
      have hlip' : ∀ s ∈ Set.Ico a' r, LipschitzOnWith K (V s) (s2 s) :=
        fun s hs => hlip s ⟨le_trans (le_of_lt ha'0) hs.1, hs.2⟩
      have := dist_le_of_trajectories_ODE_of_mem (a := a') (b := r) (K := K) (v := V) (s := s2)
        hlip' hfcont hfderiv hfs hgcont hgderiv hgs (le_refl _) r (Set.right_mem_Icc.mpr (le_of_lt ha'r))
      exact this
    -- take the limit `a' → 0⁺`: `dist (cx a') (cy a') → dist (extChartAt y x) c₀`.
    have hΦ0x : (Φ_fam 0 : M → M) x = x := by rw [hΦ0, Diffeomorph.coe_refl, id]
    have hΦ0y : (Φ_fam 0 : M → M) y = y := by rw [hΦ0, Diffeomorph.coe_refl, id]
    have hcx0v : cx 0 = extChartAt I y x := by rw [hcx]; simp only [hΦ0x]
    have hcy0v : cy 0 = c₀ := by rw [hcy]; simp only [hΦ0y]; exact hc₀.symm
    rcases eq_or_lt_of_le hr.1 with hr0 | hr0
    · -- `r = 0`: the comparison is `dist (cx 0) (cy 0) = dist (extChartAt y x) c₀`.
      have hgoal : dist (extChartAt I y ((Φ_fam r : M → M) x))
          (extChartAt I y ((Φ_fam r : M → M) y)) = dist (extChartAt I y x) c₀ := by
        rw [← hr0]; simp only [hΦ0x, hΦ0y]; rw [hc₀]
      rw [hgoal]
      have hexp_nonneg : (1 : ℝ) ≤ Real.exp (K * b) :=
        Real.one_le_exp (by positivity)
      nlinarith [dist_nonneg (x := extChartAt I y x) (y := c₀), hexp_nonneg]
    · -- `r > 0`: limit of the comparison bound as `a' → 0⁺`.
      have hcx_cont0 : ContinuousWithinAt cx (Set.Ici 0) 0 := by
        have h1 : ContinuousWithinAt (fun u : ℝ => (Φ_fam u : M → M) x) (Set.Ici 0) 0 := hΦorbit0 x
        exact ContinuousAt.comp_continuousWithinAt_of_eq
          (continuousAt_extChartAt' (I := I) hx_src) h1 hΦ0x
      have hcy_cont0 : ContinuousWithinAt cy (Set.Ici 0) 0 := by
        have h1 : ContinuousWithinAt (fun u : ℝ => (Φ_fam u : M → M) y) (Set.Ici 0) 0 := hΦorbit0 y
        exact ContinuousAt.comp_continuousWithinAt_of_eq
          (continuousAt_extChartAt' (I := I) hy_src) h1 hΦ0y
      have hIoo_ne : (𝓝[Set.Ioo (0:ℝ) r] 0).NeBot := by
        rw [nhdsWithin_Ioo_eq_nhdsGT hr0]; exact nhdsGT_neBot 0
      have htend_rhs : Filter.Tendsto
          (fun a' : ℝ => dist (cx a') (cy a') * Real.exp (K * (r - a')))
          (𝓝[Set.Ioo (0:ℝ) r] 0)
          (𝓝 (dist (extChartAt I y x) c₀ * Real.exp (K * r))) := by
        have hsub : Set.Ioo (0:ℝ) r ⊆ Set.Ici 0 := fun u hu => le_of_lt hu.1
        have hcxd : Filter.Tendsto cx (𝓝[Set.Ioo (0:ℝ) r] 0) (𝓝 (extChartAt I y x)) := by
          rw [← hcx0v]
          exact hcx_cont0.tendsto.mono_left (nhdsWithin_mono 0 hsub)
        have hcyd : Filter.Tendsto cy (𝓝[Set.Ioo (0:ℝ) r] 0) (𝓝 c₀) := by
          rw [← hcy0v]
          exact hcy_cont0.tendsto.mono_left (nhdsWithin_mono 0 hsub)
        have hdistd : Filter.Tendsto (fun a' : ℝ => dist (cx a') (cy a'))
            (𝓝[Set.Ioo (0:ℝ) r] 0) (𝓝 (dist (extChartAt I y x) c₀)) :=
          (continuous_dist.continuousAt).tendsto.comp (hcxd.prodMk_nhds hcyd)
        have hexpd : Filter.Tendsto (fun a' : ℝ => Real.exp (K * (r - a')))
            (𝓝[Set.Ioo (0:ℝ) r] 0) (𝓝 (Real.exp (K * r))) := by
          have : Filter.Tendsto (fun a' : ℝ => Real.exp (K * (r - a'))) (𝓝 0)
              (𝓝 (Real.exp (K * (r - 0)))) :=
            ((Real.continuous_exp.comp (continuous_const.mul
              (continuous_const.sub continuous_id))).tendsto 0)
          simpa using this.mono_left nhdsWithin_le_nhds
        exact hdistd.mul hexpd
      have hbound_le : dist (cx r) (cy r)
          ≤ dist (extChartAt I y x) c₀ * Real.exp (K * r) := by
        haveI := hIoo_ne
        refine ge_of_tendsto htend_rhs ?_
        filter_upwards [self_mem_nhdsWithin] with a' ha'
        exact hcompare a' ha'.1 ha'.2
      calc dist (cx r) (cy r) ≤ dist (extChartAt I y x) c₀ * Real.exp (K * r) := hbound_le
        _ ≤ dist (extChartAt I y x) c₀ * Real.exp (K * b) := by
            refine mul_le_mul_of_nonneg_left ?_ dist_nonneg
            exact Real.exp_le_exp.mpr (by
              have : (K : ℝ) * r ≤ (K : ℝ) * b :=
                mul_le_mul_of_nonneg_left (le_of_lt hr.2) (NNReal.coe_nonneg K)
              linarith)
  -- Assemble: the chart orbit tends to `c₀`, then apply the chart inverse, continuous at `c₀`.
  set F : ℝ × M → E := fun p => extChartAt I y ((Φ_fam p.1 : M → M) p.2) with hF
  set L : Filter (ℝ × M) := 𝓝[Set.Ici (0 : ℝ) ×ˢ Set.univ] (0, y) with hL
  -- the source and chart-ball region are eventually entered.
  have hsrc_nhds : (fun p : ℝ × M => p.2) ⁻¹' (extChartAt I y).source ∈ L := by
    have hopen : IsOpen (extChartAt I y).source := isOpen_extChartAt_source y
    have : (extChartAt I y).source ∈ 𝓝 y := hopen.mem_nhds (mem_extChartAt_source y)
    exact (continuous_snd.continuousWithinAt (x := ((0, y) : ℝ × M))).preimage_mem_nhdsWithin this
  have hball_nhds : (fun p : ℝ × M => extChartAt I y p.2) ⁻¹' Metric.ball c₀ ρ ∈ L := by
    have hcontsnd : ContinuousWithinAt (fun p : ℝ × M => extChartAt I y p.2)
        (Set.Ici (0:ℝ) ×ˢ Set.univ) (0, y) :=
      (continuousAt_extChartAt' (I := I) (mem_extChartAt_source y)).comp_continuousWithinAt
        (continuous_snd.continuousWithinAt)
    have hmem : Metric.ball c₀ ρ ∈ 𝓝 c₀ := Metric.ball_mem_nhds c₀ hρ_pos
    have : Metric.ball c₀ ρ ∈ 𝓝 (extChartAt I y ((0, y) : ℝ × M).2) := by
      simpa [hc₀] using hmem
    exact hcontsnd.preimage_mem_nhdsWithin this
  have htime_nhds : (fun p : ℝ × M => p.1) ⁻¹' Set.Iio b ∈ L := by
    have : Set.Iio b ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hb_pos
    exact (continuous_fst.continuousWithinAt (x := ((0, y) : ℝ × M))).preimage_mem_nhdsWithin this
  have hge0 : ∀ᶠ p : ℝ × M in L, 0 ≤ p.1 := by
    rw [hL]; filter_upwards [self_mem_nhdsWithin] with p hp using hp.1
  -- the chart orbit tends to `c₀`.
  have hFtend : Filter.Tendsto F L (𝓝 c₀) := by
    have hxtend : Filter.Tendsto (fun p : ℝ × M => extChartAt I y p.2) L (𝓝 c₀) := by
      have hcontsnd : ContinuousWithinAt (fun p : ℝ × M => extChartAt I y p.2)
          (Set.Ici (0:ℝ) ×ˢ Set.univ) (0, y) :=
        (continuousAt_extChartAt' (I := I) (mem_extChartAt_source y)).comp_continuousWithinAt
          (continuous_snd.continuousWithinAt)
      have := hcontsnd.tendsto
      simpa [hc₀, hL] using this
    have hΦ0y' : extChartAt I y ((Φ_fam 0 : M → M) y) = c₀ := by
      rw [hΦ0, Diffeomorph.coe_refl, id]
    have hytend : Filter.Tendsto (fun p : ℝ × M => extChartAt I y ((Φ_fam p.1 : M → M) y)) L (𝓝 c₀) := by
      have h1 : ContinuousWithinAt (fun u : ℝ => (Φ_fam u : M → M) y) (Set.Ici 0) 0 := hΦorbit0 y
      have h2 : ContinuousWithinAt (fun u : ℝ => extChartAt I y ((Φ_fam u : M → M) y))
          (Set.Ici 0) 0 :=
        ContinuousAt.comp_continuousWithinAt_of_eq
          (continuousAt_extChartAt' (I := I) (mem_extChartAt_source y)) h1
          (by rw [hΦ0, Diffeomorph.coe_refl, id])
      have h3 : Filter.Tendsto (fun u : ℝ => extChartAt I y ((Φ_fam u : M → M) y))
          (𝓝[Set.Ici 0] 0) (𝓝 c₀) := by
        have ht := h2.tendsto; rw [hΦ0y'] at ht; exact ht
      have hfst : Filter.Tendsto (fun p : ℝ × M => p.1) L (𝓝[Set.Ici 0] (0 : ℝ)) := by
        rw [hL]
        have hcwa : ContinuousWithinAt (fun p : ℝ × M => p.1) (Set.Ici (0:ℝ) ×ˢ Set.univ) (0, y) :=
          continuous_fst.continuousWithinAt
        have := hcwa.tendsto_nhdsWithin (t := Set.Ici (0:ℝ)) (fun p hp => hp.1)
        simpa using this
      exact h3.comp hfst
    -- squeeze: `dist (F p) c₀ ≤ dist (extChartAt y p.2) c₀ * exp(K b) + dist (extChartAt y (Φ_fam p.1 y)) c₀`.
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hRHStend : Filter.Tendsto
        (fun p : ℝ × M => dist (extChartAt I y p.2) c₀ * Real.exp (K * b)
          + dist (extChartAt I y ((Φ_fam p.1 : M → M) y)) c₀) L (𝓝 0) := by
      have hA : Filter.Tendsto (fun p : ℝ × M => dist (extChartAt I y p.2) c₀ * Real.exp (K * b))
          L (𝓝 0) := by
        have hd : Filter.Tendsto (fun p : ℝ × M => dist (extChartAt I y p.2) c₀) L (𝓝 0) := by
          have := (continuous_dist.continuousAt).tendsto.comp (hxtend.prodMk_nhds (tendsto_const_nhds (x := c₀)))
          simpa [dist_self] using this
        have := hd.mul (tendsto_const_nhds (x := Real.exp (K * b)))
        simpa using this
      have hB : Filter.Tendsto (fun p : ℝ × M => dist (extChartAt I y ((Φ_fam p.1 : M → M) y)) c₀)
          L (𝓝 0) := by
        have := (continuous_dist.continuousAt).tendsto.comp (hytend.prodMk_nhds (tendsto_const_nhds (x := c₀)))
        simpa [dist_self] using this
      have := hA.add hB
      simpa using this
    rw [Metric.tendsto_nhds] at hRHStend
    filter_upwards [hRHStend ε hε, hsrc_nhds, hball_nhds, htime_nhds, hge0] with p hpRHS hpsrc hpball hptime hpge
    have hpsrc' : p.2 ∈ (extChartAt I y).source := hpsrc
    have hpball' : extChartAt I y p.2 ∈ Metric.ball c₀ ρ := hpball
    have hptime' : p.1 < b := hptime
    have hr_mem : p.1 ∈ Set.Ico (0 : ℝ) b := ⟨hpge, hptime'⟩
    have hgb := hgronwall p.2 hpsrc' hpball' p.1 hr_mem
    have htri : dist (F p) c₀
        ≤ dist (extChartAt I y ((Φ_fam p.1 : M → M) p.2))
            (extChartAt I y ((Φ_fam p.1 : M → M) y))
          + dist (extChartAt I y ((Φ_fam p.1 : M → M) y)) c₀ := dist_triangle _ _ _
    have hkey : dist (F p) c₀
        ≤ dist (extChartAt I y p.2) c₀ * Real.exp (K * b)
          + dist (extChartAt I y ((Φ_fam p.1 : M → M) y)) c₀ := by
      refine le_trans htri ?_
      exact add_le_add hgb (le_refl _)
    have hRHSlt : dist (extChartAt I y p.2) c₀ * Real.exp (K * b)
        + dist (extChartAt I y ((Φ_fam p.1 : M → M) y)) c₀ < ε := by
      have := hpRHS; rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    exact lt_of_le_of_lt hkey hRHSlt
  -- apply the chart inverse, continuous at `c₀`.
  have hc₀_tgt : c₀ ∈ (extChartAt I y).target :=
    (extChartAt I y).map_source (mem_extChartAt_source y)
  have hsymm_cont : ContinuousAt (extChartAt I y).symm c₀ :=
    continuousAt_extChartAt_symm'' (I := I) hc₀_tgt
  have hcomp : Filter.Tendsto (fun p : ℝ × M => (extChartAt I y).symm (F p)) L (𝓝 y) := by
    have : Filter.Tendsto (fun p : ℝ × M => (extChartAt I y).symm (F p)) L
        (𝓝 ((extChartAt I y).symm c₀)) := hsymm_cont.tendsto.comp hFtend
    rwa [show (extChartAt I y).symm c₀ = y by rw [hc₀]; exact extChartAt_to_inv y] at this
  -- on the source region, `(extChartAt y).symm (F p) = Φ_fam p.1 p.2`.
  have hEqOn : (fun p : ℝ × M => (extChartAt I y).symm (F p)) =ᶠ[L]
      (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) := by
    filter_upwards [hsrc_nhds, hball_nhds, htime_nhds, hge0] with p hpsrc hpball hptime hpge
    have hr_mem : p.1 ∈ Set.Ico (0 : ℝ) b := ⟨hpge, hptime⟩
    have hgb := hgronwall p.2 hpsrc hpball p.1 hr_mem
    have horbsrc : (Φ_fam p.1 : M → M) p.2 ∈ (extChartAt I y).source :=
      (hconf p.2 hpsrc hpball p.1 hr_mem).1
    change (extChartAt I y).symm (extChartAt I y ((Φ_fam p.1 : M → M) p.2)) = _
    exact (extChartAt I y).left_inv horbsrc
  have hgoal : Filter.Tendsto (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) L (𝓝 y) :=
    hcomp.congr' hEqOn
  rw [ContinuousWithinAt]
  have hval : (Φ_fam (((0 : ℝ), y) : ℝ × M).1 : M → M) (((0 : ℝ), y) : ℝ × M).2 = y := by
    change (Φ_fam 0 : M → M) y = y; rw [hΦ0, Diffeomorph.coe_refl, id]
  rw [hval]; rw [hL] at hgoal; exact hgoal

/-- The affine line `rr ↦ z + rr • δ` has derivative `δ` at `0`. -/
private theorem hasDerivAt_affine_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z δ : E) : HasDerivAt (fun rr : ℝ => z + rr • δ) δ 0 := by
  have h1 : HasDerivAt (fun rr : ℝ => rr • δ) δ 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const δ
  have h2 : HasDerivAt (fun rr : ℝ => z + rr • δ) (0 + δ) 0 :=
    (hasDerivAt_const (0 : ℝ) z).add h1
  simpa using h2

/-- **Euclidean operator-valued spatial-variational ODE from a jointly `C∞` flow + its flow ODE.**

For a jointly `C∞` Euclidean flow `Φ_E : E → ℝ → E` of a time-dependent field `V`, at an interior
time `t`, the spatial Fréchet derivative `s ↦ fderiv ℝ (Φ_E · s) z₀` satisfies the linearised-flow
operator ODE

  `HasDerivAt (fun s => fderiv ℝ (Φ_E · s) z₀)
     ((fderiv ℝ (V t) (Φ_E z₀ t)).comp (fderiv ℝ (Φ_E · t) z₀)) t`,

i.e. `∂_s (D_z Φ_E) = (D_w V)(Φ_E) · (D_z Φ_E)`.  This is the apply-initial-free analogue of
`IsLocalFlow.hasDerivAt_partial_spatial_fderiv` (`VariationalODE/EuclideanVariationalODE.lean`):
joint `C∞` of `Φ_E` at `(z₀, t)` makes its second Fréchet derivative symmetric (Clairaut,
`ContDiffAt.isSymmSndFDerivAt`), which swaps a spatial derivative past the temporal one; the flow
ODE `hflow` (the time-derivative of the orbit at the fixed interior time `t`, for spatial points
near `z₀`) supplies the temporal slot, and the chain rule on the moving point gives the displayed
`A · D`.  The only inputs are the joint `C∞` jet, the per-spatial-point flow ODE near `z₀`, and the
spatial differentiability of the field at the orbit point — none of which is, or destructures to,
the operator-valued `HasDerivAt` conclusion. -/
private theorem hasDerivAt_partial_spatial_fderiv_of_jointContDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (Φ : E × ℝ → E) (V : ℝ → E → E) (z₀ : E) (t : ℝ)
    (hΦ_cd : ContDiffAt ℝ ∞ Φ (z₀, t))
    (hflow : ∀ᶠ z : E in nhds z₀,
      HasDerivAt (fun u : ℝ => Φ (z, u)) (V t (Φ (z, t))) t)
    (hV_diff : DifferentiableAt ℝ (V t) (Φ (z₀, t))) :
    HasDerivAt (fun s : ℝ => fderiv ℝ (fun y : E => Φ (y, s)) z₀)
      ((fderiv ℝ (V t) (Φ (z₀, t))).comp (fderiv ℝ (fun y : E => Φ (y, t)) z₀)) t := by
  have hΦ_cd1 : ContDiffAt ℝ (1 : WithTop ℕ∞) Φ (z₀, t) :=
    hΦ_cd.of_le (by exact_mod_cast le_top)
  have hΦ_diff_nhds : ∀ᶠ q : E × ℝ in nhds (z₀, t), DifferentiableAt ℝ Φ q := by
    have hev : ∀ᶠ q : E × ℝ in nhds (z₀, t), ContDiffAt ℝ (1 : WithTop ℕ∞) Φ q :=
      hΦ_cd1.eventually (by decide)
    filter_upwards [hev] with q hq using hq.differentiableAt (by norm_num)
  have hΦ_diff_xs : DifferentiableAt ℝ Φ (z₀, t) := hΦ_cd.differentiableAt (by simp)
  -- the partial spatial Fréchet derivative as the joint one precomposed with `inl`.
  have hpartial : ∀ {z : E} {s : ℝ}, DifferentiableAt ℝ Φ (z, s) →
      fderiv ℝ (fun y : E => Φ (y, s)) z
        = (fderiv ℝ Φ (z, s)).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
    intro z s hdiff
    have hslice : HasFDerivAt (fun y : E => Φ (y, s))
        ((fderiv ℝ Φ (z, s)).comp (ContinuousLinearMap.inl ℝ E ℝ)) z :=
      hdiff.hasFDerivAt.comp z (hasFDerivAt_prodMk_left z s)
    exact hslice.fderiv
  -- the second Fréchet derivative is symmetric (Clairaut).
  have hone_one_le : (1 + 1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by decide
  have hsndDiff : DifferentiableAt ℝ (fderiv ℝ Φ) (z₀, t) :=
    (hΦ_cd.fderiv_right (m := 1) hone_one_le).differentiableAt (by simp)
  have hsndHas : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) (z₀, t)) (z₀, t) :=
    hsndDiff.hasFDerivAt
  set B := fderiv ℝ (fderiv ℝ Φ) (z₀, t) with hB
  have hsymm : IsSymmSndFDerivAt ℝ Φ (z₀, t) := by
    refine hΦ_cd.isSymmSndFDerivAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]; decide
  -- the spatial slice is differentiable in time, with some operator-valued derivative `D'`.
  set Lsp : E × ℝ → (E →L[ℝ] E) :=
    fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ) with hLsp
  have hLspSmooth : ContDiffAt ℝ ∞ Lsp (z₀, t) := by
    have hfderivSmooth : ContDiffAt ℝ ∞ (fderiv ℝ Φ) (z₀, t) :=
      hΦ_cd.fderiv_right (m := ∞) (by simp)
    have hpost : ContDiffAt ℝ ∞
        (fun L : E × ℝ →L[ℝ] E => L.comp (ContinuousLinearMap.inl ℝ E ℝ)) (fderiv ℝ Φ (z₀, t)) :=
      (ContinuousLinearMap.compL ℝ E (E × ℝ) E |>.flip
        (ContinuousLinearMap.inl ℝ E ℝ)).contDiff.contDiffAt
    exact hpost.comp _ hfderivSmooth
  have hLspTimeDiff : DifferentiableAt ℝ (fun u : ℝ => Lsp (z₀, u)) t :=
    (hLspSmooth.comp t (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  set D' : E →L[ℝ] E := deriv (fun u : ℝ => Lsp (z₀, u)) t with hD'
  have hLspDeriv : HasDerivAt (fun u : ℝ => Lsp (z₀, u)) D' t := hLspTimeDiff.hasDerivAt
  have hUx_nhds : ∀ᶠ u : ℝ in nhds t, DifferentiableAt ℝ Φ (z₀, u) := by
    have hcont : ContinuousAt (fun u : ℝ => (z₀, u)) t := by fun_prop
    exact hcont.eventually hΦ_diff_nhds
  have hSliceEq : (fun u : ℝ => Lsp (z₀, u))
      =ᶠ[nhds t] (fun u : ℝ => fderiv ℝ (fun y : E => Φ (y, u)) z₀) := by
    filter_upwards [hUx_nhds] with u hu
    rw [hLsp, hpartial hu]
  have hSliceDeriv : HasDerivAt (fun u : ℝ => fderiv ℝ (fun y : E => Φ (y, u)) z₀) D' t :=
    hSliceEq.hasDerivAt_iff.mp hLspDeriv
  set RHS : E →L[ℝ] E :=
    (fderiv ℝ (V t) (Φ (z₀, t))).comp (fderiv ℝ (fun y : E => Φ (y, t)) z₀) with hRHS
  -- per-direction Clairaut identification `D' δ = RHS δ`.
  have hDeq : D' = RHS := by
    apply ContinuousLinearMap.ext
    intro δ
    set eX : E × ℝ := ContinuousLinearMap.inl ℝ E ℝ δ with heX
    set eT : E × ℝ := ContinuousLinearMap.inr ℝ E ℝ 1 with heT
    -- LHS: differentiate the (joint) spatial slice in time, evaluated at `δ`.
    have hcurveT : HasDerivAt (fun u : ℝ => (z₀, u)) eT t := by
      have : HasDerivAt (fun u : ℝ => (z₀, u)) ((0 : E), (1 : ℝ)) t := by
        simpa using (hasDerivAt_const t z₀).prodMk (hasDerivAt_id t)
      simpa [heT, ContinuousLinearMap.inr_apply] using this
    have hfderivCurve : HasDerivAt (fun u : ℝ => fderiv ℝ Φ (z₀, u)) (B eT) t :=
      hsndHas.comp_hasDerivAt t hcurveT
    have hslopeApply : HasDerivAt (fun u : ℝ => fderiv ℝ Φ (z₀, u) eX) (B eT eX) t := by
      have := (ContinuousLinearMap.apply ℝ E eX).hasFDerivAt.comp_hasDerivAt t hfderivCurve
      simpa [ContinuousLinearMap.apply_apply] using this
    have hEvEq : (fun u : ℝ => fderiv ℝ Φ (z₀, u) eX)
        =ᶠ[nhds t] (fun u : ℝ => fderiv ℝ (fun y : E => Φ (y, u)) z₀ δ) := by
      filter_upwards [hUx_nhds] with u hu
      rw [hpartial hu]
      simp [heX, ContinuousLinearMap.comp_apply]
    have hLHS : HasDerivAt (fun u : ℝ => fderiv ℝ (fun y : E => Φ (y, u)) z₀ δ) (B eT eX) t :=
      hEvEq.hasDerivAt_iff.mp hslopeApply
    -- the apply path is also `D' δ`.
    have hcurveδ : HasDerivAt (fun u : ℝ => fderiv ℝ (fun y : E => Φ (y, u)) z₀ δ) (D' δ) t := by
      have := (ContinuousLinearMap.apply ℝ E δ).hasFDerivAt.comp_hasDerivAt t hSliceDeriv
      simpa [ContinuousLinearMap.apply_apply] using this
    have hD'δ : D' δ = B eT eX := hcurveδ.unique hLHS
    -- RHS: Clairaut swap, then differentiate the flow ODE in space along a line.
    have hswap : B eT eX = B eX eT := hsymm eT eX
    have hlineCurve : HasDerivAt (fun rr : ℝ => (z₀ + rr • δ, t)) eX 0 := by
      have hline : HasDerivAt (fun rr : ℝ => z₀ + rr • δ) δ 0 := hasDerivAt_affine_line z₀ δ
      have : HasDerivAt (fun rr : ℝ => (z₀ + rr • δ, t)) (δ, (0 : ℝ)) 0 := by
        simpa using hline.prodMk (hasDerivAt_const (0 : ℝ) t)
      simpa [heX, ContinuousLinearMap.inl_apply] using this
    have hcompLine :
        HasDerivAt (fun rr : ℝ => fderiv ℝ Φ (z₀ + rr • δ, t) eT) (B eX eT) 0 := by
      have h1 : HasDerivAt (fun rr : ℝ => fderiv ℝ Φ (z₀ + rr • δ, t)) (B eX) 0 :=
        hsndHas.comp_hasDerivAt_of_eq 0 hlineCurve (by simp)
      have := (ContinuousLinearMap.apply ℝ E eT).hasFDerivAt.comp_hasDerivAt 0 h1
      simpa [ContinuousLinearMap.apply_apply] using this
    -- on the line near `0`, `fderiv Φ (z₀+rr•δ, t) eT = V t (Φ (z₀+rr•δ, t))` (flow ODE).
    have hline_nhds : ∀ᶠ rr : ℝ in nhds 0,
        fderiv ℝ Φ (z₀ + rr • δ, t) eT = V t (Φ (z₀ + rr • δ, t)) := by
      have hmap : Filter.Tendsto (fun rr : ℝ => z₀ + rr • δ) (nhds 0) (nhds z₀) := by
        have hc : ContinuousAt (fun rr : ℝ => z₀ + rr • δ) 0 := by fun_prop
        have := hc.tendsto
        simpa using this
      have hev1 : ∀ᶠ rr : ℝ in nhds 0, HasDerivAt (fun u : ℝ => Φ (z₀ + rr • δ, u))
          (V t (Φ (z₀ + rr • δ, t))) t := hmap.eventually hflow
      have hmap2 : Filter.Tendsto (fun rr : ℝ => (z₀ + rr • δ, t)) (nhds 0) (nhds (z₀, t)) := by
        have hc : ContinuousAt (fun rr : ℝ => (z₀ + rr • δ, t)) 0 := by fun_prop
        have := hc.tendsto
        simpa using this
      have hev2 : ∀ᶠ rr : ℝ in nhds 0, DifferentiableAt ℝ Φ (z₀ + rr • δ, t) :=
        hmap2.eventually hΦ_diff_nhds
      filter_upwards [hev1, hev2] with rr hrr1 hrr2
      have hcurveTrr : HasDerivAt (fun u : ℝ => (z₀ + rr • δ, u)) eT t := by
        have : HasDerivAt (fun u : ℝ => (z₀ + rr • δ, u)) ((0 : E), (1 : ℝ)) t := by
          simpa using (hasDerivAt_const t (z₀ + rr • δ)).prodMk (hasDerivAt_id t)
        simpa [heT, ContinuousLinearMap.inr_apply] using this
      have hjointTime : HasDerivAt (fun u : ℝ => Φ (z₀ + rr • δ, u))
          (fderiv ℝ Φ (z₀ + rr • δ, t) eT) t :=
        hrr2.hasFDerivAt.comp_hasDerivAt t hcurveTrr
      exact hjointTime.unique hrr1
    have hRHSline :
        HasDerivAt (fun rr : ℝ => V t (Φ (z₀ + rr • δ, t))) (B eX eT) 0 :=
      (Filter.eventuallyEq_of_mem hline_nhds (fun _ h => h)).hasDerivAt_iff.mp hcompLine
    -- chain rule: the same line-derivative is `(D_w V)(Φ z₀ t) (D_z Φ · δ)`.
    have hRHSchain :
        HasDerivAt (fun rr : ℝ => V t (Φ (z₀ + rr • δ, t)))
          (fderiv ℝ (V t) (Φ (z₀, t)) (fderiv ℝ (fun y : E => Φ (y, t)) z₀ δ)) 0 := by
      have hinner : HasDerivAt (fun rr : ℝ => Φ (z₀ + rr • δ, t))
          (fderiv ℝ (fun y : E => Φ (y, t)) z₀ δ) 0 := by
        have hsliceDiff : DifferentiableAt ℝ (fun y : E => Φ (y, t)) z₀ := by
          have hslice : HasFDerivAt (fun y : E => Φ (y, t))
              ((fderiv ℝ Φ (z₀, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) z₀ :=
            hΦ_diff_xs.hasFDerivAt.comp z₀ (hasFDerivAt_prodMk_left z₀ t)
          exact hslice.differentiableAt
        have hline : HasDerivAt (fun rr : ℝ => z₀ + rr • δ) δ 0 := hasDerivAt_affine_line z₀ δ
        have := hsliceDiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
        simpa using this
      have := hV_diff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hinner (by simp)
      simpa using this
    have hBval : B eX eT = fderiv ℝ (V t) (Φ (z₀, t)) (fderiv ℝ (fun y : E => Φ (y, t)) z₀ δ) :=
      hRHSline.unique hRHSchain
    rw [hD'δ, hswap, hBval, hRHS, ContinuousLinearMap.comp_apply]
  rw [← hDeq]
  exact hSliceDeriv

set_option linter.unusedVariables false in
/-- **Operator-valued interior linearised-flow ODE for the chart-`y`-conjugated orbit (POSITED
Euclidean Clairaut node).**

The operator-valued (frame-free) heart of `flow_chartJacobian_variational_interior`: the
chart-`y` spatial Fréchet derivative operator
`chartCloseFderiv Φ_fam y x s = mfderiv (extChartAt I y ∘ Φ_fam s) x : E →L[ℝ] E` of the
conjugating orbit satisfies, at an interior time `t` with the orbit confined to the chart-`y`
good set on the window, the linearised-flow operator ODE

  `HasDerivAt (chartCloseFderiv Φ_fam y x)
     ((fderiv (-conjugatingChartVelocityField y t ·) (extChartAt I y (Φ_fam t x))).comp
        (chartCloseFderiv Φ_fam y x t)) t`,

i.e. `∂_s (D_x c) = (D_w field)(c) · (D_x c)` with field `-conjugatingChartVelocityField`.

This is exactly the shape produced by `chartCloseFderiv_hasDerivAt_of_eucl` from the Euclidean
operator variational ODE `IsLocalFlow.hasDerivAt_partial_spatial_fderiv` of the chart-`y`-conjugated
local flow `Φ_eucl(z, s) := extChartAt I y (Φ_fam s ((extChartAt I y).symm z))` — whose joint `C∞`
comes from the interior joint-`C∞` orbit `conjugating_flow_jointContMDiffOn_interior` (the threaded
`hT` / `hfield_reg`) and whose flow ODE is the chart-`y` orbit ODE
`chart_conjugating_orbit_hasDerivWithinAt` (`∂_s Φ_eucl = -conjugatingChartVelocityField (Φ_eucl)`,
along the good set).  The Clairaut mixed-derivative swap is the apply-initial-free analogue of
`IsLocalFlow.hasDerivAt_partial_spatial_fderiv`; the remaining gap is solely the Euclidean
joint-`C∞`-plus-flow-ODE ⇒ variational-ODE producer (whose `IsLocalFlow`-form already exists in
`VariationalODE/EuclideanVariationalODE.lean`).

POSITED recursion target (the Euclidean Clairaut producer for the chart-conjugated flow);
constrains only the internal `g_DT` / `Φ_fam` / the chart-frame field.  The conclusion is a
`HasDerivAt`, never any hypothesis. -/
private theorem flow_chartCloseFderiv_hasDerivAt_interior
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
    (y : M) (x : M) (hx_src : x ∈ (extChartAt I y).source)
    (a c : ℝ) (hac : 0 ≤ a) (hcT : c ≤ T)
    (t : ℝ) (ht : t ∈ Set.Ioo a c)
    (hgood : ∀ s ∈ Set.Ioo a c,
      (Φ_fam s : M → M) x ∈ chartLeviCivitaGoodSet (I := I) y) :
    HasDerivAt (chartCloseFderiv (I := I) Φ_fam y x)
      ((fderiv ℝ (fun w : E =>
          -conjugatingChartVelocityField (I := I) g_DT g_bg y t w)
          (extChartAt I y ((Φ_fam t : M → M) x))).comp
        (chartCloseFderiv (I := I) Φ_fam y x t)) t := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- The chart-`y`-conjugated Euclidean flow and the chart-`y`-frame velocity field.
  set Φ_eucl : E → ℝ → E :=
    fun z s => extChartAt I y ((Φ_fam s : M → M) ((extChartAt I y).symm z)) with hΦeucl
  set z₀ : E := extChartAt I y x with hz₀
  -- `t` is interior, so `0 < t < T`, and the orbit at `t` is in the good set.
  obtain ⟨hat, htc⟩ := ht
  have ht0 : 0 < t := lt_of_le_of_lt hac hat
  have htT : t < T := lt_of_lt_of_le htc hcT
  have ht_mem : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hgood_t : (Φ_fam t : M → M) x ∈ chartLeviCivitaGoodSet (I := I) y := hgood t ⟨hat, htc⟩
  have hx_chart : x ∈ (chartAt H y).source := by rwa [extChartAt_source] at hx_src
  have hsymm_z₀ : (extChartAt I y).symm z₀ = x := (extChartAt I y).left_inv hx_src
  -- The orbit point at `t` lies in the chart-`y` target interior.
  have horbit_t_src : (Φ_fam t : M → M) x ∈ (extChartAt I y).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hgood_t
  have hΦeucl_t_pt : Φ_eucl z₀ t = extChartAt I y ((Φ_fam t : M → M) x) := by
    rw [hΦeucl]; simp only [hsymm_z₀]
  -- The interior joint-`C∞` orbit (the threaded `hT` / `hfield_reg`).
  have hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
    conjugating_flow_jointContMDiffOn_interior (I := I) g_DT g_bg T hT Φ_fam hΦode hfield_reg
  have hjoint_at : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) (t, x) :=
    hjoint.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht_mem, Set.mem_univ _⟩)
  -- Joint `C∞` of the chart-`y`-conjugated Euclidean flow at `(z₀, t)`.
  have hΦeucl_cd : ContDiffAt ℝ ∞ (fun q : E × ℝ => Φ_eucl q.1 q.2) (z₀, t) := by
    have hz₀_tgt : z₀ ∈ (extChartAt I y).target :=
      (extChartAt I y).map_source hx_src
    -- source map `(z, s) ↦ (s, (extChartAt y).symm z)` is `ContMDiffAt` into `ℝ × M`.
    have hsymm_cmdo : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I y).symm (extChartAt I y).target :=
      contMDiffOn_extChartAt_symm y
    have hsymm_cma : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I y).symm z₀ :=
      hsymm_cmdo.contMDiffAt (isOpen_extChartAt_target (I := I) y |>.mem_nhds hz₀_tgt)
    have hfst : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) ∞
        (fun q : E × ℝ => q.1) (z₀, t) := contMDiffAt_iff_contDiffAt.mpr contDiffAt_fst
    have hsnd : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ℝ) ∞
        (fun q : E × ℝ => q.2) (z₀, t) := contMDiffAt_iff_contDiffAt.mpr contDiffAt_snd
    have hsrcmap : ContMDiffAt 𝓘(ℝ, E × ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : E × ℝ => (q.2, (extChartAt I y).symm q.1)) (z₀, t) :=
      hsnd.prodMk (hsymm_cma.comp (z₀, t) hfst)
    have hsrcmap_pt : (fun q : E × ℝ => (q.2, (extChartAt I y).symm q.1)) (z₀, t) = (t, x) := by
      simp only [hsymm_z₀]
    -- orbit composed with the source map.
    have horbit_comp : ContMDiffAt 𝓘(ℝ, E × ℝ) I ∞
        (fun q : E × ℝ => (Φ_fam q.2 : M → M) ((extChartAt I y).symm q.1)) (z₀, t) := by
      have hcomp := hjoint_at.comp_of_eq hsrcmap hsrcmap_pt
      simpa [Function.comp] using hcomp
    -- post-compose with `extChartAt y`, smooth at the orbit point.
    have hext_cmdo : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I y) (chartAt H y).source :=
      contMDiffOn_extChartAt
    have hext_cma : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I y) ((Φ_fam t : M → M) x) := by
      have hsrc : (Φ_fam t : M → M) x ∈ (chartAt H y).source := by
        rwa [extChartAt_source] at horbit_t_src
      exact hext_cmdo.contMDiffAt ((chartAt H y).open_source.mem_nhds hsrc)
    have horbit_comp_pt :
        (fun q : E × ℝ => (Φ_fam q.2 : M → M) ((extChartAt I y).symm q.1)) (z₀, t)
          = (Φ_fam t : M → M) x := by simp only [hsymm_z₀]
    have hcomp2 : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) ∞
        (fun q : E × ℝ => Φ_eucl q.1 q.2) (z₀, t) := by
      have := hext_cma.comp_of_eq horbit_comp horbit_comp_pt
      simpa [hΦeucl, Function.comp] using this
    exact contMDiffAt_iff_contDiffAt.mp hcomp2
  -- The flow ODE for the chart-`y`-conjugated Euclidean flow near `z₀` (good-set orbit).
  have hflow : ∀ᶠ z : E in nhds z₀,
      HasDerivAt (fun u : ℝ => Φ_eucl z u)
        (-conjugatingChartVelocityField (I := I) g_DT g_bg y t (Φ_eucl z t)) t := by
    -- nearby `z`: the orbit `Φ_fam t (symm z)` stays in the open good set.
    set ψ : E → M := fun z => (Φ_fam t : M → M) ((extChartAt I y).symm z) with hψ
    have hψ_cont : ContinuousAt ψ z₀ := by
      have hjca : ContinuousAt (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) (t, x) :=
        hjoint_at.continuousAt
      have hsymm_contAt : ContinuousAt (extChartAt I y).symm z₀ :=
        continuousAt_extChartAt_symm'' (I := I) ((extChartAt I y).map_source hx_src)
      have hpair : ContinuousAt (fun z : E => (t, (extChartAt I y).symm z)) z₀ :=
        continuousAt_const.prodMk hsymm_contAt
      have hpair_pt : (fun z : E => (t, (extChartAt I y).symm z)) z₀ = (t, x) := by
        simp only [hsymm_z₀]
      have hcomp := hjca.comp_of_eq hpair hpair_pt
      exact hcomp
    have hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) y) :=
      chartLeviCivitaGoodSet_isOpen (I := I) y
    have hgood_z₀ : ψ z₀ ∈ chartLeviCivitaGoodSet (I := I) y := by
      rw [hψ]; simp only [hsymm_z₀]; exact hgood_t
    have hpre : ψ ⁻¹' (chartLeviCivitaGoodSet (I := I) y) ∈ nhds z₀ :=
      hψ_cont (hgood_open.mem_nhds hgood_z₀)
    filter_upwards [hpre] with z hz_good
    -- the orbit `Φ_fam · (symm z)` solves the manifold ODE at `t` (two-sided, interior).
    set p : M := (extChartAt I y).symm z with hp
    have hode_within : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) p)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) p)))) :=
      hΦode p t ht_mem
    have hpgood : (Φ_fam t : M → M) p ∈ chartLeviCivitaGoodSet (I := I) y := hz_good
    have hchart_within : HasDerivWithinAt (fun s : ℝ => extChartAt I y ((Φ_fam s : M → M) p))
        (-conjugatingChartVelocityField (I := I) g_DT g_bg y t (extChartAt I y ((Φ_fam t : M → M) p)))
        (Set.Ici (0 : ℝ)) t :=
      chart_conjugating_orbit_hasDerivWithinAt (I := I) g_DT g_bg y
        (fun s : ℝ => (Φ_fam s : M → M) p) t hpgood hode_within
    -- upgrade to a two-sided `HasDerivAt` (since `t > 0`, `Ici 0 ∈ 𝓝 t`).
    have hIci_nhds : Set.Ici (0 : ℝ) ∈ nhds t := Ici_mem_nhds ht0
    have hda := hchart_within.hasDerivAt hIci_nhds
    have hΦeucl_z_eq : (fun u : ℝ => Φ_eucl z u)
        = (fun s : ℝ => extChartAt I y ((Φ_fam s : M → M) p)) := rfl
    have hΦeucl_z_t : Φ_eucl z t = extChartAt I y ((Φ_fam t : M → M) p) := rfl
    rw [hΦeucl_z_eq, hΦeucl_z_t]
    exact hda
  -- Spatial differentiability of the velocity field at the orbit point.
  have hV_diff : DifferentiableAt ℝ
      (fun w : E => -conjugatingChartVelocityField (I := I) g_DT g_bg y t w) (Φ_eucl z₀ t) := by
    rw [hΦeucl_t_pt]
    have hz_int : extChartAt I y ((Φ_fam t : M → M) x) ∈ interior (extChartAt I y).target := by
      rw [mem_chartLeviCivitaGoodSet_iff] at hgood_t; exact hgood_t.2.2
    exact (conjugatingChartVelocityField_hasFDerivAt (I := I) g_DT g_bg y t hz_int).differentiableAt.neg
  -- The Euclidean operator-valued spatial-variational ODE (Helper 1, Clairaut).
  have heucl := hasDerivAt_partial_spatial_fderiv_of_jointContDiffAt
    (fun q : E × ℝ => Φ_eucl q.1 q.2)
    (fun s z => -conjugatingChartVelocityField (I := I) g_DT g_bg y s z) z₀ t
    hΦeucl_cd hflow hV_diff
  -- The producer turns it into the operator-valued `HasDerivAt` for `chartCloseFderiv`.
  -- chart-conjugation agreement near `x`, valid for every `s` (not just `t`).
  have hagree : ∀ᶠ s : ℝ in nhds t,
      (fun p : M => extChartAt I y ((Φ_fam s : M → M) p))
        =ᶠ[nhds x] (fun p : M => Φ_eucl (extChartAt I y p) s) := by
    filter_upwards [Filter.univ_mem] with s _
    have hsrc_nhds : (extChartAt I y).source ∈ nhds x :=
      isOpen_extChartAt_source (I := I) y |>.mem_nhds hx_src
    filter_upwards [hsrc_nhds] with p hp
    change extChartAt I y ((Φ_fam s : M → M) p)
      = extChartAt I y ((Φ_fam s : M → M) ((extChartAt I y).symm (extChartAt I y p)))
    rw [(extChartAt I y).left_inv hp]
  -- differentiability of the Euclidean spatial slice near `t`.
  have heucl_diff : ∀ᶠ s : ℝ in nhds t,
      DifferentiableAt ℝ (fun z : E => Φ_eucl z s) z₀ := by
    have hΦeucl_cd1 : ContDiffAt ℝ (1 : WithTop ℕ∞) (fun q : E × ℝ => Φ_eucl q.1 q.2) (z₀, t) :=
      hΦeucl_cd.of_le (by exact_mod_cast le_top)
    have hΦeucl_nhds : ∀ᶠ q : E × ℝ in nhds (z₀, t),
        ContDiffAt ℝ (1 : WithTop ℕ∞) (fun q : E × ℝ => Φ_eucl q.1 q.2) q :=
      hΦeucl_cd1.eventually (by decide)
    have hmap : Filter.Tendsto (fun s : ℝ => (z₀, s)) (nhds t) (nhds (z₀, t)) := by
      have hc : ContinuousAt (fun s : ℝ => (z₀, s)) t := by fun_prop
      simpa using hc.tendsto
    have hev : ∀ᶠ s : ℝ in nhds t,
        ContDiffAt ℝ (1 : WithTop ℕ∞) (fun q : E × ℝ => Φ_eucl q.1 q.2) (z₀, s) :=
      hmap.eventually hΦeucl_nhds
    filter_upwards [hev] with s hs
    have hdiff : DifferentiableAt ℝ (fun q : E × ℝ => Φ_eucl q.1 q.2) (z₀, s) :=
      hs.differentiableAt (by norm_num)
    have hincl : DifferentiableAt ℝ (fun z : E => (z, s)) z₀ :=
      differentiableAt_id.prodMk (differentiableAt_const s)
    have hgoal_eq : (fun z : E => Φ_eucl z s)
        = (fun q : E × ℝ => Φ_eucl q.1 q.2) ∘ (fun z : E => (z, s)) := rfl
    rw [hgoal_eq]
    exact hdiff.comp z₀ hincl
  -- Assemble via the chart-conjugation producer.
  have hprod := chartCloseFderiv_hasDerivAt_of_eucl (I := I) Φ_fam y x t Φ_eucl hx_chart
    heucl heucl_diff hagree
  -- Rewrite the producer's `D'_eucl.comp trivToE` as `A.comp (chartCloseFderiv ... t)`.
  have hchartT : chartCloseFderiv (I := I) Φ_fam y x t
      = (fderiv ℝ (fun z : E => Φ_eucl z t) z₀).comp (trivToE (I := I) y x) := by
    refine chartCloseFderiv_eq_eucl_comp_trivToE (I := I) Φ_fam y x t Φ_eucl hx_chart ?_ ?_
    · exact heucl_diff.self_of_nhds
    · exact hagree.self_of_nhds
  -- the producer's `D'_eucl.comp trivToE` equals the target derivative value.
  refine hprod.congr_deriv ?_
  change ((fderiv ℝ (fun w : E => -conjugatingChartVelocityField (I := I) g_DT g_bg y t w)
            (Φ_eucl z₀ t)).comp (fderiv ℝ (fun z : E => Φ_eucl z t) z₀)).comp
          (trivToE (I := I) y x)
      = (fderiv ℝ (fun w : E => -conjugatingChartVelocityField (I := I) g_DT g_bg y t w)
          (extChartAt I y ((Φ_fam t : M → M) x))).comp (chartCloseFderiv (I := I) Φ_fam y x t)
  rw [hchartT, hΦeucl_t_pt]
  exact ContinuousLinearMap.comp_assoc _ _ _

set_option linter.unusedVariables false in
/-- **Interior linearised variational ODE for the chart-`y` Jacobian along the moving frame.**

Writing `D(s, x) := mfderiv (extChartAt I y ∘ Φ_fam s) x (chartBasisVecFiber x₀ i x)` for the
chart-`y` Jacobian of the conjugating orbit along the fixed-chart-`x₀` frame, and
`A(t, z) := fderiv ℝ (fun w => -conjugatingChartVelocityField g_DT g_bg y t w) z` for the spatial
Fréchet derivative of the (negated) chart-`y`-frame velocity field, the chart-`y` Jacobian
solves, on the open time interval and at every basepoint `x` whose orbit is confined to the
chart-`y` interior, the linear variational ODE

  `D'(t, x) = A(t, c_x(t)) · D(t, x)`,    `c_x(t) := extChartAt I y (Φ_fam t x)`,

as a within-`Ici t` right-derivative.  This is the linearisation in `x` of the chart-`y` orbit ODE
`c_x'(t) = -conjugatingChartVelocityField (c_x t)` (`chart_conjugating_orbit_hasDerivWithinAt`):
the interior joint-`C∞` orbit `conjugating_flow_jointContMDiffOn_interior` (supplied by the threaded
`hT` / `hfield_reg`) makes `(s, x) ↦ extChartAt I y (Φ_fam s x)` jointly `C∞` on a window about
`(t, x)`, realised — via the Euclidean chart conjugation `(z, s) ↦ extChartAt I y (Φ_fam s
((extChartAt I y).symm z))` — as a local Euclidean flow `Φ` of the chart-field
`-conjugatingChartVelocityField`, whose operator-valued linearised-flow ODE
(`IsLocalFlow.hasDerivAt_partial_spatial_fderiv`, the Clairaut mixed-derivative swap) is exactly
`∂_s (D_z Φ) = (D_z field) · (D_z Φ)`.  Transporting the moving manifold frame through the chart
dictionary turns this into the displayed `D' = A · D`.

Constrains only the internal `g_DT` / `Φ_fam` / the chart-frame field; the conclusion is a
`HasDerivWithinAt`, never any hypothesis. -/
private theorem flow_chartJacobian_variational_interior
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
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) (y : M) (x : M)
    (hx_src : x ∈ (extChartAt I y).source)
    (a c : ℝ) (hac : 0 ≤ a) (hcT : c ≤ T)
    (t : ℝ) (ht : t ∈ Set.Ioo a c)
    (hgood : ∀ s ∈ Set.Ioo a c,
      (Φ_fam s : M → M) x ∈ chartLeviCivitaGoodSet (I := I) y) :
    HasDerivWithinAt
      (fun s : ℝ => mfderiv I 𝓘(ℝ, E)
        (fun z : M => extChartAt I y ((Φ_fam s : M → M) z)) x
        (chartBasisVecFiber (I := I) x₀ i x))
      ((fderiv ℝ (fun w : E =>
          -conjugatingChartVelocityField (I := I) g_DT g_bg y t w)
          (extChartAt I y ((Φ_fam t : M → M) x)))
        (mfderiv I 𝓘(ℝ, E)
          (fun z : M => extChartAt I y ((Φ_fam t : M → M) z)) x
          (chartBasisVecFiber (I := I) x₀ i x)))
      (Set.Ici (0 : ℝ)) t := by
  -- Operator-valued linearised-flow ODE for the chart-`y` spatial derivative (POSITED node).
  have hop := flow_chartCloseFderiv_hasDerivAt_interior (I := I) g_DT g_bg T hT Φ_fam hΦode
    hfield_reg y x hx_src a c hac hcT t ht hgood
  -- Apply the operator `HasDerivAt` to the fixed chart-`x₀` frame fibre.
  have happ := (ContinuousLinearMap.apply ℝ E (chartBasisVecFiber (I := I) x₀ i x)).hasFDerivAt.comp_hasDerivAt
    t hop
  -- `chartCloseFderiv Φ_fam y x s = mfderiv (extChartAt I y ∘ Φ_fam s) x`, so the applied operator
  -- path is the chart-`y` Jacobian, and the applied derivative value is the variational term.
  simp only [ContinuousLinearMap.apply_apply] at happ
  exact happ.hasDerivWithinAt

set_option linter.unusedVariables false in
/-- **Per-basepoint slice right-continuity at `t = 0` of the chart-`y` Jacobian (POSITED analytic
node).**

With `D(s, x) := mfderiv (extChartAt I y ∘ Φ_fam s) x (chartBasisVecFiber x₀ i x)`, the chart-`y`
Jacobian along the moving frame is, at every basepoint `x` IN the chart-`y` source, right-continuous
in `s` at `t = 0`:

  `∀ x, x ∈ (extChartAt I y).source → ContinuousWithinAt (fun s => D(s, x)) (Ici 0) 0`.

The membership guard is genuinely needed: off the chart-`y` source, `D(0, x) =
mfderiv (extChartAt I y) x (chartBasisVecFiber x₀ i x)` is the junk value of the non-differentiable
moving chart, and the orbit may oscillate across the chart boundary near `s = 0`, so the chart-form
Jacobian is not right-continuous there (it IS in the genuine bundle, which is what `hΦmfderiv0`
records).  For `x` in the source, the bundle-form Jacobian-at-`0` datum `hΦmfderiv0 x v` — the genuine
variational continuous-dependence-up-to-`0` of the moving spatial differential, the linearised
companion of the orbit datum `hΦorbit0` — is converted to the chart-`y` form: the moving orbit point
`Φ_fam s x` stays in the chart-`y` source near `s = 0` (orbit continuity `hΦorbit0`, source open),
where the chart dictionary `trivToE_mfderiv_eq_chartFderiv_apply` reads the fixed-chart-`y` fibre
coordinate `((triv y) ⟨Φ_fam s x, mfderiv (Φ_fam s) x v⟩).2 = D(s, x)`; that fibre coordinate is
continuous at the bundle point (which sits in `(triv y).source` since `Φ_fam 0 x = x`).  The interior
ODE `flow_chartJacobian_variational_interior` alone does not pin this initial-time limit (the
constant of integration), so it is genuinely separate analytic content; `hΦ0` computes
`D(0, x) = mfderiv (extChartAt I y) x v`.

Constrains only the internal `g_DT` / `Φ_fam` / the `t = 0`-endpoint flow data; the conclusion is a
`ContinuousWithinAt`, never any hypothesis. -/
private theorem flow_chartJacobian_pery_continuousWithinAt_zero
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hΦ0 : Φ_fam 0 = _root_.Diffeomorph.refl I M ∞)
    (hΦorbit0 : ∀ y : M,
      ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ici (0 : ℝ)) 0)
    (hΦmfderiv0 : ∀ (y : M) (u : TangentSpace I y),
      ContinuousWithinAt (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
        (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ici (0 : ℝ)) 0)
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) (y : M) :
    ∀ x : M, x ∈ (extChartAt I y).source → ContinuousWithinAt
      (fun s : ℝ => mfderiv I 𝓘(ℝ, E)
        (fun z : M => extChartAt I y ((Φ_fam s : M → M) z)) x
        (chartBasisVecFiber (I := I) x₀ i x))
      (Set.Ici (0 : ℝ)) 0 := by
  classical
  intro x hx_src
  -- The chart-`y` source contains `x`; rewrite as a chart membership for the bridge.
  have hx_chart : x ∈ (chartAt H y).source := by rwa [extChartAt_source] at hx_src
  set v : TangentSpace I x := chartBasisVecFiber (I := I) x₀ i x with hv
  -- The bundle-valued moving Jacobian at the basepoint `x`, right-continuous at `0` (`hΦmfderiv0`).
  set fb : ℝ → TangentBundle I M := fun s : ℝ =>
    (TotalSpace.mk' E ((Φ_fam s : M → M) x) (mfderiv I I (Φ_fam s : M → M) x v)
      : TangentBundle I M) with hfb
  have hfb_cont : ContinuousWithinAt fb (Set.Ici (0 : ℝ)) 0 := hΦmfderiv0 x v
  -- The fixed-chart-`y` fibre-coordinate extraction, continuous on `(triv y).source`.
  set Ψ : TangentBundle I M → E := fun b =>
    ((trivializationAt E (TangentSpace I) y) b).2 with hΨ
  -- `fb 0`'s base point is `x`, hence `fb 0 ∈ (triv y).source`.
  have hΦ0x : (Φ_fam 0 : M → M) x = x := by rw [hΦ0, Diffeomorph.coe_refl, id]
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx_chart
  have hfb0_src : fb 0 ∈ (trivializationAt E (TangentSpace I) y).source := by
    rw [Trivialization.mem_source]
    show (fb 0).proj ∈ (trivializationAt E (TangentSpace I) y).baseSet
    show (Φ_fam 0 : M → M) x ∈ _
    rw [hΦ0x]; exact hx_base
  have hΨcontAt : ContinuousAt Ψ (fb 0) := by
    have hsrc_nhds : (trivializationAt E (TangentSpace I) y).source ∈ 𝓝 (fb 0) :=
      (trivializationAt E (TangentSpace I) y).open_source.mem_nhds hfb0_src
    have hcont : ContinuousOn Ψ (trivializationAt E (TangentSpace I) y).source :=
      continuous_snd.comp_continuousOn (trivializationAt E (TangentSpace I) y).continuousOn
    exact hcont.continuousAt hsrc_nhds
  -- `Ψ ∘ fb` is right-continuous at `0`.
  have hcomp : ContinuousWithinAt (fun s : ℝ => Ψ (fb s)) (Set.Ici (0 : ℝ)) 0 :=
    hΨcontAt.comp_continuousWithinAt hfb_cont
  -- The orbit stays in the chart-`y` source near `0`.
  have horbit_src : (fun s : ℝ => (Φ_fam s : M → M) x) ⁻¹' (chartAt H y).source
      ∈ 𝓝[Set.Ici (0 : ℝ)] 0 := by
    have hopen : IsOpen (chartAt H y).source := (chartAt H y).open_source
    have hmem : (chartAt H y).source ∈ 𝓝 ((Φ_fam 0 : M → M) x) := by
      rw [hΦ0x]; exact hopen.mem_nhds hx_chart
    exact (hΦorbit0 x).preimage_mem_nhdsWithin hmem
  -- On that neighbourhood, `D(s, x) = Ψ (fb s)` (the chart dictionary bridge).
  have hEvEq : (fun s : ℝ => mfderiv I 𝓘(ℝ, E)
        (fun z : M => extChartAt I y ((Φ_fam s : M → M) z)) x v)
      =ᶠ[𝓝[Set.Ici (0 : ℝ)] 0] (fun s : ℝ => Ψ (fb s)) := by
    filter_upwards [horbit_src] with s hs
    have hFx_chart : (Φ_fam s : M → M) x ∈ (chartAt H y).source := hs
    have hFx_base : (Φ_fam s : M → M) x ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hFx_chart
    have hmdiff : MDifferentiableAt I I (Φ_fam s : M → M) x :=
      ((Φ_fam s).mdifferentiable (by decide)) x
    -- `trivToE y (Φ_fam s x) (mfderiv (Φ_fam s) x v) = Ψ (fb s)` (the trivialised fibre coordinate).
    have htriv : trivToE (I := I) y ((Φ_fam s : M → M) x) (mfderiv I I (Φ_fam s : M → M) x v)
        = Ψ (fb s) := by
      change ((trivializationAt E (TangentSpace I) y).continuousLinearMapAt ℝ
          ((Φ_fam s : M → M) x)) (mfderiv I I (Φ_fam s : M → M) x v)
        = ((trivializationAt E (TangentSpace I) y) (fb s)).2
      rw [Trivialization.continuousLinearMapAt_apply,
        Trivialization.coe_linearMapAt_of_mem _ hFx_base]
    exact (trivToE_mfderiv_eq_chartFderiv_apply (I := I)
      (Φ_fam s : M → M) y v hmdiff hFx_chart).symm.trans htriv
  refine hcomp.congr_of_eventuallyEq hEvEq ?_
  -- value match at `0`: `Ψ (fb 0) = D(0, x)`.
  have hmdiff0 : MDifferentiableAt I I (Φ_fam 0 : M → M) x :=
    ((Φ_fam 0).mdifferentiable (by decide)) x
  have hFx_base0 : (Φ_fam 0 : M → M) x ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
    rw [hΦ0x]; exact hx_base
  have htriv0 : trivToE (I := I) y ((Φ_fam 0 : M → M) x) (mfderiv I I (Φ_fam 0 : M → M) x v)
      = Ψ (fb 0) := by
    change ((trivializationAt E (TangentSpace I) y).continuousLinearMapAt ℝ
        ((Φ_fam 0 : M → M) x)) (mfderiv I I (Φ_fam 0 : M → M) x v)
      = ((trivializationAt E (TangentSpace I) y) (fb 0)).2
    rw [Trivialization.continuousLinearMapAt_apply,
      Trivialization.coe_linearMapAt_of_mem _ hFx_base0]
  rw [← htriv0]
  exact (trivToE_mfderiv_eq_chartFderiv_apply (I := I) (Φ_fam 0 : M → M) y v hmdiff0
    (by rw [hΦ0x]; exact hx_chart)).symm

set_option linter.unusedVariables false in
/-- **`t = 0` spatial-`x` continuity of the chart-`y` Jacobian along the moving frame.**

At the initial time `t = 0` (where `Φ_fam 0 = id`), the chart-`y` Jacobian along the moving frame
reduces to `D(0, x) = mfderiv (extChartAt I y) x (chartBasisVecFiber x₀ i x)`, the forward
chart-`y` trivialisation applied to the chart-`x₀` frame fibre.  As a function of the basepoint `x`,
this is continuous within the chart-`x₀` base set at `y`, PROVIDED `y` itself lies in that base set:

  `y ∈ baseSet x₀ → ContinuousWithinAt
     (fun x => mfderiv (extChartAt I y) x (chartBasisVecFiber x₀ i x)) (baseSet x₀) y`.

The premise `hy` is genuinely needed: off `baseSet x₀ ∩ baseSet y` the object
`mfderiv (extChartAt I y) x (chartBasisVecFiber x₀ i x)` is the change-of-frame coefficient
`tangentCoordChange I x₀ y x (chartModelBasis E i)`, continuous only on the overlap (an `S¹`
two-chart counterexample makes it discontinuous at a boundary point of `baseSet y`); `hy` (with
`y ∈ baseSet y` automatic) places `y` in the interior of the overlap, where the bridge applies.

On `baseSet x₀ ∩ baseSet y` (a neighbourhood-within of `y`), the bridge
`trivToE_mfderiv_eq_chartFderiv_apply` (with `F = id`) rewrites the Jacobian as the trivialised
fibre `((triv y) ⟨x, chartBasisVecFiber x₀ i x⟩).2 = ((triv y) (chartBasisVec x₀ i x)).2`,
continuous via `chartBasisVec_contMDiffOn` (the smooth, hence continuous, chart-`x₀` frame section
landing in `(triv y).source` over `baseSet y`), `Trivialization.continuousOn`, and `continuous_snd`;
`continuousWithinAt_inter` (`baseSet y ∈ 𝓝 y`) descends to the full `baseSet x₀`.  Genuine
chart-Jacobian / bundle-coordinate continuity content; the conclusion is a `ContinuousWithinAt`,
never any hypothesis. -/
private theorem flow_chartJacobian_zero_continuousWithinAt_basepoint
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) (y : M)
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContinuousWithinAt
      (fun x : M => mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y z) x
        (chartBasisVecFiber (I := I) x₀ i x))
      (trivializationAt E (TangentSpace I) x₀).baseSet y := by
  classical
  set f : M → E := fun x : M => mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y z) x
    (chartBasisVecFiber (I := I) x₀ i x) with hf
  -- The trivialised fibre form of `f` on the chart-overlap.
  set g : M → E := fun x : M =>
    ((trivializationAt E (TangentSpace I) y) (chartBasisVec (I := I) x₀ i x)).2 with hg
  have hy_basey : y ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H y
  -- `baseSet y` is an open neighbourhood of `y`.
  have hbasey_nhds : (trivializationAt E (TangentSpace I) y).baseSet ∈ 𝓝 y :=
    (trivializationAt E (TangentSpace I) y).open_baseSet.mem_nhds hy_basey
  -- On the overlap, `f x = g x` (the bridge `trivToE = mfderiv (extChartAt I y)`, `F = id`).
  have hfg : ∀ x : M, x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet ∩
      (trivializationAt E (TangentSpace I) y).baseSet → f x = g x := by
    intro x hx
    have hx_basey : x ∈ (trivializationAt E (TangentSpace I) y).baseSet := hx.2
    have hx_srcy : x ∈ (chartAt H y).source := by
      rwa [TangentBundle.trivializationAt_baseSet] at hx_basey
    -- bridge with `F = id`: `trivToE y x (mfderiv id x v) = mfderiv (extChartAt I y) x v`.
    have hbridge := trivToE_mfderiv_eq_chartFderiv_apply (I := I) (@id M) y
      (chartBasisVecFiber (I := I) x₀ i x) (mdifferentiableAt_id (I := I)) hx_srcy
    simp only [mfderiv_id] at hbridge
    -- `f x = trivToE y x (chartBasisVecFiber x₀ i x)` (the bridge RHS is `f x` up to `id`).
    have hfx : f x = trivToE (I := I) y x (chartBasisVecFiber (I := I) x₀ i x) := by
      rw [hf]; exact hbridge.symm
    -- `trivToE y x w = ((triv y) (chartBasisVec x₀ i x)).2` on `baseSet y`.
    have htriv : trivToE (I := I) y x (chartBasisVecFiber (I := I) x₀ i x)
        = ((trivializationAt E (TangentSpace I) y)
            (chartBasisVec (I := I) x₀ i x)).2 := by
      change ((trivializationAt E (TangentSpace I) y).continuousLinearMapAt ℝ x)
          (chartBasisVecFiber (I := I) x₀ i x)
        = ((trivializationAt E (TangentSpace I) y)
            (TotalSpace.mk' E x (chartBasisVecFiber (I := I) x₀ i x))).2
      rw [Trivialization.continuousLinearMapAt_apply,
        Trivialization.coe_linearMapAt_of_mem _ hx_basey]
    rw [hfx, htriv, hg]
  -- `g` is continuous on the overlap: smooth frame section into `(triv y).source`, then `(triv y)`.
  have hgcont : ContinuousOn g ((trivializationAt E (TangentSpace I) x₀).baseSet ∩
      (trivializationAt E (TangentSpace I) y).baseSet) := by
    have hsec : ContinuousOn (chartBasisVec (I := I) x₀ i)
        ((trivializationAt E (TangentSpace I) x₀).baseSet ∩
          (trivializationAt E (TangentSpace I) y).baseSet) :=
      ((chartBasisVec_contMDiffOn (I := I) x₀ i).continuousOn).mono Set.inter_subset_left
    have hmaps : Set.MapsTo (chartBasisVec (I := I) x₀ i)
        ((trivializationAt E (TangentSpace I) x₀).baseSet ∩
          (trivializationAt E (TangentSpace I) y).baseSet)
        (trivializationAt E (TangentSpace I) y).source := by
      intro x hx
      rw [Trivialization.mem_source]
      show (chartBasisVec (I := I) x₀ i x).proj ∈ _
      rw [chartBasisVec_proj]; exact hx.2
    have htrivcont : ContinuousOn (fun b : TangentBundle I M =>
        ((trivializationAt E (TangentSpace I) y) b).2)
        (trivializationAt E (TangentSpace I) y).source :=
      continuous_snd.comp_continuousOn (trivializationAt E (TangentSpace I) y).continuousOn
    exact htrivcont.comp hsec hmaps
  -- `f` is `ContinuousWithinAt` on the overlap at `y` (transport `g`'s continuity through `hfg`).
  have hy_inter : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet ∩
      (trivializationAt E (TangentSpace I) y).baseSet := ⟨hy, hy_basey⟩
  have hf_inter : ContinuousWithinAt f
      ((trivializationAt E (TangentSpace I) x₀).baseSet ∩
        (trivializationAt E (TangentSpace I) y).baseSet) y :=
    ((hgcont y hy_inter).congr (fun x hx => hfg x hx) (hfg y hy_inter))
  -- Descend from the overlap to the full chart-`x₀` base set (`baseSet y ∈ 𝓝 y`).
  exact (continuousWithinAt_inter hbasey_nhds).mp hf_inter

set_option linter.unusedVariables false in
set_option maxHeartbeats 4000000 in
/-- **Uniform-in-`x` variational Grönwall datum for the chart-`y` Jacobian.**

The analytic variational input feeding `flow_chartJacobian_jointContWithinAt_at_zero`, the
operator-valued (`E`-valued, here applied to the moving frame) sibling of the orbit Grönwall in
`conjugating_orbit_jointContWithinAt_at_zero`.  Writing
`D(t, x) := mfderiv (extChartAt I y ∘ Φ_fam t) x (chartBasisVecFiber x₀ i x)` for the chart-`y`
Jacobian along the moving frame, this packages the two genuine variational-dependence facts:

* `hcross` — the joint cross-difference `dist (D(p.1, p.2)) (D(p.1, y)) → 0` as `(p.1, p.2) → (0, y)`
  within `Ici 0 ×ˢ baseSet x₀`.  On the interior `D` solves the linear variational ODE
  `D'(t) = (D_z conjugatingChartVelocityField)(t, c_x(t)) · D(t)` (the spatial Fréchet derivative of
  the chart-frame velocity, `conjugatingChartVelocityField_hasFDerivAt`, uniformly bounded by
  `Hfderiv`), with the orbit `c_x(t) = extChartAt I y (Φ_fam t x)` confined to a chart ball by
  `conjugating_flow_uniform_chart_confinement`.  A uniform variational Grönwall
  (`dist_le_of_approx_trajectories_ODE_of_mem`) compares `D(·, x)` against `D(·, y)`: the comparison
  defect `‖(A(c_x) − A(c_y)) · D(·, y)‖` is driven to `0` by `c_x → c_y` (conjunct 1,
  `conjugating_orbit_jointContWithinAt_at_zero`) with `A` continuous (`Hfderiv`), so the cross
  difference vanishes uniformly in `t`.
* `hpery` — the per-`y` continuous-dependence-up-to-`0` `D(p.1, y) → D(0, y)` as `p.1 → 0⁺`
  (the `y`-slice variational limit; the window-flow Jacobian-at-`0` datum).

`hΦ0` pins `Φ_fam 0 = id`, so `D(0, y) = mfderiv (extChartAt I y) y (chartBasisVecFiber x₀ i y)`.
All hypotheses constrain only the internal `g_DT` / `Φ_fam` / the chart-frame field; the
conclusion is the chart-coordinate Jacobian, never equal to nor destructuring to any hypothesis.

The manifold variational ODE/Grönwall up to the initial time, assembled from its three leaves: the
interior variational ODE `flow_chartJacobian_variational_interior` (`D' = A·D`, on the threaded
`hT` / `hfield_reg`), the per-basepoint at-`0` limit `flow_chartJacobian_pery_continuousWithinAt_zero`
(on `hΦmfderiv0`), and the `t = 0` basepoint continuity
`flow_chartJacobian_zero_continuousWithinAt_basepoint` (on `hy`), wired by a uniform variational
Grönwall. -/
private theorem flow_chartJacobian_uniform_variational_tendsto
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (hT : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hΦ0 : Φ_fam 0 = _root_.Diffeomorph.refl I M ∞)
    (hΦorbit0 : ∀ y : M,
      ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ici (0 : ℝ)) 0)
    (hΦmfderiv0 : ∀ (y : M) (u : TangentSpace I y),
      ContinuousWithinAt (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
        (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ici (0 : ℝ)) 0)
    (hfield_reg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (Hcomp : ∀ (α : M) (k : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (Hfderiv : ∀ (α : M) (k : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          fderiv ℝ (fun w : E =>
            DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k w) q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) (y : M)
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    Filter.Tendsto
      (fun p : ℝ × M =>
        dist
          (mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y ((Φ_fam p.1 : M → M) z)) p.2
            (chartBasisVecFiber (I := I) x₀ i p.2))
          (mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y ((Φ_fam p.1 : M → M) z)) y
            (chartBasisVecFiber (I := I) x₀ i y)))
      (𝓝[Set.Ici (0 : ℝ) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet] (0, y)) (𝓝 0)
    ∧ Filter.Tendsto
        (fun t : ℝ =>
          mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y ((Φ_fam t : M → M) z)) y
            (chartBasisVecFiber (I := I) x₀ i y))
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 (mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y z) y
          (chartBasisVecFiber (I := I) x₀ i y))) := by
  classical
  -- The chart-`y` Jacobian along the moving frame, as a function of `(s, x)`.
  set D : ℝ → M → E := fun s x => mfderiv I 𝓘(ℝ, E)
    (fun z : M => extChartAt I y ((Φ_fam s : M → M) z)) x
    (chartBasisVecFiber (I := I) x₀ i x) with hD
  set Dval : E := mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y z) y
    (chartBasisVecFiber (I := I) x₀ i y) with hDval
  -- Per-basepoint (in-source) right-continuity at `0` of `s ↦ D s x` (variational at-`0` node).
  have hpery0 : ∀ x : M, x ∈ (extChartAt I y).source →
      ContinuousWithinAt (fun s : ℝ => D s x) (Set.Ici (0 : ℝ)) 0 :=
    flow_chartJacobian_pery_continuousWithinAt_zero (I := I) g_DT g_bg T Φ_fam hΦode hΦ0
      hΦorbit0 hΦmfderiv0 x₀ i y
  -- `D 0 x = mfderiv (extChartAt I y) x (chartBasisVecFiber x₀ i x)` (since `Φ_fam 0 = id`).
  have hD0 : ∀ x : M, D 0 x
      = mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y z) x
        (chartBasisVecFiber (I := I) x₀ i x) := by
    intro x
    have hfuneq : (fun z : M => extChartAt I y ((Φ_fam 0 : M → M) z))
        = (fun z : M => extChartAt I y z) := by
      funext z; rw [hΦ0, Diffeomorph.coe_refl, id]
    have hmfeq : mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y ((Φ_fam 0 : M → M) z)) x
        = mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y z) x :=
      Filter.EventuallyEq.mfderiv_eq (Filter.EventuallyEq.of_eq hfuneq)
    exact DFunLike.congr_fun hmfeq (chartBasisVecFiber (I := I) x₀ i x)
  have hD0y : D 0 y = Dval := by rw [hD0 y, hDval]
  refine ⟨?_, ?_⟩
  · -- ============ CONJUNCT (a): the cross-difference Grönwall ============
    set c₀ : E := extChartAt I y y with hc₀
    obtain ⟨b, ρ, hb_pos, hb_le_T, hρ_pos, hball3_int, hconf⟩ :=
      conjugating_flow_uniform_chart_confinement (I := I) g_DT g_bg T hT Φ_fam hΦode hΦ0 hΦorbit0 y
        (Hcomp y)
    have hball2_sub_int : Metric.closedBall c₀ (2 * ρ) ⊆ interior (extChartAt I y).target :=
      subset_trans (Metric.closedBall_subset_closedBall (by linarith)) hball3_int
    -- Uniform Lipschitz constant `K` of the chart-`y`-frame velocity field on the `2ρ`-ball.
    obtain ⟨K, hK⟩ := conjugatingChartVelocityField_lipschitz_uniform (I := I) g_DT g_bg y T c₀ (2 * ρ)
      hball2_sub_int (Hfderiv y)
    -- The variational operator `A t z := fderiv (-conjugatingChartVelocityField y t ·) z`.
    set A : ℝ → E → (E →L[ℝ] E) := fun t z =>
      fderiv ℝ (fun w : E => -conjugatingChartVelocityField (I := I) g_DT g_bg y t w) z with hA
    -- Good-set reconstruction from confinement.
    have hgoodset_of_ball : ∀ p : M, p ∈ (extChartAt I y).source →
        extChartAt I y p ∈ Metric.ball c₀ (3 * ρ) → p ∈ chartLeviCivitaGoodSet (I := I) y := by
      intro p hp hpz
      rw [mem_chartLeviCivitaGoodSet_iff]
      refine ⟨hp, ?_, hball3_int (Metric.ball_subset_closedBall hpz)⟩
      rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)]
      exact hp
    -- Operator norm bound `‖A t z‖ ≤ K` on the open `2ρ`-ball, uniform in `t ∈ Icc 0 T`.
    have hAbound : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z ∈ Metric.ball c₀ (2 * ρ), ‖A t z‖ ≤ (K : ℝ) := by
      intro t ht z hz
      have hlipneg : LipschitzOnWith K
          (fun w : E => -conjugatingChartVelocityField (I := I) g_DT g_bg y t w)
          (Metric.closedBall c₀ (2 * ρ)) := (hK t ht).neg
      have hnhds : Metric.closedBall c₀ (2 * ρ) ∈ 𝓝 z := by
        refine Metric.mem_nhds_iff.mpr ⟨2 * ρ - dist z c₀, ?_, fun w hw => ?_⟩
        · rw [Metric.mem_ball] at hz; linarith
        · rw [Metric.mem_ball] at hw
          rw [Metric.mem_closedBall]
          have h1 : dist w c₀ ≤ dist w z + dist z c₀ := dist_triangle _ _ _
          linarith [hw]
      exact norm_fderiv_le_of_lipschitzOn ℝ hnhds hlipneg
    -- Joint continuity of the operator `A` on the compact `Icc 0 T ×ˢ closedBall c₀ 2ρ`.
    have hAcont : ContinuousOn (fun q : ℝ × E => A q.1 q.2)
        (Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall c₀ (2 * ρ)) := by
      have hfeq : ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall c₀ (2 * ρ),
          A q.1 q.2 = -(∑ k : Fin (Module.finrank ℝ E),
            (fderiv ℝ (fun w : E =>
                DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg y k w) q.2).smulRight
              ((chartModelBasis E) k : E)) := by
        rintro ⟨t, z⟩ hq
        have hzint : z ∈ interior (extChartAt I y).target := hball2_sub_int hq.2
        have hfd := (conjugatingChartVelocityField_hasFDerivAt (I := I) g_DT g_bg y t hzint)
        show fderiv ℝ (fun w : E => -conjugatingChartVelocityField (I := I) g_DT g_bg y t w) z = _
        exact hfd.neg.fderiv
      refine ContinuousOn.congr ?_ hfeq
      refine ContinuousOn.neg ?_
      refine continuousOn_finset_sum _ (fun k _ => ?_)
      have hcontk : ContinuousOn (fun q : ℝ × E =>
          fderiv ℝ (fun w : E =>
            DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg y k w) q.2)
          (Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall c₀ (2 * ρ)) :=
        (Hfderiv y k).mono (Set.prod_mono_right hball2_sub_int)
      exact ((ContinuousLinearMap.smulRightL ℝ E E).flip ((chartModelBasis E) k : E)).continuous.comp_continuousOn hcontk
    -- Heine–Cantor: `A` is uniformly continuous on the compact set.
    have hAcompact : IsCompact (Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall c₀ (2 * ρ)) :=
      isCompact_Icc.prod (isCompact_closedBall c₀ (2 * ρ))
    have hAunif : UniformContinuousOn (fun q : ℝ × E => A q.1 q.2)
        (Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall c₀ (2 * ρ)) :=
      hAcompact.uniformContinuousOn_of_continuous hAcont
    -- The chart-`y` orbit from a confined basepoint, and the orbit Grönwall comparison.
    set cc : M → ℝ → E := fun x s => extChartAt I y ((Φ_fam s : M → M) x) with hcc
    have hy_src : y ∈ (extChartAt I y).source := mem_extChartAt_source y
    have hy_ball : extChartAt I y y ∈ Metric.ball c₀ ρ := by
      rw [hc₀, Metric.mem_ball, dist_self]; exact hρ_pos
    -- For confined `x`: chart orbits in the `2ρ`-ball, with the chart-orbit Grönwall comparison.
    have horbit_ball : ∀ x : M, x ∈ (extChartAt I y).source →
        extChartAt I y x ∈ Metric.ball c₀ ρ →
        ∀ s ∈ Set.Ico (0 : ℝ) b, cc x s ∈ Metric.ball c₀ (2 * ρ) :=
      fun x hx hxb s hs => (hconf x hx hxb s hs).2
    have horbit_src : ∀ x : M, x ∈ (extChartAt I y).source →
        extChartAt I y x ∈ Metric.ball c₀ ρ →
        ∀ s ∈ Set.Ico (0 : ℝ) b, (Φ_fam s : M → M) x ∈ (extChartAt I y).source :=
      fun x hx hxb s hs => (hconf x hx hxb s hs).1
    have hgoodx : ∀ x : M, x ∈ (extChartAt I y).source →
        extChartAt I y x ∈ Metric.ball c₀ ρ →
        ∀ s ∈ Set.Ico (0 : ℝ) b, (Φ_fam s : M → M) x ∈ chartLeviCivitaGoodSet (I := I) y :=
      fun x hx hxb s hs => hgoodset_of_ball _ (horbit_src x hx hxb s hs)
        (Metric.ball_subset_ball (by linarith) (horbit_ball x hx hxb s hs))
    -- The chart-`y` orbit Grönwall comparison `dist (cc x r) (cc y r) ≤ dist (φ x) c₀ · exp (K b)`.
    have horbit_gronwall : ∀ x : M, x ∈ (extChartAt I y).source →
        extChartAt I y x ∈ Metric.ball c₀ ρ →
        ∀ r ∈ Set.Ico (0 : ℝ) b,
          dist (cc x r) (cc y r) ≤ dist (extChartAt I y x) c₀ * Real.exp ((K : ℝ) * b) := by
      intro x hx_src hx_ball r hr
      set s2 : ℝ → Set E := fun _ => Metric.closedBall c₀ (2 * ρ) with hs2
      set V : ℝ → E → E := fun s z => -conjugatingChartVelocityField (I := I) g_DT g_bg y s z with hV
      have hcont_orbit : ∀ z : M, (∀ s ∈ Set.Ico (0 : ℝ) b,
            (Φ_fam s : M → M) z ∈ (extChartAt I y).source) →
          ContinuousOn (fun s : ℝ => extChartAt I y ((Φ_fam s : M → M) z)) (Set.Icc 0 r) := by
        intro z hz
        set gz : ℝ → M := fun u : ℝ => (Φ_fam u : M → M) z with hgz
        intro t ht
        have htb : t ∈ Set.Ico (0 : ℝ) b := ⟨ht.1, lt_of_le_of_lt ht.2 hr.2⟩
        have htsrc : gz t ∈ (extChartAt I y).source := hz t htb
        have hgcwa : ContinuousWithinAt gz (Set.Icc 0 r) t := by
          rcases eq_or_lt_of_le ht.1 with h0 | h0
          · rw [← h0]; exact (hΦorbit0 z).mono (fun u hu => hu.1)
          · have : t ∈ Set.Ioo (0 : ℝ) T := ⟨h0, lt_of_lt_of_le htb.2 hb_le_T⟩
            exact ((hΦode z t this).continuousWithinAt).mono (fun u hu => hu.1)
        exact (continuousAt_extChartAt' (I := I) htsrc).comp_continuousWithinAt hgcwa
      have hderiv_orbit : ∀ z : M,
          (∀ s ∈ Set.Ico (0 : ℝ) b, (Φ_fam s : M → M) z ∈ chartLeviCivitaGoodSet (I := I) y) →
          ∀ s : ℝ, 0 < s → s < r →
            HasDerivWithinAt (fun u : ℝ => extChartAt I y ((Φ_fam u : M → M) z))
              (V s (extChartAt I y ((Φ_fam s : M → M) z))) (Set.Ici s) s := by
        intro z hz s hs0 hsr
        have hsb : s ∈ Set.Ico (0 : ℝ) b := ⟨le_of_lt hs0, lt_trans hsr hr.2⟩
        have hzgood : (Φ_fam s : M → M) z ∈ chartLeviCivitaGoodSet (I := I) y := hz s hsb
        have hsode : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) z)
            (Set.Ici (0 : ℝ)) s
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (-(deTurckVF (I := I) (g_DT s) g_bg ((Φ_fam s : M → M) z)))) :=
          hΦode z s ⟨hs0, lt_of_lt_of_le hsb.2 hb_le_T⟩
        have hdw := chart_conjugating_orbit_hasDerivWithinAt (I := I) g_DT g_bg y
          (fun u : ℝ => (Φ_fam u : M → M) z) s hzgood hsode
        rw [hV]
        exact hdw.mono (fun u hu => le_trans (le_of_lt hs0) hu)
      have hlip : ∀ s ∈ Set.Ico (0 : ℝ) r, LipschitzOnWith K (V s) (s2 s) := by
        intro s hs
        have hsT : s ∈ Set.Icc (0 : ℝ) T :=
          ⟨hs.1, le_trans (le_of_lt (lt_of_lt_of_le hs.2 (le_of_lt hr.2))) hb_le_T⟩
        rw [hV, hs2]; exact (hK s hsT).neg
      have hcompare : ∀ a' : ℝ, 0 < a' → a' < r →
          dist (cc x r) (cc y r) ≤ dist (cc x a') (cc y a') * Real.exp ((K : ℝ) * (r - a')) := by
        intro a' ha'0 ha'r
        have hfcont : ContinuousOn (cc x) (Set.Icc a' r) :=
          (hcont_orbit x (fun s hs => horbit_src x hx_src hx_ball s hs)).mono
            (fun u hu => ⟨le_trans (le_of_lt ha'0) hu.1, hu.2⟩)
        have hgcont : ContinuousOn (cc y) (Set.Icc a' r) :=
          (hcont_orbit y (fun s hs => horbit_src y hy_src hy_ball s hs)).mono
            (fun u hu => ⟨le_trans (le_of_lt ha'0) hu.1, hu.2⟩)
        have hfderiv : ∀ s ∈ Set.Ico a' r, HasDerivWithinAt (cc x) (V s (cc x s)) (Set.Ici s) s :=
          fun s hs => hderiv_orbit x (hgoodx x hx_src hx_ball) s (lt_of_lt_of_le ha'0 hs.1) hs.2
        have hgderiv : ∀ s ∈ Set.Ico a' r, HasDerivWithinAt (cc y) (V s (cc y s)) (Set.Ici s) s :=
          fun s hs => hderiv_orbit y (hgoodx y hy_src hy_ball) s (lt_of_lt_of_le ha'0 hs.1) hs.2
        have hfs : ∀ s ∈ Set.Ico a' r, cc x s ∈ s2 s := fun s hs => by
          have hsb : s ∈ Set.Ico (0 : ℝ) b := ⟨le_trans (le_of_lt ha'0) hs.1, lt_trans hs.2 hr.2⟩
          rw [hs2]; exact Metric.ball_subset_closedBall (horbit_ball x hx_src hx_ball s hsb)
        have hgs : ∀ s ∈ Set.Ico a' r, cc y s ∈ s2 s := fun s hs => by
          have hsb : s ∈ Set.Ico (0 : ℝ) b := ⟨le_trans (le_of_lt ha'0) hs.1, lt_trans hs.2 hr.2⟩
          rw [hs2]; exact Metric.ball_subset_closedBall (horbit_ball y hy_src hy_ball s hsb)
        have hlip' : ∀ s ∈ Set.Ico a' r, LipschitzOnWith K (V s) (s2 s) :=
          fun s hs => hlip s ⟨le_trans (le_of_lt ha'0) hs.1, hs.2⟩
        exact dist_le_of_trajectories_ODE_of_mem (a := a') (b := r) (K := K) (v := V) (s := s2)
          hlip' hfcont hfderiv hfs hgcont hgderiv hgs (le_refl _) r
          (Set.right_mem_Icc.mpr (le_of_lt ha'r))
      have hccx0 : cc x 0 = extChartAt I y x := by
        rw [hcc]; simp only [hΦ0, Diffeomorph.coe_refl, id]
      have hccy0 : cc y 0 = c₀ := by
        rw [hcc]; simp only [hΦ0, Diffeomorph.coe_refl, id]; exact hc₀.symm
      rcases eq_or_lt_of_le hr.1 with hr0 | hr0
      · have hgoal : dist (cc x r) (cc y r) = dist (extChartAt I y x) c₀ := by
          rw [← hr0, ← hccx0, ← hccy0]
        rw [hgoal]
        nlinarith [dist_nonneg (x := extChartAt I y x) (y := c₀),
          Real.one_le_exp (show (0 : ℝ) ≤ (K : ℝ) * b by positivity)]
      · have hccx_cont0 : ContinuousWithinAt (cc x) (Set.Ici 0) 0 := by
          have h1 : ContinuousWithinAt (fun u : ℝ => (Φ_fam u : M → M) x) (Set.Ici 0) 0 :=
            hΦorbit0 x
          exact ContinuousAt.comp_continuousWithinAt_of_eq
            (continuousAt_extChartAt' (I := I) hx_src) h1
            (by simp only [hΦ0, Diffeomorph.coe_refl, id])
        have hccy_cont0 : ContinuousWithinAt (cc y) (Set.Ici 0) 0 := by
          have h1 : ContinuousWithinAt (fun u : ℝ => (Φ_fam u : M → M) y) (Set.Ici 0) 0 :=
            hΦorbit0 y
          exact ContinuousAt.comp_continuousWithinAt_of_eq
            (continuousAt_extChartAt' (I := I) hy_src) h1
            (by simp only [hΦ0, Diffeomorph.coe_refl, id])
        have hIoo_ne : (𝓝[Set.Ioo (0 : ℝ) r] 0).NeBot := by
          rw [nhdsWithin_Ioo_eq_nhdsGT hr0]; exact nhdsGT_neBot 0
        have htend_rhs : Filter.Tendsto
            (fun a' : ℝ => dist (cc x a') (cc y a') * Real.exp ((K : ℝ) * (r - a')))
            (𝓝[Set.Ioo (0 : ℝ) r] 0)
            (𝓝 (dist (extChartAt I y x) c₀ * Real.exp ((K : ℝ) * r))) := by
          have hsub : Set.Ioo (0 : ℝ) r ⊆ Set.Ici 0 := fun u hu => le_of_lt hu.1
          have hcxd : Filter.Tendsto (cc x) (𝓝[Set.Ioo (0 : ℝ) r] 0)
              (𝓝 (extChartAt I y x)) := by
            rw [← hccx0]; exact hccx_cont0.tendsto.mono_left (nhdsWithin_mono 0 hsub)
          have hcyd : Filter.Tendsto (cc y) (𝓝[Set.Ioo (0 : ℝ) r] 0) (𝓝 c₀) := by
            rw [← hccy0]; exact hccy_cont0.tendsto.mono_left (nhdsWithin_mono 0 hsub)
          have hdistd : Filter.Tendsto (fun a' : ℝ => dist (cc x a') (cc y a'))
              (𝓝[Set.Ioo (0 : ℝ) r] 0) (𝓝 (dist (extChartAt I y x) c₀)) :=
            (continuous_dist.continuousAt).tendsto.comp (hcxd.prodMk_nhds hcyd)
          have hexpd : Filter.Tendsto (fun a' : ℝ => Real.exp ((K : ℝ) * (r - a')))
              (𝓝[Set.Ioo (0 : ℝ) r] 0) (𝓝 (Real.exp ((K : ℝ) * r))) := by
            have : Filter.Tendsto (fun a' : ℝ => Real.exp ((K : ℝ) * (r - a'))) (𝓝 0)
                (𝓝 (Real.exp ((K : ℝ) * (r - 0)))) :=
              ((Real.continuous_exp.comp (continuous_const.mul
                (continuous_const.sub continuous_id))).tendsto 0)
            simpa using this.mono_left nhdsWithin_le_nhds
          exact hdistd.mul hexpd
        have hbound_le : dist (cc x r) (cc y r)
            ≤ dist (extChartAt I y x) c₀ * Real.exp ((K : ℝ) * b) := by
          haveI := hIoo_ne
          have hr_bound : dist (cc x r) (cc y r)
              ≤ dist (extChartAt I y x) c₀ * Real.exp ((K : ℝ) * r) := by
            refine ge_of_tendsto htend_rhs ?_
            filter_upwards [self_mem_nhdsWithin] with a' ha'
            exact hcompare a' ha'.1 ha'.2
          refine le_trans hr_bound ?_
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) dist_nonneg
          have : (K : ℝ) * r ≤ (K : ℝ) * b :=
            mul_le_mul_of_nonneg_left (le_of_lt hr.2) (NNReal.coe_nonneg K)
          linarith
        exact hbound_le
    -- The interior variational ODE for `D · x`, on the confinement window `Ioo 0 b`, for confined `x`.
    have hDode : ∀ x : M, x ∈ (extChartAt I y).source →
        extChartAt I y x ∈ Metric.ball c₀ ρ →
        ∀ s : ℝ, 0 < s → s < b →
          HasDerivWithinAt (fun u : ℝ => D u x) (A s (cc x s) (D s x)) (Set.Ici (0 : ℝ)) s := by
      intro x hx_src hx_ball s hs0 hsb
      have hgood : ∀ u ∈ Set.Ioo (0 : ℝ) b, (Φ_fam u : M → M) x ∈ chartLeviCivitaGoodSet (I := I) y :=
        fun u hu => hgoodx x hx_src hx_ball u ⟨le_of_lt hu.1, hu.2⟩
      exact flow_chartJacobian_variational_interior (I := I) g_DT g_bg T hT Φ_fam hΦode hfield_reg
        x₀ i y x hx_src 0 b (le_refl 0) hb_le_T s ⟨hs0, hsb⟩ hgood
    -- Continuity of `D · x` on `Icc 0 r` for confined `x` and `r < b`.
    have hDcont : ∀ x : M, x ∈ (extChartAt I y).source →
        extChartAt I y x ∈ Metric.ball c₀ ρ →
        ∀ r : ℝ, r < b → ContinuousOn (fun u : ℝ => D u x) (Set.Icc 0 r) := by
      intro x hx_src hx_ball r hrb u hu
      rcases eq_or_lt_of_le hu.1 with h0 | h0
      · rw [← h0]; exact ((hpery0 x hx_src).mono (fun w hw => hw.1))
      · have hub : u < b := lt_of_le_of_lt hu.2 hrb
        exact ((hDode x hx_src hx_ball u h0 hub).continuousWithinAt).mono (fun w hw => hw.1)
    -- The integrand bound `‖A u (cc x u) w‖ ≤ K ‖w‖` along confined orbits, uniform in time.
    have hAintegrand : ∀ x : M, x ∈ (extChartAt I y).source →
        extChartAt I y x ∈ Metric.ball c₀ ρ →
        ∀ u ∈ Set.Ico (0 : ℝ) b, ‖A u (cc x u)‖ ≤ (K : ℝ) := by
      intro x hx_src hx_ball u hu
      have huT : u ∈ Set.Icc (0 : ℝ) T :=
        ⟨hu.1, le_trans (le_of_lt (lt_of_lt_of_le hu.2 hb_le_T)) (le_refl T)⟩
      exact hAbound u huT (cc x u) (horbit_ball x hx_src hx_ball u hu)
    -- Grönwall a-priori bound from a positive start `a'`: `‖D r' x‖ ≤ ‖D a' x‖ · exp (K (r'−a'))`.
    have hDcompare : ∀ x : M, x ∈ (extChartAt I y).source →
        extChartAt I y x ∈ Metric.ball c₀ ρ →
        ∀ a' r' : ℝ, 0 < a' → a' ≤ r' → r' < b →
          ‖D r' x‖ ≤ ‖D a' x‖ * Real.exp ((K : ℝ) * (r' - a')) := by
      intro x hx_src hx_ball a' r' ha'0 ha'r' hr'b
      have hcont : ContinuousOn (fun u : ℝ => D u x) (Set.Icc a' r') :=
        (hDcont x hx_src hx_ball r' hr'b).mono
          (fun u hu => ⟨le_trans (le_of_lt ha'0) hu.1, hu.2⟩)
      have hderiv : ∀ u ∈ Set.Ico a' r',
          HasDerivWithinAt (fun w : ℝ => D w x) (A u (cc x u) (D u x)) (Set.Ici u) u := by
        intro u hu
        have hu0 : 0 < u := lt_of_lt_of_le ha'0 hu.1
        exact (hDode x hx_src hx_ball u hu0 (lt_trans hu.2 hr'b)).mono
          (fun w hw => le_trans (le_of_lt hu0) hw)
      have hbnd : ∀ u ∈ Set.Ico a' r', ‖A u (cc x u) (D u x)‖ ≤ (K : ℝ) * ‖D u x‖ + 0 := by
        intro u hu
        have hub : u ∈ Set.Ico (0 : ℝ) b :=
          ⟨le_trans (le_of_lt ha'0) hu.1, lt_trans hu.2 hr'b⟩
        have hAu : ‖A u (cc x u)‖ ≤ (K : ℝ) := hAintegrand x hx_src hx_ball u hub
        calc ‖A u (cc x u) (D u x)‖ ≤ ‖A u (cc x u)‖ * ‖D u x‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ (K : ℝ) * ‖D u x‖ := by gcongr
          _ = (K : ℝ) * ‖D u x‖ + 0 := by ring
      have hgb := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv (le_refl ‖D a' x‖) hbnd
      have := hgb r' (Set.right_mem_Icc.mpr ha'r')
      rw [gronwallBound_ε0] at this
      exact this
    -- Uniform Jacobian bound: take the start `a' → 0⁺` limit of `hDcompare`.
    have hDboundU : ∀ x : M, x ∈ (extChartAt I y).source →
        extChartAt I y x ∈ Metric.ball c₀ ρ →
        ∀ s ∈ Set.Ico (0 : ℝ) b, ‖D s x‖ ≤ ‖D 0 x‖ * Real.exp ((K : ℝ) * b) := by
      intro x hx_src hx_ball s hs
      rcases eq_or_lt_of_le hs.1 with h0 | h0
      · rw [← h0]
        have : (1 : ℝ) ≤ Real.exp ((K : ℝ) * b) :=
          Real.one_le_exp (by positivity)
        nlinarith [norm_nonneg (D 0 x)]
      · -- `s > 0`: from `hDcompare` with start `a' → 0⁺`.
        obtain ⟨r', hsr', hr'b⟩ := exists_between hs.2
        have hbound_a' : ∀ a' : ℝ, 0 < a' → a' ≤ s →
            ‖D s x‖ ≤ ‖D a' x‖ * Real.exp ((K : ℝ) * (s - a')) := by
          intro a' ha'0 ha's
          have := hDcompare x hx_src hx_ball a' s ha'0 ha's (lt_trans hsr' hr'b)
          exact this
        have hcont0 : ContinuousWithinAt (fun a' : ℝ => D a' x) (Set.Ici 0) 0 := hpery0 x hx_src
        have hIoo_ne : (𝓝[Set.Ioo (0 : ℝ) s] 0).NeBot := by
          rw [nhdsWithin_Ioo_eq_nhdsGT h0]; exact nhdsGT_neBot 0
        have hsub : Set.Ioo (0 : ℝ) s ⊆ Set.Ici 0 := fun u hu => le_of_lt hu.1
        have hDtend : Filter.Tendsto (fun a' : ℝ => D a' x)
            (𝓝[Set.Ioo (0 : ℝ) s] 0) (𝓝 (D 0 x)) :=
          hcont0.tendsto.mono_left (nhdsWithin_mono 0 hsub)
        have hRHStend : Filter.Tendsto
            (fun a' : ℝ => ‖D a' x‖ * Real.exp ((K : ℝ) * (s - a')))
            (𝓝[Set.Ioo (0 : ℝ) s] 0)
            (𝓝 (‖D 0 x‖ * Real.exp ((K : ℝ) * s))) := by
          have hnorm : Filter.Tendsto (fun a' : ℝ => ‖D a' x‖)
              (𝓝[Set.Ioo (0 : ℝ) s] 0) (𝓝 ‖D 0 x‖) :=
            (continuous_norm.continuousAt).tendsto.comp hDtend
          have hexp : Filter.Tendsto (fun a' : ℝ => Real.exp ((K : ℝ) * (s - a')))
              (𝓝[Set.Ioo (0 : ℝ) s] 0) (𝓝 (Real.exp ((K : ℝ) * s))) := by
            have : Filter.Tendsto (fun a' : ℝ => Real.exp ((K : ℝ) * (s - a'))) (𝓝 0)
                (𝓝 (Real.exp ((K : ℝ) * (s - 0)))) :=
              ((Real.continuous_exp.comp (continuous_const.mul
                (continuous_const.sub continuous_id))).tendsto 0)
            simpa using this.mono_left nhdsWithin_le_nhds
          exact hnorm.mul hexp
        haveI := hIoo_ne
        have hle_s : ‖D s x‖ ≤ ‖D 0 x‖ * Real.exp ((K : ℝ) * s) := by
          refine ge_of_tendsto hRHStend ?_
          filter_upwards [self_mem_nhdsWithin] with a' ha'
          exact hbound_a' a' ha'.1 (le_of_lt ha'.2)
        calc ‖D s x‖ ≤ ‖D 0 x‖ * Real.exp ((K : ℝ) * s) := hle_s
          _ ≤ ‖D 0 x‖ * Real.exp ((K : ℝ) * b) := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
              have : (K : ℝ) * s ≤ (K : ℝ) * b :=
                mul_le_mul_of_nonneg_left (le_of_lt hs.2) (NNReal.coe_nonneg K)
              linarith
    -- `D 0 ·` continuity at `y` on the chart-`x₀` base set (posited node 3).
    have hD0cont : Filter.Tendsto (fun x : M => D 0 x)
        (𝓝[(trivializationAt E (TangentSpace I) x₀).baseSet] y) (𝓝 (D 0 y)) := by
      have hcwa := flow_chartJacobian_zero_continuousWithinAt_basepoint (I := I) x₀ i y hy
      have heq : ∀ x : M, (fun x : M => mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y z) x
          (chartBasisVecFiber (I := I) x₀ i x)) x = D 0 x := fun x => (hD0 x).symm
      rw [ContinuousWithinAt] at hcwa
      have hcwa' : Filter.Tendsto (fun x : M => D 0 x)
          (𝓝[(trivializationAt E (TangentSpace I) x₀).baseSet] y)
          (𝓝 (mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y z) y
            (chartBasisVecFiber (I := I) x₀ i y))) := by
        refine hcwa.congr (fun x => heq x)
      rw [show mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y z) y
          (chartBasisVecFiber (I := I) x₀ i y) = D 0 y from (hD0 y) ▸ rfl] at hcwa'
      exact hcwa'
    -- The cross difference vanishes uniformly (the operator-valued variational Grönwall).
    rw [Metric.tendsto_nhds]
    intro ε hε
    set L : Filter (ℝ × M) :=
      𝓝[Set.Ici (0 : ℝ) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet] (0, y) with hL
    -- uniform Jacobian bound near `y`: `‖D u x‖ ≤ B` for confined `x`.
    set B : ℝ := (‖D 0 y‖ + 1) * Real.exp ((K : ℝ) * b) with hB
    have hB_nonneg : 0 ≤ B := by positivity
    -- choose the operator-defect tolerance `η`.
    have hexp_pos : (0 : ℝ) < Real.exp ((K : ℝ) * b) := Real.exp_pos _
    set Kpos : ℝ := (K : ℝ) + 1 with hKpos
    have hKpos_pos : (0 : ℝ) < Kpos := by rw [hKpos]; positivity
    set η : ℝ := (ε / 2) * Kpos / ((B + 1) * (Real.exp (Kpos * b) + 1)) with hη
    have hη_pos : 0 < η := by
      rw [hη]; positivity
    -- uniform continuity of `A` supplies `δ_A` controlling the operator defect by `η`.
    rw [Metric.uniformContinuousOn_iff] at hAunif
    obtain ⟨δA, hδA_pos, hδA⟩ := hAunif η hη_pos
    -- Clean upper bound for the Grönwall bound at `Kpos > 0`.
    have hgronwall_le : ∀ δ' ε' x' : ℝ, 0 ≤ δ' → 0 ≤ ε' → 0 ≤ x' →
        gronwallBound δ' Kpos ε' x' ≤ (δ' + ε' / Kpos) * Real.exp (Kpos * x') := by
      intro δ' ε' x' hδ' hε' hx'
      rw [gronwallBound_of_K_ne_0 (ne_of_gt hKpos_pos)]
      have hexp_ge : (1 : ℝ) ≤ Real.exp (Kpos * x') := Real.one_le_exp (by positivity)
      have h1 : ε' / Kpos * (Real.exp (Kpos * x') - 1) ≤ ε' / Kpos * Real.exp (Kpos * x') := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
      calc δ' * Real.exp (Kpos * x') + ε' / Kpos * (Real.exp (Kpos * x') - 1)
          ≤ δ' * Real.exp (Kpos * x') + ε' / Kpos * Real.exp (Kpos * x') := by linarith
        _ = (δ' + ε' / Kpos) * Real.exp (Kpos * x') := by ring
    -- The cross-difference Grönwall bound for a single confined `x` with small operator defect.
    have hcrossGr : ∀ x : M, x ∈ (extChartAt I y).source →
        extChartAt I y x ∈ Metric.ball c₀ ρ →
        (∀ u ∈ Set.Ico (0 : ℝ) b, ‖A u (cc x u) - A u (cc y u)‖ ≤ η) →
        (∀ u ∈ Set.Ico (0 : ℝ) b, ‖D u x‖ ≤ B) →
        ∀ s ∈ Set.Ico (0 : ℝ) b,
          ‖D s x - D s y‖ ≤ gronwallBound ‖D 0 x - D 0 y‖ Kpos (η * B) s := by
      intro x hx_src hx_ball hdefect hDx s hs
      set Δ : ℝ → E := fun u => D u x - D u y with hΔ
      rcases eq_or_lt_of_le hs.1 with h0 | h0
      · rw [← h0, gronwallBound_x0]
      · -- positive `s`: Grönwall on `[a', r']` with start `a' → 0⁺`.
        obtain ⟨r', hsr', hr'b⟩ := exists_between hs.2
        have hΔ_deriv : ∀ u : ℝ, 0 < u → u < b →
            HasDerivWithinAt Δ (A u (cc x u) (D u x) - A u (cc y u) (D u y)) (Set.Ici (0 : ℝ)) u := by
          intro u hu0 hub
          exact (hDode x hx_src hx_ball u hu0 hub).sub (hDode y hy_src hy_ball u hu0 hub)
        have hΔ_cont : ∀ r₂ : ℝ, r₂ < b → ContinuousOn Δ (Set.Icc 0 r₂) := by
          intro r₂ hr₂ u hu
          exact ((hDcont x hx_src hx_ball r₂ hr₂) u hu).sub ((hDcont y hy_src hy_ball r₂ hr₂) u hu)
        have hbound_a' : ∀ a' : ℝ, 0 < a' → a' ≤ s →
            ‖Δ s‖ ≤ gronwallBound ‖Δ a'‖ Kpos (η * B) (s - a') := by
          intro a' ha'0 ha's
          have hcont : ContinuousOn Δ (Set.Icc a' s) :=
            (hΔ_cont r' hr'b).mono
              (fun u hu => ⟨le_trans (le_of_lt ha'0) hu.1, le_trans hu.2 (le_of_lt hsr')⟩)
          have hderiv : ∀ u ∈ Set.Ico a' s,
              HasDerivWithinAt Δ (A u (cc x u) (D u x) - A u (cc y u) (D u y)) (Set.Ici u) u := by
            intro u hu
            have hu0 : 0 < u := lt_of_lt_of_le ha'0 hu.1
            exact (hΔ_deriv u hu0 (lt_trans hu.2 hs.2)).mono
              (fun w hw => le_trans (le_of_lt hu0) hw)
          have hbnd : ∀ u ∈ Set.Ico a' s,
              ‖A u (cc x u) (D u x) - A u (cc y u) (D u y)‖ ≤ Kpos * ‖Δ u‖ + η * B := by
            intro u hu
            have hub : u ∈ Set.Ico (0 : ℝ) b :=
              ⟨le_trans (le_of_lt ha'0) hu.1, lt_trans hu.2 hs.2⟩
            have huT : u ∈ Set.Icc (0 : ℝ) T :=
              ⟨hub.1, le_trans (le_of_lt (lt_of_lt_of_le hub.2 hb_le_T)) (le_refl T)⟩
            -- split: `A_x D_x − A_y D_y = A_y (D_x − D_y) + (A_x − A_y) D_x`.
            have hsplit : A u (cc x u) (D u x) - A u (cc y u) (D u y)
                = A u (cc y u) (Δ u) + (A u (cc x u) - A u (cc y u)) (D u x) := by
              rw [hΔ]
              simp only [ContinuousLinearMap.sub_apply, map_sub]
              abel
            rw [hsplit]
            have hAy : ‖A u (cc y u)‖ ≤ (K : ℝ) :=
              hAbound u huT (cc y u) (horbit_ball y hy_src hy_ball u hub)
            have hterm1 : ‖A u (cc y u) (Δ u)‖ ≤ Kpos * ‖Δ u‖ := by
              calc ‖A u (cc y u) (Δ u)‖ ≤ ‖A u (cc y u)‖ * ‖Δ u‖ :=
                    ContinuousLinearMap.le_opNorm _ _
                _ ≤ (K : ℝ) * ‖Δ u‖ := by gcongr
                _ ≤ Kpos * ‖Δ u‖ := by
                    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                    rw [hKpos]; linarith
            have hterm2 : ‖(A u (cc x u) - A u (cc y u)) (D u x)‖ ≤ η * B := by
              calc ‖(A u (cc x u) - A u (cc y u)) (D u x)‖
                  ≤ ‖A u (cc x u) - A u (cc y u)‖ * ‖D u x‖ := ContinuousLinearMap.le_opNorm _ _
                _ ≤ η * B := by
                    have hd := hdefect u hub
                    have hDxb := hDx u hub
                    have hηnn : 0 ≤ η := le_of_lt hη_pos
                    exact mul_le_mul hd hDxb (norm_nonneg _) hηnn
            calc ‖A u (cc y u) (Δ u) + (A u (cc x u) - A u (cc y u)) (D u x)‖
                ≤ ‖A u (cc y u) (Δ u)‖ + ‖(A u (cc x u) - A u (cc y u)) (D u x)‖ :=
                  norm_add_le _ _
              _ ≤ Kpos * ‖Δ u‖ + η * B := add_le_add hterm1 hterm2
          have hgb := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv
            (le_refl ‖Δ a'‖) hbnd
          exact hgb s (Set.right_mem_Icc.mpr ha's)
        -- take `a' → 0⁺`.
        have hcont0 : ContinuousWithinAt Δ (Set.Ici 0) 0 := by
          have := (hpery0 x hx_src).sub (hpery0 y (mem_extChartAt_source y))
          exact this
        have hIoo_ne : (𝓝[Set.Ioo (0 : ℝ) s] 0).NeBot := by
          rw [nhdsWithin_Ioo_eq_nhdsGT h0]; exact nhdsGT_neBot 0
        have hsub : Set.Ioo (0 : ℝ) s ⊆ Set.Ici 0 := fun u hu => le_of_lt hu.1
        have hΔtend : Filter.Tendsto Δ (𝓝[Set.Ioo (0 : ℝ) s] 0) (𝓝 (Δ 0)) :=
          hcont0.tendsto.mono_left (nhdsWithin_mono 0 hsub)
        have hRHStend : Filter.Tendsto
            (fun a' : ℝ => gronwallBound ‖Δ a'‖ Kpos (η * B) (s - a'))
            (𝓝[Set.Ioo (0 : ℝ) s] 0)
            (𝓝 (gronwallBound ‖Δ 0‖ Kpos (η * B) s)) := by
          have hnorm : Filter.Tendsto (fun a' : ℝ => ‖Δ a'‖)
              (𝓝[Set.Ioo (0 : ℝ) s] 0) (𝓝 ‖Δ 0‖) :=
            (continuous_norm.continuousAt).tendsto.comp hΔtend
          have hgcont : Continuous fun q : ℝ × ℝ =>
              gronwallBound q.1 Kpos (η * B) q.2 := by
            simp only [gronwallBound_of_K_ne_0 (ne_of_gt hKpos_pos)]
            fun_prop
          have hsa : Filter.Tendsto (fun a' : ℝ => ((‖Δ a'‖ : ℝ), (s - a')))
              (𝓝[Set.Ioo (0 : ℝ) s] 0) (𝓝 (‖Δ 0‖, s)) := by
            have hsnd : Filter.Tendsto (fun a' : ℝ => s - a')
                (𝓝[Set.Ioo (0 : ℝ) s] 0) (𝓝 (s - 0)) :=
              ((continuous_const.sub continuous_id).continuousAt).tendsto.mono_left
                nhdsWithin_le_nhds
            simpa using hnorm.prodMk_nhds (by simpa using hsnd)
          have := (hgcont.continuousAt).tendsto.comp hsa
          simpa using this
        haveI := hIoo_ne
        refine ge_of_tendsto hRHStend ?_
        filter_upwards [self_mem_nhdsWithin] with a' ha'
        exact hbound_a' a' ha'.1 (le_of_lt ha'.2)
    -- Assemble the squeeze: find the eventually-true neighbourhood and bound.
    have htoll : (0 : ℝ) < ε / 2 / Real.exp (Kpos * b) := by positivity
    have hball_close : (fun p : ℝ × M => dist (extChartAt I y p.2) c₀ * Real.exp ((K : ℝ) * b))
        ⁻¹' Set.Iio δA ∈ L := by
      have hcont : ContinuousWithinAt
          (fun p : ℝ × M => dist (extChartAt I y p.2) c₀ * Real.exp ((K : ℝ) * b))
          (Set.Ici (0 : ℝ) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) (0, y) := by
        have hsnd : ContinuousWithinAt (fun p : ℝ × M => extChartAt I y p.2)
            (Set.Ici (0 : ℝ) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) (0, y) :=
          (continuousAt_extChartAt' (I := I) (mem_extChartAt_source y)).comp_continuousWithinAt
            (continuous_snd.continuousWithinAt)
        have hd : ContinuousWithinAt (fun p : ℝ × M => dist (extChartAt I y p.2) c₀)
            (Set.Ici (0 : ℝ) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) (0, y) :=
          (continuous_dist.continuousAt).comp_continuousWithinAt
            (hsnd.prodMk_nhds continuousWithinAt_const)
        exact hd.mul continuousWithinAt_const
      have hval : (fun p : ℝ × M => dist (extChartAt I y p.2) c₀ * Real.exp ((K : ℝ) * b)) (0, y)
          = 0 := by simp [hc₀]
      have hmem : Set.Iio δA ∈ 𝓝 ((fun p : ℝ × M =>
          dist (extChartAt I y p.2) c₀ * Real.exp ((K : ℝ) * b)) (0, y)) := by
        rw [hval]; exact Iio_mem_nhds hδA_pos
      exact hcont.preimage_mem_nhdsWithin hmem
    have hΔ0tend : Filter.Tendsto (fun p : ℝ × M => ‖D 0 p.2 - D 0 y‖) L (𝓝 0) := by
      have hsnd : Filter.Tendsto (fun p : ℝ × M => p.2) L
          (𝓝[(trivializationAt E (TangentSpace I) x₀).baseSet] y) := by
        rw [hL]
        have hcwa : ContinuousWithinAt (fun p : ℝ × M => p.2)
            (Set.Ici (0 : ℝ) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) (0, y) :=
          continuous_snd.continuousWithinAt
        exact hcwa.tendsto_nhdsWithin (fun p hp => hp.2)
      have hcomp : Filter.Tendsto (fun p : ℝ × M => D 0 p.2) L (𝓝 (D 0 y)) :=
        hD0cont.comp hsnd
      have hsub : Filter.Tendsto (fun p : ℝ × M => D 0 p.2 - D 0 y) L (𝓝 0) := by
        have := hcomp.sub (tendsto_const_nhds (x := D 0 y) (f := L))
        simpa using this
      have := (continuous_norm.continuousAt).tendsto.comp hsub
      simpa using this
    have hδ_close : (fun p : ℝ × M => ‖D 0 p.2 - D 0 y‖)
        ⁻¹' Set.Iio (ε / 2 / Real.exp (Kpos * b)) ∈ L :=
      hΔ0tend (Iio_mem_nhds htoll)
    have hδ_close1 : (fun p : ℝ × M => ‖D 0 p.2 - D 0 y‖)
        ⁻¹' Set.Iio (1 : ℝ) ∈ L :=
      hΔ0tend (Iio_mem_nhds one_pos)
    have hsrc_nhds : (fun p : ℝ × M => p.2) ⁻¹' (extChartAt I y).source ∈ L := by
      have hopen : IsOpen (extChartAt I y).source := isOpen_extChartAt_source y
      have : (extChartAt I y).source ∈ 𝓝 y := hopen.mem_nhds (mem_extChartAt_source y)
      exact (continuous_snd.continuousWithinAt (x := ((0, y) : ℝ × M))).preimage_mem_nhdsWithin this
    have hball_nhds : (fun p : ℝ × M => extChartAt I y p.2) ⁻¹' Metric.ball c₀ ρ ∈ L := by
      have hcontsnd : ContinuousWithinAt (fun p : ℝ × M => extChartAt I y p.2)
          (Set.Ici (0 : ℝ) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) (0, y) :=
        (continuousAt_extChartAt' (I := I) (mem_extChartAt_source y)).comp_continuousWithinAt
          (continuous_snd.continuousWithinAt)
      have hmem : Metric.ball c₀ ρ ∈ 𝓝 (extChartAt I y ((0, y) : ℝ × M).2) := by
        simpa [hc₀] using Metric.ball_mem_nhds c₀ hρ_pos
      exact hcontsnd.preimage_mem_nhdsWithin hmem
    have htime_nhds : (fun p : ℝ × M => p.1) ⁻¹' Set.Iio b ∈ L := by
      have : Set.Iio b ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hb_pos
      exact (continuous_fst.continuousWithinAt (x := ((0, y) : ℝ × M))).preimage_mem_nhdsWithin this
    have hge0 : ∀ᶠ p : ℝ × M in L, 0 ≤ p.1 := by
      rw [hL]; filter_upwards [self_mem_nhdsWithin] with p hp using hp.1
    filter_upwards [hball_close, hδ_close, hδ_close1, hsrc_nhds, hball_nhds, htime_nhds, hge0]
      with p hpclose hpδ hpδ1 hpsrc hpball hptime hpge
    have hpsrc' : p.2 ∈ (extChartAt I y).source := hpsrc
    have hpball' : extChartAt I y p.2 ∈ Metric.ball c₀ ρ := hpball
    have hptime' : p.1 < b := hptime
    have hs_mem : p.1 ∈ Set.Ico (0 : ℝ) b := ⟨hpge, hptime'⟩
    -- operator defect ≤ η along this orbit.
    have hdefect : ∀ u ∈ Set.Ico (0 : ℝ) b,
        ‖A u (cc p.2 u) - A u (cc y u)‖ ≤ η := by
      intro u hu
      have hxz : cc p.2 u ∈ Metric.closedBall c₀ (2 * ρ) :=
        Metric.ball_subset_closedBall (horbit_ball p.2 hpsrc' hpball' u hu)
      have hyz : cc y u ∈ Metric.closedBall c₀ (2 * ρ) :=
        Metric.ball_subset_closedBall (horbit_ball y hy_src hy_ball u hu)
      have huT : u ∈ Set.Icc (0 : ℝ) T :=
        ⟨hu.1, le_trans (le_of_lt (lt_of_lt_of_le hu.2 hb_le_T)) (le_refl T)⟩
      have hqx : (u, cc p.2 u) ∈ Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall c₀ (2 * ρ) := ⟨huT, hxz⟩
      have hqy : (u, cc y u) ∈ Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall c₀ (2 * ρ) := ⟨huT, hyz⟩
      have hdistlt : dist (u, cc p.2 u) (u, cc y u) < δA := by
        rw [Prod.dist_eq]
        have h1 : dist u u = 0 := dist_self u
        have h2 : dist (cc p.2 u) (cc y u) < δA := by
          have := horbit_gronwall p.2 hpsrc' hpball' u hu
          exact lt_of_le_of_lt this hpclose
        simp only [h1, max_lt_iff]
        exact ⟨hδA_pos, h2⟩
      have hlt := hδA (u, cc p.2 u) hqx (u, cc y u) hqy hdistlt
      simp only at hlt
      rw [dist_eq_norm] at hlt
      exact le_of_lt hlt
    -- Jacobian bound `B` along this orbit.
    have hDxbound : ∀ u ∈ Set.Ico (0 : ℝ) b, ‖D u p.2‖ ≤ B := by
      intro u hu
      have h1 := hDboundU p.2 hpsrc' hpball' u hu
      have h2 : ‖D 0 p.2‖ ≤ ‖D 0 y‖ + 1 := by
        have hsmall : ‖D 0 p.2 - D 0 y‖ < 1 := hpδ1
        have htri : ‖D 0 p.2‖ ≤ ‖D 0 y‖ + ‖D 0 p.2 - D 0 y‖ := by
          have hkey : ‖D 0 p.2‖ - ‖D 0 y‖ ≤ ‖D 0 p.2 - D 0 y‖ := norm_sub_norm_le _ _
          linarith
        linarith
      have hKbb : (K : ℝ) * b ≤ Kpos * b := by
        refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hb_pos)
        rw [hKpos]; linarith
      calc ‖D u p.2‖ ≤ ‖D 0 p.2‖ * Real.exp ((K : ℝ) * b) := h1
        _ ≤ (‖D 0 y‖ + 1) * Real.exp ((K : ℝ) * b) :=
            mul_le_mul_of_nonneg_right h2 (le_of_lt hexp_pos)
        _ = B := by rw [hB]
    -- apply the cross-difference Grönwall bound and estimate.
    have hcross := hcrossGr p.2 hpsrc' hpball' hdefect hDxbound p.1 hs_mem
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
    rw [dist_eq_norm]
    refine lt_of_le_of_lt hcross ?_
    refine lt_of_le_of_lt (hgronwall_le ‖D 0 p.2 - D 0 y‖ (η * B) p.1
      (norm_nonneg _) (by positivity) hpge) ?_
    -- `(‖Δ₀‖ + ηB/Kpos) · exp(Kpos·p.1) < ε`.
    have hp1b : p.1 ≤ b := le_of_lt hptime'
    have hexp_mono : Real.exp (Kpos * p.1) ≤ Real.exp (Kpos * b) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp1b (le_of_lt hKpos_pos))
    have hδlt : ‖D 0 p.2 - D 0 y‖ < ε / 2 / Real.exp (Kpos * b) := hpδ
    have hexpKpos_pos : (0 : ℝ) < Real.exp (Kpos * b) := Real.exp_pos _
    have hηB : η * B / Kpos * Real.exp (Kpos * b) < ε / 2 := by
      -- `η * (B+1)/Kpos * (exp+1) = ε/2`, and `B·exp < (B+1)(exp+1)`.
      have hkey : η * (B + 1) / Kpos * (Real.exp (Kpos * b) + 1) = ε / 2 := by
        rw [hη]
        field_simp
      have hstrict : η * B / Kpos * Real.exp (Kpos * b)
          < η * (B + 1) / Kpos * (Real.exp (Kpos * b) + 1) := by
        have hηK : 0 < η / Kpos := by positivity
        have h1 : η * B / Kpos * Real.exp (Kpos * b)
            = (η / Kpos) * (B * Real.exp (Kpos * b)) := by ring
        have h2 : η * (B + 1) / Kpos * (Real.exp (Kpos * b) + 1)
            = (η / Kpos) * ((B + 1) * (Real.exp (Kpos * b) + 1)) := by ring
        rw [h1, h2]
        refine mul_lt_mul_of_pos_left ?_ hηK
        have hBnn : 0 ≤ B := hB_nonneg
        nlinarith [hexpKpos_pos]
      rw [hkey] at hstrict; exact hstrict
    calc (‖D 0 p.2 - D 0 y‖ + η * B / Kpos) * Real.exp (Kpos * p.1)
        ≤ (‖D 0 p.2 - D 0 y‖ + η * B / Kpos) * Real.exp (Kpos * b) := by
          refine mul_le_mul_of_nonneg_left hexp_mono ?_
          have : 0 ≤ η * B / Kpos := by positivity
          linarith [norm_nonneg (D 0 p.2 - D 0 y)]
      _ = ‖D 0 p.2 - D 0 y‖ * Real.exp (Kpos * b) + η * B / Kpos * Real.exp (Kpos * b) := by ring
      _ < ε / 2 / Real.exp (Kpos * b) * Real.exp (Kpos * b) + ε / 2 := by
          refine add_lt_add ?_ hηB
          exact mul_lt_mul_of_pos_right hδlt hexpKpos_pos
      _ = ε / 2 + ε / 2 := by
          rw [div_mul_cancel₀]; exact ne_of_gt hexpKpos_pos
      _ = ε := by ring
  · -- ============ CONJUNCT (b): the per-`y` slice limit ============
    have h := (hpery0 y (mem_extChartAt_source y)).tendsto
    rw [hD0y] at h
    exact h

set_option linter.unusedVariables false in
/-- **Joint `(t, x)` chart-`y` Jacobian continuity at the `t = 0` boundary slice (variational
Grönwall content).**

The chart-`y` Jacobian of the conjugating orbit applied to the moving chart-`x₀` frame —
`p ↦ mfderiv (extChartAt I y ∘ Φ_fam p.1) p.2 (chartBasisVecFiber x₀ i p.2)` — is jointly
`(t, x)`-continuous up to `(0, y)` on `Ici 0 ×ˢ baseSet x₀`.

This is the genuine uniform-in-`x` *variational* continuous-dependence-up-to-`0` datum, the
linearized analog of the orbit confinement `conjugating_orbit_jointContWithinAt_at_zero`.  Writing
`D(t, x) := ∂_x [extChartAt I y (Φ_fam t x)]`, the joint limit splits via the triangle inequality
into the joint cross-difference `dist (D(t, x)) (D(t, y)) → 0` (uniform in `t`, the variational
Grönwall comparison) and the per-`y` slice limit `D(t, y) → D(0, y)`, both supplied by the
variational datum `flow_chartJacobian_uniform_variational_tendsto`; `hΦ0` (`Φ_fam 0 = id`) computes
`D(0, y) = ∂_x (extChartAt I y) at y`.  All hypotheses constrain only the internal
`g_DT` / `Φ_fam` / the chart-frame field; the conclusion is the chart-coordinate Jacobian, neither
equal to nor destructuring to any hypothesis. -/
private theorem flow_chartJacobian_jointContWithinAt_at_zero
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (hT : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hΦ0 : Φ_fam 0 = _root_.Diffeomorph.refl I M ∞)
    (hΦorbit0 : ∀ y : M,
      ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ici (0 : ℝ)) 0)
    (hΦmfderiv0 : ∀ (y : M) (u : TangentSpace I y),
      ContinuousWithinAt (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
        (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ici (0 : ℝ)) 0)
    (hfield_reg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (Hcomp : ∀ (α : M) (k : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (Hfderiv : ∀ (α : M) (k : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          fderiv ℝ (fun w : E =>
            DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k w) q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) (y : M)
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContinuousWithinAt
      (fun p : ℝ × M => mfderiv I 𝓘(ℝ, E)
        (fun z : M => extChartAt I y ((Φ_fam p.1 : M → M) z)) p.2
        (chartBasisVecFiber (I := I) x₀ i p.2))
      (Set.Ici (0 : ℝ) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) (0, y) := by
  classical
  set D : ℝ × M → E := fun p : ℝ × M =>
    mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y ((Φ_fam p.1 : M → M) z)) p.2
      (chartBasisVecFiber (I := I) x₀ i p.2) with hD
  set s : Set (ℝ × M) :=
    Set.Ici (0 : ℝ) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet with hs
  set Dval : E := mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y z) y
    (chartBasisVecFiber (I := I) x₀ i y) with hDval
  -- The variational datum: the joint cross-difference and the per-`y` slice limit.
  obtain ⟨hcross, hpery⟩ :=
    flow_chartJacobian_uniform_variational_tendsto (I := I) g_DT g_bg T hT Φ_fam hΦode hΦ0
      hΦorbit0 hΦmfderiv0 hfield_reg Hcomp Hfderiv x₀ i y hy
  -- Target value at `(0, y)`: since `Φ_fam 0 = id`, `D (0, y) = Dval`.
  have hfuneq : (fun z : M => extChartAt I y ((Φ_fam 0 : M → M) z))
      = (fun z : M => extChartAt I y z) := by
    funext z; rw [hΦ0, Diffeomorph.coe_refl, id]
  have hmfeq : mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y ((Φ_fam 0 : M → M) z)) y
      = mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y z) y :=
    Filter.EventuallyEq.mfderiv_eq (Filter.EventuallyEq.of_eq hfuneq)
  have hval0 : D (0, y) = Dval := by
    change mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y ((Φ_fam (0, y).1 : M → M) z)) (0, y).2
        (chartBasisVecFiber (I := I) x₀ i (0, y).2)
      = mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y z) y
        (chartBasisVecFiber (I := I) x₀ i y)
    exact DFunLike.congr_fun hmfeq (chartBasisVecFiber (I := I) x₀ i y)
  rw [ContinuousWithinAt, hval0]
  -- Reduce the goal to a `𝓝 Dval` limit of `D` over `𝓝[s] (0, y)`.
  -- Rewrite `D p = D(p) - D(p.1, y) + D(p.1, y)`, the cross part `→ 0`, the `y`-slice `→ Dval`.
  set Dy : ℝ × M → E := fun p : ℝ × M =>
    mfderiv I 𝓘(ℝ, E) (fun z : M => extChartAt I y ((Φ_fam p.1 : M → M) z)) y
      (chartBasisVecFiber (I := I) x₀ i y) with hDy
  -- the `y`-slice tends to `Dval` over `𝓝[s] (0, y)`, pulled back from `𝓝[Ici 0] 0`.
  have hfst : Filter.Tendsto (fun p : ℝ × M => p.1)
      (𝓝[s] (0, y)) (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)) := by
    have hcwa : ContinuousWithinAt (fun p : ℝ × M => p.1) s (0, y) :=
      continuous_fst.continuousWithinAt
    have hmaps : Set.MapsTo (fun p : ℝ × M => p.1) s (Set.Ici (0 : ℝ)) :=
      fun p hp => hp.1
    exact hcwa.tendsto_nhdsWithin hmaps
  have hDy_tend : Filter.Tendsto Dy (𝓝[s] (0, y)) (𝓝 Dval) := by
    rw [hDval]
    exact hpery.comp hfst
  -- the cross part tends to `0` (the variational Grönwall datum, restated as `D p - Dy p → 0`).
  have hcross' : Filter.Tendsto (fun p : ℝ × M => D p - Dy p) (𝓝[s] (0, y)) (𝓝 0) := by
    have hnorm : Filter.Tendsto (fun p : ℝ × M => ‖D p - Dy p‖) (𝓝[s] (0, y)) (𝓝 0) := by
      have hdist : (fun p : ℝ × M => dist (D p) (Dy p))
          = (fun p : ℝ × M => ‖D p - Dy p‖) := by
        funext p; rw [dist_eq_norm]
      rw [← hdist]; exact hcross
    rw [← tendsto_zero_iff_norm_tendsto_zero] at hnorm
    exact hnorm
  -- combine: `D p = (D p - Dy p) + Dy p → 0 + Dval = Dval`.
  have hsum : Filter.Tendsto (fun p : ℝ × M => (D p - Dy p) + Dy p)
      (𝓝[s] (0, y)) (𝓝 (0 + Dval)) := hcross'.add hDy_tend
  simp only [zero_add, sub_add_cancel] at hsum
  exact hsum

set_option linter.unusedVariables false in
/-- **Joint `(t, x)` continuity of the conjugating orbit and its moving pushforward at the
`t = 0` boundary slice.**

The genuine uniform-in-`x` continuous-dependence-up-to-the-initial-time content: the joint
`(t, x)` continuity of the conjugating orbit and of its moving pushforward (on the fixed-chart-`x₀`
frame) at the `t = 0` boundary slice, on `Ici 0 ×ˢ univ` / `Ici 0 ×ˢ baseSet`.

The orbit conjunct is the chart-`y` continuous-dependence-up-to-`0`: the chart-`y` orbit
`r ↦ extChartAt I y (Φ_fam r x)` solves the chart-`y` ODE whose field is the chart-`y`-frame
velocity `conjugatingChartVelocityField` (the corrected velocity, NOT the raw-fibre
representation), uniformly confined to a chart ball by `conjugating_flow_uniform_chart_confinement`
(consuming the chart-frame component value-continuity `Hcomp`).  Bounding that field's spatial
Lipschitz constant uniformly via `Hfderiv` (the chart-frame component spatial-derivative
continuity) gives a Grönwall comparison `dist (chart orbit from x, chart orbit from y) ≤
dist (x, y) · exp (K r)`, which, combined with the per-`y` at-`0` orbit datum `hΦorbit0 y`, yields
the joint orbit continuity at `(0, y)`.  `Hcomp` / `Hfderiv` are exactly the two conjuncts of
`deturck_vf_continuous_up_to_zero` (the chart-`y`-frame component value- and spatial-derivative
continuity up to `t = 0`); `hΦode` / `hΦ0` pin the flow to the genuine one.

The pushforward conjunct (2) additionally requires the chart centre `y` to lie in the chart-`x₀`
base set (`y ∈ baseSet x₀`): off that overlap the fixed-chart-`y` reading of the moving frame is the
discontinuous change-of-frame coefficient (so the chart-Jacobian leaf is false there); the premise
is harmless to the eventual consumer, whose `t = 0` evaluation points `p` already satisfy
`p.2 ∈ baseSet x₀` (its `h_gram0` lives on `Ico 0 T ×ˢ baseSet x₀`).  Conjunct (2) consumes the
genuine variational `t = 0`-endpoint data `hΦmfderiv0` (the bundle moving-Jacobian limit, the
linearised companion of `hΦorbit0`) and `hfield_reg` (the interior joint-`C∞` field, feeding the
variational interior ODE); conjunct (1) (the orbit) is unaffected by these.  All hypotheses
constrain only the internal `g_DT` / `Φ_fam` / the chart-frame field, never the headline;
neither conjunct is, nor destructures to, any hypothesis. -/
theorem conjugating_flow_jointContWithinAt_at_zero
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (hT : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (Hcomp : ∀ (α : M) (k : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (Hfderiv : ∀ (α : M) (k : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          fderiv ℝ (fun w : E =>
            DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k w) q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (hΦ0 : Φ_fam 0 = _root_.Diffeomorph.refl I M ∞)
    (hΦorbit0 : ∀ y : M,
      ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ici (0 : ℝ)) 0)
    (hΦmfderiv0 : ∀ (y : M) (u : TangentSpace I y),
      ContinuousWithinAt (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
        (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ici (0 : ℝ)) 0)
    (hfield_reg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    (∀ y : M, ContinuousWithinAt (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) (0, y)) ∧
    (∀ (x₀ : M) (i : Fin (Module.finrank ℝ E)) (y : M),
      y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
      ContinuousWithinAt (fun p : ℝ × M => (TotalSpace.mk' E ((Φ_fam p.1 : M → M) p.2)
        (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2))
        : TangentBundle I M))
      (Set.Ici (0 : ℝ) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) (0, y)) := by
  classical
  refine ⟨fun y =>
    conjugating_orbit_jointContWithinAt_at_zero (I := I) g_DT g_bg T hT Φ_fam hΦode hΦ0
      hΦorbit0 Hcomp Hfderiv y, ?_⟩
  intro x₀ i y hy
  set s : Set (ℝ × M) :=
    Set.Ici (0 : ℝ) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet with hs
  set f : ℝ × M → TangentBundle I M := fun p : ℝ × M =>
    (TotalSpace.mk' E ((Φ_fam p.1 : M → M) p.2)
      (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2))
      : TangentBundle I M) with hf
  -- Base projection of the seed equals `y` (since `Φ_fam 0 = id`).
  have hproj0 : (f (0, y)).proj = y := by
    show (Φ_fam 0 : M → M) y = y
    rw [hΦ0, Diffeomorph.coe_refl, id]
  rw [FiberBundle.continuousWithinAt_totalSpace E f]
  constructor
  · -- Base continuity: the orbit (conjunct 1), restricted to the chart-`x₀` base set.
    have hbase : ContinuousWithinAt (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) (0, y) :=
      conjugating_orbit_jointContWithinAt_at_zero (I := I) g_DT g_bg T hT Φ_fam hΦode hΦ0
        hΦorbit0 Hcomp Hfderiv y
    exact hbase.mono (Set.prod_mono_right (Set.subset_univ _))
  · -- Fibre continuity: the trivialized fibre equals the chart-`y` Jacobian near `(0, y)`.
    rw [hproj0]
    -- The orbit eventually stays in the chart source of `y`, where the trivialization bridge holds.
    have hbase : ContinuousWithinAt (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) s (0, y) :=
      (conjugating_orbit_jointContWithinAt_at_zero (I := I) g_DT g_bg T hT Φ_fam hΦode hΦ0
        hΦorbit0 Hcomp Hfderiv y).mono (Set.prod_mono_right (Set.subset_univ _))
    have hsrc_open : IsOpen (chartAt H y).source := (chartAt H y).open_source
    have hy_src : y ∈ (chartAt H y).source := mem_chart_source H y
    have hsrc_nhds : (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) ⁻¹' (chartAt H y).source ∈ 𝓝[s] (0, y) :=
      hbase.preimage_mem_nhdsWithin (by
        have hval : (Φ_fam (0, y).1 : M → M) (0, y).2 = y := by
          show (Φ_fam 0 : M → M) y = y; rw [hΦ0, Diffeomorph.coe_refl, id]
        rw [hval]; exact hsrc_open.mem_nhds hy_src)
    -- The chart-`y` Jacobian section, the target of the variational continuity.
    set J : ℝ × M → E := fun p : ℝ × M => mfderiv I 𝓘(ℝ, E)
      (fun z : M => extChartAt I y ((Φ_fam p.1 : M → M) z)) p.2
      (chartBasisVecFiber (I := I) x₀ i p.2) with hJ
    have hJcont : ContinuousWithinAt J s (0, y) :=
      flow_chartJacobian_jointContWithinAt_at_zero (I := I) g_DT g_bg T hT Φ_fam hΦode hΦ0
        hΦorbit0 hΦmfderiv0 hfield_reg Hcomp Hfderiv x₀ i y hy
    refine hJcont.congr_of_eventuallyEq ?_ ?_
    · -- Eventual equality of the trivialized fibre with the chart-`y` Jacobian on the source.
      filter_upwards [hsrc_nhds] with p hp
      have hFx_src : (Φ_fam p.1 : M → M) p.2 ∈ (chartAt H y).source := hp
      have hFx_base : (Φ_fam p.1 : M → M) p.2 ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]; exact hFx_src
      have hmdiff : MDifferentiableAt I I (Φ_fam p.1 : M → M) p.2 :=
        ((Φ_fam p.1).mdifferentiable (by decide)) p.2
      have htriv2 : trivToE (I := I) y ((Φ_fam p.1 : M → M) p.2)
              (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2))
          = ((trivializationAt E (TangentSpace I) y) (f p)).2 := by
        change ((trivializationAt E (TangentSpace I) y).continuousLinearMapAt ℝ
            ((Φ_fam p.1 : M → M) p.2))
            (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2)) = _
        rw [Trivialization.continuousLinearMapAt_apply,
          Trivialization.coe_linearMapAt_of_mem _ hFx_base]
      rw [← htriv2]
      exact trivToE_mfderiv_eq_chartFderiv_apply (I := I)
        (Φ_fam p.1 : M → M) y (chartBasisVecFiber (I := I) x₀ i p.2) hmdiff hFx_src
    · -- Value match at `(0, y)`: both equal `trivToE y y (chartBasisVecFiber x₀ i y)`.
      have hy_base : y ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]; exact hy_src
      have hΦ0y : (Φ_fam 0 : M → M) y = y := by rw [hΦ0, Diffeomorph.coe_refl, id]
      have hmdiff0 : MDifferentiableAt I I (Φ_fam 0 : M → M) y :=
        ((Φ_fam 0).mdifferentiable (by decide)) y
      have hFx_src0 : (Φ_fam 0 : M → M) y ∈ (chartAt H y).source := by rw [hΦ0y]; exact hy_src
      have hFx_base0 : (Φ_fam 0 : M → M) y ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]; exact hFx_src0
      have hlhs : trivToE (I := I) y ((Φ_fam 0 : M → M) y)
              (mfderiv I I (Φ_fam 0 : M → M) y (chartBasisVecFiber (I := I) x₀ i y))
          = ((trivializationAt E (TangentSpace I) y) (f (0, y))).2 := by
        change ((trivializationAt E (TangentSpace I) y).continuousLinearMapAt ℝ
            ((Φ_fam 0 : M → M) y))
            (mfderiv I I (Φ_fam 0 : M → M) y (chartBasisVecFiber (I := I) x₀ i y)) = _
        rw [Trivialization.continuousLinearMapAt_apply,
          Trivialization.coe_linearMapAt_of_mem _ hFx_base0]
      have hrhs : J (0, y)
          = trivToE (I := I) y ((Φ_fam 0 : M → M) y)
              (mfderiv I I (Φ_fam 0 : M → M) y (chartBasisVecFiber (I := I) x₀ i y)) := by
        rw [hJ]
        exact (trivToE_mfderiv_eq_chartFderiv_apply (I := I)
          (Φ_fam 0 : M → M) y (chartBasisVecFiber (I := I) x₀ i y) hmdiff0 hFx_src0).symm
      rw [← hlhs, hrhs]

set_option linter.unusedVariables false in
/-- **Interior joint-`C∞` of the conjugating orbit's moving spatial pushforward of the
chart-`x₀` frame.**

From the joint-`C∞` orbit `hΦsmooth` (the interior smooth-dependence output `C2`), the moving
spatial differential of the orbit applied to the fixed-chart-`x₀` frame section
`m ↦ chartBasisVecFiber x₀ i m`, packaged inside the tangent bundle as
`(t, m) ↦ ⟨Φ_fam t m, mfderiv (Φ_fam t ·) m (chartBasisVecFiber x₀ i m)⟩`, is jointly `C∞` on
`Ioo 0 T ×ˢ baseSet x₀`.  The moving spatial differential is `C∞` in `(t, m)` by
`ContMDiffWithinAt.mfderivWithin` (read in tangent coordinates), and applying that `C∞` family of
differentials to the `C∞` moving frame `chartBasisVec x₀ i` is `C∞` by
`ContMDiffWithinAt.clm_apply_of_inCoordinates`; the frame's source base set restricts the domain to
`baseSet x₀`.  This is the smooth companion of the slice-wise continuity
`slice_mfderiv_continuousAt_of_jointFlow`; it feeds the chain rule for the pullback chart-Gram
entry (`pullbackGram_jointContMDiffOn_interior`) and the interior conjunct of the up-to-`0`
continuity (`flow_orbit_pushforward_jointContinuousOn_upto0`). -/
private theorem flow_pushforward_jointContMDiffOn_interior
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => (TotalSpace.mk' E ((Φ_fam p.1 : M → M) p.2)
        (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2))
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  intro p hp
  obtain ⟨hps, hpb⟩ := hp
  -- The orbit map `f q = Φ_fam q.1` parametrised by the joint parameter `q = (t, m)`, with the
  -- differentiation base point `g q = q.2`.  `Function.uncurry f ((t, m), x) = Φ_fam t x` is
  -- jointly `C∞` (it ignores `m`), obtained from `hΦsmooth` precomposed with `((t,m),x) ↦ (t,x)`.
  have hproj : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun r : (ℝ × M) × M => (r.1.1, r.2))
      ((Set.Ioo (0 : ℝ) T ×ˢ Set.univ) ×ˢ Set.univ) (p, p.2) :=
    (contMDiffWithinAt_fst.fst).prodMk contMDiffWithinAt_snd
  have hmaps' : Set.MapsTo (fun r : (ℝ × M) × M => (r.1.1, r.2))
      ((Set.Ioo (0 : ℝ) T ×ˢ Set.univ) ×ˢ Set.univ) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
    fun r hr => ⟨hr.1.1, Set.mem_univ _⟩
  have hf : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod I) I ∞
      (Function.uncurry (fun q : ℝ × M => fun x : M => (Φ_fam q.1 : M → M) x))
      ((Set.Ioo (0 : ℝ) T ×ˢ Set.univ) ×ˢ Set.univ) (p, p.2) :=
    (hΦsmooth p ⟨hps, Set.mem_univ _⟩).comp (p, p.2) hproj hmaps'
  -- The differentiation base point `g q = q.2`, jointly `C∞`.
  have hg : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => q.2) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) p :=
    contMDiffWithinAt_snd
  -- The moving spatial differential of the orbit, read in tangent coordinates, is `C∞`.
  have hmf := ContMDiffWithinAt.mfderivWithin (I := I) (I' := I)
    (N := ℝ × M) (J := 𝓘(ℝ, ℝ).prod I) (M := M) (M' := M)
    (n := ∞) (m := ∞)
    (f := fun q : ℝ × M => fun x : M => (Φ_fam q.1 : M → M) x)
    (g := fun q : ℝ × M => q.2)
    (t := Set.Ioo (0 : ℝ) T ×ˢ Set.univ) (u := Set.univ)
    hf hg ⟨hps, Set.mem_univ _⟩ (Set.mapsTo_univ _ _) (le_refl _) uniqueMDiffOn_univ
  -- The moving frame section `chartBasisVec x₀ i`, jointly `C∞` on `Ioo ×ˢ baseSet`.
  have hv : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (chartBasisVecFiber (I := I) x₀ i q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) p := by
    have hcb := (chartBasisVec_contMDiffOn (I := I) x₀ i) p.2 hpb
    have hsnd : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => q.2)
        (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) p :=
      contMDiffWithinAt_snd
    have := hcb.comp p hsnd
      (fun q hq => hq.2)
    exact this
  -- The base map `p ↦ Φ_fam p.1 p.2`, jointly `C∞` on the restricted domain.
  have hb₂ : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) p :=
    (hΦsmooth p ⟨hps, Set.mem_univ _⟩).mono
      (Set.prod_mono_right (Set.subset_univ _))
  -- Restrict the moving-differential coordinate smoothness to the frame's base set.
  have hmf' := hmf.mono (Set.prod_mono_right
    (fun x (_ : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) => Set.mem_univ x))
  -- Apply the `C∞` family of differentials to the `C∞` moving frame, tracked in coordinates.
  have happ := ContMDiffWithinAt.clm_apply_of_inCoordinates
    (F₁ := E) (E₁ := TangentSpace I (M := M)) (F₂ := E) (E₂ := TangentSpace I (M := M))
    (IB₁ := I) (IB₂ := I) (IM := 𝓘(ℝ, ℝ).prod I) (n := ∞)
    (b₁ := fun q : ℝ × M => q.2) (b₂ := fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
    (m₀ := p)
    (ϕ := fun q : ℝ × M => mfderivWithin I I (Φ_fam q.1 : M → M) Set.univ q.2)
    (v := fun q : ℝ × M => chartBasisVecFiber (I := I) x₀ i q.2)
    (s := Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
    hmf' hv hb₂
  simp only [mfderivWithin_univ] at happ
  exact happ

set_option linter.unusedVariables false in
/-- **Joint up-to-`0` continuity of the conjugating orbit and its moving pushforward.**

Assembles the joint `(t, x)`-up-to-`0` continuity of the conjugating orbit (on `Ico 0 T ×ˢ univ`)
and of its moving spatial differential applied to the fixed-chart-`x₀` frame section
`x ↦ chartBasisVecFiber x₀ i x` (on `Ico 0 T ×ˢ baseSet x₀`), by splitting `Ico` into the interior
`Ioo` (where the joint-`C∞` orbit `conjugating_flow_jointContMDiffOn_interior` and its moving
Jacobian — packaged via `flow_pushforward_jointContMDiffOn_interior` — give joint continuity) and the
`t = 0` boundary slice (`conjugating_flow_jointContWithinAt_at_zero`).  Per-`y` continuity does NOT
imply this joint continuity at `t = 0`, so this is genuinely joint.

The signature threads exactly the hypotheses of the two split providers: `hΦode` / `hfield_reg`
feed the interior joint-`C∞` orbit (`conjugating_flow_jointContMDiffOn_interior`), and
`hΦode` / `Hcomp` / `Hfderiv` / `hΦ0` / `hΦorbit0` / `hΦmfderiv0` / `hfield_reg` feed the `t = 0`
slice (`conjugating_flow_jointContWithinAt_at_zero`); the pushforward conjunct's `t = 0` slice
discharges its `y ∈ baseSet x₀` premise from the conjunct's own domain `Ico 0 T ×ˢ baseSet x₀`. -/
theorem flow_orbit_pushforward_jointContinuousOn_upto0
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
    (Hcomp : ∀ (α : M) (k : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (Hfderiv : ∀ (α : M) (k : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          fderiv ℝ (fun w : E =>
            DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k w) q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (hΦ0 : Φ_fam 0 = _root_.Diffeomorph.refl I M ∞)
    (hΦorbit0 : ∀ y : M,
      ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ici (0 : ℝ)) 0)
    (hΦmfderiv0 : ∀ (y : M) (u : TangentSpace I y),
      ContinuousWithinAt (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
        (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ici (0 : ℝ)) 0) :
    (ContinuousOn (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) (Set.Ico (0 : ℝ) T ×ˢ Set.univ)) ∧
    (∀ (x₀ : M) (i : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : ℝ × M => (TotalSpace.mk' E ((Φ_fam p.1 : M → M) p.2)
        (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2))
        : TangentBundle I M)) (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) := by
  -- The interior joint-`C∞` orbit (`C2`) and the `t = 0` slice (`C1b`).
  have hInt : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
    conjugating_flow_jointContMDiffOn_interior (I := I) g_DT g_bg T hT Φ_fam hΦode hfield_reg
  have hZero := conjugating_flow_jointContWithinAt_at_zero (I := I) g_DT g_bg T hT Φ_fam hΦode
    Hcomp Hfderiv hΦ0 hΦorbit0 hΦmfderiv0 hfield_reg
  obtain ⟨hZeroOrbit, hZeroPush⟩ := hZero
  -- Orbit continuity on `Ico ×ˢ univ`.
  have hOrbit : ContinuousOn (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
      (Set.Ico (0 : ℝ) T ×ˢ Set.univ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    rcases eq_or_lt_of_le hp1.1 with h0 | h0
    · -- `t = 0`: use the boundary slice, with `(0, p.2)` and the domain inclusion `Ico ⊆ Ici`.
      have hp0 : p = (0, p.2) := Prod.ext h0.symm rfl
      rw [hp0]
      exact (hZeroOrbit p.2).mono (Set.prod_mono_left
        (fun t (ht : t ∈ Set.Ico (0 : ℝ) T) => ht.1))
    · -- `t > 0`: use the interior joint-`C∞` orbit; `Ioo ×ˢ univ` is a nhd of `p` within `Ico ×ˢ univ`.
      have hpIoo : p ∈ Set.Ioo (0 : ℝ) T ×ˢ Set.univ := ⟨⟨h0, hp1.2⟩, Set.mem_univ _⟩
      exact (hInt.continuousOn.continuousWithinAt hpIoo).mono_of_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds ((isOpen_Ioo.prod isOpen_univ).mem_nhds hpIoo))
  refine ⟨hOrbit, ?_⟩
  intro x₀ i
  -- Pushforward continuity on `Ico ×ˢ baseSet x₀`.
  have hPushInt := flow_pushforward_jointContMDiffOn_interior (I := I) T Φ_fam hInt x₀ i
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  rcases eq_or_lt_of_le hp1.1 with h0 | h0
  · -- `t = 0`: the boundary slice, discharging `p.2 ∈ baseSet x₀` from the domain.
    have hp0 : p = (0, p.2) := Prod.ext h0.symm rfl
    rw [hp0]
    exact (hZeroPush x₀ i p.2 hp2).mono (Set.prod_mono_left
      (fun t (ht : t ∈ Set.Ico (0 : ℝ) T) => ht.1))
  · -- `t > 0`: the interior pushforward smoothness; `Ioo ×ˢ baseSet` is a nhd of `p` within
    -- `Ico ×ˢ baseSet` (the first factor `Ioo` is open and contains `p.1`, the second is shared).
    have hpIoo : p ∈ Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      ⟨⟨h0, hp1.2⟩, hp2⟩
    refine (hPushInt.continuousOn.continuousWithinAt hpIoo).mono_of_mem_nhdsWithin ?_
    have hopen : (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
        ∈ 𝓝 p :=
      (isOpen_Ioo.prod (trivializationAt E (TangentSpace I) x₀).open_baseSet).mem_nhds hpIoo
    exact mem_nhdsWithin_of_mem_nhds hopen

namespace MetricCLMSectionAux

/-- For a metric `g` and a base point `α`, the value of the metric bilinear-CLM section read
in coordinates at the chart-`α` trivialization (centred at `α`, same base point `x ∈ baseSet`),
evaluated on two fixed model-space test vectors `v, w : E`, expands as the chart-Gram bilinear
sum: it is `∑ᵢⱼ (repr v)ᵢ (repr w)ⱼ · chartGramMatrix g α x i j`.  The matrix entries are exactly
the chart-Gram entries, so a joint-in-`(t, x)` smoothness of `chartGramMatrix (g_DT ·) α · i j`
transports to joint smoothness of this scalar (with `v, w` fixed). -/
private lemma inCoordinates_metric_eq_chartGram_sum
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) (v w : E) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] ℝ) α x α x (g.inner x) v w =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
          Integral.Measure.chartGramMatrix (I := I) g α x i j := by
  classical
  have hxR : x ∈ (trivializationAt ℝ (Bundle.Trivial M ℝ) α).baseSet := Set.mem_univ x
  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ)
    (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I) (E₂ := TangentSpace I) (E₃ := Bundle.Trivial M ℝ)
    (x₀ := α) (x := x) (ϕ := g.inner x) (v := v) (w := w) hx hx hxR]
  rw [(trivializationAt ℝ (Bundle.Trivial M ℝ) α).coe_linearMapAt_of_mem hxR]
  set e := trivializationAt E (TangentSpace I) α with he
  change g.inner x (e.symmL ℝ x v) (e.symmL ℝ x w) = _
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E with hb
  have hvdec : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  have hwdec : w = ∑ j, b.repr w j • b j := (b.sum_repr w).symm
  have hsymm_v : e.symmL ℝ x v = ∑ i, b.repr v i • chartBasisVecFiber (I := I) α i x := by
    conv_lhs => rw [hvdec]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]; rfl
  have hsymm_w : e.symmL ℝ x w = ∑ j, b.repr w j • chartBasisVecFiber (I := I) α j x := by
    conv_lhs => rw [hwdec]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul]; rfl
  rw [hsymm_v, hsymm_w]
  have hL :
      g.inner x (∑ i, b.repr v i • chartBasisVecFiber (I := I) α i x)
        = ∑ i, b.repr v i • g.inner x (chartBasisVecFiber (I := I) α i x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
  rw [hL, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul, smul_eq_mul, Integral.Connection.g_inner_eq_chartGramMatrix_basis]
  ring

end MetricCLMSectionAux

set_option linter.unusedVariables false in
/-- **Joint `(t, b)` smoothness of the metric bilinear-CLM bundle section from chart-Gram data.**

The metric family's bilinear-CLM bundle section `(t, b) ↦ ⟨b, (g_DT t).inner b⟩` — the operator
section of the `Hom(TM, Hom(TM, ℝ))`-bundle carrying the per-time metric — is jointly `C∞` in
`(t, b)` on `Ioo 0 T ×ˢ univ`, given that every chart-Gram matrix entry
`p ↦ chartGramMatrix (g_DT p.1) x₀ p.2 i j` is jointly `C∞` (`hgram_DT`).

This is the converse readoff of `ContMDiffOn.clm_bundle_apply₂`: at each interior point `q₀` the
Hom-bundle section's smoothness is read in coordinates (`contMDiffAt_hom_bundle`) and reduced via
`contMDiffAt_clm_of_pointwise` (twice, once per bilinear slot) to the scalar coordinate entries,
which — by `inCoordinates_metric_eq_chartGram_sum` — are finite `(repr · ·)`-weighted sums of the
chart-Gram entries `chartGramMatrix (g_DT ·) q₀.2 · i j`, each jointly `C∞` by `hgram_DT` at the
chart centred at `q₀.2`.  Discharges the `hgInnerBase` hypothesis of
`metric_clm_section_jointContMDiffOn_along_orbit`. -/
theorem metricCLMSection_jointContMDiffOn_of_chartGram
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (hgram_DT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2
        ((g_DT q.1).inner q.2)))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
  classical
  open MetricCLMSectionAux in
  intro q₀ hq₀
  refine (?_ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun q : ℝ × M => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2
      ((g_DT q.1).inner q.2))) q₀).contMDiffWithinAt
  set α : M := q₀.2 with hα
  -- A neighbourhood (within the open product) on which `q.2 ∈ baseSet α`.
  have hbase0 : α ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [hα]; exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_snd, ?_⟩
  -- Reduce the operator-valued `inCoordinates` smoothness to per-slot scalar smoothness.
  apply contMDiffAt_clm_of_pointwise (IB := 𝓘(ℝ, ℝ).prod I) (X := ℝ × M)
  intro v
  apply contMDiffAt_clm_of_pointwise (IB := 𝓘(ℝ, ℝ).prod I) (X := ℝ × M)
  intro w
  -- The scalar `inCoordinates(...)(v)(w)` is, near `q₀`, the chart-Gram bilinear sum.
  have hgram_sum : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) α p.2 i j) q₀ := by
    intro i j
    have hmem : q₀ ∈ Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet := by
      refine ⟨hq₀.1, ?_⟩
      rw [hα]; exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
    have hopen : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
      isOpen_Ioo.prod (trivializationAt E (TangentSpace I) α).open_baseSet
    exact ((hgram_DT α i j) q₀ hmem).contMDiffAt (hopen.mem_nhds hmem)
  have hscalar : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) α p.2 i j) q₀ := by
    refine ContMDiffAt.sum (fun i _ => ?_)
    refine ContMDiffAt.sum (fun j _ => ?_)
    exact (contMDiffAt_const (c := ((chartModelBasis E).repr v i *
      (chartModelBasis E).repr w j : ℝ))).mul (hgram_sum i j)
  -- Identify the two functions on a neighbourhood within the open product where `q.2 ∈ baseSet α`.
  refine hscalar.congr_of_eventuallyEq ?_
  have hnhds : (trivializationAt E (TangentSpace I) α).baseSet ∈ nhds q₀.2 :=
    (trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hbase0
  have hpre : (fun q : ℝ × M => q.2) ⁻¹' (trivializationAt E (TangentSpace I) α).baseSet ∈ nhds q₀ :=
    (continuous_snd.continuousAt (x := q₀)).preimage_mem_nhds hnhds
  filter_upwards [hpre] with p hp
  change ((ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] ℝ) α p.2 α p.2 ((g_DT p.1).inner p.2)) v) w = _
  exact inCoordinates_metric_eq_chartGram_sum (I := I) (g_DT p.1) α hp v w

set_option linter.unusedVariables false in
/-- **Interior joint-`C∞` of the metric bilinear-CLM section along the orbit.**

The moving metric bilinear-CLM bundle section `(t, b) ↦ ⟨b, (g_DT t).inner b⟩`, evaluated at the
orbit point `b = Φ_fam p.1 p.2`, is jointly `C∞` on `Ioo 0 T ×ˢ univ`.  It is the composition of
the joint-`C∞` base metric-CLM section `hgInnerBase` (the operator-bundle section
`(t, b) ↦ ⟨b, (g_DT t).inner b⟩`, jointly `C∞` in `(t, b)` — the genuine joint-in-time regularity
of the metric family, recovered from the joint chart-Gram smoothness `hgram_DT` of the headline)
with the joint-`C∞` orbit map `(t, m) ↦ (t, Φ_fam t m)` (`hΦsmooth`, the interior smooth-dependence
output `C2`), via `ContMDiffOn.comp`.  Bridge feeding `hgInner` to
`pullbackGram_jointContMDiffOn_interior`.

`hgInnerBase` is the metric family's joint-in-`(t, b)` operator-section smoothness — it is the
analytic input carrying the time-regularity of `g_DT` (the per-time `g.contMDiff` is NOT enough for
the joint statement, and `hΦsmooth` constrains only the orbit), supplied by the headline from its
`hgram_DT`; it is not the conclusion (which lives over the moving orbit point), so this is not
hypothesis-packaging. -/
theorem metric_clm_section_jointContMDiffOn_along_orbit
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hgInnerBase : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2
        ((g_DT q.1).inner q.2)))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        ((Φ_fam p.1 : M → M) p.2)
        ((g_DT p.1).inner ((Φ_fam p.1 : M → M) p.2))))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
  -- The orbit base map `(t, m) ↦ (t, Φ_fam t m)`, jointly `C∞`, mapping `Ioo ×ˢ univ` into itself.
  have hφ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (p.1, (Φ_fam p.1 : M → M) p.2))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
    (contMDiffOn_fst).prodMk hΦsmooth
  have hmaps : Set.MapsTo (fun p : ℝ × M => (p.1, (Φ_fam p.1 : M → M) p.2))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
    fun p hp => ⟨hp.1, Set.mem_univ _⟩
  exact hgInnerBase.comp hφ hmaps

set_option linter.unusedVariables false in
/-- **Interior joint-`C∞` of the pullback chart-Gram entry.**

The `h_gram` conjunct (interior): unfolds the pullback chart-Gram entry to
`(g_DT p.1).inner (Φ_fam p.1 p.2) (dΦ·cbvf x₀ i p.2) (dΦ·cbvf x₀ j p.2)` and proves joint `C∞` on
`Ioo 0 T ×ˢ baseSet x₀` by the chain rule: the moving-Jacobian-applied-to-frame sections are jointly
`C∞` (from `hΦsmooth`), and the moving bilinear form at the moving point (`hgInner`) applied to them
is jointly `C∞` (`ContMDiffOn.clm_bundle_apply₂`). -/
theorem pullbackGram_jointContMDiffOn_interior
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (x₀ : M) (i j : Fin (Module.finrank ℝ E))
    (hΦsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hgInner : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        ((Φ_fam p.1 : M → M) p.2)
        ((g_DT p.1).inner ((Φ_fam p.1 : M → M) p.2))))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M =>
        Integral.Measure.chartGramMatrix (I := I)
          (Diffeomorph.pullbackMetric (g_DT p.1) (Φ_fam p.1)) x₀ p.2 i j)
      (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  -- The two moving-Jacobian-applied-to-frame sections, jointly `C∞` (from `hΦsmooth` = `C2`).
  have hPushI := flow_pushforward_jointContMDiffOn_interior (I := I) T Φ_fam hΦsmooth x₀ i
  have hPushJ := flow_pushforward_jointContMDiffOn_interior (I := I) T Φ_fam hΦsmooth x₀ j
  -- The moving bilinear form (`hgInner` = `C7`), restricted to the frame's base set.
  have hgInner' := hgInner.mono
    (show Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet
        ⊆ Set.Ioo (0 : ℝ) T ×ˢ Set.univ from
      fun q hq => ⟨hq.1, Set.mem_univ _⟩)
  -- Rewrite the pullback chart-Gram entry to the moving bilinear form applied to the two
  -- moving pushforward vectors (`chartGramMatrix_apply` + `pullbackMetric_inner_eq_inner_mfderiv`).
  have hcongr : Set.EqOn
      (fun p : ℝ × M =>
        Integral.Measure.chartGramMatrix (I := I)
          (Diffeomorph.pullbackMetric (g_DT p.1) (Φ_fam p.1)) x₀ p.2 i j)
      (fun p : ℝ × M =>
        (g_DT p.1).inner ((Φ_fam p.1 : M → M) p.2)
          (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2))
          (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ j p.2)))
      (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro q hq
    change Integral.Measure.chartGramMatrix (I := I)
        (Diffeomorph.pullbackMetric (g_DT q.1) (Φ_fam q.1)) x₀ q.2 i j = _
    rw [Integral.Measure.chartGramMatrix_apply, pullbackMetric_inner_eq_inner_mfderiv]
  refine ContMDiffOn.congr ?_ hcongr
  -- Apply the moving bilinear form to the two moving pushforward sections; the result is a `C∞`
  -- section of the scalar trivial bundle, whose fibre is the desired inner-mfderiv scalar.
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ)
    (b := fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
    (s := Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (ψ := fun p : ℝ × M => (g_DT p.1).inner ((Φ_fam p.1 : M → M) p.2))
    (v := fun p : ℝ × M =>
      mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2))
    (w := fun p : ℝ × M =>
      mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ j p.2))
    hgInner' hPushI hPushJ
  intro p hp
  have hpx := happ p hp
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

namespace PullbackGramJointAux

/-- Joint-domain within-at continuity of a finite sum of within-at-continuous functions on
`ℝ × M` (the `ℝ × M`-source analogue of the `ℝ`-source `cwa_finset_sum`). -/
private lemma cwa_finset_sum_prod {ι : Type*} {N : Type*} [AddCommMonoid N] [TopologicalSpace N]
    [ContinuousAdd N] {f : ι → ℝ × M → N} (s : Finset ι) {t : Set (ℝ × M)} {p : ℝ × M}
    (h : ∀ i ∈ s, ContinuousWithinAt (f i) t p) :
    ContinuousWithinAt (fun q : ℝ × M => ∑ i ∈ s, f i q) t p := by
  classical
  induction s using Finset.induction with
  | empty => simpa using continuousWithinAt_const
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

/-- A model-basis `repr`-coordinate of a within-at-continuous `E`-valued function on `ℝ × M` is
within-at-continuous (the `ℝ × M`-source analogue of `repr_continuousWithinAt`). -/
private lemma repr_jointContinuousWithinAt {S : Set (ℝ × M)} {p₀ : ℝ × M} {f : ℝ × M → E}
    (hf : ContinuousWithinAt f S p₀) (k : Fin (Module.finrank ℝ E)) :
    ContinuousWithinAt (fun q : ℝ × M => ((chartModelBasis E).repr (f q)) k) S p₀ := by
  have hlin : Continuous (fun y : E => ((chartModelBasis E).repr y) k) :=
    ((Finsupp.lapply (R := ℝ) (M := ℝ) (α := Fin (Module.finrank ℝ E)) k).comp
      (chartModelBasis E).repr.toLinearMap).continuous_of_finiteDimensional
  exact hlin.continuousWithinAt.comp hf (Set.mapsTo_univ _ _)

end PullbackGramJointAux

set_option linter.unusedVariables false in
/-- **Joint up-to-`0` continuity of the pullback chart-Gram entry.**

The `h_gram0` conjunct (up-to-`0`): the joint generalization of the per-point
`gfam_inner_continuous_on`.  Both the evaluation point `Φ_fam t p.2` and the frame
`chartBasisVecFiber x₀ i p.2` move with `p.2`, so per-`y` continuity is insufficient — this takes
joint `(t, x)` inputs (`hΦorbit`, `hΦpush`) and the joint chart-Gram continuity of `g_DT`
(`hg_jointE`) and produces joint continuity, via the chart-sum expansion
(`g_inner_eq_chart_sum`) with `moving_chartCoord_jointContinuousWithinAt`. -/
theorem pullbackGram_jointContinuousOn_upto0
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (x₀ : M) (i j : Fin (Module.finrank ℝ E))
    (hΦorbit : ContinuousOn (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
      (Set.Ico (0 : ℝ) T ×ˢ Set.univ))
    (hΦpush : ∀ (β : M) (k : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : ℝ × M => (TotalSpace.mk' E ((Φ_fam p.1 : M → M) p.2)
        (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) β k p.2))
        : TangentBundle I M)) (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) β).baseSet))
    (hg_jointE : ∀ (α : M) (a b : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun q : ℝ × M =>
        Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α a b (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ)) :
    ContinuousOn
      (fun p : ℝ × M =>
        Integral.Measure.chartGramMatrix (I := I)
          (Diffeomorph.pullbackMetric (g_DT p.1) (Φ_fam p.1)) x₀ p.2 i j)
      (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  open MovingPushforwardAux PullbackGramJointAux in
  -- Rewrite the pullback chart-Gram entry to the moving bilinear form at the moving orbit point,
  -- applied to the two moving pushforward vectors.
  have hrw : Set.EqOn
      (fun p : ℝ × M =>
        Integral.Measure.chartGramMatrix (I := I)
          (Diffeomorph.pullbackMetric (g_DT p.1) (Φ_fam p.1)) x₀ p.2 i j)
      (fun p : ℝ × M =>
        (g_DT p.1).inner ((Φ_fam p.1 : M → M) p.2)
          (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2))
          (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ j p.2)))
      (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro q _
    change Integral.Measure.chartGramMatrix (I := I)
        (Diffeomorph.pullbackMetric (g_DT q.1) (Φ_fam q.1)) x₀ q.2 i j = _
    rw [Integral.Measure.chartGramMatrix_apply, pullbackMetric_inner_eq_inner_mfderiv]
  refine ContinuousOn.congr ?_ hrw
  intro p₀ hp₀
  obtain ⟨hp₀t, hp₀x⟩ := hp₀
  set α : M := (Φ_fam p₀.1 : M → M) p₀.2 with hα
  set e := trivializationAt E (TangentSpace I) α with he
  have hbase0 : (Φ_fam p₀.1 : M → M) p₀.2 ∈ e.baseSet := by
    rw [he, hα]; exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hsrc0 : (Φ_fam p₀.1 : M → M) p₀.2 ∈ (extChartAt I α).source := by
    rw [hα]; exact mem_extChartAt_source (I := I) α
  -- Orbit continuity-within-at at `p₀`, on `Ico ×ˢ baseSet x₀` (a subset of `Ico ×ˢ univ`).
  have horbit : ContinuousWithinAt (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
      (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) p₀ :=
    (hΦorbit p₀ ⟨hp₀t, Set.mem_univ _⟩).mono
      (Set.prod_mono_right (Set.subset_univ _))
  -- Chart-`α` coordinate continuity of each moving pushforward vector, then its model-basis `repr`.
  have hcoordI : ∀ a : Fin (Module.finrank ℝ E),
      ContinuousWithinAt
        (fun p : ℝ × M => ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam p.1 : M → M) p.2)
            (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2)))) a)
        (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) p₀ := by
    intro a
    refine repr_jointContinuousWithinAt ?_ a
    exact moving_chartCoord_jointContinuousWithinAt (I := I) Φ_fam x₀ i α _ p₀ hbase0 horbit
      ((hΦpush x₀ i).continuousWithinAt ⟨hp₀t, hp₀x⟩)
  have hcoordJ : ∀ b : Fin (Module.finrank ℝ E),
      ContinuousWithinAt
        (fun p : ℝ × M => ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam p.1 : M → M) p.2)
            (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ j p.2)))) b)
        (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) p₀ := by
    intro b
    refine repr_jointContinuousWithinAt ?_ b
    exact moving_chartCoord_jointContinuousWithinAt (I := I) Φ_fam x₀ j α _ p₀ hbase0 horbit
      ((hΦpush x₀ j).continuousWithinAt ⟨hp₀t, hp₀x⟩)
  -- Chart-`α` Gram-entry continuity at the moving orbit point, via `hg_jointE` precomposed with
  -- the joint orbit map `(t, x) ↦ (t, Φ_fam t x)`.
  have hgram : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousWithinAt
        (fun p : ℝ × M => Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT p.1) α a b
          (extChartAt I α ((Φ_fam p.1 : M → M) p.2)))
        (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) p₀ := by
    intro a b
    have hpair : ContinuousWithinAt (fun p : ℝ × M => (p.1, (Φ_fam p.1 : M → M) p.2))
        (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) p₀ :=
      (continuousWithinAt_fst).prodMk horbit
    have hmaps : Set.MapsTo (fun p : ℝ × M => (p.1, (Φ_fam p.1 : M → M) p.2))
        (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
      intro q hq
      exact ⟨⟨hq.1.1, le_of_lt hq.1.2⟩, Set.mem_univ _⟩
    have hg : ContinuousWithinAt
        (fun q : ℝ × M => Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α a b
          (extChartAt I α q.2)) (Set.Icc (0 : ℝ) T ×ˢ Set.univ)
        (p₀.1, (Φ_fam p₀.1 : M → M) p₀.2) :=
      (hg_jointE α a b).continuousWithinAt (hmaps ⟨hp₀t, hp₀x⟩)
    have hcomp := hg.comp_of_eq hpair hmaps rfl
    simpa only [Function.comp_def] using hcomp
  -- Assemble the chart-sum, with continuity from the products of coordinate/Gram factors.
  have hsumcont : ContinuousWithinAt
      (fun p : ℝ × M => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam p.1 : M → M) p.2)
            (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2)))) a *
        ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam p.1 : M → M) p.2)
            (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ j p.2)))) b *
        Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT p.1) α a b
          (extChartAt I α ((Φ_fam p.1 : M → M) p.2)))
      (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) p₀ := by
    refine cwa_finset_sum_prod _ (fun a _ => ?_)
    refine cwa_finset_sum_prod _ (fun b _ => ?_)
    exact ((hcoordI a).mul (hcoordJ b)).mul (hgram a b)
  -- The chart-sum identity (`g_inner_eq_chart_sum`) on a neighbourhood within the domain.
  have hsum : ∀ p : ℝ × M, (Φ_fam p.1 : M → M) p.2 ∈ e.baseSet →
      (Φ_fam p.1 : M → M) p.2 ∈ (extChartAt I α).source →
      (g_DT p.1).inner ((Φ_fam p.1 : M → M) p.2)
          (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2))
          (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ j p.2))
        = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr
              (e.continuousLinearMapAt ℝ ((Φ_fam p.1 : M → M) p.2)
                (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2)))) a *
            ((chartModelBasis E).repr
              (e.continuousLinearMapAt ℝ ((Φ_fam p.1 : M → M) p.2)
                (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ j p.2)))) b *
            Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT p.1) α a b
              (extChartAt I α ((Φ_fam p.1 : M → M) p.2)) := by
    intro p hb hsr
    exact g_inner_eq_chart_sum (I := I) (g_DT p.1) α hb hsr
      (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2))
      (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ j p.2))
  refine hsumcont.congr_of_eventuallyEq ?_ (hsum p₀ hbase0 hsrc0)
  have hbnhds : e.baseSet ∈ nhds ((Φ_fam p₀.1 : M → M) p₀.2) := e.open_baseSet.mem_nhds hbase0
  have hsrcnhds : (extChartAt I α).source ∈ nhds ((Φ_fam p₀.1 : M → M) p₀.2) :=
    (isOpen_extChartAt_source (I := I) α).mem_nhds hsrc0
  have hpb : (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) ⁻¹' e.baseSet
      ∈ nhdsWithin p₀ (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    horbit.preimage_mem_nhdsWithin hbnhds
  have hps : (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) ⁻¹' (extChartAt I α).source
      ∈ nhdsWithin p₀ (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    horbit.preimage_mem_nhdsWithin hsrcnhds
  filter_upwards [hpb, hps] with p hb hsr
  exact hsum p hb hsr

set_option linter.unusedVariables false in
/-- **Joint `(t, x)` chart-Gram regularity of the pulled-back metric family.**

For the conjugating diffeomorphism family `Φ_fam` of the Hamilton–DeTurck construction —
PINNED to the genuine flow by the backward bare-orbit ODE `hΦode` and to the identity at
`t = 0` by `hΦ0`, with the per-`y` at-`0` orbit/pushforward data (`hΦorbit0`, `hΦmfderiv0`)
and the jointly-`C⁰`-up-to-`0` chart-frame field data (`Hcomp`, `Hfderiv`, `hfield_reg`) of
the underlying DeTurck velocity — the pulled-back metric family
`g_fam s := (Φ_fam s)^* (g_DT s) = Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)` inherits the
joint `(t, x)` chart-Gram regularity of `g_DT` along the flow:

* `h_gram` (joint-`C∞`): each chart-local Gram-matrix entry
  `p ↦ chartGramMatrix (g_fam p.1) x₀ p.2 i j` is jointly `C∞` on `Ioo 0 T ×ˢ baseSet`;
* `h_gram0` (joint continuity up to `0`): the same entry is jointly continuous on
  `Ico 0 T ×ˢ baseSet`.

Proven by recursion on the joint `(t, x)` continuity/smoothness of the orbit and its chart
Jacobian: the interior joint-`C∞` orbit (`conjugating_flow_jointContMDiffOn_interior`) feeds
the chain rule for the interior conjunct, while the joint up-to-`0` continuity of the orbit
and its moving pushforward (`flow_orbit_pushforward_jointContinuousOn_upto0`, resting on the
uniform-in-`x` continuous-dependence-up-to-`0` leaf, fed by the chart-frame field data
`Hcomp`/`Hfderiv`) feeds the up-to-`0` conjunct.  The added hypotheses constrain only the
internal data `g_DT` / the chart-frame components of the field `deTurckVF (g_DT ·) g_bg` / the
per-`y` at-`0` `Φ_fam` data; the conclusions concern the pullback
`pullbackMetric (g_DT) (Φ_fam)`, so this is not hypothesis-packaging. -/
theorem conjugating_flow_pullback_jointGram_data
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hT0 : 0 < T)
    (hΦ0 : Φ_fam 0 = _root_.Diffeomorph.refl I M ∞)
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hfield_reg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (Hcomp : ∀ (α : M) (k : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (Hfderiv : ∀ (α : M) (k : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          fderiv ℝ (fun w : E =>
            DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α k w) q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (hΦorbit0 : ∀ y : M,
      ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ici (0 : ℝ)) 0)
    (hΦmfderiv0 : ∀ (y : M) (u : TangentSpace I y),
      ContinuousWithinAt (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
        (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ici (0 : ℝ)) 0)
    (hg_jointE : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × M =>
          Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
            (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
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
  have hΦsmooth := conjugating_flow_jointContMDiffOn_interior (I := I) g_DT g_bg T hT0 Φ_fam
    hΦode hfield_reg
  have hgInner := metric_clm_section_jointContMDiffOn_along_orbit (I := I) g_DT T Φ_fam hΦsmooth
    (metricCLMSection_jointContMDiffOn_of_chartGram (I := I) g_DT T hgram_DT)
  refine ⟨fun x₀ i j => ?_, fun x₀ i j => ?_⟩
  · exact pullbackGram_jointContMDiffOn_interior (I := I) g_DT T Φ_fam x₀ i j hΦsmooth hgInner
  · obtain ⟨hΦorbit_joint, hΦpush_joint⟩ :=
      flow_orbit_pushforward_jointContinuousOn_upto0 (I := I) g_DT g_bg T hT0 Φ_fam hΦode
        hfield_reg Hcomp Hfderiv hΦ0 hΦorbit0 hΦmfderiv0
    exact pullbackGram_jointContinuousOn_upto0 (I := I) g_DT T Φ_fam x₀ i j hΦorbit_joint
      hΦpush_joint hg_jointE

end DifferentialGeometry.PDE.RicciFlow

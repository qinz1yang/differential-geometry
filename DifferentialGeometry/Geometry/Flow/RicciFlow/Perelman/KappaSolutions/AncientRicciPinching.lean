import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.RicciPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Definitions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic
open CanonicalNeighborhood
open scoped Manifold ContDiff Topology

private theorem nonnegative_at_right_endpoint
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousWithinAt f (Iic b) b)
    (hnonneg : ∀ s ∈ Ioo a b, 0 ≤ f s) : 0 ≤ f b := by
  have hlim : Tendsto f (𝓝[<] b) (𝓝 (f b)) :=
    hcont.mono Iio_subset_Iic_self
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hab] with s hs
  exact hnonneg s hs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [SigmaCompactSpace M]

private theorem ancient_ricci_pinching_regular
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval)
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3)
    {a b c : ℝ} (hab : a ≤ b) (hb : b < 0) (hc : c < 1 / 3)
    (hinit : ∀ x : M, ∀ v : TangentSpace I x,
      c * S.scalar a x * (S.family.metric a).inner x v v ≤
        S.ricciAt a x (vec2 v v)) :
    ∀ x : M, ∀ v : TangentSpace I x,
      c * S.scalar b x * (S.family.metric b).inner x v v ≤
        S.ricciAt b x (vec2 v v) := by
  let St := S.timeShift a
  have hSt : IsSolutionOn St := isSolutionOn_timeShift hS a
  have hcarrier : Icc 0 (b - a) ⊆ (ancientTimeInterval.timeShift a).carrier := by
    intro s hs
    change s + a ≤ 0
    linarith [hs.2]
  have hregular : Ioc 0 (b - a) ⊆ (ancientTimeInterval.timeShift a).regular := by
    intro s hs
    change s + a < 0
    linarith [hs.2]
  have hstart : TwoTensorFamilyNonnegativeAtTime
      (pinchTensor (fun t => St.base.metric t)
        (twoTensorSecToFamily St.ricci) St.scalar c) 0 := by
    intro x v
    change 0 ≤ S.ricciAt (0 + a) x (vec2 v v) -
      c * S.scalar (0 + a) x * (S.family.metric (0 + a)).inner x v v
    simpa only [zero_add] using sub_nonneg.mpr (hinit x v)
  have hp := pinch_solution_closed (smoothOfSolution St hSt) (sub_nonneg.mpr hab) hc
    (fun _x => hdim) hcarrier hregular hstart
  intro x v
  have h := hp (b - a) ⟨sub_nonneg.mpr hab, le_rfl⟩ x v
  change 0 ≤ S.ricciAt ((b - a) + a) x (vec2 v v) -
    c * S.scalar ((b - a) + a) x * (S.family.metric ((b - a) + a)).inner x v v at h
  simpa only [sub_add_cancel] using sub_nonneg.mp h

omit [I.Boundaryless] [CompactSpace M] [SigmaCompactSpace M] in
private theorem ancient_ricci_pinch_gap_continuous
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval)
    (hS : IsSolutionOn S) (c : ℝ) (x : M) (v : TangentSpace I x) :
    ContinuousOn (fun s => S.ricciAt s x (vec2 v v) -
      c * S.scalar s x * (S.family.metric s).inner x v v) (Iic 0) := by
  have h := tensorEval_contOn (pinchSecFamilyContinuousOnSet S hS c) x v v
  change ContinuousOn
    (fun s => twoTensorSecToFamily (pinchSec S c) s x v v) ancientTimeInterval.carrier at h
  rw [pinchSec_eq S c] at h
  exact h


theorem ancient_ricci_pinching_preserved
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval)
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3)
    {a b c : ℝ} (hab : a ≤ b) (hb : b ≤ 0) (hc : c < 1 / 3)
    (hinit : ∀ x : M, ∀ v : TangentSpace I x,
      c * S.scalar a x * (S.family.metric a).inner x v v ≤
        S.ricciAt a x (vec2 v v)) :
    ∀ x : M, ∀ v : TangentSpace I x,
      c * S.scalar b x * (S.family.metric b).inner x v v ≤
        S.ricciAt b x (vec2 v v) := by
  rcases hab.eq_or_lt with hab | hab
  · subst b
    exact hinit
  intro x v
  apply sub_nonneg.mp
  apply nonnegative_at_right_endpoint (a := a) hab
  · exact (ancient_ricci_pinch_gap_continuous S hS c x v b hb).mono
      (fun s hs => hs.trans hb)
  · intro s hs
    exact sub_nonneg.mpr
      (ancient_ricci_pinching_regular S hS hdim hs.1.le (hs.2.trans_le hb) hc hinit x v)


theorem ancient_ricci_lower_bound_of_backward_pinching
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval)
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3)
    {a c : ℕ → ℝ} (ha : Tendsto a atTop atBot)
    (hc : Tendsto c atTop (𝓝 (1 / 3)))
    (hcUpper : ∀ i, c i < 1 / 3)
    (hinit : ∀ i, ∀ x : M, ∀ v : TangentSpace I x,
      c i * S.scalar (a i) x * (S.family.metric (a i)).inner x v v ≤
        S.ricciAt (a i) x (vec2 v v)) :
    ∀ b : ℝ, b ≤ 0 → ∀ x : M, ∀ v : TangentSpace I x,
      (S.scalar b x / 3) * (S.family.metric b).inner x v v ≤
        S.ricciAt b x (vec2 v v) := by
  intro b hb x v
  have hle : ∀ᶠ i in atTop,
      c i * S.scalar b x * (S.family.metric b).inner x v v ≤
        S.ricciAt b x (vec2 v v) := by
    filter_upwards [ha.eventually (eventually_le_atBot b)] with i hi
    exact ancient_ricci_pinching_preserved S hS hdim hi hb (hcUpper i) (hinit i) x v
  have h := le_of_tendsto
    ((hc.mul_const (S.scalar b x)).mul_const ((S.family.metric b).inner x v v)) hle
  have hcoef : (1 / 3 : ℝ) * S.scalar b x = S.scalar b x / 3 := by ring
  rwa [hcoef] at h

omit [I.Boundaryless] [CompactSpace M] [SigmaCompactSpace M] in
private theorem ricci_einstein_of_sharp_lower_bound
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval)
    (hdim : Module.finrank ℝ E = 3) (b : ℝ) (x : M)
    (hlower : ∀ v : TangentSpace I x,
      (S.scalar b x / 3) * (S.family.metric b).inner x v v ≤
        S.ricciAt b x (vec2 v v)) :
    ∀ v w : TangentSpace I x, S.ricciAt b x (vec2 v w) =
      (S.scalar b x / 3) * (S.family.metric b).inner x v w := by
  classical
  let g := S.family.metric b
  let Ric := S.ricciAt b x
  obtain ⟨basis, l1, l2, l3, horth, hdiag⟩ :=
    ricciEigen3 g Ric hdim (ricci_is_symmetric S b x)
  have hscalar : S.scalar b x = l1 + l2 + l3 := by
    rw [SolutionOn.scalar_eq_metricTrace S b x]
    exact scalar_eq_diag (scalarTrace_delta g Ric horth) hdiag
  have hlo (i : Fin 3) : S.scalar b x / 3 ≤ ricciDiag3 l1 l2 l3 i i := by
    have h := hlower (basis i)
    have hr := hdiag.2 i i
    rw [ricciCompAt_apply] at hr
    change S.ricciAt b x (vec2 (basis i) (basis i)) = ricciDiag3 l1 l2 l3 i i at hr
    change (S.scalar b x / 3) * g.inner x (basis i) (basis i) ≤ _ at h
    rw [horth i i, hr] at h
    simpa [delta3] using h
  have h0 : S.scalar b x / 3 ≤ l1 := by simpa [ricciDiag3] using hlo 0
  have h1 : S.scalar b x / 3 ≤ l2 := by simpa [ricciDiag3] using hlo 1
  have h2 : S.scalar b x / 3 ≤ l3 := by simpa [ricciDiag3] using hlo 2
  have he0 : l1 = S.scalar b x / 3 := by linarith
  have he1 : l2 = S.scalar b x / 3 := by linarith
  have he2 : l3 = S.scalar b x / 3 := by linarith
  let T := ricciEndAt g Ric
  obtain ⟨hT0, hT1, hT2⟩ := ricciEnd_diagVec g horth hdiag
  have hTbasis (i : Fin 3) : T (basis i) = (S.scalar b x / 3) • basis i := by
    fin_cases i
    · simpa [T, he0] using hT0
    · simpa [T, he1] using hT1
    · simpa [T, he2] using hT2
  have hT : T = (S.scalar b x / 3) •
      (LinearMap.id : TangentSpace I x →ₗ[ℝ] TangentSpace I x) := by
    apply basis.ext
    intro i
    exact hTbasis i
  intro v w
  calc
    S.ricciAt b x (vec2 v w) = g.inner x (T v) w := (ricciEnd_inner g Ric v w).symm
    _ = (S.scalar b x / 3) * (S.family.metric b).inner x v w := by
      rw [hT]
      simp [g]


theorem ancient_ricci_einstein_of_backward_pinching
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval)
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3)
    {a c : ℕ → ℝ} (ha : Tendsto a atTop atBot)
    (hc : Tendsto c atTop (𝓝 (1 / 3))) (hcUpper : ∀ i, c i < 1 / 3)
    (hinit : ∀ i, ∀ x : M, ∀ v : TangentSpace I x,
      c i * S.scalar (a i) x * (S.family.metric (a i)).inner x v v ≤
        S.ricciAt (a i) x (vec2 v v)) :
    ∀ b : ℝ, b ≤ 0 → ∀ x : M, ∀ v w : TangentSpace I x,
      S.ricciAt b x (vec2 v w) =
        (S.scalar b x / 3) * (S.family.metric b).inner x v w := by
  intro b hb x
  exact ricci_einstein_of_sharp_lower_bound S hdim b x
    (ancient_ricci_lower_bound_of_backward_pinching S hS hdim ha hc hcUpper hinit b hb x)


theorem ancient_scalar_constant_of_backward_pinching [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval)
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3)
    {a c : ℕ → ℝ} (ha : Tendsto a atTop atBot)
    (hc : Tendsto c atTop (𝓝 (1 / 3))) (hcUpper : ∀ i, c i < 1 / 3)
    (hinit : ∀ i, ∀ x : M, ∀ v : TangentSpace I x,
      c i * S.scalar (a i) x * (S.family.metric (a i)).inner x v v ≤
        S.ricciAt (a i) x (vec2 v v)) :
    ∀ b : ℝ, b ≤ 0 → ∃ R : ℝ, ∀ x : M, S.scalar b x = R := by
  intro b hb
  have hEin := ancient_ricci_einstein_of_backward_pinching S hS hdim ha hc hcUpper hinit b hb
  let g := S.family.metric b
  have hEinStatic : ∀ x : M, ∀ v w : TangentSpace I x,
      metricRicciAt g x (vec2 v w) = (metricScalarAt g x / 3) * g.inner x v w := hEin
  apply metricScalar_const_of_dScalar_zero g
  intro x X
  obtain ⟨basis, _l1, _l2, _l3, horth, _hdiag⟩ :=
    ricciEigen3 g (S.ricciAt b x) hdim (ricci_is_symmetric S b x)
  exact dScalar_zero_ein3_at g basis delta3 (orthonormal_invBasis3 g basis horth) hEinStatic X


theorem ancient_constant_sectional_of_backward_pinching [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval)
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3)
    {a c : ℕ → ℝ} (ha : Tendsto a atTop atBot)
    (hc : Tendsto c atTop (𝓝 (1 / 3))) (hcUpper : ∀ i, c i < 1 / 3)
    (hinit : ∀ i, ∀ x : M, ∀ v : TangentSpace I x,
      c i * S.scalar (a i) x * (S.family.metric (a i)).inner x v v ≤
        S.ricciAt (a i) x (vec2 v v)) :
    ∀ b : ℝ, b ≤ 0 → ∃ K : ℝ, ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (S.family.metric b) x X Y Y X =
        K * ((S.family.metric b).inner x X X * (S.family.metric b).inner x Y Y -
          (S.family.metric b).inner x X Y * (S.family.metric b).inner x X Y) := by
  intro b hb
  obtain ⟨R, hR⟩ := ancient_scalar_constant_of_backward_pinching S hS hdim ha hc hcUpper hinit b hb
  have hEin := ancient_ricci_einstein_of_backward_pinching S hS hdim ha hc hcUpper hinit b hb
  refine ⟨R / 6, fun x X Y => ?_⟩
  let g := S.family.metric b
  obtain ⟨basis, _l1, _l2, _l3, horth, _hdiag⟩ :=
    ricciEigen3 g (S.ricciAt b x) hdim (ricci_is_symmetric S b x)
  have htrace := riemann_from_ricci_trace S (t := b) (x := x) (basis := basis) horth
  have hneg (i j : Fin 3) : ricciCompAt basis (-(S.ricciAt b x)) i j =
      ((-S.scalar b x) / 3) * delta3 i j := by
    rw [ricciCompAt_apply]
    change -(S.ricciAt b x (vec2 (basis i) (basis j))) = _
    rw [hEin x (basis i) (basis j)]
    change -((S.scalar b x / 3) * g.inner x (basis i) (basis j)) = _
    rw [horth i j]
    ring
  have hRm := rm04_einstein3_at htrace hneg X Y
  calc
    _ = -((-S.scalar b x) / 6) *
        (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y) := hRm
    _ = _ := by rw [hR x]; ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessStrictStability

set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem mapCInf_add_on_open {V : Set E} (hV : IsOpen V)
    {f g : ℕ → E → ℝ} {f₀ g₀ : E → ℝ}
    (hf : MapCInfConvergenceOnCompacts V f f₀) (hg : MapCInfConvergenceOnCompacts V g g₀)
    (hfc : ∀ n, ContDiffOn ℝ ∞ (f n) V) (hf₀c : ContDiffOn ℝ ∞ f₀ V)
    (hgc : ∀ n, ContDiffOn ℝ ∞ (g n) V) (hg₀c : ContDiffOn ℝ ∞ g₀ V) :
    MapCInfConvergenceOnCompacts V (fun n y => f n y + g n y) (fun y => f₀ y + g₀ y) := by
  have hp := mapCInfConvergence_prodMk hV hf hg hfc hf₀c hgc hg₀c
  have haddc : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => z.1 + z.2) Set.univ :=
    contDiffOn_fst.add contDiffOn_snd
  have hcomp := MapCInfConvergenceOnCompacts.comp hV isOpen_univ hp
    (mapCInfConvergence_const (U := (Set.univ : Set (ℝ × ℝ))) (fun z : ℝ × ℝ => z.1 + z.2))
    (fun n => (hfc n).prodMk (hgc n)) (hf₀c.prodMk hg₀c)
    (fun _ => haddc) haddc (mapsTo_univ _ _) (fun _ => mapsTo_univ _ _)
  exact hcomp

private theorem mapCInf_zero_of_uniform_sampled_jets
    {U : Set E} (hU : IsOpen U) {J : Set ℝ}
    (f : ℕ → ℝ → E → F) (hf : ∀ n t, t ∈ J → ContDiffOn ℝ ∞ (f n t) U)
    (hunif : ∀ K : Set E, IsCompact K → K ⊆ U → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K, ‖iteratedFDeriv ℝ r (f n t) y‖ ≤ ε)
    (θ : ℕ → ℕ) (hθ : Tendsto θ atTop atTop) (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ J) :
    MapCInfConvergenceOnCompacts U (fun n => f (θ n) (τ n)) (fun _ => 0) := by
  intro K hK hKU m
  apply mapCPConvergenceOn_of_tendstoUniformlyOn hU hKU
    (fun n => (hf (θ n) (τ n) (hτ n)).of_le (by exact_mod_cast le_top)) contDiffOn_const
  intro r _hr
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hunif K hK hKU r (ε / 2) (by positivity)
  filter_upwards [hθ.eventually_ge_atTop N] with n hn
  intro y hy
  have hh := hN (θ n) hn (τ n) (hτ n) y hy
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, dist_eq_norm, zero_sub, norm_neg]
    using hh.trans_lt (by linarith : ε / 2 < ε)

end Calculus

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance perturbationNormC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem weighted_error_covariant_norm_tendsto_of_uniform_perturbation
    (g : ℝ → SmoothRiemannianMetric I M)
    (A B : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (A' : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2) (p : M)
    {V : Set E} (hV : IsOpen V) (hVt : V ⊆ (extChartAt I p).target)
    {J L : Set ℝ}
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartGramOnE (I := I) (g z.1) p i j z.2) (L ×ˢ V))
    (hA : ∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : ℝ × E => A z.1 ((extChartAt I p).symm z.2)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z.2))) (J ×ˢ V))
    (hB : ∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : ℝ × E => B z.1 ((extChartAt I p).symm z.2)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z.2))) (L ×ˢ V))
    (hunif : ∀ slots : Fin 2 → Fin (Module.finrank ℝ E),
      ∀ Q : Set E, IsCompact Q → Q ⊆ V → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ τ ∈ J, ∀ z ∈ Q,
        ‖iteratedFDeriv ℝ r (fun w => (A' n τ - A τ) ((extChartAt I p).symm w)
          (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm w))) z‖ ≤ ε)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (tau upsilon : ℕ → ℝ) (htau : ∀ n, tau n ∈ J) (hupsilon : ∀ n, upsilon n ∈ L)
    {t u : ℝ} (ht : t ∈ J) (hu : u ∈ L)
    (htlim : Tendsto tau atTop (𝓝 t)) (hulim : Tendsto upsilon atTop (𝓝 u))
    (c alpha beta : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    {c₀ alpha₀ beta₀ : ℝ} (hc₀ : 0 < c₀)
    (hclim : Tendsto c atTop (𝓝 c₀))
    (halim : Tendsto alpha atTop (𝓝 alpha₀)) (hblim : Tendsto beta atTop (𝓝 beta₀))
    {K : Set E} (hK : IsCompact K) (hKV : K ⊆ V)
    (z : ℕ → E) (hzK : ∀ n, z n ∈ K) {z₀ : E} (hz₀ : z₀ ∈ K)
    (hz : Tendsto z atTop (𝓝 z₀)) (a : ℕ) :
    Tendsto (fun n => tensor02CovDerivNormWith (I := I) a
      (alpha n • A' (m n) (tau n) - beta n • B (upsilon n))
      (scaleMetric (c n) (hc n) (g (upsilon n)))
      (scaleMetric (c n) (hc n) (g (upsilon n))) ((extChartAt I p).symm (z n)))
      atTop (𝓝 (tensor02CovDerivNormWith (I := I) a
        (alpha₀ • A t - beta₀ • B u)
        (scaleMetric c₀ hc₀ (g u)) (scaleMetric c₀ hc₀ (g u)) ((extChartAt I p).symm z₀))) := by
  apply tensor02_covariant_norm_tendsto_of_smooth_chart_convergence
    (fun n => scaleMetric (c n) (hc n) (g (upsilon n))) (scaleMetric c₀ hc₀ (g u))
    (fun n => alpha n • A' (m n) (tau n) - beta n • B (upsilon n))
    (alpha₀ • A t - beta₀ • B u) p hV hVt ?_ ?_ hK hKV z hzK hz₀ hz a
  · intro i j
    convert mapCInfConvergenceOnCompacts_smul_of_tendsto_parameter
      (G := fun s y => chartGramOnE (I := I) (g s) p i j y)
      hV (hgram i j) upsilon hupsilon hu hulim c hclim using 1
    · funext n y
      simp [chartGramOnE,
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, scaleMetric_inner]
    · funext y
      simp [chartGramOnE,
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, scaleMetric_inner]
  · intro slots
    let comp (X : Tensor0SField (I := I) (M := M) (n := ∞) 2) (y : E) : ℝ :=
      X ((extChartAt I p).symm y)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))
    have hcomp (X : Tensor0SField (I := I) (M := M) (n := ∞) 2) : ContDiffOn ℝ ∞ (comp X) V :=
      tensor_field_chart_components_contDiffOn X p hVt slots
    let f (s : ℝ) (y : E) := A s ((extChartAt I p).symm y)
      (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))
    let k (s : ℝ) (y : E) := B s ((extChartAt I p).symm y)
      (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))
    have hfc (s : ℝ) (hs : s ∈ J) : ContDiffOn ℝ ∞ (f s) V :=
      (hA slots).comp (f := fun y => (s, y)) (contDiffOn_const.prodMk contDiffOn_id)
        (fun _ hy => ⟨hs, hy⟩)
    have hkc (s : ℝ) (hs : s ∈ L) : ContDiffOn ℝ ∞ (k s) V :=
      (hB slots).comp (f := fun y => (s, y)) (contDiffOn_const.prodMk contDiffOn_id)
        (fun _ hy => ⟨hs, hy⟩)
    have hsub := mapCInfConvergence_prodMk hV
      (mapCInfConvergenceOnCompacts_smul_of_tendsto_parameter
        (G := f) hV (hA slots) tau htau ht htlim alpha halim)
      (mapCInfConvergenceOnCompacts_smul_of_tendsto_parameter
        (G := k) hV (hB slots) upsilon hupsilon hu hulim beta hblim)
      (fun n => contDiffOn_const.mul (hfc (tau n) (htau n)))
      (contDiffOn_const.mul (hfc t ht))
      (fun n => contDiffOn_const.mul (hkc (upsilon n) (hupsilon n)))
      (contDiffOn_const.mul (hkc u hu))
    have hsubc : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => z.1 - z.2) Set.univ :=
      contDiffOn_fst.sub contDiffOn_snd
    have hmain : MapCInfConvergenceOnCompacts V
        (fun n => comp (alpha n • A (tau n) - beta n • B (upsilon n)))
        (comp (alpha₀ • A t - beta₀ • B u)) := by
      have hh := MapCInfConvergenceOnCompacts.comp hV isOpen_univ hsub
        (mapCInfConvergence_const (U := (Set.univ : Set (ℝ × ℝ))) (fun z : ℝ × ℝ => z.1 - z.2))
        (fun n => (contDiffOn_const.mul (hfc (tau n) (htau n))).prodMk
          (contDiffOn_const.mul (hkc (upsilon n) (hupsilon n))))
        ((contDiffOn_const.mul (hfc t ht)).prodMk (contDiffOn_const.mul (hkc u hu)))
        (fun _ => hsubc) hsubc (mapsTo_univ _ _) (fun _ => mapsTo_univ _ _)
      simpa only [comp, f, k, ContMDiffSection.coe_sub, ContMDiffSection.coe_smul, Pi.sub_apply,
        Pi.smul_apply, Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply, smul_eq_mul] using hh
    have hdiff : MapCInfConvergenceOnCompacts V
        (fun n => comp (A' (m n) (tau n) - A (tau n))) (fun _ => 0) :=
      mapCInf_zero_of_uniform_sampled_jets hV (fun n s => comp (A' n s - A s))
        (fun n s _ => hcomp _) (fun Q hQ hQV r ε hε => hunif slots Q hQ hQV r ε hε)
        m hm tau htau
    have hweight : MapCInfConvergenceOnCompacts V (fun n (_ : E) => alpha n • (1 : ℝ))
        (fun _ => alpha₀ • (1 : ℝ)) :=
      mapCInfConvergenceOnCompacts_smul_of_tendsto_parameter
        (G := fun (_ : ℝ) (_ : E) => (1 : ℝ)) (A := Set.univ) hV contDiffOn_const
        (fun _ => (0 : ℝ)) (fun _ => mem_univ _) (mem_univ _) tendsto_const_nhds alpha halim
    have hprod := mapCInfConvergence_mul hV hweight hdiff (fun _ => contDiffOn_const)
      contDiffOn_const (fun n => hcomp _) contDiffOn_const
    have hsum := mapCInf_add_on_open hV hmain hprod (fun n => hcomp _) (hcomp _)
      (fun n => contDiffOn_const.mul (hcomp _)) (contDiffOn_const.mul contDiffOn_const)
    convert hsum using 1
    · funext n y
      simp only [comp, ContMDiffSection.coe_sub, ContMDiffSection.coe_smul, Pi.sub_apply,
        Pi.smul_apply, Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply, smul_eq_mul]
      ring
    · funext y
      simp only [comp, mul_zero, add_zero]

omit [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem exists_compact_chart_sequence_of_tendsto (p : M)
    {V : Set E} (hV : IsOpen V) (hpV : extChartAt I p p ∈ V)
    (y : ℕ → M) (hy : Tendsto y atTop (𝓝 p)) :
    ∃ (K : Set E) (z : ℕ → E), IsCompact K ∧ K ⊆ V ∧ extChartAt I p p ∈ K ∧
      (∀ n, z n ∈ K) ∧ Tendsto z atTop (𝓝 (extChartAt I p p)) ∧
      ∀ᶠ n in atTop, (extChartAt I p).symm (z n) = y n := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hpV)
  let K := Metric.closedBall (extChartAt I p p) (r / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKV : K ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hpK : extChartAt I p p ∈ K := Metric.mem_closedBall_self (by linarith)
  have hchart : Tendsto (fun n => extChartAt I p (y n)) atTop (𝓝 (extChartAt I p p)) :=
    (continuousAt_extChartAt (I := I) p).tendsto.comp hy
  have hnear : ∀ᶠ n in atTop, extChartAt I p (y n) ∈ K :=
    hchart (Metric.closedBall_mem_nhds _ (by linarith))
  let z (n : ℕ) := if extChartAt I p (y n) ∈ K then extChartAt I p (y n)
    else extChartAt I p p
  have hzK (n : ℕ) : z n ∈ K := by
    dsimp only [z]
    split_ifs with hn
    · exact hn
    · exact hpK
  have heq : z =ᶠ[atTop] (fun n => extChartAt I p (y n)) := by
    filter_upwards [hnear] with n hn
    exact ite_eq_left hn
  have hz := (tendsto_congr' heq).2 hchart
  refine ⟨K, z, hK, hKV, hpK, hzK, hz, ?_⟩
  filter_upwards [heq, hy (extChartAt_source_mem_nhds (I := I) p)] with n hn hsrc
  rw [hn, (extChartAt I p).left_inv hsrc]

theorem weighted_error_covariant_norm_tendsto_at_point_of_uniform_perturbation
    (g : ℝ → SmoothRiemannianMetric I M)
    (A B : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (A' : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2) (p : M)
    {V : Set E} (hV : IsOpen V) (hpV : extChartAt I p p ∈ V)
    (hVt : V ⊆ (extChartAt I p).target)
    {J L : Set ℝ}
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartGramOnE (I := I) (g z.1) p i j z.2) (L ×ˢ V))
    (hA : ∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : ℝ × E => A z.1 ((extChartAt I p).symm z.2)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z.2))) (J ×ˢ V))
    (hB : ∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : ℝ × E => B z.1 ((extChartAt I p).symm z.2)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z.2))) (L ×ˢ V))
    (hunif : ∀ slots : Fin 2 → Fin (Module.finrank ℝ E),
      ∀ Q : Set E, IsCompact Q → Q ⊆ V → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ τ ∈ J, ∀ z ∈ Q,
        ‖iteratedFDeriv ℝ r (fun w => (A' n τ - A τ) ((extChartAt I p).symm w)
          (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm w))) z‖ ≤ ε)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (tau upsilon : ℕ → ℝ) (htau : ∀ n, tau n ∈ J) (hupsilon : ∀ n, upsilon n ∈ L)
    {t u : ℝ} (ht : t ∈ J) (hu : u ∈ L)
    (htlim : Tendsto tau atTop (𝓝 t)) (hulim : Tendsto upsilon atTop (𝓝 u))
    (c alpha beta : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    {c₀ alpha₀ beta₀ : ℝ} (hc₀ : 0 < c₀)
    (hclim : Tendsto c atTop (𝓝 c₀))
    (halim : Tendsto alpha atTop (𝓝 alpha₀)) (hblim : Tendsto beta atTop (𝓝 beta₀))
    (y : ℕ → M) (hy : Tendsto y atTop (𝓝 p)) (a : ℕ) :
    Tendsto (fun n => tensor02CovDerivNormWith (I := I) a
      (alpha n • A' (m n) (tau n) - beta n • B (upsilon n))
      (scaleMetric (c n) (hc n) (g (upsilon n)))
      (scaleMetric (c n) (hc n) (g (upsilon n))) (y n))
      atTop (𝓝 (tensor02CovDerivNormWith (I := I) a
        (alpha₀ • A t - beta₀ • B u)
        (scaleMetric c₀ hc₀ (g u)) (scaleMetric c₀ hc₀ (g u)) p)) := by
  obtain ⟨K, z, hK, hKV, hpK, hzK, hz, heq⟩ :=
    exists_compact_chart_sequence_of_tendsto p hV hpV y hy
  have hn := weighted_error_covariant_norm_tendsto_of_uniform_perturbation g A B A' p hV hVt
    hgram hA hB hunif m hm tau upsilon htau hupsilon ht hu htlim hulim c alpha beta hc hc₀
    hclim halim hblim hK hKV z hzK hpK hz a
  rw [(extChartAt I p).left_inv (mem_extChartAt_source p)] at hn
  apply hn.congr'
  filter_upwards [heq] with n hn
  rw [hn]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M] in
private theorem closedBall_scaleMetric_eq_div_sqrt (g : SmoothRiemannianMetric I M)
    {c : ℝ} (hc : 0 < c) (p : M) (R : ℝ) :
    riemannianClosedBallOf (scaleMetric c hc g) p R =
      riemannianClosedBallOf g p (R / Real.sqrt c) := by
  have hh := riemannianClosedBallOf_scaleMetric c hc g p (R / Real.sqrt c)
  have hcancel : Real.sqrt c * (R / Real.sqrt c) = R := by
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hc)]
  rwa [hcancel] at hh

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [I.Boundaryless] in
private theorem mem_closedBall_scaleMetric_of_tendsto (g : SmoothRiemannianMetric I M)
    (center y : ℕ → M) {p y₀ : M}
    (hcenter : Tendsto center atTop (𝓝 p)) (hy : Tendsto y atTop (𝓝 y₀))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hclim : Tendsto c atTop (𝓝 c₀)) (R : ℝ)
    (hball : ∀ n, y n ∈ riemannianClosedBallOf (scaleMetric (c n) (hc n) g) (center n) R) :
    y₀ ∈ riemannianClosedBallOf (scaleMetric c₀ hc₀ g) p R := by
  have hbound (n : ℕ) : riemannianEDistOf g p (y n) ≤
      riemannianEDistOf g p (center n) + ENNReal.ofReal (R / Real.sqrt (c n)) := by
    have hh := hball n
    rw [closedBall_scaleMetric_eq_div_sqrt] at hh
    change riemannianEDistOf g (center n) (y n) ≤ ENNReal.ofReal (R / Real.sqrt (c n)) at hh
    let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    exact (Manifold.riemannianEDist_triangle (I := I) (x := p) (y := center n) (z := y n)).trans
      (add_le_add le_rfl hh)
  have hleft : Tendsto (fun n => riemannianEDistOf g p (y n)) atTop
      (𝓝 (riemannianEDistOf g p y₀)) := (continuous_riemannianEDist g p).tendsto y₀ |>.comp hy
  have hcenter' : Tendsto (fun n => riemannianEDistOf g p (center n)) atTop
      (𝓝 (riemannianEDistOf g p p)) :=
    (continuous_riemannianEDist g p).tendsto p |>.comp hcenter
  have hradius : Tendsto (fun n => ENNReal.ofReal (R / Real.sqrt (c n))) atTop
      (𝓝 (ENNReal.ofReal (R / Real.sqrt c₀))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.div hclim.sqrt (ne_of_gt (Real.sqrt_pos.mpr hc₀)))
  have hle := le_of_tendsto_of_tendsto hleft (hcenter'.add hradius)
    (Filter.Eventually.of_forall hbound)
  rw [riemannianEDistOf_self, zero_add] at hle
  rw [closedBall_scaleMetric_eq_div_sqrt]
  exact hle

variable [SigmaCompactSpace M] in
theorem eventually_strict_weighted_error_norm_on_scaled_ball_of_uniform_perturbation
    (g : ℝ → SmoothRiemannianMetric I M)
    (A B : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (A' : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (p : M) (R : ℝ) {K : Set M} (hK : IsCompact K)
    {J L : Set ℝ}
    (hregular : ∀ y ∈ K, ∃ V : Set E, IsOpen V ∧ extChartAt I y y ∈ V ∧
      V ⊆ (extChartAt I y).target ∧
      (∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
        (fun z : ℝ × E => chartGramOnE (I := I) (g z.1) y i j z.2) (L ×ˢ V)) ∧
      (∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
        (fun z : ℝ × E => A z.1 ((extChartAt I y).symm z.2)
          (fun j => chartBasisVecFiber (I := I) y (slots j) ((extChartAt I y).symm z.2)))
          (J ×ˢ V)) ∧
      (∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
        (fun z : ℝ × E => B z.1 ((extChartAt I y).symm z.2)
          (fun j => chartBasisVecFiber (I := I) y (slots j) ((extChartAt I y).symm z.2)))
          (L ×ˢ V)))
    (hperturb : ∀ y ∈ K, ∃ V : Set E, IsOpen V ∧ extChartAt I y y ∈ V ∧
      V ⊆ (extChartAt I y).target ∧ ∀ slots : Fin 2 → Fin (Module.finrank ℝ E),
      ∀ Q : Set E, IsCompact Q → Q ⊆ V → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ τ ∈ J, ∀ z ∈ Q,
        ‖iteratedFDeriv ℝ r (fun w => (A' n τ - A τ) ((extChartAt I y).symm w)
          (fun j => chartBasisVecFiber (I := I) y (slots j) ((extChartAt I y).symm w))) z‖ ≤ ε)
    (center : ℕ → M) (hcenter : Tendsto center atTop (𝓝 p))
    (t Q c alpha beta : ℕ → ℝ) {t₀ Q₀ c₀ alpha₀ beta₀ : ℝ}
    (hQ₀ : 0 < Q₀) (hc : ∀ n, 0 < c n) (hc₀ : 0 < c₀)
    (htlim : Tendsto t atTop (𝓝 t₀)) (hQlim : Tendsto Q atTop (𝓝 Q₀))
    (hclim : Tendsto c atTop (𝓝 c₀)) (halim : Tendsto alpha atTop (𝓝 alpha₀))
    (hblim : Tendsto beta atTop (𝓝 beta₀))
    {lo hi eps : ℝ} (order : ℕ)
    (hcontain : ∀ n, riemannianClosedBallOf (scaleMetric (c n) (hc n) (g 0)) (center n) R ⊆ K)
    (hsource : ∀ n s, s ∈ Icc lo hi → t n + s / Q n ∈ J)
    (hmodel : ∀ n s, s ∈ Icc lo hi → s / c n ∈ L)
    (hsource₀ : ∀ s ∈ Icc lo hi, t₀ + s / Q₀ ∈ J)
    (hmodel₀ : ∀ s ∈ Icc lo hi, s / c₀ ∈ L)
    (hstrict : ∀ s ∈ Icc lo hi,
      ∀ y ∈ riemannianClosedBallOf (scaleMetric c₀ hc₀ (g 0)) p R,
        tensor02CovDerivNormWith (I := I) order
          (alpha₀ • A (t₀ + s / Q₀) - beta₀ • B (s / c₀))
          (scaleMetric c₀ hc₀ (g (s / c₀))) (scaleMetric c₀ hc₀ (g (s / c₀))) y < eps) :
    ∀ᶠ n in atTop, ∀ s ∈ Icc lo hi,
      ∀ y ∈ riemannianClosedBallOf (scaleMetric (c n) (hc n) (g 0)) (center n) R,
        tensor02CovDerivNormWith (I := I) order
          (alpha n • A' n (t n + s / Q n) - beta n • B (s / c n))
          (scaleMetric (c n) (hc n) (g (s / c n)))
          (scaleMetric (c n) (hc n) (g (s / c n))) y < eps := by
  classical
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let f (n : ℕ) (s : ℝ) (y : M) := tensor02CovDerivNormWith (I := I) order
    (alpha n • A' n (t n + s / Q n) - beta n • B (s / c n))
    (scaleMetric (c n) (hc n) (g (s / c n))) (scaleMetric (c n) (hc n) (g (s / c n))) y
  change ∀ᶠ n in atTop, ∀ s ∈ Icc lo hi,
    ∀ y ∈ riemannianClosedBallOf (scaleMetric (c n) (hc n) (g 0)) (center n) R, f n s y < eps
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, ¬ (∀ s ∈ Icc lo hi,
      ∀ y ∈ riemannianClosedBallOf (scaleMetric (c n) (hc n) (g 0)) (center n) R,
        f n s y < eps) := by
    simpa only [Filter.Frequently, not_not] using hnot
  obtain ⟨ns, hns, hbad⟩ := Filter.exists_seq_forall_of_frequently hfreq
  have hbad' (n : ℕ) : ∃ s ∈ Icc lo hi,
      ∃ y ∈ riemannianClosedBallOf (scaleMetric (c (ns n)) (hc (ns n)) (g 0)) (center (ns n)) R,
        eps ≤ f (ns n) s y := by
    have hh := hbad n
    push Not at hh
    exact hh
  choose s hs y hy hbadnorm using hbad'
  obtain ⟨w, hw, phi, hphi, hwlim⟩ := (isCompact_Icc.prod hK).tendsto_subseq
    (x := fun n => (s n, y n)) (fun n => ⟨hs n, hcontain (ns n) (hy n)⟩)
  let pick := ns ∘ phi
  have hpick : Tendsto pick atTop atTop := hns.comp hphi.tendsto_atTop
  have hslim : Tendsto (fun n => s (phi n)) atTop (𝓝 w.1) :=
    (continuous_fst.tendsto w).comp hwlim
  have hylim : Tendsto (fun n => y (phi n)) atTop (𝓝 w.2) :=
    (continuous_snd.tendsto w).comp hwlim
  have hwball := mem_closedBall_scaleMetric_of_tendsto (g 0) (fun n => center (pick n))
    (fun n => y (phi n)) (hcenter.comp hpick) hylim (fun n => c (pick n))
    (fun n => hc (pick n)) hc₀ (hclim.comp hpick) R (fun n => hy (phi n))
  obtain ⟨V, hV, hwV, hVt, hgram, hA, hB⟩ := hregular w.2 hw.2
  obtain ⟨V', hV', hwV', _hV't, hunif⟩ := hperturb w.2 hw.2
  have hsourcelim : Tendsto (fun n => t (pick n) + s (phi n) / Q (pick n)) atTop
      (𝓝 (t₀ + w.1 / Q₀)) := (htlim.comp hpick).add (hslim.div (hQlim.comp hpick) hQ₀.ne')
  have hmodellim : Tendsto (fun n => s (phi n) / c (pick n)) atTop (𝓝 (w.1 / c₀)) :=
    hslim.div (hclim.comp hpick) hc₀.ne'
  have hnorm := weighted_error_covariant_norm_tendsto_at_point_of_uniform_perturbation
    g A B A' w.2 (hV.inter hV') ⟨hwV, hwV'⟩ (inter_subset_left.trans hVt)
    (fun i j => (hgram i j).mono (prod_mono Subset.rfl inter_subset_left))
    (fun slots => (hA slots).mono (prod_mono Subset.rfl inter_subset_left))
    (fun slots => (hB slots).mono (prod_mono Subset.rfl inter_subset_left))
    (fun slots Q' hQ' hQ'V r ε hε =>
      hunif slots Q' hQ' (hQ'V.trans inter_subset_right) r ε hε)
    pick hpick (fun n => t (pick n) + s (phi n) / Q (pick n))
    (fun n => s (phi n) / c (pick n))
    (fun n => hsource (pick n) (s (phi n)) (hs (phi n)))
    (fun n => hmodel (pick n) (s (phi n)) (hs (phi n)))
    (hsource₀ w.1 hw.1) (hmodel₀ w.1 hw.1) hsourcelim hmodellim
    (fun n => c (pick n)) (fun n => alpha (pick n)) (fun n => beta (pick n))
    (fun n => hc (pick n)) hc₀ (hclim.comp hpick) (halim.comp hpick) (hblim.comp hpick)
    (fun n => y (phi n)) hylim order
  have hge := ge_of_tendsto hnorm (Filter.Eventually.of_forall (fun n => hbadnorm (phi n)))
  exact (not_le_of_gt (hstrict w.1 hw.1 w.2 hwball)) hge

end Generic

section Pullback

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u v

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N]

private local instance pullbackAmbientC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance pullbackModelC1 : IsManifold I3 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem pullback_tower_chart_eq {D : RealTimeInterval}
    (X : SolutionOn (I := I3) (M := M) D) (hX : IsSolutionOn X)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (Phi : PartialDiffeomorph I3 I3 N M ∞) (U : TopologicalSpace.Opens N)
    [SigmaCompactSpace U] (hU : (U : Set N) ⊆ Phi.source)
    [SigmaCompactSpace (⟨Phi '' (U : Set N), image_opens_isOpen Phi hU⟩ :
      TopologicalSpace.Opens M)]
    (A : ℕ → ℝ → Tensor0SField (I := I3) (M := N) (n := ∞) 2)
    (hzero : ∀ t, ∀ x ∈ U, ∀ v : Fin 2 → TangentSpace I3 x,
      A 0 t x v = (X.base.metric t).inner (Phi x)
        (mfderiv I3 I3 Phi x (v 0)) (mfderiv I3 I3 Phi x (v 1)))
    (hA : ∀ q t, t ∈ Icc c b → ∀ x ∈ U,
      HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) (Icc c b) t)
    (p : U) (q : ℕ) (slots : Fin 2 → Fin (Module.finrank ℝ ThreeSpace))
    {τ : ℝ} (hτ : τ ∈ Icc c b) {z : ThreeSpace} (hz : z ∈ (extChartAt I3 p).target) :
    (iteratedDerivWithin q (fun s => metricTensorField
      ((solutionOnPullback (solutionOnRestrictOpen
        (X.timeRestrict (RealTimeInterval.closed a b (hac.trans hcb).le))
        ⟨Phi '' (U : Set N), image_opens_isOpen Phi hU⟩)
        (DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Phi hU)).base.metric s)
        ((extChartAt I3 p).symm z)) (Icc c b) τ)
        (fun j => chartBasisVecFiber (I := I3) p (slots j) ((extChartAt I3 p).symm z)) =
      A q τ ((extChartAt I3 (p : N)).symm z)
        (fun j => chartBasisVecFiber (I := I3) (p : N) (slots j)
          ((extChartAt I3 (p : N)).symm z)) := by
  let D' := RealTimeInterval.closed a b (hac.trans hcb).le
  let W : TopologicalSpace.Opens M := ⟨Phi '' (U : Set N), image_opens_isOpen Phi hU⟩
  let e := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Phi hU
  let T := solutionOnPullback (solutionOnRestrictOpen (X.timeRestrict D') W) e
  have hT : IsSolutionOn T := isSolutionOn_pullback _ (isSolutionOn_restrictOpen _
    (isSolutionOn_timeRestrict hX hslab hreg) W) e
  obtain ⟨C, hC0, hC⟩ := exists_closedWindow_metric_time_fields T hT hac hcb
    (fun _ hs => hs) (fun _ hs => hs)
  let x : U := (extChartAt I3 p).symm z
  have hxchart : (x : N) ∈ (chartAt ThreeSpace (p : N)).source := by
    have hxlocal := (extChartAt I3 p).map_target hz
    rw [extChartAt_source_eq_chartAt_source, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source] at hxlocal
    exact hxlocal
  have hxcoe : (x : N) = (extChartAt I3 (p : N)).symm z :=
    extChartAt_opens_symm_coe U p hz
  let vU : Fin 2 → TangentSpace I3 x := fun j => chartBasisVecFiber (I := I3) p (slots j) x
  let v : Fin 2 → TangentSpace I3 (x : N) :=
    fun j => chartBasisVecFiber (I := I3) (p : N) (slots j) (x : N)
  have hvv : ∀ j, vU j = v j := fun j =>
    chartBasisVecFiber_restrictOpen U p x hxchart (slots j)
  rw [← (hC q τ hτ x).1]
  rw [← hxcoe]
  have heq := scalar_time_towers_eq (uniqueDiffOn_Icc hcb)
    (fun k s => C k s x vU) (fun k s => A k s (x : N) v)
    (fun k s hs => (tensor0SEvalCLM (I := I3) (M := U) (x := x) vU).hasFDerivAt
      |>.comp_hasDerivWithinAt s (hC k s hs x).2)
    (fun k s hs => (tensor0SEvalCLM (I := I3) (M := N) (x := (x : N)) v).hasFDerivAt
      |>.comp_hasDerivWithinAt s (hA k s hs x x.property))
    (fun s _ => by
      rw [hC0 s, metricTensorField_apply, hzero s x x.property v]
      change (Diffeomorph.pullbackMetric ((X.base.metric s).restrictOpen W) e).inner x
        (vU 0) (vU 1) = _
      rw [Diffeomorph.pullbackMetric_inner, SmoothRiemannianMetric.restrictOpen_inner]
      rw [DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU x (vU 0),
        DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU x (vU 1),
        hvv 0, hvv 1]
      rfl) q τ hτ
  exact heq

theorem uniform_pullback_time_tower_chart_jets_of_metric_convergence {D : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I3) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I3) (M := M) D) (hS₀ : IsSolutionOn S₀)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (Phi : PartialDiffeomorph I3 I3 N M ∞) (U : TopologicalSpace.Opens N)
    (hU : (U : Set N) ⊆ Phi.source)
    (A : ℕ → ℝ → Tensor0SField (I := I3) (M := N) (n := ∞) 2)
    (A' : ℕ → ℕ → ℝ → Tensor0SField (I := I3) (M := N) (n := ∞) 2)
    (hzero : ∀ t, ∀ x ∈ U, ∀ v : Fin 2 → TangentSpace I3 x,
      A 0 t x v = (S₀.base.metric t).inner (Phi x)
        (mfderiv I3 I3 Phi x (v 0)) (mfderiv I3 I3 Phi x (v 1)))
    (hA : ∀ q t, t ∈ Icc c b → ∀ x ∈ U,
      HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) (Icc c b) t)
    (hzero' : ∀ n t, ∀ x ∈ U, ∀ v : Fin 2 → TangentSpace I3 x,
      A' n 0 t x v = ((S n).base.metric t).inner (Phi x)
        (mfderiv I3 I3 Phi x (v 0)) (mfderiv I3 I3 Phi x (v 1)))
    (hA' : ∀ n q t, t ∈ Icc c b → ∀ x ∈ U,
      HasDerivWithinAt (fun s => A' n q s x) (A' n (q + 1) t x) (Icc c b) t)
    (R : SmoothRiemannianMetric I3 M)
    (hconv : ∀ K : Set M, IsCompact K → ∀ r : ℕ, ∀ e : ℝ, 0 < e →
      ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ τ ∈ Icc c b,
        metricDerivNormSupOn K r ((S n).base.metric τ) (S₀.base.metric τ) R < e)
    (y : N) (hy : y ∈ U) (q : ℕ) :
    ∃ V : Set ThreeSpace, IsOpen V ∧ extChartAt I3 y y ∈ V ∧
      V ⊆ (extChartAt I3 y).target ∧ ∀ slots : Fin 2 → Fin (Module.finrank ℝ ThreeSpace),
      ∀ Q : Set ThreeSpace, IsCompact Q → Q ⊆ V → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ τ ∈ Icc c b, ∀ z ∈ Q,
        ‖iteratedFDeriv ℝ r (fun w => (A' n q τ - A q τ) ((extChartAt I3 y).symm w)
          (fun j => chartBasisVecFiber (I := I3) y (slots j) ((extChartAt I3 y).symm w))) z‖
          ≤ ε := by
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  let D' := RealTimeInterval.closed a b (hac.trans hcb).le
  let W : TopologicalSpace.Opens M := ⟨Phi '' (U : Set N), image_opens_isOpen Phi hU⟩
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 W.isOpen)
  let e := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Phi hU
  let T (X : SolutionOn (I := I3) (M := M) D) :=
    solutionOnPullback (solutionOnRestrictOpen (X.timeRestrict D') W) e
  have hT (X : SolutionOn (I := I3) (M := M) D) (hX : IsSolutionOn X) : IsSolutionOn (T X) :=
    isSolutionOn_pullback _ (isSolutionOn_restrictOpen _
      (isSolutionOn_timeRestrict hX hslab hreg) W) e
  let RU := Diffeomorph.pullbackMetric (R.restrictOpen W) e
  have hconvU : ∀ K : Set U, IsCompact K → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ τ ∈ Icc c b,
        metricDerivNormSupOn K r ((T (S n)).base.metric τ) ((T S₀).base.metric τ) RU < ε := by
    intro K hK r ε hε
    obtain ⟨N₀, hN₀⟩ := hconv (Subtype.val '' (e '' K))
      ((hK.image e.continuous).image continuous_subtype_val) r ε hε
    refine ⟨N₀, fun n hn τ hτ => ?_⟩
    change metricDerivNormSupOn K r
      (Diffeomorph.pullbackMetric (((S n).base.metric τ).restrictOpen W) e)
      (Diffeomorph.pullbackMetric ((S₀.base.metric τ).restrictOpen W) e) RU < ε
    rw [metricDerivNormSupOn_pullback_image, metricDerivNormSupOn_restrictOpen]
    exact hN₀ n hn τ hτ
  let p : U := ⟨y, hy⟩
  have hpy : extChartAt I3 y y = extChartAt I3 p p := rfl
  refine ⟨(extChartAt I3 p).target, isOpen_extChartAt_target p, ?_,
    extChartAt_opens_target_subset U p, ?_⟩
  · rw [hpy]
    exact mem_extChartAt_target p
  intro slots Q hQ hQV r ε hε
  obtain ⟨N₀, hN₀⟩ := uniform_ordinary_metric_jets_of_metric_convergence_on_closed_interval
    (fun n => T (S n)) (fun n => hT (S n) (hS n)) (T S₀) (hT S₀ hS₀) hac hcb rfl
    (fun _ hs => hs) isCompact_Icc Subset.rfl p (isOpen_extChartAt_target p) Subset.rfl RU
    hconvU hQ hQV r q slots ε hε
  refine ⟨N₀, fun n hn τ hτ w hw => ?_⟩
  have hwV : w ∈ (extChartAt I3 p).target := hQV hw
  have hwN : w ∈ (extChartAt I3 y).target := extChartAt_opens_target_subset U p hwV
  let F (B : Tensor0SField (I := I3) (M := N) (n := ∞) 2) (w' : ThreeSpace) : ℝ :=
    B ((extChartAt I3 y).symm w')
      (fun j => chartBasisVecFiber (I := I3) y (slots j) ((extChartAt I3 y).symm w'))
  have hFc (B : Tensor0SField (I := I3) (M := N) (n := ∞) 2) :
      ContDiffAt ℝ r (F B) w :=
    ((tensor_field_chart_components_contDiffOn B y Subset.rfl slots).contDiffAt
      ((isOpen_extChartAt_target y).mem_nhds hwN)).of_le (by exact_mod_cast le_top)
  have hsplit : (fun w' => (A' n q τ - A q τ) ((extChartAt I3 y).symm w')
      (fun j => chartBasisVecFiber (I := I3) y (slots j) ((extChartAt I3 y).symm w'))) =
      F (A' n q τ) - F (A q τ) := by
    funext w'
    simp only [F, ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply]
  have hlocal (X : SolutionOn (I := I3) (M := M) D) (hX : IsSolutionOn X)
      (B : ℕ → ℝ → Tensor0SField (I := I3) (M := N) (n := ∞) 2)
      (hB0 : ∀ t, ∀ x ∈ U, ∀ v : Fin 2 → TangentSpace I3 x,
        B 0 t x v = (X.base.metric t).inner (Phi x)
          (mfderiv I3 I3 Phi x (v 0)) (mfderiv I3 I3 Phi x (v 1)))
      (hB : ∀ q t, t ∈ Icc c b → ∀ x ∈ U,
        HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (Icc c b) t) :
      iteratedFDeriv ℝ r (F (B q τ)) w = iteratedFDeriv ℝ r (fun w' =>
        (iteratedDerivWithin q (fun s => metricTensorField ((T X).base.metric s)
          ((extChartAt I3 p).symm w')) (Icc c b) τ)
          (fun j => chartBasisVecFiber (I := I3) p (slots j) ((extChartAt I3 p).symm w'))) w := by
    have hev : F (B q τ) =ᶠ[𝓝 w] fun w' =>
        (iteratedDerivWithin q (fun s => metricTensorField ((T X).base.metric s)
          ((extChartAt I3 p).symm w')) (Icc c b) τ)
          (fun j => chartBasisVecFiber (I := I3) p (slots j) ((extChartAt I3 p).symm w')) := by
      filter_upwards [(isOpen_extChartAt_target p).mem_nhds hwV] with w' hw'
      exact (pullback_tower_chart_eq X hX hac hcb hslab hreg Phi U hU B hB0 hB p q slots hτ
        hw').symm
    exact (hev.iteratedFDeriv ℝ r).eq_of_nhds
  rw [hsplit, iteratedFDeriv_sub_apply (hFc _) (hFc _),
    hlocal (S n) (hS n) (A' n) (hzero' n) (hA' n), hlocal S₀ hS₀ A hzero hA]
  exact hN₀ n hn τ hτ w hw

end Pullback

section Recenter

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance recenterFlowC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem WindowedModelWitness.exists_recentered_strict_of_flow_time_towers
    {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S x t)
    (S' : SolutionOn (I := I3) (M := M) D) (z : W.model.M) (t' : ℝ)
    (hc : 0 < W.model.S.scalar 0 z) (hQ : 0 < S'.scalar t' (W.embedding z))
    (ht' : t' ∈ D.carrier)
    (hwindow : Icc (t' - (eps * S'.scalar t' (W.embedding z))⁻¹) t' ⊆ D.carrier)
    (U : Set W.model.M) (hU : U ⊆ W.embedding.source)
    (hbuffer : riemannianClosedBallOf
      (scaleMetric (W.model.S.scalar 0 z) hc (W.model.S.base.metric 0)) z
      (modelRadius eps + 1) ⊆ W.embedding.source)
    (hcompare : riemannianClosedBallOf
      (scaleMetric (W.model.S.scalar 0 z) hc (W.model.S.base.metric 0)) z
      (modelRadius eps) ⊆ U)
    (A B : ℕ → ℝ → Tensor0SField (I := I3) (M := W.model.M) (n := ∞) 2)
    (hA₀ : ∀ s, ∀ y ∈ U, ∀ v : Fin 2 → TangentSpace I3 y,
      A 0 s y v = (S'.base.metric s).inner (W.embedding y)
        (mfderiv I3 I3 W.embedding y (v 0)) (mfderiv I3 I3 W.embedding y (v 1)))
    (hB₀ : ∀ s, B 0 s = metricTensorField (W.model.S.base.metric s))
    (J L : Set ℝ)
    (hA : ∀ q s, s ∈ J → ∀ y,
      HasDerivWithinAt (fun r => A q r y) (A (q + 1) s y) J s)
    (hB : ∀ q s, s ∈ L → ∀ y,
      HasDerivWithinAt (fun r => B q r y) (B (q + 1) s y) L s)
    (hsourceMap : MapsTo (parabolicTime t' (S'.scalar t' (W.embedding z)))
      (Icc (-modelDepth eps) 0) J)
    (hmodelMap : MapsTo (parabolicTime 0 (W.model.S.scalar 0 z)) (Icc (-modelDepth eps) 0) L)
    (hstrict : ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
      ∀ y ∈ riemannianClosedBallOf
        (scaleMetric (W.model.S.scalar 0 z) hc (W.model.S.base.metric 0)) z (modelRadius eps),
        tensor02CovDerivNormWith (I := I3) a
          (rescaledTensorTimeTower A t' (S'.scalar t' (W.embedding z)) b s -
            rescaledTensorTimeTower B 0 (W.model.S.scalar 0 z) b s)
          (rescaledMetric W.model.S 0 (W.model.S.scalar 0 z) hc s)
          (rescaledMetric W.model.S 0 (W.model.S.scalar 0 z) hc s) y < eps) :
    ∃ W' : WindowedModelWitness eps kappa S' (W.embedding z) t',
      (∀ (o : TangentOrientationSection M) (oN : TangentOrientationSection W.model.M),
        (∀ y ∈ W.embedding.source, ∃ hf : Function.Bijective (mfderiv I3 I3 W.embedding y),
          PreservesTangentOrientationAt oN o W.embedding y hf) →
        ∃ oN' : TangentOrientationSection W'.model.M, ∀ y ∈ W'.embedding.source,
          ∃ hf : Function.Bijective (mfderiv I3 I3 W'.embedding y),
            PreservesTangentOrientationAt oN' o W'.embedding y hf) ∧
      ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
        ∀ y ∈ riemannianClosedBallOf (W'.model.S.base.metric 0) W'.model.basepoint
            (modelRadius eps),
          tensor02CovDerivNormWith (I := I3) a (W'.comparison.jet b s)
            (W'.model.S.base.metric s) (W'.model.S.base.metric s) y < eps := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let P := curvatureNormalizedFlow W.model W.model_ancient.carrier_eq
    W.model_ancient.regular_eq 0 (W.model.S.scalar 0 z) hc
    (by change (0 : ℝ) ≤ 0; exact le_rfl) z
  have hP : IsAncientKappaSolution kappa P :=
    isAncientKappaSolution_curvatureNormalizedFlow W.model W.model_ancient
      0 _ hc (by change (0 : ℝ) ≤ 0; exact le_rfl) z rfl
  have hPbase : PointedFlowScalarAtBase P 1 :=
    curvatureNormalizedFlow_scalar_base W.model W.model_ancient.carrier_eq
      W.model_ancient.regular_eq 0 _ hc (by change (0 : ℝ) ≤ 0; exact le_rfl) z rfl
  let h := rescaledMetric W.model.S 0 (W.model.S.scalar 0 z) hc
  let g := rescaledMetric S' t' (S'.scalar t' (W.embedding z)) hQ
  let A' := rescaledTensorTimeTower A t' (S'.scalar t' (W.embedding z))
  let B' := rescaledTensorTimeTower B 0 (W.model.S.scalar 0 z)
  let V := riemannianClosedBallOf (h 0) z (modelRadius eps)
  have hVU : V ⊆ U := by
    simpa only [V, h, rescaledMetric, parabolicTime_zero] using hcompare
  have hbuff : riemannianClosedBallOf (h 0) z (modelRadius eps + 1) ⊆ W.embedding.source := by
    simpa only [h, rescaledMetric, parabolicTime_zero] using hbuffer
  have hA'₀ (s : ℝ) (y : W.model.M) (hy : y ∈ V) (v : Fin 2 → TangentSpace I3 y) :
      A' 0 s y v = (g s).inner (W.embedding y)
        (mfderiv I3 I3 W.embedding y (v 0)) (mfderiv I3 I3 W.embedding y (v 1)) := by
    simp only [A', rescaledTensorTimeTower, pow_zero, mul_one, ContMDiffSection.coe_smul,
      Pi.smul_apply, Tensor0SSpace.smul_apply, smul_eq_mul, hA₀ _ y (hVU hy) v,
      g, rescaledMetric, scaleMetric_inner]
  have hB'₀ (s : ℝ) (y : W.model.M) (v : Fin 2 → TangentSpace I3 y) :
      B' 0 s y v = (h s).inner y (v 0) (v 1) := by
    simp only [B', rescaledTensorTimeTower, pow_zero, mul_one, ContMDiffSection.coe_smul,
      Pi.smul_apply, Tensor0SSpace.smul_apply, smul_eq_mul, hB₀, metricTensorField_apply,
      h, rescaledMetric, scaleMetric_inner]
  have hA' (q : ℕ) (s : ℝ) (hs : s ∈ Icc (-modelDepth eps) 0) (y : W.model.M) :
      HasDerivWithinAt (fun r => A' q r y) (A' (q + 1) s y) (Icc (-modelDepth eps) 0) s :=
    hasDerivWithinAt_rescaledTensorTimeTower A t' _ hsourceMap hA q s hs y
  have hB' (q : ℕ) (s : ℝ) (hs : s ∈ Icc (-modelDepth eps) 0) (y : W.model.M) :
      HasDerivWithinAt (fun r => B' q r y) (B' (q + 1) s y) (Icc (-modelDepth eps) 0) s :=
    hasDerivWithinAt_rescaledTensorTimeTower B 0 _ hmodelMap hB q s hs y
  have hbound (a b : ℕ) (hab : a + 2 * b ≤ modelOrder eps)
      (s : ℝ) (hs : s ∈ Icc (-modelDepth eps) 0) (y : W.model.M) (hy : y ∈ V) :
      tensor02CovDerivNormWith a (A' b s - B' b s) (h s) (h s) y ≤ eps := by
    have hy' : y ∈ riemannianClosedBallOf
        (scaleMetric (W.model.S.scalar 0 z) hc (W.model.S.base.metric 0)) z (modelRadius eps) := by
      simpa only [V, h, rescaledMetric, parabolicTime_zero] using hy
    exact (hstrict a b hab s hs y hy').le
  let C := metricComparisonOnOfGenuineTimeTowers h g W.embedding V (Icc (-modelDepth eps) 0)
    (uniqueDiffOn_Icc (neg_lt_zero.mpr (inv_pos.mpr W.eps_pos))) (modelOrder eps) eps
    A' B' hA'₀ hB'₀ (fun q s hs y _hy => hA' q s hs y)
    (fun q s hs y _hy => hB' q s hs y) hbound
  have hcomplete : RiemannianMetricComplete (I := I3) (h 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (P.atTime 0) (hP.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  have htime : (0 : ℝ) ∈ Icc (-modelDepth eps) 0 :=
    ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩
  obtain ⟨eta, heta, hcapture⟩ := MetricComparisonOn.exists_source_capture_reserve h g
    W.embedding z htime W.eps_pos W.eps_lt_one C
    (RiemannianMetricComplete.closedEBall_isCompact hcomplete z (modelRadius eps)) (hVU.trans hU)
  let W' : WindowedModelWitness eps kappa S' (W.embedding z) t' := {
    eps_pos := W.eps_pos
    eps_lt_one := W.eps_lt_one
    time_mem := ht'
    scalar_pos := hQ
    window_mem := hwindow
    model := P
    model_ancient := hP
    model_scalar_base := hPbase
    embedding := W.embedding
    buffered_ball := hbuff
    base_map := rfl
    comparison := C
    source_capture := by
      intro q hq
      have hq' : q ∈ riemannianClosedBallOf (g 0) (W.embedding z)
          (modelRadius eps - 1 + eta) := by
        change riemannianEDistOf (g 0) (W.embedding z) q ≤
          ENNReal.ofReal (modelRadius eps - 1 + eta)
        exact (le_of_lt hq).trans (ENNReal.ofReal_le_ofReal (by linarith))
      obtain ⟨y, hy, hyq⟩ := hcapture hq'
      exact ⟨y, hU (hVU hy), hyq⟩ }
  refine ⟨W', fun o oN hO => ⟨oN, hO⟩, ?_⟩
  intro a b hab s hs y hy
  change y ∈ V at hy
  have hy' : y ∈ riemannianClosedBallOf
      (scaleMetric (W.model.S.scalar 0 z) hc (W.model.S.base.metric 0)) z (modelRadius eps) := by
    simpa only [V, h, rescaledMetric, parabolicTime_zero] using hy
  exact hstrict a b hab s hs y hy'

end Recenter

section Perturbation

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

private local instance perturbationFlowC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem WindowedModelWitness.eventually_strict_of_tendsto_flows
    {S₀ : SolutionOn (I := I3) (M := M) D} (hS₀ : IsSolutionOn S₀)
    {S : ℕ → SolutionOn (I := I3) (M := M) D} (hS : ∀ n, IsSolutionOn (S n))
    {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S₀ x t)
    (hwindow : Icc (t - (eps * S₀.scalar t x)⁻¹) t ⊆ D.regular)
    (hstrict : ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
      ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps),
        tensor02CovDerivNormWith a (W.comparison.jet b s)
          (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps)
    (R : SmoothRiemannianMetric I3 M)
    (hconv : ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop,
      ∀ τ ∈ D.carrier, metricDerivNormSupOn K p ((S n).base.metric τ) (S₀.base.metric τ) R < e)
    {x' : ℕ → M} (hx' : Tendsto x' atTop (𝓝 x))
    (hscalar : Tendsto (fun n => (S n).scalar t (x' n)) atTop (𝓝 (S₀.scalar t x))) :
    ∀ᶠ n in atTop, Icc (t - (eps * (S n).scalar t (x' n))⁻¹) t ⊆ D.regular ∧
      ∃ W' : WindowedModelWitness eps kappa (S n) (x' n) t,
        (∀ (o : TangentOrientationSection M) (oN : TangentOrientationSection W.model.M),
          (∀ y ∈ W.embedding.source, ∃ hf : Function.Bijective (mfderiv I3 I3 W.embedding y),
            PreservesTangentOrientationAt oN o W.embedding y hf) →
          ∃ oN' : TangentOrientationSection W'.model.M, ∀ y ∈ W'.embedding.source,
            ∃ hf : Function.Bijective (mfderiv I3 I3 W'.embedding y),
              PreservesTangentOrientationAt oN' o W'.embedding y hf) ∧
        ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
          ∀ y ∈ riemannianClosedBallOf (W'.model.S.base.metric 0) W'.model.basepoint
              (modelRadius eps),
            tensor02CovDerivNormWith a (W'.comparison.jet b s)
              (W'.model.S.base.metric s) (W'.model.S.base.metric s) y < eps := by
  classical
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I3 M
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨a, c, b, hac, hclo, htb, hslab, hreg⟩ := W.exists_common_source_slab hwindow
  have hback : t - (eps * S₀.scalar t x)⁻¹ < t :=
    sub_lt_self _ (inv_pos.mpr (mul_pos W.eps_pos W.scalar_pos))
  have hcb : c < b := (hclo.trans hback).trans htb
  have hdepth : 0 < modelDepth eps := inv_pos.mpr W.eps_pos
  have hR : 0 < modelRadius eps := inv_pos.mpr (Real.sqrt_pos.mpr W.eps_pos)
  let L := Icc (-2 * modelDepth eps - 1) 0
  let K := riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
    (modelRadius eps + 1)
  have hcomplete : RiemannianMetricComplete (I := I3) (W.model.S.base.metric 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  have hK : IsCompact K := RiemannianMetricComplete.closedEBall_isCompact hcomplete _ _
  obtain ⟨chi, hchi, _hcompact, hchiOne, hsupp, _hrange⟩ :=
    DifferentialGeometry.Analysis.exists_mfd_bump (I := I3) hK W.embedding.open_source
      W.buffered_ball
  obtain ⟨V, hV, hKV, hVone⟩ := mem_nhdsSet_iff_exists.mp hchiOne
  let U : TopologicalSpace.Opens W.model.M :=
    ⟨V ∩ W.embedding.source, hV.inter W.embedding.open_source⟩
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  have hKU : K ⊆ U := fun y hy => ⟨hKV hy, W.buffered_ball hy⟩
  have hU : (U : Set W.model.M) ⊆ W.embedding.source := fun _ hy => hy.2
  have hOne (y : W.model.M) (hy : y ∈ U) : chi y = 1 := hVone hy.1
  obtain ⟨A, hA₀', _hAout, hA⟩ := exists_closedWindow_pullback_metric_time_tower S₀ hS₀
    hac hcb hslab hreg W.embedding chi hchi hsupp
  choose A' hA'₀' _hA'out hA' using fun n => exists_closedWindow_pullback_metric_time_tower
    (S n) (hS n) hac hcb hslab hreg W.embedding chi hchi hsupp
  have hA₀ (s : ℝ) (y : W.model.M) (hy : y ∈ U) (v : Fin 2 → TangentSpace I3 y) :
      A 0 s y v = (S₀.base.metric s).inner (W.embedding y)
        (mfderiv I3 I3 W.embedding y (v 0)) (mfderiv I3 I3 W.embedding y (v 1)) := by
    simpa only [hOne y hy, one_mul] using hA₀' s y (hU hy) v
  have hA'₀ (n : ℕ) (s : ℝ) (y : W.model.M) (hy : y ∈ U) (v : Fin 2 → TangentSpace I3 y) :
      A' n 0 s y v = ((S n).base.metric s).inner (W.embedding y)
        (mfderiv I3 I3 W.embedding y (v 0)) (mfderiv I3 I3 W.embedding y (v 1)) := by
    simpa only [hOne y hy, one_mul] using hA'₀' n s y (hU hy) v
  have hmodelSlab : Icc (-2 * modelDepth eps - 2) 0 ⊆ ancientTimeInterval.carrier :=
    fun _ hr => hr.2
  have hmodelReg : Ioo (-2 * modelDepth eps - 2) 0 ⊆ ancientTimeInterval.regular :=
    fun _ hr => hr.2
  obtain ⟨B, hB₀, hBd⟩ := exists_closedWindow_metric_time_fields W.model.S W.model.isSolution
    (a := -2 * modelDepth eps - 2) (c := -2 * modelDepth eps - 1) (b := 0)
    (by linarith) (by linarith) hmodelSlab hmodelReg
  have hB (q : ℕ) (s : ℝ) (hs : s ∈ L) (y : W.model.M) :
      HasDerivWithinAt (fun r => B q r y) (B (q + 1) s y) L s := (hBd q s hs y).2
  have hp : W.model.basepoint ∈ W.embedding.source := by
    apply W.buffered_ball
    change riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint W.model.basepoint ≤ _
    rw [riemannianEDistOf_self]
    exact zero_le
  have hx : x ∈ W.embedding.target := by
    simpa only [W.base_map] using W.embedding.map_source' hp
  have hinv : W.embedding.symm x = W.model.basepoint :=
    (congrArg (W.embedding.symm : M → W.model.M) W.base_map.symm).trans
      (W.embedding.left_inv' hp)
  have hcone : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  have hmodelSub : Icc (-modelDepth eps) 0 ⊆ L := fun s hs => ⟨by linarith [hs.1], hs.2⟩
  have hsourceMap₀ : MapsTo (parabolicTime t (S₀.scalar t x)) (Icc (-modelDepth eps) 0)
      (Icc c b) := by
    intro s hs
    have hQ₀ := W.scalar_pos
    have hl : t - (eps * S₀.scalar t x)⁻¹ ≤ parabolicTime t (S₀.scalar t x) s := by
      simpa only [parabolicTime, modelDepth, div_eq_mul_inv, mul_inv, neg_mul, sub_eq_add_neg,
        add_comm] using add_le_add_left (div_le_div_of_nonneg_right hs.1 hQ₀.le) t
    have hu : parabolicTime t (S₀.scalar t x) s ≤ t :=
      add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs.2 hQ₀.le)
    exact ⟨hclo.le.trans hl, hu.trans htb.le⟩
  have hsmallU : riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps) ⊆ U :=
    (riemannianClosedBallOf_mono _ _ (le_add_of_nonneg_right zero_le_one)).trans hKU
  have hOld := W.strict_original_error_of_time_towers A B U hsmallU
    (fun s y hy v => hA₀ s y hy v) hB₀ (Icc c b) L (fun q s hs y => hA q s hs y) hB
    hsourceMap₀ hmodelSub hstrict
  have hAreg := partial_pullback_time_tower_contDiffOn_closed S₀ hS₀ hac hcb hslab hreg
    W.embedding U hU A (fun s y hy v => hA₀ s y hy v) (fun q s hs y _hy => hA q s hs y)
  let F := PartialDiffeomorph.refl (I := I3) W.model.M
  have hBzero (s : ℝ) (y : W.model.M) (_hy : y ∈ U) (v : Fin 2 → TangentSpace I3 y) :
      B 0 s y v = (W.model.S.base.metric s).inner (F y)
        (mfderiv I3 I3 F y (v 0)) (mfderiv I3 I3 F y (v 1)) := by
    change B 0 s y v = (W.model.S.base.metric s).inner y
      (mfderiv I3 I3 (id : W.model.M → W.model.M) y (v 0))
      (mfderiv I3 I3 (id : W.model.M → W.model.M) y (v 1))
    simp only [hB₀, metricTensorField_apply, mfderiv_id, ContinuousLinearMap.id_apply]
  have hBreg := partial_pullback_time_tower_contDiffOn_closed W.model.S W.model.isSolution
    (a := -2 * modelDepth eps - 2) (c := -2 * modelDepth eps - 1) (b := 0)
    (by linarith) (by linarith) hmodelSlab hmodelReg F U (Set.subset_univ _) B hBzero
    (fun q s hs y _hy => hB q s hs y)
  have hscaleOne (g : SmoothRiemannianMetric I3 W.model.M) :
      scaleMetric 1 zero_lt_one g = g :=
    SmoothRiemannianMetric.ext_inner (fun y v w => by simp only [scaleMetric_inner, one_mul])
  let center (n : ℕ) := W.embedding.symm (x' n)
  let Q (n : ℕ) := (S n).scalar t (x' n)
  let C (n : ℕ) := W.model.S.scalar 0 (center n)
  have hcenterLim : Tendsto center atTop (𝓝 W.model.basepoint) := by
    have hh := (W.embedding.symm.contMDiffOn_toFun.continuousOn.continuousAt
      (W.embedding.open_target.mem_nhds hx)).tendsto.comp hx'
    rw [hinv] at hh
    exact hh
  have hscalarModel : ContinuousAt (fun z => W.model.S.scalar 0 z) W.model.basepoint :=
    (metricScalar_smooth (W.model.S.base.metric 0)).continuous.continuousAt
  have hClim : Tendsto C atTop (𝓝 (1 : ℝ)) := by
    have hh := hscalarModel.tendsto.comp hcenterLim
    rw [hcone] at hh
    exact hh
  have hLowLim : Tendsto (fun n => t - (eps * Q n)⁻¹) atTop
      (𝓝 (t - (eps * S₀.scalar t x)⁻¹)) :=
    tendsto_const_nhds.sub ((tendsto_const_nhds.mul hscalar).inv₀
      (mul_ne_zero W.eps_pos.ne' W.scalar_pos.ne'))
  have hBuff := eventually_scaled_closedBall_subset (W.model.S.base.metric 0) hcomplete
    W.model.basepoint (show 0 ≤ modelRadius eps + 1 by linarith) W.embedding.open_source
    W.buffered_ball (fun z => W.model.S.scalar 0 z) hscalarModel hcone
  have hOldSmall : riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps) ⊆
      riemannianBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps + 1) := by
    intro y hy
    have hyR : riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint y ≤
        ENNReal.ofReal (modelRadius eps) := hy
    exact hyR.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
  have hCmp := eventually_scaled_closedBall_subset (W.model.S.base.metric 0) hcomplete
    W.model.basepoint hR.le (isOpen_lt (continuous_riemannianEDist (W.model.S.base.metric 0)
      W.model.basepoint) continuous_const) hOldSmall (fun z => W.model.S.scalar 0 z)
      hscalarModel hcone
  let Valid (n : ℕ) : Prop := x' n ∈ W.embedding.target ∧ ∃ hc : 0 < C n, 0 < Q n ∧
    riemannianClosedBallOf (scaleMetric (C n) hc (W.model.S.base.metric 0)) (center n)
      (modelRadius eps + 1) ⊆ W.embedding.source ∧
    riemannianClosedBallOf (scaleMetric (C n) hc (W.model.S.base.metric 0)) (center n)
      (modelRadius eps) ⊆ K ∧
    Icc (t - (eps * Q n)⁻¹) t ⊆ D.regular ∧
    MapsTo (parabolicTime t (Q n)) (Icc (-modelDepth eps) 0) (Icc c b) ∧
    MapsTo (parabolicTime 0 (C n)) (Icc (-modelDepth eps) 0) L
  have hvalid : ∀ᶠ n in atTop, Valid n := by
    filter_upwards [hx'.eventually (W.embedding.open_target.mem_nhds hx),
      hscalar.eventually (Ioi_mem_nhds W.scalar_pos), hLowLim.eventually (Ioi_mem_nhds hclo),
      hClim.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
      hcenterLim.eventually hBuff, hcenterLim.eventually hCmp] with n hxt hQpos hlo hcHalf hb hcb'
    obtain ⟨hc, hbuff⟩ := hb
    obtain ⟨_hc', hcmp⟩ := hcb'
    refine ⟨hxt, hc, hQpos, hbuff, ?_, ?_, ?_, ?_⟩
    · intro y hy
      change riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint y ≤
        ENNReal.ofReal (modelRadius eps + 1)
      exact (hcmp hy).le
    · intro r hr
      exact hreg ⟨(hac.trans hlo).trans_le hr.1, hr.2.trans_lt htb⟩
    · intro s hs
      have hl : t - (eps * Q n)⁻¹ ≤ parabolicTime t (Q n) s := by
        simpa only [parabolicTime, modelDepth, div_eq_mul_inv, mul_inv, neg_mul, sub_eq_add_neg,
          add_comm] using add_le_add_left (div_le_div_of_nonneg_right hs.1 hQpos.le) t
      have hu : parabolicTime t (Q n) s ≤ t :=
        add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs.2 hQpos.le)
      exact ⟨hlo.le.trans hl, hu.trans htb.le⟩
    · intro s hs
      simp only [parabolicTime, zero_add]
      constructor
      · apply (le_div_iff₀ hc).mpr
        have hm := mul_le_mul_of_nonneg_left hcHalf.le
          (show 0 ≤ 2 * modelDepth eps + 1 by linarith)
        nlinarith [hs.1]
      · exact div_nonpos_of_nonpos_of_nonneg hs.2 hc.le
  let Good (n : ℕ) : Prop := Icc (t - (eps * (S n).scalar t (x' n))⁻¹) t ⊆ D.regular ∧
    ∃ W' : WindowedModelWitness eps kappa (S n) (x' n) t,
      (∀ (o : TangentOrientationSection M) (oN : TangentOrientationSection W.model.M),
        (∀ y ∈ W.embedding.source, ∃ hf : Function.Bijective (mfderiv I3 I3 W.embedding y),
          PreservesTangentOrientationAt oN o W.embedding y hf) →
        ∃ oN' : TangentOrientationSection W'.model.M, ∀ y ∈ W'.embedding.source,
          ∃ hf : Function.Bijective (mfderiv I3 I3 W'.embedding y),
            PreservesTangentOrientationAt oN' o W'.embedding y hf) ∧
      ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
        ∀ y ∈ riemannianClosedBallOf (W'.model.S.base.metric 0) W'.model.basepoint
            (modelRadius eps),
          tensor02CovDerivNormWith a (W'.comparison.jet b s)
            (W'.model.S.base.metric s) (W'.model.S.base.metric s) y < eps
  change ∀ᶠ n in atTop, Good n
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, ¬ Good n := by
    simpa only [Filter.Frequently, not_not] using hnot
  obtain ⟨φ, hφ, hbad⟩ := Filter.extraction_of_frequently_atTop (hfreq.and_eventually hvalid)
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  choose hxt hc hQ hbuff hcmp hwin hsrc hmod using fun k => (hbad k).2
  have hconvφ : ∀ K' : Set M, IsCompact K' → ∀ r : ℕ, ∀ e : ℝ, 0 < e →
      ∃ N₀ : ℕ, ∀ k ≥ N₀, ∀ τ ∈ Icc c b,
        metricDerivNormSupOn K' r ((S (φ k)).base.metric τ) (S₀.base.metric τ) R < e := by
    intro K' hK' r e he
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hconv K' hK' r e he)
    exact ⟨N₀, fun k hk τ hτ =>
      hN₀ (φ k) (hk.trans (hφ.id_le k)) τ (hslab ⟨hac.le.trans hτ.1, hτ.2⟩)⟩
  have hQφ : Tendsto (fun k => Q (φ k)) atTop (𝓝 (S₀.scalar t x)) := hscalar.comp hφtop
  have hCφ : Tendsto (fun k => C (φ k)) atTop (𝓝 1) := hClim.comp hφtop
  have hpair (i j : ℕ) (hij : i + 2 * j ≤ modelOrder eps) :
      ∀ᶠ k in atTop, ∀ s ∈ Icc (-modelDepth eps) 0,
        ∀ y ∈ riemannianClosedBallOf (scaleMetric (C (φ k)) (hc k) (W.model.S.base.metric 0))
            (center (φ k)) (modelRadius eps),
          tensor02CovDerivNormWith i
            (rescaledTensorTimeTower (A' (φ k)) t (Q (φ k)) j s -
              rescaledTensorTimeTower B 0 (C (φ k)) j s)
            (rescaledMetric W.model.S 0 (C (φ k)) (hc k) s)
            (rescaledMetric W.model.S 0 (C (φ k)) (hc k) s) y < eps := by
    have hAlpha : Tendsto (fun k => Q (φ k) * (Q (φ k))⁻¹ ^ j) atTop
        (𝓝 (S₀.scalar t x * (S₀.scalar t x)⁻¹ ^ j)) :=
      hQφ.mul ((hQφ.inv₀ W.scalar_pos.ne').pow j)
    have hBeta : Tendsto (fun k => C (φ k) * (C (φ k))⁻¹ ^ j) atTop (𝓝 (1 : ℝ)) := by
      simpa only [inv_one, one_pow, one_mul] using hCφ.mul ((hCφ.inv₀ one_ne_zero).pow j)
    have hh := eventually_strict_weighted_error_norm_on_scaled_ball_of_uniform_perturbation
      (fun s => W.model.S.base.metric s) (A j) (B j) (fun k => A' (φ k) j)
      W.model.basepoint (modelRadius eps) hK
      (fun y hy => by
        obtain ⟨V₁, hV₁, hp₁, ht₁, hAc⟩ := hAreg (⟨y, hKU hy⟩ : U)
        obtain ⟨V₂, hV₂, hp₂, _ht₂, hBc⟩ := hBreg (⟨y, hKU hy⟩ : U)
        obtain ⟨V₃, hV₃, hp₃, _ht₃, hgc⟩ := solution_chartGram_contDiffOn_closed
          W.model.S W.model.isSolution (a := -2 * modelDepth eps - 2)
          (c := -2 * modelDepth eps - 1) (b := 0) (by linarith) (by linarith) hmodelSlab
          hmodelReg y
        refine ⟨V₁ ∩ (V₂ ∩ V₃), hV₁.inter (hV₂.inter hV₃), ⟨hp₁, hp₂, hp₃⟩,
          (fun z hz => ht₁ hz.1), ?_, ?_, ?_⟩
        · intro r s
          exact (hgc r s).mono (Set.prod_mono Subset.rfl (fun z hz => hz.2.2))
        · intro slots
          exact (hAc j slots).mono (Set.prod_mono Subset.rfl (fun z hz => hz.1))
        · intro slots
          exact (hBc j slots).mono (Set.prod_mono Subset.rfl (fun z hz => hz.2.1)))
      (fun y hy => uniform_pullback_time_tower_chart_jets_of_metric_convergence
        (fun k => S (φ k)) (fun k => hS (φ k)) S₀ hS₀ hac hcb hslab hreg W.embedding U hU
        A (fun k => A' (φ k)) (fun s y hy v => hA₀ s y hy v) (fun q s hs y _hy => hA q s hs y)
        (fun k s y hy v => hA'₀ (φ k) s y hy v) (fun k q s hs y _hy => hA' (φ k) q s hs y)
        R hconvφ y (hKU hy) j)
      (fun k => center (φ k)) (hcenterLim.comp hφtop) (fun _ => t) (fun k => Q (φ k))
      (fun k => C (φ k)) (fun k => Q (φ k) * (Q (φ k))⁻¹ ^ j)
      (fun k => C (φ k) * (C (φ k))⁻¹ ^ j)
      W.scalar_pos hc zero_lt_one tendsto_const_nhds hQφ hCφ hAlpha hBeta i hcmp
      (fun k s hs => hsrc k hs)
      (fun k s hs => by simpa only [parabolicTime, zero_add] using hmod k hs)
      (fun s hs => hsourceMap₀ hs)
      (fun s hs => by simpa only [div_one] using hmodelSub hs)
      (fun s hs y hy => by
        have hy' : y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
            (modelRadius eps) := by
          simpa only [hscaleOne] using hy
        simpa only [div_one, one_smul, hscaleOne] using hOld i j hij s hs y hy')
    simpa only [rescaledTensorTimeTower, rescaledMetric, parabolicTime, zero_add] using hh
  have hfinite : {ij : ℕ × ℕ | ij.1 + 2 * ij.2 ≤ modelOrder eps}.Finite := by
    apply ((Finset.range (modelOrder eps + 1)).product
      (Finset.range (modelOrder eps + 1))).finite_toSet.subset
    intro ij hij
    change ij.1 + 2 * ij.2 ≤ modelOrder eps at hij
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩
  have hall := (Filter.eventually_all_finite hfinite).mpr (fun ij hij => hpair ij.1 ij.2 hij)
  obtain ⟨k, hk⟩ := hall.exists
  have hright : W.embedding (center (φ k)) = x' (φ k) := W.embedding.right_inv' (hxt k)
  have hnew := W.exists_recentered_strict_of_flow_time_towers (S (φ k)) (center (φ k)) t
    (hc k) (by rw [hright]; exact hQ k) W.time_mem
    (by rw [hright]; exact (hwin k).trans D.regular_subset)
    U hU (hbuff k) ((hcmp k).trans hKU) (A' (φ k)) B
    (fun s y hy v => hA'₀ (φ k) s y hy v) hB₀ (Icc c b) L
    (fun q s hs y => hA' (φ k) q s hs y) hB
    (by rw [hright]; exact hsrc k) (hmod k)
    (fun i j hij s hs y hy => by
      have hh := hk (i, j) hij s hs y hy
      simpa only [hright] using hh)
  apply (hbad k).1
  refine ⟨hwin k, ?_⟩
  rw [hright] at hnew
  exact hnew

theorem WindowedModelWitness.eventually_of_tendsto_flows
    {S₀ : SolutionOn (I := I3) (M := M) D} (hS₀ : IsSolutionOn S₀)
    {S : ℕ → SolutionOn (I := I3) (M := M) D} (hS : ∀ n, IsSolutionOn (S n))
    {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S₀ x t)
    (hwindow : Icc (t - (eps * S₀.scalar t x)⁻¹) t ⊆ D.regular)
    (hstrict : ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
      ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps),
        tensor02CovDerivNormWith a (W.comparison.jet b s)
          (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps)
    (R : SmoothRiemannianMetric I3 M)
    (hconv : ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ τ ∈ D.carrier, ∀ i ≤ p, ∀ v : M,
      metricDerivNorm i ((S n).base.metric τ) (S₀.base.metric τ) R v < e)
    {x' : ℕ → M} (hx' : Tendsto x' atTop (𝓝 x))
    (hscalar : Tendsto (fun n => (S n).scalar t (x' n)) atTop (𝓝 (S₀.scalar t x))) :
    ∀ᶠ n in atTop, Icc (t - (eps * (S n).scalar t (x' n))⁻¹) t ⊆ D.regular ∧
      Nonempty (WindowedModelWitness eps kappa (S n) (x' n) t) := by
  have hconv' : ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop,
      ∀ τ ∈ D.carrier, metricDerivNormSupOn K p ((S n).base.metric τ) (S₀.base.metric τ) R < e := by
    intro K _hK p e he
    filter_upwards [hconv p (e / 2) (half_pos he)] with n hn τ hτ
    exact (metricDerivNormSupOn_le_of_forall K p _ _ R (e / 2) (half_pos he).le
      fun i hi v _hv => (hn τ hτ i hi v).le).trans_lt (half_lt_self he)
  filter_upwards [W.eventually_strict_of_tendsto_flows hS₀ hS hwindow hstrict R hconv' hx'
    hscalar] with n hn
  obtain ⟨hwin, W', _, _⟩ := hn
  exact ⟨hwin, ⟨W'⟩⟩

theorem orientedWitness_eventually_of_tendsto_flows
    {S₀ : SolutionOn (I := I3) (M := M) D} (hS₀ : IsSolutionOn S₀)
    {S : ℕ → SolutionOn (I := I3) (M := M) D} (hS : ∀ n, IsSolutionOn (S n))
    {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S₀ x t)
    (o : TangentOrientationSection M) (oN : TangentOrientationSection W.model.M)
    (hO : ∀ y ∈ W.embedding.source, ∃ hf : Function.Bijective (mfderiv I3 I3 W.embedding y),
      PreservesTangentOrientationAt oN o W.embedding y hf)
    (hwindow : Icc (t - (eps * S₀.scalar t x)⁻¹) t ⊆ D.regular)
    (hstrict : ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
      ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps),
        tensor02CovDerivNormWith a (W.comparison.jet b s)
          (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps)
    (R : SmoothRiemannianMetric I3 M)
    (hconv : ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop,
      ∀ τ ∈ D.carrier, metricDerivNormSupOn K p ((S n).base.metric τ) (S₀.base.metric τ) R < e)
    {x' : ℕ → M} (hx' : Tendsto x' atTop (𝓝 x))
    (hscalar : Tendsto (fun n => (S n).scalar t (x' n)) atTop (𝓝 (S₀.scalar t x))) :
    ∀ᶠ n in atTop, Icc (t - (eps * (S n).scalar t (x' n))⁻¹) t ⊆ D.regular ∧
      OrientedWitness (S n) o eps kappa (x' n) t := by
  filter_upwards [W.eventually_strict_of_tendsto_flows hS₀ hS hwindow hstrict R hconv hx'
    hscalar] with n hn
  obtain ⟨hwin, W', horient, _⟩ := hn
  obtain ⟨oN', hO'⟩ := horient o oN hO
  exact ⟨hwin, W', oN', hO'⟩

end Perturbation

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

import SigmaProbCompletionContinuity
import SigmaProbCompletionProcess

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

/-- Almost sure convergence of measurable random variables implies weak convergence
of their actual probability laws. -/
theorem probability_law_tendsto_of_ae {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → E) (Y : Ω → E)
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (ht : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Tendsto (fun n => ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) (hX n).aemeasurable)
      atTop (𝓝 (ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) hY.aemeasurable)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  simp only [ProbabilityMeasure.toMeasure_map]
  simp_rw [integral_map (hX _).aemeasurable f.continuous.measurable.aestronglyMeasurable,
    integral_map hY.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro n
    exact (f.continuous.measurable.comp (hX n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun ω => f.norm_coe_le_norm (X n ω)
  · filter_upwards [ht] with ω hω
    exact f.continuous.continuousAt.tendsto.comp hω

/-- Gamma laws are preserved under almost sure limits when their time parameters
converge; the zero-time Dirac law is included. -/
theorem gamma_law_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (ht : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (r : ℕ → ℝ≥0) (t : ℝ≥0) (hr : Tendsto r atTop (𝓝 t))
    (hlaw : ∀ n, P.map (X n) = gammaCompletion (r n)) :
    P.map Y = gammaCompletion t := by
  have h := probability_law_tendsto_of_ae P X Y hX hY ht
  have he : (fun n => ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
      (hX n).aemeasurable) = fun n => gammaCompletionProbability (r n) := by
    funext n
    apply Subtype.ext
    exact hlaw n
  rw [he] at h
  exact congrArg ProbabilityMeasure.toMeasure
    (tendsto_nhds_unique h (gamma_completion_weak_continuous.tendsto t |>.comp hr))

/-- Equal laws at every stage imply equal laws of almost sure limits, even when
the two sequences are defined on different probability spaces. -/
theorem probability_law_eq_of_ae_limits {Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → E) (Y : Ω → E) (X' : ℕ → Ω' → E) (Y' : Ω' → E)
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hX' : ∀ n, Measurable (X' n)) (hY' : Measurable Y')
    (ht : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (ht' : ∀ᵐ ω ∂Q, Tendsto (fun n => X' n ω) atTop (𝓝 (Y' ω)))
    (he : ∀ n, P.map (X n) = Q.map (X' n)) : P.map Y = Q.map Y' := by
  have h := probability_law_tendsto_of_ae P X Y hX hY ht
  have h' := probability_law_tendsto_of_ae Q X' Y' hX' hY' ht'
  have he' : (fun n => ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
      (hX n).aemeasurable) = fun n =>
      ProbabilityMeasure.map (⟨Q, inferInstance⟩ : ProbabilityMeasure Ω')
        (hX' n).aemeasurable := by
    funext n
    exact Subtype.ext (he n)
  rw [he'] at h
  exact congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique h h')

/-- A finite independent family remains independent in the form of its exact
joint product law after coordinatewise almost sure convergence. -/
theorem independent_finite_joint_law_of_ae_tendsto {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → ι → Ω → ℝ) (Y : ι → Ω → ℝ)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ i, Measurable (Y i))
    (hI : ∀ n, iIndepFun (fun _ => inferInstance) (X n) P)
    (ht : ∀ i, ∀ᵐ ω ∂P, Tendsto (fun n => X n i ω) atTop (𝓝 (Y i ω))) :
    P.map (fun ω i => Y i ω) = Measure.pi (fun i => P.map (Y i)) := by
  let Q : Measure (ι → Ω) := Measure.pi (fun _ : ι => P)
  have hcopy (n : ℕ) : Q.map (fun ω i => X n i (ω i)) =
      Measure.pi (fun i => P.map (X n i)) :=
    (measurePreserving_pi (fun _ : ι => P) (fun i => P.map (X n i))
      (fun i => ⟨hX n i, rfl⟩)).map_eq
  have hcopyY : Q.map (fun ω i => Y i (ω i)) =
      Measure.pi (fun i => P.map (Y i)) :=
    (measurePreserving_pi (fun _ : ι => P) (fun i => P.map (Y i))
      (fun i => ⟨hY i, rfl⟩)).map_eq
  rw [← hcopyY]
  apply probability_law_eq_of_ae_limits P Q
    (fun n ω i => X n i ω) (fun ω i => Y i ω)
    (fun n ω i => X n i (ω i)) (fun ω i => Y i (ω i))
  · exact fun n => measurable_pi_lambda _ (hX n)
  · exact measurable_pi_lambda _ hY
  · exact fun n => measurable_pi_lambda _ fun i => (hX n i).comp (measurable_pi_apply i)
  · exact measurable_pi_lambda _ fun i => (hY i).comp (measurable_pi_apply i)
  · filter_upwards [ae_all_iff.mpr ht] with ω hω
    exact tendsto_pi_nhds.mpr hω
  · have hh : ∀ i, ∀ᵐ ω ∂Q, Tendsto (fun n => X n i (ω i)) atTop
        (𝓝 (Y i (ω i))) := fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => P) (i := i)).eventually (ht i)
    filter_upwards [ae_all_iff.mpr hh] with ω hω
    exact tendsto_pi_nhds.mpr hω
  · intro n
    rw [hcopy, independent_finite_joint_law P (X n) (hX n) (hI n)]

/-- Exact finite product law is equivalent to independence in the direction used
for the limiting family. -/
theorem independent_finite_of_joint_law {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i))
    (hlaw : P.map (fun ω i => Y i ω) = Measure.pi (fun i => P.map (Y i))) :
    iIndepFun (fun _ => inferInstance) Y P := by
  classical
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S sets hs
  let A : ι → Set ℝ := fun i => if i ∈ S then sets i else univ
  have hA : ∀ i, MeasurableSet (A i) := by
    intro i
    dsimp [A]
    split_ifs with hi
    · exact hs i hi
    · exact MeasurableSet.univ
  have he : (fun ω i => Y i ω) ⁻¹' Set.pi univ A = ⋂ i ∈ S, Y i ⁻¹' sets i := by
    ext ω
    simp [A]
  rw [← he, ← Measure.map_apply (measurable_pi_lambda _ hY) (MeasurableSet.univ_pi hA),
    hlaw, Measure.pi_pi, ← Finset.prod_mul_prod_compl S]
  have hc : (∏ i ∈ Sᶜ, (P.map (Y i)) (A i)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    simp only [A, if_neg (Finset.mem_compl.mp hi)]
    rw [Measure.map_apply (hY i) MeasurableSet.univ]
    simp
  rw [hc, mul_one]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [A, if_pos hi]
  exact Measure.map_apply (hY i) (hs i hi)

/-- Finite independence is closed under coordinatewise almost sure limits. -/
theorem independent_finite_of_ae_tendsto {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → ι → Ω → ℝ) (Y : ι → Ω → ℝ)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ i, Measurable (Y i))
    (hI : ∀ n, iIndepFun (fun _ => inferInstance) (X n) P)
    (ht : ∀ i, ∀ᵐ ω ∂P, Tendsto (fun n => X n i ω) atTop (𝓝 (Y i ω))) :
    iIndepFun (fun _ => inferInstance) Y P :=
  independent_finite_of_joint_law P Y hY
    (independent_finite_joint_law_of_ae_tendsto P X Y hX hY hI ht)

/-- Restrict an independent real family along any injection. -/
theorem independent_real_reindex {Ω ι κ : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ι → Ω → ℝ)
    (hI : iIndepFun (fun _ => inferInstance) X P) (e : κ ↪ ι) :
    iIndepFun (fun _ => inferInstance) (fun i => X (e i)) P := by
  classical
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S sets hs
  let g : ι → Set ℝ := Function.extend e sets (fun _ => univ)
  have hg (i : κ) : g (e i) = sets i := e.injective.extend_apply _ _ _
  have hm (i : ι) (hi : i ∈ S.map e) : MeasurableSet (g i) := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    rw [hg]
    exact hs j hj
  have hh := hI.measure_inter_preimage_eq_mul (S.map e) hm
  have he : (⋂ i ∈ S.map e, X i ⁻¹' g i) = ⋂ i ∈ S, X (e i) ⁻¹' sets i := by
    ext ω
    simp only [mem_iInter,mem_preimage]
    constructor
    · intro h i hi
      simpa only [hg] using h (e i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
    · intro h i hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
      simpa only [hg] using h j hj
  rw [he, Finset.prod_map] at hh
  simpa only [hg] using hh

/-- Arbitrary indexed independence is preserved by coordinatewise almost sure
limits. No simultaneous exceptional set across all indices is required. -/
theorem independent_of_ae_tendsto {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → ι → Ω → ℝ) (Y : ι → Ω → ℝ)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ i, Measurable (Y i))
    (hI : ∀ n, iIndepFun (fun _ => inferInstance) (X n) P)
    (ht : ∀ i, ∀ᵐ ω ∂P, Tendsto (fun n => X n i ω) atTop (𝓝 (Y i ω))) :
    iIndepFun (fun _ => inferInstance) Y P := by
  classical
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S sets hs
  have hS := independent_finite_of_ae_tendsto P
    (fun n (i : S) => X n i) (fun (i : S) => Y i)
    (fun n i => hX n i) (fun i => hY i)
    (fun n => independent_real_reindex P (X n) (hI n) (Function.Embedding.subtype _))
    (fun i => ht i)
  have hh := hS.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i : S => sets i) (fun i _ => hs i i.property)
  rw [← Finset.prod_attach S (fun i => P (Y i ⁻¹' sets i))]
  simpa only [Finset.mem_univ, iInter_true, iInter_subtype] using hh

end
end Sigma

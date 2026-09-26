import SigmaProbGammaProcessFinite

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

/-- Disjoint collections of independent sigma algebras remain independent when
each collection is joined. This is the finite-block aggregation step in the
consistency argument for the process laws. -/
theorem gamma_process_independent_sigma_groups {Ω ι κ : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : ι → MeasurableSpace Ω)
    (hm : ∀ i, m i ≤ mΩ) (hi : iIndep m P)
    (s : κ → Set ι) (hdis : Pairwise (fun j k => Disjoint (s j) (s k))) :
    iIndep (fun j => ⨆ i ∈ s j, m i) P := by
  classical
  rw [iIndep_iff]
  intro F events hmeas
  induction F using Finset.induction_on generalizing events with
  | empty => simp
  | @insert j F hj ih =>
    let T : Set ι := ⋃ k ∈ F, s k
    have hd : Disjoint (s j) T := by
      rw [Set.disjoint_left]
      intro i hij hiT
      obtain ⟨k, hk, hik⟩ := Set.mem_iUnion₂.mp hiT
      exact Set.disjoint_left.mp (hdis (show j ≠ k by intro he; subst k; exact hj hk)) hij hik
    have hpair := indep_iSup_of_disjoint hm hi hd
    have hrest : @MeasurableSet Ω (⨆ i ∈ T, m i) (⋂ k ∈ F, events k) := by
      apply F.measurableSet_biInter
      intro k hk
      have hle : (⨆ i ∈ s k, m i) ≤ ⨆ i ∈ T, m i := by
        apply iSup_le
        intro i
        apply iSup_le
        intro hik
        exact le_iSup_of_le i (le_iSup_of_le (Set.mem_iUnion₂.mpr ⟨k, hk, hik⟩) le_rfl)
      exact hle _ (hmeas k (Finset.mem_insert_of_mem hk))
    rw [Finset.set_biInter_insert]
    rw [(Indep_iff _ _ P).mp hpair (events j) (⋂ k ∈ F, events k)
      (hmeas j (Finset.mem_insert_self _ _)) hrest]
    rw [ih (fun k hk => hmeas k (Finset.mem_insert_of_mem hk)), Finset.prod_insert hj]

/-- Measurable transformations of pairwise disjoint finite coordinate blocks
of an independent family remain jointly independent. -/
theorem gamma_process_independent_finite_groups {Ω ι κ : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hi : iIndepFun (fun _ => inferInstance) X P)
    (s : κ → Finset ι) (hdis : Pairwise (fun j k => Disjoint (s j) (s k)))
    (f : ∀ k, (s k → ℝ) → ℝ) (hf : ∀ k, Measurable (f k)) :
    iIndepFun (fun _ => inferInstance) (fun k ω => f k (fun i => X i ω)) P := by
  let m : ι → MeasurableSpace Ω := fun i => MeasurableSpace.comap (X i) inferInstance
  have hmi (i : ι) : m i ≤ mΩ := (hX i).comap_le
  have hgroup := gamma_process_independent_sigma_groups P m hmi hi
    (fun k => (s k : Set ι)) (fun j k hjk => by simpa using hdis hjk)
  apply (iIndep_iff _ _).mpr
  intro F events hevents
  apply (iIndep_iff _ _).mp hgroup
  intro k hk
  have hmX (i : s k) : @Measurable Ω ℝ (⨆ i ∈ (s k : Set ι), m i) inferInstance (X i) := by
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le i.val (le_iSup_of_le i.property le_rfl)
  have hmfun : @Measurable Ω ℝ (⨆ i ∈ (s k : Set ι), m i) inferInstance
      (fun ω => f k (fun i => X i ω)) := by
    letI : MeasurableSpace Ω := ⨆ i ∈ (s k : Set ι), m i
    exact (hf k).comp (measurable_pi_lambda _ hmX)
  exact hmfun.comap_le _ (hevents k hk)


/-- Disjoint blocks of Gamma increments have the product Gamma law with
parameters equal to their summed durations. This is actual joint-law equality,
not merely a collection of one-dimensional marginals. -/
theorem gamma_process_block_joint_law {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hi : iIndepFun (fun _ => inferInstance) X P)
    (d : ι → ℝ≥0) (hlaw : ∀ i, P.map (X i) = gammaCompletion (d i))
    (s : κ → Finset ι) (hdis : Pairwise (fun j k => Disjoint (s j) (s k))) :
    P.map (fun ω k => ∑ i ∈ s k, X i ω) =
      Measure.pi (fun k => gammaCompletion (∑ i ∈ s k, d i)) := by
  classical
  have hgroups := gamma_process_independent_finite_groups P X hX hi s hdis
    (fun k z => ∑ i : s k, z i) (fun k => Finset.measurable_sum _ fun i hi => measurable_pi_apply i)
  have he (k : κ) (ω : Ω) : (∑ i : s k, X i ω) = ∑ i ∈ s k, X i ω :=
    Finset.sum_coe_sort (s k) (fun i => X i ω)
  simp_rw [he] at hgroups
  rw [independent_finite_joint_law P _
    (fun k => Finset.measurable_sum _ fun i hi => hX i) hgroups]
  congr 1
  funext k
  exact gamma_process_finset_sum_law P X hX hi d hlaw (s k)

/-- Projective consistency at the independent-increment level: coarsening any
finite partition groups disjoint increment blocks and gives exactly the product
law of the coarsened durations. -/
theorem gamma_process_grouped_product_law {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ι → ℝ≥0) (s : κ → Finset ι)
    (hdis : Pairwise (fun j k => Disjoint (s j) (s k))) :
    (Measure.pi (fun i => gammaCompletion (d i))).map (fun x k => ∑ i ∈ s k, x i) =
      Measure.pi (fun k => gammaCompletion (∑ i ∈ s k, d i)) :=
  gamma_process_block_joint_law _ (fun i x => x i) (fun i => measurable_pi_apply i)
    (gamma_process_product_coordinates_independent d) d (gamma_process_product_coordinate_law d) s hdis

end
end Sigma

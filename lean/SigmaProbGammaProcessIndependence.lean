import SigmaProbGammaProcessGroups

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators

/-- Restricting an independent family along an injection preserves independence. -/
theorem gamma_process_independent_reindex {Ω ι κ E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : ι → Ω → E) (hi : iIndepFun (fun _ => inferInstance) X P)
    (e : κ ↪ ι) : iIndepFun (fun _ => inferInstance) (fun k => X (e k)) P := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hs
  let g : ι → Set E := Function.extend e sets (fun _ => univ)
  have hg (k : κ) : g (e k) = sets k := e.injective.extend_apply _ _ _
  have hh := hi.measure_inter_preimage_eq_mul (S.map e) (sets := g) (by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
    rw [hg]
    exact hs k hk)
  have he : (⋂ i ∈ S.map e, X i ⁻¹' g i) = ⋂ k ∈ S, X (e k) ⁻¹' sets k := by
    ext ω
    simp only [mem_iInter, mem_preimage]
    constructor
    · intro h k hk
      simpa only [hg] using h (e k) (Finset.mem_map.mpr ⟨k, hk, rfl⟩)
    · intro h i hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
      simpa only [hg] using h k hk
  rw [he, Finset.prod_map] at hh
  simpa only [hg] using hh

theorem gamma_process_finite_joint_law {Ω ι E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → E) (hm : ∀ i, Measurable (X i)) (hi : iIndepFun (fun _ => inferInstance) X P) :
    P.map (fun ω i => X i ω) = Measure.pi (fun i => P.map (X i)) := by
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (measurable_pi_lambda _ hm) (MeasurableSet.univ_pi hs)]
  have he : (fun ω i => X i ω) ⁻¹' Set.pi Set.univ s = ⋂ i, X i ⁻¹' s i := by
    ext ω
    simp
  rw [he, hi.meas_iInter (fun i => ⟨s i, hs i, rfl⟩)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Measure.map_apply (hm i) (hs i)]

theorem gamma_process_independent_of_finite_joint_laws {Ω ι E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → E) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ S : Finset ι, P.map (fun ω (i : S) => X i ω) =
      Measure.pi (fun i : S => P.map (X i))) : iIndepFun (fun _ => inferInstance) X P := by
  classical
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S sets hs
  have he : (⋂ i ∈ S, X i ⁻¹' sets i) =
      (fun ω (i : S) => X i ω) ⁻¹' Set.pi Set.univ (fun i : S => sets i) := by
    ext ω
    simp
  rw [he, ← Measure.map_apply (measurable_pi_lambda _ (fun i : S => hX i))
    (MeasurableSet.univ_pi (fun i : S => hs i i.property)), hlaw S, Measure.pi_pi]
  rw [← Finset.prod_coe_sort S]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Measure.map_apply (hX i) (hs i i.property)]

/-- Measurable functions of two independent sigma algebras are independent. -/
theorem gamma_process_independent_from_sigma {Ω E F : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F] (P : Measure Ω) (m n : MeasurableSpace Ω)
    (h : Indep m n P) (X : Ω → E) (Y : Ω → F)
    (hX : @Measurable Ω E m inferInstance X) (hY : @Measurable Ω F n inferInstance Y) :
    IndepFun X Y P := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  exact (Indep_iff m n P).mp h (X ⁻¹' s) (Y ⁻¹' t) (hX hs) (hY ht)

/-- Two independent finite vectors with independent coordinates have a product
law after pairing corresponding coordinates. -/
theorem gamma_process_paired_vector_law {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hiX : iIndepFun (fun _ => inferInstance) X P) (hiY : iIndepFun (fun _ => inferInstance) Y P)
    (hXY : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P) :
    P.map (fun ω i => (X i ω, Y i ω)) =
      Measure.pi (fun i => (P.map (X i)).prod (P.map (Y i))) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι
  have hp := (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_lambda _ hX).aemeasurable (measurable_pi_lambda _ hY).aemeasurable).mp hXY
  rw [gamma_process_finite_joint_law P X hX hiX, gamma_process_finite_joint_law P Y hY hiY] at hp
  have he := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun i => P.map (X i)) (fun i => P.map (Y i))).symm e
  rw [← he.map_eq, ← hp, Measure.map_map e.symm.measurable
    ((measurable_pi_lambda _ hX).prod_mk (measurable_pi_lambda _ hY))]
  rfl

end
end Sigma

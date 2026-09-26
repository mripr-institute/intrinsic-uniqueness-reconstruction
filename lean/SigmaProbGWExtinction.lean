import SigmaProbGWCanonical

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- The critical Poisson PGF has exactly one real fixed point. -/
theorem poisson_one_pgf_fixed_point (x : ℝ) (hx : x = Real.exp (x - 1)) : x = 1 := by
  by_contra h
  have he := Real.add_one_lt_exp (sub_ne_zero.mpr h)
  linarith

theorem gw_poisson_extinction_probability_succ (d : ℕ) :
    (gwExtinctionProbability (ProbabilityTheory.poissonPMF 1) (d+1)).toReal =
      Real.exp ((gwExtinctionProbability (ProbabilityTheory.poissonPMF 1) d).toReal - 1) := by
  rw [gw_extinction_probability_succ,
    nat_probability_generating_ennreal_toReal _ _ (gw_extinction_probability_le_one _ d),
    poisson_one_native_pgf]

/-- The increasing probabilities of extinction at finite depth converge to one.
The fixed-point equation is obtained from the actual branching recurrence. -/
theorem gw_poisson_extinction_probability_iSup :
    (⨆ d, gwExtinctionProbability (ProbabilityTheory.poissonPMF 1) d) = 1 := by
  let q := ProbabilityTheory.poissonPMF 1
  let L : ℝ≥0∞ := ⨆ d, gwExtinctionProbability q d
  have hL : L ≤ 1 := iSup_le fun d => gw_extinction_probability_le_one q d
  have hLt : L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hL
  have ht : Tendsto (gwExtinctionProbability q) atTop (𝓝 L) :=
    tendsto_atTop_iSup (gw_extinction_probability_mono q)
  have htr : Tendsto (fun d => (gwExtinctionProbability q d).toReal) atTop (𝓝 L.toReal) :=
    (ENNReal.tendsto_toReal hLt).comp ht
  have hs : Tendsto (fun d => (gwExtinctionProbability q (d+1)).toReal)
      atTop (𝓝 L.toReal) := htr.comp (tendsto_add_atTop_nat 1)
  have he : Tendsto (fun d => Real.exp ((gwExtinctionProbability q d).toReal - 1))
      atTop (𝓝 (Real.exp (L.toReal - 1))) :=
    Real.continuous_exp.continuousAt.tendsto.comp (htr.sub_const 1)
  have hfix : L.toReal = Real.exp (L.toReal - 1) := by
    apply tendsto_nhds_unique hs
    simpa only [q, gw_poisson_extinction_probability_succ] using he
  have hreal : L.toReal = 1 := poisson_one_pgf_fixed_point _ hfix
  exact (ENNReal.toReal_eq_toReal hLt ENNReal.one_ne_top).mp
    (by simpa only [ENNReal.one_toReal] using hreal)

theorem gw_poisson_finite_probability :
    treeSourceProbability {ω | gwTotalSize (gwOffspring (ProbabilityTheory.poissonPMF 1) ω) < ∞} =
      1 := by
  rw [gw_finite_probability, gw_poisson_extinction_probability_iSup]

/-- Almost-sure finiteness of the literal retained tree, not an assumed
finite-size random variable. -/
theorem gw_poisson_total_size_finite_ae :
    ∀ᵐ ω ∂treeSourceProbability,
      gwTotalSize (gwOffspring (ProbabilityTheory.poissonPMF 1) ω) < ∞ := by
  apply (mem_ae_iff_prob_eq_one ?_).mpr gw_poisson_finite_probability
  exact measurableSet_lt
    (gw_total_size_measurable.comp (gw_offspring_measurable _)) measurable_const

theorem gw_poisson_tree_finite_ae :
    ∀ᵐ ω ∂treeSourceProbability,
      (gwTree (gwOffspring (ProbabilityTheory.poissonPMF 1) ω)).Finite :=
  gw_poisson_total_size_finite_ae.mono fun _ h => (gw_total_size_finite_iff _).mp h

theorem gw_poisson_extinct_ae :
    ∀ᵐ ω ∂treeSourceProbability,
      ∃ d, gwExtinctAt d (gwOffspring (ProbabilityTheory.poissonPMF 1) ω) :=
  gw_poisson_total_size_finite_ae.mono fun _ h => (gw_total_size_finite_iff_extinct _).mp h

/-- A concrete native probability space carrying iid Poisson offspring and the
usual rooted construction with almost surely finite total size. -/
theorem exists_poisson_gw_finite_tree :
    ∃ a : TreeSource → GWOffspringArray,
      Measurable a ∧
      ProbabilityTheory.iIndepFun (fun _ : List ℕ => inferInstance)
        (fun w ω => a ω w) treeSourceProbability ∧
      (∀ w, treeSourceProbability.map (fun ω => a ω w) =
        (ProbabilityTheory.poissonPMF 1).toMeasure) ∧
      (∀ᵐ ω ∂treeSourceProbability, (gwTree (a ω)).Finite) :=
  ⟨gwOffspring (ProbabilityTheory.poissonPMF 1), gw_offspring_measurable _,
    gw_offspring_independent _, gw_offspring_coordinate_law _, gw_poisson_tree_finite_ae⟩

end
end Sigma

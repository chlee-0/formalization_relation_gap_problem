import D2RelationGap.FoxRank

/-! Fox-span control for any normally generating tuple of the actual kernel.
The source independent rows originate in OpenAI, A Counterexample to Wall's D(2) Problem,
October 6, 2026; openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
This proves the lower bound four, not the required lower bound five. -/
namespace D2RelationGap.FoxSpan
open Targets Cyclotomic FoxSemantics FoxRank
noncomputable section

/-- Kernel elements whose evaluated Fox vector lies in V form a subgroup normal in F. -/
def spanKernel (V : Submodule E Vector) : Subgroup F where
  carrier := {f | f ∈ N ∧ derivative f ∈ V}
  one_mem' := ⟨N.one_mem, by simp⟩
  mul_mem' := by
    rintro u v ⟨hu, hdu⟩ ⟨hv, hdv⟩
    refine ⟨N.mul_mem hu hv, ?_⟩
    rw [derivative_mul]
    exact V.add_mem hdu (V.smul_mem _ hdv)
  inv_mem' := by
    rintro u ⟨hu, hdu⟩
    refine ⟨N.inv_mem hu, ?_⟩
    rw [derivative_inv]
    exact V.neg_mem (V.smul_mem _ hdu)

instance spanKernel_normal (V : Submodule E Vector) : (spanKernel V).Normal where
  conj_mem := by
    rintro n ⟨hn, hdn⟩ f
    refine ⟨Subgroup.Normal.conj_mem (inferInstance : N.Normal) n hn f, ?_⟩
    rw [derivative_conjugate f (⟨n, hn⟩ : N)]
    exact V.smul_mem _ hdn

/-- Normal closure sends every kernel element into the span of the proposed generators. -/
theorem normal_generators_span {k : ℕ} (v : Fin k → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) (n : N) :
    derivative (n : F) ∈ Submodule.span E (Set.range (fun j => derivative (v j))) := by
  let V := Submodule.span E (Set.range (fun j => derivative (v j)))
  have h : Subgroup.normalClosure (Set.range v) ≤ spanKernel V := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j, rfl⟩
    refine ⟨?_, Submodule.subset_span ⟨j, rfl⟩⟩
    rw [← hv]
    exact Subgroup.subset_normalClosure ⟨j, rfl⟩
  rw [hv] at h
  exact (h n.property).2

theorem sourceRelator_mem_kernel (i : Fin 4) : freeWord (sourceRelator i) ∈ N := by
  apply MonoidHom.mem_ker.mpr
  apply PresentedGroup.one_of_mem
  fin_cases i <;> simp [sourceRelator, quotientRelations, sourceRelations]

theorem source_span_le_normal_generator_span {k : ℕ} (v : Fin k → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) :
    Submodule.span E (Set.range sourceRows) ≤
      Submodule.span E (Set.range (fun j => derivative (v j))) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact normal_generators_span v hv ⟨_, sourceRelator_mem_kernel i⟩

/-- An unconditional bound on arbitrary normal-generating families for the fixed epimorphism. -/
theorem normal_generators_at_least_four {k : ℕ} (h : HasNormalGenerators k) : 4 ≤ k := by
  obtain ⟨v, hv⟩ := h
  have hspan := source_span_le_normal_generator_span v hv
  have hdim := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card sourceRows_independent] at hdim
  exact hdim.trans (by simpa only [Set.finrank, Fintype.card_fin] using
    finrank_range_le_card (R := E) (fun j => derivative (v j)))

/-- A hypothetical four-element normal-generating tuple has independent evaluated rows. -/
theorem four_normal_generator_rows_independent (v : Fin 4 → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) :
    LinearIndependent E (fun j => derivative (v j)) := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  have hdim := Submodule.finrank_mono (source_span_le_normal_generator_span v hv)
  rw [sourceRows_span_dimension] at hdim
  apply le_antisymm hdim
  simpa only [Set.finrank, Fintype.card_fin] using
    finrank_range_le_card (R := E) (fun j => derivative (v j))

/-- This is algebraic injectivity only; a presentation-complex boundary bridge is still needed. -/
theorem four_normal_generator_linearCombination_injective (v : Fin 4 → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) :
    Function.Injective (Fintype.linearCombination E (fun j => derivative (v j))) :=
  linearIndependent_iff_injective_fintypeLinearCombination.mp
    (four_normal_generator_rows_independent v hv)

end
end D2RelationGap.FoxSpan

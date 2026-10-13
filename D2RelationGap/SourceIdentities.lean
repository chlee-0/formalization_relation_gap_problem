import D2RelationGap.WordSemantics
import D2RelationGap.TraceData

/-! Interprets OpenAI's six word certificates in the actual presented group P.
Credit: "A Counterexample to Wall's D(2) Problem", October 6, 2026,
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
The certificate replay soundness is ours; the identities are OpenAI's. -/
namespace D2RelationGap
open Targets

abbrev sourceMap : F →* P := PresentedGroup.mk sourceRelations

theorem rule_relator_mem (a b : Word) (hm : (a, b) ∈ rules) :
    freeWord (a ++ inverseWord b) ∈ sourceRelations := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h
  all_goals
    rcases Prod.mk.inj h with ⟨rfl, rfl⟩
    simp [sourceRelations, r1, r2, r3, r4, inverseWord, invert, pos, neg]

theorem rules_hold_of_relators {H : Type*} [Group H] (f : F →* H)
    (hrels : ∀ r ∈ sourceRelations, f r = 1) :
    ∀ a b, (a, b) ∈ rules → f (freeWord a) = f (freeWord b) := by
  intro a b hm
  have he := hrels _ (rule_relator_mem a b hm)
  rw [freeWord_append, freeWord_inverse, map_mul, map_inv] at he
  exact mul_inv_eq_one.mp he

theorem source_rules_hold :
    ∀ a b, (a, b) ∈ rules → sourceMap (freeWord a) = sourceMap (freeWord b) :=
  rules_hold_of_relators sourceMap (fun _ hr => PresentedGroup.one_of_mem hr)

theorem traces_sound_of_relators {H : Type*} [Group H] (f : F →* H)
    (hrels : ∀ r ∈ sourceRelations, f r = 1) :
    ∀ t ∈ wordTraces, f (freeWord t.start) = f (freeWord t.target) := by
  intro t ht
  exact checkTrace_sound f (rules_hold_of_relators f hrels) t
    (List.all_eq_true.mp source_traces_replay t ht)

theorem source_traces_sound :
    ∀ t ∈ wordTraces, sourceMap (freeWord t.start) = sourceMap (freeWord t.target) :=
  traces_sound_of_relators sourceMap (fun _ hr => PresentedGroup.one_of_mem hr)

abbrev fiveMap : F →* PresentedGroup fiveRelations := PresentedGroup.mk fiveRelations

/-- OpenAI's t1 = [t2,a2] makes t1 redundant in the actual five-relator quotient. -/
theorem t1_trivial_in_five_quotient : fiveMap (freeWord t1) = 1 := by
  have hrels : ∀ r ∈ sourceRelations, fiveMap r = 1 := by
    intro r hr
    exact PresentedGroup.one_of_mem (show r ∈ fiveRelations from Or.inl hr)
  have ht2 : fiveMap (freeWord t2) = 1 :=
    PresentedGroup.one_of_mem (show freeWord t2 ∈ fiveRelations by simp [fiveRelations])
  have he := traces_sound_of_relators fiveMap hrels (wordTraces[4]) (List.getElem_mem _)
  change fiveMap (freeWord (t2 ++ [pos .a2] ++ inverseWord t2 ++ [neg .a2])) =
    fiveMap (freeWord t1) at he
  simpa [freeWord_append, freeWord_inverse, freeWord_cons, freeLetter, pos, neg, ht2]
    using he.symm

theorem t1_mem_five_normalClosure : freeWord t1 ∈ Subgroup.normalClosure fiveRelations :=
  PresentedGroup.mk_eq_one_iff.mp t1_trivial_in_five_quotient

theorem five_normalClosure_eq :
    Subgroup.normalClosure fiveRelations = Subgroup.normalClosure quotientRelations := by
  apply le_antisymm
  · apply Subgroup.normalClosure_mono
    intro r hr
    rcases hr with hsource | ht2
    · exact Or.inl hsource
    · exact Or.inr (Set.mem_insert_of_mem _ ht2)
  · apply Subgroup.normalClosure_le_normal
    intro r hr
    rcases hr with hsource | hlast
    · exact Subgroup.subset_normalClosure (show r ∈ fiveRelations from Or.inl hsource)
    · rcases Set.mem_insert_iff.mp hlast with ht1 | ht2
      · rw [ht1]
        exact t1_mem_five_normalClosure
      · exact Subgroup.subset_normalClosure (show r ∈ fiveRelations from Or.inr ht2)

theorem original_kernel_eq : N = Subgroup.normalClosure quotientRelations := by
  ext g
  change quotientMap g = 1 ↔ g ∈ Subgroup.normalClosure quotientRelations
  exact PresentedGroup.mk_eq_one_iff

def normalGenerators : Fin 5 → F :=
  Fin.cons (freeWord r1) (Fin.cons (freeWord r2) (Fin.cons (freeWord r3)
    (Fin.cons (freeWord r4) (Fin.cons (freeWord t2) Fin.elim0))))

theorem normalGenerators_range : Set.range normalGenerators = fiveRelations := by
  ext r
  simp [normalGenerators, Set.mem_range, fiveRelations,
    sourceRelations, eq_comm, or_comm, or_assoc]

/-- The fixed original kernel has an explicit normally generating family of size five.
This supplies an upper bound, not minimality or global deficiency zero. -/
theorem hasNormalGenerators_five : HasNormalGenerators 5 := by
  refine ⟨normalGenerators, ?_⟩
  rw [normalGenerators_range, five_normalClosure_eq, ← original_kernel_eq]

end D2RelationGap
